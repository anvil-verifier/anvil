#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    api_server::{state_machine::*, types::InstalledTypes}, 
    cluster::*, 
    message::*
};
use crate::temporal_logic::{defs::*, rules::*};
use crate::vdeployment_controller::{
    model::{install::*, reconciler::*},
    trusted::{
        liveness_theorem::*, 
        rely_guarantee::*, 
        spec_types::*, 
        step::*
    },
    proof::{predicate::*},
};
use crate::vreplicaset_controller::{
    trusted::{
        spec_types::*,
    }
};
use vstd::prelude::*;

verus! {

// NOTE: helpers must be declared `pub open` for the main invariant to be declared so.

pub open spec fn no_other_pending_create_request_interferes_with_vd_reconcile(
    req: CreateRequest,
    vd: VDeploymentView
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        (req.obj.kind == VReplicaSetView::kind()
            && req.key().namespace == vd.metadata.namespace.unwrap()) ==> !{
            let owner_references = req.obj.metadata.owner_references->0;
            &&& req.obj.metadata.owner_references is Some
            &&& owner_references.contains(vd.controller_owner_ref())
        }
    }
}

pub open spec fn no_other_pending_update_request_interferes_with_vd_reconcile(
    req: UpdateRequest,
    vd: VDeploymentView
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        (req.obj.kind == VReplicaSetView::kind()
            && req.key().namespace == vd.metadata.namespace.unwrap()) ==>
            req.obj.metadata.resource_version is Some
            // Prevents 1): where a message not from our specific vd updates
            // a vd-owned vrs.
            && !{
                let etcd_obj = s.resources()[req.key()];
                let owner_references = etcd_obj.metadata.owner_references->0;
                &&& s.resources().contains_key(req.key())
                &&& etcd_obj.metadata.namespace == vd.metadata.namespace
                &&& etcd_obj.metadata.resource_version is Some
                &&& etcd_obj.metadata.resource_version == req.obj.metadata.resource_version
                &&& etcd_obj.metadata.owner_references is Some
                &&& owner_references.contains(vd.controller_owner_ref())
            }
            // Prevents 2): where any message not from our specific vd updates 
            // vrs objects so they become owned by another VDeployment.
            && (req.obj.metadata.owner_references is Some ==>
                        ! req.obj.metadata.owner_references->0.contains(vd.controller_owner_ref()))
    }
}

pub open spec fn no_other_pending_update_status_request_interferes_with_vd_reconcile(
    req: UpdateStatusRequest,
    vd: VDeploymentView
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        (req.obj.kind == VReplicaSetView::kind()
            && req.key().namespace == vd.metadata.namespace.unwrap()) ==> 
            req.obj.metadata.resource_version is Some
            && !{
                let etcd_obj = s.resources()[req.key()];
                let owner_references = etcd_obj.metadata.owner_references->0;
                &&& s.resources().contains_key(req.key())
                &&& etcd_obj.metadata.namespace == vd.metadata.namespace
                &&& etcd_obj.metadata.resource_version is Some
                &&& etcd_obj.metadata.resource_version == req.obj.metadata.resource_version
                &&& etcd_obj.metadata.owner_references is Some
                &&& owner_references.contains(vd.controller_owner_ref())
            }
    }
}

pub open spec fn no_other_pending_get_then_update_request_interferes_with_vd_reconcile(
    req: GetThenUpdateRequest,
    vd: VDeploymentView
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        req.obj.kind == VReplicaSetView::kind() ==> {
            // Prevents 1): where a message not from our specific vd updates
            // a vd-owned vrs.
            &&& (req.key().namespace == vd.metadata.namespace.unwrap() ==> {
                &&& req.owner_ref.controller is Some
                &&& req.owner_ref.controller->0
                &&& req.owner_ref != vd.controller_owner_ref()
            })
            // Prevents 2): where any message not from our specific vd updates 
            // vrs objects so they become owned by another VDeployment.
            &&& ((req.obj.metadata.owner_references is Some
                    && req.key().namespace == vd.object_ref().namespace) ==>
                    ! req.obj.metadata.owner_references->0.contains(vd.controller_owner_ref()))
        }
    }
}

pub open spec fn no_other_pending_delete_request_interferes_with_vd_reconcile(
    req: DeleteRequest,
    vd: VDeploymentView
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        (req.key.kind == VReplicaSetView::kind()
            && req.key.namespace == vd.metadata.namespace.unwrap()) ==>
            req.preconditions is Some
            && {
                ||| {
                    req.preconditions->0.resource_version is Some
                    && !{
                        let etcd_obj = s.resources()[req.key];
                        let owner_references = etcd_obj.metadata.owner_references->0;
                        &&& s.resources().contains_key(req.key)
                        &&& etcd_obj.metadata.namespace == vd.metadata.namespace
                        &&& etcd_obj.metadata.resource_version is Some
                        &&& etcd_obj.metadata.resource_version
                            == req.preconditions->0.resource_version
                        &&& etcd_obj.metadata.owner_references is Some
                        &&& owner_references.contains(vd.controller_owner_ref())
                    }
                }
                ||| { // required to handle garbage collector's messages.
                    &&& req.preconditions.unwrap().uid is Some
                    &&& req.preconditions.unwrap().uid.unwrap() < s.api_server.uid_counter
                    &&& s.resources().contains_key(req.key) ==> {
                        let obj = s.resources()[req.key];
                        ||| !(obj.metadata.owner_references_contains(vd.controller_owner_ref())
                                && obj.kind == VReplicaSetView::kind()
                                && obj.metadata.namespace == vd.metadata.namespace)
                        ||| obj.metadata.uid.unwrap() > req.preconditions.unwrap().uid.unwrap()
                    }
                }
            }
    }
}

pub open spec fn no_other_pending_get_then_delete_request_interferes_with_vd_reconcile(
    req: GetThenDeleteRequest,
    vd: VDeploymentView
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        (req.key.kind == VReplicaSetView::kind()
            && req.key.namespace == vd.metadata.namespace.unwrap()) ==> {
            &&& req.owner_ref.controller is Some
            &&& req.owner_ref.controller->0
            &&& req.owner_ref != vd.controller_owner_ref()
        }
    }
}

// States that no pending request that is not from the specific reconcile
// associated with `vd` interferes with the reconcile of `vd`.
pub open spec fn no_other_pending_request_interferes_with_vd_reconcile(
    vd: VDeploymentView,
    controller_id: int
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg: Message| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.src != HostId::Controller(controller_id, vd.object_ref())
            &&& msg.dst.is_APIServer()
            &&& msg.content.is_APIRequest()
        } ==> {
            let content = msg.content;
            match content.get_APIRequest_0() {
                APIRequest::CreateRequest(req) => no_other_pending_create_request_interferes_with_vd_reconcile(req, vd)(s),
                APIRequest::UpdateRequest(req) => no_other_pending_update_request_interferes_with_vd_reconcile(req, vd)(s),
                APIRequest::UpdateStatusRequest(req) => no_other_pending_update_status_request_interferes_with_vd_reconcile(req, vd)(s),
                APIRequest::GetThenUpdateRequest(req) => no_other_pending_get_then_update_request_interferes_with_vd_reconcile(req, vd)(s),
                APIRequest::DeleteRequest(req) => no_other_pending_delete_request_interferes_with_vd_reconcile(req, vd)(s),
                APIRequest::GetThenDeleteRequest(req) => no_other_pending_get_then_delete_request_interferes_with_vd_reconcile(req, vd)(s),
                _ => true,
            }
        }
    }
}

pub open spec fn vd_reconcile_create_request_only_interferes_with_itself(
    req: CreateRequest,
    vd: VDeploymentView
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let owner_references = req.obj.metadata.owner_references->0;
        &&& req.obj.kind == VReplicaSetView::kind()
        &&& req.key().namespace == vd.metadata.namespace.unwrap()
        &&& req.obj.metadata.owner_references is Some
        &&& exists |owner_ref: OwnerReferenceView| {
            // using the macro messes up the trigger.
            &&& owner_references == #[trigger] Seq::empty().push(owner_ref)
            &&& owner_ref.controller is Some
            &&& owner_ref.controller->0
            &&& owner_ref.kind == VDeploymentView::kind()
            &&& owner_ref.name == vd.object_ref().name
        }
    }
}

pub open spec fn vd_reconcile_get_then_update_request_only_interferes_with_itself(
    req: GetThenUpdateRequest,
    vd: VDeploymentView
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let owners = req.obj.metadata.owner_references.get_Some_0();
        let controller_owners = owners.filter(
            |o: OwnerReferenceView| o.controller.is_Some() && o.controller.get_Some_0()
        );
        &&& req.key().kind == VReplicaSetView::kind()
        &&& req.key().namespace == vd.metadata.namespace.unwrap()
        &&& req.owner_ref.controller is Some
        &&& req.owner_ref.controller->0
        &&& req.owner_ref.kind == VDeploymentView::kind()
        &&& req.owner_ref.name == vd.object_ref().name
        &&& req.obj.metadata.owner_references.is_Some()
        &&& controller_owners == seq![vd.controller_owner_ref()]
    }
}

pub open spec fn vd_reconcile_request_only_interferes_with_itself(
    controller_id: int,
    vd: VDeploymentView
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.content.is_APIRequest()
            &&& msg.src == HostId::Controller(controller_id, vd.object_ref())
        } ==> match msg.content.get_APIRequest_0() {
            APIRequest::ListRequest(_) => true,
            APIRequest::CreateRequest(req) => vd_reconcile_create_request_only_interferes_with_itself(req, vd)(s),
            APIRequest::GetThenUpdateRequest(req) => vd_reconcile_get_then_update_request_only_interferes_with_itself(req, vd)(s),
            _ => false, // vd doesn't send other requests (yet).
        }
    }
}

// TODO: rethink the below pair of invariants (which rely on each other for proof).
pub open spec fn no_pending_interfering_update_request() -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg: Message| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.dst.is_APIServer()
            &&& msg.content.is_APIRequest()
        } ==> match msg.content.get_APIRequest_0() {
            APIRequest::UpdateRequest(req) => vd_rely_update_req(req)(s),
            APIRequest::GetThenUpdateRequest(req) => vd_rely_get_then_update_req(req)(s),
            _ => true,
        }
    }
}

pub open spec fn garbage_collector_does_not_delete_vd_vrs_objects(vd: VDeploymentView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg: Message| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.src.is_BuiltinController()
            &&& msg.dst.is_APIServer()
            &&& msg.content.is_APIRequest()
        } ==> {
            let req = msg.content.get_delete_request(); 
            &&& msg.content.is_delete_request()
            &&& req.preconditions is Some
            &&& req.preconditions.unwrap().uid is Some
            &&& req.preconditions.unwrap().uid.unwrap() < s.api_server.uid_counter
            &&& s.resources().contains_key(req.key) ==> {
                let obj = s.resources()[req.key];
                ||| !(obj.metadata.owner_references_contains(vd.controller_owner_ref())
                        && obj.kind == VReplicaSetView::kind()
                        && obj.metadata.namespace == vd.metadata.namespace)
                ||| obj.metadata.uid.unwrap() > req.preconditions.unwrap().uid.unwrap()
            }
        }
    }
}

pub open spec fn no_pending_mutation_request_not_from_controller_on_vrs_objects() -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg: Message| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& !(msg.src.is_Controller() || msg.src.is_BuiltinController())
            &&& msg.dst.is_APIServer()
            &&& msg.content.is_APIRequest()
        } ==> {
            &&& msg.content.is_create_request() ==> msg.content.get_create_request().key().kind != VReplicaSetView::kind()
            &&& msg.content.is_update_request() ==> msg.content.get_update_request().key().kind != VReplicaSetView::kind()
            // too radical, loosen it later to allow updates on vrs status.
            &&& msg.content.is_update_status_request() ==> msg.content.get_update_status_request().key().kind != VReplicaSetView::kind()
            &&& msg.content.is_delete_request() ==> msg.content.get_delete_request().key.kind != VReplicaSetView::kind()
            &&& msg.content.is_get_then_delete_request() ==> msg.content.get_get_then_delete_request().key.kind != VReplicaSetView::kind()
            &&& msg.content.is_get_then_update_request() ==> msg.content.get_get_then_update_request().key().kind != VReplicaSetView::kind()
        }
    }
}

pub open spec fn vrs_objects_in_local_reconcile_state_are_controllerly_owned_by_vd(controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |key: ObjectRef|
            #[trigger] s.ongoing_reconciles(controller_id).contains_key(key)
            ==> {
                let state = VDeploymentReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[key].local_state).unwrap();
                let triggering_cr = VDeploymentView::unmarshal(s.ongoing_reconciles(controller_id)[key].triggering_cr).unwrap();
                let new_vrs = state.new_vrs.unwrap();
                let old_vrs_list = state.old_vrs_list;
                &&& triggering_cr.object_ref() == key
                &&& triggering_cr.metadata().well_formed_for_namespaced()
                &&& forall |i| #![trigger old_vrs_list[i]] 0 <= i < old_vrs_list.len() ==>
                    (
                        old_vrs_list[i].object_ref().namespace == triggering_cr.metadata.namespace.unwrap()
                        && old_vrs_list[i].metadata.owner_references_contains(
                            triggering_cr.controller_owner_ref()
                        )
                    )
                &&& state.new_vrs is Some
                    ==> (new_vrs.object_ref().namespace == triggering_cr.metadata.namespace.unwrap()
                        && new_vrs.metadata.owner_references_contains(triggering_cr.controller_owner_ref()))
                // Special case: a stronger property implying the above property
                // after filtering holds on a list response to the
                // appropriate request. 
                &&& state.reconcile_step == VDeploymentReconcileStepView::AfterListVRS ==> {
                    let req_msg = s.ongoing_reconciles(controller_id)[key].pending_req_msg->0;
                    &&& s.ongoing_reconciles(controller_id)[triggering_cr.object_ref()].pending_req_msg is Some
                    &&& req_msg.dst.is_APIServer()
                    &&& req_msg.content.is_list_request()
                    &&& req_msg.content.get_list_request() == ListRequest {
                        kind: VReplicaSetView::kind(),
                        namespace: triggering_cr.metadata.namespace.unwrap(),
                    }
                    &&& forall |msg| {
                        let req_msg = s.ongoing_reconciles(controller_id)[triggering_cr.object_ref()].pending_req_msg->0;
                        &&& #[trigger] s.in_flight().contains(msg)
                        &&& s.ongoing_reconciles(controller_id)[triggering_cr.object_ref()].pending_req_msg is Some
                        &&& msg.src.is_APIServer()
                        &&& resp_msg_matches_req_msg(msg, req_msg)
                        &&& is_ok_resp(msg.content.get_APIResponse_0())
                    } ==> {
                        let resp_objs = msg.content.get_list_response().res.unwrap();
                        &&& msg.content.is_list_response()
                        &&& msg.content.get_list_response().res is Ok
                        &&& resp_objs.filter(|o: DynamicObjectView| VReplicaSetView::unmarshal(o).is_err()).len() == 0 
                        &&& forall |i| #![trigger resp_objs[i]] 0 <= i < resp_objs.len() ==>
                        (
                            resp_objs[i].metadata.namespace.is_some()
                            && resp_objs[i].metadata.namespace.unwrap() == triggering_cr.metadata.namespace.unwrap()
                            && resp_objs[i].kind == VReplicaSetView::kind()
                        )
                    }
                }
            }
    }
}
//
// TODO: See if we can split up this invariant into smaller ones.
// Both parts are necessary outside of this proof, but maybe for presentation purposes it 
// would be better to split them.
//

pub open spec fn every_msg_from_vd_controller_carries_vd_key(
    controller_id: int,
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg: Message| #![trigger s.in_flight().contains(msg)] {
            let content = msg.content;
            &&& s.in_flight().contains(msg)
            &&& msg.src.is_Controller()
            &&& msg.src.get_Controller_0() == controller_id
        } ==> {
            msg.src.get_Controller_1().kind == VDeploymentView::kind()
        }
    }
}

pub open spec fn vd_in_etcd_does_not_have_deletion_timestamp(
    vd: VDeploymentView, controller_id: int,
) -> StatePred<ClusterState> {
    |s: ClusterState| s.resources().contains_key(vd.object_ref()) ==> {
        &&& s.resources()[vd.object_ref()].metadata.deletion_timestamp is None
        &&& VDeploymentView::unmarshal(s.resources()[vd.object_ref()]).unwrap().metadata().deletion_timestamp is None
    }
}

pub open spec fn vd_in_schedule_does_not_have_deletion_timestamp(
    vd: VDeploymentView, controller_id: int,
) -> StatePred<ClusterState> {
    |s: ClusterState| s.scheduled_reconciles(controller_id).contains_key(vd.object_ref()) ==> {
        &&& s.scheduled_reconciles(controller_id)[vd.object_ref()].metadata.deletion_timestamp is None
        &&& VDeploymentView::unmarshal(s.scheduled_reconciles(controller_id)[vd.object_ref()]).unwrap().metadata().deletion_timestamp is None
    }
}

pub open spec fn vd_in_ongoing_reconciles_does_not_have_deletion_timestamp(
    vd: VDeploymentView, controller_id: int,
) -> StatePred<ClusterState> {
    |s: ClusterState| s.ongoing_reconciles(controller_id).contains_key(vd.object_ref()) ==> {
        &&& s.ongoing_reconciles(controller_id)[vd.object_ref()].triggering_cr.metadata.deletion_timestamp is None
        &&& VDeploymentView::unmarshal(s.ongoing_reconciles(controller_id)[vd.object_ref()].triggering_cr).unwrap().metadata().deletion_timestamp is None
    }
}

}