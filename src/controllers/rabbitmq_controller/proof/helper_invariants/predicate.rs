// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::kubernetes_api_objects::spec::{
    prelude::*, api_method::*, common::*, config_map::*, dynamic::*, owner_reference::*, resource::*,
    stateful_set::*, label_selector::LabelSelectorView,
};
use crate::kubernetes_cluster::spec::{
    cluster::*,
    controller::types::{ControllerActionInput, ControllerStep},
    message::*,
};
use crate::vstatefulset_controller::trusted::spec_types::VStatefulSetView;
use crate::rabbitmq_controller::{
    model::{reconciler::*, resource::*},
    proof::{predicate::*, resource::*},
    trusted::{spec_types::*, step::*, rely_guarantee::*},
};
use crate::reconciler::spec::reconciler::*;
use crate::temporal_logic::{defs::*, rules::*};
use crate::vstd_ext::{multiset_lib, seq_lib, string_view::*};
use vstd::{multiset::*, prelude::*, string::*};

verus! {

pub open spec fn requests_from_rmq_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(controller_id: int, sub_resource: SubResource, cr_key: ObjectRef) -> StatePred<ClusterState> {
    let cr = RabbitmqClusterView {
        metadata: ObjectMetaView {
            name: Some(cr_key.name),
            namespace: Some(cr_key.namespace),
            ..ObjectMetaView::default()
        },
        ..RabbitmqClusterView::default()
    };
    let resource_key = get_request(sub_resource, cr).key;
    |s: ClusterState| {
        forall |msg: Message| {
            &&& s.in_flight().contains(msg)
            &&& #[trigger] msg.src == HostId::Controller(controller_id, cr_key)
        } ==> {
            &&& resource_create_request_msg(resource_key)(msg) ==> exists |owner_reference: OwnerReferenceView| {
                &&& msg.content.get_create_request().obj.metadata.owner_references == Some(seq![owner_reference])
                &&& #[trigger] owner_reference_eq_without_uid(owner_reference, cr.controller_owner_ref())
            }
            &&& resource_get_then_update_request_msg(resource_key)(msg) ==> exists |owner_reference: OwnerReferenceView| {
                &&& msg.content.get_create_request().obj.metadata.owner_references == Some(seq![owner_reference])
                &&& #[trigger] owner_reference_eq_without_uid(owner_reference, cr.controller_owner_ref())
            }
        }
    }
}

pub open spec fn resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref(sub_resource: SubResource, rabbitmq: RabbitmqClusterView) -> StatePred<ClusterState> {
    let resource_key = get_request(sub_resource, rabbitmq).key;
    |s: ClusterState| {
        s.resources().contains_key(resource_key)
        ==> s.resources()[resource_key].metadata.deletion_timestamp is None
            && s.resources()[resource_key].metadata.finalizers is None
            && exists |owner_reference: OwnerReferenceView| {
                &&& s.resources()[resource_key].metadata.owner_references == Some(seq![owner_reference])
                &&& #[trigger] owner_reference_eq_without_uid(owner_reference, rabbitmq.controller_owner_ref())
            }
    }
}

pub open spec fn resource_get_response_msg(key: ObjectRef) -> spec_fn(Message) -> bool {
    |msg: Message|
        msg.src is APIServer
        && msg.content.is_get_response()
        && (
            msg.content.get_get_response().res is Ok
            ==> msg.content.get_get_response().res->Ok_0.object_ref() == key
        )
}

pub open spec fn resource_get_then_update_response_msg(key: ObjectRef, s: ClusterState) -> spec_fn(Message) -> bool {
    |msg: Message|
        msg.src is APIServer
        && msg.content.is_get_then_update_response()
        && (
            msg.content.get_get_then_update_response().res is Ok
            ==> (
                s.resources().contains_key(key)
                && msg.content.get_get_then_update_response().res->Ok_0 == s.resources()[key]
            )
        )
}

pub open spec fn resource_create_response_msg(key: ObjectRef, s: ClusterState) -> spec_fn(Message) -> bool {
    |msg: Message|
        msg.src is APIServer
        && msg.content.is_create_response()
        && (
            msg.content.get_create_response().res is Ok
            ==> (
                s.resources().contains_key(key)
                && msg.content.get_create_response().res->Ok_0 == s.resources()[key]
            )
        )
}


pub open spec fn every_valid_resource_update_request_sets_owner_references_to_current_cr(controller_id: int, sub_resource: SubResource, rabbitmq: RabbitmqClusterView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let key = rabbitmq.object_ref();
        forall |msg: Message| {
            let req = msg.content.get_get_then_update_request();
            &&& #[trigger] s.in_flight().contains(msg)
            &&& resource_get_then_update_request_msg(get_request(sub_resource, rabbitmq).key)(msg)
            &&& req.owner_ref.controller == Some(true) && req.owner_ref.kind == RabbitmqClusterView::kind()
        } ==> {
            &&& at_rabbitmq_step(key, controller_id, RabbitmqReconcileStep::AfterKRequestStep(ActionKind::Update, sub_resource))(s)
            &&& Cluster::pending_req_msg_is(controller_id, s, key, msg)
            &&& msg.content.get_get_then_update_request().obj.metadata.owner_references_only_contains(rabbitmq.controller_owner_ref())
        }
    }
}

pub open spec fn resource_object_only_has_owner_reference_pointing_to_current_cr(sub_resource: SubResource, rabbitmq: RabbitmqClusterView) -> StatePred<ClusterState> {
    let key = get_request(sub_resource, rabbitmq).key;
    |s: ClusterState| {
        s.resources().contains_key(key) ==> s.resources()[key].metadata.owner_references_only_contains(rabbitmq.controller_owner_ref())
    }
}

// The owner_references requirement consumed by `Cluster::lemma_eventually_objects_owner_references_satisfies`:
// the only valid owner_references for our sub-resource is `[rabbitmq.controller_owner_ref()]`.
pub open spec fn owner_ref_is_current_cr_only(rabbitmq: RabbitmqClusterView) -> spec_fn(Option<Seq<OwnerReferenceView>>) -> bool {
    |o: Option<Seq<OwnerReferenceView>>| o == Some(seq![rabbitmq.controller_owner_ref()])
}

// No delete request to resource_key from the garbage collector is in flight.
// The garbage collector only issues a delete when an object's owner is gone, but
// resource_key always has the current rabbitmq's controller_owner_ref (which is alive
// while desired_state_is(rabbitmq) holds). To rule out delete requests from other
// controllers, callers should directly invoke the rely conditions.
pub open spec fn no_delete_resource_request_msg_from_gc_in_flight(sub_resource: SubResource, rabbitmq: RabbitmqClusterView) -> StatePred<ClusterState> {
    let resource_key = get_request(sub_resource, rabbitmq).key;
    |s: ClusterState| {
        forall |msg: Message| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.src == HostId::BuiltinController
        } ==> !resource_delete_request_msg(resource_key)(msg)
    }
}

// Self-rely-guarantee between RMQ reconciles managed by the same controller_id
// but for different cr_keys. Says that any in-flight request issued by another
// (cr_key', controller_id) reconcile of the same RMQ kind does not target any
// of `cr_key`'s sub-resources. Resource keys are uniquely determined by
// (sub_resource, cr_key), so different cr_keys produce disjoint sub-resource
// keys; this predicate states that fact at the message level.
//
// Used by the shield lemma when a request comes from our own controller_id but a different cr_key.
// Only Create and GetThenUpdate are constrained, mirroring rmq_guarantee
// (rabbitmq controller is forbidden from issuing other mutating request types).
pub open spec fn rmq_self_rely_guarantee(controller_id: int, cr_key: ObjectRef) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg: Message| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.content is APIRequest
            &&& msg.src.is_controller_id(controller_id)
            &&& msg.src != HostId::Controller(controller_id, cr_key)
        } ==> match msg.content->APIRequest_0 {
            APIRequest::CreateRequest(req) => rmq_self_rely_guarantee_create_req(req, cr_key),
            APIRequest::GetThenUpdateRequest(req) => rmq_self_rely_guarantee_get_then_update_req(req, cr_key),
            _ => true,
        }
    }
}

pub open spec fn rmq_self_rely_guarantee_create_req(req: CreateRequest, cr_key: ObjectRef) -> bool {
    forall |sub: SubResource| req.key() != #[trigger] make_resource_key(cr_key, sub)
}

pub open spec fn rmq_self_rely_guarantee_get_then_update_req(req: GetThenUpdateRequest, cr_key: ObjectRef) -> bool {
    forall |sub: SubResource| req.key() != #[trigger] make_resource_key(cr_key, sub)
}

pub open spec fn sts_create_request_msg_has_correct_selector_with_rabbitmq_name(rabbitmq: RabbitmqClusterView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let sts_key = make_stateful_set_key(rabbitmq);
        forall |msg: Message| s.in_flight().contains(msg) && resource_create_request_msg(sts_key)(msg)
        ==> {
            let sts = VStatefulSetView::unmarshal(msg.content.get_create_request().obj)->Ok_0;
            &&& VStatefulSetView::unmarshal(msg.content.get_create_request().obj) is Ok
            &&& sts.spec.selector == LabelSelectorView::default().with_match_labels(Map::empty().insert("app"@, rabbitmq.metadata.name->0))
        }
    }
}

pub open spec fn sts_in_etcd_with_rmq_key_match_rmq_selector(rabbitmq: RabbitmqClusterView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let sts_key = make_stateful_set_key(rabbitmq);
        let sts = VStatefulSetView::unmarshal(s.resources()[sts_key]).unwrap();
        &&& s.resources().contains_key(sts_key)
            ==> sts.spec.selector == LabelSelectorView::default().with_match_labels(Map::empty().insert("app"@, rabbitmq.metadata.name->0))
    }
}

}
