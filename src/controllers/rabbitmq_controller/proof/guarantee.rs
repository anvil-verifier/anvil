#![allow(unused_imports)]
use super::predicate::*;
use crate::rabbitmq_controller::model::install::rabbitmq_controller_model;
use crate::kubernetes_api_objects::spec::{
    api_method::*, common::*, owner_reference::*, prelude::*, resource::*,
    label_selector::LabelSelectorView, volume_resource_requirements::*,
};
use crate::kubernetes_cluster::spec::{
    cluster::*,
    message::*,
    api_server::state_machine::*,
};
use crate::rabbitmq_controller::{
    model::{reconciler::*, resource::*},
    proof::{predicate::*, resource::*},
    trusted::{liveness_theorem::*, spec_types::*, step::*, rely_guarantee::*},
};
use crate::rabbitmq_controller::trusted::step::RabbitmqReconcileStep::AfterKRequestStep;
use crate::reconciler::spec::io::*;
use crate::vstatefulset_controller::trusted::spec_types::{VStatefulSetView, StatefulSetPodNameLabel, StatefulSetOrdinalLabel};
use crate::temporal_logic::{defs::*, rules::*};
use crate::vstd_ext::{multiset_lib, seq_lib, string_view::*};
use vstd::{multiset::*, prelude::*, string::*};

verus !{


#[verifier(spinoff_prover)]
pub proof fn guarantee_condition_holds(spec: TempPred<ClusterState>, cluster: Cluster, controller_id: int)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
    ensures
        spec.entails(always(lift_state(rmq_guarantee(controller_id))))
{
    let invariant = rmq_guarantee(controller_id);

    cluster.lemma_always_cr_states_are_unmarshallable::<RabbitmqReconciler, RabbitmqReconcileState, RabbitmqClusterView, VoidEReqView, VoidERespView>(spec, controller_id);
    cluster.lemma_always_there_is_the_controller_state(spec, controller_id);
    cluster.lemma_always_each_object_in_etcd_has_at_most_one_controller_owner(spec);
    cluster.lemma_always_each_object_in_etcd_is_weakly_well_formed(spec);

    let stronger_next = |s, s_prime| {
        &&& cluster.next()(s, s_prime)
        &&& Cluster::there_is_the_controller_state(controller_id)(s)
        &&& Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)(s)
        &&& Cluster::each_object_in_etcd_has_at_most_one_controller_owner()(s)
        &&& Cluster::each_object_in_etcd_is_weakly_well_formed()(s)
    };

    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next), lift_action(cluster.next()),
        lift_state(Cluster::there_is_the_controller_state(controller_id)),
        lift_state(Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)),
        lift_state(Cluster::each_object_in_etcd_has_at_most_one_controller_owner()),
        lift_state(Cluster::each_object_in_etcd_is_weakly_well_formed())
    );

    assert forall |s, s_prime| invariant(s) && #[trigger] stronger_next(s, s_prime) implies invariant(s_prime) by {
        RabbitmqClusterView::marshal_preserves_integrity();
        RabbitmqReconcileState::marshal_preserves_integrity();

        assert forall |msg| {
            &&& invariant(s)
            &&& stronger_next(s, s_prime)
            &&& #[trigger] s_prime.in_flight().contains(msg)
            &&& msg.content is APIRequest
            &&& msg.src.is_controller_id(controller_id)
        } implies match msg.content->APIRequest_0 {
            APIRequest::GetRequest(_) => true,
            APIRequest::CreateRequest(req) => rmq_guarantee_create_req(req),
            APIRequest::GetThenUpdateRequest(req) => rmq_guarantee_get_then_update_req(req),
            _ => false,
        } by {
            if s.in_flight().contains(msg) {} // used to instantiate invariant's trigger.

            let step = choose |step| cluster.next_step(s, s_prime, step);
            let new_msgs = s_prime.in_flight().sub(s.in_flight());
            match step {
                Step::ControllerStep((id, resp_msg_opt, cr_key_opt)) => {
                    if id == controller_id && new_msgs.contains(msg) {
                        let cr_key = cr_key_opt->0;
                        let triggering_cr = RabbitmqClusterView::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].triggering_cr).unwrap();
                        let local_state = RabbitmqReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].local_state).unwrap();
                        let resp_o: Option<ResponseView<VoidERespView>> = if resp_msg_opt is Some {
                            if resp_msg_opt->0.content is APIResponse {
                                Some(ResponseView::KResponse(resp_msg_opt->0.content->APIResponse_0))
                            } else {
                                // RMQ controller has no external model, so this case is unreachable
                                None
                            }
                        } else {
                            None
                        };
                        assert(msg.content->APIRequest_0 == reconcile_core(triggering_cr, resp_o, local_state).1->0->KRequest_0);
                        lemma_guarantee_from_reconcile_state(msg, local_state, triggering_cr, resp_o);
                    }
                },
                _ => {}
            }
        }
    }

    init_invariant(spec, cluster.init(), stronger_next, invariant);
}


pub proof fn lemma_guarantee_from_reconcile_state(
    msg: Message,
    state: RabbitmqReconcileState,
    rmq: RabbitmqClusterView,
    resp_o: Option<ResponseView<VoidERespView>>,
)
    requires
        msg.content is APIRequest,
        reconcile_core(rmq, resp_o, state).1 is Some,
        reconcile_core(rmq, resp_o, state).1->0 is KRequest,
        msg.content->APIRequest_0 == reconcile_core(rmq, resp_o, state).1->0->KRequest_0,
    ensures
        match msg.content->APIRequest_0 {
            APIRequest::GetRequest(_) => true,
            APIRequest::CreateRequest(req) => rmq_guarantee_create_req(req),
            APIRequest::GetThenUpdateRequest(req) => rmq_guarantee_get_then_update_req(req),
            _ => false,
        }
{
    match state.reconcile_step {
        RabbitmqReconcileStep::Init => {
            // Init sends a GetRequest, which is always OK
            assert(msg.content.is_get_request());
        },
        AfterKRequestStep(action, resource) => {
            match action {
                ActionKind::Get => {
                    // AfterKRequestStep(Get, _) processes the Get response and sends
                    // either a CreateRequest (if object not found) or UpdateRequest (if object exists).
                    // Need to show both satisfy the guarantee.
                    if resp_o is Some && resp_o->0 is KResponse && resp_o->0->KResponse_0 is GetResponse {
                        let get_resp = resp_o->0->KResponse_0->GetResponse_0.res;
                        if get_resp is Ok {
                            // Update path: sends UpdateRequest
                            // reconcile_helper calls Builder::update which sets owner_references
                            assert(msg.content.is_get_then_update_request());
                            let req = msg.content.get_get_then_update_request();
                            // The update function for every resource builder sets
                            // owner_references = Some(seq![rmq.controller_owner_ref()])
                            assert(rmq_guarantee_get_then_update_req(req));
                        } else if get_resp->Err_0 is ObjectNotFound {
                            // Create path: sends CreateRequest
                            // reconcile_helper calls Builder::make which sets owner_references
                            assert(msg.content.is_create_request());
                            let req = msg.content.get_create_request();
                            // The make function for every resource builder sets
                            // owner_references = Some(seq![rmq.controller_owner_ref()])
                            assert(rmq_guarantee_create_req(req));
                        } else {
                            // Error case: no message sent (reconcile_core returns None)
                            assert(reconcile_core(rmq, resp_o, state).1 is None);
                        }
                    } else {
                        // Invalid/missing response: no message sent
                        assert(reconcile_core(rmq, resp_o, state).1 is None);
                    }
                },
                ActionKind::Create => {
                    // AfterKRequestStep(Create, _) processes the Create response and
                    // calls state_after_create which sends a GetRequest for the next resource.
                    if resp_o is Some && resp_o->0 is KResponse && resp_o->0->KResponse_0 is CreateResponse {
                        let create_resp = resp_o->0->KResponse_0->CreateResponse_0.res;
                        if create_resp is Ok {
                            // state_after_create returns GetRequest for next subresource
                            assert(msg.content.is_get_request());
                        } else {
                            // Error case: no message sent
                            assert(reconcile_core(rmq, resp_o, state).1 is None);
                        }
                    } else {
                        assert(reconcile_core(rmq, resp_o, state).1 is None);
                    }
                },
                ActionKind::Update => {
                    // AfterKRequestStep(Update, _) processes the Update response and
                    // calls state_after_update which sends a GetRequest for the next resource.
                    if resp_o is Some && resp_o->0 is KResponse && resp_o->0->KResponse_0 is UpdateResponse {
                        let update_resp = resp_o->0->KResponse_0->UpdateResponse_0.res;
                        if update_resp is Ok {
                            // state_after_update returns GetRequest for next subresource
                            assert(msg.content.is_get_request());
                        } else {
                            // Error case: no message sent
                            assert(reconcile_core(rmq, resp_o, state).1 is None);
                        }
                    } else {
                        assert(reconcile_core(rmq, resp_o, state).1 is None);
                    }
                },
            }
        },
        _ => {
            // Done/Error: no message sent
            assert(reconcile_core(rmq, resp_o, state).1 is None);
        }
    }
}

}