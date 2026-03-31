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

        let step = choose |step| cluster.next_step(s, s_prime, step);
        let new_msgs = s_prime.in_flight().sub(s.in_flight());
        match step {
            Step::APIServerStep(req_msg_opt) => {
                let req_msg = req_msg_opt.unwrap();

                assert forall |msg| {
                    &&& invariant(s)
                    &&& stronger_next(s, s_prime)
                    &&& #[trigger] s_prime.in_flight().contains(msg)
                    &&& msg.content is APIRequest
                    &&& msg.src.is_controller_id(controller_id)
                } implies match msg.content->APIRequest_0 {
                    APIRequest::GetRequest(_) => true,
                    APIRequest::CreateRequest(req) => rmq_guarantee_create_req(req),
                    APIRequest::UpdateRequest(req) => rmq_guarantee_update_req(req),
                    _ => false,
                } by {
                    if s.in_flight().contains(msg) {} // used to instantiate invariant's trigger.
                }
            }
            Step::ControllerStep((id, _, cr_key_opt)) => {
                let cr_key = cr_key_opt->0;
                assert forall |msg| {
                    &&& invariant(s)
                    &&& stronger_next(s, s_prime)
                    &&& #[trigger] s_prime.in_flight().contains(msg)
                    &&& msg.content is APIRequest
                    &&& msg.src.is_controller_id(controller_id)
                } implies match msg.content->APIRequest_0 {
                    APIRequest::GetRequest(_) => true,
                    APIRequest::CreateRequest(req) => rmq_guarantee_create_req(req),
                    APIRequest::UpdateRequest(req) => rmq_guarantee_update_req(req),
                    _ => false,
                } by {
                    if s.in_flight().contains(msg) {} // used to instantiate invariant's trigger.

                    if id == controller_id && new_msgs.contains(msg) {
                        let triggering_cr = RabbitmqClusterView::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].triggering_cr).unwrap();
                        let local_state = RabbitmqReconcileState::unmarshal(s.ongoing_reconciles(controller_id)[cr_key].local_state).unwrap();
                        assert(msg.content->APIRequest_0 == reconcile_core(triggering_cr, None, local_state).1->0->KRequest_0);
                        lemma_guarantee_from_reconcile_state(msg, local_state, triggering_cr);
                    }
                }
            }
            _ => {
                assert forall |msg| {
                    &&& invariant(s)
                    &&& stronger_next(s, s_prime)
                    &&& #[trigger] s_prime.in_flight().contains(msg)
                    &&& msg.content is APIRequest
                    &&& msg.src.is_controller_id(controller_id)
                } implies match msg.content->APIRequest_0 {
                    APIRequest::GetRequest(_) => true,
                    APIRequest::CreateRequest(req) => rmq_guarantee_create_req(req),
                    APIRequest::UpdateRequest(req) => rmq_guarantee_update_req(req),
                    _ => false,
                } by {
                    if s.in_flight().contains(msg) {} // used to instantiate invariant's trigger.
                }
            }
        }
    }

    init_invariant(spec, cluster.init(), stronger_next, invariant);
}


pub proof fn lemma_guarantee_from_reconcile_state(
    msg: Message,
    state: RabbitmqReconcileState,
    rmq: RabbitmqClusterView,
)
    requires
        msg.content is APIRequest,
        reconcile_core(rmq, None, state).1 is Some,
        reconcile_core(rmq, None, state).1->0 is KRequest,
        msg.content->APIRequest_0 == reconcile_core(rmq, None, state).1->0->KRequest_0,
    ensures
        match msg.content->APIRequest_0 {
            APIRequest::GetRequest(_) => true,
            APIRequest::CreateRequest(req) => rmq_guarantee_create_req(req),
            APIRequest::UpdateRequest(req) => rmq_guarantee_update_req(req),
            _ => false,
        }
{
    match state.reconcile_step {
        AfterKRequestStep(ActionKind::Get, _) => {
            assert(msg.content.is_get_request());
        },
        AfterKRequestStep(ActionKind::Create, _) => {
            assert(msg.content.is_create_request());
            assert(rmq_guarantee_create_req(msg.content.get_create_request()));
        },
        AfterKRequestStep(ActionKind::Update, _) => {
            assert(msg.content.is_update_request());
            assert(rmq_guarantee_update_req(msg.content.get_update_request()));
        },
        _ => {
            assume(reconcile_core(rmq, None, state).1 is None);
        }
    }
}

pub open spec fn no_interfering_request_between_rmq_forall_rmq(controller_id: int, sub_resource: SubResource) -> StatePred<ClusterState> {
    |s: ClusterState| forall |rmq: RabbitmqClusterView| #[trigger] no_interfering_request_between_rmq(controller_id, sub_resource, rmq)(s)
}

// internal guarantee
// don't be confused by the argument name, other_rmq can be the current CR in reconciliation if you need
pub open spec fn no_interfering_request_between_rmq(controller_id: int, sub_resource: SubResource, other_rmq: RabbitmqClusterView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg| {
            &&& #[trigger] s.in_flight().contains(msg)
            &&& msg.content is APIRequest
            &&& msg.src == HostId::Controller(controller_id, other_rmq.object_ref())
        } ==> match msg.content->APIRequest_0 {
            APIRequest::GetRequest(req) => {
                req.key() == get_request(sub_resource, other_rmq).key
            },
            APIRequest::CreateRequest(req) => {
                req.key() == get_request(sub_resource, other_rmq).key
            },
            APIRequest::UpdateRequest(req)=> {
                req.key() == get_request(sub_resource, other_rmq).key
            },
            // RMQ controller doesn't send other requests
            _ => false
        }
    }
}

}