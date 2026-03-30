// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::rabbitmq_controller::model::install::*;
use crate::kubernetes_api_objects::spec::{
    api_method::*, common::*, config_map::*, dynamic::*, owner_reference::*, resource::*,
    stateful_set::*,
};
use crate::vstatefulset_controller::trusted::spec_types::VStatefulSetView;
use crate::vstatefulset_controller::trusted::spec_types::*;
use crate::kubernetes_cluster::spec::{
    cluster::*,
    controller::types::{ControllerActionInput, ControllerStep},
    message::*,
};
use crate::rabbitmq_controller::{
    model::{reconciler::*, resource::*},
    proof::{
        helper_invariants::{owner_ref::*, predicate::*, proof::*},
        predicate::*,
        resource::*,
    },
    trusted::{spec_types::*, step::*, rely_guarantee::*},
};
use crate::reconciler::spec::{reconciler::*, resource_builder::*};
use crate::temporal_logic::{defs::*, rules::*};
use crate::vstd_ext::{multiset_lib, seq_lib, string_view::*};
use vstd::{multiset::*, prelude::*, string::*};
use crate::reconciler::spec::io::{VoidEReqView, VoidERespView};

verus! {

// We need such a spec for stateful set because certain fields are determined by the spec of custom resource object and won't
// be updated. So we need the transition validation of custom resource (rabbitmq) to show some fields of rabbitmq won't change
// by the update request. Therefore, though updating stateful set won't update those fields, the stateful set will still match
// the desired state.
//
// We don't need this for other subresources because they don't have such fields: (1) those fields are determined by the rabbitmq
// object (except the key of rabbitmq); and (2) these fields won't be updated during update.
pub open spec fn certain_fields_of_stateful_set_stay_unchanged(obj: DynamicObjectView, rabbitmq: RabbitmqClusterView) -> bool {
    let made_spec = make_stateful_set(rabbitmq, ""@).spec;
    let sts = VStatefulSetView::unmarshal(obj)->Ok_0;

    obj.metadata.owner_references_only_contains(rabbitmq.controller_owner_ref()) ==> made_spec == VStatefulSetSpecView {
        replicas: made_spec.replicas,
        template: made_spec.template,
        persistent_volume_claim_retention_policy: made_spec.persistent_volume_claim_retention_policy,
        ..sts.spec
    }
}

pub open spec fn stateful_set_update_request_msg_does_not_change_owner_reference(rabbitmq: RabbitmqClusterView) -> StatePred<ClusterState> {
    let key = rabbitmq.object_ref();
    let sts_key = StatefulSetBuilder::get_request(rabbitmq).key;
    |s: ClusterState| {
        forall |msg: Message|
            s.in_flight().contains(msg)
            && #[trigger] resource_update_request_msg(sts_key)(msg)
            && s.resources().contains_key(sts_key)
            && s.resources()[sts_key].metadata.resource_version == msg.content.get_update_request().obj.metadata.resource_version
            ==> s.resources()[sts_key].metadata.owner_references == msg.content.get_update_request().obj.metadata.owner_references
    }
}

pub proof fn lemma_always_stateful_set_update_request_msg_does_not_change_owner_reference(controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>, rabbitmq: RabbitmqClusterView)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
    ensures spec.entails(always(lift_state(stateful_set_update_request_msg_does_not_change_owner_reference(rabbitmq)))),
{
    VStatefulSetView::marshal_preserves_integrity();
    RabbitmqClusterView::marshal_preserves_integrity();
    let key = rabbitmq.object_ref();
    let sts_key = StatefulSetBuilder::get_request(rabbitmq).key;
    let inv = stateful_set_update_request_msg_does_not_change_owner_reference(rabbitmq);
    let next = |s, s_prime| {
        &&& cluster.next()(s, s_prime)
        &&& cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()(s)
        &&& cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()(s_prime)
        &&& response_at_after_get_resource_step_is_resource_get_response(controller_id, SubResource::VStatefulSetView, rabbitmq)(s)
        &&& Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& Cluster::object_in_ok_get_resp_is_same_as_etcd_with_same_rv(sts_key)(s)
        &&& object_in_resource_update_request_msg_has_smaller_rv_than_etcd(SubResource::VStatefulSetView, rabbitmq)(s)
    };
    cluster.lemma_always_each_object_in_etcd_is_well_formed::<RabbitmqClusterView>(spec);
    lemma_always_response_at_after_get_resource_step_is_resource_get_response(controller_id, cluster, spec, SubResource::VStatefulSetView, rabbitmq);
    always_to_always_later(spec, lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()));
    cluster.lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec, controller_id);
    cluster.lemma_always_object_in_ok_get_resp_is_same_as_etcd_with_same_rv(spec, sts_key);
    lemma_always_object_in_resource_update_request_msg_has_smaller_rv_than_etcd(controller_id, cluster, spec, SubResource::VStatefulSetView, rabbitmq);
    combine_spec_entails_always_n!(
        spec, lift_action(next), lift_action(cluster.next()),
        lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()),
        later(lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>())),
        lift_state(response_at_after_get_resource_step_is_resource_get_response(controller_id, SubResource::VStatefulSetView, rabbitmq)),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::object_in_ok_get_resp_is_same_as_etcd_with_same_rv(sts_key)),
        lift_state(object_in_resource_update_request_msg_has_smaller_rv_than_etcd(SubResource::VStatefulSetView, rabbitmq))
    );
    assert forall |s, s_prime| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        assert forall |msg| #[trigger] s_prime.in_flight().contains(msg) && resource_update_request_msg(sts_key)(msg)
        && s_prime.resources().contains_key(sts_key)
        && s_prime.resources()[sts_key].metadata.resource_version == msg.content.get_update_request().obj.metadata.resource_version
        implies s_prime.resources()[sts_key].metadata.owner_references == msg.content.get_update_request().obj.metadata.owner_references by {
            let step = choose |step| cluster.next_step(s, s_prime, step);
            match step {
                Step::APIServerStep(input) => {
                    assume(false);
                },
                Step::ControllerStep(_) => {
                    // controller only sends msg, do not touch etcd obj / delete msg, just prove it holds for new messages
                    if !s.in_flight().contains(msg) && resource_update_request_msg(get_request(SubResource::VStatefulSetView, rabbitmq).key)(msg) {
                        lemma_resource_update_request_msg_implies_key_in_reconcile_equals(controller_id, cluster, SubResource::VStatefulSetView, rabbitmq, s, s_prime, msg, step);
                    }
                },
                _ => {}
            }
        }
    }
    init_invariant(spec, cluster.init(), next, inv);
}

pub open spec fn object_in_resource_update_request_msg_has_smaller_rv_than_etcd(sub_resource: SubResource, rabbitmq: RabbitmqClusterView) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let resource_key = get_request(sub_resource, rabbitmq).key;
        let etcd_rv = s.resources()[resource_key].metadata.resource_version->0;
        forall |msg: Message|
            s.in_flight().contains(msg)
            && #[trigger] resource_update_request_msg(get_request(sub_resource, rabbitmq).key)(msg)
            ==> msg.content.get_update_request().obj.metadata.resource_version is Some
                && msg.content.get_update_request().obj.metadata.resource_version->0 < s.api_server.resource_version_counter
    }
}

#[verifier(spinoff_prover)]
#[verifier(rlimit(300))]
pub proof fn lemma_always_object_in_resource_update_request_msg_has_smaller_rv_than_etcd(controller_id: int, cluster: Cluster, spec: TempPred<ClusterState>, sub_resource: SubResource, rabbitmq: RabbitmqClusterView)
    requires
        spec.entails(lift_state(cluster.init())),
        spec.entails(always(lift_action(cluster.next()))),
        spec.entails(always(lift_state(no_interfering_request_between_rmq_forall_rmq(controller_id, sub_resource)))),
        spec.entails(always(lift_state(rmq_rely_conditions(cluster, controller_id)))),
        cluster.type_is_installed_in_cluster::<RabbitmqClusterView>(),
        cluster.type_is_installed_in_cluster::<VStatefulSetView>(),
        cluster.controller_models.contains_pair(controller_id, rabbitmq_controller_model()),
    ensures spec.entails(always(lift_state(object_in_resource_update_request_msg_has_smaller_rv_than_etcd(sub_resource, rabbitmq)))),
{
    let key = rabbitmq.object_ref();
    let sts_key = get_request(sub_resource, rabbitmq).key;
    let inv = object_in_resource_update_request_msg_has_smaller_rv_than_etcd(sub_resource, rabbitmq);
    let stronger_next = |s, s_prime| {
        &&& cluster.next()(s, s_prime)
        &&& response_at_after_get_resource_step_is_resource_get_response(controller_id, sub_resource, rabbitmq)(s)
        &&& cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()(s)
        &&& cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()(s_prime)
        &&& Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& Cluster::object_in_ok_get_response_has_smaller_rv_than_etcd()(s)
        &&& Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)(s)
        &&& Cluster::cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(controller_id)(s)
        &&& cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()(s)
        &&& no_interfering_request_between_rmq_forall_rmq(controller_id, sub_resource)(s_prime)
        &&& rmq_rely_conditions(cluster, controller_id)(s_prime)
    };
    cluster.lemma_always_each_object_in_etcd_is_well_formed::<RabbitmqClusterView>(spec);
    cluster.lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec, controller_id);
    cluster.lemma_always_object_in_ok_get_response_has_smaller_rv_than_etcd(spec);
    cluster.lemma_always_cr_states_are_unmarshallable::<RabbitmqReconciler, RabbitmqReconcileState, RabbitmqClusterView, VoidEReqView, VoidERespView>(spec, controller_id);
    cluster.lemma_always_cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(spec, controller_id);
    cluster.lemma_always_every_in_flight_req_msg_from_controller_has_valid_controller_id(spec);
    lemma_always_response_at_after_get_resource_step_is_resource_get_response(controller_id, cluster, spec, sub_resource, rabbitmq);
    always_to_always_later(spec, lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()));
    always_to_always_later(spec, lift_state(no_interfering_request_between_rmq_forall_rmq(controller_id, sub_resource)));
    always_to_always_later(spec, lift_state(rmq_rely_conditions(cluster, controller_id)));
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(cluster.next()),
        lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>()),
        later(lift_state(cluster.each_object_in_etcd_is_well_formed::<RabbitmqClusterView>())),
        lift_state(response_at_after_get_resource_step_is_resource_get_response(controller_id, sub_resource, rabbitmq)),
        lift_state(Cluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Cluster::object_in_ok_get_response_has_smaller_rv_than_etcd()),
        lift_state(Cluster::cr_states_are_unmarshallable::<RabbitmqReconcileState, RabbitmqClusterView>(controller_id)),
        lift_state(Cluster::cr_objects_in_reconcile_satisfy_state_validation::<RabbitmqClusterView>(controller_id)),
        lift_state(cluster.every_in_flight_req_msg_from_controller_has_valid_controller_id()),
        later(lift_state(no_interfering_request_between_rmq_forall_rmq(controller_id, sub_resource))),
        later(lift_state(rmq_rely_conditions(cluster, controller_id)))
    );
    assert forall |s, s_prime| inv(s) && #[trigger] stronger_next(s, s_prime) implies inv(s_prime) by {
        assert forall |msg| #[trigger] s_prime.in_flight().contains(msg) && resource_update_request_msg(sts_key)(msg) implies
        msg.content.get_update_request().obj.metadata.resource_version is Some
        && msg.content.get_update_request().obj.metadata.resource_version->0 < s_prime.api_server.resource_version_counter by {
            let step = choose |step| cluster.next_step(s, s_prime, step);
            if s.in_flight().contains(msg) {
                assert(s.api_server.resource_version_counter <= s_prime.api_server.resource_version_counter);
            } else if resource_update_request_msg(sts_key)(msg) {
                lemma_resource_update_request_msg_implies_key_in_reconcile_equals(controller_id, cluster, sub_resource, rabbitmq, s, s_prime, msg, step);
                let resp = step->ControllerStep_0.1->0;
                assert(is_ok_get_response_msg()(resp));
            }
        }
    }
    init_invariant(spec, cluster.init(), stronger_next, inv);
}

}
