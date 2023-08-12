// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::{
    api_method::*, common::*, dynamic::*, resource::*, stateful_set::*,
};
use crate::kubernetes_cluster::spec::{
    cluster::*,
    cluster_state_machine::Step,
    controller::common::{controller_req_msg, ControllerActionInput, ControllerStep},
    message::*,
};
use crate::rabbitmq_controller::{
    common::*,
    proof::{common::*, helper_invariants, terminate},
    spec::{rabbitmqcluster::*, reconciler::*},
};
use crate::temporal_logic::{defs::*, rules::*};
use vstd::prelude::*;

verus! {

pub open spec fn stateful_set_has_no_larger_replicas_than_rabbitmq(key: ObjectRef) -> StatePred<RMQCluster> {
    |s: RMQCluster| {
        let rabbitmq = RabbitmqClusterView::from_dynamic_object(s.resource_obj_of(key)).get_Ok_0();
        key.kind.is_CustomResourceKind()
        && s.resource_key_exists(key)
        && s.resource_key_exists(make_stateful_set_key(key))
        && s.resource_obj_of(make_stateful_set_key(key)).metadata.owner_references.is_Some()
        && s.resource_obj_of(make_stateful_set_key(key)).metadata.owner_references.get_Some_0().contains(rabbitmq.controller_owner_ref())
        ==> (
            StatefulSetView::from_dynamic_object(s.resource_obj_of(make_stateful_set_key(key))).is_Ok()
            && StatefulSetView::from_dynamic_object(s.resource_obj_of(make_stateful_set_key(key))).get_Ok_0().spec.get_Some_0().replicas.get_Some_0() <= rabbitmq.spec.replicas
        )
    }
}

#[verifier(external_body)]
pub proof fn lemma_always_stateful_set_has_no_larger_replicas_than_rabbitmq(spec: TempPred<RMQCluster>, key: ObjectRef)
    requires
        spec.entails(lift_state(RMQCluster::init())),
        spec.entails(always(lift_action(RMQCluster::next()))),
    ensures
        spec.entails(
            always(lift_state(stateful_set_has_no_larger_replicas_than_rabbitmq(key)))
        ),
{
    let invariant = stateful_set_has_no_larger_replicas_than_rabbitmq(key);
    let stronger_next = |s, s_prime: RMQCluster| {
        RMQCluster::next()(s, s_prime)
        && RMQCluster::each_object_in_etcd_is_well_formed()(s)
    };
    RMQCluster::lemma_always_each_object_in_etcd_is_well_formed(spec);
    entails_always_and_n!(
        spec,
        lift_action(RMQCluster::next()),
        lift_state(RMQCluster::each_object_in_etcd_is_well_formed())
    );
    temp_pred_equality(
        lift_action(RMQCluster::next())
        .and(lift_state(RMQCluster::each_object_in_etcd_is_well_formed())),
        lift_action(stronger_next)
    );
    assert forall |s, s_prime| invariant(s) && #[trigger] stronger_next(s, s_prime) implies invariant(s_prime) by {
        let rabbitmq = RabbitmqClusterView::from_dynamic_object(s_prime.resource_obj_of(key)).get_Ok_0();
        if key.kind.is_CustomResourceKind() && s_prime.resource_key_exists(key) && s_prime.resource_key_exists(make_stateful_set_key(key))
        && s_prime.resource_obj_of(make_stateful_set_key(key)).metadata.owner_references.is_Some()
        && s_prime.resource_obj_of(make_stateful_set_key(key)).metadata.owner_references.get_Some_0().contains(rabbitmq.controller_owner_ref()) {
            assert(RabbitmqClusterView::from_dynamic_object(s_prime.resource_obj_of(key)).is_Ok());
            let step = choose |step| RMQCluster::next_step(s, s_prime, step);
            match step {
                Step::KubernetesAPIStep(input) => {

                },
                _ => {}
            }
        }
    }
    init_invariant(spec, RMQCluster::init(), stronger_next, invariant);
}

}
