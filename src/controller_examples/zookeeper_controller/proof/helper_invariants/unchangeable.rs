// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::{EmptyAPI, EmptyTypeView};
use crate::kubernetes_api_objects::spec::{
    api_method::*, common::*, dynamic::*, owner_reference::*, prelude::*, resource::*,
};
use crate::kubernetes_cluster::spec::{
    cluster::*,
    cluster_state_machine::Step,
    controller::types::{ControllerActionInput, ControllerStep},
    message::*,
};
use crate::reconciler::spec::{reconciler::*, resource_builder::*};
use crate::temporal_logic::{defs::*, rules::*};
use crate::vstd_ext::{multiset_lib, seq_lib::*, string_view::*};
use crate::zookeeper_controller::{
    model::{reconciler::*, resource::*},
    proof::{
        helper_invariants::{owner_ref::*, predicate::*, proof::*, validation::*},
        predicate::*,
        resource::*,
    },
    trusted::{
        config_map::*, spec_types::*, step::*, zookeeper_api_spec::validate_config_map_data,
    },
};
use vstd::{multiset::*, prelude::*, seq_lib::*, string::*};

verus! {

// This module is to prove that for every subresource object, it satisfies some properties as long as it exists in etcd
// regardless of when it was created or how many times it has been updated or what its owner references point to.
// Right now only the `unchangeable` spec functions are proved by this. But actually things like
// `resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref` can also use the following lemmas.
// And the following lemmas are more powerful because it considers the cases when the objects in update request messages
// and etcd rely on each other to show they satisfy those properties.

/// Objects in create request messages satisfying the properties can be proved along because it doesn't have to do with
/// how the objects in etcd look like now.
pub open spec fn object_in_every_create_request_msg_satisfies_unchangeable(sub_resource: SubResource, zookeeper: ZookeeperClusterView) -> StatePred<ZKCluster> {
    let resource_key = get_request(sub_resource, zookeeper).key;
    |s: ZKCluster| {
        forall |msg: ZKMessage|
            s.in_flight().contains(msg)
            && #[trigger] resource_create_request_msg(get_request(sub_resource, zookeeper).key)(msg)
            ==> unchangeable(sub_resource, msg.content.get_create_request().obj, zookeeper)
    }
}

/// On the contrary, we should combine the proof of update request message and etcd because they rely on each other.
pub open spec fn object_in_every_update_request_msg_satisfies_unchangeable(sub_resource: SubResource, zookeeper: ZookeeperClusterView) -> StatePred<ZKCluster> {
    let resource_key = get_request(sub_resource, zookeeper).key;
    |s: ZKCluster| {
        forall |msg: ZKMessage|
            s.in_flight().contains(msg)
            && #[trigger] resource_update_request_msg(get_request(sub_resource, zookeeper).key)(msg)
            && s.resources().contains_key(resource_key)
            && s.resources()[resource_key].metadata.resource_version == msg.content.get_update_request().obj.metadata.resource_version
            ==> unchangeable(sub_resource, msg.content.get_update_request().obj, zookeeper)
    }
}

proof fn lemma_always_object_in_every_create_request_msg_satisfies_unchangeable(spec: TempPred<ZKCluster>, sub_resource: SubResource, zookeeper: ZookeeperClusterView)
    requires
        spec.entails(lift_state(ZKCluster::init())),
        spec.entails(always(lift_action(ZKCluster::next()))),
    ensures spec.entails(always(lift_state(object_in_every_create_request_msg_satisfies_unchangeable(sub_resource, zookeeper)))),
{
    let inv = object_in_every_create_request_msg_satisfies_unchangeable(sub_resource, zookeeper);
    let next = |s, s_prime| {
        &&& ZKCluster::next()(s, s_prime)
        &&& ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
        &&& the_object_in_reconcile_satisfies_state_validation(zookeeper.object_ref())(s)
    };
    ZKCluster::lemma_always_each_object_in_etcd_is_well_formed(spec);
    ZKCluster::lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec);
    lemma_always_the_object_in_reconcile_satisfies_state_validation(spec, zookeeper.object_ref());
    combine_spec_entails_always_n!(
        spec, lift_action(next),
        lift_action(ZKCluster::next()),
        lift_state(ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        lift_state(the_object_in_reconcile_satisfies_state_validation(zookeeper.object_ref()))
    );
    let resource_key = get_request(sub_resource, zookeeper).key;
    assert forall |s: ZKCluster, s_prime: ZKCluster| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        assert forall |msg: ZKMessage| s_prime.in_flight().contains(msg) && #[trigger] resource_create_request_msg(resource_key)(msg)
        implies unchangeable(sub_resource, msg.content.get_create_request().obj, zookeeper) by {
            if !s.in_flight().contains(msg) {
                let step = choose |step| ZKCluster::next_step(s, s_prime, step);
                lemma_resource_create_or_update_request_msg_implies_key_in_reconcile_equals(sub_resource, zookeeper, s, s_prime, msg, step);
                match sub_resource {
                    SubResource::ConfigMap => {
                        ConfigMapView::marshal_preserves_integrity();
                        ConfigMapView::marshal_spec_preserves_integrity();
                        made_config_map_data_satisfies_validation(s.ongoing_reconciles()[zookeeper.object_ref()].triggering_cr);
                    },
                    SubResource::StatefulSet => {
                        StatefulSetView::marshal_preserves_integrity();
                        StatefulSetView::marshal_spec_preserves_integrity();
                    },
                    _ => {},
                }
            }
        }
    }
    init_invariant(spec, ZKCluster::init(), next, inv);
}

pub proof fn lemma_always_object_in_etcd_satisfies_unchangeable(spec: TempPred<ZKCluster>, sub_resource: SubResource, zookeeper: ZookeeperClusterView)
    requires
        spec.entails(lift_state(ZKCluster::init())),
        spec.entails(always(lift_action(ZKCluster::next()))),
    ensures spec.entails(always(lift_state(object_in_etcd_satisfies_unchangeable(sub_resource, zookeeper)))),
{
    let inv = |s: ZKCluster| {
        &&& object_in_etcd_satisfies_unchangeable(sub_resource, zookeeper)(s)
        &&& object_in_every_update_request_msg_satisfies_unchangeable(sub_resource, zookeeper)(s)
    };
    let resource_key = get_request(sub_resource, zookeeper).key;
    let next = |s: ZKCluster, s_prime: ZKCluster| {
        &&& ZKCluster::next()(s, s_prime)
        &&& ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
        &&& ZKCluster::each_object_in_etcd_is_well_formed()(s)
        &&& ZKCluster::each_object_in_etcd_is_well_formed()(s_prime)
        &&& ZKCluster::object_in_ok_get_resp_is_same_as_etcd_with_same_rv(resource_key)(s)
        &&& object_in_resource_update_request_msg_has_smaller_rv_than_etcd(sub_resource, zookeeper)(s)
        &&& object_in_every_create_request_msg_satisfies_unchangeable(sub_resource, zookeeper)(s)
        &&& response_at_after_get_resource_step_is_resource_get_response(sub_resource, zookeeper)(s)
        &&& the_object_in_reconcile_satisfies_state_validation(zookeeper.object_ref())(s)
    };
    ZKCluster::lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec);
    ZKCluster::lemma_always_each_object_in_etcd_is_well_formed(spec);
    always_to_always_later(spec, lift_state(ZKCluster::each_object_in_etcd_is_well_formed()));
    ZKCluster::lemma_always_object_in_ok_get_resp_is_same_as_etcd_with_same_rv(spec, resource_key);
    lemma_always_object_in_resource_update_request_msg_has_smaller_rv_than_etcd(spec, sub_resource, zookeeper);
    lemma_always_object_in_every_create_request_msg_satisfies_unchangeable(spec, sub_resource, zookeeper);
    lemma_always_response_at_after_get_resource_step_is_resource_get_response(spec, sub_resource, zookeeper);
    lemma_always_the_object_in_reconcile_satisfies_state_validation(spec, zookeeper.object_ref());
    combine_spec_entails_always_n!(
        spec, lift_action(next), lift_action(ZKCluster::next()),
        lift_state(ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        lift_state(ZKCluster::each_object_in_etcd_is_well_formed()),
        later(lift_state(ZKCluster::each_object_in_etcd_is_well_formed())),
        lift_state(ZKCluster::object_in_ok_get_resp_is_same_as_etcd_with_same_rv(resource_key)),
        lift_state(object_in_resource_update_request_msg_has_smaller_rv_than_etcd(sub_resource, zookeeper)),
        lift_state(object_in_every_create_request_msg_satisfies_unchangeable(sub_resource, zookeeper)),
        lift_state(response_at_after_get_resource_step_is_resource_get_response(sub_resource, zookeeper)),
        lift_state(the_object_in_reconcile_satisfies_state_validation(zookeeper.object_ref()))
    );
    assert forall |s: ZKCluster, s_prime: ZKCluster| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        object_in_etcd_satisfies_unchangeable_induction(sub_resource, zookeeper, s, s_prime);
        object_in_every_update_request_msg_satisfies_unchangeable_induction(sub_resource, zookeeper, s, s_prime);
    }
    init_invariant(spec, ZKCluster::init(), next, inv);
    always_weaken_temp(spec, lift_state(inv), lift_state(object_in_etcd_satisfies_unchangeable(sub_resource, zookeeper)));
}

pub proof fn object_in_etcd_satisfies_unchangeable_induction(sub_resource: SubResource, zookeeper: ZookeeperClusterView, s: ZKCluster, s_prime: ZKCluster)
    requires
        object_in_every_update_request_msg_satisfies_unchangeable(sub_resource, zookeeper)(s),
        object_in_every_create_request_msg_satisfies_unchangeable(sub_resource, zookeeper)(s),
        ZKCluster::next()(s, s_prime),
        ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s),
        ZKCluster::each_object_in_etcd_is_well_formed()(s),
        ZKCluster::each_object_in_etcd_is_well_formed()(s_prime),
        object_in_resource_update_request_msg_has_smaller_rv_than_etcd(sub_resource, zookeeper)(s),
        object_in_etcd_satisfies_unchangeable(sub_resource, zookeeper)(s),
    ensures object_in_etcd_satisfies_unchangeable(sub_resource, zookeeper)(s_prime),
{
    let resource_key = get_request(sub_resource, zookeeper).key;
    let step = choose |step| ZKCluster::next_step(s, s_prime, step);
    if s_prime.resources().contains_key(resource_key) {
        match sub_resource {
            SubResource::ConfigMap => {
                ConfigMapView::marshal_preserves_integrity();
                ConfigMapView::marshal_spec_preserves_integrity();
            },
            SubResource::StatefulSet => {
                StatefulSetView::marshal_preserves_integrity();
                StatefulSetView::marshal_spec_preserves_integrity();
            },
            _ => {},
        }
        match step {
            Step::ApiServerStep(input) => {
                let req = input.get_Some_0();
                if resource_create_request_msg(resource_key)(req) {} else {}
                if resource_update_request_msg(resource_key)(req) {} else {}
            },
            _ => {}
        }
    }
}

pub proof fn object_in_every_update_request_msg_satisfies_unchangeable_induction(sub_resource: SubResource, zookeeper: ZookeeperClusterView, s: ZKCluster, s_prime: ZKCluster)
    requires
        object_in_every_update_request_msg_satisfies_unchangeable(sub_resource, zookeeper)(s),
        ZKCluster::next()(s, s_prime),
        ZKCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s),
        ZKCluster::each_object_in_etcd_is_well_formed()(s),
        ZKCluster::object_in_ok_get_resp_is_same_as_etcd_with_same_rv(get_request(sub_resource, zookeeper).key)(s),
        response_at_after_get_resource_step_is_resource_get_response(sub_resource, zookeeper)(s),
        object_in_resource_update_request_msg_has_smaller_rv_than_etcd(sub_resource, zookeeper)(s),
        object_in_etcd_satisfies_unchangeable(sub_resource, zookeeper)(s),
        the_object_in_reconcile_satisfies_state_validation(zookeeper.object_ref())(s),
    ensures object_in_every_update_request_msg_satisfies_unchangeable(sub_resource, zookeeper)(s_prime),
{
    let resource_key = get_request(sub_resource, zookeeper).key;
    assert forall |msg: ZKMessage| s_prime.in_flight().contains(msg) && #[trigger] resource_update_request_msg(resource_key)(msg)
    && s_prime.resources().contains_key(resource_key) && s_prime.resources()[resource_key].metadata.resource_version == msg.content.get_update_request().obj.metadata.resource_version
    implies unchangeable(sub_resource, msg.content.get_update_request().obj, zookeeper) by {
        if s.in_flight().contains(msg) {
            if s.resources().contains_key(resource_key) {
                if s.resources()[resource_key].metadata.resource_version == msg.content.get_update_request().obj.metadata.resource_version {
                    assert(unchangeable(sub_resource, msg.content.get_update_request().obj, zookeeper));
                } else {
                    assert(s_prime.resources()[resource_key].metadata.resource_version.get_Some_0() == s.kubernetes_api_state.resource_version_counter);
                }
            } else {
                assert(s_prime.resources()[resource_key].metadata.resource_version.get_Some_0() == s.kubernetes_api_state.resource_version_counter);
            }
            assert(unchangeable(sub_resource, msg.content.get_update_request().obj, zookeeper));
        } else {
            let step = choose |step| ZKCluster::next_step(s, s_prime, step);
            lemma_resource_create_or_update_request_msg_implies_key_in_reconcile_equals(sub_resource, zookeeper, s, s_prime, msg, step);
            match sub_resource {
                SubResource::ConfigMap => {
                    ConfigMapView::marshal_preserves_integrity();
                    ConfigMapView::marshal_spec_preserves_integrity();
                    made_config_map_data_satisfies_validation(s.ongoing_reconciles()[zookeeper.object_ref()].triggering_cr);
                },
                SubResource::StatefulSet => {
                    StatefulSetView::marshal_preserves_integrity();
                    StatefulSetView::marshal_spec_preserves_integrity();
                },
                _ => {},
            }
        }
    }
}

proof fn made_config_map_data_satisfies_validation(zookeeper: ZookeeperClusterView)
    requires zookeeper.state_validation(),
    ensures
        make_config_map(zookeeper).data.is_Some(),
        validate_config_map_data(make_config_map(zookeeper).data.get_Some_0()),
{
    let data = make_config_map(zookeeper).data.get_Some_0();
    reveal_strlit("zoo.cfg");
    reveal_strlit("log4j.properties");
    reveal_strlit("log4j-quiet.properties");
    reveal_strlit("env.sh");
    assert(new_strlit("zoo.cfg")@.len() == 7);
    assert(data.contains_key(new_strlit("zoo.cfg")@));
    let zk_config = make_zk_config(zookeeper);
    assert(data[new_strlit("zoo.cfg")@] == zk_config);
}

}
