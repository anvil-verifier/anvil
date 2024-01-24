// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::{EmptyAPI, EmptyTypeView};
use crate::fluent_controller::fluentbit::{
    model::{reconciler::*, resource::*},
    proof::{
        helper_invariants::{owner_ref::*, predicate::*, proof::*, validation::*},
        predicate::*,
        resource::*,
    },
    trusted::{spec_types::*, step::*},
};
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
use crate::vstd_ext::{multiset_lib, seq_lib, string_view::*};
use vstd::{multiset::*, prelude::*, string::*};

verus! {

// This module is to prove that for every subresource object, it satisfies some properties as long as it exists in etcd
// regardless of when it was created or how many times it has been updated or what its owner references point to.
// Right now only the `unchangeable` spec functions are proved by this. But actually things like
// `resource_object_has_no_finalizers_or_timestamp_and_only_has_controller_owner_ref` can also use the following lemmas.
// And the following lemmas are more powerful because it considers the cases when the objects in update request messages
// and etcd rely on each other to show they satisfy those properties.

/// Objects in create request messages satisfying the properties can be proved along because it doesn't have to do with
/// how the objects in etcd look like now.
pub open spec fn object_in_every_create_request_msg_satisfies_unchangeable(sub_resource: SubResource, fb: FluentBitView) -> StatePred<FBCluster> {
    let resource_key = get_request(sub_resource, fb).key;
    |s: FBCluster| {
        forall |msg: FBMessage|
            #[trigger] s.in_flight().contains(msg)
            && resource_create_request_msg(resource_key)(msg)
            ==> unchangeable(sub_resource, msg.content.get_create_request().obj, fb)
    }
}

/// On the contrary, we should combine the proof of update request message and etcd because they rely on each other.
pub open spec fn object_in_every_update_request_msg_satisfies_unchangeable(sub_resource: SubResource, fb: FluentBitView) -> StatePred<FBCluster> {
    let resource_key = get_request(sub_resource, fb).key;
    |s: FBCluster| {
        forall |msg: FBMessage|
            #[trigger] s.in_flight().contains(msg)
            && resource_update_request_msg(resource_key)(msg)
            && s.resources().contains_key(resource_key)
            && s.resources()[resource_key].metadata.resource_version == msg.content.get_update_request().obj.metadata.resource_version
            ==> unchangeable(sub_resource, msg.content.get_update_request().obj, fb)
    }
}

proof fn lemma_always_object_in_every_create_request_msg_satisfies_unchangeable(spec: TempPred<FBCluster>, sub_resource: SubResource, fb: FluentBitView)
    requires
        spec.entails(lift_state(FBCluster::init())),
        spec.entails(always(lift_action(FBCluster::next()))),
    ensures spec.entails(always(lift_state(object_in_every_create_request_msg_satisfies_unchangeable(sub_resource, fb)))),
{
    let inv = object_in_every_create_request_msg_satisfies_unchangeable(sub_resource, fb);
    let next = |s, s_prime| {
        &&& FBCluster::next()(s, s_prime)
        &&& FBCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
    };
    FBCluster::lemma_always_each_object_in_etcd_is_well_formed(spec);
    FBCluster::lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec);
    combine_spec_entails_always_n!(
        spec, lift_action(next),
        lift_action(FBCluster::next()),
        lift_state(FBCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata())
    );
    let resource_key = get_request(sub_resource, fb).key;
    assert forall |s: FBCluster, s_prime: FBCluster| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        assert forall |msg: FBMessage| #[trigger] s_prime.in_flight().contains(msg) && resource_create_request_msg(resource_key)(msg)
        implies unchangeable(sub_resource, msg.content.get_create_request().obj, fb) by {
            if !s.in_flight().contains(msg) {
                let step = choose |step| FBCluster::next_step(s, s_prime, step);
                lemma_resource_create_or_update_request_msg_implies_key_in_reconcile_equals(sub_resource, fb, s, s_prime, msg, step);
                match sub_resource {
                    SubResource::RoleBinding => {
                        RoleBindingView::marshal_preserves_integrity();
                    },
                    SubResource::ServiceAccount => {
                        ServiceAccountView::marshal_preserves_integrity();
                    },
                    SubResource::Service => {
                        ServiceView::marshal_preserves_integrity();
                    },
                    SubResource::DaemonSet => {
                        DaemonSetView::marshal_preserves_integrity();
                    },
                    _ => {},
                }
            }
        }
    }
    init_invariant(spec, FBCluster::init(), next, inv);
}

pub proof fn lemma_always_object_in_etcd_satisfies_unchangeable(spec: TempPred<FBCluster>, sub_resource: SubResource, fb: FluentBitView)
    requires
        spec.entails(lift_state(FBCluster::init())),
        spec.entails(always(lift_action(FBCluster::next()))),
    ensures spec.entails(always(lift_state(object_in_etcd_satisfies_unchangeable(sub_resource, fb)))),
{
    let inv = |s: FBCluster| {
        &&& object_in_etcd_satisfies_unchangeable(sub_resource, fb)(s)
        &&& object_in_every_update_request_msg_satisfies_unchangeable(sub_resource, fb)(s)
    };
    let resource_key = get_request(sub_resource, fb).key;
    let next = |s: FBCluster, s_prime: FBCluster| {
        &&& FBCluster::next()(s, s_prime)
        &&& FBCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s)
        &&& FBCluster::each_object_in_etcd_is_well_formed()(s)
        &&& FBCluster::each_object_in_etcd_is_well_formed()(s_prime)
        &&& FBCluster::object_in_ok_get_resp_is_same_as_etcd_with_same_rv(resource_key)(s)
        &&& object_in_resource_update_request_msg_has_smaller_rv_than_etcd(sub_resource, fb)(s)
        &&& object_in_every_create_request_msg_satisfies_unchangeable(sub_resource, fb)(s)
        &&& response_at_after_get_resource_step_is_resource_get_response(sub_resource, fb)(s)
    };
    FBCluster::lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(spec);
    FBCluster::lemma_always_each_object_in_etcd_is_well_formed(spec);
    always_to_always_later(spec, lift_state(FBCluster::each_object_in_etcd_is_well_formed()));
    FBCluster::lemma_always_object_in_ok_get_resp_is_same_as_etcd_with_same_rv(spec, resource_key);
    lemma_always_object_in_resource_update_request_msg_has_smaller_rv_than_etcd(spec, sub_resource, fb);
    lemma_always_object_in_every_create_request_msg_satisfies_unchangeable(spec, sub_resource, fb);
    lemma_always_response_at_after_get_resource_step_is_resource_get_response(spec, sub_resource, fb);
    combine_spec_entails_always_n!(
        spec, lift_action(next), lift_action(FBCluster::next()),
        lift_state(FBCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()),
        lift_state(FBCluster::each_object_in_etcd_is_well_formed()),
        later(lift_state(FBCluster::each_object_in_etcd_is_well_formed())),
        lift_state(FBCluster::object_in_ok_get_resp_is_same_as_etcd_with_same_rv(resource_key)),
        lift_state(object_in_resource_update_request_msg_has_smaller_rv_than_etcd(sub_resource, fb)),
        lift_state(object_in_every_create_request_msg_satisfies_unchangeable(sub_resource, fb)),
        lift_state(response_at_after_get_resource_step_is_resource_get_response(sub_resource, fb))
    );
    assert forall |s: FBCluster, s_prime: FBCluster| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        object_in_etcd_satisfies_unchangeable_induction(sub_resource, fb, s, s_prime);
        object_in_every_update_request_msg_satisfies_unchangeable_induction(sub_resource, fb, s, s_prime);
    }
    init_invariant(spec, FBCluster::init(), next, inv);
    always_weaken_temp(spec, lift_state(inv), lift_state(object_in_etcd_satisfies_unchangeable(sub_resource, fb)));
}

pub proof fn object_in_etcd_satisfies_unchangeable_induction(sub_resource: SubResource, fb: FluentBitView, s: FBCluster, s_prime: FBCluster)
    requires
        object_in_every_update_request_msg_satisfies_unchangeable(sub_resource, fb)(s),
        object_in_every_create_request_msg_satisfies_unchangeable(sub_resource, fb)(s),
        FBCluster::next()(s, s_prime),
        FBCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s),
        FBCluster::each_object_in_etcd_is_well_formed()(s),
        FBCluster::each_object_in_etcd_is_well_formed()(s_prime),
        object_in_resource_update_request_msg_has_smaller_rv_than_etcd(sub_resource, fb)(s),
        object_in_etcd_satisfies_unchangeable(sub_resource, fb)(s),
    ensures object_in_etcd_satisfies_unchangeable(sub_resource, fb)(s_prime),
{
    let resource_key = get_request(sub_resource, fb).key;
    if s_prime.resources().contains_key(resource_key) {
        match sub_resource {
            SubResource::RoleBinding => {
                RoleBindingView::marshal_preserves_integrity();
                RoleBindingView::marshal_spec_preserves_integrity();
            },
            SubResource::ServiceAccount => {
                ServiceAccountView::marshal_preserves_integrity();
                ServiceAccountView::marshal_spec_preserves_integrity();
            },
            SubResource::Service => {
                ServiceView::marshal_preserves_integrity();
                ServiceView::marshal_spec_preserves_integrity();
            },
            SubResource::DaemonSet => {
                DaemonSetView::marshal_preserves_integrity();
                DaemonSetView::marshal_spec_preserves_integrity();
            },
            _ => {},
        }
        let step = choose |step| FBCluster::next_step(s, s_prime, step);
        match step {
            Step::ApiServerStep(input) => {
                let req = input.get_Some_0();
                if resource_update_request_msg(resource_key)(req) {} else {}
            },
            _ => {}
        }
    }
}

pub proof fn object_in_every_update_request_msg_satisfies_unchangeable_induction(sub_resource: SubResource, fb: FluentBitView, s: FBCluster, s_prime: FBCluster)
    requires
        object_in_every_update_request_msg_satisfies_unchangeable(sub_resource, fb)(s),
        FBCluster::next()(s, s_prime),
        FBCluster::each_object_in_reconcile_has_consistent_key_and_valid_metadata()(s),
        FBCluster::each_object_in_etcd_is_well_formed()(s),
        FBCluster::object_in_ok_get_resp_is_same_as_etcd_with_same_rv(get_request(sub_resource, fb).key)(s),
        response_at_after_get_resource_step_is_resource_get_response(sub_resource, fb)(s),
        object_in_resource_update_request_msg_has_smaller_rv_than_etcd(sub_resource, fb)(s),
        object_in_etcd_satisfies_unchangeable(sub_resource, fb)(s),
    ensures object_in_every_update_request_msg_satisfies_unchangeable(sub_resource, fb)(s_prime),
{
    let resource_key = get_request(sub_resource, fb).key;
    assert forall |msg: FBMessage| #[trigger] s_prime.in_flight().contains(msg) && resource_update_request_msg(resource_key)(msg)
    && s_prime.resources().contains_key(resource_key) && s_prime.resources()[resource_key].metadata.resource_version == msg.content.get_update_request().obj.metadata.resource_version
    implies unchangeable(sub_resource, msg.content.get_update_request().obj, fb) by {
        if s.in_flight().contains(msg) {
            if s.resources().contains_key(resource_key) {
                if s.resources()[resource_key].metadata.resource_version == msg.content.get_update_request().obj.metadata.resource_version {
                    assert(unchangeable(sub_resource, msg.content.get_update_request().obj, fb));
                } else {
                    assert(s_prime.resources()[resource_key].metadata.resource_version.get_Some_0() == s.kubernetes_api_state.resource_version_counter);
                }
            } else {
                assert(s_prime.resources()[resource_key].metadata.resource_version.get_Some_0() == s.kubernetes_api_state.resource_version_counter);
            }
            assert(unchangeable(sub_resource, msg.content.get_update_request().obj, fb));
        } else {
            let step = choose |step| FBCluster::next_step(s, s_prime, step);
            lemma_resource_create_or_update_request_msg_implies_key_in_reconcile_equals(sub_resource, fb, s, s_prime, msg, step);
            match sub_resource {
                SubResource::RoleBinding => {
                    RoleBindingView::marshal_preserves_integrity();
                },
                SubResource::ServiceAccount => {
                    ServiceAccountView::marshal_preserves_integrity();
                },
                SubResource::Service => {
                    ServiceView::marshal_preserves_integrity();
                }
                SubResource::DaemonSet => {
                    DaemonSetView::marshal_preserves_integrity();
                },
                _ => {},
            }
        }
    }
}


}
