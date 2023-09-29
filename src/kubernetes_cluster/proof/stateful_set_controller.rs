// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::ExternalAPI;
use crate::kubernetes_api_objects::{error::*, prelude::*};
use crate::kubernetes_cluster::spec::{
    builtin_controllers::types::*, cluster::*, cluster_state_machine::Step,
    kubernetes_api::common::KubernetesAPIAction, message::*,
};
use crate::reconciler::spec::reconciler::Reconciler;
use crate::temporal_logic::defs::*;
use crate::temporal_logic::rules::*;
use crate::vstd_ext::multiset_lib::*;
use vstd::assert_multisets_equal;
use vstd::prelude::*;

verus! {

impl <K: ResourceView, E: ExternalAPI, R: Reconciler<K, E>> Cluster<K, E, R> {

pub open spec fn every_in_flight_update_req_msg_for_this_object_satisfies(
    key: ObjectRef, requirements: DynamicObjectMutViewPred
) -> StatePred<Self> {
    |s: Self| {
        forall |msg: MsgType<E>|
            #[trigger] s.in_flight().contains(msg)
            && msg.dst.is_KubernetesAPI()
            && msg.content.is_update_request()
            && msg.content.get_update_request().key() == key
            ==> requirements(msg.content.get_update_request().obj.mutable_subset())
    }
}

pub open spec fn this_object_exists(key: ObjectRef) -> StatePred<Self> {
    |s: Self| {
        s.resources().contains_key(key)
    }
}

pub open spec fn this_object_satisfies(key: ObjectRef, requirements: DynamicObjectMutViewPred) -> StatePred<Self> {
    |s: Self| {
        &&& s.resources().contains_key(key)
        &&& requirements(s.resources()[key].mutable_subset())
    }
}

pub open spec fn this_object_is_stable(key: ObjectRef) -> StatePred<Self> {
    |s: Self| {
        &&& s.stable_resources().contains(key)
    }
}

pub open spec fn no_status_update_req_msg_for_this_object(key: ObjectRef) -> StatePred<Self> {
    |s: Self| {
        forall |msg: MsgType<E>|
            #![trigger s.in_flight().contains(msg)]
            msg.dst.is_KubernetesAPI()
            && msg.content.is_update_status_request()
            && msg.content.get_update_status_request().key() == key
            ==> !s.in_flight().contains(msg)
    }
}

/// This lemma shows that if spec ensures the stateful set object (identified by the key) always exists and
/// every update request for this stateful set object satisfies some requirements,
/// the system will eventually reaches a state where either the stateful set object is
/// updated to always satisfy that requirement,
/// or there is never update_status request for this stateful set object
/// (which means any following update request does not need to compete with update_state request).

#[verifier(external_body)]
pub proof fn lemma_true_leads_to_always_stateful_set_satisfies_or_no_update_status_req_msg(
    spec: TempPred<Self>, key: ObjectRef, requirements: DynamicObjectMutViewPred
)
    requires
        key.kind == StatefulSetView::kind(),
        spec.entails(always(lift_state(Self::this_object_exists(key)))),
        spec.entails(always(lift_state(Self::every_in_flight_update_req_msg_for_this_object_satisfies(key, requirements)))),
        spec.entails(always(lift_action(Self::next()))),
        spec.entails(tla_forall(|i| Self::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| Self::builtin_controllers_next().weak_fairness(i))),
    ensures
        spec.entails(
            true_pred().leads_to(always(lift_state(
                |s: Self| {
                    ||| Self::this_object_satisfies(key, requirements)(s)
                    ||| Self::no_status_update_req_msg_for_this_object(key)(s)
                }
            )))
        ),
{}

pub proof fn lemma_true_leads_to_stateful_set_is_stable(spec: TempPred<Self>, key: ObjectRef)
    requires
        key.kind == StatefulSetView::kind(),
        spec.entails(always(lift_state(Self::this_object_exists(key)))),
        spec.entails(always(lift_action(Self::next()))),
        spec.entails(tla_forall(|i| Self::builtin_controllers_next().weak_fairness(i))),
    ensures
        spec.entails(true_pred().leads_to(lift_state(Self::this_object_is_stable(key)))),
{
    let pre = |s: Self| true;
    let post = Self::this_object_is_stable(key);

    let input = (BuiltinControllerChoice::Stabilizer, key);
    let stronger_next = |s, s_prime: Self| {
        &&& Self::next()(s, s_prime)
        &&& Self::this_object_exists(key)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(Self::next()),
        lift_state(Self::this_object_exists(key))
    );

    Self::lemma_pre_leads_to_post_by_builtin_controllers_borrow_from_spec(
        spec, input, stronger_next, Self::run_stabilizer(), Self::this_object_exists(key), pre, post
    );
}

}

}
