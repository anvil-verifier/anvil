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

pub open spec fn no_status_update_req_msg_from_bc_for_this_object(key: ObjectRef) -> StatePred<Self> {
    |s: Self| {
        forall |msg: MsgType<E>|
            update_status_msg_from_bc_for(key)(msg) ==> !s.in_flight().contains(msg)
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
                    ||| Self::no_status_update_req_msg_from_bc_for_this_object(key)(s)
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

proof fn lemma_pending_update_status_req_num_is_n_leads_to_object_updated_or_no_more_pending_req(
    spec: TempPred<Self>, key: ObjectRef, requirements: DynamicObjectMutViewPred, msg_num: nat
)
    requires
        spec.entails(always(lift_action(Self::next()))),
        spec.entails(tla_forall(|i| Self::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(Self::this_object_exists(key)))),
        spec.entails(always(lift_state(Self::every_in_flight_update_req_msg_for_this_object_satisfies(key, requirements)))),
    ensures
        spec.entails(
            lift_state(|s: Self| {
                &&& s.in_flight().filter(update_status_msg_from_bc_for(key)).len() == msg_num
                &&& Self::this_object_is_stable(key)(s)
            }).leads_to(lift_state(
                |s: Self| {
                    ||| Self::this_object_satisfies(key, requirements)(s)
                    ||| {
                        &&& Self::no_status_update_req_msg_from_bc_for_this_object(key)(s)
                        &&& Self::this_object_is_stable(key)(s)
                    }
                }
            ))
        ),
    decreases msg_num
{
    let pre = |s: Self| {
        &&& s.in_flight().filter(update_status_msg_from_bc_for(key)).len() == msg_num
        &&& Self::this_object_is_stable(key)(s)
    };
    let post = |s: Self| {
        ||| Self::this_object_satisfies(key, requirements)(s)
        ||| {
            &&& Self::no_status_update_req_msg_from_bc_for_this_object(key)(s)
            &&& Self::this_object_is_stable(key)(s)
        }
    };
    if msg_num == 0 {
        assert_by(valid(lift_state(pre).implies(lift_state(post))), {
            assert forall |s| #[trigger] pre(s) implies post(s) by {
                assert forall |msg| update_status_msg_from_bc_for(key)(msg) implies !s.in_flight().contains(msg) by {
                    assert(s.in_flight().filter(update_status_msg_from_bc_for(key)).count(msg) == 0);
                }
            }
        });
        valid_implies_implies_leads_to(spec, lift_state(pre), lift_state(post));
    } else {
        let pre_concrete_msg = |msg: MsgType<E>| lift_state(|s: Self| {
            &&& s.in_flight().filter(update_status_msg_from_bc_for(key)).len() == msg_num
            &&& Self::this_object_is_stable(key)(s)
            &&& s.in_flight().filter(update_status_msg_from_bc_for(key)).count(msg) > 0
        });
        let pre_minus_one = lift_state(|s: Self| {
            &&& s.in_flight().filter(update_status_msg_from_bc_for(key)).len() == (msg_num - 1) as nat
            &&& Self::this_object_is_stable(key)(s)
        });
        let obj_updated = lift_state(Self::this_object_satisfies(key, requirements));
        let no_more_pending_req = lift_state(|s: Self| {
            &&& Self::no_status_update_req_msg_from_bc_for_this_object(key)(s)
            &&& Self::this_object_is_stable(key)(s)
        });
        let pre_minus_one_or_obj_updated = lift_state(|s: Self| {
            ||| Self::this_object_satisfies(key, requirements)(s)
            ||| {
                &&& s.in_flight().filter(update_status_msg_from_bc_for(key)).len() == (msg_num - 1) as nat
                &&& Self::this_object_is_stable(key)(s)
            }
        });
        assert_by(spec.entails(lift_state(pre).leads_to(pre_minus_one_or_obj_updated)), {
            assert forall |msg: MsgType<E>|
            spec.entails(#[trigger] pre_concrete_msg(msg).leads_to(pre_minus_one_or_obj_updated)) by {
                Self::object_updated_or_pending_update_status_requests_num_decreases(spec, key, requirements, msg_num, msg);
            }
            leads_to_exists_intro(spec, pre_concrete_msg, pre_minus_one_or_obj_updated);
            assert_by(tla_exists(pre_concrete_msg) == lift_state(pre), {
                assert forall |ex| #[trigger] lift_state(pre).satisfied_by(ex)
                implies tla_exists(pre_concrete_msg).satisfied_by(ex) by {
                    let msg = ex.head().in_flight().filter(update_status_msg_from_bc_for(key)).choose();
                    assert(ex.head().in_flight().filter(update_status_msg_from_bc_for(key)).count(msg) > 0);
                    assert(pre_concrete_msg(msg).satisfied_by(ex));
                }
                temp_pred_equality(tla_exists(pre_concrete_msg), lift_state(pre));
            });
        });
        Self::lemma_pending_update_status_req_num_is_n_leads_to_object_updated_or_no_more_pending_req(
            spec, key, requirements, (msg_num - 1) as nat
        );
        temp_pred_equality(pre_minus_one_or_obj_updated, pre_minus_one.or(obj_updated));
        temp_pred_equality(lift_state(post), no_more_pending_req.or(obj_updated));
        leads_to_shortcut_temp(spec, lift_state(pre), pre_minus_one, no_more_pending_req, obj_updated);
    }
}

proof fn object_updated_or_pending_update_status_requests_num_decreases(
    spec: TempPred<Self>, key: ObjectRef, requirements: DynamicObjectMutViewPred, msg_num: nat, msg: MsgType<E>
)
    requires
        msg_num > 0,
        spec.entails(always(lift_action(Self::next()))),
        spec.entails(tla_forall(|i| Self::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(Self::this_object_exists(key)))),
        spec.entails(always(lift_state(Self::every_in_flight_update_req_msg_for_this_object_satisfies(key, requirements)))),
    ensures
        spec.entails(
            lift_state(|s: Self| {
                &&& s.in_flight().filter(update_status_msg_from_bc_for(key)).len() == msg_num
                &&& Self::this_object_is_stable(key)(s)
                &&& s.in_flight().filter(update_status_msg_from_bc_for(key)).count(msg) > 0
            }).leads_to(lift_state(|s: Self| {
                ||| Self::this_object_satisfies(key, requirements)(s)
                ||| {
                    &&& s.in_flight().filter(update_status_msg_from_bc_for(key)).len() == (msg_num - 1) as nat
                    &&& Self::this_object_is_stable(key)(s)
                }
            }))
        ),
{
    let pre = |s: Self| {
        &&& s.in_flight().filter(update_status_msg_from_bc_for(key)).len() == msg_num
        &&& Self::this_object_is_stable(key)(s)
        &&& s.in_flight().filter(update_status_msg_from_bc_for(key)).count(msg) > 0
    };
    let post = |s: Self| {
        ||| Self::this_object_satisfies(key, requirements)(s)
        ||| {
            &&& s.in_flight().filter(update_status_msg_from_bc_for(key)).len() == (msg_num - 1) as nat
            &&& Self::this_object_is_stable(key)(s)
        }
    };
    let input = Some(msg);
    let stronger_next = |s, s_prime: Self| {
        &&& Self::next()(s, s_prime)
        &&& Self::this_object_exists(key)(s)
        &&& Self::every_in_flight_update_req_msg_for_this_object_satisfies(key, requirements)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(Self::next()),
        lift_state(Self::this_object_exists(key)),
        lift_state(Self::every_in_flight_update_req_msg_for_this_object_satisfies(key, requirements))
    );

    assert forall |s, s_prime: Self| pre(s) && #[trigger] stronger_next(s, s_prime)
    implies pre(s_prime) || post(s_prime) by {
        let pending_req_multiset = s.in_flight().filter(update_status_msg_from_bc_for(key));
        let pending_req_multiset_prime = s_prime.in_flight().filter(update_status_msg_from_bc_for(key));
        let step = choose |step| Self::next_step(s, s_prime, step);
        match step {
            Step::KubernetesAPIStep(input) => {
                if pending_req_multiset.count(input.get_Some_0()) > 0 {
                    assert(pending_req_multiset.remove(input.get_Some_0()) =~= pending_req_multiset_prime);
                    assert(Self::this_object_is_stable(key)(s_prime));
                } else {
                    assert(pending_req_multiset =~= pending_req_multiset_prime);
                    assert(Self::this_object_is_stable(key)(s_prime) || Self::this_object_satisfies(key, requirements)(s_prime));
                }
            },
            Step::FailTransientlyStep(input) => {
                if pending_req_multiset.count(input.0) > 0 {
                    assert(pending_req_multiset.remove(input.0) =~= pending_req_multiset_prime);
                } else {
                    assert(pending_req_multiset =~= pending_req_multiset_prime);
                }
            },
            Step::BuiltinControllersStep(input) => {
                assert(pending_req_multiset =~= pending_req_multiset_prime);
            },
            Step::ControllerStep(input) => {
                assert(pending_req_multiset =~= pending_req_multiset_prime);
            },
            Step::ClientStep() => {
                assert(pending_req_multiset =~= pending_req_multiset_prime);
            },
            Step::ExternalAPIStep(input) => {
                assert(pending_req_multiset =~= pending_req_multiset_prime);
            },
            _ => {}
        }
    }
    assert forall |s, s_prime: Self|
        pre(s) && #[trigger] stronger_next(s, s_prime) && Self::kubernetes_api_next().forward(input)(s, s_prime)
    implies post(s_prime) by {
        let pending_req_multiset = s.in_flight().filter(update_status_msg_from_bc_for(key));
        let pending_req_multiset_prime = s_prime.in_flight().filter(update_status_msg_from_bc_for(key));
        assert(pending_req_multiset.remove(msg) =~= pending_req_multiset_prime);
    }
    Self::lemma_pre_leads_to_post_by_kubernetes_api(
        spec, input, stronger_next, Self::handle_request(), pre, post
    );
}

}

}
