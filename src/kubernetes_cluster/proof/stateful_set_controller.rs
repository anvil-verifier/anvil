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

pub open spec fn every_in_flight_create_req_msg_for_this_object_satisfies(
    key: ObjectRef, requirements: DynamicObjectMutViewPred
) -> StatePred<Self> {
    |s: Self| {
        forall |msg: MsgType<E>|
            #[trigger] s.in_flight().contains(msg)
            && msg.dst.is_KubernetesAPI()
            && msg.content.is_create_request()
            && msg.content.get_create_request().namespace == key.namespace
            && msg.content.get_create_request().obj.kind == key.kind
            && msg.content.get_create_request().obj.metadata.name.is_Some()
            && msg.content.get_create_request().obj.metadata.name.get_Some_0() == key.name
            ==> requirements(msg.content.get_create_request().obj.mutable_subset())
    }
}

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

pub proof fn lemma_true_leads_to_always_object_not_exist_or_updated_or_no_more_pending_req(
    spec: TempPred<Self>, key: ObjectRef, requirements: DynamicObjectMutViewPred
)
    requires
        spec.entails(always(lift_action(Self::next()))),
        spec.entails(tla_forall(|i| Self::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| Self::builtin_controllers_next().weak_fairness(i))),
        spec.entails(always(lift_state(Self::every_in_flight_create_req_msg_for_this_object_satisfies(key, requirements)))),
        spec.entails(always(lift_state(Self::every_in_flight_update_req_msg_for_this_object_satisfies(key, requirements)))),
    ensures
        spec.entails(true_pred().leads_to(always(lift_state(
            |s: Self| {
                ||| !s.resources().contains_key(key)
                ||| Self::this_object_satisfies(key, requirements)(s)
                ||| {
                    &&& Self::no_status_update_req_msg_from_bc_for_this_object(key)(s)
                    &&& Self::this_object_is_stable(key)(s)
                }
            }
        )))),
{
    Self::lemma_true_leads_to_object_not_exist_or_updated_or_no_more_pending_req(spec, key, requirements);

    let post = |s: Self| {
        ||| !s.resources().contains_key(key)
        ||| Self::this_object_satisfies(key, requirements)(s)
        ||| {
            &&& Self::no_status_update_req_msg_from_bc_for_this_object(key)(s)
            &&& Self::this_object_is_stable(key)(s)
        }
    };
    let stronger_next = |s, s_prime: Self| {
        &&& Self::next()(s, s_prime)
        &&& Self::every_in_flight_create_req_msg_for_this_object_satisfies(key, requirements)(s)
        &&& Self::every_in_flight_update_req_msg_for_this_object_satisfies(key, requirements)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(Self::next()),
        lift_state(Self::every_in_flight_create_req_msg_for_this_object_satisfies(key, requirements)),
        lift_state(Self::every_in_flight_update_req_msg_for_this_object_satisfies(key, requirements))
    );

    assert forall |s, s_prime| post(s) && #[trigger] stronger_next(s, s_prime) implies post(s_prime) by {
        if !s.resources().contains_key(key) || Self::this_object_satisfies(key, requirements)(s) {
            // Trivial case.
        } else {
            assert forall |msg| update_status_msg_from_bc_for(key)(msg) implies !s_prime.in_flight().contains(msg) by {
                // Just need s.in_flight().contains(msg) to trigger the universal quantifier.
                if s.in_flight().contains(msg) {} else {}
            }
        }
    }

    leads_to_stable_temp(spec, lift_action(stronger_next), true_pred(), lift_state(post));
}

pub proof fn lemma_true_leads_to_object_not_exist_or_updated_or_no_more_pending_req(
    spec: TempPred<Self>, key: ObjectRef, requirements: DynamicObjectMutViewPred
)
    requires
        spec.entails(always(lift_action(Self::next()))),
        spec.entails(tla_forall(|i| Self::builtin_controllers_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| Self::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(Self::every_in_flight_create_req_msg_for_this_object_satisfies(key, requirements)))),
        spec.entails(always(lift_state(Self::every_in_flight_update_req_msg_for_this_object_satisfies(key, requirements)))),
    ensures
        spec.entails(true_pred().leads_to(lift_state(
            |s: Self| {
                ||| !s.resources().contains_key(key)
                ||| Self::this_object_satisfies(key, requirements)(s)
                ||| {
                    &&& Self::no_status_update_req_msg_from_bc_for_this_object(key)(s)
                    &&& Self::this_object_is_stable(key)(s)
                }
            }
        ))),
{
    let key_exists = |s: Self| s.resources().contains_key(key);
    let key_not_exists = |s: Self| !s.resources().contains_key(key);
    let post = |s: Self| {
        ||| !s.resources().contains_key(key)
        ||| Self::this_object_satisfies(key, requirements)(s)
        ||| {
            &&& Self::no_status_update_req_msg_from_bc_for_this_object(key)(s)
            &&& Self::this_object_is_stable(key)(s)
        }
    };
    assert_by(spec.entails(lift_state(key_exists).leads_to(lift_state(post))), {
        let key_not_exists_or_stable = |s: Self| {
            ||| !s.resources().contains_key(key)
            ||| Self::this_object_is_stable(key)(s)
        };
        let input = (BuiltinControllerChoice::Stabilizer, key);
        Self::lemma_pre_leads_to_post_by_builtin_controllers(
            spec, input, Self::next(), Self::run_stabilizer(), key_exists, key_not_exists_or_stable
        );
        assert_by(spec.entails(lift_state(Self::this_object_is_stable(key)).leads_to(lift_state(post))), {
            let stable_and_pending_update_status_req_num_is_n = |msg_num: nat| lift_state(|s: Self| {
                &&& s.in_flight().filter(update_status_msg_from_bc_for(key)).len() == msg_num
                &&& Self::this_object_is_stable(key)(s)
            });
            assert forall |msg_num: nat|
                spec.entails(#[trigger] stable_and_pending_update_status_req_num_is_n(msg_num).leads_to(lift_state(post)))
            by {
                Self::lemma_pending_update_status_req_num_is_n_leads_to_object_not_exist_or_updated_or_no_more_pending_req(
                    spec, key, requirements, msg_num
                );
            }
            leads_to_exists_intro(spec, stable_and_pending_update_status_req_num_is_n, lift_state(post));
            assert_by(tla_exists(stable_and_pending_update_status_req_num_is_n) == lift_state(Self::this_object_is_stable(key)), {
                assert forall |ex| #[trigger] lift_state(Self::this_object_is_stable(key)).satisfied_by(ex) implies
                tla_exists(stable_and_pending_update_status_req_num_is_n).satisfied_by(ex) by {
                    let current_msg_num = ex.head().network_state.in_flight.filter(update_status_msg_from_bc_for(key)).len();
                    assert(stable_and_pending_update_status_req_num_is_n(current_msg_num).satisfied_by(ex));
                }
                temp_pred_equality(tla_exists(stable_and_pending_update_status_req_num_is_n), lift_state(Self::this_object_is_stable(key)));
            });
        });
        temp_pred_equality(lift_state(Self::this_object_is_stable(key)).or(lift_state(key_not_exists)), lift_state(key_not_exists_or_stable));
        temp_pred_equality(lift_state(post).or(lift_state(key_not_exists)), lift_state(post));
        sandwich_leads_to_by_or_temp(spec, lift_state(Self::this_object_is_stable(key)), lift_state(post), lift_state(key_not_exists));
        leads_to_trans_temp(spec, lift_state(key_exists), lift_state(key_not_exists_or_stable), lift_state(post));
    });
    temp_pred_equality(lift_state(key_exists).or(lift_state(key_not_exists)), true_pred());
    temp_pred_equality(lift_state(post).or(lift_state(key_not_exists)), lift_state(post));
    sandwich_leads_to_by_or_temp(spec, lift_state(key_exists), lift_state(post), lift_state(key_not_exists));
}

proof fn lemma_pending_update_status_req_num_is_n_leads_to_object_not_exist_or_updated_or_no_more_pending_req(
    spec: TempPred<Self>, key: ObjectRef, requirements: DynamicObjectMutViewPred, msg_num: nat
)
    requires
        spec.entails(always(lift_action(Self::next()))),
        spec.entails(tla_forall(|i| Self::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(Self::every_in_flight_create_req_msg_for_this_object_satisfies(key, requirements)))),
        spec.entails(always(lift_state(Self::every_in_flight_update_req_msg_for_this_object_satisfies(key, requirements)))),
    ensures
        spec.entails(
            lift_state(|s: Self| {
                &&& s.in_flight().filter(update_status_msg_from_bc_for(key)).len() == msg_num
                &&& Self::this_object_is_stable(key)(s)
            }).leads_to(lift_state(
                |s: Self| {
                    ||| !s.resources().contains_key(key)
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
        ||| !s.resources().contains_key(key)
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
        let obj_not_exist_or_updated = lift_state(|s: Self| {
            ||| !s.resources().contains_key(key)
            ||| Self::this_object_satisfies(key, requirements)(s)
        });
        let no_more_pending_req = lift_state(|s: Self| {
            &&& Self::no_status_update_req_msg_from_bc_for_this_object(key)(s)
            &&& Self::this_object_is_stable(key)(s)
        });
        let pre_minus_one_or_obj_not_exist_or_updated = lift_state(|s: Self| {
            ||| !s.resources().contains_key(key)
            ||| Self::this_object_satisfies(key, requirements)(s)
            ||| {
                &&& s.in_flight().filter(update_status_msg_from_bc_for(key)).len() == (msg_num - 1) as nat
                &&& Self::this_object_is_stable(key)(s)
            }
        });
        assert_by(spec.entails(lift_state(pre).leads_to(pre_minus_one_or_obj_not_exist_or_updated)), {
            assert forall |msg: MsgType<E>|
            spec.entails(#[trigger] pre_concrete_msg(msg).leads_to(pre_minus_one_or_obj_not_exist_or_updated)) by {
                Self::object_not_exist_or_updated_or_pending_update_status_requests_num_decreases(spec, key, requirements, msg_num, msg);
            }
            leads_to_exists_intro(spec, pre_concrete_msg, pre_minus_one_or_obj_not_exist_or_updated);
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
        Self::lemma_pending_update_status_req_num_is_n_leads_to_object_not_exist_or_updated_or_no_more_pending_req(
            spec, key, requirements, (msg_num - 1) as nat
        );
        temp_pred_equality(pre_minus_one_or_obj_not_exist_or_updated, pre_minus_one.or(obj_not_exist_or_updated));
        temp_pred_equality(lift_state(post), no_more_pending_req.or(obj_not_exist_or_updated));
        leads_to_shortcut_temp(spec, lift_state(pre), pre_minus_one, no_more_pending_req, obj_not_exist_or_updated);
    }
}

proof fn object_not_exist_or_updated_or_pending_update_status_requests_num_decreases(
    spec: TempPred<Self>, key: ObjectRef, requirements: DynamicObjectMutViewPred, msg_num: nat, msg: MsgType<E>
)
    requires
        msg_num > 0,
        spec.entails(always(lift_action(Self::next()))),
        spec.entails(tla_forall(|i| Self::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(Self::every_in_flight_create_req_msg_for_this_object_satisfies(key, requirements)))),
        spec.entails(always(lift_state(Self::every_in_flight_update_req_msg_for_this_object_satisfies(key, requirements)))),
    ensures
        spec.entails(
            lift_state(|s: Self| {
                &&& s.in_flight().filter(update_status_msg_from_bc_for(key)).len() == msg_num
                &&& Self::this_object_is_stable(key)(s)
                &&& s.in_flight().filter(update_status_msg_from_bc_for(key)).count(msg) > 0
            }).leads_to(lift_state(|s: Self| {
                ||| !s.resources().contains_key(key)
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
        ||| !s.resources().contains_key(key)
        ||| Self::this_object_satisfies(key, requirements)(s)
        ||| {
            &&& s.in_flight().filter(update_status_msg_from_bc_for(key)).len() == (msg_num - 1) as nat
            &&& Self::this_object_is_stable(key)(s)
        }
    };
    let input = Some(msg);
    let stronger_next = |s, s_prime: Self| {
        &&& Self::next()(s, s_prime)
        &&& Self::every_in_flight_create_req_msg_for_this_object_satisfies(key, requirements)(s)
        &&& Self::every_in_flight_update_req_msg_for_this_object_satisfies(key, requirements)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(Self::next()),
        lift_state(Self::every_in_flight_create_req_msg_for_this_object_satisfies(key, requirements)),
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
                } else {
                    assert(pending_req_multiset =~= pending_req_multiset_prime);
                    assert(
                        Self::this_object_is_stable(key)(s_prime)
                        || Self::this_object_satisfies(key, requirements)(s_prime)
                        || !s.resources().contains_key(key)
                    );
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
