// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    builtin_controllers::types::BuiltinControllerChoice,
    cluster::*,
    cluster_state_machine::Step,
    controller::types::{ControllerActionInput, ControllerStep},
    message::*,
};
use crate::reconciler::spec::reconciler::Reconciler;
use crate::temporal_logic::{defs::*, rules::*};
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

verus! {

impl <K: ResourceView, E: ExternalAPI, R: Reconciler<K, E>> Cluster<K, E, R> {

pub open spec fn every_in_flight_create_req_msg_for_this_ds_matches(
    key: ObjectRef, make_fn: FnSpec() -> DaemonSetView
) -> StatePred<Self> {
    |s: Self| {
        forall |msg| {
            &&& s.in_flight().contains(msg)
            &&& #[trigger] resource_create_request_msg(key)(msg)
        } ==> {
            &&& msg.content.get_create_request().obj == make_fn().marshal()
        }
    }
}

pub open spec fn every_in_flight_update_req_msg_for_this_ds_matches(
    key: ObjectRef, make_fn: FnSpec() -> DaemonSetView
) -> StatePred<Self> {
    |s: Self| {
        let made_ds = make_fn();
        forall |msg| {
            &&& s.in_flight().contains(msg)
            &&& #[trigger] resource_update_request_msg(key)(msg)
        } ==> {
            &&& msg.content.get_update_request().obj.metadata.resource_version.is_Some()
            &&& {
                &&& s.resources().contains_key(key)
                &&& msg.content.get_update_request().obj.metadata.resource_version == s.resources()[key].metadata.resource_version
            } ==> {
                let obj = msg.content.get_update_request().obj;
                &&& DaemonSetView::unmarshal(obj).is_Ok()
                &&& DaemonSetView::unmarshal(obj).get_Ok_0().spec.is_Some()
                &&& DaemonSetView::unmarshal(obj).get_Ok_0().spec.get_Some_0().template == made_ds.spec.get_Some_0().template
                &&& obj.metadata.labels == made_ds.metadata.labels
                &&& obj.metadata.annotations == made_ds.metadata.annotations
            }
        }
    }
}

pub open spec fn daemon_set_not_exist_or_updated_or_no_more_status_from_bc(
    key: ObjectRef, make_fn: FnSpec() -> DaemonSetView
) -> StatePred<Self> {
    |s: Self| {
        ||| !s.resources().contains_key(key)
        ||| {
            let obj = s.resources()[key];
            let made_ds = make_fn();
            &&& s.resources().contains_key(key)
            &&& DaemonSetView::unmarshal(obj).is_Ok()
            &&& DaemonSetView::unmarshal(obj).get_Ok_0().spec.is_Some()
            &&& DaemonSetView::unmarshal(obj).get_Ok_0().spec.get_Some_0().template == made_ds.spec.get_Some_0().template
            &&& obj.metadata.labels == made_ds.metadata.labels
            &&& obj.metadata.annotations == made_ds.metadata.annotations
        }
        ||| {
            &&& Self::no_status_update_req_msg_from_bc_for_this_object(key)(s)
            &&& s.stable_resources().contains(key)
        }
    }
}

/// This lemma is very similar to lemma_true_leads_to_always_stateful_set_not_exist_or_updated_or_no_more_pending_req
/// but does not consider the dependency on a configmap('s rv)

pub proof fn lemma_true_leads_to_always_daemon_set_not_exist_or_updated_or_no_more_pending_req(spec: TempPred<Self>, key: ObjectRef, make_fn: FnSpec() -> DaemonSetView)
    requires
        key.kind == DaemonSetView::kind(),
        spec.entails(always(lift_action(Self::next()))),
        spec.entails(tla_forall(|i| Self::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| Self::builtin_controllers_next().weak_fairness(i))),
        spec.entails(always(lift_state(Self::every_in_flight_create_req_msg_for_this_ds_matches(key, make_fn)))),
        spec.entails(always(lift_state(Self::every_in_flight_update_req_msg_for_this_ds_matches(key, make_fn)))),
        spec.entails(always(lift_state(Self::each_object_in_etcd_is_well_formed()))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(Self::daemon_set_not_exist_or_updated_or_no_more_status_from_bc(key, make_fn))))),
{
    Self::lemma_true_leads_to_daemon_set_not_exist_or_updated_or_no_more_pending_req(spec, key, make_fn);

    let post = Self::daemon_set_not_exist_or_updated_or_no_more_status_from_bc(key, make_fn);
    let stronger_next = |s, s_prime: Self| {
        &&& Self::next()(s, s_prime)
        &&& Self::every_in_flight_create_req_msg_for_this_ds_matches(key, make_fn)(s)
        &&& Self::every_in_flight_update_req_msg_for_this_ds_matches(key, make_fn)(s)
        &&& Self::each_object_in_etcd_is_well_formed()(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(Self::next()),
        lift_state(Self::every_in_flight_create_req_msg_for_this_ds_matches(key, make_fn)),
        lift_state(Self::every_in_flight_update_req_msg_for_this_ds_matches(key, make_fn)),
        lift_state(Self::each_object_in_etcd_is_well_formed())
    );

    assert forall |s, s_prime| post(s) && #[trigger] stronger_next(s, s_prime) implies post(s_prime) by {
        let step = choose |step| Self::next_step(s, s_prime, step);
        match step {
            Step::ApiServerStep(input) => {
                let req = input.get_Some_0();
                DaemonSetView::marshal_spec_preserves_integrity();
                DaemonSetView::marshal_status_preserves_integrity();
                match req.content.get_APIRequest_0() {
                    APIRequest::CreateRequest(_) => {
                        if resource_create_request_msg(key)(req) {}
                    }
                    APIRequest::UpdateRequest(_) => {
                        if resource_update_request_msg(key)(req) {}
                    }
                    _ => {}
                }
            },
            _ => {}
        }
    }

    leads_to_stable_temp(spec, lift_action(stronger_next), true_pred(), lift_state(post));
}

proof fn lemma_true_leads_to_daemon_set_not_exist_or_updated_or_no_more_pending_req(spec: TempPred<Self>, key: ObjectRef, make_fn: FnSpec() -> DaemonSetView)
    requires
        key.kind == DaemonSetView::kind(),
        spec.entails(always(lift_action(Self::next()))),
        spec.entails(tla_forall(|i| Self::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| Self::builtin_controllers_next().weak_fairness(i))),
        spec.entails(always(lift_state(Self::every_in_flight_create_req_msg_for_this_ds_matches(key, make_fn)))),
        spec.entails(always(lift_state(Self::every_in_flight_update_req_msg_for_this_ds_matches(key, make_fn)))),
        spec.entails(always(lift_state(Self::each_object_in_etcd_is_well_formed()))),
    ensures spec.entails(true_pred().leads_to(lift_state(Self::daemon_set_not_exist_or_updated_or_no_more_status_from_bc(key, make_fn)))),
{
    let key_exists = |s: Self| s.resources().contains_key(key);
    let key_not_exists = |s: Self| !s.resources().contains_key(key);
    let post = Self::daemon_set_not_exist_or_updated_or_no_more_status_from_bc(key, make_fn);
    assert_by(spec.entails(lift_state(key_exists).leads_to(lift_state(post))), {
        let key_not_exists_or_stable = |s: Self| {
            ||| !s.resources().contains_key(key)
            ||| s.stable_resources().contains(key)
        };
        let input = (BuiltinControllerChoice::Stabilizer, key);
        Self::lemma_pre_leads_to_post_by_builtin_controllers(
            spec, input, Self::next(), Self::run_stabilizer(), key_exists, key_not_exists_or_stable
        );
        assert_by(spec.entails(lift_state(|s: Self| s.stable_resources().contains(key)).leads_to(lift_state(post))), {
            let stable_and_pending_update_status_req_num_is_n = |msg_num: nat| lift_state(|s: Self| {
                &&& s.in_flight().filter(update_status_msg_from_bc_for(key)).len() == msg_num
                &&& s.stable_resources().contains(key)
            });
            assert forall |msg_num: nat|
                spec.entails(#[trigger] stable_and_pending_update_status_req_num_is_n(msg_num).leads_to(lift_state(post)))
            by {
                Self::lemma_pending_update_status_req_num_is_n_leads_to_daemon_set_not_exist_or_updated_or_no_more_pending_req(
                    spec, key, make_fn, msg_num
                );
            }
            leads_to_exists_intro(spec, stable_and_pending_update_status_req_num_is_n, lift_state(post));
            assert_by(tla_exists(stable_and_pending_update_status_req_num_is_n) == lift_state(|s: Self| s.stable_resources().contains(key)), {
                assert forall |ex| lift_state(|s: Self| s.stable_resources().contains(key)).satisfied_by(ex) implies
                #[trigger] tla_exists(stable_and_pending_update_status_req_num_is_n).satisfied_by(ex) by {
                    let current_msg_num = ex.head().network_state.in_flight.filter(update_status_msg_from_bc_for(key)).len();
                    assert(stable_and_pending_update_status_req_num_is_n(current_msg_num).satisfied_by(ex));
                }
                temp_pred_equality(tla_exists(stable_and_pending_update_status_req_num_is_n), lift_state(|s: Self| s.stable_resources().contains(key)));
            });
        });
        temp_pred_equality(lift_state(|s: Self| s.stable_resources().contains(key)).or(lift_state(key_not_exists)), lift_state(key_not_exists_or_stable));
        temp_pred_equality(lift_state(post).or(lift_state(key_not_exists)), lift_state(post));
        sandwich_leads_to_by_or_temp(spec, lift_state(|s: Self| s.stable_resources().contains(key)), lift_state(post), lift_state(key_not_exists));
        leads_to_trans_temp(spec, lift_state(key_exists), lift_state(key_not_exists_or_stable), lift_state(post));
    });
    temp_pred_equality(lift_state(key_exists).or(lift_state(key_not_exists)), true_pred());
    temp_pred_equality(lift_state(post).or(lift_state(key_not_exists)), lift_state(post));
    sandwich_leads_to_by_or_temp(spec, lift_state(key_exists), lift_state(post), lift_state(key_not_exists));
}

proof fn lemma_pending_update_status_req_num_is_n_leads_to_daemon_set_not_exist_or_updated_or_no_more_pending_req(spec: TempPred<Self>, key: ObjectRef, make_fn: FnSpec() -> DaemonSetView, msg_num: nat)
    requires
        key.kind == DaemonSetView::kind(),
        spec.entails(always(lift_action(Self::next()))),
        spec.entails(tla_forall(|i| Self::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(Self::every_in_flight_create_req_msg_for_this_ds_matches(key, make_fn)))),
        spec.entails(always(lift_state(Self::every_in_flight_update_req_msg_for_this_ds_matches(key, make_fn)))),
        spec.entails(always(lift_state(Self::each_object_in_etcd_is_well_formed()))),
    ensures
        spec.entails(
            lift_state(|s: Self| {
                &&& s.in_flight().filter(update_status_msg_from_bc_for(key)).len() == msg_num
                &&& s.stable_resources().contains(key)
            }).leads_to(lift_state(Self::daemon_set_not_exist_or_updated_or_no_more_status_from_bc(key, make_fn)))
        ),
    decreases msg_num
{
    let pre = |s: Self| {
        &&& s.in_flight().filter(update_status_msg_from_bc_for(key)).len() == msg_num
        &&& s.stable_resources().contains(key)
    };
    let post = Self::daemon_set_not_exist_or_updated_or_no_more_status_from_bc(key, make_fn);
    if msg_num == 0 {
        assert_by(valid(lift_state(pre).implies(lift_state(post))), {
            assert forall |s: Self| #[trigger] pre(s) implies post(s) by {
                assert forall |msg| update_status_msg_from_bc_for(key)(msg) implies !s.in_flight().contains(msg) by {
                    assert(s.in_flight().filter(update_status_msg_from_bc_for(key)).count(msg) == 0);
                }
            }
        });
        valid_implies_implies_leads_to(spec, lift_state(pre), lift_state(post));
    } else {
        let pre_concrete_msg = |msg: MsgType<E>| lift_state(|s: Self| {
            &&& s.in_flight().filter(update_status_msg_from_bc_for(key)).len() == msg_num
            &&& s.stable_resources().contains(key)
            &&& s.in_flight().filter(update_status_msg_from_bc_for(key)).count(msg) > 0
        });
        let pre_minus_one = lift_state(|s: Self| {
            &&& s.in_flight().filter(update_status_msg_from_bc_for(key)).len() == (msg_num - 1) as nat
            &&& s.stable_resources().contains(key)
        });
        let obj_not_exist_or_updated = lift_state(|s: Self| {
            ||| !s.resources().contains_key(key)
            ||| {
                let obj = s.resources()[key];
                let made_ds = make_fn();
                &&& s.resources().contains_key(key)
                &&& DaemonSetView::unmarshal(obj).is_Ok()
                &&& DaemonSetView::unmarshal(obj).get_Ok_0().spec.is_Some()
                &&& DaemonSetView::unmarshal(obj).get_Ok_0().spec.get_Some_0().template == made_ds.spec.get_Some_0().template
                &&& obj.metadata.labels == made_ds.metadata.labels
                &&& obj.metadata.annotations == made_ds.metadata.annotations
            }
        });
        let no_more_pending_req = lift_state(|s: Self| {
            &&& Self::no_status_update_req_msg_from_bc_for_this_object(key)(s)
            &&& s.stable_resources().contains(key)
        });
        let pre_minus_one_or_obj_not_exist_or_updated = lift_state(|s: Self| {
            ||| !s.resources().contains_key(key)
            ||| {
                let obj = s.resources()[key];
                let made_ds = make_fn();
                &&& s.resources().contains_key(key)
                &&& DaemonSetView::unmarshal(obj).is_Ok()
                &&& DaemonSetView::unmarshal(obj).get_Ok_0().spec.is_Some()
                &&& DaemonSetView::unmarshal(obj).get_Ok_0().spec.get_Some_0().template == made_ds.spec.get_Some_0().template
                &&& obj.metadata.labels == made_ds.metadata.labels
                &&& obj.metadata.annotations == made_ds.metadata.annotations
            }
            ||| {
                &&& s.in_flight().filter(update_status_msg_from_bc_for(key)).len() == (msg_num - 1) as nat
                &&& s.stable_resources().contains(key)
            }
        });
        assert_by(spec.entails(lift_state(pre).leads_to(pre_minus_one_or_obj_not_exist_or_updated)), {
            assert forall |msg: MsgType<E>|
            spec.entails(#[trigger] pre_concrete_msg(msg).leads_to(pre_minus_one_or_obj_not_exist_or_updated)) by {
                Self::daemon_set_not_exist_or_updated_or_pending_update_status_requests_num_decreases(spec, key, make_fn, msg_num, msg);
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
        Self::lemma_pending_update_status_req_num_is_n_leads_to_daemon_set_not_exist_or_updated_or_no_more_pending_req(
            spec, key, make_fn, (msg_num - 1) as nat
        );
        temp_pred_equality(pre_minus_one_or_obj_not_exist_or_updated, pre_minus_one.or(obj_not_exist_or_updated));
        temp_pred_equality(lift_state(post), no_more_pending_req.or(obj_not_exist_or_updated));
        leads_to_shortcut_temp(spec, lift_state(pre), pre_minus_one, no_more_pending_req, obj_not_exist_or_updated);
    }
}

proof fn daemon_set_not_exist_or_updated_or_pending_update_status_requests_num_decreases(spec: TempPred<Self>, key: ObjectRef, make_fn: FnSpec() -> DaemonSetView, msg_num: nat, msg: MsgType<E>)
    requires
        key.kind == DaemonSetView::kind(),
        msg_num > 0,
        spec.entails(always(lift_action(Self::next()))),
        spec.entails(tla_forall(|i| Self::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_state(Self::every_in_flight_create_req_msg_for_this_ds_matches(key, make_fn)))),
        spec.entails(always(lift_state(Self::every_in_flight_update_req_msg_for_this_ds_matches(key, make_fn)))),
        spec.entails(always(lift_state(Self::each_object_in_etcd_is_well_formed()))),
    ensures
        spec.entails(
            lift_state(|s: Self| {
                &&& s.in_flight().filter(update_status_msg_from_bc_for(key)).len() == msg_num
                &&& s.stable_resources().contains(key)
                &&& s.in_flight().filter(update_status_msg_from_bc_for(key)).count(msg) > 0
            }).leads_to(lift_state(|s: Self| {
                ||| !s.resources().contains_key(key)
                ||| {
                    let obj = s.resources()[key];
                    let made_ds = make_fn();
                    &&& s.resources().contains_key(key)
                    &&& DaemonSetView::unmarshal(obj).is_Ok()
                    &&& DaemonSetView::unmarshal(obj).get_Ok_0().spec.is_Some()
                    &&& DaemonSetView::unmarshal(obj).get_Ok_0().spec.get_Some_0().template == made_ds.spec.get_Some_0().template
                    &&& obj.metadata.labels == made_ds.metadata.labels
                    &&& obj.metadata.annotations == made_ds.metadata.annotations
                }
                ||| {
                    &&& s.in_flight().filter(update_status_msg_from_bc_for(key)).len() == (msg_num - 1) as nat
                    &&& s.stable_resources().contains(key)
                }
            }))
        ),
{
    let pre = |s: Self| {
        &&& s.in_flight().filter(update_status_msg_from_bc_for(key)).len() == msg_num
        &&& s.stable_resources().contains(key)
        &&& s.in_flight().filter(update_status_msg_from_bc_for(key)).count(msg) > 0
    };
    let post = |s: Self| {
        ||| !s.resources().contains_key(key)
        ||| {
            let obj = s.resources()[key];
            let made_ds = make_fn();
            &&& s.resources().contains_key(key)
            &&& DaemonSetView::unmarshal(obj).is_Ok()
            &&& DaemonSetView::unmarshal(obj).get_Ok_0().spec.is_Some()
            &&& DaemonSetView::unmarshal(obj).get_Ok_0().spec.get_Some_0().template == made_ds.spec.get_Some_0().template
            &&& obj.metadata.labels == made_ds.metadata.labels
            &&& obj.metadata.annotations == made_ds.metadata.annotations
        }
        ||| {
            &&& s.in_flight().filter(update_status_msg_from_bc_for(key)).len() == (msg_num - 1) as nat
            &&& s.stable_resources().contains(key)
        }
    };
    let input = Some(msg);
    let stronger_next = |s, s_prime: Self| {
        &&& Self::next()(s, s_prime)
        &&& Self::every_in_flight_create_req_msg_for_this_ds_matches(key, make_fn)(s)
        &&& Self::every_in_flight_update_req_msg_for_this_ds_matches(key, make_fn)(s)
        &&& Self::each_object_in_etcd_is_well_formed()(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(Self::next()),
        lift_state(Self::every_in_flight_create_req_msg_for_this_ds_matches(key, make_fn)),
        lift_state(Self::every_in_flight_update_req_msg_for_this_ds_matches(key, make_fn)),
        lift_state(Self::each_object_in_etcd_is_well_formed())
    );

    assert forall |s, s_prime: Self| pre(s) && #[trigger] stronger_next(s, s_prime)
    implies pre(s_prime) || post(s_prime) by {
        let pending_req_multiset = s.in_flight().filter(update_status_msg_from_bc_for(key));
        let pending_req_multiset_prime = s_prime.in_flight().filter(update_status_msg_from_bc_for(key));
        let step = choose |step| Self::next_step(s, s_prime, step);
        match step {
            Step::ApiServerStep(input) => {
                if pending_req_multiset.count(input.get_Some_0()) > 0 {
                    assert(pending_req_multiset.remove(input.get_Some_0()) =~= pending_req_multiset_prime);
                } else {
                    DaemonSetView::marshal_spec_preserves_integrity();
                    DaemonSetView::marshal_status_preserves_integrity();
                    if resource_create_request_msg(key)(input.get_Some_0()) {} else {}
                    if resource_update_request_msg(key)(input.get_Some_0()) {} else {}
                    assert(pending_req_multiset =~= pending_req_multiset_prime);
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
        DaemonSetView::marshal_preserves_integrity();
        assert(pending_req_multiset.remove(msg) =~= pending_req_multiset_prime);
    }
    Self::lemma_pre_leads_to_post_by_kubernetes_api(
        spec, input, stronger_next, Self::handle_request(), pre, post
    );
}

}

}
