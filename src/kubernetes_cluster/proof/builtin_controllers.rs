// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::external_api::spec::*;
use crate::kubernetes_api_objects::{
    api_method::*, common::*, config_map::*, dynamic::*, owner_reference::*, resource::*,
    stateful_set::*,
};
use crate::kubernetes_cluster::spec::{
    builtin_controllers::types::{built_in_controller_req_msg, BuiltinControllerChoice},
    cluster::*,
    cluster_state_machine::Step,
    controller::common::{controller_req_msg, ControllerActionInput, ControllerStep},
    message::*,
};
use crate::reconciler::spec::reconciler::Reconciler;
use crate::temporal_logic::{defs::*, rules::*};
use vstd::prelude::*;

verus! {

impl <K: ResourceView, E: ExternalAPI, R: Reconciler<K, E>> Cluster<K, E, R> {

pub open spec fn every_update_msg_sets_owner_references_as(
    key: ObjectRef, requirements: FnSpec(Option<Seq<OwnerReferenceView>>) -> bool
) -> StatePred<Self> {
    |s: Self| {
        forall |msg: Message|
            #[trigger] s.message_in_flight(msg)
            && msg.dst.is_KubernetesAPI()
            && msg.content.is_update_request()
            && msg.content.get_update_request().key == key
            ==> requirements(msg.content.get_update_request().obj.metadata.owner_references)
    }
}

pub open spec fn every_create_msg_sets_owner_references_as(
    key: ObjectRef, requirements: FnSpec(Option<Seq<OwnerReferenceView>>) -> bool
) -> StatePred<Self> {
    |s: Self| {
        forall |msg: Message|
            #[trigger] s.message_in_flight(msg)
            && msg.dst.is_KubernetesAPI()
            && msg.content.is_create_request()
            && msg.content.get_create_request().namespace == key.namespace
            && msg.content.get_create_request().obj.metadata.name.get_Some_0() == key.name
            && msg.content.get_create_request().obj.kind == key.kind
            ==> requirements(msg.content.get_create_request().obj.metadata.owner_references)
    }
}

pub open spec fn objects_owner_references_satisfies(key: ObjectRef, requirements: FnSpec(Option<Seq<OwnerReferenceView>>) -> bool) -> StatePred<Self> {
    |s: Self| {
        s.resource_key_exists(key) ==> requirements(s.resource_obj_of(key).metadata.owner_references)
    }
}

pub open spec fn objects_owner_references_violates(key: ObjectRef, requirements: FnSpec(Option<Seq<OwnerReferenceView>>) -> bool) -> StatePred<Self> {
    |s: Self| {
        s.resource_key_exists(key) && !requirements(s.resource_obj_of(key).metadata.owner_references)
    }
}

pub open spec fn object_has_no_finalizers_or_deletion_timestamp(key: ObjectRef) -> StatePred<Self> {
    |s: Self| {
        s.resource_key_exists(key)
        ==> s.resource_obj_of(key).metadata.deletion_timestamp.is_None()
            && s.resource_obj_of(key).metadata.finalizers.is_None()
    }
}

spec fn exists_delete_request_msg_in_flight_with_key(key: ObjectRef) -> StatePred<Self> {
    |s: Self| {
        exists |msg: Message| {
            #[trigger] s.message_in_flight(msg)
            && msg.dst.is_KubernetesAPI()
            && msg.content.is_delete_request_with_key(key)
        }
    }
}

/// This lemma requires the following preconditions:
///     1. spec |= [](in_flight(update_msg_with(msg, key)) ==> satisfies(msg.obj.metadata.owner_references, eventual_owner_ref)).
///     2. spec |= [](in_flight(create_msg_with(msg, key)) ==> satisfies(msg.obj.metadata.owner_references, eventual_owner_ref)).
///     3. spec |= [](key_exists(key) ==> resource_obj_of(key) has no finalizers or deletion_timestamp).
///     4. spec |= [](!expected(owner_references) => deleted).
/// In 3, no finalizers ensures the stability: once the desired state reaches, every update request
/// 
/// The proof of spec |= true ~> objects_owner_references_satisfies(eventual_owner_ref) consists of two parts:
///     1. spec |= true ~> (object_has_invalid_owner_reference ==> delete message in flight).
///     2. spec |= (object_has_invalid_owner_reference ==> delete message in flight) ~> all_objects_have_expected_owner_references.
/// The first is primarily obtained by the weak fairness of the builtin controllers action (specifially, the garbage collector);
/// and the second holds due to the weak fairness of kubernetes api.
/// 
/// To prove 1, we split `true` into three cases:
///     a. The object's.
///     b. The object has valid owner references.
///     c. The object doesn't exist.
/// For the last two cases, the post state ((object_has_invalid_owner_reference ==> delete message in flight)) is already reached. 
/// We only need to show spec |= case a ~> post. This is straightforward via the weak fairness of builtin controllers.
pub proof fn lemma_eventually_objects_owner_references_satisfies(
    spec: TempPred<Self>, key: ObjectRef, eventual_owner_ref: FnSpec(Option<Seq<OwnerReferenceView>>) -> bool
)
    requires
        spec.entails(always(lift_state(Self::busy_disabled()))),
        spec.entails(always(lift_action(Self::next()))),
        spec.entails(tla_forall(|i| Self::kubernetes_api_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| Self::builtin_controllers_next().weak_fairness(i))),
        spec.entails(always(lift_state(Self::every_create_msg_sets_owner_references_as(key, eventual_owner_ref)))),
        spec.entails(always(lift_state(Self::every_update_msg_sets_owner_references_as(key, eventual_owner_ref)))),
        spec.entails(always(lift_state(Self::object_has_no_finalizers_or_deletion_timestamp(key)))),
        // If the current owner_references does not satisfy the eventual requirement, the gc action is enabled.
        spec.entails(always(lift_state(Self::objects_owner_references_violates(key, eventual_owner_ref)).implies(lift_state(Self::garbage_collector_deletion_enabled(key))))),
    ensures
        spec.entails(true_pred().leads_to(always(lift_state(Self::objects_owner_references_satisfies(key, eventual_owner_ref))))),
{
    let pre = |s: Self| {
        &&& Self::objects_owner_references_violates(key, eventual_owner_ref)(s)
        &&& Self::garbage_collector_deletion_enabled(key)(s)
    };

    let delete_msg_in_flight = |s: Self| {
        Self::objects_owner_references_violates(key, eventual_owner_ref)(s) ==> Self::exists_delete_request_msg_in_flight_with_key(key)(s)
    };
    let post = Self::objects_owner_references_satisfies(key, eventual_owner_ref);

    let input = (BuiltinControllerChoice::GarbageCollector, key);
    let stronger_next = |s, s_prime: Self| {
        &&& Self::next()(s, s_prime)
        &&& Self::every_create_msg_sets_owner_references_as(key, eventual_owner_ref)(s)
        &&& Self::every_update_msg_sets_owner_references_as(key, eventual_owner_ref)(s)
        &&& Self::object_has_no_finalizers_or_deletion_timestamp(key)(s)
        &&& Self::objects_owner_references_violates(key, eventual_owner_ref)(s) ==> Self::garbage_collector_deletion_enabled(key)(s)
        &&& Self::objects_owner_references_violates(key, eventual_owner_ref)(s_prime) ==> Self::garbage_collector_deletion_enabled(key)(s_prime)
    };
    always_to_always_later(spec, lift_state(Self::objects_owner_references_violates(key, eventual_owner_ref)).implies(lift_state(Self::garbage_collector_deletion_enabled(key))));
    strengthen_next_n!(
        stronger_next, spec,
        lift_action(Self::next()),
        lift_state(Self::every_create_msg_sets_owner_references_as(key, eventual_owner_ref)),
        lift_state(Self::every_update_msg_sets_owner_references_as(key, eventual_owner_ref)),
        lift_state(Self::object_has_no_finalizers_or_deletion_timestamp(key)),
        lift_state(Self::objects_owner_references_violates(key, eventual_owner_ref)).implies(lift_state(Self::garbage_collector_deletion_enabled(key))),
        later(lift_state(Self::objects_owner_references_violates(key, eventual_owner_ref)).implies(lift_state(Self::garbage_collector_deletion_enabled(key))))
    );

    assert forall |s, s_prime: Self| pre(s) && #[trigger] stronger_next(s, s_prime) && Self::builtin_controllers_next().forward(input)(s, s_prime) implies delete_msg_in_flight(s_prime) by {
        assert(Self::garbage_collector_deletion_enabled(key)(s));
        let delete_req_msg = built_in_controller_req_msg(delete_req_msg_content(
            key, s.rest_id_allocator.allocate().1
        ));
        assert(s_prime.message_in_flight(delete_req_msg));
        assert(Self::exists_delete_request_msg_in_flight_with_key(key)(s_prime));
        assert(delete_msg_in_flight(s_prime));
    }

    assert forall |s, s_prime: Self| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || delete_msg_in_flight(s_prime) by {
        let step = choose |step| Self::next_step(s, s_prime, step);
        match step {
            Step::BuiltinControllersStep(i) => {
                if i == input {
                    assert(Self::garbage_collector_deletion_enabled(key)(s));
                    let delete_req_msg = built_in_controller_req_msg(delete_req_msg_content(
                        key, s.rest_id_allocator.allocate().1
                    ));
                    assert(s_prime.message_in_flight(delete_req_msg));
                    assert(Self::exists_delete_request_msg_in_flight_with_key(key)(s_prime));
                    assert(delete_msg_in_flight(s_prime));
                } else {
                    assert(pre(s_prime));
                }
            },
            Step::KubernetesAPIStep(i) => {
                if i.get_Some_0().content.is_update_request_with_key(key) {
                    if Self::validate_update_request(i.get_Some_0().content.get_update_request(), s.kubernetes_api_state).is_Some()
                    || Self::update_is_noop(i.get_Some_0().content.get_update_request().obj, s.resource_obj_of(key)) {
                        assert(pre(s_prime));
                    } else {
                        assert(Self::objects_owner_references_satisfies(key, eventual_owner_ref)(s_prime));
                    }
                } else if i.get_Some_0().content.is_delete_request_with_key(key) {
                    assert(s.resource_obj_of(key).metadata.finalizers.is_None());
                    assert(!s_prime.resource_key_exists(key));
                } else {
                    assert(pre(s_prime));
                }
            },
            _ => {
                assert(pre(s_prime) || delete_msg_in_flight(s_prime));
            }
        }
    }

    Self::lemma_pre_leads_to_post_by_builtin_controllers(
        spec, input, stronger_next, Self::run_garbage_collector(), pre, delete_msg_in_flight
    );

    leads_to_self(post);

    assert_by(
        spec.entails(lift_state(Self::objects_owner_references_violates(key, eventual_owner_ref)).leads_to(lift_state(post))),
        {
            Self::lemma_delete_msg_in_flight_leads_to_owner_references_satisfies(spec, key, eventual_owner_ref);
            or_leads_to_combine_temp(spec, lift_state(post), lift_state(Self::exists_delete_request_msg_in_flight_with_key(key)), lift_state(post));
            temp_pred_equality(lift_state(delete_msg_in_flight), lift_state(post).or(lift_state(Self::exists_delete_request_msg_in_flight_with_key(key))));
            leads_to_trans_n!(spec, lift_state(pre), lift_state(delete_msg_in_flight), lift_state(post));

            temp_pred_equality(lift_state(Self::objects_owner_references_violates(key, eventual_owner_ref)).implies(lift_state(Self::garbage_collector_deletion_enabled(key))), lift_state(Self::objects_owner_references_violates(key, eventual_owner_ref)).implies(lift_state(pre)));
            leads_to_weaken_temp(spec, lift_state(pre), lift_state(post), lift_state(Self::objects_owner_references_violates(key, eventual_owner_ref)), lift_state(post));
        }
    );

    or_leads_to_combine_temp(spec, lift_state(Self::objects_owner_references_violates(key, eventual_owner_ref)), lift_state(post), lift_state(post));
    temp_pred_equality(true_pred(), lift_state(Self::objects_owner_references_violates(key, eventual_owner_ref)).or(lift_state(post)));

    leads_to_stable(spec, stronger_next, |s: Self| true, post);
}

proof fn lemma_delete_msg_in_flight_leads_to_owner_references_satisfies(
    spec: TempPred<Self>, key: ObjectRef, eventual_owner_ref: FnSpec(Option<Seq<OwnerReferenceView>>) -> bool
)
    requires
        spec.entails(always(lift_state(Self::busy_disabled()))),
        spec.entails(tla_forall(|i| Self::kubernetes_api_next().weak_fairness(i))),
        spec.entails(always(lift_action(Self::next()))),
        spec.entails(always(lift_state(Self::every_update_msg_sets_owner_references_as(key, eventual_owner_ref)))),
        spec.entails(always(lift_state(Self::object_has_no_finalizers_or_deletion_timestamp(key)))),
    ensures
        spec.entails(
            lift_state(Self::exists_delete_request_msg_in_flight_with_key(key))
            .leads_to(lift_state(Self::objects_owner_references_satisfies(key, eventual_owner_ref)))
        ),
{
    let pre = Self::exists_delete_request_msg_in_flight_with_key(key);
    let post = Self::objects_owner_references_satisfies(key, eventual_owner_ref);
    assert_by(
        spec.entails(lift_state(pre).leads_to(lift_state(post))),
        {
            let msg_to_p = |msg: Message| {
                lift_state(|s: Self| {
                    &&& s.message_in_flight(msg)
                    &&& msg.dst.is_KubernetesAPI()
                    &&& msg.content.is_delete_request_with_key(key)
                })
            };
            assert forall |msg: Message| spec.entails((#[trigger] msg_to_p(msg)).leads_to(lift_state(post))) by {
                let input = Some(msg);
                let msg_to_p_state = |s: Self| {
                    &&& s.message_in_flight(msg)
                    &&& msg.dst.is_KubernetesAPI()
                    &&& msg.content.is_delete_request_with_key(key)
                };
                let stronger_next = |s, s_prime: Self| {
                    &&& Self::next()(s, s_prime)
                    &&& Self::busy_disabled()(s)
                    &&& Self::every_update_msg_sets_owner_references_as(key, eventual_owner_ref)(s)
                    &&& Self::object_has_no_finalizers_or_deletion_timestamp(key)(s)
                };
                strengthen_next_n!(
                    stronger_next, spec,
                    lift_action(Self::next()),
                    lift_state(Self::busy_disabled()),
                    lift_state(Self::every_update_msg_sets_owner_references_as(key, eventual_owner_ref)),
                    lift_state(Self::object_has_no_finalizers_or_deletion_timestamp(key))
                );
                Self::lemma_pre_leads_to_post_by_kubernetes_api(spec, input, stronger_next, Self::handle_request(), msg_to_p_state, post);
            }
            leads_to_exists_intro(spec, msg_to_p, lift_state(post));
            assert_by(
                tla_exists(msg_to_p) == lift_state(pre),
                {
                    assert forall |ex| #[trigger] lift_state(pre).satisfied_by(ex) implies tla_exists(msg_to_p).satisfied_by(ex) by {
                        let msg = choose |msg| {
                            &&& #[trigger] ex.head().message_in_flight(msg)
                            &&& msg.dst.is_KubernetesAPI()
                            &&& msg.content.is_delete_request_with_key(key)
                        };
                        assert(msg_to_p(msg).satisfied_by(ex));
                    }
                    temp_pred_equality(tla_exists(msg_to_p), lift_state(pre));
                }
            )
        }
    );
}

}

}
