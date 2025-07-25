use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    api_server::types::*, builtin_controllers::garbage_collector::run_garbage_collector,
    builtin_controllers::types::*, cluster::*, message::*,
};
use crate::temporal_logic::{defs::*, rules::*};
use crate::vstd_ext::string_view::StringView;
use vstd::prelude::*;

verus! {

impl Cluster {

// Everytime when we reason about update request message, we can only consider those valid ones (see validata_update_request).
// However, listing all requirements makes spec looks cumbersome (consider using validate_create/update_request); we can only
// list those that we need or that may appear according to the spec of system.
//
// For example, in some lemma we use msg.content.get_update_request().obj.kind == key.kind, so this requirement is added here.
pub open spec fn every_update_msg_sets_owner_references_as(
    key: ObjectRef, requirements: spec_fn(Option<Seq<OwnerReferenceView>>) -> bool
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        &&& forall |msg: Message|
            s.in_flight().contains(msg)
            && #[trigger] resource_update_request_msg(key)(msg)
            ==> requirements(msg.content.get_update_request().obj.metadata.owner_references)
        &&& forall |msg: Message|
            s.in_flight().contains(msg)
            && #[trigger] resource_get_then_update_request_msg(key)(msg)
            ==> requirements(msg.content.get_get_then_update_request().obj.metadata.owner_references)
    }
}

pub open spec fn every_create_msg_sets_owner_references_as(
    key: ObjectRef, requirements: spec_fn(Option<Seq<OwnerReferenceView>>) -> bool
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg: Message|
            s.in_flight().contains(msg)
            && #[trigger] resource_create_request_msg(key)(msg)
            ==> requirements(msg.content.get_create_request().obj.metadata.owner_references)
    }
}

pub open spec fn no_create_msg_that_uses_generate_name(
    kind: Kind, namespace: StringView
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg: Message| !{
            &&& s.in_flight().contains(msg)
            &&& #[trigger] resource_create_request_msg_without_name(kind, namespace)(msg)
        }
    }
}

pub open spec fn objects_owner_references_satisfies(key: ObjectRef, requirements: spec_fn(Option<Seq<OwnerReferenceView>>) -> bool) -> StatePred<ClusterState> {
    |s: ClusterState| {
        s.resources().contains_key(key) ==> requirements(s.resources()[key].metadata.owner_references)
    }
}

pub open spec fn objects_owner_references_violates(key: ObjectRef, requirements: spec_fn(Option<Seq<OwnerReferenceView>>) -> bool) -> StatePred<ClusterState> {
    |s: ClusterState| {
        s.resources().contains_key(key) && !requirements(s.resources()[key].metadata.owner_references)
    }
}

pub open spec fn object_has_no_finalizers(key: ObjectRef) -> StatePred<ClusterState> {
    |s: ClusterState| {
        s.resources().contains_key(key)
        ==> s.resources()[key].metadata.finalizers is None
    }
}

spec fn effective_delete_request_msg_for_key(key: ObjectRef, msg: Message) -> StatePred<ClusterState> {
    |s: ClusterState| {
        s.in_flight().contains(msg)
        && s.api_server.resources.contains_key(key)
        && msg.dst.is_APIServer()
        && msg.content.is_delete_request_with_key(key)
        && msg.content.get_delete_request().preconditions->0.uid == s.api_server.resources[key].metadata.uid
        && msg.content.get_delete_request().preconditions->0.resource_version is None
    }
}

spec fn exists_effective_delete_request_msg_for_key(key: ObjectRef) -> StatePred<ClusterState> {
    |s: ClusterState| {
        exists |msg: Message| #![trigger s.in_flight().contains(msg)] Self::effective_delete_request_msg_for_key(key, msg)(s)
    }
}

pub open spec fn garbage_collector_deletion_enabled(key: ObjectRef) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let input = BuiltinControllersActionInput {
            choice: BuiltinControllerChoice::GarbageCollector,
            key: key,
            rpc_id_allocator: s.rpc_id_allocator,
            resources: s.api_server.resources
        };
        (run_garbage_collector().precondition)(input, ())
    }
}

// This lemma is used to show that under some assumptions, the owner references of given object will eventually satisfy the
// provided requirements (e.g., only points to the current cr's reference). We introduce this lemma because during reconciler
// process, the reconciler only considers the object created from current cr and if so, it continues; otherwises, it returns.
// With this lemma, we can prove that the reconciler will eventually continue the reconcile process. To use this lemma, please
// read the explanations of all the preconditions and what each of them is for.
//
// This lemma requires the following preconditions:
//     1. spec |= [](in_flight(update_msg_with(msg, key)) ==> satisfies(msg.obj.metadata.owner_references, eventual_owner_ref)).
//     2. spec |= [](in_flight(create_msg_with(msg, key)) ==> satisfies(msg.obj.metadata.owner_references, eventual_owner_ref)).
//     3. spec |= [](key_exists(key) ==> resource_obj_of(key) has no finalizers).
//     4. spec |= [](!satisfies(eventual_owner_ref, key) => Self::garbage_collector_deletion_enabled).
// 1 is used to prove the stability; otherwise, even if the invalid object is deleted, the current system may also create an invalid
// object or update the obejct into an invalid status.
// In 3, no finalizers ensures the deletion will be done as long as the deleted request is received, used by
// lemma_delete_msg_in_flight_leads_to_owner_references_satisfies.
// 4 is quite intuitive. To reach the expected owner references state, we must ensure that if it's not expected, it satifies
// the precondition of gc deleting it. Suppose eventual_owner_ref is owner_ref == Some(seq![o]), then the object of the given key
// if with any other owner references, should be deleted. 4 basically limits the domain of "any other owner references". For example,
// in rabbitmq controller, the universal set should be the set of any cr's controller owner ref that has once been in reconcile.
// If we don't have this, suppose owner_ref == None, then the object won't be deleted.
//
// The proof of spec |= true ~> objects_owner_references_satisfies(eventual_owner_ref) consists of two parts:
//     1. spec |= true ~> (object_has_invalid_owner_reference ==> delete message in flight).
//     2. spec |= (object_has_invalid_owner_reference ==> delete message in flight) ~> all_objects_have_expected_owner_references.
// The first is primarily obtained by the weak fairness of the builtin controllers action (specifially, the garbage collector);
// and the second holds due to the weak fairness of kubernetes api.
//
// This lemma is enough for current proof, if later we introduce more complex case, we can try to strengthen it.
pub proof fn lemma_eventually_objects_owner_references_satisfies(
    self, spec: TempPred<ClusterState>, key: ObjectRef, eventual_owner_ref: spec_fn(Option<Seq<OwnerReferenceView>>) -> bool
)
    requires
        spec.entails(always(lift_action(self.next()))),
        spec.entails(tla_forall(|i| self.api_server_next().weak_fairness(i))),
        spec.entails(tla_forall(|i| self.builtin_controllers_next().weak_fairness(i))),
        spec.entails(always(lift_state(Self::req_drop_disabled()))),
        spec.entails(always(lift_state(Self::every_create_msg_sets_owner_references_as(key, eventual_owner_ref)))),
        spec.entails(always(lift_state(Self::every_update_msg_sets_owner_references_as(key, eventual_owner_ref)))),
        spec.entails(always(lift_state(Self::no_create_msg_that_uses_generate_name(key.kind, key.namespace)))),
        spec.entails(always(lift_state(Self::object_has_no_finalizers(key)))),
        // If the current owner_references does not satisfy the eventual requirement, the gc action is enabled.
        spec.entails(always(lift_state(Self::objects_owner_references_violates(key, eventual_owner_ref)).implies(lift_state(Self::garbage_collector_deletion_enabled(key))))),
        spec.entails(always(lift_state(Self::each_object_in_etcd_is_weakly_well_formed()))),
    ensures spec.entails(true_pred().leads_to(always(lift_state(Self::objects_owner_references_satisfies(key, eventual_owner_ref))))),
{
    // We split `true` into two cases:
    //     a. The object's owner references violates eventual_owner_ref.
    //     b. The object's owner references satisfies eventual_owner_ref.
    // b. is already the post state. We only need to show spec |= case a ~> post. This is straightforward via the weak fairness of builtin
    // controllers. Note that from precondition 4, we can replace a. with the "pre" (the variable in the lemma body).

    let pre = |s: ClusterState| {
        &&& Self::objects_owner_references_violates(key, eventual_owner_ref)(s)
        &&& Self::garbage_collector_deletion_enabled(key)(s)
    };

    let delete_msg_in_flight = |s: ClusterState| {
        Self::objects_owner_references_violates(key, eventual_owner_ref)(s) ==> Self::exists_effective_delete_request_msg_for_key(key)(s)
    };
    let post = Self::objects_owner_references_satisfies(key, eventual_owner_ref);

    let input = (BuiltinControllerChoice::GarbageCollector, key);
    let stronger_next = |s, s_prime| {
        &&& self.next()(s, s_prime)
        &&& Self::every_create_msg_sets_owner_references_as(key, eventual_owner_ref)(s)
        &&& Self::every_update_msg_sets_owner_references_as(key, eventual_owner_ref)(s)
        &&& Self::no_create_msg_that_uses_generate_name(key.kind, key.namespace)(s)
        &&& Self::objects_owner_references_violates(key, eventual_owner_ref)(s) ==> Self::garbage_collector_deletion_enabled(key)(s)
        &&& Self::objects_owner_references_violates(key, eventual_owner_ref)(s_prime) ==> Self::garbage_collector_deletion_enabled(key)(s_prime)
    };
    always_to_always_later(spec, lift_state(Self::objects_owner_references_violates(key, eventual_owner_ref)).implies(lift_state(Self::garbage_collector_deletion_enabled(key))));
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(self.next()),
        lift_state(Self::every_create_msg_sets_owner_references_as(key, eventual_owner_ref)),
        lift_state(Self::every_update_msg_sets_owner_references_as(key, eventual_owner_ref)),
        lift_state(Self::no_create_msg_that_uses_generate_name(key.kind, key.namespace)),
        lift_state(Self::objects_owner_references_violates(key, eventual_owner_ref)).implies(lift_state(Self::garbage_collector_deletion_enabled(key))),
        later(lift_state(Self::objects_owner_references_violates(key, eventual_owner_ref)).implies(lift_state(Self::garbage_collector_deletion_enabled(key))))
    );

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) && self.builtin_controllers_next().forward(input)(s, s_prime) implies delete_msg_in_flight(s_prime) by {
        let preconditions = PreconditionsView {
            uid: s.api_server.resources[key].metadata.uid,
            resource_version: None,
        };
        let delete_req_msg = built_in_controller_req_msg(s.rpc_id_allocator.allocate().1, delete_req_msg_content(key, Some(preconditions)));
        assert(s_prime.in_flight().contains(delete_req_msg));
    }

    assert forall |s, s_prime| pre(s) && #[trigger] stronger_next(s, s_prime) implies pre(s_prime) || delete_msg_in_flight(s_prime) by {
        let step = choose |step| self.next_step(s, s_prime, step);
        match step {
            Step::BuiltinControllersStep(i) => {
                if i == input {
                    assert(Self::garbage_collector_deletion_enabled(key)(s));
                    let preconditions = PreconditionsView {
                        uid: s.api_server.resources[key].metadata.uid,
                        resource_version: None,
                    };
                    let delete_req_msg = built_in_controller_req_msg(s.rpc_id_allocator.allocate().1, delete_req_msg_content(key, Some(preconditions)));
                    assert(s_prime.in_flight().contains(delete_req_msg));
                    assert(Self::exists_effective_delete_request_msg_for_key(key)(s_prime));
                    assert(delete_msg_in_flight(s_prime));
                } else {
                    assert(pre(s_prime));
                }
            },
            _ => {
                assert(pre(s_prime) || delete_msg_in_flight(s_prime));
            }
        }
    }

    self.lemma_pre_leads_to_post_by_builtin_controllers(
        spec, input, stronger_next, BuiltinControllersStep::RunGarbageCollector, pre, delete_msg_in_flight
    );

    leads_to_self_temp(lift_state(post));

    assert_by(
        spec.entails(lift_state(Self::objects_owner_references_violates(key, eventual_owner_ref)).leads_to(lift_state(post))),
        {
            self.lemma_delete_msg_in_flight_leads_to_owner_references_satisfies(spec, key, eventual_owner_ref);
            or_leads_to_combine_and_equality!(spec, lift_state(delete_msg_in_flight), lift_state(post), lift_state(Self::exists_effective_delete_request_msg_for_key(key)); lift_state(post));
            leads_to_trans_n!(spec, lift_state(pre), lift_state(delete_msg_in_flight), lift_state(post));

            temp_pred_equality(lift_state(Self::objects_owner_references_violates(key, eventual_owner_ref)).implies(lift_state(Self::garbage_collector_deletion_enabled(key))), lift_state(Self::objects_owner_references_violates(key, eventual_owner_ref)).implies(lift_state(pre)));
            leads_to_weaken(spec, lift_state(pre), lift_state(post), lift_state(Self::objects_owner_references_violates(key, eventual_owner_ref)), lift_state(post));
        }
    );

    or_leads_to_combine_and_equality!(spec, true_pred(), lift_state(Self::objects_owner_references_violates(key, eventual_owner_ref)), lift_state(post); lift_state(post));

    assert forall |s, s_prime| post(s) && #[trigger] stronger_next(s, s_prime) implies post(s_prime) by {
        let step = choose |step| self.next_step(s, s_prime, step);
        match step {
            Step::APIServerStep(input) => {
                let req = input->0;
                if resource_create_request_msg(key)(req) {} else {}
                if resource_update_request_msg(key)(req) {} else {}
                if resource_get_then_update_request_msg(key)(req) {} else {}
                if resource_create_request_msg_without_name(key.kind, key.namespace)(req) {} else {}
            },
            _ => {}
        }
    }

    leads_to_stable(spec, lift_action(stronger_next), true_pred(), lift_state(post));
}

proof fn lemma_delete_msg_in_flight_leads_to_owner_references_satisfies(
    self, spec: TempPred<ClusterState>, key: ObjectRef, eventual_owner_ref: spec_fn(Option<Seq<OwnerReferenceView>>) -> bool
)
    requires
        spec.entails(always(lift_state(Self::req_drop_disabled()))),
        spec.entails(tla_forall(|i| self.api_server_next().weak_fairness(i))),
        spec.entails(always(lift_action(self.next()))),
        spec.entails(always(lift_state(Self::every_create_msg_sets_owner_references_as(key, eventual_owner_ref)))),
        spec.entails(always(lift_state(Self::every_update_msg_sets_owner_references_as(key, eventual_owner_ref)))),
        spec.entails(always(lift_state(Self::object_has_no_finalizers(key)))),
        spec.entails(always(lift_state(Self::each_object_in_etcd_is_weakly_well_formed()))),
    ensures spec.entails(lift_state(Self::exists_effective_delete_request_msg_for_key(key)).leads_to(lift_state(Self::objects_owner_references_satisfies(key, eventual_owner_ref)))),
{
    let pre = Self::exists_effective_delete_request_msg_for_key(key);
    let post = Self::objects_owner_references_satisfies(key, eventual_owner_ref);
    assert_by(
        spec.entails(lift_state(pre).leads_to(lift_state(post))),
        {
            let msg_to_p = |msg: Message| lift_state(Self::effective_delete_request_msg_for_key(key, msg));
            assert forall |msg: Message| spec.entails((#[trigger] msg_to_p(msg)).leads_to(lift_state(post))) by {
                let input = Some(msg);
                let msg_to_p_state = Self::effective_delete_request_msg_for_key(key, msg);
                let stronger_next = |s, s_prime| {
                    &&& self.next()(s, s_prime)
                    &&& Self::req_drop_disabled()(s)
                    &&& Self::every_create_msg_sets_owner_references_as(key, eventual_owner_ref)(s)
                    &&& Self::every_update_msg_sets_owner_references_as(key, eventual_owner_ref)(s)
                    &&& Self::object_has_no_finalizers(key)(s)
                    &&& Self::each_object_in_etcd_is_weakly_well_formed()(s)
                };
                combine_spec_entails_always_n!(
                    spec, lift_action(stronger_next),
                    lift_action(self.next()),
                    lift_state(Self::req_drop_disabled()),
                    lift_state(Self::every_create_msg_sets_owner_references_as(key, eventual_owner_ref)),
                    lift_state(Self::every_update_msg_sets_owner_references_as(key, eventual_owner_ref)),
                    lift_state(Self::object_has_no_finalizers(key)),
                    lift_state(Self::each_object_in_etcd_is_weakly_well_formed())
                );
                self.lemma_pre_leads_to_post_by_api_server(spec, input, stronger_next, APIServerStep::HandleRequest, msg_to_p_state, post);
            }
            leads_to_exists_intro(spec, msg_to_p, lift_state(post));
            assert_by(
                tla_exists(msg_to_p) == lift_state(pre),
                {
                    assert forall |ex| #[trigger] lift_state(pre).satisfied_by(ex) implies tla_exists(msg_to_p).satisfied_by(ex) by {
                        let msg = choose |msg| {
                            &&& #[trigger] ex.head().in_flight().contains(msg)
                            &&& ex.head().api_server.resources.contains_key(key)
                            &&& msg.dst.is_APIServer()
                            &&& msg.content.is_delete_request_with_key(key)
                            &&& msg.content.get_delete_request().preconditions->0.uid == ex.head().api_server.resources[key].metadata.uid
                            &&& msg.content.get_delete_request().preconditions->0.resource_version is None
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
