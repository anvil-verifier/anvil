use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{cluster::*, message::*};
use crate::temporal_logic::{defs::*, rules::*};
use crate::vstd_ext::string_view::StringView;
use vstd::prelude::*;

verus! {

impl Cluster {

pub open spec fn each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |key: ObjectRef|
            #[trigger] s.scheduled_reconciles(controller_id).contains_key(key)
                ==> s.scheduled_reconciles(controller_id)[key].object_ref() == key
                    && s.scheduled_reconciles(controller_id)[key].metadata.well_formed()
    }
}

pub proof fn lemma_always_each_scheduled_object_has_consistent_key_and_valid_metadata(self, spec: TempPred<ClusterState>, controller_id: int)
    requires
        spec.entails(lift_state(self.init())),
        spec.entails(always(lift_action(self.next()))),
        self.controller_models.contains_key(controller_id),
    ensures spec.entails(always(lift_state(Self::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id)))),
{
    let invariant = Self::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id);

    self.lemma_always_each_object_in_etcd_is_weakly_well_formed(spec);
    self.lemma_always_there_is_the_controller_state(spec, controller_id);

    let stronger_next = |s, s_prime| {
        &&& self.next()(s, s_prime)
        &&& Self::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& Self::there_is_the_controller_state(controller_id)(s)
    };

    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next), lift_action(self.next()),
        lift_state(Self::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(Self::there_is_the_controller_state(controller_id))
    );

    assert forall |s, s_prime| invariant(s) && #[trigger] stronger_next(s, s_prime) implies invariant(s_prime) by {
        assert forall |key: ObjectRef| #[trigger] s_prime.scheduled_reconciles(controller_id).contains_key(key)
        implies
            s_prime.scheduled_reconciles(controller_id)[key].object_ref() == key
            && s_prime.scheduled_reconciles(controller_id)[key].metadata.well_formed()
        by {
            let step = choose |step| self.next_step(s, s_prime, step);
            match step {
                Step::ScheduleControllerReconcileStep(input) => {},
                _ => {
                    assert(s.scheduled_reconciles(controller_id).contains_key(key));
                }
            }
        }
    }

    init_invariant(spec, self.init(), stronger_next, invariant);
}

pub open spec fn each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |key: ObjectRef|
            #[trigger] s.ongoing_reconciles(controller_id).contains_key(key)
                ==> s.ongoing_reconciles(controller_id)[key].triggering_cr.object_ref() == key
                    && s.ongoing_reconciles(controller_id)[key].triggering_cr.metadata.well_formed()
    }
}

pub proof fn lemma_always_each_object_in_reconcile_has_consistent_key_and_valid_metadata(self, spec: TempPred<ClusterState>, controller_id: int)
    requires
        spec.entails(lift_state(self.init())),
        spec.entails(always(lift_action(self.next()))),
        self.controller_models.contains_key(controller_id),
    ensures spec.entails(always(lift_state(Self::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id)))),
{
    let invariant = Self::each_object_in_reconcile_has_consistent_key_and_valid_metadata(controller_id);

    self.lemma_always_each_scheduled_object_has_consistent_key_and_valid_metadata(spec, controller_id);
    self.lemma_always_there_is_the_controller_state(spec, controller_id);

    let stronger_next = |s, s_prime| {
        &&& self.next()(s, s_prime)
        &&& Self::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id)(s)
        &&& Self::there_is_the_controller_state(controller_id)(s)
    };

    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next), lift_action(self.next()),
        lift_state(Self::each_scheduled_object_has_consistent_key_and_valid_metadata(controller_id)),
        lift_state(Self::there_is_the_controller_state(controller_id))
    );

    assert forall |s, s_prime| invariant(s) && #[trigger] stronger_next(s, s_prime) implies invariant(s_prime) by {
        assert forall |key: ObjectRef| #[trigger] s_prime.ongoing_reconciles(controller_id).contains_key(key)
        implies
            s_prime.ongoing_reconciles(controller_id)[key].triggering_cr.object_ref() == key
            && s_prime.ongoing_reconciles(controller_id)[key].triggering_cr.metadata.well_formed()
        by {
            if s.ongoing_reconciles(controller_id).contains_key(key) {
            } else {
                assert(s.scheduled_reconciles(controller_id).contains_key(key));
            }
        }
    }

    init_invariant(spec, self.init(), stronger_next, invariant);
}

}

}
