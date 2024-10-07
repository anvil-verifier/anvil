use crate::kubernetes_api_objects::spec::prelude::*;
use crate::temporal_logic::{defs::*, rules::*};
use crate::kubernetes_cluster::spec::{cluster::*, message::*};
use vstd::prelude::*;

verus! {

impl Cluster {

pub open spec fn crash_disabled(controller_id: int) -> StatePred<ClusterState> {
    |s: ClusterState| !s.controller_and_externals[controller_id].crash_enabled
}

pub proof fn lemma_true_leads_to_crash_always_disabled(self, spec: TempPred<ClusterState>, controller_id: int)
    requires
        spec.entails(lift_state(self.init())),
        spec.entails(always(lift_action(self.next()))),
        spec.entails(self.disable_crash().weak_fairness(controller_id)),
        self.controller_models.contains_key(controller_id)
    ensures spec.entails(true_pred().leads_to(always(lift_state(Self::crash_disabled(controller_id))))),
{
    let true_state = |s: ClusterState| true;
    self.disable_crash().wf1(controller_id, spec, self.next(), true_state, Self::crash_disabled(controller_id));
    self.lemma_always_there_is_the_controller_state(spec, controller_id);
    let stronger_next = |s, s_prime| {
        &&& self.next()(s, s_prime)
        &&& Self::there_is_the_controller_state(controller_id)(s)
    };
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next), lift_action(self.next()),
        lift_state(Self::there_is_the_controller_state(controller_id))
    );
    leads_to_stable(spec, lift_action(stronger_next), true_pred(), lift_state(Self::crash_disabled(controller_id)));
}

pub open spec fn req_drop_disabled() -> StatePred<ClusterState> {
    |s: ClusterState| !s.req_drop_enabled
}

pub proof fn lemma_true_leads_to_req_drop_always_disabled(self, spec: TempPred<ClusterState>)
    requires
        spec.entails(always(lift_action(self.next()))),
        spec.entails(self.disable_req_drop().weak_fairness(())),
    ensures spec.entails(true_pred().leads_to(always(lift_state(Self::req_drop_disabled())))),
{
    let true_state = |s: ClusterState| true;
    self.disable_req_drop().wf1((), spec, self.next(), true_state, Self::req_drop_disabled());
    leads_to_stable(spec, lift_action(self.next()), true_pred(), lift_state(Self::req_drop_disabled()));
}

}

}
