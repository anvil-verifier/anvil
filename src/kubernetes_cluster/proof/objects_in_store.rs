use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    api_server::state_machine::{unmarshallable_object, valid_object},
    cluster::*,
};
use crate::temporal_logic::{defs::*, rules::*};
use vstd::prelude::*;

verus! {

impl Cluster {

pub open spec fn etcd_object_is_weakly_well_formed(key: ObjectRef) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let obj = s.resources()[key];
        &&& obj.metadata.well_formed_for_namespaced()
        &&& obj.object_ref() == key
        &&& obj.metadata.resource_version->0 < s.api_server.resource_version_counter
        &&& obj.metadata.uid->0 < s.api_server.uid_counter
    }
}

pub open spec fn etcd_objects_have_unique_uids() -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |k1: ObjectRef, k2: ObjectRef| {
            &&& #[trigger] s.resources().contains_key(k1)
            &&& #[trigger] s.resources().contains_key(k2)
            &&& k1 != k2
        } ==> s.resources()[k1].metadata.uid->0 != s.resources()[k2].metadata.uid->0
    }
}

pub open spec fn each_object_in_etcd_is_weakly_well_formed() -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |key: ObjectRef|
            #[trigger] s.resources().contains_key(key)
                ==> Self::etcd_object_is_weakly_well_formed(key)(s)
    }
}

// TODO: investigate flaky proof
#[verifier(rlimit(200))]
pub proof fn lemma_always_each_object_in_etcd_is_weakly_well_formed(self, spec: TempPred<ClusterState>)
    requires
        spec.entails(lift_state(self.init())),
        spec.entails(always(lift_action(self.next()))),
    ensures spec.entails(always(lift_state(Self::each_object_in_etcd_is_weakly_well_formed()))),
{
    let invariant = Self::each_object_in_etcd_is_weakly_well_formed();

    assert forall |s, s_prime| invariant(s) && #[trigger] self.next()(s, s_prime) implies invariant(s_prime) by {
        assert forall |key: ObjectRef| #[trigger] s_prime.resources().contains_key(key)
        implies Self::etcd_object_is_weakly_well_formed(key)(s_prime) by {
            if s.resources().contains_key(key) {} else {}
        }
    }

    init_invariant(spec, self.init(), self.next(), invariant);
}

pub proof fn lemma_always_etcd_objects_have_unique_uids(self, spec: TempPred<ClusterState>)
    requires
        spec.entails(lift_state(self.init())),
        spec.entails(always(lift_action(self.next()))),
        spec.entails(always(lift_state(Self::each_object_in_etcd_is_weakly_well_formed()))),
    ensures spec.entails(always(lift_state(Self::etcd_objects_have_unique_uids()))),
{
    let invariant = Self::etcd_objects_have_unique_uids();
    let stronger_next = |s: ClusterState, s_prime: ClusterState| {
        &&& self.next()(s, s_prime)
        &&& Self::each_object_in_etcd_is_weakly_well_formed()(s)
    };
    combine_spec_entails_always_n!(
        spec,
        lift_action(stronger_next),
        lift_action(self.next()),
        lift_state(Self::each_object_in_etcd_is_weakly_well_formed())
    );
    assert forall |s, s_prime| invariant(s) && #[trigger] stronger_next(s, s_prime) implies invariant(s_prime) by {
        assert forall |k1: ObjectRef, k2: ObjectRef| {
            &&& #[trigger] s_prime.resources().contains_key(k1)
            &&& #[trigger] s_prime.resources().contains_key(k2)
            &&& k1 != k2
        } implies s_prime.resources()[k1].metadata.uid->0 != s_prime.resources()[k2].metadata.uid->0 by {
            if s.resources().contains_key(k1) {
                if !s.resources().contains_key(k2) {
                    assert(s_prime.resources()[k2].metadata.uid->0 == s.api_server.uid_counter);
                }
            } else {
                if s.resources().contains_key(k2) {
                    assert(s_prime.resources()[k1].metadata.uid->0 == s.api_server.uid_counter);
                }
            }
        }
    }
    init_invariant(spec, self.init(), stronger_next, invariant);
}


pub open spec fn etcd_object_is_well_formed(self, key: ObjectRef) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let obj = s.resources()[key];
        &&& Self::etcd_object_is_weakly_well_formed(key)(s)
        &&& unmarshallable_object(obj, self.installed_types)
        &&& valid_object(obj, self.installed_types)
    }
}

pub open spec fn each_builtin_object_in_etcd_is_well_formed(self) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |key: ObjectRef|
            #[trigger] s.resources().contains_key(key)
            && !key.kind is CustomResourceKind
                ==> self.etcd_object_is_well_formed(key)(s)
    }
}

#[verifier(rlimit(100))]
pub proof fn lemma_always_each_builtin_object_in_etcd_is_well_formed(self, spec: TempPred<ClusterState>)
    requires
        spec.entails(lift_state(self.init())),
        spec.entails(always(lift_action(self.next()))),
    ensures spec.entails(always(lift_state(self.each_builtin_object_in_etcd_is_well_formed()))),
{
    let invariant = self.each_builtin_object_in_etcd_is_well_formed();

    assert forall |s, s_prime| invariant(s) && #[trigger] self.next()(s, s_prime) implies invariant(s_prime) by {
        assert forall |key: ObjectRef| #[trigger] s_prime.resources().contains_key(key) && !key.kind is CustomResourceKind
        implies self.etcd_object_is_well_formed(key)(s_prime) by {
            if s.resources().contains_key(key) {
                assert(self.etcd_object_is_well_formed(key)(s));
                let step = choose |step| self.next_step(s, s_prime, step);
                match step {
                    Step::APIServerStep(input) => {
                        match input->0.content->APIRequest_0 {
                            APIRequest::GetRequest(_) => {}
                            APIRequest::ListRequest(_) => {}
                            APIRequest::CreateRequest(_) => {}
                            APIRequest::DeleteRequest(_) => {}
                            APIRequest::UpdateRequest(_) => {}
                            APIRequest::UpdateStatusRequest(_) => {}
                            APIRequest::GetThenDeleteRequest(_) => {}
                            APIRequest::GetThenUpdateRequest(_) => {}
                        }
                    }
                    _ => {}
                }
            } else {
                let step = choose |step| self.next_step(s, s_prime, step);
                match step {
                    Step::APIServerStep(input) => {
                        match input->0.content->APIRequest_0 {
                            APIRequest::GetRequest(_) => {}
                            APIRequest::ListRequest(_) => {}
                            APIRequest::CreateRequest(_) => {
                                ConfigMapView::marshal_status_preserves_integrity();
                                DaemonSetView::marshal_status_preserves_integrity();
                                PersistentVolumeClaimView::marshal_status_preserves_integrity();
                                PodView::marshal_status_preserves_integrity();
                                RoleBindingView::marshal_status_preserves_integrity();
                                RoleView::marshal_status_preserves_integrity();
                                SecretView::marshal_status_preserves_integrity();
                                ServiceView::marshal_status_preserves_integrity();
                                StatefulSetView::marshal_status_preserves_integrity();
                                ServiceAccountView::marshal_status_preserves_integrity();
                            }
                            APIRequest::DeleteRequest(_) => {}
                            APIRequest::UpdateRequest(_) => {}
                            APIRequest::UpdateStatusRequest(_) => {}
                            APIRequest::GetThenDeleteRequest(_) => {}
                            APIRequest::GetThenUpdateRequest(_) => {}
                        }
                    }
                    _ => {}
                }
            }
        }
    }

    init_invariant(spec, self.init(), self.next(), invariant);
}

pub open spec fn each_custom_object_in_etcd_is_well_formed<T: CustomResourceView>(self) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |key: ObjectRef|
            #[trigger] s.resources().contains_key(key)
            && key.kind == T::kind()
                ==> self.etcd_object_is_well_formed(key)(s)
    }
}

pub proof fn lemma_always_each_custom_object_in_etcd_is_well_formed<T: CustomResourceView>(self, spec: TempPred<ClusterState>)
    requires
        spec.entails(lift_state(self.init())),
        spec.entails(always(lift_action(self.next()))),
        self.type_is_installed_in_cluster::<T>(),
    ensures spec.entails(always(lift_state(self.each_custom_object_in_etcd_is_well_formed::<T>()))),
{
    let invariant = self.each_custom_object_in_etcd_is_well_formed::<T>();

    T::kind_is_custom_resource();
    assert forall |s, s_prime| invariant(s) && #[trigger] self.next()(s, s_prime) implies invariant(s_prime) by {
        assert forall |key: ObjectRef| #[trigger] s_prime.resources().contains_key(key) && key.kind == T::kind()
        implies self.etcd_object_is_well_formed(key)(s_prime) by {
            if s.resources().contains_key(key) {
                assert(self.etcd_object_is_well_formed(key)(s));
                let step = choose |step| self.next_step(s, s_prime, step);
                match step {
                    Step::APIServerStep(input) => {
                        match input->0.content->APIRequest_0 {
                            APIRequest::GetRequest(_) => {}
                            APIRequest::ListRequest(_) => {}
                            APIRequest::CreateRequest(_) => {}
                            APIRequest::DeleteRequest(_) => {
                                let obj = s.resources()[key];
                                let t_obj = T::unmarshal(obj)->Ok_0;
                                T::unmarshal_result_determined_by_unmarshal_spec_and_status();
                                T::validation_result_determined_by_spec_and_status();
                                assert(t_obj.state_validation() == T::spec_status_validation(t_obj.spec(), t_obj.status()));
                                assert(valid_object(obj, self.installed_types));
                            }
                            APIRequest::UpdateRequest(_) => {}
                            APIRequest::UpdateStatusRequest(_) => {}
                            APIRequest::GetThenDeleteRequest(_) => {
                                let obj = s.resources()[key];
                                let t_obj = T::unmarshal(obj)->Ok_0;
                                T::unmarshal_result_determined_by_unmarshal_spec_and_status();
                                T::validation_result_determined_by_spec_and_status();
                                assert(t_obj.state_validation() == T::spec_status_validation(t_obj.spec(), t_obj.status()));
                                assert(valid_object(obj, self.installed_types));
                            }
                            APIRequest::GetThenUpdateRequest(_) => {}
                        }
                    }
                    _ => {}
                }
            } else {
                let step = choose |step| self.next_step(s, s_prime, step);
                match step {
                    Step::APIServerStep(input) => {
                        match input->0.content->APIRequest_0 {
                            APIRequest::GetRequest(_) => {}
                            APIRequest::ListRequest(_) => {}
                            APIRequest::CreateRequest(_) => {
                                T::marshal_status_preserves_integrity();
                            }
                            APIRequest::DeleteRequest(_) => {}
                            APIRequest::UpdateRequest(_) => {}
                            APIRequest::UpdateStatusRequest(_) => {}
                            APIRequest::GetThenDeleteRequest(_) => {}
                            APIRequest::GetThenUpdateRequest(_) => {}
                        }
                    }
                    _ => {}
                }
            }
        }
    }

    init_invariant(spec, self.init(), self.next(), invariant);
}

pub open spec fn each_object_in_etcd_is_well_formed<T: CustomResourceView>(self) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |key: ObjectRef|
            #[trigger] s.resources().contains_key(key)
            && (!key.kind is CustomResourceKind && key.kind == T::kind())
                ==> self.etcd_object_is_well_formed(key)(s)
    }
}

pub proof fn lemma_always_each_object_in_etcd_is_well_formed<T: CustomResourceView>(self, spec: TempPred<ClusterState>)
    requires
        spec.entails(lift_state(self.init())),
        spec.entails(always(lift_action(self.next()))),
        self.type_is_installed_in_cluster::<T>(),
    ensures spec.entails(always(lift_state(self.each_object_in_etcd_is_well_formed::<T>()))),
{
    let invariant = self.each_object_in_etcd_is_well_formed::<T>();

    T::kind_is_custom_resource();
    self.lemma_always_each_builtin_object_in_etcd_is_well_formed(spec);
    self.lemma_always_each_custom_object_in_etcd_is_well_formed::<T>(spec);
    let p1 = self.each_builtin_object_in_etcd_is_well_formed();
    let p2 = self.each_custom_object_in_etcd_is_well_formed::<T>();
    let p = |s| {
        &&& p1(s)
        &&& p2(s)
    };
    entails_always_and_n!(spec, lift_state(p1), lift_state(p2));
    temp_pred_equality(lift_state(p1).and(lift_state(p2)), lift_state(p));
    always_weaken::<ClusterState>(spec, lift_state(p), lift_state(invariant));
}

pub open spec fn each_object_in_etcd_has_at_most_one_controller_owner() -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |key: ObjectRef|
            #[trigger] s.resources().contains_key(key)
                ==> {
                    let obj = s.resources()[key];
                    let owners = obj.metadata.owner_references->0;
                    let controller_owners = owners.filter(
                        |o: OwnerReferenceView| o.controller is Some && o.controller->0
                    );
                    obj.metadata.owner_references is Some ==> controller_owners.len() <= 1
                }
    }
}

pub proof fn lemma_always_each_object_in_etcd_has_at_most_one_controller_owner(self, spec: TempPred<ClusterState>)
    requires
        spec.entails(lift_state(self.init())),
        spec.entails(always(lift_action(self.next()))),
    ensures spec.entails(always(lift_state(Self::each_object_in_etcd_has_at_most_one_controller_owner())))
{
    init_invariant(
        spec, self.init(), self.next(),
        Self::each_object_in_etcd_has_at_most_one_controller_owner()
    );
}

pub open spec fn etcd_is_finite() -> StatePred<ClusterState> {
    |s: ClusterState| s.resources().dom().finite()
}

pub proof fn lemma_always_etcd_is_finite(
    self, spec: TempPred<ClusterState>,
)
    requires
        spec.entails(lift_state(self.init())),
        spec.entails(always(lift_action(self.next()))),
    ensures spec.entails(always(lift_state(Self::etcd_is_finite()))),
{
    init_invariant(spec, self.init(), self.next(), Self::etcd_is_finite());
}

}

}
