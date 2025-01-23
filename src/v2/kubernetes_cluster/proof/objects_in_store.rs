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
        &&& obj.metadata.well_formed()
        &&& obj.object_ref() == key
        &&& obj.metadata.resource_version.get_Some_0() < s.api_server.resource_version_counter
        &&& obj.metadata.uid.get_Some_0() < s.api_server.uid_counter
    }
}

pub open spec fn each_object_in_etcd_is_weakly_well_formed() -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |key: ObjectRef|
            #[trigger] s.resources().contains_key(key)
                ==> Self::etcd_object_is_weakly_well_formed(key)(s)
    }
}

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
            && !key.kind.is_CustomResourceKind()
                ==> self.etcd_object_is_well_formed(key)(s)
    }
}

pub proof fn lemma_always_each_builtin_object_in_etcd_is_well_formed(self, spec: TempPred<ClusterState>)
    requires
        spec.entails(lift_state(self.init())),
        spec.entails(always(lift_action(self.next()))),
    ensures spec.entails(always(lift_state(self.each_builtin_object_in_etcd_is_well_formed()))),
{
    let invariant = self.each_builtin_object_in_etcd_is_well_formed();

    assert forall |s, s_prime| invariant(s) && #[trigger] self.next()(s, s_prime) implies invariant(s_prime) by {
        assert forall |key: ObjectRef| #[trigger] s_prime.resources().contains_key(key) && !key.kind.is_CustomResourceKind()
        implies self.etcd_object_is_well_formed(key)(s_prime) by {
            if s.resources().contains_key(key) {
                assert(self.etcd_object_is_well_formed(key)(s));
                let step = choose |step| self.next_step(s, s_prime, step);
                match step {
                    Step::APIServerStep(input) => {
                        match input.get_Some_0().content.get_APIRequest_0() {
                            APIRequest::GetRequest(_) => {}
                            APIRequest::ListRequest(_) => {}
                            APIRequest::CreateRequest(_) => {}
                            APIRequest::DeleteRequest(_) => {}
                            APIRequest::UpdateRequest(_) => {}
                            APIRequest::UpdateStatusRequest(_) => {}
                        }
                    }
                    _ => {}
                }
            } else {
                let step = choose |step| self.next_step(s, s_prime, step);
                match step {
                    Step::APIServerStep(input) => {
                        match input.get_Some_0().content.get_APIRequest_0() {
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
                        match input.get_Some_0().content.get_APIRequest_0() {
                            APIRequest::GetRequest(_) => {}
                            APIRequest::ListRequest(_) => {}
                            APIRequest::CreateRequest(_) => {}
                            APIRequest::DeleteRequest(_) => {
                                let obj = s.resources()[key];
                                let t_obj = T::unmarshal(obj).get_Ok_0();
                                T::unmarshal_result_determined_by_unmarshal_spec_and_status();
                                T::validation_result_determined_by_spec_and_status();
                                assert(t_obj.state_validation() == T::spec_status_validation(t_obj.spec(), t_obj.status()));
                                assert(valid_object(obj, self.installed_types));
                            }
                            APIRequest::UpdateRequest(_) => {}
                            APIRequest::UpdateStatusRequest(_) => {}
                        }
                    }
                    _ => {}
                }
            } else {
                let step = choose |step| self.next_step(s, s_prime, step);
                match step {
                    Step::APIServerStep(input) => {
                        match input.get_Some_0().content.get_APIRequest_0() {
                            APIRequest::GetRequest(_) => {}
                            APIRequest::ListRequest(_) => {}
                            APIRequest::CreateRequest(_) => {
                                T::marshal_status_preserves_integrity();
                            }
                            APIRequest::DeleteRequest(_) => {}
                            APIRequest::UpdateRequest(_) => {}
                            APIRequest::UpdateStatusRequest(_) => {}
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
            && (!key.kind.is_CustomResourceKind() && key.kind == T::kind())
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
                    let owners = obj.metadata.owner_references.get_Some_0();
                    let controller_owners = owners.filter(
                        |o: OwnerReferenceView| o.controller.is_Some() && o.controller.get_Some_0()
                    );
                    obj.metadata.owner_references.is_Some() ==> controller_owners.len() <= 1
                }
    }
}
//
// TODO: Prove this (probably Cathy).
//

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
    let inv = Self::etcd_is_finite();
    let stronger_next = |s, s_prime: ClusterState| {
        &&& self.next()(s, s_prime)
    };
    
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(self.next())
    );
    init_invariant(spec, self.init(), stronger_next, inv);
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
    let inv = Self::etcd_is_finite();
    let stronger_next = |s, s_prime: ClusterState| {
        &&& self.next()(s, s_prime)
    };
    
    combine_spec_entails_always_n!(
        spec, lift_action(stronger_next),
        lift_action(self.next())
    );
    init_invariant(spec, self.init(), stronger_next, inv);
}

}

}
