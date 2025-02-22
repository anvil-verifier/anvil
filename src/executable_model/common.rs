use crate::executable_model::string_set::*;
use crate::kubernetes_api_objects::error::UnmarshalError;
use crate::kubernetes_api_objects::exec::{api_resource::ApiResource, prelude::*};
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    api_server::state_machine as model, api_server::types as model_types,
};
use crate::vstd_ext::string_view::StringView;
use vstd::prelude::*;
use vstd::string::*;

// We use ExternalObjectRef, instead of KubeObjectRef, as the key of the ObjectMap
// because the key has to implement a few traits including Ord and PartialOrd.
// It's easy to implement such traits for ExternalObjectRef but hard for KubeObjectRef
// because it internally uses vstd::string::String, which does not implement such traits.
#[derive(Clone, Ord, PartialOrd, Eq, PartialEq)]
pub struct ExternalObjectRef {
    pub kind: KindExec,
    pub name: std::string::String,
    pub namespace: std::string::String,
}

impl KubeObjectRef {
    pub fn into_external_object_ref(self) -> ExternalObjectRef {
        ExternalObjectRef {
            kind: self.kind.clone(),
            name: self.name,
            namespace: self.namespace,
        }
    }
}

verus! {

pub struct KubeObjectRef {
    pub kind: KindExec,
    pub name: String,
    pub namespace: String,
}

impl View for KubeObjectRef {
    type V = ObjectRef;
    open spec fn view(&self) -> ObjectRef {
        ObjectRef {
            kind: self.kind@,
            name: self.name@,
            namespace: self.namespace@,
        }
    }
}

impl std::clone::Clone for KubeObjectRef {
    fn clone(&self) -> (result: Self)
        ensures result == self
    {
        KubeObjectRef {
            kind: self.kind.clone(),
            name: self.name.clone(),
            namespace: self.namespace.clone(),
        }
    }
}

impl ApiResource {
    // This kind() is not a perfect implementation but it is sufficient for conformance tests.
    #[verifier(external_body)]
    pub fn kind(&self) -> (kind: KindExec)
        ensures kind@ == self@.kind,
    {
        match self.as_kube_ref().kind.as_str() {
            "ConfigMap" => KindExec::ConfigMapKind,
            "DaemonSet" => KindExec::DaemonSetKind,
            "PersistentVolumeClaim" => KindExec::PersistentVolumeClaimKind,
            "Pod" => KindExec::PodKind,
            "Role" => KindExec::RoleKind,
            "RoleBinding" => KindExec::RoleBindingKind,
            "StatefulSet" => KindExec::StatefulSetKind,
            "Service" => KindExec::ServiceKind,
            "ServiceAccount" => KindExec::ServiceAccountKind,
            "Secret" => KindExec::SecretKind,
            _ => panic!(), // We assume the DynamicObject won't be a custom object
        }
    }
}

impl ObjectMeta {
    pub fn finalizers_as_set(&self) -> (ret: StringSet)
        ensures ret@ == self@.finalizers_as_set()
    {
        if self.finalizers().is_none() {
            StringSet::empty()
        } else {
            string_vec_to_string_set(self.finalizers().unwrap())
        }
    }
}

impl DynamicObjectView {
    pub open spec fn unset_deletion_timestamp(self) -> DynamicObjectView {
        DynamicObjectView {
            metadata: ObjectMetaView {
                deletion_timestamp: None,
                ..self.metadata
            },
            ..self
        }
    }

    pub open spec fn overwrite_deletion_stamp(self, deletion_timestamp: Option<StringView>) -> DynamicObjectView {
        DynamicObjectView {
            metadata: ObjectMetaView {
                deletion_timestamp: deletion_timestamp,
                ..self.metadata
            },
            ..self
        }
    }

    pub open spec fn overwrite_uid(self, uid: Option<int>) -> DynamicObjectView {
        DynamicObjectView {
            metadata: ObjectMetaView {
                uid: uid,
                ..self.metadata
            },
            ..self
        }
    }

    pub open spec fn overwrite_resource_version(self, resource_version: Option<int>) -> DynamicObjectView {
        DynamicObjectView {
            metadata: ObjectMetaView {
                resource_version: resource_version,
                ..self.metadata
            },
            ..self
        }
    }

    pub open spec fn set_spec(self, spec: Value) -> DynamicObjectView {
        DynamicObjectView {
            spec: spec,
            ..self
        }
    }

    pub open spec fn set_status(self, status: Value) -> DynamicObjectView {
        DynamicObjectView {
            status: status,
            ..self
        }
    }
}

impl DynamicObject {
    // This kind() is not a perfect implementation but it is sufficient for conformance tests.
    #[verifier(external_body)]
    pub fn kind(&self) -> (kind: KindExec)
        ensures kind@ == self@.kind,
    {
        if self.as_kube_ref().types.is_none() {
            panic!();
        }
        match self.as_kube_ref().types.as_ref().unwrap().kind.as_str() {
            "ConfigMap" => KindExec::ConfigMapKind,
            "DaemonSet" => KindExec::DaemonSetKind,
            "PersistentVolumeClaim" => KindExec::PersistentVolumeClaimKind,
            "Pod" => KindExec::PodKind,
            "Role" => KindExec::RoleKind,
            "RoleBinding" => KindExec::RoleBindingKind,
            "StatefulSet" => KindExec::StatefulSetKind,
            "Service" => KindExec::ServiceKind,
            "ServiceAccount" => KindExec::ServiceAccountKind,
            "Secret" => KindExec::SecretKind,
            _ => panic!(), // We assume the DynamicObject won't be a custom object
        }
    }

    // We implement getter and setter functions of the DynamicObject
    // which are used by the exec API server model.

    #[verifier(external_body)]
    pub fn object_ref(&self) -> (object_ref: KubeObjectRef)
        requires
            self@.metadata.name.is_Some(),
            self@.metadata.namespace.is_Some(),
        ensures object_ref@ == self@.object_ref(),
    {
        KubeObjectRef {
            kind: self.kind(),
            name: self.metadata().name().unwrap(),
            namespace: self.metadata().namespace().unwrap(),
        }
    }

    #[verifier(external_body)]
    pub fn set_name(&mut self, name: String)
        ensures self@ == old(self)@.set_name(name@),
    {
        self.as_kube_mut_ref().metadata.name = Some(name);
    }

    #[verifier(external_body)]
    pub fn set_namespace(&mut self, namespace: String)
        ensures self@ == old(self)@.set_namespace(namespace@),
    {
        self.as_kube_mut_ref().metadata.namespace = Some(namespace);
    }

    #[verifier(external_body)]
    pub fn set_resource_version(&mut self, resource_version: i64)
        ensures self@ == old(self)@.set_resource_version(resource_version as int),
    {
        self.as_kube_mut_ref().metadata.resource_version = Some(resource_version.to_string());
    }

    #[verifier(external_body)]
    pub fn set_resource_version_from(&mut self, other: &DynamicObject)
        ensures self@ == old(self)@.overwrite_resource_version(other@.metadata.resource_version),
    {
        self.as_kube_mut_ref().metadata.resource_version = other.as_kube_ref().metadata.resource_version.clone();
    }

    #[verifier(external_body)]
    pub fn set_uid(&mut self, uid: i64)
        ensures self@ == old(self)@.set_uid(uid as int),
    {
        self.as_kube_mut_ref().metadata.uid = Some(uid.to_string());
    }

    #[verifier(external_body)]
    pub fn set_uid_from(&mut self, other: &DynamicObject)
        ensures self@ == old(self)@.overwrite_uid(other@.metadata.uid),
    {
        self.as_kube_mut_ref().metadata.uid = other.as_kube_ref().metadata.uid.clone();
    }

    #[verifier(external_body)]
    pub fn unset_deletion_timestamp(&mut self)
        ensures self@ == old(self)@.unset_deletion_timestamp(),
    {
        self.as_kube_mut_ref().metadata.deletion_timestamp = None;
    }

    #[verifier(external_body)]
    pub fn set_deletion_timestamp_from(&mut self, other: &DynamicObject)
        ensures self@ == old(self)@.overwrite_deletion_stamp(other@.metadata.deletion_timestamp),
    {
        self.as_kube_mut_ref().metadata.deletion_timestamp = other.as_kube_ref().metadata.deletion_timestamp.clone();
    }


    // This function sets the deletion timestamp to the current time.
    // This seems a bit inconsistent with the model's behavior which
    // always sets it to the return value of deletion_timestamp().
    // However, this function is actually closer to Kubernetes' real behavior.
    #[verifier(external_body)]
    pub fn set_current_deletion_timestamp(&mut self)
        ensures self@ == old(self)@.set_deletion_timestamp(model::deletion_timestamp()),
    {
        self.as_kube_mut_ref().metadata.deletion_timestamp = Some(deps_hack::k8s_openapi::apimachinery::pkg::apis::meta::v1::Time(deps_hack::chrono::Utc::now()));
    }

    #[verifier(external_body)]
    pub fn eq(&self, other: &DynamicObject) -> (ret: bool)
        ensures ret == (self@ == other@)
    {
        self.as_kube_ref() == other.as_kube_ref()
    }

    #[verifier(external_body)]
    pub fn set_metadata_from(&mut self, other: &DynamicObject)
        ensures self@ == old(self)@.set_metadata(other@.metadata)
    {
        self.as_kube_mut_ref().metadata = other.as_kube_ref().metadata.clone()
    }

    // We intentionally leave set_spec_from overly sets the data and
    // set_status_from does not set any data because they are rather
    // difficult to implement: we'll have to unmarshal other.inner and extract
    // the spec/status part from the json representation.
    // Since these two are left empty, the conformance test should not check
    // the content of the spec and status.
    #[verifier(external_body)]
    pub fn set_spec_from(&mut self, other: &DynamicObject)
        ensures self@ == old(self)@.set_spec(other@.spec)
    {
        self.as_kube_mut_ref().data = other.as_kube_ref().data.clone()
    }

    #[verifier(external_body)]
    pub fn set_status_from(&mut self, other: &DynamicObject)
        ensures self@ == old(self)@.set_status(other@.status)
    {}

    #[verifier(external_body)]
    pub fn set_default_status<K: CustomResourceView>(&mut self)
        ensures
            self@ == old(self)@.set_status(model::marshalled_default_status::<K>(self@.kind)),
            model::unmarshallable_status::<K>(self@),
    {}
}

// We implement the validation logic in exec code for different k8s object types below
// which are called by the exec API server model.
// These validation functions must conform to their correspondences of the spec-level objects.

impl ConfigMap {
    pub fn state_validation(&self) -> (ret: bool)
        ensures ret == self@.state_validation()
    { true }

    pub fn transition_validation(&self, old_obj: &ConfigMap) -> (ret: bool)
        ensures ret == self@.transition_validation(old_obj@)
    { true }
}

impl DaemonSet {
    pub fn state_validation(&self) -> (ret: bool)
        ensures ret == self@.state_validation()
    { self.spec().is_some() }

    pub fn transition_validation(&self, old_obj: &DaemonSet) -> (ret: bool)
        requires
            self@.state_validation(),
            old_obj@.state_validation(),
        ensures ret == self@.transition_validation(old_obj@)
    {
        self.spec().unwrap().selector().eq(&old_obj.spec().unwrap().selector())
    }
}

impl Pod {
    pub fn state_validation(&self) -> (ret: bool)
        ensures ret == self@.state_validation()
    { self.spec().is_some() }

    pub fn transition_validation(&self, old_obj: &Pod) -> (ret: bool)
        ensures ret == self@.transition_validation(old_obj@)
    { true }
}

impl PersistentVolumeClaim {
    pub fn state_validation(&self) -> (ret: bool)
        ensures ret == self@.state_validation()
    { self.spec().is_some() }

    pub fn transition_validation(&self, old_obj: &PersistentVolumeClaim) -> (ret: bool)
        ensures ret == self@.transition_validation(old_obj@)
    { true }
}

impl PolicyRule {
    pub fn state_validation(&self) -> (ret: bool)
        ensures ret == self@.state_validation()
    {
        self.api_groups().is_some()
        && self.api_groups().as_ref().unwrap().len() > 0
        && self.resources().is_some()
        && self.resources().as_ref().unwrap().len() > 0
        && self.verbs().len() > 0
    }
}

impl Role {
    pub fn state_validation(&self) -> (ret: bool)
        ensures ret == self@.state_validation()
    {
        if self.rules().is_some() {
            let policy_rules = self.rules().unwrap();
            let mut all_valid = true;
            let mut i = 0;
            while i < policy_rules.len()
                invariant
                    all_valid == (forall |j| #![trigger policy_rules[j]] 0 <= j < i ==> policy_rules@.map_values(|policy_rule: PolicyRule| policy_rule@)[j].state_validation()),
                    i <= policy_rules.len(),
            {
                all_valid = all_valid && policy_rules[i].state_validation();
                i += 1;
            }
            all_valid
        } else {
            true
        }
    }

    pub fn transition_validation(&self, old_obj: &Role) -> (ret: bool)
        ensures ret == self@.transition_validation(old_obj@)
    { true }
}

impl RoleBinding {
    pub fn state_validation(&self) -> (ret: bool)
        ensures ret == self@.state_validation()
    {
        self.role_ref().api_group().eq(&"rbac.authorization.k8s.io".to_string())
        && (self.role_ref().kind().eq(&"Role".to_string())
            || self.role_ref().kind().eq(&"ClusterRole".to_string()))
    }

    pub fn transition_validation(&self, old_obj: &RoleBinding) -> (ret: bool)
        ensures ret == self@.transition_validation(old_obj@)
    {
        self.role_ref().eq(&old_obj.role_ref())
    }
}

impl Secret {
    pub fn state_validation(&self) -> (ret: bool)
        ensures ret == self@.state_validation()
    { true }


    pub fn transition_validation(&self, old_obj: &Secret) -> (ret: bool)
        ensures ret == self@.transition_validation(old_obj@)
    { true }
}

impl Service {
    pub fn state_validation(&self) -> (ret: bool)
        ensures ret == self@.state_validation()
    { self.spec().is_some() }

    pub fn transition_validation(&self, old_obj: &Service) -> (ret: bool)
        ensures ret == self@.transition_validation(old_obj@)
    { true }
}

impl ServiceAccount {
    pub fn state_validation(&self) -> (ret: bool)
        ensures ret == self@.state_validation()
    { true }

    pub fn transition_validation(&self, old_obj: &ServiceAccount) -> (ret: bool)
        ensures ret == self@.transition_validation(old_obj@)
    { true }
}

impl StatefulSet {
    pub fn state_validation(&self) -> (ret: bool)
        ensures ret == self@.state_validation()
    {
        self.spec().is_some() && if self.spec().unwrap().replicas().is_some() {
            self.spec().unwrap().replicas().unwrap() >= 0
        } else {
            true
        }
    }

    pub fn transition_validation(&self, old_obj: &StatefulSet) -> (ret: bool)
        requires
            self@.state_validation(),
            old_obj@.state_validation(),
        ensures ret == self@.transition_validation(old_obj@)
    {
        self.spec().unwrap().selector().eq(&old_obj.spec().unwrap().selector())
        && self.spec().unwrap().service_name().eq(&old_obj.spec().unwrap().service_name())
        && (self.spec().unwrap().pod_management_policy().is_none() == old_obj.spec().unwrap().pod_management_policy().is_none()
            && if self.spec().unwrap().pod_management_policy().is_some() {
                self.spec().unwrap().pod_management_policy().unwrap().eq(&old_obj.spec().unwrap().pod_management_policy().unwrap())
            } else {
                true
            }
        )
        && (self.spec().unwrap().volume_claim_templates().is_none() == old_obj.spec().unwrap().volume_claim_templates().is_none()
            && if self.spec().unwrap().volume_claim_templates().is_some() {
                let new_volume_claim_templates = self.spec().unwrap().volume_claim_templates().unwrap();
                let old_volume_claim_templates = old_obj.spec().unwrap().volume_claim_templates().unwrap();
                let mut all_equal = true;
                let mut i = 0;
                if new_volume_claim_templates.len() != old_volume_claim_templates.len() {
//                    proof { assert(self@.spec.get_Some_0().volume_claim_templates.get_Some_0().len() != old_obj@.spec.get_Some_0().volume_claim_templates.get_Some_0().len()) }
//                    proof { assert(!(self@.spec.get_Some_0().volume_claim_templates.get_Some_0() =~= old_obj@.spec.get_Some_0().volume_claim_templates.get_Some_0())) }
                    false
                } else {
                    while i < new_volume_claim_templates.len()
                        invariant
                            all_equal == (forall |j| #![trigger new_volume_claim_templates[j]]
                                0 <= j < i
                                    ==> new_volume_claim_templates@.map_values(|p: PersistentVolumeClaim| p@)[j] == old_volume_claim_templates@.map_values(|p: PersistentVolumeClaim| p@)[j]
                            ),
                            i <= new_volume_claim_templates.len(),
                            new_volume_claim_templates.len() == old_volume_claim_templates.len(),
                    {
                        all_equal = all_equal && new_volume_claim_templates[i].eq(&old_volume_claim_templates[i]);
                        i += 1;
                    }
                    proof { assert(all_equal == (self@.spec.get_Some_0().volume_claim_templates =~= old_obj@.spec.get_Some_0().volume_claim_templates)) }
                    all_equal
                }
            } else {
                true
            }
        )
    }
}

// CustomResource is the trait that associates the exec methods (e.g., unmarshal)
// with their spec correspondences, and is only used for proving the executable API server model
// conforms to the spec model.
pub trait CustomResource: View
where Self::V: CustomResourceView, Self: std::marker::Sized
{
    fn unmarshal(obj: DynamicObject) -> (res: Result<Self, UnmarshalError>)
        ensures
            res.is_Ok() == Self::V::unmarshal(obj@).is_Ok(),
            res.is_Ok() ==> res.get_Ok_0()@ == Self::V::unmarshal(obj@).get_Ok_0();

    fn state_validation(&self) -> (ret: bool)
        ensures ret == self@.state_validation();

    fn transition_validation(&self, old_obj: &Self) -> (ret: bool)
        ensures ret == self@.transition_validation(old_obj@);
}

// SimpleCRView and SimpleCR are types only used for instantiating the executable API server model,
// which is only used for conformance tests, so we keep the two types minimal.

pub struct SimpleCRView {
    pub metadata: ObjectMetaView,
    pub spec: SimpleCRSpecView,
    pub status: Option<SimpleCRStatusView>,
}

pub struct SimpleCRSpecView {}

pub struct SimpleCRStatusView {}

impl ResourceView for SimpleCRView {
    type Spec = SimpleCRSpecView;
    type Status = Option<SimpleCRStatusView>;

    open spec fn default() -> SimpleCRView {
        SimpleCRView {
            metadata: ObjectMetaView::default(),
            spec: arbitrary(),
            status: None,
        }
    }

    open spec fn metadata(self) -> ObjectMetaView { self.metadata }

    open spec fn kind() -> Kind { Kind::CustomResourceKind("simple"@) }

    open spec fn object_ref(self) -> ObjectRef {
        ObjectRef {
            kind: Self::kind(),
            name: self.metadata.name.get_Some_0(),
            namespace: self.metadata.namespace.get_Some_0(),
        }
    }

    proof fn object_ref_is_well_formed() {}

    open spec fn spec(self) -> SimpleCRSpecView { self.spec }

    open spec fn status(self) -> Option<SimpleCRStatusView> { self.status }

    open spec fn marshal(self) -> DynamicObjectView {
        DynamicObjectView {
            kind: Self::kind(),
            metadata: self.metadata,
            spec: SimpleCRView::marshal_spec(self.spec),
            status: SimpleCRView::marshal_status(self.status),
        }
    }

    open spec fn unmarshal(obj: DynamicObjectView) -> Result<SimpleCRView, UnmarshalError> {
        if obj.kind != Self::kind() {
            Err(())
        } else if !SimpleCRView::unmarshal_spec(obj.spec).is_Ok() {
            Err(())
        } else if !SimpleCRView::unmarshal_status(obj.status).is_Ok() {
            Err(())
        } else {
            Ok(SimpleCRView {
                metadata: obj.metadata,
                spec: SimpleCRView::unmarshal_spec(obj.spec).get_Ok_0(),
                status: SimpleCRView::unmarshal_status(obj.status).get_Ok_0(),
            })
        }
    }

    proof fn marshal_preserves_integrity() {
        SimpleCRView::marshal_spec_preserves_integrity();
        SimpleCRView::marshal_status_preserves_integrity();
    }

    proof fn marshal_preserves_metadata() {}

    proof fn marshal_preserves_kind() {}

    closed spec fn marshal_spec(s: SimpleCRSpecView) -> Value;

    closed spec fn unmarshal_spec(v: Value) -> Result<SimpleCRSpecView, UnmarshalError>;

    closed spec fn marshal_status(s: Option<SimpleCRStatusView>) -> Value;

    closed spec fn unmarshal_status(v: Value) -> Result<Option<SimpleCRStatusView>, UnmarshalError>;

    #[verifier(external_body)]
    proof fn marshal_spec_preserves_integrity() {}

    #[verifier(external_body)]
    proof fn marshal_status_preserves_integrity() {}

    proof fn unmarshal_result_determined_by_unmarshal_spec_and_status() {}

    open spec fn state_validation(self) -> bool { true }

    open spec fn transition_validation(self, old_obj: SimpleCRView) -> bool { true }
}

impl CustomResourceView for SimpleCRView {
    proof fn kind_is_custom_resource() {}

    open spec fn spec_status_validation(obj_spec: Self::Spec, obj_status: Self::Status) -> bool { true }

    proof fn validation_result_determined_by_spec_and_status()
        ensures forall |obj: Self| #[trigger] obj.state_validation() == Self::spec_status_validation(obj.spec(), obj.status())
    {}
}

#[verifier(external_body)]
pub struct SimpleCR {}

impl View for SimpleCR {
    type V = SimpleCRView;

    spec fn view(&self) -> SimpleCRView;
}

impl CustomResource for SimpleCR {
    #[verifier(external_body)]
    fn unmarshal(obj: DynamicObject) -> (res: Result<SimpleCR, UnmarshalError>)
        ensures
            res.is_Ok() == SimpleCRView::unmarshal(obj@).is_Ok(),
            res.is_Ok() ==> res.get_Ok_0()@ == SimpleCRView::unmarshal(obj@).get_Ok_0(),
    {
        Ok(SimpleCR {})
    }

    fn state_validation(&self) -> (ret: bool)
        ensures ret == self@.state_validation()
    {
        true
    }

    fn transition_validation(&self, old_obj: &Self) -> (ret: bool)
        ensures ret == self@.transition_validation(old_obj@)
    {
        true
    }
}

#[verifier(external_body)]
pub fn filter_controller_references(owner_references: Vec<OwnerReference>) -> (ret: Vec<OwnerReference>)
    ensures ret@.map_values(|o: OwnerReference| o@) == owner_references@.map_values(|o: OwnerReference| o@).filter(|o: OwnerReferenceView| o.controller.is_Some() && o.controller.get_Some_0())
{
    // TODO: is there a way to prove postconditions involving filter?
    // TODO: clone the entire Vec instead of clone in map()
    owner_references.iter().map(|o: &OwnerReference| o.clone()).filter(|o: &OwnerReference| o.controller().is_some() && o.controller().unwrap()).collect()
}

#[verifier(external_body)]
pub fn string_vec_to_string_set(s: Vec<String>) -> (ret: StringSet)
    ensures ret@ == s@.map_values(|s: String| s@).to_set()
{
    StringSet::from_rust_set(s.into_iter().collect())
}

}
