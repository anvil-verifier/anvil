use crate::kubernetes_api_objects::error::ParseDynamicObjectError;
use crate::kubernetes_api_objects::exec::{api_resource::ApiResource, prelude::*};
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    api_server::state_machine as model, api_server::types as model_types,
};
use vstd::prelude::*;
use vstd::string::*;

#[derive(Clone, Ord, PartialOrd, Eq, PartialEq)]
pub struct ExternalObjectRef {
    pub kind: Kind,
    pub name: std::string::String,
    pub namespace: std::string::String,
}

impl KubeObjectRef {
    pub fn into_external_object_ref(self) -> ExternalObjectRef {
        ExternalObjectRef {
            kind: self.kind.clone(),
            name: self.name.into_rust_string(),
            namespace: self.namespace.into_rust_string(),
        }
    }

    pub fn from_external_object_ref(key: ExternalObjectRef) -> KubeObjectRef {
        KubeObjectRef {
            kind: key.kind.clone(),
            name: String::from_rust_string(key.name),
            namespace: String::from_rust_string(key.namespace),
        }
    }
}

verus! {

pub struct KubeObjectRef {
    pub kind: Kind,
    pub name: String,
    pub namespace: String,
}

impl View for KubeObjectRef {
    type V = ObjectRef;
    open spec fn view(&self) -> ObjectRef {
        ObjectRef {
            kind: self.kind,
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
    #[verifier(external_body)]
    pub fn kind(&self) -> (kind: Kind)
        ensures kind == self@.kind,
    {
        match self.as_kube_ref().kind.as_str() {
            "ConfigMap" => Kind::ConfigMapKind,
            "DaemonSet" => Kind::DaemonSetKind,
            "PersistentVolumeClaim" => Kind::PersistentVolumeClaimKind,
            "Pod" => Kind::PodKind,
            "Role" => Kind::RoleKind,
            "RoleBinding" => Kind::RoleBindingKind,
            "StatefulSet" => Kind::StatefulSetKind,
            "Service" => Kind::ServiceKind,
            "ServiceAccount" => Kind::ServiceAccountKind,
            "Secret" => Kind::SecretKind,
            _ => panic!(), // We assume the DynamicObject won't be a custom object
        }
    }
}

impl DynamicObject {
    #[verifier(external_body)]
    pub fn kind(&self) -> (kind: Kind)
        ensures kind == self@.kind,
    {
        if self.as_kube_ref().types.is_none() {
            panic!();
        }
        match self.as_kube_ref().types.as_ref().unwrap().kind.as_str() {
            "ConfigMap" => Kind::ConfigMapKind,
            "DaemonSet" => Kind::DaemonSetKind,
            "PersistentVolumeClaim" => Kind::PersistentVolumeClaimKind,
            "Pod" => Kind::PodKind,
            "Role" => Kind::RoleKind,
            "RoleBinding" => Kind::RoleBindingKind,
            "StatefulSet" => Kind::StatefulSetKind,
            "Service" => Kind::ServiceKind,
            "ServiceAccount" => Kind::ServiceAccountKind,
            "Secret" => Kind::SecretKind,
            _ => panic!(), // We assume the DynamicObject won't be a custom object
        }
    }

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
        self.as_kube_mut_ref().metadata.name = Some(name.into_rust_string());
    }

    #[verifier(external_body)]
    pub fn set_namespace(&mut self, namespace: String)
        ensures self@ == old(self)@.set_namespace(namespace@),
    {
        self.as_kube_mut_ref().metadata.namespace = Some(namespace.into_rust_string());
    }

    #[verifier(external_body)]
    pub fn set_resource_version(&mut self, resource_version: i64)
        ensures self@ == old(self)@.set_resource_version(resource_version as int),
    {
        self.as_kube_mut_ref().metadata.resource_version = Some(resource_version.to_string());
    }

    #[verifier(external_body)]
    pub fn set_uid(&mut self, uid: i64)
        ensures self@ == old(self)@.set_uid(uid as int),
    {
        self.as_kube_mut_ref().metadata.uid = Some(uid.to_string());
    }

    #[verifier(external_body)]
    pub fn unset_deletion_timestamp(&mut self)
        ensures self@ == old(self)@.unset_deletion_timestamp(),
    {
        self.as_kube_mut_ref().metadata.deletion_timestamp = None;
    }

    #[verifier(external_body)]
    pub fn set_spec(&mut self, other: &DynamicObject)
        ensures self@ == old(self)@.set_spec(other@.spec)
    {
        self.as_kube_mut_ref().data = other.as_kube_ref().data.clone()
    }

    #[verifier(external_body)]
    pub fn set_status(&mut self, other: &DynamicObject)
        ensures self@ == old(self)@.set_status(other@.status)
    {}

    #[verifier(external_body)]
    pub fn set_default_status<K: CustomResourceView>(&mut self)
        ensures
            self@ == old(self)@.set_status(model::marshalled_default_status::<K>(self@.kind)),
            model::unmarshallable_status::<K>(self@),
    {}
}

impl ConfigMap {
    pub fn state_validation(&self) -> (ret: bool)
        ensures ret == self@.state_validation()
    { true }
}

impl DaemonSet {
    pub fn state_validation(&self) -> (ret: bool)
        ensures ret == self@.state_validation()
    { self.spec().is_some() }
}

impl Pod {
    pub fn state_validation(&self) -> (ret: bool)
        ensures ret == self@.state_validation()
    { self.spec().is_some() }
}

impl PersistentVolumeClaim {
    pub fn state_validation(&self) -> (ret: bool)
        ensures ret == self@.state_validation()
    { self.spec().is_some() }
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
}

impl RoleBinding {
    pub fn state_validation(&self) -> (ret: bool)
        ensures ret == self@.state_validation()
    {
        self.role_ref().api_group().eq(&new_strlit("rbac.authorization.k8s.io").to_string())
        && (self.role_ref().kind().eq(&new_strlit("Role").to_string())
            || self.role_ref().kind().eq(&new_strlit("ClusterRole").to_string()))
    }
}

impl Secret {
    pub fn state_validation(&self) -> (ret: bool)
        ensures ret == self@.state_validation()
    { true }
}

impl Service {
    pub fn state_validation(&self) -> (ret: bool)
        ensures ret == self@.state_validation()
    { self.spec().is_some() }
}

impl ServiceAccount {
    pub fn state_validation(&self) -> (ret: bool)
        ensures ret == self@.state_validation()
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
}

pub trait CustomResource: View
where Self::V: CustomResourceView, Self: std::marker::Sized
{
    fn unmarshal(obj: DynamicObject) -> (res: Result<Self, ParseDynamicObjectError>)
        ensures
            res.is_Ok() == Self::V::unmarshal(obj@).is_Ok(),
            res.is_Ok() ==> res.get_Ok_0()@ == Self::V::unmarshal(obj@).get_Ok_0();

    fn state_validation(&self) -> (ret: bool)
        ensures ret == self@.state_validation();
}

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

    open spec fn kind() -> Kind { Kind::CustomResourceKind }

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

    open spec fn unmarshal(obj: DynamicObjectView) -> Result<SimpleCRView, ParseDynamicObjectError> {
        if obj.kind != Self::kind() {
            Err(ParseDynamicObjectError::UnmarshalError)
        } else if !SimpleCRView::unmarshal_spec(obj.spec).is_Ok() {
            Err(ParseDynamicObjectError::UnmarshalError)
        } else if !SimpleCRView::unmarshal_status(obj.status).is_Ok() {
            Err(ParseDynamicObjectError::UnmarshalError)
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

    closed spec fn unmarshal_spec(v: Value) -> Result<SimpleCRSpecView, ParseDynamicObjectError>;

    closed spec fn marshal_status(s: Option<SimpleCRStatusView>) -> Value;

    closed spec fn unmarshal_status(v: Value) -> Result<Option<SimpleCRStatusView>, ParseDynamicObjectError>;

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
}

#[verifier(external_body)]
pub struct SimpleCR {}

impl View for SimpleCR {
    type V = SimpleCRView;

    spec fn view(&self) -> SimpleCRView;
}

impl CustomResource for SimpleCR {
    #[verifier(external_body)]
    fn unmarshal(obj: DynamicObject) -> (res: Result<SimpleCR, ParseDynamicObjectError>)
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
}


}
