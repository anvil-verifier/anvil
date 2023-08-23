// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::api_resource::*;
use crate::kubernetes_api_objects::common::*;
use crate::kubernetes_api_objects::dynamic::*;
use crate::kubernetes_api_objects::error::ParseDynamicObjectError;
use crate::kubernetes_api_objects::marshal::*;
use crate::kubernetes_api_objects::object_meta::*;
use crate::kubernetes_api_objects::resource::*;
use crate::pervasive_ext::string_map::StringMap;
use crate::pervasive_ext::string_view::StringView;
use vstd::prelude::*;
use vstd::seq_lib::*;

verus! {

/// Service is a type of API object used for exposing a network application
/// that is running as one or more Pods in your cluster.
/// A Service object can be used to assign stable IP addresses and DNS names to pods.
///
/// This definition is a wrapper of Service defined at
/// https://github.com/Arnavion/k8s-openapi/blob/v0.17.0/src/v1_26/api/core/v1/service.rs.
/// It is supposed to be used in exec controller code.
///
/// More detailed information: https://kubernetes.io/docs/concepts/services-networking/service/.

#[verifier(external_body)]
pub struct Service {
    inner: deps_hack::k8s_openapi::api::core::v1::Service,
}

impl Service {
    pub spec fn view(&self) -> ServiceView;

    #[verifier(external_body)]
    pub fn default() -> (service: Service)
        ensures
            service@ == ServiceView::default(),
    {
        Service {
            inner: deps_hack::k8s_openapi::api::core::v1::Service::default(),
        }
    }

    #[verifier(external_body)]
    pub fn metadata(&self) -> (metadata: ObjectMeta)
        ensures
            metadata@ == self@.metadata,
    {
        ObjectMeta::from_kube(self.inner.metadata.clone())
    }

    #[verifier(external_body)]
    pub fn spec(&self) -> (spec: Option<ServiceSpec>)
        ensures
            self@.spec.is_Some() == spec.is_Some(),
            spec.is_Some() ==> spec.get_Some_0()@ == self@.spec.get_Some_0(),
    {
        todo!()
    }

    #[verifier(external_body)]
    pub fn set_metadata(&mut self, metadata: ObjectMeta)
        ensures
            self@ == old(self)@.set_metadata(metadata@),
    {
        self.inner.metadata = metadata.into_kube();
    }

    #[verifier(external_body)]
    pub fn set_spec(&mut self, spec: ServiceSpec)
        ensures
            self@ == old(self)@.set_spec(spec@),
    {
        self.inner.spec = Some(spec.into_kube());
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::Service {
        self.inner
    }

    #[verifier(external_body)]
    pub fn api_resource() -> (res: ApiResource)
        ensures
            res@.kind == ServiceView::kind(),
    {
        ApiResource::from_kube(deps_hack::kube::api::ApiResource::erase::<deps_hack::k8s_openapi::api::core::v1::Service>(&()))
    }

    #[verifier(external_body)]
    pub fn to_dynamic_object(self) -> (obj: DynamicObject)
        ensures
            obj@ == self@.to_dynamic_object(),
    {
        DynamicObject::from_kube(
            deps_hack::k8s_openapi::serde_json::from_str(&deps_hack::k8s_openapi::serde_json::to_string(&self.inner).unwrap()).unwrap()
        )
    }

    #[verifier(external_body)]
    pub fn from_dynamic_object(obj: DynamicObject) -> (res: Result<Service, ParseDynamicObjectError>)
        ensures
            res.is_Ok() == ServiceView::from_dynamic_object(obj@).is_Ok(),
            res.is_Ok() ==> res.get_Ok_0()@ == ServiceView::from_dynamic_object(obj@).get_Ok_0(),
    {
        let parse_result = obj.into_kube().try_parse::<deps_hack::k8s_openapi::api::core::v1::Service>();
        if parse_result.is_ok() {
            let res = Service { inner: parse_result.unwrap() };
            Ok(res)
        } else {
            Err(ParseDynamicObjectError::ExecError)
        }
    }
}

#[verifier(external_body)]
pub struct ServiceSpec {
    inner: deps_hack::k8s_openapi::api::core::v1::ServiceSpec,
}

impl ServiceSpec {
    pub spec fn view(&self) -> ServiceSpecView;

    #[verifier(external_body)]
    pub fn default() -> (service_spec: ServiceSpec)
        ensures
            service_spec@ == ServiceSpecView::default(),
    {
        ServiceSpec {
            inner: deps_hack::k8s_openapi::api::core::v1::ServiceSpec::default(),
        }
    }

    #[verifier(external_body)]
    pub fn set_cluster_ip(&mut self, cluster_ip: String)
        ensures
            self@ == old(self)@.set_cluster_ip(cluster_ip@),
    {
        self.inner.cluster_ip = Some(cluster_ip.into_rust_string())
    }

    #[verifier(external_body)]
    pub fn set_ports(&mut self, ports: Vec<ServicePort>)
        ensures
            self@ == old(self)@.set_ports(ports@.map_values(|port: ServicePort| port@)),
    {
        self.inner.ports = Some(
            ports.into_iter().map(|port: ServicePort| port.into_kube()).collect()
        )
    }

    #[verifier(external_body)]
    pub fn set_selector(&mut self, selector: StringMap)
        ensures
            self@ == old(self)@.set_selector(selector@),
    {
        self.inner.selector = Some(selector.into_rust_map())
    }

    #[verifier(external_body)]
    pub fn set_publish_not_ready_addresses(&mut self, publish_not_ready_addresses: bool)
        ensures
            self@ == old(self)@.set_publish_not_ready_addresses(publish_not_ready_addresses),
    {
        self.inner.publish_not_ready_addresses = Some(publish_not_ready_addresses);
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::ServiceSpec {
        self.inner
    }
}

#[verifier(external_body)]
pub struct ServicePort {
    inner: deps_hack::k8s_openapi::api::core::v1::ServicePort,
}

impl ServicePort {
    pub spec fn view(&self) -> ServicePortView;

    #[verifier(external_body)]
    pub fn default() -> (service_port: ServicePort)
        ensures
            service_port@ == ServicePortView::default(),
    {
        ServicePort {
            inner: deps_hack::k8s_openapi::api::core::v1::ServicePort::default(),
        }
    }

    pub fn new_with(name: String, port: i32) -> (service_port: ServicePort)
        ensures
            service_port@ == ServicePortView::default().set_name(name@).set_port(port as nat),
    {
        let mut service_port = Self::default();
        service_port.set_name(name);
        service_port.set_port(port);

        service_port
    }

    #[verifier(external_body)]
    pub fn set_name(&mut self, name: String)
        ensures
            self@ == old(self)@.set_name(name@),
    {
        self.inner.name = Some(name.into_rust_string());
    }

    #[verifier(external_body)]
    pub fn set_port(&mut self, port: i32)
        ensures
            self@ == old(self)@.set_port(port as nat),
    {
        self.inner.port = port;
    }

    #[verifier(external_body)]
    pub fn set_app_protocol(&mut self, app_protocol: String)
        ensures
            self@ == old(self)@.set_app_protocol(app_protocol@),
    {
        self.inner.app_protocol = Some(app_protocol.into_rust_string());
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::ServicePort {
        self.inner
    }
}

/// ServiceView is the ghost type of Service.
/// It is supposed to be used in spec and proof code.

pub struct ServiceView {
    pub metadata: ObjectMetaView,
    pub spec: Option<ServiceSpecView>,
}

impl ServiceView {
    pub open spec fn default() -> ServiceView {
        ServiceView {
            metadata: ObjectMetaView::default(),
            spec: None,
        }
    }

    pub open spec fn set_metadata(self, metadata: ObjectMetaView) -> ServiceView {
        ServiceView {
            metadata: metadata,
            ..self
        }
    }

    pub open spec fn set_spec(self, spec: ServiceSpecView) -> ServiceView {
        ServiceView {
            spec: Some(spec),
            ..self
        }
    }
}

impl ResourceView for ServiceView {
    type Spec = Option<ServiceSpecView>;

    open spec fn metadata(self) -> ObjectMetaView {
        self.metadata
    }

    open spec fn kind() -> Kind {
        Kind::ServiceKind
    }

    open spec fn object_ref(self) -> ObjectRef {
        ObjectRef {
            kind: Self::kind(),
            name: self.metadata.name.get_Some_0(),
            namespace: self.metadata.namespace.get_Some_0(),
        }
    }

    proof fn object_ref_is_well_formed() {}

    open spec fn spec(self) -> Option<ServiceSpecView> {
        self.spec
    }

    open spec fn to_dynamic_object(self) -> DynamicObjectView {
        DynamicObjectView {
            kind: Self::kind(),
            metadata: self.metadata,
            spec: ServiceView::marshal_spec(self.spec),
        }
    }

    open spec fn from_dynamic_object(obj: DynamicObjectView) -> Result<ServiceView, ParseDynamicObjectError> {
        if obj.kind != Self::kind() {
            Err(ParseDynamicObjectError::UnmarshalError)
        } else if !ServiceView::unmarshal_spec(obj.spec).is_Ok() {
            Err(ParseDynamicObjectError::UnmarshalError)
        } else {
            Ok(ServiceView {
                metadata: obj.metadata,
                spec: ServiceView::unmarshal_spec(obj.spec).get_Ok_0(),
            })
        }
    }

    proof fn to_dynamic_preserves_integrity() {
        ServiceView::spec_integrity_is_preserved_by_marshal();
    }

    proof fn from_dynamic_preserves_metadata() {}

    proof fn from_dynamic_preserves_kind() {}

    closed spec fn marshal_spec(s: Option<ServiceSpecView>) -> Value;

    closed spec fn unmarshal_spec(v: Value) -> Result<Option<ServiceSpecView>, ParseDynamicObjectError>;

    #[verifier(external_body)]
    proof fn spec_integrity_is_preserved_by_marshal() {}

    proof fn from_dynamic_object_result_determined_by_unmarshal() {}

    open spec fn rule(obj: ServiceView) -> bool {
        true
    }

    open spec fn transition_rule(new_obj: ServiceView, old_obj: ServiceView) -> bool {
        true
    }
}

pub struct ServiceSpecView {
    pub cluster_ip: Option<StringView>,
    pub ports: Option<Seq<ServicePortView>>,
    pub selector: Option<Map<StringView, StringView>>,
    pub publish_not_ready_addresses: Option<bool>,
}

impl ServiceSpecView {
    pub open spec fn default() -> ServiceSpecView {
        ServiceSpecView {
            cluster_ip: None,
            ports: None,
            selector: None,
            publish_not_ready_addresses: None,
        }
    }

    pub open spec fn set_cluster_ip(self, cluster_ip: StringView) -> ServiceSpecView {
        ServiceSpecView {
            cluster_ip: Some(cluster_ip),
            ..self
        }
    }

    pub open spec fn set_ports(self, ports: Seq<ServicePortView>) -> ServiceSpecView {
        ServiceSpecView {
            ports: Some(ports),
            ..self
        }
    }

    pub open spec fn set_selector(self, selector: Map<StringView, StringView>) -> ServiceSpecView {
        ServiceSpecView {
            selector: Some(selector),
            ..self
        }
    }

    pub open spec fn set_publish_not_ready_addresses(self, publish_not_ready_addresses: bool) -> ServiceSpecView {
        ServiceSpecView {
            publish_not_ready_addresses: Some(publish_not_ready_addresses),
            ..self
        }
    }
}

impl Marshalable for ServiceSpecView {
    spec fn marshal(self) -> Value;

    spec fn unmarshal(value: Value) -> Result<Self, ParseDynamicObjectError>;

    #[verifier(external_body)]
    proof fn marshal_returns_non_null() {}

    #[verifier(external_body)]
    proof fn marshal_preserves_integrity() {}
}

pub struct ServicePortView {
    pub name: Option<StringView>,
    pub port: nat,
    pub app_protocol: Option<StringView>,
}

impl ServicePortView {
    pub open spec fn default() -> ServicePortView {
        ServicePortView {
            name: None,
            port: 0, // TODO: is this the correct default value?
            app_protocol: None,
        }
    }

    pub open spec fn set_name(self, name: StringView) -> ServicePortView {
        ServicePortView {
            name: Some(name),
            ..self
        }
    }

    pub open spec fn set_port(self, port: nat) -> ServicePortView {
        ServicePortView {
            port: port,
            ..self
        }
    }

    pub open spec fn set_app_protocol(self, app_protocol: StringView) -> ServicePortView {
        ServicePortView {
            app_protocol: Some(app_protocol),
            ..self
        }
    }
}

impl Marshalable for ServicePortView {
    spec fn marshal(self) -> Value;

    spec fn unmarshal(value: Value) -> Result<Self, ParseDynamicObjectError>;

    #[verifier(external_body)]
    proof fn marshal_returns_non_null() {}

    #[verifier(external_body)]
    proof fn marshal_preserves_integrity() {}
}

}
