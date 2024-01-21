// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::ParseDynamicObjectError;
use crate::kubernetes_api_objects::exec::{
    api_resource::*, dynamic::*, object_meta::*, resource::*,
};
use crate::kubernetes_api_objects::spec::{resource::*, service::*};
use crate::vstd_ext::string_map::StringMap;
use crate::vstd_ext::string_view::StringView;
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

impl View for Service {
    type V = ServiceView;

    spec fn view(&self) -> ServiceView;
}

impl Service {
    #[verifier(external_body)]
    pub fn default() -> (service: Service)
        ensures service@ == ServiceView::default(),
    {
        Service {
            inner: deps_hack::k8s_openapi::api::core::v1::Service::default(),
        }
    }

    #[verifier(external_body)]
    pub fn clone(&self) -> (s: Self)
        ensures s@ == self@,
    {
        Service { inner: self.inner.clone() }
    }

    #[verifier(external_body)]
    pub fn metadata(&self) -> (metadata: ObjectMeta)
        ensures metadata@ == self@.metadata,
    {
        ObjectMeta::from_kube(self.inner.metadata.clone())
    }

    #[verifier(external_body)]
    pub fn spec(&self) -> (spec: Option<ServiceSpec>)
        ensures
            self@.spec.is_Some() == spec.is_Some(),
            spec.is_Some() ==> spec.get_Some_0()@ == self@.spec.get_Some_0(),
    {
        match &self.inner.spec {
            Some(s) => Some(ServiceSpec::from_kube(s.clone())),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn set_metadata(&mut self, metadata: ObjectMeta)
        ensures self@ == old(self)@.set_metadata(metadata@),
    {
        self.inner.metadata = metadata.into_kube();
    }

    #[verifier(external_body)]
    pub fn set_spec(&mut self, spec: ServiceSpec)
        ensures self@ == old(self)@.set_spec(spec@),
    {
        self.inner.spec = Some(spec.into_kube());
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::Service { self.inner }

    #[verifier(external)]
    pub fn from_kube(inner: deps_hack::k8s_openapi::api::core::v1::Service) -> Service { Service { inner: inner } }

    #[verifier(external_body)]
    pub fn api_resource() -> (res: ApiResource)
        ensures res@.kind == ServiceView::kind(),
    {
        ApiResource::from_kube(deps_hack::kube::api::ApiResource::erase::<deps_hack::k8s_openapi::api::core::v1::Service>(&()))
    }

    #[verifier(external_body)]
    pub fn marshal(self) -> (obj: DynamicObject)
        ensures obj@ == self@.marshal(),
    {
        DynamicObject::from_kube(deps_hack::k8s_openapi::serde_json::from_str(&deps_hack::k8s_openapi::serde_json::to_string(&self.inner).unwrap()).unwrap())
    }

    #[verifier(external_body)]
    pub fn unmarshal(obj: DynamicObject) -> (res: Result<Service, ParseDynamicObjectError>)
        ensures
            res.is_Ok() == ServiceView::unmarshal(obj@).is_Ok(),
            res.is_Ok() ==> res.get_Ok_0()@ == ServiceView::unmarshal(obj@).get_Ok_0(),
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
        ensures service_spec@ == ServiceSpecView::default(),
    {
        ServiceSpec {
            inner: deps_hack::k8s_openapi::api::core::v1::ServiceSpec::default(),
        }
    }

    #[verifier(external_body)]
    pub fn clone(&self) -> (s: Self)
        ensures s@ == self@,
    {
        ServiceSpec { inner: self.inner.clone() }
    }

    #[verifier(external_body)]
    pub fn set_cluster_ip(&mut self, cluster_ip: String)
        ensures self@ == old(self)@.set_cluster_ip(cluster_ip@),
    {
        self.inner.cluster_ip = Some(cluster_ip.into_rust_string())
    }

    #[verifier(external_body)]
    pub fn ports(&self) -> (ports: Option<Vec<ServicePort>>)
        ensures
            self@.ports.is_Some() == ports.is_Some(),
            ports.is_Some() ==> ports.get_Some_0()@.map_values(|port: ServicePort| port@) == self@.ports.get_Some_0(),
    {
        match &self.inner.ports {
            Some(p) => Some(p.into_iter().map(|port: &deps_hack::k8s_openapi::api::core::v1::ServicePort| ServicePort::from_kube(port.clone())).collect()),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn set_ports(&mut self, ports: Vec<ServicePort>)
        ensures self@ == old(self)@.set_ports(ports@.map_values(|port: ServicePort| port@)),
    {
        self.inner.ports = Some(ports.into_iter().map(|port: ServicePort| port.into_kube()).collect())
    }

    #[verifier(external_body)]
    pub fn selector(&self) -> (selector: Option<StringMap>)
        ensures
            self@.selector.is_Some() == selector.is_Some(),
            selector.is_Some() ==> selector.get_Some_0()@ == self@.selector.get_Some_0(),
    {
        match &self.inner.selector {
            Some(s) => Some(StringMap::from_rust_map(s.clone())),
            None => None,
        }
    }

    #[verifier(external_body)]
    pub fn set_selector(&mut self, selector: StringMap)
        ensures self@ == old(self)@.set_selector(selector@),
    {
        self.inner.selector = Some(selector.into_rust_map())
    }

    #[verifier(external_body)]
    pub fn publish_not_ready_addresses(&self) -> (publish_not_ready_addresses: Option<bool>)
        ensures
            self@.publish_not_ready_addresses.is_Some() == publish_not_ready_addresses.is_Some(),
            publish_not_ready_addresses.is_Some() ==> publish_not_ready_addresses.get_Some_0() == self@.publish_not_ready_addresses.get_Some_0(),
    {
        self.inner.publish_not_ready_addresses.clone()
    }

    #[verifier(external_body)]
    pub fn set_publish_not_ready_addresses(&mut self, publish_not_ready_addresses: bool)
        ensures self@ == old(self)@.set_publish_not_ready_addresses(publish_not_ready_addresses),
    {
        self.inner.publish_not_ready_addresses = Some(publish_not_ready_addresses);
    }

    #[verifier(external_body)]
    pub fn unset_publish_not_ready_addresses(&mut self)
        ensures self@ == old(self)@.unset_publish_not_ready_addresses(),
    {
        self.inner.publish_not_ready_addresses = None;
    }

    #[verifier(external)]
    pub fn from_kube(inner: deps_hack::k8s_openapi::api::core::v1::ServiceSpec) -> ServiceSpec { ServiceSpec { inner: inner } }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::ServiceSpec { self.inner }
}

#[verifier(external_body)]
pub struct ServicePort {
    inner: deps_hack::k8s_openapi::api::core::v1::ServicePort,
}

impl ServicePort {
    pub spec fn view(&self) -> ServicePortView;

    #[verifier(external_body)]
    pub fn default() -> (service_port: ServicePort)
        ensures service_port@ == ServicePortView::default(),
    {
        ServicePort {
            inner: deps_hack::k8s_openapi::api::core::v1::ServicePort::default(),
        }
    }

    pub fn new_with(name: String, port: i32) -> (service_port: ServicePort)
        ensures service_port@ == ServicePortView::default().set_name(name@).set_port(port as int),
    {
        let mut service_port = Self::default();
        service_port.set_name(name);
        service_port.set_port(port);

        service_port
    }

    #[verifier(external_body)]
    pub fn set_name(&mut self, name: String)
        ensures self@ == old(self)@.set_name(name@),
    {
        self.inner.name = Some(name.into_rust_string());
    }

    #[verifier(external_body)]
    pub fn set_port(&mut self, port: i32)
        ensures self@ == old(self)@.set_port(port as int),
    {
        self.inner.port = port;
    }

    #[verifier(external_body)]
    pub fn set_app_protocol(&mut self, app_protocol: String)
        ensures self@ == old(self)@.set_app_protocol(app_protocol@),
    {
        self.inner.app_protocol = Some(app_protocol.into_rust_string());
    }

    #[verifier(external_body)]
    pub fn set_protocol(&mut self, protocol: String)
        ensures self@ == old(self)@.set_protocol(protocol@),
    {
        self.inner.protocol = Some(protocol.into_rust_string());
    }

    #[verifier(external)]
    pub fn from_kube(inner: deps_hack::k8s_openapi::api::core::v1::ServicePort) -> ServicePort { ServicePort { inner: inner } }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::ServicePort { self.inner }
}

}
