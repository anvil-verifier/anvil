// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::common::*;
use crate::kubernetes_api_objects::dynamic::*;
use crate::kubernetes_api_objects::object_meta::*;
use crate::kubernetes_api_objects::resource::*;
use crate::pervasive_ext::string_map::StringMap;
use crate::pervasive_ext::string_view::StringView;
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::vec::*;

verus! {

#[verifier(external_body)]
pub struct Service {
    inner: k8s_openapi::api::core::v1::Service,
}

#[verifier(external_body)]
pub struct ServiceSpec {
    inner: k8s_openapi::api::core::v1::ServiceSpec,
}

#[verifier(external_body)]
pub struct ServicePort {
    inner: k8s_openapi::api::core::v1::ServicePort,
}

pub struct ServiceView {
    pub metadata: ObjectMetaView,
    pub spec: Option<ServiceSpecView>,
}

pub struct ServiceSpecView {
    pub cluster_ip: Option<StringView>,
    pub ports: Option<Seq<ServicePortView>>,
    pub selector: Option<Map<StringView, StringView>>,
}

pub struct ServicePortView {
    pub name: Option<StringView>,
    pub port: nat,
}

impl Service {
    pub spec fn view(&self) -> ServiceView;

    #[verifier(external_body)]
    pub fn default() -> (service: Service)
        ensures
            service@ == ServiceView::default(),
    {
        Service {
            inner: k8s_openapi::api::core::v1::Service::default(),
        }
    }

    #[verifier(external_body)]
    pub fn metadata(&self) -> (metadata: ObjectMeta)
        ensures
            metadata@ == self@.metadata,
    {
        todo!()
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
    pub fn set_name(&mut self, name: String)
        ensures
            self@ == old(self)@.set_name(name@),
    {
        self.inner.metadata.name = std::option::Option::Some(name.into_rust_string());
    }

    #[verifier(external_body)]
    pub fn set_namespace(&mut self, namespace: String)
        ensures
            self@ == old(self)@.set_namespace(namespace@),
    {
        self.inner.metadata.namespace = std::option::Option::Some(namespace.into_rust_string());
    }

    #[verifier(external_body)]
    pub fn set_spec(&mut self, spec: ServiceSpec)
        ensures
            self@ == old(self)@.set_spec(spec@),
    {
        self.inner.spec = std::option::Option::Some(spec.into_kube_service_spec());
    }
}

impl ServiceView {
    pub open spec fn default() -> ServiceView {
        ServiceView {
            metadata: ObjectMetaView::default(),
            spec: Option::None,
        }
    }

    pub open spec fn set_name(self, name: StringView) -> ServiceView {
        ServiceView {
            metadata: self.metadata.set_name(name),
            ..self
        }
    }

    pub open spec fn set_namespace(self, namespace: StringView) -> ServiceView {
        ServiceView {
            metadata: self.metadata.set_namespace(namespace),
            ..self
        }
    }

    pub open spec fn set_spec(self, spec: ServiceSpecView) -> ServiceView {
        ServiceView {
            spec: Option::Some(spec),
            ..self
        }
    }

    pub open spec fn spec_field() -> nat {0}
}

impl ResourceView for ServiceView {
    open spec fn metadata(self) -> ObjectMetaView {
        self.metadata
    }

    open spec fn kind(self) -> Kind {
        Kind::ServiceKind
    }

    open spec fn object_ref(self) -> ObjectRef {
        ObjectRef {
            kind: self.kind(),
            name: self.metadata.name.get_Some_0(),
            namespace: self.metadata.namespace.get_Some_0(),
        }
    }

    open spec fn to_dynamic_object(self) -> DynamicObjectView {
        DynamicObjectView {
            kind: self.kind(),
            metadata: self.metadata,
            data: Value::Object(Map::empty()
                                    .insert(Self::spec_field(), if self.spec.is_None() {Value::Null} else {
                                        self.spec.get_Some_0().marshal()
                                    })),
        }
    }

    open spec fn from_dynamic_object(obj: DynamicObjectView) -> ServiceView {
        ServiceView {
            metadata: obj.metadata,
            spec: if obj.data.get_Object_0()[Self::spec_field()].is_Null() {Option::None} else {
                Option::Some(ServiceSpecView::unmarshal(obj.data.get_Object_0()[Self::spec_field()]))
            },
        }
    }

    proof fn integrity_check() {
        assert forall |o: Self| o == Self::from_dynamic_object(#[trigger] o.to_dynamic_object()) by {
            if o.spec.is_Some() && o.spec.get_Some_0().ports.is_Some() {
                assert_seqs_equal!(
                    o.spec.get_Some_0().ports.get_Some_0(),
                    Self::from_dynamic_object(o.to_dynamic_object()).spec.get_Some_0().ports.get_Some_0()
                );
            }
        }
    }
}

impl ServiceSpec {
    pub spec fn view(&self) -> ServiceSpecView;

    #[verifier(external_body)]
    pub fn default() -> (service_spec: ServiceSpec)
        ensures
            service_spec@ == ServiceSpecView::default(),
    {
        ServiceSpec {
            inner: k8s_openapi::api::core::v1::ServiceSpec::default(),
        }
    }

    #[verifier(external_body)]
    pub fn set_cluster_ip(&mut self, cluster_ip: String)
        ensures
            self@ == old(self)@.set_cluster_ip(cluster_ip@),
    {
        self.inner.cluster_ip = std::option::Option::Some(cluster_ip.into_rust_string())
    }

    #[verifier(external_body)]
    pub fn set_ports(&mut self, ports: Vec<ServicePort>)
        ensures
            self@ == old(self)@.set_ports(ports@.map_values(|port: ServicePort| port@)),
    {
        self.inner.ports = std::option::Option::Some(
            ports.vec.into_iter().map(|port: ServicePort| port.into_kube_service_port()).collect()
        )
    }

    #[verifier(external_body)]
    pub fn set_selector(&mut self, selector: StringMap)
        ensures
            self@ == old(self)@.set_selector(selector@),
    {
        self.inner.selector = std::option::Option::Some(selector.into_rust_map())
    }

    #[verifier(external)]
    pub fn into_kube_service_spec(self) -> k8s_openapi::api::core::v1::ServiceSpec {
        self.inner
    }
}

impl ServiceSpecView {
    pub open spec fn default() -> ServiceSpecView {
        ServiceSpecView {
            cluster_ip: Option::None,
            ports: Option::None,
            selector: Option::None,
        }
    }


    pub open spec fn set_cluster_ip(self, cluster_ip: StringView) -> ServiceSpecView {
        ServiceSpecView {
            cluster_ip: Option::Some(cluster_ip),
            ..self
        }
    }

    pub open spec fn set_ports(self, ports: Seq<ServicePortView>) -> ServiceSpecView {
        ServiceSpecView {
            ports: Option::Some(ports),
            ..self
        }
    }

    pub open spec fn set_selector(self, selector: Map<StringView, StringView>) -> ServiceSpecView {
        ServiceSpecView {
            selector: Option::Some(selector),
            ..self
        }
    }

    pub open spec fn marshal(self) -> Value {
        Value::Object(
            Map::empty()
                .insert(Self::cluster_ip_field(), if self.cluster_ip.is_None() {Value::Null} else {
                    Value::String(self.cluster_ip.get_Some_0())
                })
                .insert(Self::ports_field(), if self.ports.is_None() {Value::Null} else {
                    Value::Array(self.ports.get_Some_0().map_values(|port: ServicePortView| port.marshal()))
                })
                .insert(Self::selector_field(), if self.selector.is_None() {Value::Null} else {
                    Value::StringStringMap(self.selector.get_Some_0())
                })
        )
    }

    pub open spec fn unmarshal(value: Value) -> Self {
        ServiceSpecView {
            cluster_ip: if value.get_Object_0()[Self::cluster_ip_field()].is_Null() {Option::None} else {
                Option::Some(value.get_Object_0()[Self::cluster_ip_field()].get_String_0())
            },
            ports: if value.get_Object_0()[Self::ports_field()].is_Null() {Option::None} else {
                Option::Some(value.get_Object_0()[Self::ports_field()].get_Array_0().map_values(|v| ServicePortView::unmarshal(v)))
            },
            selector: if value.get_Object_0()[Self::selector_field()].is_Null() {Option::None} else {
                Option::Some(value.get_Object_0()[Self::selector_field()].get_StringStringMap_0())
            },
        }
    }

    proof fn integrity_check()
        ensures forall |o: Self| o == Self::unmarshal(#[trigger] o.marshal())
    {
        assert forall |o: Self| o == Self::unmarshal(#[trigger] o.marshal()) by {
            if o.ports.is_Some() {
                assert_seqs_equal!(o.ports.get_Some_0(), Self::unmarshal(o.marshal()).ports.get_Some_0());
            }
        }
    }

    pub open spec fn cluster_ip_field() -> nat {0}

    pub open spec fn ports_field() -> nat {1}

    pub open spec fn selector_field() -> nat {2}
}

impl ServicePort {
    pub spec fn view(&self) -> ServicePortView;

    #[verifier(external_body)]
    pub fn default() -> (service_port: ServicePort)
        ensures
            service_port@ == ServicePortView::default(),
    {
        ServicePort {
            inner: k8s_openapi::api::core::v1::ServicePort::default(),
        }
    }

    #[verifier(external_body)]
    pub fn set_name(&mut self, name: String)
        ensures
            self@ == old(self)@.set_name(name@),
    {
        self.inner.name = std::option::Option::Some(name.into_rust_string());
    }

    #[verifier(external_body)]
    pub fn set_port(&mut self, port: i32)
        ensures
            self@ == old(self)@.set_port(port as nat),
    {
        self.inner.port = port;
    }

    #[verifier(external)]
    pub fn into_kube_service_port(self) -> k8s_openapi::api::core::v1::ServicePort {
        self.inner
    }
}

impl ServicePortView {
    pub open spec fn default() -> ServicePortView {
        ServicePortView {
            name: Option::None,
            port: 0, // TODO: is this the correct default value?
        }
    }

    pub open spec fn set_name(self, name: StringView) -> ServicePortView {
        ServicePortView {
            name: Option::Some(name),
            ..self
        }
    }

    pub open spec fn set_port(self, port: nat) -> ServicePortView {
        ServicePortView {
            port: port,
            ..self
        }
    }

    pub open spec fn marshal(self) -> Value {
        Value::Object(
            Map::empty()
                .insert(Self::name_field(), if self.name.is_None() {Value::Null} else {
                    Value::String(self.name.get_Some_0())
                })
                .insert(Self::port_field(), Value::Nat(self.port))
        )
    }

    pub open spec fn unmarshal(value: Value) -> Self {
        ServicePortView {
            name: if value.get_Object_0()[Self::name_field()].is_Null() {Option::None} else {
                Option::Some(value.get_Object_0()[Self::name_field()].get_String_0())
            },
            port: value.get_Object_0()[Self::port_field()].get_Nat_0(),
        }
    }

    proof fn integrity_check()
        ensures forall |o: Self| o == Self::unmarshal(#[trigger] o.marshal())
    {}

    pub open spec fn name_field() -> nat {0}

    pub open spec fn port_field() -> nat {1}
}

}
