// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::api_resource::*;
use crate::kubernetes_api_objects::common::*;
use crate::kubernetes_api_objects::dynamic::*;
use crate::kubernetes_api_objects::label_selector::*;
use crate::kubernetes_api_objects::object_meta::*;
use crate::kubernetes_api_objects::resource::*;
use crate::pervasive_ext::string_map::*;
use crate::pervasive_ext::string_view::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {

#[verifier(external_body)]
pub struct StatefulSet {
    inner: k8s_openapi::api::apps::v1::StatefulSet,
}

#[verifier(external_body)]
pub struct StatefulSetSpec {
    inner: k8s_openapi::api::apps::v1::StatefulSetSpec,
}

pub struct StatefulSetView {
    pub metadata: ObjectMetaView,
    pub spec: Option<StatefulSetSpecView>,
}

pub struct StatefulSetSpecView {
    pub replicas: Option<int>,
    pub selector: LabelSelectorView,
    pub service_name: StringView,
}

impl StatefulSet {
    pub spec fn view(&self) -> StatefulSetView;

    #[verifier(external_body)]
    pub fn default() -> (stateful_set: StatefulSet)
        ensures
            stateful_set@ == StatefulSetView::default(),
    {
        StatefulSet {
            inner: k8s_openapi::api::apps::v1::StatefulSet::default(),
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
    pub fn spec(&self) -> (spec: Option<StatefulSetSpec>)
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
        self.inner.metadata = metadata.into_kube_object_meta();
    }

    #[verifier(external_body)]
    pub fn set_spec(&mut self, spec: StatefulSetSpec)
        ensures
            self@ == old(self)@.set_spec(spec@),
    {
        self.inner.spec = std::option::Option::Some(spec.into_kube_stateful_set_spec());
    }

    #[verifier(external)]
    pub fn into_kube_obj(self) -> k8s_openapi::api::apps::v1::StatefulSet {
        self.inner
    }

    #[verifier(external_body)]
    pub fn api_resource() -> (res: ApiResource)
        ensures
            res@.kind == Kind::CustomResourceKind,
    {
        ApiResource::from_kube_api_resource(kube::api::ApiResource::erase::<k8s_openapi::api::apps::v1::StatefulSet>(&()))
    }

    // NOTE: This function assumes serde_json::to_string won't fail!
    #[verifier(external_body)]
    pub fn to_dynamic_object(self) -> (obj: DynamicObject)
        ensures
            obj@ == self@.to_dynamic_object(),
    {
        DynamicObject::from_kube_obj(
            k8s_openapi::serde_json::from_str(&k8s_openapi::serde_json::to_string(&self.inner).unwrap()).unwrap()
        )
    }

    /// Convert a DynamicObject to a StatefulSet
    #[verifier(external_body)]
    pub fn from_dynamic_object(obj: DynamicObject) -> (sts: StatefulSet)
        ensures
            sts@ == StatefulSetView::from_dynamic_object(obj@),
    {
        StatefulSet { inner: obj.into_kube_obj().try_parse::<k8s_openapi::api::apps::v1::StatefulSet>().unwrap() }
    }
}

impl StatefulSetView {
    pub open spec fn default() -> StatefulSetView {
        StatefulSetView {
            metadata: ObjectMetaView::default(),
            spec: Option::None,
        }
    }

    pub open spec fn set_metadata(self, metadata: ObjectMetaView) -> StatefulSetView {
        StatefulSetView {
            metadata: metadata,
            ..self
        }
    }

    pub open spec fn set_spec(self, spec: StatefulSetSpecView) -> StatefulSetView {
        StatefulSetView {
            spec: Option::Some(spec),
            ..self
        }
    }

    pub open spec fn spec_field() -> nat {0}
}

impl ResourceView for StatefulSetView {
    open spec fn metadata(self) -> ObjectMetaView {
        self.metadata
    }

    open spec fn kind(self) -> Kind {
        Kind::StatefulSetKind
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

    open spec fn from_dynamic_object(obj: DynamicObjectView) -> StatefulSetView {
        StatefulSetView {
            metadata: obj.metadata,
            spec: if obj.data.get_Object_0()[Self::spec_field()].is_Null() {Option::None} else {
                Option::Some(StatefulSetSpecView::unmarshal(obj.data.get_Object_0()[Self::spec_field()]))
            },
        }
    }

    proof fn integrity_check() {}
}

impl StatefulSetSpec {
    pub spec fn view(&self) -> StatefulSetSpecView;

    #[verifier(external_body)]
    pub fn default() -> (stateful_set_spec: StatefulSetSpec)
        ensures
            stateful_set_spec@ == StatefulSetSpecView::default(),
    {
        StatefulSetSpec {
            inner: k8s_openapi::api::apps::v1::StatefulSetSpec::default(),
        }
    }

    #[verifier(external_body)]
    pub fn set_replicas(&mut self, replicas: i32)
        ensures
            self@ == old(self)@.set_replicas(replicas as int),
    {
        self.inner.replicas = std::option::Option::Some(replicas)
    }

    #[verifier(external_body)]
    pub fn set_selector(&mut self, selector: LabelSelector)
        ensures
            self@ == old(self)@.set_selector(selector@),
    {
        self.inner.selector = selector.into_kube_label_selector()
    }

    #[verifier(external_body)]
    pub fn set_service_name(&mut self, service_name: String)
        ensures
            self@ == old(self)@.set_service_name(service_name@),
    {
        self.inner.service_name = service_name.into_rust_string()
    }

    #[verifier(external)]
    pub fn into_kube_stateful_set_spec(self) -> k8s_openapi::api::apps::v1::StatefulSetSpec {
        self.inner
    }
}

impl StatefulSetSpecView {
    pub open spec fn default() -> StatefulSetSpecView {
        StatefulSetSpecView {
            replicas: Option::None,
            selector: LabelSelectorView::default(),
            service_name: new_strlit("")@,
        }
    }

    pub open spec fn set_replicas(self, replicas: int) -> StatefulSetSpecView {
        StatefulSetSpecView {
            replicas: Option::Some(replicas),
            ..self
        }
    }

    pub open spec fn set_selector(self, selector: LabelSelectorView) -> StatefulSetSpecView {
        StatefulSetSpecView {
            selector: selector,
            ..self
        }
    }

    pub open spec fn set_service_name(self, service_name: StringView) -> StatefulSetSpecView {
        StatefulSetSpecView {
            service_name: service_name,
            ..self
        }
    }

    pub open spec fn marshal(self) -> Value {
        Value::Object(
            Map::empty()
                .insert(Self::replicas_field(), if self.replicas.is_None() {Value::Null} else {
                    Value::Int(self.replicas.get_Some_0())
                })
                .insert(Self::selector_field(), self.selector.marshal())
                .insert(Self::service_name_field(), Value::String(self.service_name))
        )
    }

    pub open spec fn unmarshal(value: Value) -> Self {
        StatefulSetSpecView {
            replicas: if value.get_Object_0()[Self::replicas_field()].is_Null() {Option::None} else {
                Option::Some(value.get_Object_0()[Self::replicas_field()].get_Int_0())
            },
            selector: LabelSelectorView::unmarshal(value.get_Object_0()[Self::selector_field()]),
            service_name: value.get_Object_0()[Self::service_name_field()].get_String_0(),
        }
    }

    proof fn integrity_check()
        ensures forall |o: Self| o == Self::unmarshal(#[trigger] o.marshal()),
    {}

    pub open spec fn replicas_field() -> nat {0}

    pub open spec fn selector_field() -> nat {1}

    pub open spec fn service_name_field() -> nat {2}
}

}
