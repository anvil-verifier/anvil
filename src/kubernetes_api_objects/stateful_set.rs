// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::common::*;
use crate::kubernetes_api_objects::object_meta::*;
use vstd::prelude::*;

use k8s_openapi::api::apps::v1::StatefulSet as K8SStatefulSet;
use k8s_openapi::api::apps::v1::StatefulSetSpec as K8SStatefulSetSpec;
use k8s_openapi::api::apps::v1::StatefulSetStatus as K8SStatefulSetStatus;

verus! {

#[verifier(external_body)]
pub struct StatefulSet {
    inner: K8SStatefulSet,
}

pub struct StatefulSetView {
    pub metadata: ObjectMetaView,
    pub spec: Option<StatefulSetSpecView>,
    pub status: Option<StatefulSetStatusView>,
}

impl StatefulSet {
    pub spec fn view(&self) -> StatefulSetView;

    #[verifier(external_body)]
    pub fn default() -> (stateful_set: StatefulSet)
        ensures
            stateful_set@ == StatefulSetView::default(),
    {
        StatefulSet {
            inner: K8SStatefulSet::default(),
        }
    }

    #[verifier(external_body)]
    pub fn metadata(&self) -> (metadata: ObjectMeta)
        ensures
            metadata@ == self@.metadata,
    {
        todo!()
    }

    // is it OK to name it spec?
    #[verifier(external_body)]
    pub fn spec(&self) -> (spec: Option<StatefulSetSpec>)
        ensures
            self@.spec.is_Some() == spec.is_Some(),
            spec.is_Some() ==> spec.get_Some_0()@ == self@.spec.get_Some_0(),
    {
        todo!()
    }

    #[verifier(external_body)]
    pub fn status(&self) -> (status: Option<StatefulSetStatus>)
        ensures
            self@.status.is_Some() == status.is_Some(),
            status.is_Some() ==> status.get_Some_0()@ == self@.status.get_Some_0(),
    {
        todo!()
    }
}

impl StatefulSetView {
    pub open spec fn kind(self) -> Kind {
        Kind::StatefulSetKind
    }

    pub open spec fn object_ref(self) -> ObjectRef
        recommends
            self.metadata.name.is_Some(),
            self.metadata.namespace.is_Some(),
    {
        ObjectRef {
            kind: self.kind(),
            name: self.metadata.name.get_Some_0(),
            namespace: self.metadata.namespace.get_Some_0(),
        }
    }

    pub open spec fn default() -> StatefulSetView {
        StatefulSetView {
            metadata: ObjectMetaView::default(),
            spec: Option::None,
            status: Option::None,
        }
    }
}

#[verifier(external_body)]
pub struct StatefulSetSpec {
    inner: K8SStatefulSetSpec,
}

pub struct StatefulSetSpecView {
    // A lot more fields to specify...
}

impl StatefulSetSpec {
    pub spec fn view(&self) -> StatefulSetSpecView;

    #[verifier(external_body)]
    pub fn default() -> (stateful_set_spec: StatefulSetSpec)
        ensures
            stateful_set_spec@ == StatefulSetSpecView::default(),
    {
        StatefulSetSpec {
            inner: K8SStatefulSetSpec::default(),
        }
    }
}

impl StatefulSetSpecView {
    pub open spec fn default() -> StatefulSetSpecView {
       StatefulSetSpecView {}
    }
}

#[verifier(external_body)]
pub struct StatefulSetStatus {
    inner: K8SStatefulSetStatus,
}

pub struct StatefulSetStatusView {
    // A lot more fields to specify...
}

impl StatefulSetStatus {
    pub spec fn view(&self) -> StatefulSetStatusView;

    #[verifier(external_body)]
    pub fn default() -> (stateful_set_status: StatefulSetStatus)
        ensures
            stateful_set_status@ == StatefulSetStatusView::default(),
    {
        StatefulSetStatus {
            inner: K8SStatefulSetStatus::default(),
        }
    }
}

impl StatefulSetStatusView {
    pub open spec fn default() -> StatefulSetStatusView {
       StatefulSetStatusView {}
    }
}

}
