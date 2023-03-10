// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::object_meta::*;
use crate::pervasive::prelude::*;

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
    pub fn default() -> (pod: StatefulSet)
        ensures
            pod@.is_default(),
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
    pub open spec fn is_default(self) -> bool {
        &&& self.metadata.is_default()
        &&& self.spec.is_None()
        &&& self.status.is_None()
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
    pub fn default() -> (pod_spec: StatefulSetSpec)
        ensures
            pod_spec@.is_default(),
    {
        StatefulSetSpec {
            inner: K8SStatefulSetSpec::default(),
        }
    }
}

impl StatefulSetSpecView {
    pub open spec fn is_default(self) -> bool {
       true
       // The condition depends on how default() is implemented
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
    pub fn default() -> (pod_status: StatefulSetStatus)
        ensures
            pod_status@.is_default(),
    {
        StatefulSetStatus {
            inner: K8SStatefulSetStatus::default(),
        }
    }
}

impl StatefulSetStatusView {
    pub open spec fn is_default(self) -> bool {
       true
       // The condition depends on how default() is implemented
    }
}

}
