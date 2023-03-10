// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::common::*;
use crate::kubernetes_api_objects::object_meta::*;
use crate::pervasive::prelude::*;

use k8s_openapi::api::core::v1::Service as K8SService;
use k8s_openapi::api::core::v1::ServiceSpec as K8SServiceSpec;
use k8s_openapi::api::core::v1::ServiceStatus as K8SServiceStatus;

verus! {

#[verifier(external_body)]
pub struct Service {
    inner: K8SService,
}

pub struct ServiceView {
    pub metadata: ObjectMetaView,
    pub spec: Option<ServiceSpecView>,
    pub status: Option<ServiceStatusView>,
}

impl Service {
    pub spec fn view(&self) -> ServiceView;

    #[verifier(external_body)]
    pub fn default() -> (service: Service)
        ensures
            service@.is_default(),
    {
        Service {
            inner: K8SService::default(),
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
    pub fn spec(&self) -> (spec: Option<ServiceSpec>)
        ensures
            self@.spec.is_Some() == spec.is_Some(),
            spec.is_Some() ==> spec.get_Some_0()@ == self@.spec.get_Some_0(),
    {
        todo!()
    }

    #[verifier(external_body)]
    pub fn status(&self) -> (status: Option<ServiceStatus>)
        ensures
            self@.status.is_Some() == status.is_Some(),
            status.is_Some() ==> status.get_Some_0()@ == self@.status.get_Some_0(),
    {
        todo!()
    }
}

impl ServiceView {
    pub open spec fn kind(self) -> Kind {
        Kind::ServiceKind
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

    pub open spec fn is_default(self) -> bool {
        &&& self.metadata.is_default()
        &&& self.spec.is_None()
        &&& self.status.is_None()
    }
}

#[verifier(external_body)]
pub struct ServiceSpec {
    inner: K8SServiceSpec,
}

pub struct ServiceSpecView {
    // A lot more fields to specify...
}

impl ServiceSpec {
    pub spec fn view(&self) -> ServiceSpecView;

    #[verifier(external_body)]
    pub fn default() -> (service_spec: ServiceSpec)
        ensures
            service_spec@.is_default(),
    {
        ServiceSpec {
            inner: K8SServiceSpec::default(),
        }
    }
}

impl ServiceSpecView {
    pub open spec fn is_default(self) -> bool {
       true
       // The condition depends on how default() is implemented
    }
}

#[verifier(external_body)]
pub struct ServiceStatus {
    inner: K8SServiceStatus,
}

pub struct ServiceStatusView {
    // A lot more fields to specify...
}

impl ServiceStatus {
    pub spec fn view(&self) -> ServiceStatusView;

    #[verifier(external_body)]
    pub fn default() -> (service_status: ServiceStatus)
        ensures
            service_status@.is_default(),
    {
        ServiceStatus {
            inner: K8SServiceStatus::default(),
        }
    }
}

impl ServiceStatusView {
    pub open spec fn is_default(self) -> bool {
       true
       // The condition depends on how default() is implemented
    }
}

}
