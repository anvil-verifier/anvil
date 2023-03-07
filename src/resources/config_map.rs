// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_cluster::spec::common::StringView;
use crate::pervasive::prelude::*;
use crate::resources::object_meta::*;
use crate::resources::string_map;

use k8s_openapi::api::core::v1::ConfigMap as K8SConfigMap;

verus! {

#[verifier(external_body)]
pub struct ConfigMap {
    inner: K8SConfigMap,
}

pub struct ConfigMapView {
    pub metadata: ObjectMetaView,
    pub data: Option<Map<StringView, StringView>>,
}

impl ConfigMap {
    pub spec fn view(&self) -> ConfigMapView;

    #[verifier(external_body)]
    pub fn metadata(&self) -> (metadata: ObjectMeta)
        ensures
            metadata@ == self@.metadata,
    {
        todo!()
    }

    #[verifier(external_body)]
    pub fn data(&self) -> (data: Option<string_map::StringMap>)
        ensures
            self@.data.is_Some() == data.is_Some(),
            data.is_Some() ==> data.get_Some_0()@ == self@.data.get_Some_0(),
    {
        todo!()
    }
}

}
