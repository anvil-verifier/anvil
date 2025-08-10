// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::exec::resource::*;
use crate::kubernetes_api_objects::spec::volume::*;
use vstd::prelude::*;

implement_field_wrapper_type!(
    Volume,
    deps_hack::k8s_openapi::api::core::v1::Volume,
    VolumeView
);

implement_field_wrapper_type!(
    EmptyDirVolumeSource,
    deps_hack::k8s_openapi::api::core::v1::EmptyDirVolumeSource,
    EmptyDirVolumeSourceView
);

implement_field_wrapper_type!(
    HostPathVolumeSource,
    deps_hack::k8s_openapi::api::core::v1::HostPathVolumeSource,
    HostPathVolumeSourceView
);

implement_field_wrapper_type!(
    ConfigMapVolumeSource,
    deps_hack::k8s_openapi::api::core::v1::ConfigMapVolumeSource,
    ConfigMapVolumeSourceView
);

implement_field_wrapper_type!(
    SecretVolumeSource,
    deps_hack::k8s_openapi::api::core::v1::SecretVolumeSource,
    SecretVolumeSourceView
);

implement_field_wrapper_type!(
    ProjectedVolumeSource,
    deps_hack::k8s_openapi::api::core::v1::ProjectedVolumeSource,
    ProjectedVolumeSourceView
);

implement_field_wrapper_type!(
    VolumeProjection,
    deps_hack::k8s_openapi::api::core::v1::VolumeProjection,
    VolumeProjectionView
);

implement_field_wrapper_type!(
    ConfigMapProjection,
    deps_hack::k8s_openapi::api::core::v1::ConfigMapProjection,
    ConfigMapProjectionView
);

implement_field_wrapper_type!(
    SecretProjection,
    deps_hack::k8s_openapi::api::core::v1::SecretProjection,
    SecretProjectionView
);

implement_field_wrapper_type!(
    KeyToPath,
    deps_hack::k8s_openapi::api::core::v1::KeyToPath,
    KeyToPathView
);

implement_field_wrapper_type!(
    DownwardAPIVolumeSource,
    deps_hack::k8s_openapi::api::core::v1::DownwardAPIVolumeSource,
    DownwardAPIVolumeSourceView
);

implement_field_wrapper_type!(
    DownwardAPIVolumeFile,
    deps_hack::k8s_openapi::api::core::v1::DownwardAPIVolumeFile,
    DownwardAPIVolumeFileView
);

implement_field_wrapper_type!(
    ObjectFieldSelector,
    deps_hack::k8s_openapi::api::core::v1::ObjectFieldSelector,
    ObjectFieldSelectorView
);

verus! {

impl Volume {
    #[verifier(external_body)]
    pub fn set_name(&mut self, name: String)
        ensures self@ == old(self)@.with_name(name@),
    {
        self.inner.name = name;
    }

    #[verifier(external_body)]
    pub fn set_host_path(&mut self, host_path: HostPathVolumeSource)
        ensures self@ == old(self)@.with_host_path(host_path@),
    {
        self.inner.host_path = Some(host_path.into_kube());
    }

    #[verifier(external_body)]
    pub fn set_config_map(&mut self, config_map: ConfigMapVolumeSource)
        ensures self@ == old(self)@.with_config_map(config_map@),
    {
        self.inner.config_map = Some(config_map.into_kube());
    }

    #[verifier(external_body)]
    pub fn set_projected(&mut self, projected: ProjectedVolumeSource)
        ensures self@ == old(self)@.with_projected(projected@),
    {
        self.inner.projected = Some(projected.into_kube());
    }

    #[verifier(external_body)]
    pub fn set_secret(&mut self, secret: SecretVolumeSource)
        ensures self@ == old(self)@.with_secret(secret@),
    {
        self.inner.secret = Some(secret.into_kube());
    }

    #[verifier(external_body)]
    pub fn set_downward_api(&mut self, downward_api: DownwardAPIVolumeSource)
        ensures self@ == old(self)@.with_downward_api(downward_api@),
    {
        self.inner.downward_api = Some(downward_api.into_kube());
    }

    // Methods for the fields that Anvil currently does not reason about

    #[verifier(external_body)]
    pub fn set_empty_dir(&mut self, empty_dir: EmptyDirVolumeSource)
        ensures self@ == old(self)@.with_empty_dir(empty_dir@),
    {
        self.inner.empty_dir = Some(empty_dir.into_kube());
    }
}

impl HostPathVolumeSource {
    #[verifier(external_body)]
    pub fn set_path(&mut self, path: String)
        ensures self@ == old(self)@.with_path(path@),
    {
        self.inner.path = path;
    }
}

impl ConfigMapVolumeSource {
    #[verifier(external_body)]
    pub fn set_name(&mut self, name: String)
        ensures self@ == old(self)@.with_name(name@),
    {
        self.inner.name = Some(name);
    }
}

impl SecretVolumeSource {
    #[verifier(external_body)]
    pub fn set_secret_name(&mut self, secret_name: String)
        ensures self@ == old(self)@.with_secret_name(secret_name@),
    {
        self.inner.secret_name = Some(secret_name);
    }
}

impl ProjectedVolumeSource {
    #[verifier(external_body)]
    pub fn set_sources(&mut self, sources: Vec<VolumeProjection>)
        ensures self@ == old(self)@.with_sources(sources.deep_view()),
    {
        self.inner.sources = Some(sources.into_iter().map(|v: VolumeProjection| v.into_kube()).collect());
    }
}

impl VolumeProjection {
    #[verifier(external_body)]
    pub fn set_config_map(&mut self, config_map: ConfigMapProjection)
        ensures self@ == old(self)@.with_config_map(config_map@),
    {
        self.inner.config_map = Some(config_map.into_kube());
    }

    #[verifier(external_body)]
    pub fn set_secret(&mut self, secret: SecretProjection)
        ensures self@ == old(self)@.with_secret(secret@),
    {
        self.inner.secret = Some(secret.into_kube());
    }
}

impl ConfigMapProjection {
    #[verifier(external_body)]
    pub fn set_name(&mut self, name: String)
        ensures self@ == old(self)@.with_name(name@),
    {
        self.inner.name = Some(name);
    }

    #[verifier(external_body)]
    pub fn set_items(&mut self, items: Vec<KeyToPath>)
        ensures self@ == old(self)@.with_items(items.deep_view()),
    {
        self.inner.items = Some(items.into_iter().map(|v: KeyToPath| v.into_kube()).collect());
    }
}

impl SecretProjection {
    #[verifier(external_body)]
    pub fn set_name(&mut self, name: String)
        ensures self@ == old(self)@.with_name(name@),
    {
        self.inner.name = Some(name);
    }

    #[verifier(external_body)]
    pub fn set_items(&mut self, items: Vec<KeyToPath>)
        ensures self@ == old(self)@.with_items(items.deep_view()),
    {
        self.inner.items = Some(items.into_iter().map(|v: KeyToPath| v.into_kube()).collect());
    }
}

impl KeyToPath {
    #[verifier(external_body)]
    pub fn set_key(&mut self, key: String)
        ensures self@ == old(self)@.with_key(key@),
    {
        self.inner.key = key;
    }

    #[verifier(external_body)]
    pub fn set_path(&mut self, path: String)
        ensures self@ == old(self)@.with_path(path@),
    {
        self.inner.path = path;
    }
}

impl DownwardAPIVolumeSource {
    #[verifier(external_body)]
    pub fn set_items(&mut self, items: Vec<DownwardAPIVolumeFile>)
        ensures self@ == old(self)@.with_items(items.deep_view()),
    {
        self.inner.items = Some(items.into_iter().map(|v: DownwardAPIVolumeFile| v.into_kube()).collect());
    }
}

impl DownwardAPIVolumeFile {
    #[verifier(external_body)]
    pub fn set_field_ref(&mut self, field_ref: ObjectFieldSelector)
        ensures self@ == old(self)@.with_field_ref(field_ref@),
    {
        self.inner.field_ref = Some(field_ref.into_kube());
    }

    #[verifier(external_body)]
    pub fn set_path(&mut self, path: String)
        ensures self@ == old(self)@.with_path(path@),
    {
        self.inner.path = path;
    }
}

impl ObjectFieldSelector {
    pub fn new_with(api_version: String, field_path: String) -> (object_field_selector: ObjectFieldSelector)
        ensures object_field_selector@ == ObjectFieldSelectorView::default().with_api_version(api_version@).with_field_path(field_path@),
    {
        let mut selector = ObjectFieldSelector::default();
        selector.set_api_version(api_version);
        selector.set_field_path(field_path);
        selector
    }

    #[verifier(external_body)]
    pub fn set_field_path(&mut self, field_path: String)
        ensures self@ == old(self)@.with_field_path(field_path@),
    {
        self.inner.field_path = field_path;
    }

    #[verifier(external_body)]
    pub fn set_api_version(&mut self, api_version: String)
        ensures self@ == old(self)@.with_api_version(api_version@),
    {
        self.inner.api_version = Some(api_version);
    }
}

}

implement_resource_wrapper_trait!(Volume, deps_hack::k8s_openapi::api::core::v1::Volume);

implement_resource_wrapper_trait!(
    EmptyDirVolumeSource,
    deps_hack::k8s_openapi::api::core::v1::EmptyDirVolumeSource
);

implement_resource_wrapper_trait!(
    HostPathVolumeSource,
    deps_hack::k8s_openapi::api::core::v1::HostPathVolumeSource
);

implement_resource_wrapper_trait!(
    ConfigMapVolumeSource,
    deps_hack::k8s_openapi::api::core::v1::ConfigMapVolumeSource
);

implement_resource_wrapper_trait!(
    SecretVolumeSource,
    deps_hack::k8s_openapi::api::core::v1::SecretVolumeSource
);

implement_resource_wrapper_trait!(
    ProjectedVolumeSource,
    deps_hack::k8s_openapi::api::core::v1::ProjectedVolumeSource
);

implement_resource_wrapper_trait!(
    VolumeProjection,
    deps_hack::k8s_openapi::api::core::v1::VolumeProjection
);

implement_resource_wrapper_trait!(
    ConfigMapProjection,
    deps_hack::k8s_openapi::api::core::v1::ConfigMapProjection
);

implement_resource_wrapper_trait!(
    SecretProjection,
    deps_hack::k8s_openapi::api::core::v1::SecretProjection
);

implement_resource_wrapper_trait!(KeyToPath, deps_hack::k8s_openapi::api::core::v1::KeyToPath);

implement_resource_wrapper_trait!(
    DownwardAPIVolumeSource,
    deps_hack::k8s_openapi::api::core::v1::DownwardAPIVolumeSource
);

implement_resource_wrapper_trait!(
    DownwardAPIVolumeFile,
    deps_hack::k8s_openapi::api::core::v1::DownwardAPIVolumeFile
);

implement_resource_wrapper_trait!(
    ObjectFieldSelector,
    deps_hack::k8s_openapi::api::core::v1::ObjectFieldSelector
);
