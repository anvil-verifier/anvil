// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::exec::resource::*;
use crate::kubernetes_api_objects::spec::volume::*;
use vstd::prelude::*;

verus! {

#[verifier(external_body)]
pub struct Volume {
    inner: deps_hack::k8s_openapi::api::core::v1::Volume,
}

impl Volume {
    pub uninterp spec fn view(&self) -> VolumeView;

    #[verifier(external_body)]
    pub fn default() -> (volume: Volume)
        ensures volume@ == VolumeView::default(),
    {
        Volume {
            inner: deps_hack::k8s_openapi::api::core::v1::Volume::default(),
        }
    }

    #[verifier(external_body)]
    pub fn clone(&self) -> (volume: Volume)
        ensures volume@ == self@,
    {
        Volume { inner: self.inner.clone() }
    }

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

#[verifier(external_body)]
pub struct EmptyDirVolumeSource {
    inner: deps_hack::k8s_openapi::api::core::v1::EmptyDirVolumeSource,
}

impl EmptyDirVolumeSource {
    pub uninterp spec fn view(&self) -> EmptyDirVolumeSourceView;

    #[verifier(external_body)]
    pub fn default() -> (empty_dir_volum_source: EmptyDirVolumeSource)
        ensures empty_dir_volum_source@ == EmptyDirVolumeSourceView::default(),
    {
        EmptyDirVolumeSource {
            inner: deps_hack::k8s_openapi::api::core::v1::EmptyDirVolumeSource::default(),
        }
    }

    #[verifier(external_body)]
    pub fn clone(&self) -> (empty_dir_volum_source: EmptyDirVolumeSource)
        ensures empty_dir_volum_source@ == self@,
    {
        EmptyDirVolumeSource { inner: self.inner.clone() }
    }
}

#[verifier(external_body)]
pub struct HostPathVolumeSource {
    inner: deps_hack::k8s_openapi::api::core::v1::HostPathVolumeSource,
}

impl HostPathVolumeSource {
    pub uninterp spec fn view(&self) -> HostPathVolumeSourceView;

    #[verifier(external_body)]
    pub fn default() -> (host_path_volume_source: HostPathVolumeSource)
        ensures host_path_volume_source@ == HostPathVolumeSourceView::default(),
    {
        HostPathVolumeSource { inner: deps_hack::k8s_openapi::api::core::v1::HostPathVolumeSource::default() }
    }

    #[verifier(external_body)]
    pub fn clone(&self) -> (host_path_volume_source: HostPathVolumeSource)
        ensures host_path_volume_source@ == self@,
    {
        HostPathVolumeSource { inner: self.inner.clone() }
    }

    #[verifier(external_body)]
    pub fn set_path(&mut self, path: String)
        ensures self@ == old(self)@.with_path(path@),
    {
        self.inner.path = path;
    }
}

#[verifier(external_body)]
pub struct ConfigMapVolumeSource {
    inner: deps_hack::k8s_openapi::api::core::v1::ConfigMapVolumeSource,
}

impl ConfigMapVolumeSource {
    pub uninterp spec fn view(&self) -> ConfigMapVolumeSourceView;

    #[verifier(external_body)]
    pub fn default() -> (config_map_volume_source: ConfigMapVolumeSource)
        ensures config_map_volume_source@ == ConfigMapVolumeSourceView::default(),
    {
        ConfigMapVolumeSource { inner: deps_hack::k8s_openapi::api::core::v1::ConfigMapVolumeSource::default() }
    }

    #[verifier(external_body)]
    pub fn clone(&self) -> (config_map_volume_source: ConfigMapVolumeSource)
        ensures config_map_volume_source@ == self@,
    {
        ConfigMapVolumeSource { inner: self.inner.clone() }
    }

    #[verifier(external_body)]
    pub fn set_name(&mut self, name: String)
        ensures self@ == old(self)@.with_name(name@),
    {
        self.inner.name = Some(name);
    }
}

#[verifier(external_body)]
pub struct SecretVolumeSource {
    inner: deps_hack::k8s_openapi::api::core::v1::SecretVolumeSource,
}

impl SecretVolumeSource {
    pub uninterp spec fn view(&self) -> SecretVolumeSourceView;

    #[verifier(external_body)]
    pub fn default() -> (secret_volume_source: SecretVolumeSource)
        ensures secret_volume_source@ == SecretVolumeSourceView::default(),
    {
        SecretVolumeSource {
            inner: deps_hack::k8s_openapi::api::core::v1::SecretVolumeSource::default(),
        }
    }

    #[verifier(external_body)]
    pub fn clone(&self) -> (secret_volume_source: SecretVolumeSource)
        ensures secret_volume_source@ == self@,
    {
        SecretVolumeSource { inner: self.inner.clone() }
    }

    #[verifier(external_body)]
    pub fn set_secret_name(&mut self, secret_name: String)
        ensures self@ == old(self)@.with_secret_name(secret_name@),
    {
        self.inner.secret_name = Some(secret_name);
    }
}

#[verifier(external_body)]
pub struct ProjectedVolumeSource {
    inner: deps_hack::k8s_openapi::api::core::v1::ProjectedVolumeSource,
}

impl ProjectedVolumeSource {
    pub uninterp spec fn view(&self) -> ProjectedVolumeSourceView;

    #[verifier(external_body)]
    pub fn default() -> (projected_volume_source: ProjectedVolumeSource)
        ensures projected_volume_source@ == ProjectedVolumeSourceView::default(),
    {
        ProjectedVolumeSource { inner: deps_hack::k8s_openapi::api::core::v1::ProjectedVolumeSource::default() }
    }

    #[verifier(external_body)]
    pub fn clone(&self) -> (projected_volume_source: ProjectedVolumeSource)
        ensures projected_volume_source@ == self@,
    {
        ProjectedVolumeSource { inner: self.inner.clone() }
    }

    #[verifier(external_body)]
    pub fn set_sources(&mut self, sources: Vec<VolumeProjection>)
        ensures self@ == old(self)@.with_sources(sources@.map_values(|v: VolumeProjection| v@)),
    {
        self.inner.sources = Some(sources.into_iter().map(|v: VolumeProjection| v.into_kube()).collect());
    }
}

#[verifier(external_body)]
pub struct VolumeProjection {
    inner: deps_hack::k8s_openapi::api::core::v1::VolumeProjection,
}

impl VolumeProjection {
    pub uninterp spec fn view(&self) -> VolumeProjectionView;

    #[verifier(external_body)]
    pub fn default() -> (volume_projection: VolumeProjection)
        ensures volume_projection@ == VolumeProjectionView::default(),
    {
        VolumeProjection { inner: deps_hack::k8s_openapi::api::core::v1::VolumeProjection::default() }
    }

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

#[verifier(external_body)]
pub struct ConfigMapProjection {
    inner: deps_hack::k8s_openapi::api::core::v1::ConfigMapProjection,
}

impl ConfigMapProjection {
    pub uninterp spec fn view(&self) -> ConfigMapProjectionView;

    #[verifier(external_body)]
    pub fn default() -> (config_map_projection: ConfigMapProjection)
        ensures config_map_projection@ == ConfigMapProjectionView::default(),
    {
        ConfigMapProjection { inner: deps_hack::k8s_openapi::api::core::v1::ConfigMapProjection::default() }
    }

    #[verifier(external_body)]
    pub fn clone(&self) -> (config_map_projection: ConfigMapProjection)
        ensures config_map_projection@ == self@,
    {
        ConfigMapProjection { inner: self.inner.clone() }
    }

    #[verifier(external_body)]
    pub fn set_name(&mut self, name: String)
        ensures self@ == old(self)@.with_name(name@),
    {
        self.inner.name = Some(name);
    }

    #[verifier(external_body)]
    pub fn set_items(&mut self, items: Vec<KeyToPath>)
        ensures self@ == old(self)@.with_items(items@.map_values(|v: KeyToPath| v@)),
    {
        self.inner.items = Some(items.into_iter().map(|v: KeyToPath| v.into_kube()).collect());
    }
}

#[verifier(external_body)]
pub struct SecretProjection {
    inner: deps_hack::k8s_openapi::api::core::v1::SecretProjection,
}

impl SecretProjection {
    pub uninterp spec fn view(&self) -> SecretProjectionView;

    #[verifier(external_body)]
    pub fn default() -> (secret_projection: SecretProjection)
        ensures secret_projection@ == SecretProjectionView::default(),
    {
        SecretProjection { inner: deps_hack::k8s_openapi::api::core::v1::SecretProjection::default() }
    }

    #[verifier(external_body)]
    pub fn clone(&self) -> (secret_projection: SecretProjection)
        ensures secret_projection@ == self@,
    {
        SecretProjection { inner: self.inner.clone() }
    }

    #[verifier(external_body)]
    pub fn set_name(&mut self, name: String)
        ensures self@ == old(self)@.with_name(name@),
    {
        self.inner.name = Some(name);
    }

    #[verifier(external_body)]
    pub fn set_items(&mut self, items: Vec<KeyToPath>)
        ensures self@ == old(self)@.with_items(items@.map_values(|v: KeyToPath| v@)),
    {
        self.inner.items = Some(items.into_iter().map(|v: KeyToPath| v.into_kube()).collect());
    }
}

#[verifier(external_body)]
pub struct KeyToPath {
    inner: deps_hack::k8s_openapi::api::core::v1::KeyToPath,
}

impl KeyToPath {
    pub uninterp spec fn view(&self) -> KeyToPathView;

    #[verifier(external_body)]
    pub fn default() -> (key_to_path: KeyToPath)
        ensures key_to_path@ == KeyToPathView::default(),
    {
        KeyToPath { inner: deps_hack::k8s_openapi::api::core::v1::KeyToPath::default() }
    }

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

#[verifier(external_body)]
pub struct DownwardAPIVolumeSource {
    inner: deps_hack::k8s_openapi::api::core::v1::DownwardAPIVolumeSource,
}

impl DownwardAPIVolumeSource {
    pub uninterp spec fn view(&self) -> DownwardAPIVolumeSourceView;

    #[verifier(external_body)]
    pub fn default() -> (downward_api_volume_source: DownwardAPIVolumeSource)
        ensures downward_api_volume_source@ == DownwardAPIVolumeSourceView::default(),
    {
        DownwardAPIVolumeSource { inner: deps_hack::k8s_openapi::api::core::v1::DownwardAPIVolumeSource::default() }
    }

    #[verifier(external_body)]
    pub fn clone(&self) -> (downward_api_volume_source: DownwardAPIVolumeSource)
        ensures downward_api_volume_source@ == self@,
    {
        DownwardAPIVolumeSource { inner: self.inner.clone() }
    }

    #[verifier(external_body)]
    pub fn set_items(&mut self, items: Vec<DownwardAPIVolumeFile>)
        ensures self@ == old(self)@.with_items(items@.map_values(|v: DownwardAPIVolumeFile| v@)),
    {
        self.inner.items = Some(items.into_iter().map(|v: DownwardAPIVolumeFile| v.into_kube()).collect());
    }
}

#[verifier(external_body)]
pub struct DownwardAPIVolumeFile {
    inner: deps_hack::k8s_openapi::api::core::v1::DownwardAPIVolumeFile,
}

impl DownwardAPIVolumeFile {
    pub uninterp spec fn view(&self) -> DownwardAPIVolumeFileView;

    #[verifier(external_body)]
    pub fn default() -> (downward_api_volume_file: DownwardAPIVolumeFile)
        ensures downward_api_volume_file@ == DownwardAPIVolumeFileView::default(),
    {
        DownwardAPIVolumeFile { inner: deps_hack::k8s_openapi::api::core::v1::DownwardAPIVolumeFile::default() }
    }

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

#[verifier(external_body)]
pub struct ObjectFieldSelector {
    inner: deps_hack::k8s_openapi::api::core::v1::ObjectFieldSelector,
}

impl ObjectFieldSelector {
    pub uninterp spec fn view(&self) -> ObjectFieldSelectorView;

    #[verifier(external_body)]
    pub fn default() -> (object_field_selector: ObjectFieldSelector)
        ensures object_field_selector@ == ObjectFieldSelectorView::default(),
    {
        ObjectFieldSelector { inner: deps_hack::k8s_openapi::api::core::v1::ObjectFieldSelector::default() }
    }

    #[verifier(external_body)]
    pub fn clone(&self) -> (object_field_selector: ObjectFieldSelector)
        ensures object_field_selector@ == self@,
    {
        ObjectFieldSelector { inner: self.inner.clone() }
    }

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
