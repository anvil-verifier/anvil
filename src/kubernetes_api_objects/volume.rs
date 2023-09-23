// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::{
    api_resource::*, common::*, dynamic::*, error::ParseDynamicObjectError, marshal::*,
    object_meta::*, resource::*,
};
use crate::pervasive_ext::string_view::*;
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::string::*;

verus! {

#[verifier(external_body)]
pub struct Volume {
    inner: deps_hack::k8s_openapi::api::core::v1::Volume,
}

impl Volume {
    pub spec fn view(&self) -> VolumeView;

    #[verifier(external_body)]
    pub fn default() -> (volume: Volume)
        ensures
            volume@ == VolumeView::default(),
    {
        Volume {
            inner: deps_hack::k8s_openapi::api::core::v1::Volume::default(),
        }
    }

    #[verifier(external_body)]
    pub fn set_name(&mut self, name: String)
        ensures
            self@ == old(self)@.set_name(name@),
    {
        self.inner.name = name.into_rust_string();
    }

    #[verifier(external_body)]
    pub fn set_host_path(&mut self, host_path: HostPathVolumeSource)
        ensures
            self@ == old(self)@.set_host_path(host_path@),
    {
        self.inner.host_path = Some(host_path.into_kube());
    }

    #[verifier(external_body)]
    pub fn set_config_map(&mut self, config_map: ConfigMapVolumeSource)
        ensures
            self@ == old(self)@.set_config_map(config_map@),
    {
        self.inner.config_map = Some(config_map.into_kube());
    }

    #[verifier(external_body)]
    pub fn set_projected(&mut self, projected: ProjectedVolumeSource)
        ensures
            self@ == old(self)@.set_projected(projected@),
    {
        self.inner.projected = Some(projected.into_kube());
    }

    #[verifier(external_body)]
    pub fn set_secret(&mut self, secret: SecretVolumeSource)
        ensures
            self@ == old(self)@.set_secret(secret@),
    {
        self.inner.secret = Some(secret.into_kube());
    }

    #[verifier(external_body)]
    pub fn set_downward_api(&mut self, downward_api: DownwardAPIVolumeSource)
        ensures
            self@ == old(self)@.set_downward_api(downward_api@),
    {
        self.inner.downward_api = Some(downward_api.into_kube());
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::Volume {
        self.inner
    }

    /// Methods for the fields that Anvil currently does not reason about

    #[verifier(external_body)]
    pub fn set_empty_dir(&mut self, empty_dir: EmptyDirVolumeSource)
        ensures
            self@ == old(self)@.set_empty_dir(empty_dir@),
    {
        self.inner.empty_dir = Some(empty_dir.into_kube());
    }
}

#[verifier(external_body)]
pub struct EmptyDirVolumeSource {
    inner: deps_hack::k8s_openapi::api::core::v1::EmptyDirVolumeSource,
}

impl EmptyDirVolumeSource {
    pub spec fn view(&self) -> EmptyDirVolumeSourceView;

    #[verifier(external_body)]
    pub fn default() -> (empty_dir_volum_source: EmptyDirVolumeSource)
        ensures
            empty_dir_volum_source@ == EmptyDirVolumeSourceView::default(),
    {
        EmptyDirVolumeSource {
            inner: deps_hack::k8s_openapi::api::core::v1::EmptyDirVolumeSource::default(),
        }
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::EmptyDirVolumeSource {
        self.inner
    }
}

#[verifier(external_body)]
pub struct HostPathVolumeSource {
    inner: deps_hack::k8s_openapi::api::core::v1::HostPathVolumeSource,
}

impl HostPathVolumeSource {
    pub spec fn view(&self) -> HostPathVolumeSourceView;

    #[verifier(external_body)]
    pub fn default() -> (host_path_volume_source: HostPathVolumeSource)
        ensures
            host_path_volume_source@ == HostPathVolumeSourceView::default(),
    {
        HostPathVolumeSource {
            inner: deps_hack::k8s_openapi::api::core::v1::HostPathVolumeSource::default(),
        }
    }

    #[verifier(external_body)]
    pub fn set_path(&mut self, path: String)
        ensures
            self@ == old(self)@.set_path(path@),
    {
        self.inner.path = path.into_rust_string();
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::HostPathVolumeSource {
        self.inner
    }
}

#[verifier(external_body)]
pub struct ConfigMapVolumeSource {
    inner: deps_hack::k8s_openapi::api::core::v1::ConfigMapVolumeSource,
}

impl ConfigMapVolumeSource {
    pub spec fn view(&self) -> ConfigMapVolumeSourceView;

    #[verifier(external_body)]
    pub fn default() -> (config_map_volume_source: ConfigMapVolumeSource)
        ensures
            config_map_volume_source@ == ConfigMapVolumeSourceView::default(),
    {
        ConfigMapVolumeSource {
            inner: deps_hack::k8s_openapi::api::core::v1::ConfigMapVolumeSource::default(),
        }
    }

    #[verifier(external_body)]
    pub fn set_name(&mut self, name: String)
        ensures
            self@ == old(self)@.set_name(name@),
    {
        self.inner.name = Some(name.into_rust_string());
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::ConfigMapVolumeSource {
        self.inner
    }
}

#[verifier(external_body)]
pub struct SecretVolumeSource {
    inner: deps_hack::k8s_openapi::api::core::v1::SecretVolumeSource,
}

impl SecretVolumeSource {
    pub spec fn view(&self) -> SecretVolumeSourceView;

    #[verifier(external_body)]
    pub fn default() -> (secret_volume_source: SecretVolumeSource)
        ensures
            secret_volume_source@ == SecretVolumeSourceView::default(),
    {
        SecretVolumeSource {
            inner: deps_hack::k8s_openapi::api::core::v1::SecretVolumeSource::default(),
        }
    }

    #[verifier(external_body)]
    pub fn set_secret_name(&mut self, secret_name: String)
        ensures
            self@ == old(self)@.set_secret_name(secret_name@),
    {
        self.inner.secret_name = Some(secret_name.into_rust_string());
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::SecretVolumeSource {
        self.inner
    }
}

#[verifier(external_body)]
pub struct ProjectedVolumeSource {
    inner: deps_hack::k8s_openapi::api::core::v1::ProjectedVolumeSource,
}

impl ProjectedVolumeSource {
    pub spec fn view(&self) -> ProjectedVolumeSourceView;

    #[verifier(external_body)]
    pub fn default() -> (projected_volume_source: ProjectedVolumeSource)
        ensures
            projected_volume_source@ == ProjectedVolumeSourceView::default(),
    {
        ProjectedVolumeSource {
            inner: deps_hack::k8s_openapi::api::core::v1::ProjectedVolumeSource::default(),
        }
    }

    #[verifier(external_body)]
    pub fn set_sources(&mut self, sources: Vec<VolumeProjection>)
        ensures
            self@ == old(self)@.set_sources(sources@.map_values(|v: VolumeProjection| v@)),
    {
        self.inner.sources = Some(
            sources.into_iter().map(|v: VolumeProjection| v.into_kube()).collect()
        );
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::ProjectedVolumeSource {
        self.inner
    }
}

#[verifier(external_body)]
pub struct VolumeProjection {
    inner: deps_hack::k8s_openapi::api::core::v1::VolumeProjection,
}

impl VolumeProjection {
    pub spec fn view(&self) -> VolumeProjectionView;

    #[verifier(external_body)]
    pub fn default() -> (volume_projection: VolumeProjection)
        ensures
            volume_projection@ == VolumeProjectionView::default(),
    {
        VolumeProjection {
            inner: deps_hack::k8s_openapi::api::core::v1::VolumeProjection::default(),
        }
    }

    #[verifier(external_body)]
    pub fn set_config_map(&mut self, config_map: ConfigMapProjection)
        ensures
            self@ == old(self)@.set_config_map(config_map@),
    {
        self.inner.config_map = Some(config_map.into_kube());
    }

    #[verifier(external_body)]
    pub fn set_secret(&mut self, secret: SecretProjection)
        ensures
            self@ == old(self)@.set_secret(secret@),
    {
        self.inner.secret = Some(secret.into_kube());
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::VolumeProjection {
        self.inner
    }
}

#[verifier(external_body)]
pub struct ConfigMapProjection {
    inner: deps_hack::k8s_openapi::api::core::v1::ConfigMapProjection,
}

impl ConfigMapProjection {
    pub spec fn view(&self) -> ConfigMapProjectionView;

    #[verifier(external_body)]
    pub fn default() -> (config_map_projection: ConfigMapProjection)
        ensures
            config_map_projection@ == ConfigMapProjectionView::default(),
    {
        ConfigMapProjection {
            inner: deps_hack::k8s_openapi::api::core::v1::ConfigMapProjection::default(),
        }
    }

    #[verifier(external_body)]
    pub fn set_name(&mut self, name: String)
        ensures
            self@ == old(self)@.set_name(name@),
    {
        self.inner.name = Some(name.into_rust_string());
    }

    #[verifier(external_body)]
    pub fn set_items(&mut self, items: Vec<KeyToPath>)
        ensures
            self@ == old(self)@.set_items(items@.map_values(|v: KeyToPath| v@)),
    {
        self.inner.items = Some(
            items.into_iter().map(|v: KeyToPath| v.into_kube()).collect()
        );
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::ConfigMapProjection {
        self.inner
    }
}

#[verifier(external_body)]
pub struct SecretProjection {
    inner: deps_hack::k8s_openapi::api::core::v1::SecretProjection,
}

impl SecretProjection {
    pub spec fn view(&self) -> SecretProjectionView;

    #[verifier(external_body)]
    pub fn default() -> (secret_projection: SecretProjection)
        ensures
            secret_projection@ == SecretProjectionView::default(),
    {
        SecretProjection {
            inner: deps_hack::k8s_openapi::api::core::v1::SecretProjection::default(),
        }
    }

    #[verifier(external_body)]
    pub fn set_name(&mut self, name: String)
        ensures
            self@ == old(self)@.set_name(name@),
    {
        self.inner.name = Some(name.into_rust_string());
    }

    #[verifier(external_body)]
    pub fn set_items(&mut self, items: Vec<KeyToPath>)
        ensures
            self@ == old(self)@.set_items(items@.map_values(|v: KeyToPath| v@)),
    {
        self.inner.items = Some(
            items.into_iter().map(|v: KeyToPath| v.into_kube()).collect()
        );
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::SecretProjection {
        self.inner
    }
}

#[verifier(external_body)]
pub struct KeyToPath {
    inner: deps_hack::k8s_openapi::api::core::v1::KeyToPath,
}

impl KeyToPath {
    pub spec fn view(&self) -> KeyToPathView;

    #[verifier(external_body)]
    pub fn default() -> (key_to_path: KeyToPath)
        ensures
            key_to_path@ == KeyToPathView::default(),
    {
        KeyToPath {
            inner: deps_hack::k8s_openapi::api::core::v1::KeyToPath::default(),
        }
    }

    #[verifier(external_body)]
    pub fn set_key(&mut self, key: String)
        ensures
            self@ == old(self)@.set_key(key@),
    {
        self.inner.key = key.into_rust_string();
    }

    #[verifier(external_body)]
    pub fn set_path(&mut self, path: String)
        ensures
            self@ == old(self)@.set_path(path@),
    {
        self.inner.path = path.into_rust_string();
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::KeyToPath {
        self.inner
    }
}

#[verifier(external_body)]
pub struct DownwardAPIVolumeSource {
    inner: deps_hack::k8s_openapi::api::core::v1::DownwardAPIVolumeSource,
}

impl DownwardAPIVolumeSource {
    pub spec fn view(&self) -> DownwardAPIVolumeSourceView;

    #[verifier(external_body)]
    pub fn default() -> (downward_api_volume_source: DownwardAPIVolumeSource)
        ensures
            downward_api_volume_source@ == DownwardAPIVolumeSourceView::default(),
    {
        DownwardAPIVolumeSource {
            inner: deps_hack::k8s_openapi::api::core::v1::DownwardAPIVolumeSource::default(),
        }
    }

    #[verifier(external_body)]
    pub fn set_items(&mut self, items: Vec<DownwardAPIVolumeFile>)
        ensures
            self@ == old(self)@.set_items(items@.map_values(|v: DownwardAPIVolumeFile| v@)),
    {
        self.inner.items = Some(
            items.into_iter().map(|v: DownwardAPIVolumeFile| v.into_kube()).collect()
        );
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::DownwardAPIVolumeSource {
        self.inner
    }
}

#[verifier(external_body)]
pub struct DownwardAPIVolumeFile {
    inner: deps_hack::k8s_openapi::api::core::v1::DownwardAPIVolumeFile,
}

impl DownwardAPIVolumeFile {
    pub spec fn view(&self) -> DownwardAPIVolumeFileView;

    #[verifier(external_body)]
    pub fn default() -> (downward_api_volume_file: DownwardAPIVolumeFile)
        ensures
            downward_api_volume_file@ == DownwardAPIVolumeFileView::default(),
    {
        DownwardAPIVolumeFile {
            inner: deps_hack::k8s_openapi::api::core::v1::DownwardAPIVolumeFile::default(),
        }
    }

    #[verifier(external_body)]
    pub fn set_field_ref(&mut self, field_ref: ObjectFieldSelector)
        ensures
            self@ == old(self)@.set_field_ref(field_ref@),
    {
        self.inner.field_ref = Some(field_ref.into_kube());
    }

    #[verifier(external_body)]
    pub fn set_path(&mut self, path: String)
        ensures
            self@ == old(self)@.set_path(path@),
    {
        self.inner.path = path.into_rust_string();
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::DownwardAPIVolumeFile {
        self.inner
    }
}

#[verifier(external_body)]
pub struct ObjectFieldSelector {
    inner: deps_hack::k8s_openapi::api::core::v1::ObjectFieldSelector,
}

impl ObjectFieldSelector {
    pub spec fn view(&self) -> ObjectFieldSelectorView;

    #[verifier(external_body)]
    pub fn default() -> (object_field_selector: ObjectFieldSelector)
        ensures
            object_field_selector@ == ObjectFieldSelectorView::default(),
    {
        ObjectFieldSelector {
            inner: deps_hack::k8s_openapi::api::core::v1::ObjectFieldSelector::default(),
        }
    }

    pub fn new_with(api_version: String, field_path: String) -> (object_field_selector: ObjectFieldSelector)
        ensures
            object_field_selector@ == ObjectFieldSelectorView::default().set_api_version(api_version@).set_field_path(field_path@),
    {
        let mut selector = ObjectFieldSelector::default();
        selector.set_api_version(api_version);
        selector.set_field_path(field_path);
        selector
    }

    #[verifier(external_body)]
    pub fn set_field_path(&mut self, field_path: String)
        ensures
            self@ == old(self)@.set_field_path(field_path@),
    {
        self.inner.field_path = field_path.into_rust_string();
    }

    #[verifier(external_body)]
    pub fn set_api_version(&mut self, api_version: String)
        ensures
            self@ == old(self)@.set_api_version(api_version@),
    {
        self.inner.api_version = Some(api_version.into_rust_string());
    }

    #[verifier(external)]
    pub fn into_kube(self) -> deps_hack::k8s_openapi::api::core::v1::ObjectFieldSelector {
        self.inner
    }
}

pub struct VolumeView {
    pub host_path: Option<HostPathVolumeSourceView>,
    pub config_map: Option<ConfigMapVolumeSourceView>,
    pub name: StringView,
    pub projected: Option<ProjectedVolumeSourceView>,
    pub secret: Option<SecretVolumeSourceView>,
    pub downward_api: Option<DownwardAPIVolumeSourceView>,
    pub empty_dir: Option<EmptyDirVolumeSourceView>,
}

impl VolumeView {
    pub open spec fn default() -> VolumeView {
        VolumeView {
            name: new_strlit("")@,
            config_map: None,
            host_path: None,
            projected: None,
            secret: None,
            downward_api: None,
            empty_dir: None,
        }
    }

    pub open spec fn set_host_path(self, host_path: HostPathVolumeSourceView) -> VolumeView {
        VolumeView {
            host_path: Some(host_path),
            ..self
        }
    }

    pub open spec fn set_config_map(self, config_map: ConfigMapVolumeSourceView) -> VolumeView {
        VolumeView {
            config_map: Some(config_map),
            ..self
        }
    }

    pub open spec fn set_name(self, name: StringView) -> VolumeView {
        VolumeView {
            name: name,
            ..self
        }
    }

    pub open spec fn set_projected(self, projected: ProjectedVolumeSourceView) -> VolumeView {
        VolumeView {
            projected: Some(projected),
            ..self
        }
    }

    pub open spec fn set_secret(self, secret: SecretVolumeSourceView) -> VolumeView  {
        VolumeView {
            secret: Some(secret),
            ..self
        }
    }

    pub open spec fn set_empty_dir(self, empty_dir: EmptyDirVolumeSourceView) -> VolumeView {
        VolumeView {
            empty_dir: Some(empty_dir),
            ..self
        }
    }

    pub open spec fn set_downward_api(self, downward_api: DownwardAPIVolumeSourceView) -> VolumeView {
        VolumeView {
            downward_api: Some(downward_api),
            ..self
        }
    }
}

pub struct EmptyDirVolumeSourceView {
    pub medium: Option<String>,
    pub size_limit: Option<StringView>,
}

impl EmptyDirVolumeSourceView {
    pub open spec fn default() -> EmptyDirVolumeSourceView {
        EmptyDirVolumeSourceView {
            medium: None,
            size_limit: None,
        }
    }
}

pub struct HostPathVolumeSourceView {
    pub path: StringView,
}

impl HostPathVolumeSourceView {
    pub open spec fn default() -> HostPathVolumeSourceView {
        HostPathVolumeSourceView {
            path: new_strlit("")@,
        }
    }

    pub open spec fn set_path(self, path: StringView) -> HostPathVolumeSourceView {
        HostPathVolumeSourceView {
            path: path,
            ..self
        }
    }
}

pub struct ConfigMapVolumeSourceView {
    pub name: Option<StringView>,
}

impl ConfigMapVolumeSourceView {
    pub open spec fn default() -> ConfigMapVolumeSourceView {
        ConfigMapVolumeSourceView {
            name: None,
        }
    }

    pub open spec fn set_name(self, name: StringView) -> ConfigMapVolumeSourceView {
        ConfigMapVolumeSourceView {
            name: Some(name),
            ..self
        }
    }
}

pub struct SecretVolumeSourceView {
    pub secret_name: Option<StringView>,
}

impl SecretVolumeSourceView {
    pub open spec fn default() -> SecretVolumeSourceView {
        SecretVolumeSourceView {
            secret_name: None,
        }
    }

    pub open spec fn set_secret_name(self, secret_name: StringView) -> SecretVolumeSourceView {
        SecretVolumeSourceView {
            secret_name: Some(secret_name),
            ..self
        }
    }
}

pub struct ProjectedVolumeSourceView {
    pub sources: Option<Seq<VolumeProjectionView>>,
}

impl ProjectedVolumeSourceView {
    pub open spec fn default() -> ProjectedVolumeSourceView {
        ProjectedVolumeSourceView {
            sources: None,
        }
    }

    pub open spec fn set_sources(self, sources: Seq<VolumeProjectionView>) -> ProjectedVolumeSourceView {
        ProjectedVolumeSourceView {
            sources: Some(sources),
            ..self
        }
    }
}

pub struct VolumeProjectionView {
    pub config_map: Option<ConfigMapProjectionView>,
    pub secret: Option<SecretProjectionView>,
}

impl VolumeProjectionView {
    pub open spec fn default() -> VolumeProjectionView {
        VolumeProjectionView {
            config_map: None,
            secret: None,
        }
    }

    pub open spec fn set_config_map(self, config_map: ConfigMapProjectionView) -> VolumeProjectionView {
        VolumeProjectionView {
            config_map: Some(config_map),
            ..self
        }
    }

    pub open spec fn set_secret(self, secret: SecretProjectionView) -> VolumeProjectionView {
        VolumeProjectionView {
            secret: Some(secret),
            ..self
        }
    }
}

pub struct ConfigMapProjectionView {
    pub items: Option<Seq<KeyToPathView>>,
    pub name: Option<StringView>
}

impl ConfigMapProjectionView {
    pub open spec fn default() -> ConfigMapProjectionView {
        ConfigMapProjectionView {
            items: None,
            name: None,
        }
    }

    pub open spec fn set_items(self, items: Seq<KeyToPathView>) -> ConfigMapProjectionView {
        ConfigMapProjectionView {
            items: Some(items),
            ..self
        }
    }

    pub open spec fn set_name(self, name: StringView) -> ConfigMapProjectionView {
        ConfigMapProjectionView {
            name: Some(name),
            ..self
        }
    }
}

pub struct SecretProjectionView {
    pub items: Option<Seq<KeyToPathView>>,
    pub name: Option<StringView>
}

impl SecretProjectionView {
    pub open spec fn default() -> SecretProjectionView {
        SecretProjectionView {
            items: None,
            name: None,
        }
    }

    pub open spec fn set_items(self, items: Seq<KeyToPathView>) -> SecretProjectionView {
        SecretProjectionView {
            items: Some(items),
            ..self
        }
    }

    pub open spec fn set_name(self, name: StringView) -> SecretProjectionView {
        SecretProjectionView {
            name: Some(name),
            ..self
        }
    }
}

pub struct KeyToPathView {
    pub key: StringView,
    pub path: StringView,
}

impl KeyToPathView {
    pub open spec fn default() -> KeyToPathView {
        KeyToPathView {
            key: new_strlit("")@,
            path: new_strlit("")@,
        }
    }

    pub open spec fn set_key(self, key: StringView) -> KeyToPathView {
        KeyToPathView {
            key,
            ..self
        }
    }

    pub open spec fn set_path(self, path: StringView) -> KeyToPathView {
        KeyToPathView {
            path,
            ..self
        }
    }
}

pub struct DownwardAPIVolumeSourceView {
    pub items: Option<Seq<DownwardAPIVolumeFileView>>,
}

impl DownwardAPIVolumeSourceView {
    pub open spec fn default() -> DownwardAPIVolumeSourceView {
        DownwardAPIVolumeSourceView {
            items: None,
        }
    }

    pub open spec fn set_items(self, items: Seq<DownwardAPIVolumeFileView>) -> DownwardAPIVolumeSourceView {
        DownwardAPIVolumeSourceView {
            items: Some(items),
            ..self
        }
    }
}

pub struct DownwardAPIVolumeFileView {
    pub field_ref: Option<ObjectFieldSelectorView>,
    pub path: StringView,
}

impl DownwardAPIVolumeFileView {
    pub open spec fn default() -> DownwardAPIVolumeFileView {
        DownwardAPIVolumeFileView {
            field_ref: None,
            path: new_strlit("")@,
        }
    }

    pub open spec fn set_field_ref(self, field_ref: ObjectFieldSelectorView) -> DownwardAPIVolumeFileView {
        DownwardAPIVolumeFileView {
            field_ref: Some(field_ref),
            ..self
        }
    }

    pub open spec fn set_path(self, path: StringView) -> DownwardAPIVolumeFileView {
        DownwardAPIVolumeFileView {
            path,
            ..self
        }
    }
}

pub struct ObjectFieldSelectorView {
    pub field_path: StringView,
    pub api_version: Option<StringView>,
}

impl ObjectFieldSelectorView {
    pub open spec fn default() -> ObjectFieldSelectorView {
        ObjectFieldSelectorView {
            field_path: new_strlit("")@,
            api_version: None,
        }
    }

    pub open spec fn set_field_path(self, field_path: StringView) -> ObjectFieldSelectorView {
        ObjectFieldSelectorView {
            field_path: field_path,
            ..self
        }
    }

    pub open spec fn set_api_version(self, api_version: StringView) -> ObjectFieldSelectorView {
        ObjectFieldSelectorView {
            api_version: Some(api_version),
            ..self
        }
    }
}

}
