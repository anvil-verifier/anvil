// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::spec::{
    common::*, dynamic::*, marshal::*, object_meta::*, resource::*,
};
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::string::*;

verus! {

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
