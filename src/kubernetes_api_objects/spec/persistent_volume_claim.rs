// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::spec::{
    common::*, dynamic::*, object_meta::*, resource::*, volume_resource_requirements::*,
};
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

verus! {

// PersistentVolumeClaimView is the ghost type of PersistentVolumeClaim.

pub struct PersistentVolumeClaimView {
    pub metadata: ObjectMetaView,
    pub spec: Option<PersistentVolumeClaimSpecView>,
    pub status: Option<PersistentVolumeClaimStatusView>,
}

pub type PersistentVolumeClaimStatusView = EmptyStatusView;

impl PersistentVolumeClaimView {
    pub open spec fn with_metadata(self, metadata: ObjectMetaView) -> PersistentVolumeClaimView {
        PersistentVolumeClaimView {
            metadata: metadata,
            ..self
        }
    }

    pub open spec fn with_spec(self, spec: PersistentVolumeClaimSpecView) -> PersistentVolumeClaimView {
        PersistentVolumeClaimView {
            spec: Some(spec),
            ..self
        }
    }

    #[verifier(inline)]
    pub open spec fn _state_validation(self) -> bool {
        self.spec is Some
    }

    #[verifier(inline)]
    pub open spec fn _transition_validation(self, old_obj: PersistentVolumeClaimView) -> bool { true }
}

implement_resource_view_trait!(PersistentVolumeClaimView, Option<PersistentVolumeClaimSpecView>, None,
    Option<PersistentVolumeClaimStatusView>, None, Kind::PersistentVolumeClaimKind, _state_validation,
    _transition_validation);

pub struct PersistentVolumeClaimSpecView {
    pub storage_class_name: Option<StringView>,
    pub access_modes: Option<Seq<StringView>>,
    pub resources: Option<VolumeResourceRequirementsView>,
}

impl PersistentVolumeClaimSpecView {
    pub open spec fn default() -> PersistentVolumeClaimSpecView {
        PersistentVolumeClaimSpecView {
            storage_class_name: None,
            access_modes: None,
            resources: None,
        }
    }

    pub open spec fn with_access_modes(self, access_modes: Seq<StringView>) -> PersistentVolumeClaimSpecView {
        PersistentVolumeClaimSpecView {
            access_modes: Some(access_modes),
            ..self
        }
    }

    pub open spec fn with_resources(self, resources: VolumeResourceRequirementsView) -> PersistentVolumeClaimSpecView {
        PersistentVolumeClaimSpecView {
            resources: Some(resources),
            ..self
        }
    }

    pub open spec fn with_storage_class_name(self, storage_class_name: StringView) -> PersistentVolumeClaimSpecView {
        PersistentVolumeClaimSpecView {
            storage_class_name: Some(storage_class_name),
            ..self
        }
    }
}

}
