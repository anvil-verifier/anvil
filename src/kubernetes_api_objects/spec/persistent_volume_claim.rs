// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::spec::{
    common::*, dynamic::*, marshal::*, object_meta::*, resource::*, resource_requirements::*,
};
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;
use vstd::seq_lib::*;

verus! {

/// PersistentVolumeClaimView is the ghost type of PersistentVolumeClaim.
/// It is supposed to be used in spec and proof code.

pub struct PersistentVolumeClaimView {
    pub metadata: ObjectMetaView,
    pub spec: Option<PersistentVolumeClaimSpecView>,
    pub status: Option<PersistentVolumeClaimStatusView>,
}

pub type PersistentVolumeClaimStatusView = EmptyStatusView;

impl PersistentVolumeClaimView {
    pub open spec fn set_metadata(self, metadata: ObjectMetaView) -> PersistentVolumeClaimView {
        PersistentVolumeClaimView {
            metadata: metadata,
            ..self
        }
    }

    pub open spec fn set_spec(self, spec: PersistentVolumeClaimSpecView) -> PersistentVolumeClaimView {
        PersistentVolumeClaimView {
            spec: Some(spec),
            ..self
        }
    }
}

impl ResourceView for PersistentVolumeClaimView {
    type Spec = Option<PersistentVolumeClaimSpecView>;
    type Status = Option<PersistentVolumeClaimStatusView>;

    open spec fn default() -> PersistentVolumeClaimView {
        PersistentVolumeClaimView {
            metadata: ObjectMetaView::default(),
            spec: None,
            status: None,
        }
    }

    open spec fn metadata(self) -> ObjectMetaView {
        self.metadata
    }

    open spec fn kind() -> Kind {
        Kind::PersistentVolumeClaimKind
    }

    open spec fn object_ref(self) -> ObjectRef {
        ObjectRef {
            kind: Self::kind(),
            name: self.metadata.name.get_Some_0(),
            namespace: self.metadata.namespace.get_Some_0(),
        }
    }

    proof fn object_ref_is_well_formed() {}

    open spec fn spec(self) -> Option<PersistentVolumeClaimSpecView> {
        self.spec
    }

    open spec fn status(self) -> Option<PersistentVolumeClaimStatusView> {
        self.status
    }

    open spec fn marshal(self) -> DynamicObjectView {
        DynamicObjectView {
            kind: Self::kind(),
            metadata: self.metadata,
            spec: PersistentVolumeClaimView::marshal_spec(self.spec),
            status: PersistentVolumeClaimView::marshal_status(self.status),
        }
    }

    open spec fn unmarshal(obj: DynamicObjectView) -> Result<PersistentVolumeClaimView, ParseDynamicObjectError> {
        if obj.kind != Self::kind() {
            Err(ParseDynamicObjectError::UnmarshalError)
        } else if !PersistentVolumeClaimView::unmarshal_spec(obj.spec).is_Ok() {
            Err(ParseDynamicObjectError::UnmarshalError)
        } else if !PersistentVolumeClaimView::unmarshal_status(obj.status).is_Ok() {
            Err(ParseDynamicObjectError::UnmarshalError)
        } else {
            Ok(PersistentVolumeClaimView {
                metadata: obj.metadata,
                spec: PersistentVolumeClaimView::unmarshal_spec(obj.spec).get_Ok_0(),
                status: PersistentVolumeClaimView::unmarshal_status(obj.status).get_Ok_0(),
            })
        }
    }

    proof fn marshal_preserves_integrity() {
        PersistentVolumeClaimView::marshal_spec_preserves_integrity();
        PersistentVolumeClaimView::marshal_status_preserves_integrity();
    }

    proof fn marshal_preserves_metadata() {}

    proof fn marshal_preserves_kind() {}

    closed spec fn marshal_spec(s: Option<PersistentVolumeClaimSpecView>) -> Value;

    closed spec fn unmarshal_spec(v: Value) -> Result<Option<PersistentVolumeClaimSpecView>, ParseDynamicObjectError>;

    closed spec fn marshal_status(s: Option<PersistentVolumeClaimStatusView>) -> Value;

    closed spec fn unmarshal_status(v: Value) -> Result<Option<PersistentVolumeClaimStatusView>, ParseDynamicObjectError>;

    #[verifier(external_body)]
    proof fn marshal_spec_preserves_integrity() {}

    #[verifier(external_body)]
    proof fn marshal_status_preserves_integrity() {}

    proof fn unmarshal_result_determined_by_unmarshal_spec_and_status() {}

    open spec fn state_validation(self) -> bool {
        &&& self.spec.is_Some()
    }

    open spec fn transition_validation(self, old_obj: PersistentVolumeClaimView) -> bool {
        true
    }
}

pub struct PersistentVolumeClaimSpecView {
    pub storage_class_name: Option<StringView>,
    pub access_modes: Option<Seq<StringView>>,
    pub resources: Option<ResourceRequirementsView>,
}

impl PersistentVolumeClaimSpecView {
    pub open spec fn default() -> PersistentVolumeClaimSpecView {
        PersistentVolumeClaimSpecView {
            storage_class_name: None,
            access_modes: None,
            resources: None,
        }
    }

    pub open spec fn set_access_modes(self, access_modes: Seq<StringView>) -> PersistentVolumeClaimSpecView {
        PersistentVolumeClaimSpecView {
            access_modes: Some(access_modes),
            ..self
        }
    }

    pub open spec fn set_resources(self, resources: ResourceRequirementsView) -> PersistentVolumeClaimSpecView {
        PersistentVolumeClaimSpecView {
            resources: Some(resources),
            ..self
        }
    }

    pub open spec fn set_storage_class_name(self, storage_class_name: StringView) -> PersistentVolumeClaimSpecView {
        PersistentVolumeClaimSpecView {
            storage_class_name: Some(storage_class_name),
            ..self
        }
    }
}

}
