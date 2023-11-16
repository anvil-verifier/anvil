// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::spec::{
    common::*, dynamic::*, marshal::*, object_meta::*, resource::*,
};
use crate::vstd_ext::string_map::*;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

verus! {

pub struct SecretView {
    pub metadata: ObjectMetaView,
    pub data: Option<Map<StringView, StringView>>, // For view, <String, String> map is used instead of <String, Bytestring> map for now.
}

type SecretSpecView = (Option<Map<StringView, StringView>>, ());

impl SecretView {
    pub open spec fn set_metadata(self, metadata: ObjectMetaView) -> SecretView {
        SecretView {
            metadata: metadata,
            ..self
        }
    }

    pub open spec fn set_data(self, data: Map<StringView, StringView>) -> SecretView {
        SecretView {
            data: Some(data),
            ..self
        }
    }
}

impl ResourceView for SecretView {
    type Spec = SecretSpecView;
    type Status = EmptyStatusView;

    open spec fn default() -> SecretView {
        SecretView {
            metadata: ObjectMetaView::default(),
            data: None,
        }
    }

    open spec fn metadata(self) -> ObjectMetaView {
        self.metadata
    }

    open spec fn kind() -> Kind {
        Kind::SecretKind
    }

    open spec fn object_ref(self) -> ObjectRef {
        ObjectRef {
            kind: Self::kind(),
            name: self.metadata.name.get_Some_0(),
            namespace: self.metadata.namespace.get_Some_0(),
        }
    }

    open spec fn spec(self) -> SecretSpecView {
        (self.data, ())
    }

    open spec fn status(self) -> EmptyStatusView {
        empty_status()
    }

    proof fn object_ref_is_well_formed() {}

    open spec fn marshal(self) -> DynamicObjectView {
        DynamicObjectView {
            kind: Self::kind(),
            metadata: self.metadata,
            spec: SecretView::marshal_spec((self.data, ())),
            status: SecretView::marshal_status(empty_status()),
        }
    }

    open spec fn unmarshal(obj: DynamicObjectView) -> Result<SecretView, ParseDynamicObjectError> {
        if obj.kind != Self::kind() {
            Err(ParseDynamicObjectError::UnmarshalError)
        } else if !SecretView::unmarshal_spec(obj.spec).is_Ok() {
            Err(ParseDynamicObjectError::UnmarshalError)
        } else if !SecretView::unmarshal_status(obj.status).is_Ok() {
            Err(ParseDynamicObjectError::UnmarshalError)
        } else {
            Ok(SecretView {
                metadata: obj.metadata,
                data: SecretView::unmarshal_spec(obj.spec).get_Ok_0().0,
            })
        }
    }

    proof fn marshal_preserves_integrity() {
        SecretView::marshal_spec_preserves_integrity();
        SecretView::marshal_status_preserves_integrity();
    }

    proof fn marshal_preserves_metadata() {}

    proof fn marshal_preserves_kind() {}

    open spec fn marshal_spec(s: SecretSpecView) -> Value;

    open spec fn unmarshal_spec(v: Value) -> Result<SecretSpecView, ParseDynamicObjectError>;

    closed spec fn marshal_status(s: EmptyStatusView) -> Value;

    closed spec fn unmarshal_status(v: Value) -> Result<EmptyStatusView, ParseDynamicObjectError>;

    #[verifier(external_body)]
    proof fn marshal_spec_preserves_integrity() {}

    #[verifier(external_body)]
    proof fn marshal_status_preserves_integrity() {}

    proof fn unmarshal_result_determined_by_unmarshal_spec_and_status() {}

    open spec fn state_validation(self) -> bool {
        true
    }

    open spec fn transition_validation(self, old_obj: SecretView) -> bool {
        true
    }
}

}
