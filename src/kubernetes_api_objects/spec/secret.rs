// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::spec::{common::*, dynamic::*, object_meta::*, resource::*};
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

verus! {

pub struct SecretView {
    pub metadata: ObjectMetaView,
    pub data: Option<Map<StringView, StringView>>, // For view, <String, String> map is used instead of <String, Bytestring> map for now.
}

type SecretSpecView = Option<Map<StringView, StringView>>;

impl SecretView {
    pub open spec fn with_metadata(self, metadata: ObjectMetaView) -> SecretView {
        SecretView {
            metadata: metadata,
            ..self
        }
    }

    pub open spec fn with_data(self, data: Map<StringView, StringView>) -> SecretView {
        SecretView {
            data: Some(data),
            ..self
        }
    }

    #[verifier(inline)]
    pub open spec fn _default() -> SecretView {
        SecretView {
            metadata: ObjectMetaView::default(),
            data: None,
        }
    }

    #[verifier(inline)]
    pub open spec fn _spec(self) -> SecretSpecView {
        self.data
    }

    #[verifier(inline)]
    pub open spec fn _status(self) -> EmptyStatusView {
        empty_status()
    }

    #[verifier(inline)]
    pub open spec fn _unmarshal_helper(obj: DynamicObjectView) -> SecretView {
        SecretView {
            metadata: obj.metadata,
            data: SecretView::unmarshal_spec(obj.spec)->Ok_0,
        }
    }

    #[verifier(inline)]
    pub open spec fn _state_validation(self) -> bool { true }

    #[verifier(inline)]
    pub open spec fn _transition_validation(self, old_obj: SecretView) -> bool { true }
}

implement_resource_view_trait!(SecretView, SecretSpecView, EmptyStatusView, _default, Kind::SecretKind, _spec,
    _status, _unmarshal_helper, _state_validation, _transition_validation);

}
