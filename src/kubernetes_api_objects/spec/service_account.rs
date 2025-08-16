// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::spec::{common::*, dynamic::*, object_meta::*, resource::*};
use vstd::prelude::*;

verus! {

// ServiceAccountView is the ghost type of ServiceAccount.

pub struct ServiceAccountView {
    pub metadata: ObjectMetaView,
    pub automount_service_account_token: Option<bool>,
}

type ServiceAccountSpecView = Option<bool>;

impl ServiceAccountView {
    pub open spec fn with_metadata(self, metadata: ObjectMetaView) -> ServiceAccountView {
        ServiceAccountView {
            metadata: metadata,
            ..self
        }
    }

    #[verifier(inline)]
    pub open spec fn _default() -> ServiceAccountView {
        ServiceAccountView {
            metadata: ObjectMetaView::default(),
            automount_service_account_token: None,
        }
    }

    #[verifier(inline)]
    pub open spec fn _spec(self) -> ServiceAccountSpecView {
        self.automount_service_account_token
    }

    #[verifier(inline)]
    pub open spec fn _status(self) -> EmptyStatusView {
        empty_status()
    }

    #[verifier(inline)]
    pub open spec fn _unmarshal_helper(obj: DynamicObjectView) -> ServiceAccountView {
        ServiceAccountView {
            metadata: obj.metadata,
            automount_service_account_token: ServiceAccountView::unmarshal_spec(obj.spec)->Ok_0,
        }
    }

    #[verifier(inline)]
    pub open spec fn _state_validation(self) -> bool { true }

    #[verifier(inline)]
    pub open spec fn _transition_validation(self, old_obj: ServiceAccountView) -> bool { true }
}

implement_resource_view_trait!(ServiceAccountView, ServiceAccountSpecView, EmptyStatusView, _default,
    Kind::ServiceAccountKind, _spec, _status, _unmarshal_helper, _state_validation, _transition_validation);

}
