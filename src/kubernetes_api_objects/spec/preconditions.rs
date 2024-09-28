// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::spec::{
    common::{ResourceVersion, Uid},
    object_meta::*,
};
use vstd::prelude::*;

verus! {

pub struct PreconditionsView {
    pub uid: Option<Uid>,
    pub resource_version: Option<ResourceVersion>,
}

impl PreconditionsView {
    pub open spec fn default() -> PreconditionsView {
        PreconditionsView {
            uid: None,
            resource_version: None,
        }
    }

    pub open spec fn set_uid_from_object_meta(self, object_meta: ObjectMetaView) -> PreconditionsView {
        PreconditionsView {
            uid: object_meta.uid,
            ..self
        }
    }

    pub open spec fn set_resource_version_from_object_meta(self, object_meta: ObjectMetaView) -> PreconditionsView {
        PreconditionsView {
            resource_version: object_meta.resource_version,
            ..self
        }
    }
}

}
