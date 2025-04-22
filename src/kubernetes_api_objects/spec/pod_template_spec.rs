// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::spec::{object_meta::*, pod::*};
use vstd::prelude::*;

verus! {

pub struct PodTemplateSpecView {
    pub metadata: Option<ObjectMetaView>,
    pub spec: Option<PodSpecView>,
}

impl PodTemplateSpecView {
    pub open spec fn default() -> PodTemplateSpecView {
        PodTemplateSpecView {
            metadata: None,
            spec: None,
        }
    }

    pub open spec fn with_metadata(self, metadata: ObjectMetaView) -> PodTemplateSpecView {
        PodTemplateSpecView {
            metadata: Some(metadata),
            ..self
        }
    }

    pub open spec fn with_spec(self, spec: PodSpecView) -> PodTemplateSpecView {
        PodTemplateSpecView {
            spec: Some(spec),
            ..self
        }
    }
}

}
