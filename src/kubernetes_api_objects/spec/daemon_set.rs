// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::spec::{
    common::*, dynamic::*, label_selector::*, object_meta::*, pod_template_spec::*, resource::*,
};
use vstd::prelude::*;

verus! {

// DaemonSetView is the ghost type of DaemonSet.

pub struct DaemonSetView {
    pub metadata: ObjectMetaView,
    pub spec: Option<DaemonSetSpecView>,
    pub status: Option<DaemonSetStatusView>,
}

impl DaemonSetView {
    pub open spec fn with_metadata(self, metadata: ObjectMetaView) -> DaemonSetView {
        DaemonSetView {
            metadata: metadata,
            ..self
        }
    }

    pub open spec fn with_spec(self, spec: DaemonSetSpecView) -> DaemonSetView {
        DaemonSetView {
            spec: Some(spec),
            ..self
        }
    }

    #[verifier(inline)]
    pub open spec fn _state_validation(self) -> bool {
        self.spec is Some
    }

    #[verifier(inline)]
    pub open spec fn _transition_validation(self, old_obj: DaemonSetView) -> bool {
        let old_spec = old_obj.spec->0;
        let new_spec = self.spec->0;
        old_spec.selector == new_spec.selector
    }
}

implement_resource_view_trait!(DaemonSetView, Option<DaemonSetSpecView>, None, Option<DaemonSetStatusView>, None,
    Kind::DaemonSetKind, _state_validation, _transition_validation);

pub struct DaemonSetSpecView {
    pub selector: LabelSelectorView,
    pub template: PodTemplateSpecView,
}

impl DaemonSetSpecView {
    pub open spec fn default() -> DaemonSetSpecView {
        DaemonSetSpecView {
            selector: LabelSelectorView::default(),
            template: PodTemplateSpecView::default(),
        }
    }

    pub open spec fn with_selector(self, selector: LabelSelectorView) -> DaemonSetSpecView {
        DaemonSetSpecView {
            selector: selector,
            ..self
        }
    }

    pub open spec fn with_template(self, template: PodTemplateSpecView) -> DaemonSetSpecView {
        DaemonSetSpecView {
            template: template,
            ..self
        }
    }
}

pub struct DaemonSetStatusView {
    pub number_ready: int,
}

impl DaemonSetStatusView {
    pub open spec fn default() -> DaemonSetStatusView {
        DaemonSetStatusView {
            number_ready: 0,
        }
    }
}


}
