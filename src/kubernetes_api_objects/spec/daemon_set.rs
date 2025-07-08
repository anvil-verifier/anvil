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
}

impl ResourceView for DaemonSetView {
    type Spec = Option<DaemonSetSpecView>;
    type Status = Option<DaemonSetStatusView>;

    open spec fn default() -> DaemonSetView {
        DaemonSetView {
            metadata: ObjectMetaView::default(),
            spec: None,
            status: None,
        }
    }

    open spec fn metadata(self) -> ObjectMetaView {
        self.metadata
    }

    open spec fn kind() -> Kind {
        Kind::DaemonSetKind
    }

    open spec fn object_ref(self) -> ObjectRef {
        ObjectRef {
            kind: Self::kind(),
            name: self.metadata.name->0,
            namespace: self.metadata.namespace->0,
        }
    }

    proof fn object_ref_is_well_formed() {}

    open spec fn spec(self) -> Option<DaemonSetSpecView> {
        self.spec
    }

    open spec fn status(self) -> Option<DaemonSetStatusView> {
        self.status
    }

    open spec fn marshal(self) -> DynamicObjectView {
        DynamicObjectView {
            kind: Self::kind(),
            metadata: self.metadata,
            spec: DaemonSetView::marshal_spec(self.spec),
            status: DaemonSetView::marshal_status(self.status),
        }
    }

    open spec fn unmarshal(obj: DynamicObjectView) -> Result<DaemonSetView, UnmarshalError> {
        if obj.kind != Self::kind() {
            Err(())
        } else if !(DaemonSetView::unmarshal_spec(obj.spec) is Ok) {
            Err(())
        } else if !(DaemonSetView::unmarshal_status(obj.status) is Ok) {
            Err(())
        } else {
            Ok(DaemonSetView {
                metadata: obj.metadata,
                spec: DaemonSetView::unmarshal_spec(obj.spec)->Ok_0,
                status: DaemonSetView::unmarshal_status(obj.status)->Ok_0,
            })
        }
    }

    proof fn marshal_preserves_integrity() {
        DaemonSetView::marshal_spec_preserves_integrity();
        DaemonSetView::marshal_status_preserves_integrity();
    }

    proof fn marshal_preserves_metadata() {}

    proof fn marshal_preserves_kind() {}

    uninterp spec fn marshal_spec(s: Option<DaemonSetSpecView>) -> Value;

    uninterp spec fn unmarshal_spec(v: Value) -> Result<Option<DaemonSetSpecView>, UnmarshalError>;

    uninterp spec fn marshal_status(s: Option<DaemonSetStatusView>) -> Value;

    uninterp spec fn unmarshal_status(v: Value) -> Result<Option<DaemonSetStatusView>, UnmarshalError>;

    #[verifier(external_body)]
    proof fn marshal_spec_preserves_integrity() {}

    #[verifier(external_body)]
    proof fn marshal_status_preserves_integrity() {}

    proof fn unmarshal_result_determined_by_unmarshal_spec_and_status() {}

    open spec fn state_validation(self) -> bool {
        &&& self.spec is Some
    }

    open spec fn transition_validation(self, old_obj: DaemonSetView) -> bool {
        let old_spec = old_obj.spec->0;
        let new_spec = self.spec->0;
        &&& old_spec.selector == new_spec.selector
    }
}

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

}
