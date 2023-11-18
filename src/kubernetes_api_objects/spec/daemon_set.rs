// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::spec::{
    common::*, dynamic::*, label_selector::*, marshal::*, object_meta::*, pod_template_spec::*,
    resource::*,
};
use crate::vstd_ext::string_map::*;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::string::*;

verus! {

/// DaemonSetView is the ghost type of DaemonSet.
/// It is supposed to be used in spec and proof code.

pub struct DaemonSetView {
    pub metadata: ObjectMetaView,
    pub spec: Option<DaemonSetSpecView>,
    pub status: Option<DaemonSetStatusView>,
}

impl DaemonSetView {
    pub open spec fn set_metadata(self, metadata: ObjectMetaView) -> DaemonSetView {
        DaemonSetView {
            metadata: metadata,
            ..self
        }
    }

    pub open spec fn set_spec(self, spec: DaemonSetSpecView) -> DaemonSetView {
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
            name: self.metadata.name.get_Some_0(),
            namespace: self.metadata.namespace.get_Some_0(),
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

    open spec fn unmarshal(obj: DynamicObjectView) -> Result<DaemonSetView, ParseDynamicObjectError> {
        if obj.kind != Self::kind() {
            Err(ParseDynamicObjectError::UnmarshalError)
        } else if !DaemonSetView::unmarshal_spec(obj.spec).is_Ok() {
            Err(ParseDynamicObjectError::UnmarshalError)
        } else if !DaemonSetView::unmarshal_status(obj.status).is_Ok() {
            Err(ParseDynamicObjectError::UnmarshalError)
        } else {
            Ok(DaemonSetView {
                metadata: obj.metadata,
                spec: DaemonSetView::unmarshal_spec(obj.spec).get_Ok_0(),
                status: DaemonSetView::unmarshal_status(obj.status).get_Ok_0(),
            })
        }
    }

    proof fn marshal_preserves_integrity() {
        DaemonSetView::marshal_spec_preserves_integrity();
        DaemonSetView::marshal_status_preserves_integrity();
    }

    proof fn marshal_preserves_metadata() {}

    proof fn marshal_preserves_kind() {}

    closed spec fn marshal_spec(s: Option<DaemonSetSpecView>) -> Value;

    closed spec fn unmarshal_spec(v: Value) -> Result<Option<DaemonSetSpecView>, ParseDynamicObjectError>;

    closed spec fn marshal_status(s: Option<DaemonSetStatusView>) -> Value;

    closed spec fn unmarshal_status(v: Value) -> Result<Option<DaemonSetStatusView>, ParseDynamicObjectError>;

    #[verifier(external_body)]
    proof fn marshal_spec_preserves_integrity() {}

    #[verifier(external_body)]
    proof fn marshal_status_preserves_integrity() {}

    proof fn unmarshal_result_determined_by_unmarshal_spec_and_status() {}

    open spec fn state_validation(self) -> bool {
        &&& self.spec.is_Some()
    }

    open spec fn transition_validation(self, old_obj: DaemonSetView) -> bool {
        let old_spec = old_obj.spec.get_Some_0();
        let new_spec = self.spec.get_Some_0();
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

    pub open spec fn set_selector(self, selector: LabelSelectorView) -> DaemonSetSpecView {
        DaemonSetSpecView {
            selector: selector,
            ..self
        }
    }

    pub open spec fn set_template(self, template: PodTemplateSpecView) -> DaemonSetSpecView {
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
