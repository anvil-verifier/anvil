// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::spec::{
    api_resource::*, common::*, dynamic::*, marshal::*, object_meta::*, resource::*,
    role_binding::*,
};
use vstd::prelude::*;

verus! {

/// ClusterRoleBindingView is the ghost type of ClusterRoleBinding.
/// It is supposed to be used in spec and proof code.

pub struct ClusterRoleBindingView {
    pub metadata: ObjectMetaView,
    pub role_ref: RoleRefView,
    pub subjects: Option<Seq<SubjectView>>,
}

type ClusterRoleBindingSpecView = (RoleRefView, Option<Seq<SubjectView>>);

impl ClusterRoleBindingView {
    pub open spec fn set_metadata(self, metadata: ObjectMetaView) -> ClusterRoleBindingView {
        ClusterRoleBindingView {
            metadata: metadata,
            ..self
        }
    }

    pub open spec fn set_role_ref(self, role_ref: RoleRefView) -> ClusterRoleBindingView {
        ClusterRoleBindingView {
            role_ref: role_ref,
            ..self
        }
    }

    pub open spec fn set_subjects(self, subjects: Seq<SubjectView>) -> ClusterRoleBindingView {
        ClusterRoleBindingView {
            subjects: Some(subjects),
            ..self
        }
    }
}

impl ResourceView for ClusterRoleBindingView {
    type Spec = ClusterRoleBindingSpecView;
    type Status = EmptyStatusView;

    open spec fn default() -> ClusterRoleBindingView {
        ClusterRoleBindingView {
            metadata: ObjectMetaView::default(),
            role_ref: RoleRefView::default(),
            subjects: None,
        }
    }

    open spec fn metadata(self) -> ObjectMetaView {
        self.metadata
    }

    open spec fn kind() -> Kind {
        Kind::ClusterRoleBindingKind
    }

    open spec fn object_ref(self) -> ObjectRef {
        ObjectRef {
            kind: Self::kind(),
            name: self.metadata.name.get_Some_0(),
            namespace: self.metadata.namespace.get_Some_0(),
        }
    }

    proof fn object_ref_is_well_formed() {}

    open spec fn spec(self) -> ClusterRoleBindingSpecView {
        (self.role_ref, self.subjects)
    }

    open spec fn status(self) -> EmptyStatusView {
        empty_status()
    }

    open spec fn marshal(self) -> DynamicObjectView {
        DynamicObjectView {
            kind: Self::kind(),
            metadata: self.metadata,
            spec: ClusterRoleBindingView::marshal_spec((self.role_ref, self.subjects)),
            status: ClusterRoleBindingView::marshal_status(empty_status()),
        }
    }

    open spec fn unmarshal(obj: DynamicObjectView) -> Result<ClusterRoleBindingView, ParseDynamicObjectError> {
        if obj.kind != Self::kind() {
            Err(ParseDynamicObjectError::UnmarshalError)
        } else if !ClusterRoleBindingView::unmarshal_spec(obj.spec).is_Ok() {
            Err(ParseDynamicObjectError::UnmarshalError)
        } else if !ClusterRoleBindingView::unmarshal_status(obj.status).is_Ok() {
            Err(ParseDynamicObjectError::UnmarshalError)
        } else {
            Ok(ClusterRoleBindingView {
                metadata: obj.metadata,
                role_ref: ClusterRoleBindingView::unmarshal_spec(obj.spec).get_Ok_0().0,
                subjects: ClusterRoleBindingView::unmarshal_spec(obj.spec).get_Ok_0().1,
            })
        }
    }

    proof fn marshal_preserves_integrity() {
        ClusterRoleBindingView::marshal_spec_preserves_integrity();
        ClusterRoleBindingView::marshal_status_preserves_integrity();
    }

    proof fn marshal_preserves_metadata() {}

    proof fn marshal_preserves_kind() {}

    closed spec fn marshal_spec(s: ClusterRoleBindingSpecView) -> Value;

    closed spec fn unmarshal_spec(v: Value) -> Result<ClusterRoleBindingSpecView, ParseDynamicObjectError>;

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

    open spec fn transition_validation(self, old_obj: ClusterRoleBindingView) -> bool {
        true
    }
}

}
