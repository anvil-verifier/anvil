// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::spec::{common::*, dynamic::*, object_meta::*, resource::*};
use crate::vstd_ext::string_view::StringView;
use vstd::prelude::*;

verus! {

// RoleBindingView is the ghost type of RoleBinding.


pub struct RoleBindingView {
    pub metadata: ObjectMetaView,
    pub role_ref: RoleRefView,
    pub subjects: Option<Seq<SubjectView>>,
}

type RoleBindingSpecView = (RoleRefView, Option<Seq<SubjectView>>);

impl RoleBindingView {
    pub open spec fn with_metadata(self, metadata: ObjectMetaView) -> RoleBindingView {
        RoleBindingView {
            metadata: metadata,
            ..self
        }
    }

    pub open spec fn with_role_ref(self, role_ref: RoleRefView) -> RoleBindingView {
        RoleBindingView {
            role_ref: role_ref,
            ..self
        }
    }

    pub open spec fn with_subjects(self, subjects: Seq<SubjectView>) -> RoleBindingView {
        RoleBindingView {
            subjects: Some(subjects),
            ..self
        }
    }
}

impl ResourceView for RoleBindingView {
    type Spec = RoleBindingSpecView;
    type Status = EmptyStatusView;

    open spec fn default() -> RoleBindingView {
        RoleBindingView {
            metadata: ObjectMetaView::default(),
            role_ref: RoleRefView::default(),
            subjects: None,
        }
    }

    open spec fn metadata(self) -> ObjectMetaView {
        self.metadata
    }

    open spec fn kind() -> Kind {
        Kind::RoleBindingKind
    }

    open spec fn object_ref(self) -> ObjectRef {
        ObjectRef {
            kind: Self::kind(),
            name: self.metadata.name->0,
            namespace: self.metadata.namespace->0,
        }
    }

    proof fn object_ref_is_well_formed() {}

    open spec fn spec(self) -> RoleBindingSpecView {
        (self.role_ref, self.subjects)
    }

    open spec fn status(self) -> EmptyStatusView {
        empty_status()
    }

    open spec fn marshal(self) -> DynamicObjectView {
        DynamicObjectView {
            kind: Self::kind(),
            metadata: self.metadata,
            spec: RoleBindingView::marshal_spec((self.role_ref, self.subjects)),
            status: RoleBindingView::marshal_status(empty_status()),
        }
    }

    open spec fn unmarshal(obj: DynamicObjectView) -> Result<RoleBindingView, UnmarshalError> {
        if obj.kind != Self::kind() {
            Err(())
        } else if !(RoleBindingView::unmarshal_spec(obj.spec) is Ok) {
            Err(())
        } else if !(RoleBindingView::unmarshal_status(obj.status) is Ok) {
            Err(())
        } else {
            Ok(RoleBindingView {
                metadata: obj.metadata,
                role_ref: RoleBindingView::unmarshal_spec(obj.spec)->Ok_0.0,
                subjects: RoleBindingView::unmarshal_spec(obj.spec)->Ok_0.1,
            })
        }
    }

    proof fn marshal_preserves_integrity() {
        RoleBindingView::marshal_spec_preserves_integrity();
        RoleBindingView::marshal_status_preserves_integrity();
    }

    proof fn marshal_preserves_metadata() {}

    proof fn marshal_preserves_kind() {}

    uninterp spec fn marshal_spec(s: RoleBindingSpecView) -> Value;

    uninterp spec fn unmarshal_spec(v: Value) -> Result<RoleBindingSpecView, UnmarshalError>;

    uninterp spec fn marshal_status(s: EmptyStatusView) -> Value;

    uninterp spec fn unmarshal_status(v: Value) -> Result<EmptyStatusView, UnmarshalError>;

    #[verifier(external_body)]
    proof fn marshal_spec_preserves_integrity() {}

    #[verifier(external_body)]
    proof fn marshal_status_preserves_integrity() {}

    proof fn unmarshal_result_determined_by_unmarshal_spec_and_status() {}

    open spec fn state_validation(self) -> bool {
        &&& self.role_ref.api_group == "rbac.authorization.k8s.io"@
        &&& (self.role_ref.kind == "Role"@ || self.role_ref.kind == "ClusterRole"@)
        // &&& self.role_ref.name.len() > 0
        // &&& self.subjects is Some
        //     ==> forall |i| 0 <= i < self.subjects->0.len() ==> #[trigger] self.subjects->0[i].state_validation(true)
    }

    open spec fn transition_validation(self, old_obj: RoleBindingView) -> bool {
        &&& old_obj.role_ref == self.role_ref // role_ref is immutable
    }
}

pub struct RoleRefView {
    pub api_group: StringView,
    pub kind: StringView,
    pub name: StringView,
}

impl RoleRefView {
    pub open spec fn default() -> RoleRefView {
        RoleRefView {
            api_group: ""@,
            kind: ""@,
            name: ""@,
        }
    }

    pub open spec fn with_api_group(self, api_group: StringView) -> RoleRefView {
        RoleRefView {
            api_group: api_group,
            ..self
        }
    }

    pub open spec fn with_kind(self, kind: StringView) -> RoleRefView {
        RoleRefView {
            kind: kind,
            ..self
        }
    }

    pub open spec fn with_name(self, name: StringView) -> RoleRefView {
        RoleRefView {
            name: name,
            ..self
        }
    }
}

pub struct SubjectView {
    pub kind: StringView,
    pub name: StringView,
    pub namespace: Option<StringView>,
}

impl SubjectView {
    pub open spec fn default() -> SubjectView {
        SubjectView {
            kind: ""@,
            name: ""@,
            namespace: None,
        }
    }

    pub open spec fn state_validation(self, is_namespaced: bool) -> bool {
        &&& self.kind == "ServiceAccount"@ // TODO: support User and Group as kind here
        &&& is_namespaced ==> self.namespace is Some && self.namespace->0.len() > 0
    }

    pub open spec fn with_kind(self, kind: StringView) -> SubjectView {
        SubjectView {
            kind: kind,
            ..self
        }
    }

    pub open spec fn with_name(self, name: StringView) -> SubjectView {
        SubjectView {
            name: name,
            ..self
        }
    }

    pub open spec fn with_namespace(self, namespace: StringView) -> SubjectView {
        SubjectView {
            namespace: Some(namespace),
            ..self
        }
    }
}

}
