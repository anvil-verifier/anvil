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

    #[verifier(inline)]
    pub open spec fn _default() -> RoleBindingView {
        RoleBindingView {
            metadata: ObjectMetaView::default(),
            role_ref: RoleRefView::default(),
            subjects: None,
        }
    }

    #[verifier(inline)]
    pub open spec fn _spec(self) -> RoleBindingSpecView {
        (self.role_ref, self.subjects)
    }

    #[verifier(inline)]
    pub open spec fn _status(self) -> EmptyStatusView {
        empty_status()
    }

    #[verifier(inline)]
    pub open spec fn _unmarshal_helper(obj: DynamicObjectView) -> RoleBindingView {
        RoleBindingView {
            metadata: obj.metadata,
            role_ref: RoleBindingView::unmarshal_spec(obj.spec)->Ok_0.0,
            subjects: RoleBindingView::unmarshal_spec(obj.spec)->Ok_0.1,
        }
    }

    #[verifier(inline)]
    pub open spec fn _state_validation(self) -> bool {
        &&& self.role_ref.api_group == "rbac.authorization.k8s.io"@
        &&& (self.role_ref.kind == "Role"@ || self.role_ref.kind == "ClusterRole"@)
        // &&& self.role_ref.name.len() > 0
        // &&& self.subjects is Some
        //     ==> forall |i| 0 <= i < self.subjects->0.len() ==> #[trigger] self.subjects->0[i].state_validation(true)
    }

    #[verifier(inline)]
    pub open spec fn _transition_validation(self, old_obj: RoleBindingView) -> bool {
        old_obj.role_ref == self.role_ref // role_ref is immutable
    }
}

implement_resource_view_trait!(RoleBindingView, RoleBindingSpecView, EmptyStatusView, _default, Kind::RoleBindingKind,
    _spec, _status, _unmarshal_helper, _state_validation, _transition_validation);

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
