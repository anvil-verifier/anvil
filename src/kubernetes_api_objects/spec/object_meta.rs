// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::spec::{common::*, marshal::*, owner_reference::*, resource::*};
use crate::vstd_ext::string_map::*;
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;
use vstd::string::*;

verus! {

/// ObjectMetaView is the ghost type of ObjectMeta.
/// It is supposed to be used in spec and proof code.

pub struct ObjectMetaView {
    pub name: Option<StringView>,
    pub namespace: Option<StringView>,
    pub resource_version: Option<ResourceVersion>,
    pub uid: Option<Uid>,
    pub labels: Option<Map<StringView, StringView>>,
    pub annotations: Option<Map<StringView, StringView>>,
    pub owner_references: Option<Seq<OwnerReferenceView>>,
    pub finalizers: Option<Seq<StringView>>,
    pub deletion_timestamp: Option<StringView>,
}

impl ObjectMetaView {
    pub open spec fn default() -> ObjectMetaView {
        ObjectMetaView {
            name: None,
            namespace: None,
            resource_version: None,
            uid: None,
            labels: None,
            annotations: None,
            owner_references: None,
            finalizers: None,
            deletion_timestamp: None,
        }
    }

    pub open spec fn owner_references_only_contains(self, owner_ref: OwnerReferenceView) -> bool {
        match self.owner_references {
            Some(owner_refs) => owner_refs == seq![owner_ref],
            None => false,
        }
    }

    pub open spec fn set_name(self, name: StringView) -> ObjectMetaView {
        ObjectMetaView {
            name: Some(name),
            ..self
        }
    }

    pub open spec fn set_namespace(self, namespace: StringView) -> ObjectMetaView {
        ObjectMetaView {
            namespace: Some(namespace),
            ..self
        }
    }

    pub open spec fn set_labels(self, labels: Map<StringView, StringView>) -> ObjectMetaView {
        ObjectMetaView {
            labels: Some(labels),
            ..self
        }
    }

    pub open spec fn set_annotations(self, annotations: Map<StringView, StringView>) -> ObjectMetaView {
        ObjectMetaView {
            annotations: Some(annotations),
            ..self
        }
    }

    pub open spec fn add_annotation(self, key: StringView, value: StringView) -> ObjectMetaView {
        let old_map = if self.annotations.is_None() {
            Map::empty()
        } else {
            self.annotations.get_Some_0()
        };
        ObjectMetaView {
            annotations: Some(old_map.insert(key, value)),
            ..self
        }
    }

    pub open spec fn set_resource_version(self, resource_version: ResourceVersion) -> ObjectMetaView {
        ObjectMetaView {
            resource_version: Some(resource_version),
            ..self
        }
    }

    pub open spec fn set_owner_references(self, owner_references: Seq<OwnerReferenceView>) -> ObjectMetaView {
        ObjectMetaView {
            owner_references: Some(owner_references),
            ..self
        }
    }

    pub open spec fn set_finalizers(self, finalizers: Seq<StringView>) -> ObjectMetaView {
        ObjectMetaView {
            finalizers: Some(finalizers),
            ..self
        }
    }

    pub open spec fn unset_finalizers(self) -> ObjectMetaView {
        ObjectMetaView {
            finalizers: None,
            ..self
        }
    }

    pub open spec fn finalizers_as_set(self) -> Set<StringView> {
        if self.finalizers.is_None() {
            Set::empty()
        } else {
            self.finalizers.get_Some_0().to_set()
        }
    }

    pub open spec fn set_deletion_timestamp(self, deletion_timestamp: StringView) -> ObjectMetaView {
        ObjectMetaView {
            deletion_timestamp: Some(deletion_timestamp),
            ..self
        }
    }

    pub open spec fn well_formed(self) -> bool {
        &&& self.name.is_Some()
        &&& self.namespace.is_Some()
        &&& self.resource_version.is_Some()
        &&& self.uid.is_Some()
    }
}

}
