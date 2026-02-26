// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::spec::{common::*, owner_reference::*};
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

verus! {

// ObjectMetaView is the ghost type of ObjectMeta.


pub struct ObjectMetaView {
    pub name: Option<StringView>,
    pub generate_name: Option<StringView>,
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
            generate_name: None,
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

    pub open spec fn owner_references_contains(self, owner_ref: OwnerReferenceView) -> bool {
        match self.owner_references {
            Some(owner_refs) => owner_refs.contains(owner_ref),
            None => false,
        }
    }

    pub open spec fn owner_references_only_contains(self, owner_ref: OwnerReferenceView) -> bool {
        match self.owner_references {
            Some(owner_refs) => owner_refs == seq![owner_ref],
            None => false,
        }
    }

    pub open spec fn with_name(self, name: StringView) -> ObjectMetaView {
        ObjectMetaView {
            name: Some(name),
            ..self
        }
    }

    pub open spec fn with_generate_name(self, generate_name: StringView) -> ObjectMetaView {
        ObjectMetaView {
            generate_name: Some(generate_name),
            ..self
        }
    }

    pub open spec fn with_namespace(self, namespace: StringView) -> ObjectMetaView {
        ObjectMetaView {
            namespace: Some(namespace),
            ..self
        }
    }

    pub open spec fn with_labels(self, labels: Map<StringView, StringView>) -> ObjectMetaView {
        ObjectMetaView {
            labels: Some(labels),
            ..self
        }
    }

    pub open spec fn add_label(self, key: StringView, value: StringView) -> ObjectMetaView {
        let old_map = if self.labels is None {
            Map::empty()
        } else {
            self.labels->0
        };
        ObjectMetaView {
            labels: Some(old_map.insert(key, value)),
            ..self
        }
    }

    pub open spec fn without_label(self, key: StringView) -> ObjectMetaView {
        if self.labels is Some {
            ObjectMetaView {
                labels: Some(self.labels.unwrap().remove(key)),
                ..self
            }
        } else {
            self
        }
    }

    pub open spec fn without_labels(self) -> ObjectMetaView {
        ObjectMetaView {
            labels: None,
            ..self
        }
    }

    pub open spec fn with_annotations(self, annotations: Map<StringView, StringView>) -> ObjectMetaView {
        ObjectMetaView {
            annotations: Some(annotations),
            ..self
        }
    }

    pub open spec fn add_annotation(self, key: StringView, value: StringView) -> ObjectMetaView {
        let old_map = if self.annotations is None {
            Map::empty()
        } else {
            self.annotations->0
        };
        ObjectMetaView {
            annotations: Some(old_map.insert(key, value)),
            ..self
        }
    }

    pub open spec fn with_resource_version(self, resource_version: ResourceVersion) -> ObjectMetaView {
        ObjectMetaView {
            resource_version: Some(resource_version),
            ..self
        }
    }

    pub open spec fn without_resource_version(self) -> ObjectMetaView {
        ObjectMetaView {
            resource_version: None,
            ..self
        }
    }

    pub open spec fn with_owner_references(self, owner_references: Seq<OwnerReferenceView>) -> ObjectMetaView {
        ObjectMetaView {
            owner_references: Some(owner_references),
            ..self
        }
    }

    pub open spec fn with_finalizers(self, finalizers: Seq<StringView>) -> ObjectMetaView {
        ObjectMetaView {
            finalizers: Some(finalizers),
            ..self
        }
    }

    pub open spec fn without_finalizers(self) -> ObjectMetaView {
        ObjectMetaView {
            finalizers: None,
            ..self
        }
    }

    pub open spec fn finalizers_as_set(self) -> Set<StringView> {
        if self.finalizers is None {
            Set::empty()
        } else {
            self.finalizers->0.to_set()
        }
    }

    pub open spec fn with_deletion_timestamp(self, deletion_timestamp: StringView) -> ObjectMetaView {
        ObjectMetaView {
            deletion_timestamp: Some(deletion_timestamp),
            ..self
        }
    }

    pub open spec fn without_deletion_timestamp(self) -> ObjectMetaView {
        ObjectMetaView {
            deletion_timestamp: None,
            ..self
        }
    }

    pub open spec fn well_formed_for_namespaced(self) -> bool {
        &&& self.name is Some
        &&& self.namespace is Some
        &&& self.resource_version is Some
        &&& self.uid is Some
    }
}

}
