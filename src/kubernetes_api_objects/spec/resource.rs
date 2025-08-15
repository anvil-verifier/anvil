// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::spec::{common::*, dynamic::*, object_meta::*};
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

verus! {

// StoredState represents the entire cluster state that consists of
// many different objects in the form of DynamicObjectView
pub type StoredState = Map<ObjectRef, DynamicObjectView>;

// Value represents the data that each object/field gets marshalled into
pub type Value = StringView;

pub trait Marshallable: Sized {
    spec fn marshal(self) -> Value;

    spec fn unmarshal(v: Value) -> Result<Self, UnmarshalError>;

    proof fn marshal_preserves_integrity()
        ensures forall |o: Self| Self::unmarshal(#[trigger] o.marshal()) is Ok && o == Self::unmarshal(o.marshal())->Ok_0;
}

// This trait defines the methods that each ghost type of Kubernetes resource object should implement
pub trait ResourceView: Sized {
    type Spec;
    type Status;

    spec fn default() -> Self;

    // Get the metadata of the object

    spec fn metadata(self) -> ObjectMetaView;

    // Get the kind of the object

    spec fn kind() -> Kind;

    // Get the reference of the object,
    // which consists of kind, name and namespace

    // TODO: object_ref can be implemented here if default implementation is supported by Verus
    spec fn object_ref(self) -> ObjectRef;

    proof fn object_ref_is_well_formed()
        ensures
            forall |o: Self|
                #[trigger] o.object_ref() == (ObjectRef {
                    kind: Self::kind(),
                    name: o.metadata().name->0,
                    namespace: o.metadata().namespace->0,
                });

    // Get the spec of the object

    spec fn spec(self) -> Self::Spec;

    // Get the status of the object

    spec fn status(self) -> Self::Status;

    // Convert the object to a dynamic object

    spec fn marshal(self) -> DynamicObjectView;

    // Convert back from a dynamic object

    spec fn unmarshal(obj: DynamicObjectView) -> Result<Self, UnmarshalError>;

    // Check if the data integrity is preserved after converting to and back from dynamic object

    proof fn marshal_preserves_integrity()
        ensures forall |o: Self| Self::unmarshal(#[trigger] o.marshal()) is Ok && o == Self::unmarshal(o.marshal())->Ok_0;

    proof fn marshal_preserves_metadata()
        ensures forall |d: DynamicObjectView| #[trigger] Self::unmarshal(d) is Ok ==> d.metadata == Self::unmarshal(d)->Ok_0.metadata();

    proof fn marshal_preserves_kind()
        ensures forall |d: DynamicObjectView| #[trigger] Self::unmarshal(d) is Ok ==> d.kind == Self::kind();

    spec fn marshal_spec(s: Self::Spec) -> Value;

    spec fn unmarshal_spec(v: Value) -> Result<Self::Spec, UnmarshalError>;

    spec fn marshal_status(s: Self::Status) -> Value;

    spec fn unmarshal_status(v: Value) -> Result<Self::Status, UnmarshalError>;

    proof fn marshal_spec_preserves_integrity()
        ensures forall |s: Self::Spec| Self::unmarshal_spec(#[trigger] Self::marshal_spec(s)) is Ok && s == Self::unmarshal_spec(Self::marshal_spec(s))->Ok_0;

    proof fn marshal_status_preserves_integrity()
        ensures forall |s: Self::Status| Self::unmarshal_status(#[trigger] Self::marshal_status(s)) is Ok && s == Self::unmarshal_status(Self::marshal_status(s))->Ok_0;

    proof fn unmarshal_result_determined_by_unmarshal_spec_and_status()
        ensures
            // unmarshal is OK iff unmarshal_spec and unmarshaml_status are OK
            forall |obj: DynamicObjectView| obj.kind == Self::kind()
                ==> #[trigger] Self::unmarshal(obj) is Ok == (Self::unmarshal_spec(obj.spec) is Ok && Self::unmarshal_status(obj.status) is Ok),
            // if unmarshal is OK then unmarshalling the spec (status) gives you the spec (status) of the unmarshalled object
            forall |obj: DynamicObjectView| #[trigger] Self::unmarshal(obj) is Ok
                ==> Self::unmarshal_spec(obj.spec)->Ok_0 == Self::unmarshal(obj)->Ok_0.spec()
                    && Self::unmarshal_status(obj.status)->Ok_0 == Self::unmarshal(obj)->Ok_0.status();

    // This method specifies the validation rule that only checks the new object.
    spec fn state_validation(self) -> bool;

    // This method specifies the validation rule that checks the relations between the new and old object.
    spec fn transition_validation(self, old_obj: Self) -> bool;

}

pub type EmptyStatusView = ();

pub open spec fn empty_status() -> EmptyStatusView {
    ()
}

pub trait CustomResourceView: ResourceView {
    proof fn kind_is_custom_resource()
        ensures Self::kind().is_CustomResourceKind();

    // The following spec and proof state that validation is only determined by spec and status.
    // That is, validation is not affected by the metadata.
    // TODO: promote this to ResourceView.

    spec fn spec_status_validation(obj_spec: Self::Spec, obj_status: Self::Status) -> bool;

    proof fn validation_result_determined_by_spec_and_status()
        ensures forall |obj: Self| #[trigger] obj.state_validation() == Self::spec_status_validation(obj.spec(), obj.status());
}

#[macro_export]
macro_rules! implement_resource_view_trait {
    ($t:ty, $spec_t:ty, $spec_default:expr, $status_t:ty, $status_default:expr, $kind:expr, $state_validation:ident, $transition_validation:ident) => {
        verus! {

        impl ResourceView for $t {
            type Spec = $spec_t;
            type Status = $status_t;

            open spec fn default() -> Self {
                Self {
                    metadata: ObjectMetaView::default(),
                    spec: $spec_default,
                    status: $status_default,
                }
            }

            open spec fn metadata(self) -> ObjectMetaView {
                self.metadata
            }

            open spec fn kind() -> Kind {
                $kind
            }

            open spec fn object_ref(self) -> ObjectRef {
                ObjectRef {
                    kind: Self::kind(),
                    name: self.metadata.name->0,
                    namespace: self.metadata.namespace->0,
                }
            }

            proof fn object_ref_is_well_formed() {}

            open spec fn spec(self) -> Self::Spec {
                self.spec
            }

            open spec fn status(self) -> Self::Status {
                self.status
            }

            open spec fn marshal(self) -> DynamicObjectView {
                DynamicObjectView {
                    kind: Self::kind(),
                    metadata: self.metadata,
                    spec: Self::marshal_spec(self.spec),
                    status: Self::marshal_status(self.status),
                }
            }

            open spec fn unmarshal(obj: DynamicObjectView) -> Result<Self, UnmarshalError> {
                if obj.kind != Self::kind() {
                    Err(())
                } else if !(Self::unmarshal_spec(obj.spec) is Ok) {
                    Err(())
                } else if !(Self::unmarshal_status(obj.status) is Ok) {
                    Err(())
                } else {
                    Ok(Self {
                        metadata: obj.metadata,
                        spec: Self::unmarshal_spec(obj.spec)->Ok_0,
                        status: Self::unmarshal_status(obj.status)->Ok_0,
                    })
                }
            }

            proof fn marshal_preserves_integrity() {
                Self::marshal_spec_preserves_integrity();
                Self::marshal_status_preserves_integrity();
            }

            proof fn marshal_preserves_metadata() {}

            proof fn marshal_preserves_kind() {}

            uninterp spec fn marshal_spec(s: Self::Spec) -> Value;

            uninterp spec fn unmarshal_spec(v: Value) -> Result<Self::Spec, UnmarshalError>;

            uninterp spec fn marshal_status(s: Self::Status) -> Value;

            uninterp spec fn unmarshal_status(v: Value) -> Result<Self::Status, UnmarshalError>;

            #[verifier(external_body)]
            proof fn marshal_spec_preserves_integrity() {}

            #[verifier(external_body)]
            proof fn marshal_status_preserves_integrity() {}

            proof fn unmarshal_result_determined_by_unmarshal_spec_and_status() {}

            open spec fn state_validation(self) -> bool {
                self.$state_validation()
            }

            open spec fn transition_validation(self, old_obj: Self) -> bool {
                self.$transition_validation(old_obj)
            }
        }

        }
    };
}

pub use implement_resource_view_trait;

}
