use crate::kubernetes_api_objects::error::*;
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{api_server::types::*, message::*, cluster::Cluster};
use crate::state_machine::action::*;
use crate::state_machine::state_machine::*;
use crate::vstd_ext::string_view::*;
use vstd::{multiset::*, prelude::*};

verus! {

// This state machine describes the behavior of the API server and its back-end datastore (e.g., etcd).
// More concretely, it models how the datastore stores state objects, and how the API server handles
// controllers' requests to read and write state objects. We model the two components in one state
// machine because controllers always interact with state objects via API servers.
//
// The datastore provides a key-value store interface to store all the state objects. For each
// state object, the key is a tuple of its name, namespace and kind, and the value is the entire
// object. Besides name, namespace and kind, each object has other metadata fields including:
// * a resource_version that tracks the revision of this object
// * a uid that uniquely distinguishes an object from its historical occurrences
// * so on...
//
// The API server provides a REST API, including Get, List, Create, Update and Delete. The API
// implementation is more complex than a simple key-value store because a modification to the
// cluster state must pass a series of validation checks (e.g., whether the resource_version matches).
// In real world, each REST API operation above is supposed to be atomic and implemented using a etcd
// transaction, so we can model them using one state machine step.
//
// This state machine ues a Map to represent the state object datastore, matching its key-value interface.
// Besides the key-value store, this state machine also needs to maintain a local state that is used
// for managing the metadata of each object. E.g., it needs to allocate a universally unique uid to
// each object when it gets created, and updates the resource version of each object when it's updated.
//
// The model is not always submissive to the implementation. When writing the model, we sometimes choose
// the data representation that is most suitable for formal reasoning without affecting correctness.
// For example, the uid is modeled as an int, instead of a string. Generating unique uid is done by
// incrementing an int counter, so that each newly generated uid is different from any previous ones.
// This simple modeling easily guarantees the uniqueness of uid without tedious reasoning on strings.
// To make sure this inconsistency does not sacrifice soundness, Anvil does not allow controllers to see
// an object's uid. Instead, a controller can check whether two uids are the same, and copying a uid to
// construct an owner_reference or deletion precondition. In this way, modeling the uid as an int or a string
// makes no difference to controller implementations.
//
// Importantly, we do *not* model the API server's watch cache for simplicity. This means that:
// * Watch operation is not modeled, and controllers rely on the schedule_controller_reconcile action of the
// cluster state machine to get invoked (instead of getting triggered by a watch stream).
// * Controllers are forced to *not* read from the API server's watch cache and every read hits the consistent datastore.
// This avoids the time-travel bugs reported by the Sieve project (https://github.com/sieve-project/sieve).
// Note that controllers can still maintain an internal cache of the cluster state if they want.
//
// Certainly, this model is not perfect and have some inconsistency and incompleteness issues. We have a TODO
// list to gradually improve the model.
//
// The TODO list:
// + Support more expressive list operation
//
// + Model Patch (if needed)
//
// + Model uniqueness of generated name using spec ensures (when supported)
//
// + Model all the validation checks of built-in types
//
// + Model kind-specific strategy like AllowCreateOnUpdate
//
// + Model graceful deletion
//
// + Model foreground and orphan deletion options
//
// + Support cluster-wide state objects (the ones that don't belong to a namespace)
//
// + Keep the error code consistent with the real API Server
//
// + Document intended mismatch between the model and the real API server

#[verifier(inline)]
pub open spec fn unmarshallable_spec(obj: DynamicObjectView, installed_types: InstalledTypes) -> bool {
    match obj.kind {
        Kind::ConfigMapKind => ConfigMapView::unmarshal_spec(obj.spec) is Ok,
        Kind::DaemonSetKind => DaemonSetView::unmarshal_spec(obj.spec) is Ok,
        Kind::PersistentVolumeClaimKind => PersistentVolumeClaimView::unmarshal_spec(obj.spec) is Ok,
        Kind::PodKind => PodView::unmarshal_spec(obj.spec) is Ok,
        Kind::RoleBindingKind => RoleBindingView::unmarshal_spec(obj.spec) is Ok,
        Kind::RoleKind => RoleView::unmarshal_spec(obj.spec) is Ok,
        Kind::SecretKind => SecretView::unmarshal_spec(obj.spec) is Ok,
        Kind::ServiceKind => ServiceView::unmarshal_spec(obj.spec) is Ok,
        Kind::StatefulSetKind => StatefulSetView::unmarshal_spec(obj.spec) is Ok,
        Kind::ServiceAccountKind => ServiceAccountView::unmarshal_spec(obj.spec) is Ok,
        Kind::CustomResourceKind(string) => (installed_types[string].unmarshallable_spec)(obj.spec),
    }
}

#[verifier(inline)]
pub open spec fn unmarshallable_status(obj: DynamicObjectView, installed_types: InstalledTypes) -> bool {
    match obj.kind {
        Kind::ConfigMapKind => ConfigMapView::unmarshal_status(obj.status) is Ok,
        Kind::DaemonSetKind => DaemonSetView::unmarshal_status(obj.status) is Ok,
        Kind::PersistentVolumeClaimKind => PersistentVolumeClaimView::unmarshal_status(obj.status) is Ok,
        Kind::PodKind => PodView::unmarshal_status(obj.status) is Ok,
        Kind::RoleBindingKind => RoleBindingView::unmarshal_status(obj.status) is Ok,
        Kind::RoleKind => RoleView::unmarshal_status(obj.status) is Ok,
        Kind::SecretKind => SecretView::unmarshal_status(obj.status) is Ok,
        Kind::ServiceKind => ServiceView::unmarshal_status(obj.status) is Ok,
        Kind::StatefulSetKind => StatefulSetView::unmarshal_status(obj.status) is Ok,
        Kind::ServiceAccountKind => ServiceAccountView::unmarshal_status(obj.status) is Ok,
        Kind::CustomResourceKind(string) => (installed_types[string].unmarshallable_status)(obj.status),
    }
}

pub open spec fn unmarshallable_object(obj: DynamicObjectView, installed_types: InstalledTypes) -> bool {
    unmarshallable_spec(obj, installed_types) && unmarshallable_status(obj, installed_types)
}

pub open spec fn metadata_validity_check(obj: DynamicObjectView) -> Option<APIError> {
    if obj.metadata.owner_references is Some
    && obj.metadata.owner_references->0.len() > 1
    && obj.metadata.owner_references->0.filter(|o: OwnerReferenceView| o.controller is Some && o.controller->0).len() > 1 {
        Some(APIError::Invalid)
    } else {
        None
    }
}

pub open spec fn metadata_transition_validity_check(obj: DynamicObjectView, old_obj: DynamicObjectView) -> Option<APIError> {
    if old_obj.metadata.deletion_timestamp is Some
    && obj.metadata.finalizers is Some // Short circuit: we don't need to reason about the set difference if the finalizers is None
    && !obj.metadata.finalizers_as_set().subset_of(old_obj.metadata.finalizers_as_set()) {
        Some(APIError::Forbidden)
    } else {
        None
    }
}

pub open spec fn valid_object(obj: DynamicObjectView, installed_types: InstalledTypes) -> bool {
    match obj.kind {
        Kind::ConfigMapKind => ConfigMapView::unmarshal(obj)->Ok_0.state_validation(),
        Kind::DaemonSetKind => DaemonSetView::unmarshal(obj)->Ok_0.state_validation(),
        Kind::PersistentVolumeClaimKind => PersistentVolumeClaimView::unmarshal(obj)->Ok_0.state_validation(),
        Kind::PodKind => PodView::unmarshal(obj)->Ok_0.state_validation(),
        Kind::RoleBindingKind => RoleBindingView::unmarshal(obj)->Ok_0.state_validation(),
        Kind::RoleKind => RoleView::unmarshal(obj)->Ok_0.state_validation(),
        Kind::SecretKind => SecretView::unmarshal(obj)->Ok_0.state_validation(),
        Kind::ServiceKind => ServiceView::unmarshal(obj)->Ok_0.state_validation(),
        Kind::StatefulSetKind => StatefulSetView::unmarshal(obj)->Ok_0.state_validation(),
        Kind::ServiceAccountKind => ServiceAccountView::unmarshal(obj)->Ok_0.state_validation(),
        Kind::CustomResourceKind(string) => (installed_types[string].valid_object)(obj),
    }
}

pub open spec fn object_validity_check(obj: DynamicObjectView, installed_types: InstalledTypes) -> Option<APIError> {
    if !valid_object(obj, installed_types) {
        Some(APIError::Invalid)
    } else {
        None
    }
}

pub open spec fn valid_transition(obj: DynamicObjectView, old_obj: DynamicObjectView, installed_types: InstalledTypes) -> bool {
    match obj.kind {
        Kind::ConfigMapKind => ConfigMapView::unmarshal(obj)->Ok_0.transition_validation(ConfigMapView::unmarshal(old_obj)->Ok_0),
        Kind::DaemonSetKind => DaemonSetView::unmarshal(obj)->Ok_0.transition_validation(DaemonSetView::unmarshal(old_obj)->Ok_0),
        Kind::PersistentVolumeClaimKind => PersistentVolumeClaimView::unmarshal(obj)->Ok_0.transition_validation(PersistentVolumeClaimView::unmarshal(old_obj)->Ok_0),
        Kind::PodKind => PodView::unmarshal(obj)->Ok_0.transition_validation(PodView::unmarshal(old_obj)->Ok_0),
        Kind::RoleBindingKind => RoleBindingView::unmarshal(obj)->Ok_0.transition_validation(RoleBindingView::unmarshal(old_obj)->Ok_0),
        Kind::RoleKind => RoleView::unmarshal(obj)->Ok_0.transition_validation(RoleView::unmarshal(old_obj)->Ok_0),
        Kind::SecretKind => SecretView::unmarshal(obj)->Ok_0.transition_validation(SecretView::unmarshal(old_obj)->Ok_0),
        Kind::ServiceKind => ServiceView::unmarshal(obj)->Ok_0.transition_validation(ServiceView::unmarshal(old_obj)->Ok_0),
        Kind::StatefulSetKind => StatefulSetView::unmarshal(obj)->Ok_0.transition_validation(StatefulSetView::unmarshal(old_obj)->Ok_0),
        Kind::ServiceAccountKind => ServiceAccountView::unmarshal(obj)->Ok_0.transition_validation(ServiceAccountView::unmarshal(old_obj)->Ok_0),
        Kind::CustomResourceKind(string) => (installed_types[string].valid_transition)(obj, old_obj),
    }
}

pub open spec fn object_transition_validity_check(obj: DynamicObjectView, old_obj: DynamicObjectView, installed_types: InstalledTypes) -> Option<APIError> {
    if !valid_transition(obj, old_obj, installed_types) {
        Some(APIError::Invalid)
    } else {
        None
    }
}

pub open spec fn marshalled_default_status(kind: Kind, installed_types: InstalledTypes) -> Value {
    match kind {
        Kind::ConfigMapKind => ConfigMapView::marshal_status(ConfigMapView::default().status()),
        Kind::DaemonSetKind => DaemonSetView::marshal_status(DaemonSetView::default().status()),
        Kind::PersistentVolumeClaimKind => PersistentVolumeClaimView::marshal_status(PersistentVolumeClaimView::default().status()),
        Kind::PodKind => PodView::marshal_status(PodView::default().status()),
        Kind::RoleBindingKind => RoleBindingView::marshal_status(RoleBindingView::default().status()),
        Kind::RoleKind => RoleView::marshal_status(RoleView::default().status()),
        Kind::SecretKind => SecretView::marshal_status(SecretView::default().status()),
        Kind::ServiceKind => ServiceView::marshal_status(ServiceView::default().status()),
        Kind::StatefulSetKind => StatefulSetView::marshal_status(StatefulSetView::default().status()),
        Kind::ServiceAccountKind => ServiceAccountView::marshal_status(ServiceAccountView::default().status()),
        Kind::CustomResourceKind(string) => (installed_types[string].marshalled_default_status)(),
    }
}

#[verifier(inline)]
pub open spec fn handle_get_request(req: GetRequest, s: APIServerState) -> GetResponse {
    if !s.resources.contains_key(req.key) {
        // Get fails
        GetResponse{res: Err(APIError::ObjectNotFound)}
    } else {
        // Get succeeds
        GetResponse{res: Ok(s.resources[req.key])}
    }
}

#[verifier(inline)]
pub open spec fn handle_list_request(req: ListRequest, s: APIServerState) -> ListResponse {
    // s.resources.values() returns the set of objects in s.resources
    // This will not make list return fewer number of objects because
    // each object is unique in terms of {name, namespace, kind}
    ListResponse{res: Ok(s.resources.values().filter(|o: DynamicObjectView| {
        &&& o.object_ref().namespace == req.namespace
        &&& o.object_ref().kind == req.kind
    }).to_seq())}
}

pub open spec fn create_request_admission_check(installed_types: InstalledTypes, req: CreateRequest, s: APIServerState) -> Option<APIError> {
    if req.obj.metadata.name is None && req.obj.metadata.generate_name is None {
        // Creation fails because neither the name nor the generate_name of the provided object is provided
        Some(APIError::Invalid)
    } else if req.obj.metadata.namespace is Some && req.namespace != req.obj.metadata.namespace->0 {
        // Creation fails because the namespace of the provided object does not match the namespace sent on the request
        Some(APIError::BadRequest)
    } else if !unmarshallable_object(req.obj, installed_types) {
        // Creation fails because the provided object is not well formed
        Some(APIError::BadRequest) // TODO: should the error be BadRequest?
    } else if req.obj.metadata.name is Some && s.resources.contains_key(req.obj.with_namespace(req.namespace).object_ref()) {
        // Creation fails because the object has a name and it already exists
        Some(APIError::ObjectAlreadyExists)
    } else {
        None
    }
}

pub open spec fn created_object_validity_check(created_obj: DynamicObjectView, installed_types: InstalledTypes) -> Option<APIError> {
    if metadata_validity_check(created_obj) is Some {
        metadata_validity_check(created_obj)
    } else if object_validity_check(created_obj, installed_types) is Some {
        object_validity_check(created_obj, installed_types)
    } else {
        None
    }
}

pub uninterp spec fn generate_name(s: APIServerState, generate_name: StringView) -> StringView;

// NOTE: In the actual implementation, the API server might fail to generate a unique name
// after a number of attempts. For the sake of liveness, we simplify that behavior and assume
// that the API server is always able to find a unique name by random generation in our model.
// For more details, see the implementation: https://github.com/kubernetes/kubernetes/blob/v1.30.0/staging/src/k8s.io/apiserver/pkg/registry/generic/registry/store.go#L432-L443

#[verifier(external_body)]
pub proof fn generated_name_spec(s: APIServerState, generate_name_field: StringView)
    ensures
        forall |key| #[trigger] s.resources.contains_key(key) ==> key.name != generate_name(s, generate_name_field),
        exists |suffix| {
            &&& generate_name(s, generate_name_field) == generate_name_field + suffix
            &&& #[trigger] dash_free(suffix)
        }
,{}

// TODO: add fine grained support for namespace and kind
// #[verifier(external_body)]
// pub proof fn generated_name_spec(s: APIServerState, generate_name: StringView, kind: Kind, namespace: StringView)
//     ensures
//         forall |key| #[trigger] s.resources.contains_key(key) ==> (key != ObjectRef { name: generate_name(s, generate_name, kind, namespace), namespace: namespace, kind: kind }),
//         exists |suffix| generate_name(s, generate_name, kind, namespace) = generate_name + suffix,
// {}

#[verifier(inline)]
pub open spec fn handle_create_request(installed_types: InstalledTypes, req: CreateRequest, s: APIServerState) -> (APIServerState, CreateResponse) {
    if create_request_admission_check(installed_types, req, s) is Some {
        // Creation fails.
        (s, CreateResponse{res: Err(create_request_admission_check(installed_types, req, s)->0)})
    } else {
        let created_obj = DynamicObjectView {
            kind: req.obj.kind,
            metadata: ObjectMetaView {
                // Set name for new object if name is not provided, here we generate
                // a unique name. The uniqueness is guaranteed by generated_name_spec.
                name: if req.obj.metadata.name is Some {
                    req.obj.metadata.name
                } else {
                    Some(generate_name(s, req.obj.metadata.generate_name.unwrap()))
                },
                namespace: Some(req.namespace), // Set namespace for new object
                resource_version: Some(s.resource_version_counter), // Set rv for new object
                uid: Some(s.uid_counter), // Set uid for new object
                deletion_timestamp: None, // Unset deletion timestamp for new object
                ..req.obj.metadata
            },
            spec: req.obj.spec,
            status: marshalled_default_status(req.obj.kind, installed_types), // Overwrite the status with the default one
        };
        if s.resources.contains_key(created_obj.object_ref()) {
            // Note 1: You might find this branch redundant since we already have
            // generated_name_spec which guarantees that the created_obj's
            // key is different from any existing keys even if name was not provided.
            // But we still add this branch just to avoid calling generated_name_spec
            // when we want to show that create without a provided name does not override
            // an existing object when writing proofs.
            //
            // Note 2: Adding this branch also means that if we want to prove the object
            // is eventually created by a create request without the name provided,
            // we need to explicitly call generated_name_spec to show that
            // we do not fall into this branch.
            (s, CreateResponse{res: Err(APIError::ObjectAlreadyExists)})
        } else if created_object_validity_check(created_obj, installed_types) is Some {
            // Creation fails.
            (s, CreateResponse{res: Err(created_object_validity_check(created_obj, installed_types)->0)})
        } else {
            // Creation succeeds.
            (APIServerState {
                resources: s.resources.insert(created_obj.object_ref(), created_obj),
                uid_counter: s.uid_counter + 1,
                resource_version_counter: s.resource_version_counter + 1,
                ..s
            }, CreateResponse{res: Ok(created_obj)})
        }
    }
}

pub open spec fn delete_request_admission_check(req: DeleteRequest, s: APIServerState) -> Option<APIError> {
    if !s.resources.contains_key(req.key) {
        // Deletion fails because the object does not exist
        Some(APIError::ObjectNotFound)
    } else if req.preconditions is Some {
        let preconditions = req.preconditions->0;
        if preconditions.uid is Some && preconditions.uid != s.resources[req.key].metadata.uid {
            // Deletion fails because the uid of the object does not match the uid in the precondition
            Some(APIError::Conflict)
        } else if preconditions.resource_version is Some && preconditions.resource_version != s.resources[req.key].metadata.resource_version {
            // Deletion fails because the resource version of the object does not match the resource version in the precondition
            Some(APIError::Conflict)
        } else {
            None
        }
    } else {
        None
    }
}

// Here we make a compromise when modeling the behavior of setting
// deletion timestamp to each object that is deemed to be deleted.
// The real Kubernetes' behavior uses the current timestamp as the
// deletion timestamp, but we only use an opaque string here.
// This is fine because the request handling logic we want to model
// only cares whether the object has a deletion timestamp or not.
// By using this closed deletion_timestamp() function, we make the
// modeling and proof much easier compared to modelling the real clock.
pub uninterp spec fn deletion_timestamp() -> StringView;

// NOTE: Deletion has three modes including background (default), foreground, orphan.
// For now, we only model background deletion and only allow our controllers to perform background deletion
// (by hiding the mode option).
// This is acceptable for this project because background deletion is enough for all the reconciliation tasks
// performed by our controllers.
pub open spec fn handle_delete_request(req: DeleteRequest, s: APIServerState) -> (APIServerState, DeleteResponse) {
    if delete_request_admission_check(req, s) is Some {
        // Deletion fails.
        (s, DeleteResponse{res: Err(delete_request_admission_check(req, s)->0)})
    } else {
        // Deletion succeeds.
        let obj = s.resources[req.key];
        if obj.metadata.finalizers is Some && obj.metadata.finalizers->0.len() > 0 {
            // With the finalizer(s) in the object, we cannot immediately delete it from the key-value store.
            // Instead, we set the deletion timestamp of this object.
            // If the object already has a deletion timestamp, then skip.
            //
            // NOTE: Having finalizer(s) is not the only reason that a deletion is postponed. Having a graceful
            // period set in the deletion option is another reason. Currently we do not model the graceful period
            // option so we don't model how the API server checks whether a deletion should be graceful.
            // However, even without a graceful period option, deleting a Pod can still be graceful depending on its
            // spec content (see https://github.com/kubernetes/kubernetes/blob/v1.30.0/pkg/apis/core/types.go#L3256)
            // because Pod implements CheckGracefulDelete (see https://github.com/kubernetes/kubernetes/blob/v1.30.0/pkg/registry/core/pod/strategy.go#L168).
            // This is irrelevant to application controllers that do not manage pods, and acceptable for verifying
            // low-level built-in controllers because they are supposed to treat terminating pods as non-existing pods.
            if obj.metadata.deletion_timestamp is Some {
                // A deletion timestamp is already set so no need to bother it.
                (s, DeleteResponse{res: Ok(())})
            } else {
                let stamped_obj_with_new_rv = obj.with_deletion_timestamp(deletion_timestamp())
                                                 .with_resource_version(s.resource_version_counter);
                (APIServerState {
                    // Here we use req.key, instead of stamped_obj.object_ref(), to insert to the map.
                    // This is intended because using stamped_obj.object_ref() will require us to use
                    // the invariant each_object_in_etcd_is_well_formed a lot more frequently:
                    // we need this invariant to convince Verus that the stamped_obj is well formed
                    // so the key we use to insert to the map is the same as req.key.
                    resources: s.resources.insert(req.key, stamped_obj_with_new_rv),
                    resource_version_counter: s.resource_version_counter + 1,
                    ..s
                }, DeleteResponse{res: Ok(())})
            }
        } else {
            // The object can be immediately removed from the key-value store.
            //
            // NOTE: In some very corner case, the API server *seems* to first updates the object (to update its finalizers)
            // and then deletes the object immediately, which makes the entire Delete operation not atomic.
            // However, this only happens in the orphan or foreground deletion mode, so we do not model this
            // seemingly non-atomic behavior for now.
            // For more details, see how the API server updates the object in the middle of handling deletion requests:
            // https://github.com/kubernetes/kubernetes/blob/v1.30.0/staging/src/k8s.io/apiserver/pkg/registry/generic/registry/store.go#L1009
            (APIServerState {
                resources: s.resources.remove(req.key),
                resource_version_counter: s.resource_version_counter + 1,
                ..s
            }, DeleteResponse{res: Ok(())})
        }
    }
}

// Unconditional update means one can update the object without providing a resource version.
// For all the supported kinds, unconditional update is disallowed for CustomResource only.
// Note that if the resource version is provided, it has to be the correct one.
pub open spec fn allow_unconditional_update(kind: Kind) -> bool {
    match kind {
        Kind::CustomResourceKind(_) => false,
        _ => true,
    }
}

pub open spec fn update_request_admission_check_helper(installed_types: InstalledTypes, name: StringView, namespace: StringView, obj: DynamicObjectView, s: APIServerState) -> Option<APIError> {
    let key = ObjectRef {
        kind: obj.kind,
        namespace: namespace,
        name: name,
    };
    if obj.metadata.name is None {
        // Update fails because the name of the object is not provided
        Some(APIError::BadRequest)
    } else if name != obj.metadata.name->0 {
        // Update fails because the name of the provided object
        // does not match the name sent on the request
        Some(APIError::BadRequest)
    } else if obj.metadata.namespace is Some
        && namespace != obj.metadata.namespace->0 {
        // Update fails because the namespace of the provided object
        // does not match the namespace sent on the request
        Some(APIError::BadRequest)
    } else if !unmarshallable_object(obj, installed_types) {
        // Update fails because the provided object is not well formed
        // TODO: should the error be BadRequest?
        Some(APIError::BadRequest)
    } else if !s.resources.contains_key(key) {
        // Update fails because the object does not exist
        // TODO: check AllowCreateOnUpdate() to see whether to support create-on-update
        Some(APIError::ObjectNotFound)
    } else if obj.metadata.resource_version is None
        && !allow_unconditional_update(key.kind) {
        // Update fails because the object does not provide a rv and unconditional update is not supported
        Some(APIError::Invalid)
    } else if obj.metadata.resource_version is Some
        && obj.metadata.resource_version != s.resources[key].metadata.resource_version {
        // Update fails because the object has a wrong rv
        Some(APIError::Conflict)
    } else if obj.metadata.uid is Some
        && obj.metadata.uid != s.resources[key].metadata.uid {
        // Update fails because the object has a wrong uid
        Some(APIError::Conflict)
    } else {
        None
    }
}

pub open spec fn update_request_admission_check(installed_types: InstalledTypes, req: UpdateRequest, s: APIServerState) -> Option<APIError> {
    update_request_admission_check_helper(installed_types, req.name, req.namespace, req.obj, s)
}

pub open spec fn updated_object(req: UpdateRequest, old_obj: DynamicObjectView) -> DynamicObjectView {
    let updated_obj = DynamicObjectView {
        kind: old_obj.kind,
        metadata: ObjectMetaView {
            namespace: Some(req.namespace), // Overwrite namespace since it might not be provided
            resource_version: old_obj.metadata.resource_version, // Overwrite rv since it might not be provided
            uid: old_obj.metadata.uid, // Overwrite uid since it might not be provided
            deletion_timestamp: old_obj.metadata.deletion_timestamp, // Ignore any change to deletion_timestamp
            ..req.obj.metadata
        },
        spec: req.obj.spec,
        status: old_obj.status, // Ignore any change to status
    };
    updated_obj
}

pub open spec fn updated_object_validity_check(updated_obj: DynamicObjectView, old_obj: DynamicObjectView, installed_types: InstalledTypes) -> Option<APIError> {
    if metadata_validity_check(updated_obj) is Some {
        metadata_validity_check(updated_obj)
    } else if metadata_transition_validity_check(updated_obj, old_obj) is Some {
        metadata_transition_validity_check(updated_obj, old_obj)
    } else if object_validity_check(updated_obj, installed_types) is Some {
        object_validity_check(updated_obj, installed_types)
    } else if object_transition_validity_check(updated_obj, old_obj, installed_types) is Some {
        object_transition_validity_check(updated_obj, old_obj, installed_types)
    } else {
        None
    }
}

#[verifier(inline)]
pub open spec fn handle_update_request(installed_types: InstalledTypes, req: UpdateRequest, s: APIServerState) -> (APIServerState, UpdateResponse) {
    if update_request_admission_check(installed_types, req, s) is Some {
        // Update fails.
        (s, UpdateResponse{res: Err(update_request_admission_check(installed_types, req, s)->0)})
    } else {
        let old_obj = s.resources[req.key()];
        let updated_obj = updated_object(req, old_obj);
        if updated_obj == old_obj {
            // Update is a noop because there is nothing to update
            // so the resource version counter does not increase here,
            // and the resource version of this object remains the same.
            (s, UpdateResponse{res: Ok(old_obj)})
        } else {
            // Update changes something in the object (either in spec or metadata), so we set it a newer resource version,
            // which is the current rv counter.
            let updated_obj_with_new_rv = updated_obj.with_resource_version(s.resource_version_counter);
            if updated_object_validity_check(updated_obj_with_new_rv, old_obj, installed_types) is Some {
                // Update fails.
                (s, UpdateResponse{res: Err(updated_object_validity_check(updated_obj_with_new_rv, old_obj, installed_types)->0)})
            } else {
                // Update succeeds.
                if updated_obj_with_new_rv.metadata.deletion_timestamp is None
                    || (updated_obj_with_new_rv.metadata.finalizers is Some
                        && updated_obj_with_new_rv.metadata.finalizers->0.len() > 0)
                {
                    // The regular update case, where the object has no deletion timestamp set
                    // or has at least one finalizer.
                    (APIServerState {
                        resources: s.resources.insert(req.key(), updated_obj_with_new_rv),
                        resource_version_counter: s.resource_version_counter + 1, // Advance the rv counter
                        ..s
                    }, UpdateResponse{res: Ok(updated_obj_with_new_rv)})
                } else {
                    // The delete-during-update case, where the update removes the finalizers from
                    // the object that has a deletion timestamp, so the object needs to be deleted now.
                    //
                    // NOTE: in the actual implementation, when handling an update request,
                    // the API server first applies the update to the object in the key-value store,
                    // then checks whether the object can be deleted.
                    // If so, it continues to delete the object from the key-value store before replying
                    // to the update request.
                    // This means that there is a super short window where the object has been updated in the store
                    // (with a deletion timestamp and without any finalizer), but has not been deleted yet.
                    // This behavior, strictly speaking, makes the entire Update operation not atomic.
                    // We choose to still model the Update operation as an atomic step for simplicity.
                    // This design choice does not affect the correctness of the controller that issues Update
                    // in a blocking manner because the controller will never observe this intermediate state between
                    // the update and deletion.
                    // More generally speaking, this modeling won't affect the correctness of any controller that
                    // treats a terminating object without finalizers as a non-existing object --- a good practice
                    // controllers should follow.
                    //
                    // NOTE: the API server should also check whether the deletion grace period in the metadata
                    // is set to 0 before deleting the object in case of graceful deletion
                    // (see https://github.com/kubernetes/kubernetes/blob/v1.30.0/staging/src/k8s.io/apiserver/pkg/registry/generic/registry/store.go#L533).
                    // Here we omit that condition because graceful deletion is not supported.
                    (APIServerState {
                        resources: s.resources.remove(updated_obj_with_new_rv.object_ref()),
                        resource_version_counter: s.resource_version_counter + 1, // Advance the rv counter
                        ..s
                    }, UpdateResponse{res: Ok(updated_obj_with_new_rv)})
                }
            }
        }
    }
}

pub open spec fn update_status_request_admission_check(installed_types: InstalledTypes, req: UpdateStatusRequest, s: APIServerState) -> Option<APIError> {
    update_request_admission_check_helper(installed_types, req.name, req.namespace, req.obj, s)
}

pub open spec fn status_updated_object(req: UpdateStatusRequest, old_obj: DynamicObjectView) -> DynamicObjectView {
    let status_updated_object = DynamicObjectView {
        kind: old_obj.kind,
        metadata: old_obj.metadata, // Ignore any change to metadata
        spec: old_obj.spec, // Ignore any change to spec
        status: req.obj.status,
    };
    status_updated_object
}

#[verifier(inline)]
pub open spec fn handle_update_status_request(installed_types: InstalledTypes, req: UpdateStatusRequest, s: APIServerState) -> (APIServerState, UpdateStatusResponse) {
    if update_status_request_admission_check(installed_types, req, s) is Some {
        // UpdateStatus fails.
        (s, UpdateStatusResponse{res: Err(update_status_request_admission_check(installed_types, req, s)->0)})
    } else {
        let old_obj = s.resources[req.key()];
        let updated_obj = status_updated_object(req, old_obj);
        if updated_obj == old_obj {
            // UpdateStatus is a noop because there is nothing to update
            // so the resource version counter does not increase here,
            // and the resource version of this object remains the same.
            (s, UpdateStatusResponse{res: Ok(old_obj)})
        } else {
            // UpdateStatus changes something in the object (in status), so we set it a newer resource version,
            // which is the current rv counter.
            let updated_obj_with_new_rv = updated_obj.with_resource_version(s.resource_version_counter);
            if updated_object_validity_check(updated_obj_with_new_rv, old_obj, installed_types) is Some {
                // UpdateStatus fails.
                (s, UpdateStatusResponse{res: Err(updated_object_validity_check(updated_obj_with_new_rv, old_obj, installed_types)->0)})
            } else {
                // UpdateStatus succeeds.
                (APIServerState {
                    resources: s.resources.insert(req.key(), updated_obj_with_new_rv),
                    resource_version_counter: s.resource_version_counter + 1, // Advance the rv counter
                    ..s
                }, UpdateStatusResponse{res: Ok(updated_obj_with_new_rv)})
            }
        }
    }
}

pub open spec fn handle_get_request_msg(msg: Message, s: APIServerState) -> (APIServerState, Message)
    recommends
        msg.content.is_get_request(),
{
    let req = msg.content.get_get_request();
    (s, form_get_resp_msg(msg, handle_get_request(req, s)))
}

pub open spec fn handle_list_request_msg(msg: Message, s: APIServerState) -> (APIServerState, Message)
    recommends
        msg.content.is_list_request(),
{
    let req = msg.content.get_list_request();
    (s, form_list_resp_msg(msg, handle_list_request(req, s)))
}

pub open spec fn handle_create_request_msg(installed_types: InstalledTypes, msg: Message, s: APIServerState) -> (APIServerState, Message)
    recommends
        msg.content.is_create_request(),
{
    let req = msg.content.get_create_request();
    let (s_prime, resp) = handle_create_request(installed_types, req, s);
    (s_prime, form_create_resp_msg(msg, resp))
}

pub open spec fn handle_delete_request_msg(msg: Message, s: APIServerState) -> (APIServerState, Message)
    recommends
        msg.content.is_delete_request(),
{
    let req = msg.content.get_delete_request();
    let (s_prime, resp) = handle_delete_request(req, s);
    (s_prime, form_delete_resp_msg(msg, resp))
}

pub open spec fn handle_update_request_msg(installed_types: InstalledTypes, msg: Message, s: APIServerState) -> (APIServerState, Message)
    recommends
        msg.content.is_update_request(),
{
    let req = msg.content.get_update_request();
    let (s_prime, resp) = handle_update_request(installed_types, req, s);
    (s_prime, form_update_resp_msg(msg, resp))
}

pub open spec fn handle_update_status_request_msg(installed_types: InstalledTypes, msg: Message, s: APIServerState) -> (APIServerState, Message)
    recommends
        msg.content.is_update_status_request(),
{
    let req = msg.content.get_update_status_request();
    let (s_prime, resp) = handle_update_status_request(installed_types, req, s);
    (s_prime, form_update_status_resp_msg(msg, resp))
}

// get_then_delete performs transactional operations by first getting the object, and then apply an delete when some
// condition holds. A get_then_delete request will never fail due to conflicting operations from other controllers.
//
// Note that get_then_delete is not provided by etcd. It can be implemented by retrying the delete upon conflict errors.
// The retry's termination depends on fairness assumption.
pub open spec fn handle_get_then_delete_request_msg(msg: Message, s: APIServerState) -> (APIServerState, Message)
    recommends
        msg.content.is_get_then_delete_request(),
{
    let req = msg.content.get_get_then_delete_request();
    if !req.well_formed() { // must have a controller reference
        (s, form_get_then_delete_resp_msg(msg, GetThenDeleteResponse {res: Err(APIError::BadRequest)}))
    } else {
        // Step 1: get the object
        let get_req = GetRequest {
            key: req.key
        };
        let get_resp = handle_get_request(get_req, s);
        match get_resp.res {
            Ok(_) => {
                let current_obj = s.resources[req.key()];
                // Step 2: if the object exists, perform a check using a predicate on object
                // The predicate: Is the current object owned by req.owner_ref?
                // TODO: the predicate should be provided by clients instead of the hardcoded one
                if current_obj.metadata.owner_references_contains(req.owner_ref) {
                    // Step 3: if the check passes, delete the object
                    let delete_req = DeleteRequest {
                        key: req.key,
                        preconditions: None,
                    };
                    let (s_prime, delete_resp) = handle_delete_request(delete_req, s);
                    (s_prime, form_get_then_delete_resp_msg(msg, GetThenDeleteResponse {res: delete_resp.res}))
                } else {
                    (s, form_get_then_delete_resp_msg(msg, GetThenDeleteResponse {res: Err(APIError::TransactionAbort)}))
                }
            }
            Err(err) => (s, form_get_then_delete_resp_msg(msg, GetThenDeleteResponse {res: Err(err)}))
        }
    }
}

// get_then_update performs transactional operations by first getting the object, and then apply an update when some
// condition holds. A get_then_update request will never fail due to conflicting operations from other controllers.
//
// Note that get_then_update is not provided by etcd. It can be implemented by retrying the update upon conflict errors.
// The retry's termination depends on fairness assumption.
pub open spec fn handle_get_then_update_request_msg(installed_types: InstalledTypes, msg: Message, s: APIServerState) -> (APIServerState, Message)
    recommends
        msg.content.is_get_then_update_request(),
{
    let req = msg.content.get_get_then_update_request();
    if !req.well_formed() { // must have a controller reference
        (s, form_get_then_update_resp_msg(msg, GetThenUpdateResponse {res: Err(APIError::BadRequest)}))
    } else {
        // Step 1: get the object
        let get_req = GetRequest {
            key: req.key()
        };
        let get_resp = handle_get_request(get_req, s);
        match get_resp.res {
            Ok(_) => {
                let current_obj = s.resources[req.key()];
                // Step 2: if the object exists, perform a check using a predicate on object
                // The predicate: Is the current object owned by req.owner_ref?
                // TODO: the predicate should be provided by clients instead of the hardcoded one
                if current_obj.metadata.owner_references_contains(req.owner_ref) {
                    // Step 3: if the check passes, overwrite the object with the new one
                    // Note that resource_version and uid comes from the current object to avoid conflict error
                    let new_obj = DynamicObjectView {
                        metadata: ObjectMetaView {
                            resource_version: current_obj.metadata.resource_version,
                            uid: current_obj.metadata.uid,
                            ..req.obj.metadata
                        },
                        ..req.obj
                    };
                    let update_req = UpdateRequest {
                        name: req.name,
                        namespace: req.namespace,
                        obj: new_obj,
                    };
                    let (s_prime, update_resp) = handle_update_request(installed_types, update_req, s);
                    (s_prime, form_get_then_update_resp_msg(msg, GetThenUpdateResponse {res: update_resp.res}))
                } else {
                    (s, form_get_then_update_resp_msg(msg, GetThenUpdateResponse {res: Err(APIError::TransactionAbort)}))
                }
            }
            Err(err) => (s, form_get_then_update_resp_msg(msg, GetThenUpdateResponse {res: Err(err)}))
        }
    }
}

pub open spec fn transition_by_etcd(installed_types: InstalledTypes, msg: Message, s: APIServerState) -> (APIServerState, Message)
    recommends
        msg.content is APIRequest,
{
    match msg.content->APIRequest_0 {
        APIRequest::GetRequest(_) => handle_get_request_msg(msg, s),
        APIRequest::ListRequest(_) => handle_list_request_msg(msg, s),
        APIRequest::CreateRequest(_) => handle_create_request_msg(installed_types, msg, s),
        APIRequest::DeleteRequest(_) => handle_delete_request_msg(msg, s),
        APIRequest::UpdateRequest(_) => handle_update_request_msg(installed_types, msg, s),
        APIRequest::UpdateStatusRequest(_) => handle_update_status_request_msg(installed_types, msg, s),
        APIRequest::GetThenDeleteRequest(_) => handle_get_then_delete_request_msg(msg, s),
        APIRequest::GetThenUpdateRequest(_) => handle_get_then_update_request_msg(installed_types, msg, s),
    }
}

pub open spec fn handle_request(installed_types: InstalledTypes) -> APIServerAction {
    Action {
        precondition: |input: APIServerActionInput, s: APIServerState| {
            &&& input.recv is Some
            &&& input.recv->0.content is APIRequest
        },
        transition: |input: APIServerActionInput, s: APIServerState| {
            let (s_prime, etcd_resp) = transition_by_etcd(installed_types, input.recv->0, s);
            (s_prime, APIServerActionOutput {
                send: Multiset::singleton(etcd_resp)
            })
        },
    }
}

pub open spec fn api_server(installed_types: InstalledTypes) -> APIServerStateMachine {
    StateMachine {
        init: |s: APIServerState| {
            s.resources == Map::<ObjectRef, DynamicObjectView>::empty()
        },
        actions: set![handle_request(installed_types)],
        step_to_action: |step: APIServerStep| {
            match step {
                APIServerStep::HandleRequest => handle_request(installed_types),
            }
        },
        action_input: |step: APIServerStep, input: APIServerActionInput| {
            input
        }
    }
}

}
