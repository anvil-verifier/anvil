open spec fn state_validation(self) -> bool {
    // replicas is non‑negative
    &&& self.spec.replicas.is_Some() ==>
        self.spec.replicas.get_Some_0() >= 0

    // minReadySeconds must be non‑negative if present
    &&& self.spec.min_ready_seconds.is_Some() ==>
        self.spec.min_ready_seconds.get_Some_0() >= 0

    // revisionHistoryLimit must be non‑negative if present
    &&& self.spec.revision_history_limit.is_Some() ==>
        self.spec.revision_history_limit.get_Some_0() >= 0

    // ordinals.start must be non‑negative if ordinals is provided
    &&& self.spec.ordinals.is_Some() ==>
        self.spec.ordinals.get_Some_0().start >= 0

    // ordinals.start must be less than replicas when both present
    &&& self.spec.ordinals.is_Some() && self.spec.replicas.is_Some() ==>
        self.spec.ordinals.get_Some_0().start < self.spec.replicas.get_Some_0()

    // podManagementPolicy must be either OrderedReady or Parallel
    &&& self.spec.pod_management_policy.is_Some() ==>
        ( self.spec.pod_management_policy.get_Some_0() == PodManagementPolicy::OrderedReady
        || self.spec.pod_management_policy.get_Some_0() == PodManagementPolicy::Parallel )

    // persistentVolumeClaimRetentionPolicy.whenDeleted/whenScaled must be Delete or Retain
    &&& self.spec.persistent_volume_claim_retention_policy.is_Some() ==>
        let pvc = self.spec.persistent_volume_claim_retention_policy.get_Some_0();
        ( pvc.when_deleted == "Delete" || pvc.when_deleted == "Retain" )
     && ( pvc.when_scaled  == "Delete" || pvc.when_scaled  == "Retain" )

    // selector must exist
    &&& self.spec.selector.is_Some()

    // if match_labels is provided, it must be non‑empty
    &&& self.spec.selector.get_Some_0().match_labels.is_Some() ==>
        self.spec.selector.get_Some_0().match_labels.get_Some_0().len() > 0

    // serviceName is required and must not be empty
    &&& self.spec.service_name.is_Some()
    &&& self.spec.service_name.get_Some_0().len() > 0

    // template, template.metadata and template.spec must all exist
    &&& self.spec.template.is_Some()
    &&& self.spec.template.get_Some_0().metadata.is_Some()
    &&& self.spec.template.get_Some_0().spec.is_Some()

    // selector.match_labels must match template.metadata.labels
    &&& self.spec.selector.get_Some_0().matches(
            self.spec.template.get_Some_0()
                .metadata.get_Some_0()
                .labels.unwrap_or(Map::empty())
        )

    // if ownerReferences provided, each must include apiVersion, kind, name, and uid
    &&& self.spec.template.get_Some_0().metadata.get_Some_0().owner_references.is_Some() ==>
        forall r in self.spec.template.get_Some_0().metadata.get_Some_0().owner_references.get_Some_0() :: (
            r.api_version.is_Some()
         && r.kind.is_Some()
         && r.name.is_Some()
         && r.uid.is_Some()
        )

    // deletionGracePeriodSeconds in metadata must be non‑negative if present
    &&& self.spec.template.get_Some_0().metadata.get_Some_0().deletion_grace_period_seconds.is_Some() ==>
        self.spec.template.get_Some_0()
            .metadata.get_Some_0()
            .deletion_grace_period_seconds
            .get_Some_0() >= 0

    // managedFields entries must be complete when provided
    &&& self.spec.template.get_Some_0().metadata.get_Some_0().managed_fields.is_Some() ==>
        forall mf in self.spec.template.get_Some_0().metadata.get_Some_0().managed_fields.get_Some_0() :: (
            mf.api_version.is_Some()
         && mf.fields_type.is_Some()
         && mf.fields_v1.is_Some()
         && mf.manager.is_Some()
         && mf.operation.is_Some()
         && mf.time.is_Some()
        )
}