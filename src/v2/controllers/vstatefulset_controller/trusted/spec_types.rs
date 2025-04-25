/*
open spec fn state_validation(self) -> bool {
    // selector exists, and its match_labels is not empty
    // TODO: revise it after supporting selector.match_expressions
    &&& self.spec.selector.match_labels.is_Some()
    &&& self.spec.selector.match_labels.get_Some_0().len() > 0
    // template and its metadata and spec exists
    &&& self.spec.template.is_Some()
    &&& self.spec.template.get_Some_0().metadata.is_Some()
    &&& self.spec.template.get_Some_0().spec.is_Some()
    // selector matches template's metadata's labels
    &&& self.spec.selector.matches(self.spec.template.get_Some_0().metadata.get_Some_0().labels.unwrap_or(Map::empty()))

    // replicas is non‑negative
    &&& self.spec.replicas.is_Some() ==>
    self.spec.replicas.get_Some_0() >= 0

    &&& self.spec.update_strategy.is_Some() ==> (
        // updateStrategy.type must be either RollingUpdate or OnDelete (used "type_" to avoid clashing with Rust keyword)
        self.spec.update_strategy.get_Some_0().type_.is_Some() ==>
        match self.spec.update_strategy.get_Some_0().type_.get_Some_0() {
            "RollingUpdate"@ => self.spec.update_strategy.get_Some_0().rolling_update.is_Some() ==> (
                                    // updateStrategy.rollingUpdate.partition is non-negative
                                    self.spec.update_strategy.get_Some_0().rolling_update.get_Some_0().partition.is_Some() ==>
                                    self.spec.update_strategy.get_Some_0().rolling_update.get_Some_0().partition.get_Some_0() >= 0
                                    // if updateStrategy.rollingUpdate.maxUnavailable is present, validate it's positive (assuming its an integer for now)
                                    &&& self.spec.update_strategy.get_Some_0().rolling_update.get_Some_0().max_unavailable.is_Some() ==>
                                    self.spec.update_strategy.get_Some_0().rolling_update.get_Some_0().max_unavailable.get_Some_0() > 0
                                )
            // updateStrategy.rollingUpdate is None if updateStrategy.type is OnDelete
            "OnDelete"@ => self.spec.update_strategy.get_Some_0().rolling_update.is_None(),
            _ => false
        }
    )

    // podManagementPolicy must be either OrderedReady or Parallel
    &&& self.spec.pod_management_policy.is_Some() ==>
    self.spec.pod_management_policy.get_Some_0() == "OrderedReady"@
    || self.spec.pod_management_policy.get_Some_0() == "Parallel"@


    // volumeClaimTemplates
    // TODO: this object is too big, assume state_validation() is implemented for PersistentVolumeClaimSpec for now
    // TODO: volumeClaimTemplates is actually a list
    &&& self.spec.volume_claim_templates.is_Some() ==>
    self.spec.volume_claim_templates.get_Some_0().state_validation()

    // minReadySeconds must be non‑negative if present
    &&& self.spec.min_ready_seconds.is_Some() ==>
    self.spec.min_ready_seconds.get_Some_0() >= 0

    // persistentVolumeClaimRetentionPolicy.whenDeleted/whenScaled must be Delete or Retain
    &&& self.spec.persistent_volume_claim_retention_policy.is_Some() ==> (
        self.spec.persistent_volume_claim_retention_policy.get_Some_0().when_deleted.is_Some() ==> (
            self.spec.persistent_volume_claim_retention_policy.get_Some_0().when_deleted.get_Some_0() == "Delete"@
            || self.spec.persistent_volume_claim_retention_policy.get_Some_0().when_deleted.get_Some_0() == "Retain"@
        )
        self.spec.persistent_volume_claim_retention_policy.get_Some_0().when_scaled.is_Some() ==> (
            self.spec.persistent_volume_claim_retention_policy.get_Some_0().when_scaled.get_Some_0() == "Delete"@
            || self.spec.persistent_volume_claim_retention_policy.get_Some_0().when_scaled.get_Some_0() == "Retain"@
        )
    )

    // ordinals.start must be non‑negative if ordinals is provided
    &&& self.spec.ordinals.is_Some() ==> (
        self.spec.ordinals.get_Some_0().start.is_Some() ==>
        self.spec.ordinals.get_Some_0().start.get_Some_0() >= 0
    )
}
*/
