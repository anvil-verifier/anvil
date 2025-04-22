/*
open spec fn state_validation(self) -> bool {
    // serviceName is required and must not be empty
    &&& self.spec.service_name.is_Some()
    &&& self.spec.service_name.get_Some_0().len() > 0

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

    // podManagementPolicy must be either OrderedReady or Parallel
    &&& self.spec.pod_management_policy.is_Some() ==>
    self.spec.pod_management_policy.get_Some_0() == "OrderedReady"@
    || self.spec.pod_management_policy.get_Some_0() == "Parallel"@

    // revisionHistoryLimit must be non‑negative if present
    &&& self.spec.revision_history_limit.is_Some() ==>
    self.spec.revision_history_limit.get_Some_0() >= 0

    // volumeClaimTemplates
    // TODO: this object is too big, assume state_validation() is implemented for PersistentVolumeClaimSpec for now
    &&& self.spec.volume_claim_templates.is_Some() ==>
    self.spec.volume_claim_templates.state_validation()

    // minReadySeconds must be non‑negative if present
    &&& self.spec.min_ready_seconds.is_Some() ==>
    self.spec.min_ready_seconds.get_Some_0() >= 0

    // persistentVolumeClaimRetentionPolicy.whenDeleted/whenScaled must be Delete or Retain
    &&& self.spec.persistent_volume_claim_retention_policy.is_Some() ==>
    self.spec.persistent_volume_claim_retention_policy.get_Some_0().when_deleted == "Delete"@
    || self.spec.persistent_volume_claim_retention_policy.get_Some_0().when_deleted == "Retain"@
    &&& self.spec.persistent_volume_claim_retention_policy.get_Some_0().when_scaled  == "Delete"@
    || self.spec.persistent_volume_claim_retention_policy.get_Some_0().when_scaled  == "Retain"@

    // ordinals.start must be non‑negative if ordinals is provided
    &&& self.spec.ordinals.is_Some() ==>
    self.spec.ordinals.get_Some_0().start >= 0
}
*/
