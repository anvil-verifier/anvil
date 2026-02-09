use crate::kubernetes_api_objects::exec::{
    api_resource::*, label_selector::*, persistent_volume_claim::*, pod_template_spec::*,
    prelude::*, resource::*,
};
use crate::kubernetes_api_objects::spec::{
    persistent_volume_claim::*, resource::*, volume_resource_requirements::*,
};
use crate::vstatefulset_controller::trusted::exec_types::{VStatefulSet, StatefulSetOrdinalLabel, StatefulSetPodNameLabel};
use crate::vstatefulset_controller::trusted::spec_types;
use crate::vstd_ext::{string_map::*, string_view::*};
use vstd::prelude::*;

verus! {

impl VStatefulSet {
    pub fn state_validation(&self) -> (res: bool)
        ensures res == self@.state_validation()
    {
        // replicas
        if let Some(replicas) = self.spec().replicas() {
            // non-negative
            if replicas < 0 {
                return false;
            }
        }

        // updateStrategy
        if let Some(update_strategy) = self.spec().update_strategy() {
            if let Some(update_strategy_type) = update_strategy.type_() {
                // update_strategy is either "Recreate" or "RollingUpdate"
                if string_equal(&update_strategy_type, "RollingUpdate") {
                    if let Some(rolling_update) = update_strategy.rolling_update() {
                        if let Some(partition) = rolling_update.partition() {
                            // partition should be non-negative
                            if partition < 0 {
                                return false;
                            }
                        }
                        if let Some(max_unavailable) = rolling_update.max_unavailable() {
                            // max_unavailable should be positive
                            if max_unavailable <= 0 {
                                return false;
                            }
                        }
                    }
                }
                else if string_equal(&update_strategy_type, "OnDelete") {
                    // RollingUpdate block should not exist
                    if update_strategy.rolling_update().is_some() {
                        return false;
                    }
                }
                else {
                    return false;
                }
            }
        }

        // podManagementPolicy
        if let Some(pod_management_policy) = self.spec().pod_management_policy() {
            // should be either "OrderedReady" or "Parallel"
            if !string_equal(&pod_management_policy, "OrderedReady") && !string_equal(&pod_management_policy, "Parallel") {
                return false;
            }
        }

        // volumeClaimTemplates
        if let Some(vct) = self.spec().volume_claim_templates() {
            let mut idx: usize = 0;
            let ghost mut vct_view: Seq<PersistentVolumeClaimView> = Seq::new(vct.len() as nat,|i: int| vct[i]@);
            assert(vct@.map_values(|pvc: PersistentVolumeClaim| pvc@) == vct_view);
            for idx in 0..vct.len()
                invariant
                    0 <= idx <= vct.len(),
                    forall |i: int|  #![trigger vct[i]] 0 <= i < idx ==> vct[i]@.state_validation() && vct[i]@.metadata.well_formed_for_namespaced() && dash_free(vct[i]@.metadata.name->0),
                    vct@.map_values(|pvc: PersistentVolumeClaim| pvc@) == vct_view,
                    self@.spec.volume_claim_templates is Some,
                    vct_view == self@.spec.volume_claim_templates->0,
            {
                let pvc_sv = vct[idx].spec().is_some();
                let pvc_metadata_sv = vct[idx].metadata().well_formed_for_namespaced();
                
                assert(pvc_sv == vct_view[idx as int].state_validation());
                assert(pvc_metadata_sv == vct_view[idx as int].metadata.well_formed_for_namespaced());
                
                if !pvc_sv || !pvc_metadata_sv {
                    return false;
                }
                let dash_check = dash_free_exec(&vct[idx].metadata().name().unwrap());
                assert(dash_check == dash_free(vct_view[idx as int].metadata.name->0));

                if !dash_check {
                    return false;
                }
            }
        }

        // minReadySeconds
        if let Some(min_ready_seconds) = self.spec().min_ready_seconds() {
            // cannot be negative
            if min_ready_seconds < 0 {
                return false;
            }
        }

        // persistentVolumeClaimRetentionPolicy
        if let Some(persistent_volume_claim_retention_policy) = self.spec().persistent_volume_claim_retention_policy() {
            // when_deleted and when_scaled should be either "Retain" or "Delete"
            if let Some(when_deleted) = persistent_volume_claim_retention_policy.when_deleted() {
                if !string_equal(&when_deleted, "Retain") && !string_equal(&when_deleted, "Delete") {
                    return false;
                }
            }
            if let Some(when_scaled) = persistent_volume_claim_retention_policy.when_scaled() {
                if !string_equal(&when_scaled, "Retain") && !string_equal(&when_scaled, "Delete") {
                    return false;
                }
            }
        }

        // ordinals
        if let Some(ordinals) = self.spec().ordinals() {
            // start should be non-negative
            if let Some(start) = ordinals.start() {
                if start < 0 {
                    return false;
                }
            }
        }

        // Check if selector's match_labels exist and are non-empty
        if let Some(match_labels) = self.spec().selector().match_labels() {
            if match_labels.len() <= 0 {
                return false;
            }
        } else {
            return false;
        }

        // template, metadata, and spec exist
        if self.spec().template().metadata().is_none() || self.spec().template().spec().is_none() {
            return false;
        }
        // Map::empty() did not compile
        if !self.spec().selector().matches(self.spec().template().metadata().unwrap().labels().unwrap_or(StringMap::empty())) {
            return false;
        }

        if let Some(labels) = self.spec().template().metadata().unwrap().labels() {
            if labels.contains_key(&StatefulSetPodNameLabel.to_string()) || labels.contains_key(&StatefulSetOrdinalLabel.to_string()) {
                return false;
            }
        }

        true
    }
}

}
