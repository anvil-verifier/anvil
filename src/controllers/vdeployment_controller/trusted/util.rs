use crate::kubernetes_api_objects::spec::{
    prelude::*,
    pod_template_spec::PodTemplateSpecView,
    label_selector::LabelSelectorView,
};
use crate::vreplicaset_controller::trusted::spec_types::*;
use crate::vdeployment_controller::trusted::spec_types::*;
use vstd::prelude::*;

verus! {

// some util spec functions are moved here from model::reconciler
// so we can share them with high-level specs and proofs for VD
pub open spec fn objects_to_vrs_list(objs: Seq<DynamicObjectView>) -> (vrs_list: Option<Seq<VReplicaSetView>>) {
    if objs.filter(|o: DynamicObjectView| VReplicaSetView::unmarshal(o).is_err()).len() != 0 {
        None
    } else {
        Some(objs.map_values(|o: DynamicObjectView| VReplicaSetView::unmarshal(o).unwrap()))
    }
}

pub open spec fn filter_vrs_list(vd: VDeploymentView, vrs_list: Seq<VReplicaSetView>) -> (filtered_vrs_list: Seq<VReplicaSetView>) {
    vrs_list.filter(|vrs: VReplicaSetView|
        vrs.metadata.owner_references_contains(vd.controller_owner_ref())
        && vrs.metadata.deletion_timestamp.is_None()
        && vrs.well_formed())
}

pub open spec fn filter_old_and_new_vrs(vd: VDeploymentView, vrs_list: Seq<VReplicaSetView>) -> (res: (Option<VReplicaSetView>, Seq<VReplicaSetView>))
{
    let new_vrs_list = vrs_list.filter(|vrs: VReplicaSetView| match_template_without_hash(vd, vrs));
    let new_vrs = if new_vrs_list.len() == 0 {
        None
    } else {
        Some(new_vrs_list.first())
    };
    let old_vrs_list = vrs_list.filter(|vrs: VReplicaSetView| {
        &&& new_vrs.is_None() || vrs.metadata.uid != new_vrs.get_Some_0().metadata.uid
        &&& vrs.spec.replicas.is_None() || vrs.spec.replicas.unwrap() > 0
    });
    (new_vrs, old_vrs_list)
}

pub open spec fn match_template_without_hash(vd: VDeploymentView, vrs: VReplicaSetView) -> bool {
    let vrs_template = vrs.spec.template.unwrap();
    vd.spec.template == PodTemplateSpecView {
        metadata: Some(ObjectMetaView {
            labels: Some(vrs_template.metadata.unwrap().labels.unwrap().remove("pod-template-hash"@)),
            ..vrs_template.metadata.unwrap()
        }),
        ..vrs_template
    }
}

}