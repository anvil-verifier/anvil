use crate::kubernetes_api_objects::spec::{
    prelude::*,
    pod_template_spec::PodTemplateSpecView,
    label_selector::LabelSelectorView,
};
use crate::vreplicaset_controller::trusted::spec_types::*;
use crate::vdeployment_controller::trusted::spec_types::*;
use vstd::prelude::*;

verus! {

pub open spec fn objects_to_vrs_list(objs: Seq<DynamicObjectView>) -> (vrs_list: Option<Seq<VReplicaSetView>>) {
    if objs.filter(|o: DynamicObjectView| VReplicaSetView::unmarshal(o).is_err()).len() != 0 {
        None
    } else {
        Some(objs.map_values(|o: DynamicObjectView| VReplicaSetView::unmarshal(o).unwrap()))
    }
}

pub open spec fn filter_vrs_list(vrs_list: Seq<VReplicaSetView>, vd: VDeploymentView) -> (filtered_vrs_list: Seq<VReplicaSetView>) {
    vrs_list.filter(|vrs: VReplicaSetView|
        vrs.metadata.owner_references_contains(vd.controller_owner_ref())
        && vrs.metadata.deletion_timestamp.is_None()
        && vrs.well_formed())
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