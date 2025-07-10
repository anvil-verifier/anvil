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

pub open spec fn weakly_well_formed(vrs: VReplicaSetView, vd: VDeploymentView) -> bool {
    // weaker version of well_formed, only need the key to be in etcd
    // and corresponding objects can pass the filter
    &&& vrs.metadata.name is Some
    // if I include the namespace check, we will see
    // error: The verifier does not yet support the following Rust feature: ==/!= for non smt equality types
    //    --> src/controllers/vdeployment_controller/exec/reconciler.rs:419:12
    //     |
    // 419 |         && vrs.metadata().namespace().unwrap() == vd.metadata().namespace().unwrap() 
    // It's ok to go ahead without that because the namespace is ensured on API server side
    &&& vrs.metadata.owner_references_contains(vd.controller_owner_ref())
    &&& vrs.state_validation()
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
        &&& new_vrs is None || vrs.metadata.uid != new_vrs->0.metadata.uid
        &&& vrs.spec.replicas is None || vrs.spec.replicas.unwrap() > 0
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

pub open spec fn match_replicas(vd: VDeploymentView, vrs: VReplicaSetView) -> bool {
    vd.spec.replicas.unwrap_or(1) == vrs.spec.replicas.unwrap_or(1 as int)
}

}