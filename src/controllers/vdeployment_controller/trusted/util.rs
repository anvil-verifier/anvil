use crate::kubernetes_api_objects::spec::{
    prelude::*,
    pod_template_spec::PodTemplateSpecView,
    label_selector::LabelSelectorView,
};
use crate::vreplicaset_controller::trusted::spec_types::*;
use crate::vdeployment_controller::trusted::{spec_types::*, liveness_theorem::*};
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

pub open spec fn valid_owned_vrs(vrs: VReplicaSetView, vd: VDeploymentView) -> bool {
    // weaker version of well_formed, only need the key to be in etcd
    // and corresponding objects can pass the filter
    &&& vrs.metadata.name is Some
    &&& vrs.metadata.namespace == vd.metadata.namespace
    &&& vrs.metadata.deletion_timestamp is None
    &&& vrs.metadata.owner_references_contains(vd.controller_owner_ref())
    &&& vrs.state_validation()
}

pub open spec fn filter_old_and_new_vrs(vd: VDeploymentView, vrs_list: Seq<VReplicaSetView>) -> (res: (Option<VReplicaSetView>, Seq<VReplicaSetView>))
{
    // first vrs that match template and has non-zero replicas
    // non-zero replicas ensures the stability of esr
    let new_vrs_list = vrs_list.filter(|vrs: VReplicaSetView| {
        &&& match_template_without_hash(vd.spec.template, vrs)
        &&& vrs.spec.replicas is None || vrs.spec.replicas.unwrap() > 0
    });
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

pub open spec fn match_template_without_hash(template: PodTemplateSpecView, vrs: VReplicaSetView) -> bool {
    let vrs_template = vrs.spec.template.unwrap();
    template == PodTemplateSpecView {
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

// hacky workaround for type conversion bug: error[E0605]: non-primitive cast: `{integer}` as `builtin::nat`
#[macro_export]
macro_rules! nat0 {
    () => {
        spec_literal_nat("0")
    };
}

#[macro_export]
macro_rules! nat1 {
    () => {
        spec_literal_nat("1")
    };
}

#[macro_export]
macro_rules! int0 {
    () => {
        spec_literal_int("0")
    };
}

#[macro_export]
macro_rules! int1 {
    () => {
        spec_literal_int("1")
    };
}

pub use nat0;
pub use nat1;
pub use int0;
pub use int1;

}