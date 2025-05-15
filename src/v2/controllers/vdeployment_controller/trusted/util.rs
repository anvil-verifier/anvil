use crate::kubernetes_api_objects::spec::{
    prelude::*,
    pod_template_spec::PodTemplateSpecView,
    label_selector::LabelSelectorView,
};
use crate::vreplicaset_controller::trusted::spec_types::*;
use crate::vdeployment_controller::trusted::spec_types::*;
use crate::vstd_ext::string_view::*;
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

pub open spec fn filter_old_and_new_vrs(vrs_list: Seq<VReplicaSetView>, vd: VDeploymentView) -> (res: (Seq<VReplicaSetView>, Seq<VReplicaSetView>))
// we don't consider there is more than one new vrs controlled by vd, check discussion/kubernetes-model/deployment_controller.md for details
{
    // even if we know vrs controlled by vd should have spec.template.metadata.is_Some() because we add the pot-template-hash label
    // we still need to check it here and pretend we don't know it

    let new_spec_filter = |vrs: VReplicaSetView|
        match_template_without_hash(vd, vrs);
    let old_spec_filter = |vrs: VReplicaSetView|
        !new_spec_filter(vrs)
        && (vrs.spec.replicas.is_None() || vrs.spec.replicas.unwrap() > 0);
    let new_vrs_list = vrs_list.filter(new_spec_filter);
    let old_vrs_list = vrs_list.filter(old_spec_filter);
    (new_vrs_list, old_vrs_list)
}

// See https://github.com/kubernetes/kubernetes/blob/cdc807a9e849b651fb48c962cc18e25d39ec5edf/pkg/controller/deployment/sync.go#L196-L210
// pod template hash is used to prevent old and new vrs from owning the same pod
// here we use resource_version of vd as a hash
//
// TODO: now we scale up the new vrs' replicas at once,
// we may consider existing pods in old vrs later to satisfy maxSurge
pub open spec fn make_replica_set(vd: VDeploymentView) -> (vrs: VReplicaSetView)
{
    let pod_template_hash = int_to_string_view(vd.metadata.resource_version.unwrap());
    let match_labels = vd.spec.template.metadata.unwrap().labels.unwrap().insert("pod-template-hash"@, pod_template_hash);
    VReplicaSetView {
        metadata: ObjectMetaView {
            name: Some(vd.metadata.name.unwrap() + "-"@ + pod_template_hash),
            namespace: vd.metadata.namespace,
            labels: vd.metadata.labels,
            owner_references: Some(make_owner_references(vd)),
            ..ObjectMetaView::default()
        }.add_label("pod-template-hash"@, pod_template_hash),
        spec: VReplicaSetSpecView {
            replicas: vd.spec.replicas,
            selector: LabelSelectorView {
                match_labels: Some(match_labels),
            },
            template: Some(template_with_hash(vd, pod_template_hash))
        },
        ..VReplicaSetView::default()
    }
}

pub open spec fn template_with_hash(vd: VDeploymentView, hash: StringView) -> PodTemplateSpecView
{
    PodTemplateSpecView {
        metadata: Some(ObjectMetaView {
            labels: Some(vd.spec.template.metadata.unwrap().labels.unwrap().insert("pod-template-hash"@, hash)),
            ..ObjectMetaView::default()
        }),
        spec: Some(vd.spec.template.spec.unwrap()),
        ..PodTemplateSpecView::default()
    }
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

pub open spec fn make_owner_references(vd: VDeploymentView) -> Seq<OwnerReferenceView> {
    seq![vd.controller_owner_ref()]
}

}