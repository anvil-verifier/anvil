use crate::temporal_logic::{defs::*, rules::*};
use crate::kubernetes_api_objects::spec::prelude::*;
use crate::vdeployment_controller::{
    trusted::{rely_guarantee::*, step::*, spec_types::*},
    model::{install::*, reconciler::*},
    proof::*,
};
use crate::kubernetes_cluster::spec::{
    controller::types::*,
    cluster::*, 
    message::*
};
use crate::vdeployment_controller::{
    trusted::{step::*, spec_types::*, util::*,
        rely_guarantee::vd_rely, liveness_theorem::*},
    model::{install::*, reconciler::*},
};
use crate::vreplicaset_controller::trusted::spec_types::VReplicaSetView;
use crate::vdeployment_controller::trusted::step::VDeploymentReconcileStepView::*;
use vstd::prelude::*;

verus! {

// in addition to new_vrs_and_old_vrs_of_n_can_be_extracted_from_resp_objs
pub open spec fn resp_objs_with_new_vrs_status_matching_replicas_and_no_old_vrs(
    vd: VDeploymentView, controller_id: int, resp_msg: Message, nv_uid_key: Option<(Uid, ObjectRef)>
) -> StatePred<ClusterState> {
    |s: ClusterState| {
        let resp_objs = resp_msg.content.get_list_response().res.unwrap();
        let vrs_list = objects_to_vrs_list(resp_objs)->0;
        let managed_vrs_list = vrs_list.filter(|vrs| valid_owned_vrs(vrs, vd));
        &&& resp_msg_is_ok_list_resp_containing_matched_vrs(vd, resp_msg, s)
        &&& {
            let (new_vrs, old_vrs_list) = filter_old_and_new_vrs(vd, managed_vrs_list);
            &&& new_vrs is Some == nv_uid_key is Some
            &&& new_vrs is Some ==> {
                &&& new_vrs->0.metadata.uid is Some
                &&& new_vrs->0.metadata.uid->0 == (nv_uid_key->0).0
                &&& new_vrs->0.metadata.name is Some
                &&& new_vrs->0.metadata.namespace is Some
                &&& new_vrs->0.status is Some
                &&& new_vrs->0.status->0.replicas == get_replicas(new_vrs->0.spec.replicas)
                &&& new_vrs->0.object_ref() == (nv_uid_key->0).1
                &&& get_replicas(new_vrs->0.spec.replicas) == get_replicas(vd.spec.replicas)
            }
            &&& old_vrs_list.len() == 0
        }
    }
}

}