use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    controller::types::*,
    cluster::*, 
    message::*,
    api_server::{state_machine::*, types::*},
};
use crate::temporal_logic::{defs::*, rules::*};
use crate::vstatefulset_controller::{
    model::{install::*, reconciler::*},
    proof::predicate::*,
    trusted::{rely_guarantee::*, spec_types::*, liveness_theorem::*, step::VStatefulSetReconcileStepView::*},
};
use crate::vstd_ext::{map_lib::*, seq_lib::*, set_lib::*, string_view::*};
use vstd::{seq_lib::*, map_lib::*, set_lib::*};
use vstd::prelude::*;

verus! {

// TODO: move to cluster lemma
pub proof fn lemma_update_status_req_at_most_updates_rv(
    s: APIServerState, s_prime: APIServerState, msg: Message, installed_types: InstalledTypes
)
requires
    s_prime == transition_by_etcd(installed_types, msg, s).0,
    msg.content.is_update_status_request(),
ensures
    ({
        let key = msg.content.get_update_status_request().key();
        &&& s.resources.contains_key(key) ==> {
            &&& s_prime.resources.contains_key(key)
            &&& s.resources[key].metadata.without_resource_version() == s_prime.resources[key].metadata.without_resource_version()
            &&& s.resources[key].kind == s_prime.resources[key].kind
            &&& s.resources[key].spec == s_prime.resources[key].spec
        }
    })
{
    
}

}