use crate::vstatefulset_controller::{
    trusted::{spec_types::*, step::*},
    model::{reconciler::VStatefulSetReconcileState, install::*}
};
use crate::kubernetes_cluster::spec::controller::types::*;
use crate::kubernetes_api_objects::spec::resource::*;
use vstd::prelude::*;

verus! {

// just to make Verus happy
pub uninterp spec fn dummy<T>(t: T) -> bool;

}