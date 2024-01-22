use crate::executable_model::{object_map::ObjectMap, object_ref_set::ObjectRefSet};
use crate::kubernetes_api_objects::exec::dynamic::DynamicObject;
use crate::kubernetes_api_objects::spec::{
    common::{Kind, ObjectRef},
    dynamic::{DynamicObjectView, StoredState},
};
use crate::kubernetes_cluster::spec::api_server::types as model_types;
use vstd::prelude::*;
use vstd::string::*;

verus! {

pub struct ApiServerState {
    pub resources: ObjectMap,
    pub uid_counter: i64,
    pub resource_version_counter: i64,
    pub stable_resources: ObjectRefSet,
}

impl View for ApiServerState {
    type V = model_types::KubernetesAPIState;
    open spec fn view(&self) -> model_types::KubernetesAPIState {
        model_types::KubernetesAPIState {
            resources: self.resources@,
            uid_counter: self.uid_counter as int,
            resource_version_counter: self.resource_version_counter as int,
            stable_resources: self.stable_resources@,
        }
    }
}

}
