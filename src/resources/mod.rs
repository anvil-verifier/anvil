pub mod string_map;

use crate::pervasive::prelude::*;
use crate::pervasive::string::*;

// use k8s_openapi::api::core::v1::ConfigMap as K8SConfigMap;
use k8s_openapi::apimachinery::pkg::apis::meta::v1::ObjectMeta as K8SObjectMeta;

verus! {

#[verifier(external_body)]
pub struct ObjectMeta {
    inner: K8SObjectMeta,
}

pub struct ObjectMetaView {
    pub name: Option<Seq<char>>,
}

impl ObjectMeta {
    pub spec fn view(&self) -> ObjectMetaView;

    #[verifier(external_body)]
    pub fn name(&self) -> (name: Option<String>)
        ensures
            self@.name.is_Some() == name.is_Some(),
            name.is_Some() ==> name.get_Some_0()@ == self@.name.get_Some_0(),
    {
        todo!()
    }
}

}
