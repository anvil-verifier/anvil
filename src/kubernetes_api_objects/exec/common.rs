// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
use crate::kubernetes_api_objects::spec::common::*;
use crate::vstd_ext::string_view::*;
use vstd::{prelude::*, string::*};

// verus! {

// pub struct KubeObjectRef {
//     pub kind: Kind,
//     pub name: String,
//     pub namespace: String,
// }

// impl View for KubeObjectRef {
//     type V = ObjectRef;
//     open spec fn view(&self) -> ObjectRef {
//         ObjectRef {
//             kind: self.kind,
//             name: self.name@,
//             namespace: self.namespace@,
//         }
//     }
// }

// }

// impl Copy for KubeObjectRef {}

// impl Clone for KubeObjectRef {
//     fn clone(&self) -> Self {
//         KubeObjectRef {
//             kind: self.kind.clone(),
//             name: self.name.clone(),
//             namespace: self.namespace.clone(),
//         }
//     }
// }
