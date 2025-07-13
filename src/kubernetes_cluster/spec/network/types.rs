use crate::kubernetes_cluster::spec::message::*;
use vstd::{multiset::*, prelude::*};

verus! {

pub struct NetworkState {
    pub in_flight: Multiset<Message>,
}

}
