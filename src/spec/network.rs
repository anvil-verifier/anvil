// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT

#[allow(unused_imports)]
use builtin_macros::*;
#[allow(unused_imports)]
use builtin::{exists, requires, ensures, equal};
#[allow(unused_imports)]
use crate::common::*;
#[allow(unused_imports)]
use crate::pervasive::{*, option::Option, set::*};
#[allow(unused_imports)]
use crate::apis::*;

verus! {
pub struct NetworkConstants {
    // Do we need any constant here?
}

pub struct NetworkVariables {
    pub sent_messages: Set<Packet>,
}

pub open spec fn init(c: NetworkConstants, v: NetworkVariables) -> bool {
    equal(v.sent_messages, Set::empty())
}

pub open spec fn next(c: NetworkConstants, v: NetworkVariables, v_prime: NetworkVariables, network_ops: NetworkOps) -> bool {
    true
    && match network_ops.recv {
        Option::Some(message_to_recv) => v.sent_messages.contains(message_to_recv),
        Option::None => true,
    }
    && match network_ops.send {
        Option::Some(message_to_send) => (v.sent_messages.insert(message_to_send) === v_prime.sent_messages),
        Option::None => (v.sent_messages === v_prime.sent_messages),
    }
}

}