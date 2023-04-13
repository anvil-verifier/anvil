// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use vstd::prelude::*;
use builtin::*;
use builtin_macros::*;

verus! {

/// ChannelManager allocates new channel id for each request sent by the controller.
/// The response will carry the same channel id.

// TODO: the concept of channel should be modeled inside the network state machine
pub struct ChannelManager {
    pub cur_chan_id: nat,
}

impl ChannelManager {
    pub open spec fn init() -> Self {
        ChannelManager {
            cur_chan_id: 0,
        }
    }

    /// allocate returns cur_chan_id and another ChannelManager with an incremented cur_chan_id

    pub open spec fn allocate(self) -> (Self, nat) {
        (ChannelManager {
            cur_chan_id: self.cur_chan_id + 1,
        }, self.cur_chan_id)
    }
}

}
