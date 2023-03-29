// Copyright 2022 VMware, Inc.
// SPDX-License-Identifier: MIT
#![allow(unused_imports)]
use crate::pervasive::prelude::*;
use builtin::*;
use builtin_macros::*;

verus! {

pub struct ChannelManager {
    pub cur_chan_id: nat,
}

impl ChannelManager {
    pub open spec fn init() -> Self {
        ChannelManager {
            cur_chan_id: 0,
        }
    }

    pub open spec fn allocate(self) -> (Self, nat) {
        (ChannelManager {
            cur_chan_id: self.cur_chan_id + 1,
        }, self.cur_chan_id)
    }
}

}
