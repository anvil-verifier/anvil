use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    api_server::state_machine::{
        handle_create_request_msg, handle_get_request_msg, handle_update_request_msg,
    },
    cluster::*,
    message::*,
};
use crate::temporal_logic::{defs::*, rules::*};
use vstd::prelude::*;

verus! {

impl Cluster {

pub open spec fn object_in_ok_get_response_has_smaller_rv_than_etcd() -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg: Message|
            s.in_flight().contains(msg)
            && #[trigger] is_ok_get_response_msg()(msg)
            ==> msg.content.get_get_response().res.get_Ok_0().metadata.resource_version.is_Some()
                && msg.content.get_get_response().res.get_Ok_0().metadata.resource_version.get_Some_0() < s.api_server.resource_version_counter
    }
}

// TODO: Investigate flaky proof.
#[verifier(rlimit(100))]
pub proof fn lemma_always_object_in_ok_get_response_has_smaller_rv_than_etcd(self, spec: TempPred<ClusterState>)
    requires
        spec.entails(lift_state(self.init())),
        spec.entails(always(lift_action(self.next()))),
    ensures spec.entails(always(lift_state(Self::object_in_ok_get_response_has_smaller_rv_than_etcd()))),
{
    let inv = Self::object_in_ok_get_response_has_smaller_rv_than_etcd();
    let next = |s, s_prime| {
        &&& self.next()(s, s_prime)
        &&& Self::each_object_in_etcd_is_weakly_well_formed()(s)
    };
    self.lemma_always_each_object_in_etcd_is_weakly_well_formed(spec);
    combine_spec_entails_always_n!(
        spec, lift_action(next), lift_action(self.next()),
        lift_state(Self::each_object_in_etcd_is_weakly_well_formed())
    );
    assert forall |s, s_prime| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        assert forall |msg| s_prime.in_flight().contains(msg) && #[trigger] is_ok_get_response_msg()(msg)
        implies
            msg.content.get_get_response().res.get_Ok_0().metadata.resource_version.is_Some()
            && msg.content.get_get_response().res.get_Ok_0().metadata.resource_version.get_Some_0() < s_prime.api_server.resource_version_counter
        by {
            let step = choose |step| self.next_step(s, s_prime, step);
            if s.in_flight().contains(msg) {
                assert(s.api_server.resource_version_counter <= s_prime.api_server.resource_version_counter);
            } else {
                let input = step.get_APIServerStep_0().get_Some_0();
                match input.content.get_APIRequest_0() {
                    APIRequest::GetRequest(req) => {
                        if is_ok_get_response_msg()(msg) {
                            let req_key = req.key;
                            assert(s.resources().contains_key(req_key));
                            assert(msg.content.get_get_response().res.get_Ok_0().metadata.resource_version.get_Some_0() == s.resources()[req_key].metadata.resource_version.get_Some_0());
                            assert(s.resources()[req_key].metadata.resource_version.get_Some_0() < s_prime.api_server.resource_version_counter);
                        } else {}
                    }
                    _ => {}
                }
            }
        }
    }
    init_invariant(spec, self.init(), next, inv);
}

pub open spec fn object_in_ok_get_resp_is_same_as_etcd_with_same_rv(key: ObjectRef) -> StatePred<ClusterState> {
    |s: ClusterState| {
        forall |msg|
            #[trigger] s.in_flight().contains(msg)
            && is_ok_get_response_msg_and_matches_key(key)(msg)
            && s.resources().contains_key(key)
            && s.resources()[key].metadata.resource_version.get_Some_0() == msg.content.get_get_response().res.get_Ok_0().metadata.resource_version.get_Some_0()
            ==> s.resources()[key] == msg.content.get_get_response().res.get_Ok_0()
    }
}

pub proof fn lemma_always_object_in_ok_get_resp_is_same_as_etcd_with_same_rv(self, spec: TempPred<ClusterState>, key: ObjectRef)
    requires
        spec.entails(lift_state(self.init())),
        spec.entails(always(lift_action(self.next()))),
    ensures spec.entails(always(lift_state(Self::object_in_ok_get_resp_is_same_as_etcd_with_same_rv(key)))),
{
    let inv = Self::object_in_ok_get_resp_is_same_as_etcd_with_same_rv(key);
    let next = |s, s_prime| {
        &&& self.next()(s, s_prime)
        &&& Self::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& Self::object_in_ok_get_response_has_smaller_rv_than_etcd()(s)
    };
    self.lemma_always_each_object_in_etcd_is_weakly_well_formed(spec);
    self.lemma_always_object_in_ok_get_response_has_smaller_rv_than_etcd(spec);
    combine_spec_entails_always_n!(
        spec, lift_action(next), lift_action(self.next()), lift_state(Self::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(Self::object_in_ok_get_response_has_smaller_rv_than_etcd())
    );
    assert forall |s, s_prime| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        assert forall |msg| #[trigger] s_prime.in_flight().contains(msg)
            && is_ok_get_response_msg_and_matches_key(key)(msg)
            && s_prime.resources().contains_key(key)
            && s_prime.resources()[key].metadata.resource_version.get_Some_0() == msg.content.get_get_response().res.get_Ok_0().metadata.resource_version.get_Some_0()
        implies s_prime.resources()[key] == msg.content.get_get_response().res.get_Ok_0() by {
            assert(is_ok_get_response_msg()(msg));
            if s.in_flight().contains(msg) {
                if !s.resources().contains_key(key) || s.resources()[key] != s_prime.resources()[key] {
                    assert(s_prime.resources()[key].metadata.resource_version.get_Some_0() != msg.content.get_get_response().res.get_Ok_0().metadata.resource_version.get_Some_0())
                }
            } else {
                let step = choose |step| self.next_step(s, s_prime, step);
                assert(step.is_APIServerStep());
                let req = step.get_APIServerStep_0().get_Some_0();
                match req.content.get_APIRequest_0() {
                    APIRequest::GetRequest(_) => {}
                    APIRequest::ListRequest(_) => {}
                    APIRequest::CreateRequest(_) => {}
                    APIRequest::DeleteRequest(_) => {}
                    APIRequest::UpdateRequest(_) => {}
                    APIRequest::UpdateStatusRequest(_) => {}
                    APIRequest::GetThenDeleteRequest(_) => {}
                    APIRequest::GetThenUpdateRequest(_) => {}
                }
                assert(msg == handle_get_request_msg(req, s.api_server).1);
                assert(s.resources().contains_key(req.content.get_get_request().key));
                assert(msg.content.get_get_response().res.get_Ok_0() == s.resources()[req.content.get_get_request().key]);
                assert(req.content.get_get_request().key == msg.content.get_get_response().res.get_Ok_0().object_ref());
                assert(s.api_server == s_prime.api_server);
                assert(s_prime.resources()[key] == msg.content.get_get_response().res.get_Ok_0());
            }
        }
    }
    init_invariant(spec, self.init(), next, inv);
}

pub open spec fn key_of_object_in_matched_ok_get_resp_message_is_same_as_key_of_pending_req(controller_id: int, key: ObjectRef) -> StatePred<ClusterState>
    recommends
        key.kind.is_CustomResourceKind(),
{
    |s: ClusterState| {
        forall |msg: Message|
            #[trigger] s.in_flight().contains(msg)
            && is_ok_get_response_msg()(msg)
            && s.ongoing_reconciles(controller_id).contains_key(key)
            && s.ongoing_reconciles(controller_id)[key].pending_req_msg.is_Some()
            && resp_msg_matches_req_msg(msg, s.ongoing_reconciles(controller_id)[key].pending_req_msg.get_Some_0())
            ==> is_ok_get_response_msg_and_matches_key(s.ongoing_reconciles(controller_id)[key].pending_req_msg.get_Some_0().content.get_get_request().key)(msg)
    }
}

pub proof fn lemma_always_key_of_object_in_matched_ok_get_resp_message_is_same_as_key_of_pending_req(self, spec: TempPred<ClusterState>, controller_id: int, key: ObjectRef)
    requires
        key.kind.is_CustomResourceKind(),
        spec.entails(lift_state(self.init())),
        spec.entails(always(lift_action(self.next()))),
        self.controller_models.contains_key(controller_id),
    ensures spec.entails(always(lift_state(Self::key_of_object_in_matched_ok_get_resp_message_is_same_as_key_of_pending_req(controller_id, key)))),
{
    let inv = Self::key_of_object_in_matched_ok_get_resp_message_is_same_as_key_of_pending_req(controller_id, key);
    let next = |s, s_prime| {
        &&& self.next()(s, s_prime)
        &&& Self::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& Self::every_in_flight_msg_has_lower_id_than_allocator()(s)
        &&& Self::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(controller_id, key)(s)
        &&& Self::every_in_flight_msg_has_unique_id()(s)
        &&& Self::there_is_the_controller_state(controller_id)(s)
    };
    self.lemma_always_each_object_in_etcd_is_weakly_well_formed(spec);
    self.lemma_always_every_in_flight_msg_has_lower_id_than_allocator(spec);
    self.lemma_always_every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(spec, controller_id, key);
    self.lemma_always_every_in_flight_msg_has_unique_id(spec);
    self.lemma_always_there_is_the_controller_state(spec, controller_id);
    combine_spec_entails_always_n!(
        spec, lift_action(next), lift_action(self.next()), lift_state(Self::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(Self::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(Self::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(controller_id, key)),
        lift_state(Self::every_in_flight_msg_has_unique_id()),
        lift_state(Self::there_is_the_controller_state(controller_id))
    );
    assert forall |s, s_prime| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        assert forall |msg| #[trigger] s_prime.in_flight().contains(msg)
            && is_ok_get_response_msg()(msg)
            && s_prime.ongoing_reconciles(controller_id).contains_key(key)
            && s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg.is_Some()
            && resp_msg_matches_req_msg(msg, s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg.get_Some_0())
        implies
            is_ok_get_response_msg_and_matches_key(s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg.get_Some_0().content.get_get_request().key)(msg)
        by {
            assert(s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg.get_Some_0().content.is_get_request());
            let req_key = s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg.get_Some_0().content.get_get_request().key;
            let step = choose |step| self.next_step(s, s_prime, step);
            match step {
                Step::ControllerStep(input) => {
                    assert(s.in_flight().contains(msg));
                    let input_controller_id = input.0;
                    let input_cr_key = input.2.get_Some_0();
                    if input_controller_id == controller_id && input_cr_key == key {
                        assert(false);
                    } else {
                        assert(s.ongoing_reconciles(controller_id)[key] == s_prime.ongoing_reconciles(controller_id)[key]);
                        assert(is_ok_get_response_msg_and_matches_key(req_key)(msg));
                    }
                },
                Step::APIServerStep(input) => {
                    assert(s.ongoing_reconciles(controller_id)[key] == s_prime.ongoing_reconciles(controller_id)[key]);
                    if !s.in_flight().contains(msg) {
                        assert(msg.content.is_get_response());
                        assert(msg == handle_get_request_msg(s.ongoing_reconciles(controller_id)[key].pending_req_msg.get_Some_0(), s.api_server).1);
                        assert(msg.src.is_APIServer() && msg.content.is_get_response());
                        if msg.content.get_get_response().res.is_Ok() {
                            assert(s.resources().contains_key(req_key));
                            assert(s.resources()[req_key].object_ref() == req_key);
                        }
                        assert(is_ok_get_response_msg_and_matches_key(req_key)(msg));
                    }
                },
                Step::DropReqStep(input) => {
                    assert(s.ongoing_reconciles(controller_id)[key] == s_prime.ongoing_reconciles(controller_id)[key]);
                    if !s.in_flight().contains(msg) {
                        assert(msg.src.is_APIServer());
                        assert(msg.content.is_get_response());
                        assert(msg.content.get_get_response().res.is_Err());
                    }
                    assert(is_ok_get_response_msg_and_matches_key(req_key)(msg));
                },
                Step::ExternalStep(input) => {
                    assert(input.1.get_Some_0() != msg);
                    assert(s.in_flight().contains(msg));
                },
                _ => {
                    assert(s.in_flight().contains(msg));
                    assert(is_ok_get_response_msg_and_matches_key(req_key)(msg));
                }
            }
        }
    }
    init_invariant(spec, self.init(), next, inv);
}

pub open spec fn key_of_object_in_matched_ok_update_resp_message_is_same_as_key_of_pending_req(controller_id: int, key: ObjectRef) -> StatePred<ClusterState>
    recommends
        key.kind.is_CustomResourceKind(),
{
    |s: ClusterState| {
        let pending_req = s.ongoing_reconciles(controller_id)[key].pending_req_msg.get_Some_0();
        let update_req = pending_req.content.get_update_request();
        forall |msg: Message|
            #[trigger] s.in_flight().contains(msg)
            && is_ok_update_response_msg()(msg)
            && s.ongoing_reconciles(controller_id).contains_key(key)
            && s.ongoing_reconciles(controller_id)[key].pending_req_msg.is_Some()
            && resp_msg_matches_req_msg(msg, pending_req)
            ==> is_ok_update_response_msg_and_matches_key(update_req.key())(msg)
    }
}

pub proof fn lemma_always_key_of_object_in_matched_ok_update_resp_message_is_same_as_key_of_pending_req(self, spec: TempPred<ClusterState>, controller_id: int, key: ObjectRef)
    requires
        key.kind.is_CustomResourceKind(),
        spec.entails(lift_state(self.init())),
        spec.entails(always(lift_action(self.next()))),
        self.controller_models.contains_key(controller_id),
    ensures spec.entails(always(lift_state(Self::key_of_object_in_matched_ok_update_resp_message_is_same_as_key_of_pending_req(controller_id, key)))),
{
    let inv = Self::key_of_object_in_matched_ok_update_resp_message_is_same_as_key_of_pending_req(controller_id, key);
    let next = |s, s_prime| {
        &&& self.next()(s, s_prime)
        &&& Self::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& Self::every_in_flight_msg_has_lower_id_than_allocator()(s)
        &&& Self::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(controller_id, key)(s)
        &&& Self::every_in_flight_msg_has_unique_id()(s)
        &&& Self::there_is_the_controller_state(controller_id)(s)
    };
    self.lemma_always_each_object_in_etcd_is_weakly_well_formed(spec);
    self.lemma_always_every_in_flight_msg_has_lower_id_than_allocator(spec);
    self.lemma_always_every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(spec, controller_id, key);
    self.lemma_always_every_in_flight_msg_has_unique_id(spec);
    self.lemma_always_there_is_the_controller_state(spec, controller_id);
    combine_spec_entails_always_n!(
        spec, lift_action(next), lift_action(self.next()), lift_state(Self::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(Self::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(Self::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(controller_id, key)),
        lift_state(Self::every_in_flight_msg_has_unique_id()),
        lift_state(Self::there_is_the_controller_state(controller_id))
    );
    assert forall |s, s_prime| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        assert forall |msg| #[trigger] s_prime.in_flight().contains(msg)
            && is_ok_update_response_msg()(msg) && s_prime.ongoing_reconciles(controller_id).contains_key(key)
            && s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg.is_Some()
            && resp_msg_matches_req_msg(msg, s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg.get_Some_0())
        implies
            is_ok_update_response_msg_and_matches_key(s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg.get_Some_0().content.get_update_request().key())(msg)
        by {
            assert(s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg.get_Some_0().content.is_update_request());
            let req_key = s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg.get_Some_0().content.get_update_request().key();
            let step = choose |step| self.next_step(s, s_prime, step);
            match step {
                Step::ControllerStep(input) => {
                    assert(s.in_flight().contains(msg));
                    let input_controller_id = input.0;
                    let input_cr_key = input.2.get_Some_0();
                    if input_controller_id == controller_id && input_cr_key == key {
                        assert(false);
                    } else {
                        assert(s.ongoing_reconciles(controller_id)[key] == s_prime.ongoing_reconciles(controller_id)[key]);
                        assert(is_ok_update_response_msg_and_matches_key(req_key)(msg));
                    }
                },
                Step::APIServerStep(input) => {
                    assert(s.ongoing_reconciles(controller_id)[key] == s_prime.ongoing_reconciles(controller_id)[key]);
                    if !s.in_flight().contains(msg) {
                        assert(msg.content.is_update_response());
                        assert(msg == handle_update_request_msg(self.installed_types, s.ongoing_reconciles(controller_id)[key].pending_req_msg.get_Some_0(), s.api_server).1);
                        assert(msg.src.is_APIServer() && msg.content.is_update_response());
                        if msg.content.get_update_response().res.is_Ok() {
                            assert(s.resources().contains_key(req_key));
                            assert(s.resources()[req_key].object_ref() == req_key);
                        }
                        assert(is_ok_update_response_msg_and_matches_key(req_key)(msg));
                    }
                },
                Step::DropReqStep(input) => {
                    assert(s.ongoing_reconciles(controller_id)[key] == s_prime.ongoing_reconciles(controller_id)[key]);
                    if !s.in_flight().contains(msg) {
                        assert(msg.src.is_APIServer());
                        assert(msg.content.is_update_response());
                        assert(msg.content.get_update_response().res.is_Err());
                    }
                    assert(is_ok_update_response_msg_and_matches_key(req_key)(msg));
                },
                Step::ExternalStep(input) => {
                    assert(input.1.get_Some_0() != msg);
                    assert(s.in_flight().contains(msg));
                },
                _ => {
                    assert(s.in_flight().contains(msg));
                    assert(is_ok_update_response_msg_and_matches_key(req_key)(msg));
                }
            }
        }
    }
    init_invariant(spec, self.init(), next, inv);
}

pub open spec fn key_of_object_in_matched_ok_create_resp_message_is_same_as_key_of_pending_req(controller_id: int, key: ObjectRef) -> StatePred<ClusterState>
    recommends
        key.kind.is_CustomResourceKind(),
{
    |s: ClusterState| {
        let pending_req = s.ongoing_reconciles(controller_id)[key].pending_req_msg.get_Some_0();
        let create_req = pending_req.content.get_create_request();
        forall |msg: Message|
            s.in_flight().contains(msg)
            && is_ok_create_response_msg()(msg)
            && s.ongoing_reconciles(controller_id).contains_key(key)
            && s.ongoing_reconciles(controller_id)[key].pending_req_msg.is_Some()
            && #[trigger] resp_msg_matches_req_msg(msg, s.ongoing_reconciles(controller_id)[key].pending_req_msg.get_Some_0())
            && create_req.obj.metadata.name.is_Some()
            ==> is_ok_create_response_msg_and_matches_key(create_req.key())(msg)
    }
}

pub proof fn lemma_always_key_of_object_in_matched_ok_create_resp_message_is_same_as_key_of_pending_req(self, spec: TempPred<ClusterState>, controller_id: int, key: ObjectRef)
    requires
        key.kind.is_CustomResourceKind(),
        spec.entails(lift_state(self.init())),
        spec.entails(always(lift_action(self.next()))),
        self.controller_models.contains_key(controller_id),
    ensures spec.entails(always(lift_state(Self::key_of_object_in_matched_ok_create_resp_message_is_same_as_key_of_pending_req(controller_id, key)))),
{
    let inv = Self::key_of_object_in_matched_ok_create_resp_message_is_same_as_key_of_pending_req(controller_id, key);
    let next = |s, s_prime| {
        &&& self.next()(s, s_prime)
        &&& Self::each_object_in_etcd_is_weakly_well_formed()(s)
        &&& Self::every_in_flight_msg_has_lower_id_than_allocator()(s)
        &&& Self::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(controller_id, key)(s)
        &&& Self::every_in_flight_msg_has_unique_id()(s)
        &&& Self::there_is_the_controller_state(controller_id)(s)
    };
    self.lemma_always_each_object_in_etcd_is_weakly_well_formed(spec);
    self.lemma_always_every_in_flight_msg_has_lower_id_than_allocator(spec);
    self.lemma_always_every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(spec, controller_id, key);
    self.lemma_always_every_in_flight_msg_has_unique_id(spec);
    self.lemma_always_there_is_the_controller_state(spec, controller_id);
    combine_spec_entails_always_n!(
        spec, lift_action(next), lift_action(self.next()), lift_state(Self::each_object_in_etcd_is_weakly_well_formed()),
        lift_state(Self::every_in_flight_msg_has_lower_id_than_allocator()),
        lift_state(Self::every_in_flight_req_msg_has_different_id_from_pending_req_msg_of(controller_id, key)),
        lift_state(Self::every_in_flight_msg_has_unique_id()),
        lift_state(Self::there_is_the_controller_state(controller_id))
    );
    assert forall |s, s_prime| inv(s) && #[trigger] next(s, s_prime) implies inv(s_prime) by {
        let create_req = s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg.get_Some_0().content.get_create_request();
        assert forall |msg| #[trigger] s_prime.in_flight().contains(msg)
            && is_ok_create_response_msg()(msg) && s_prime.ongoing_reconciles(controller_id).contains_key(key)
            && s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg.is_Some()
            && resp_msg_matches_req_msg(msg, s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg.get_Some_0())
            && create_req.obj.metadata.name.is_Some()
        implies
            is_ok_create_response_msg_and_matches_key(s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg.get_Some_0().content.get_create_request().key())(msg)
        by {
            assert(s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg.get_Some_0().content.is_create_request());
            let req_key = create_req.key();
            let step = choose |step| self.next_step(s, s_prime, step);
            match step {
                Step::ControllerStep(input) => {
                    assert(s.in_flight().contains(msg));
                    let input_controller_id = input.0;
                    let input_cr_key = input.2.get_Some_0();
                    if input_controller_id == controller_id && input_cr_key == key {
                        assert(false);
                    } else {
                        assert(s.ongoing_reconciles(controller_id)[key].pending_req_msg == s_prime.ongoing_reconciles(controller_id)[key].pending_req_msg);
                        assert(is_ok_create_response_msg_and_matches_key(create_req.key())(msg));
                    }
                },
                Step::APIServerStep(input) => {
                    assert(s.ongoing_reconciles(controller_id)[key] == s_prime.ongoing_reconciles(controller_id)[key]);
                    if !s.in_flight().contains(msg) {
                        assert(msg.content.is_create_response());
                        assert(msg == handle_create_request_msg(self.installed_types, s.ongoing_reconciles(controller_id)[key].pending_req_msg.get_Some_0(), s.api_server).1);
                        assert(msg.src.is_APIServer() && msg.content.is_create_response());
                        if msg.content.get_create_response().res.is_Ok() {
                            assert(s_prime.resources()[req_key].object_ref() == req_key);
                        }
                        assert(is_ok_create_response_msg_and_matches_key(req_key)(msg));
                    }
                },
                Step::DropReqStep(input) => {
                    assert(s.ongoing_reconciles(controller_id)[key] == s_prime.ongoing_reconciles(controller_id)[key]);
                    if !s.in_flight().contains(msg) {
                        assert(msg.src.is_APIServer());
                        assert(msg.content.is_create_response());
                        assert(msg.content.get_create_response().res.is_Err());
                    }
                    assert(is_ok_create_response_msg_and_matches_key(req_key)(msg));
                },
                Step::ExternalStep(input) => {
                    assert(input.1.get_Some_0() != msg);
                    assert(s.in_flight().contains(msg));
                    assert(s.ongoing_reconciles(controller_id)[key] == s_prime.ongoing_reconciles(controller_id)[key]);
                },
                _ => {
                    assert(s.in_flight().contains(msg));
                    assert(is_ok_create_response_msg_and_matches_key(req_key)(msg));
                }
            }
        }
    }
    init_invariant(spec, self.init(), next, inv);
}

}

}
