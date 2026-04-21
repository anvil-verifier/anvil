use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    api_server::{types::*, state_machine::*}, message::*, cluster::*
};
use crate::vstd_ext::string_view::*;
use vstd::prelude::*;

verus !{

pub proof fn generated_name_reflects_prefix(s: APIServerState, generate_name_field: StringView, prefix: StringView)
ensures
    (exists |suffix| generate_name_field == prefix + "-"@ + suffix)
    <==> (exists |suffix| #[trigger] generated_name(s, generate_name_field) == prefix + "-"@ + suffix)
{
    generated_name_spec(s, generate_name_field);
    let generate_name = generated_name(s, generate_name_field);
    if exists |suffix| #[trigger] generated_name(s, generate_name_field) == prefix + "-"@ + suffix {
        let suffix = choose |suffix| generate_name == prefix + "-"@ + suffix;
        dash_char_view_eq_str_view();
        let suffix2 = choose |suffix2| generate_name == generate_name_field + suffix2 && #[trigger] dash_free(suffix2);
        dash_char_view_eq_str_view();
        if prefix.len() >= generate_name_field.len() {
            assert(generate_name[prefix.len() as int] == '-'@);
            assert(suffix2 == generate_name.subrange(generate_name_field.len() as int, generate_name.len() as int));
            assert(suffix2[prefix.len() - generate_name_field.len()] == '-'@);
            assert(false);
        }
        assert(generate_name_field == generate_name.take(generate_name_field.len() as int));
        assert(prefix + "-"@ == generate_name_field.take(prefix.len() as int + 1));
        assert(generate_name_field == prefix + "-"@ + generate_name_field.subrange(prefix.len() as int + 1, generate_name_field.len() as int));
        assert(exists |suffix| generate_name_field == prefix + "-"@ + suffix);
    }
    if exists |suffix| generate_name_field == prefix + "-"@ + suffix {
        let suffix = choose |suffix| generate_name_field == prefix + "-"@ + suffix;
        let suffix2 = choose |suffix2| generate_name == generate_name_field + suffix2 && #[trigger] dash_free(suffix2);
        assert(generate_name == prefix + "-"@ + (suffix + suffix2));
    }
}

pub proof fn other_objects_are_unaffected_if_request_fails_to_be_applied(cluster: Cluster, s: ClusterState, s_prime: ClusterState, msg: Message, key: ObjectRef)
requires
    cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))),
    Cluster::each_object_in_etcd_is_weakly_well_formed()(s),
    Cluster::each_object_in_etcd_has_at_most_one_controller_owner()(s),
    msg.content is APIRequest,
    msg.dst is APIServer,
    match msg.content->APIRequest_0 {
        APIRequest::CreateRequest(req) => { // key does not match
            &&& req.obj.metadata.name is Some ==> req.obj.metadata.name->0 != key.name
            &&& req.obj.metadata.name is None && req.obj.metadata.generate_name is Some ==> generated_name(s.api_server, req.obj.metadata.generate_name->0) != key.name
        },
        APIRequest::DeleteRequest(req) => {
            resource_delete_request_msg(key)(msg) && s.resources().contains_key(req.key())
            ==> req.preconditions is Some && req.preconditions->0.resource_version is Some && !{
                let etcd_obj = s.resources()[key];
                &&& etcd_obj.metadata.resource_version is Some
                &&& etcd_obj.metadata.resource_version == req.preconditions->0.resource_version
            }
        },
        APIRequest::UpdateRequest(req) => {
            resource_update_request_msg(key)(msg) && s.resources().contains_key(req.key())
            ==> req.obj.metadata.resource_version is Some && !{
                let etcd_obj = s.resources()[key];
                &&& etcd_obj.metadata.resource_version is Some
                &&& etcd_obj.metadata.resource_version == req.obj.metadata.resource_version
            }
        },
        APIRequest::UpdateStatusRequest(req) => {
            resource_update_status_request_msg(key)(msg) && s.resources().contains_key(req.key())
            ==> req.obj.metadata.resource_version is Some && !{
                let etcd_obj = s.resources()[key];
                &&& req.obj.metadata.resource_version is Some
                &&& etcd_obj.metadata.resource_version is Some
                &&& etcd_obj.metadata.resource_version == req.obj.metadata.resource_version
            }
        },
        APIRequest::GetThenDeleteRequest(req) => {
            resource_get_then_delete_request_msg(key)(msg) && s.resources().contains_key(req.key())
            ==> !s.resources()[key].metadata.owner_references_contains(req.owner_ref)
        },
        APIRequest::GetThenUpdateRequest(req) => {
            resource_get_then_update_request_msg(key)(msg) && s.resources().contains_key(req.key())
            ==> !s.resources()[key].metadata.owner_references_contains(req.owner_ref)
        },
        APIRequest::GetThenUpdateStatusRequest(req) => {
            resource_get_then_update_status_request_msg(key)(msg) && s.resources().contains_key(req.key())
            ==> !s.resources()[key].metadata.owner_references_contains(req.owner_ref)
        },
        _ => true, // get/list requests are read only
    }
ensures
    s_prime.resources().contains_key(key) == s.resources().contains_key(key),
    s_prime.resources()[key] == s.resources()[key],
{
    let req = msg.content->APIRequest_0;
    match req {
        APIRequest::CreateRequest(create_req) => {
            if create_req.obj.metadata.name is Some {} else if create_req.obj.metadata.generate_name is Some {}
        },
        APIRequest::DeleteRequest(delete_req) => {},
        APIRequest::UpdateRequest(update_req) => {},
        APIRequest::UpdateStatusRequest(update_status_req) => {},
        APIRequest::GetThenUpdateRequest(get_then_update_req) => {},
        APIRequest::GetThenDeleteRequest(get_then_delete_req) => {},
        APIRequest::GetThenUpdateStatusRequest(get_then_update_status_req) => {},
        _ => {}
    };
}

}