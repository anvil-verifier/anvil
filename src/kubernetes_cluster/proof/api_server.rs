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

#[verifier(rlimit(50))]
pub proof fn other_objects_are_unaffected_if_request_fails_to_be_applied(cluster: Cluster, s: ClusterState, s_prime: ClusterState, msg: Message, key: ObjectRef)
requires
    cluster.next_step(s, s_prime, Step::APIServerStep(Some(msg))),
    Cluster::each_object_in_etcd_is_weakly_well_formed()(s),
    msg.content is APIRequest,
    msg.dst is APIServer,
    match msg.content->APIRequest_0 {
        APIRequest::CreateRequest(req) => { // key does not match
            &&& req.obj.metadata.name is Some ==> req.obj.metadata.name->0 != key.name
            &&& req.obj.metadata.name is None && req.obj.metadata.generate_name is Some ==> generated_name(s.api_server, req.obj.metadata.generate_name->0) != key.name
        },
        APIRequest::DeleteRequest(req) => {
            resource_delete_request_msg(key)(msg) && s.resources().contains_key(req.key()) ==> !{
                let etcd_obj = s.resources()[key];
                &&& req.preconditions is Some
                &&& req.preconditions->0.resource_version is Some
                &&& etcd_obj.metadata.resource_version is Some
                &&& etcd_obj.metadata.resource_version == req.preconditions->0.resource_version
            }
        },
        APIRequest::UpdateRequest(req) => {
            resource_update_request_msg(key)(msg) && s.resources().contains_key(req.key()) ==> !{
                let etcd_obj = s.resources()[key];
                &&& req.obj.metadata.resource_version is Some
                &&& etcd_obj.metadata.resource_version is Some
                &&& etcd_obj.metadata.resource_version == req.obj.metadata.resource_version
            }
        },
        APIRequest::UpdateStatusRequest(req) => {
            resource_update_status_request_msg(key)(msg) && s.resources().contains_key(req.key()) ==> !{
                let etcd_obj = s.resources()[key];
                &&& req.obj.metadata.resource_version is Some
                &&& etcd_obj.metadata.resource_version is Some
                &&& etcd_obj.metadata.resource_version == req.obj.metadata.resource_version
            }
        },
        APIRequest::GetThenDeleteRequest(req) => {
            resource_get_then_delete_request_msg(key)(msg) && s.resources().contains_key(req.key()) ==> !{
                let etcd_obj = s.resources()[key];
                &&& req.owner_ref.controller == Some(true) // no get_then_delete request can succeed
                &&& etcd_obj.metadata.owner_references is Some
                &&& req.owner_ref.kind != etcd_obj.metadata.owner_references->0.filter(controller_owner_filter())[0].kind
            }
        },
        APIRequest::GetThenUpdateRequest(req) => {
            resource_get_then_update_request_msg(key)(msg) && s.resources().contains_key(req.key()) ==> !{
                let etcd_obj = s.resources()[key];
                &&& req.owner_ref.controller == Some(true) // no get_then_update request can succeed
                &&& etcd_obj.metadata.owner_references is Some
                &&& req.owner_ref.kind != etcd_obj.metadata.owner_references->0.filter(controller_owner_filter())[0].kind
            }
        },
        APIRequest::GetThenUpdateStatusRequest(req) => {
            resource_get_then_update_status_request_msg(key)(msg) && s.resources().contains_key(req.key()) ==> !{
                let etcd_obj = s.resources()[key];
                &&& req.owner_ref.controller == Some(true) // no get_then_update_status request can succeed
                &&& etcd_obj.metadata.owner_references is Some
                &&& req.owner_ref.kind != etcd_obj.metadata.owner_references->0.filter(controller_owner_filter())[0].kind
            }
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
            assert(!resource_create_request_msg(key)(msg));
            assert(!resource_create_request_msg_without_name(key.kind, key.namespace)(msg));
            if create_req.obj.metadata.name is Some {
                assert(msg.content.get_create_request().key() != key);
            } else if create_req.obj.metadata.generate_name is Some {
                assert(create_req.obj.kind != key.kind || create_req.namespace != key.namespace);
            }
        },
        APIRequest::DeleteRequest(delete_req) => {
            assert(!resource_delete_request_msg(key)(msg));
            assert(delete_req.key() != key);
        },
        APIRequest::UpdateRequest(update_req) => {
            assert(!resource_update_request_msg(key)(msg));
            assert(update_req.key() != key);
            if update_request_admission_check(cluster.installed_types, update_req, s.api_server) is None {
                let old_obj = s.resources()[update_req.key()];
                assert(old_obj.object_ref() == update_req.key());
                let uo = updated_object(update_req, old_obj);
                assert(uo.object_ref() == update_req.key());
            }
        },
        APIRequest::UpdateStatusRequest(update_status_req) => {
            assert(!resource_update_status_request_msg(key)(msg));
            assert(update_status_req.key() != key);
        },
        APIRequest::GetThenUpdateRequest(get_then_update_req) => {
            assert(!resource_get_then_update_request_msg(key)(msg));
            assert(get_then_update_req.key() != key);
            if s.resources().contains_key(get_then_update_req.key()) {
                let current_obj = s.resources()[get_then_update_req.key()];
                if current_obj.metadata.owner_references_contains(get_then_update_req.owner_ref) {
                    let new_obj = DynamicObjectView {
                        metadata: ObjectMetaView {
                            resource_version: current_obj.metadata.resource_version,
                            uid: current_obj.metadata.uid,
                            ..get_then_update_req.obj.metadata
                        },
                        ..get_then_update_req.obj
                    };
                    let inner_req = UpdateRequest {
                        name: get_then_update_req.name,
                        namespace: get_then_update_req.namespace,
                        obj: new_obj,
                    };
                    assert(inner_req.key() == get_then_update_req.key());
                    if update_request_admission_check(cluster.installed_types, inner_req, s.api_server) is None {
                        let old_obj = s.resources()[inner_req.key()];
                        assert(old_obj.object_ref() == inner_req.key());
                        let uo = updated_object(inner_req, old_obj);
                        assert(uo.object_ref() == inner_req.key());
                    }
                }
            }
        },
        APIRequest::GetThenDeleteRequest(get_then_delete_req) => {
            assert(!resource_get_then_delete_request_msg(key)(msg));
            assert(get_then_delete_req.key() != key);
        },
        APIRequest::GetThenUpdateStatusRequest(get_then_update_status_req) => {
            assert(!resource_get_then_update_status_request_msg(key)(msg));
            assert(get_then_update_status_req.key() != key);
            if s.resources().contains_key(get_then_update_status_req.key()) {
                let current_obj = s.resources()[get_then_update_status_req.key()];
                if current_obj.metadata.owner_references_contains(get_then_update_status_req.owner_ref) {
                    let new_obj = DynamicObjectView {
                        metadata: current_obj.metadata,
                        spec: current_obj.spec,
                        status: get_then_update_status_req.obj.status,
                        ..current_obj
                    };
                    let inner_req = UpdateStatusRequest {
                        name: get_then_update_status_req.name,
                        namespace: get_then_update_status_req.namespace,
                        obj: new_obj,
                    };
                    assert(inner_req.key().name == get_then_update_status_req.key().name);
                    assert(inner_req.key().namespace == get_then_update_status_req.key().namespace);
                }
            }
        },
        _ => {
            // Get and List are read-only, s_prime == s
        }
    };
}

}