use crate::kubernetes_api_objects::spec::prelude::*;
use crate::kubernetes_cluster::spec::{
    api_server::{types::*, state_machine::*}
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

}