use vstd::prelude::*;
use vstd::seq_lib::*;
use vstd::view::DeepView;
use super::seq_lib::lemma_filter_push;

verus! {

trait VerusClone: View + Sized {
    fn verus_clone(&self) -> (r: Self)
        ensures self == r;
}

fn vec_filter<T: VerusClone + Sized + DeepView<V = U>, U>(v: Vec<T>, f: impl Fn(&T) -> bool, f_spec: spec_fn(U) -> bool) -> (r: Vec<T>)
    requires
        forall |v: T| #[trigger] f.requires((&v,)),
        forall |v: T, r: bool| f.ensures((&v,), r) ==> f_spec(v.deep_view()) == r // this says that f and f_spec are in conformance,
    ensures r.deep_view() =~= v.deep_view().filter(f_spec)
{
    let mut r = Vec::new();
    let mut i = 0;
    for i in 0..v.len()
        invariant
            forall |v: T| #[trigger] f.requires((&v,)),
            r.deep_view() =~= v.deep_view().take(i as int).filter(f_spec),
            forall |v: T, r: bool| f.ensures((&v,), r) ==> f_spec(v.deep_view()) == r,
    {

        let elem = &v[i];
        let take = f(elem);
        if take {
            r.push(elem.verus_clone());
        }
        proof {
            let elem_spec = elem.deep_view();
            assert(f_spec(elem_spec) == take);
            let r_old = if take {
                r.deep_view().drop_last()
            } else {
                r.deep_view()
            };
            assert(r_old == v.deep_view().take(i as int).filter(f_spec));
            lemma_filter_push(v.deep_view().take(i as int), f_spec, elem_spec);
            assert(v.deep_view().take(i + 1 as int) == v.deep_view().take(i as int).push(elem_spec))
        }
    }
    proof {
        assert(v.deep_view().take(v.len() as int) == v.deep_view());
    }
    r
}

}
