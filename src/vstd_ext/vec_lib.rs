use vstd::prelude::*;
use vstd::seq_lib::*;
use super::seq_lib::lemma_filter_push;

verus! {

trait VerusClone: View + Sized {
    fn verus_clone(&self) -> (r: Self)
        ensures self == r;
}

fn vec_filter<V: VerusClone + View + Sized>(v: Vec<V>, f: impl Fn(&V) -> bool, f_spec: spec_fn(V) -> bool) -> (r: Vec<V>)
    requires
        forall |v: V| #[trigger] f.requires((&v,)),
        forall |v: V, r: bool| f.ensures((&v,), r) <==> f_spec(v) == r // this says that f and f_spec are in conformance,
    ensures r@ =~= v@.filter(f_spec)
{
    let mut r = Vec::new();
    let mut i = 0;
    for i in 0..v.len()
        invariant
            forall |v: V| #[trigger] f.requires((&v,)),
            r@ =~= v@.take(i as int).filter(f_spec),
            forall |v: V, r: bool| f.ensures((&v,), r) <==> f_spec(v) == r,
    {

        let elem = &v[i];
        let take = f(elem);
        if take {
            r.push(elem.verus_clone());
        }
        proof {
            assert(f_spec(*elem) == take);
            let r_old = if take {
                r@.drop_last()
            } else {
                r@
            };
            assert(r_old == v@.take(i as int).filter(f_spec));
            lemma_filter_push(v@.take(i as int), f_spec, *elem);
            assert(v@.take(i + 1 as int) == v@.take(i as int).push(*elem));
        }
    }
    proof {
        assert(v@.take(v.len() as int) == v@);
    }
    r
}

}
