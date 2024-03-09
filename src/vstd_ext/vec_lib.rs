use vstd::prelude::*;
use vstd::seq_lib::*;

verus! {

trait VerusClone: View + Sized {
    fn verus_clone(&self) -> (r: Self)
        ensures self == r;
}

fn vec_filter<V: VerusClone + View + Sized>(v: Vec<V>, f: impl Fn(&V)->bool, f_spec: spec_fn(V)->bool) -> (r: Vec<V>)
    requires
        forall|v: V| #[trigger] f.requires((&v,)),
        forall |v:V,r:bool| f.ensures((&v,), r) ==> f_spec(v) == r,
    ensures r@.to_multiset() =~= v@.to_multiset().filter(f_spec)
{
    let mut r = Vec::new();
    let mut i = 0;
    proof { lemma_seq_properties::<V>(); }
    while i < v.len()
        invariant
            forall|v: V| #[trigger] f.requires((&v,)),
            i <= v.len(),
            r@.to_multiset() =~= v@.subrange(0, i as int).to_multiset().filter(f_spec),
            forall |v:V,r:bool| f.ensures((&v,), r) ==> f_spec(v) == r,
    {
        proof { lemma_seq_properties::<V>(); }
        let ghost pre_r = r@.to_multiset();
        assert(
            v@.subrange(0, i as int + 1)
            =~=
            v@.subrange(0, i as int).push(v@[i as int]));
        if f(&v[i]) {
            r.push(v[i].verus_clone());
        }

        i += 1;
    }
    r
}

}
