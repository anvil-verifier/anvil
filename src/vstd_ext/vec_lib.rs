#![allow(unused_imports)]
use vstd::prelude::*;
use vstd::seq_lib::*;
use super::seq_lib::*;

verus! {

// Filters v with the exec predicate f, whose result must agree with the spec predicate pred on the
// deep view of every element. Replaces the hand-written filter loop plus its take/push proof.
pub fn vec_filter<T, F>(v: &Vec<T>, f: F, Ghost(pred): Ghost<spec_fn(T::V) -> bool>) -> (res: Vec<T>)
where
    T: DeepView + Clone,
    F: Fn(&T) -> bool,
    requires
        forall |i: int| 0 <= i < v@.len() ==> #[trigger] call_requires(f, (&v@[i],)),
        forall |t: T, b: bool| #[trigger] call_ensures(f, (&t,), b) ==> b == pred(t.deep_view()),
        forall |a: T, b: T| #[trigger] call_ensures(T::clone, (&a,), b) ==> b.deep_view() == a.deep_view(),
    ensures
        res.deep_view() == v.deep_view().filter(pred),
        forall |i: int| #![trigger res@[i]] 0 <= i < res@.len() ==> pred(res@[i].deep_view()),
{
    let mut res: Vec<T> = Vec::new();
    for idx in 0..v.len()
        invariant
            res.deep_view() == v.deep_view().take(idx as int).filter(pred),
            forall |i: int| 0 <= i < v@.len() ==> #[trigger] call_requires(f, (&v@[i],)),
            forall |t: T, b: bool| #[trigger] call_ensures(f, (&t,), b) ==> b == pred(t.deep_view()),
            forall |a: T, b: T| #[trigger] call_ensures(T::clone, (&a,), b) ==> b.deep_view() == a.deep_view(),
    {
        let e = &v[idx];
        if f(e) {
            let cloned_e = e.clone();
            res.push(cloned_e);
        }
        proof {
            v.deep_view().take(idx as int).lemma_filter_push(e.deep_view(), pred);
            assert(v.deep_view().take(idx as int).push(e.deep_view()) =~= v.deep_view().take(idx + 1 as int));
        }
    }
    assert(v.deep_view().take(v.len() as int) =~= v.deep_view());
    proof {
        broadcast use Seq::lemma_filter_pred;
        assert forall |i: int| #![trigger res@[i]] 0 <= i < res@.len() implies pred(res@[i].deep_view()) by {
            assert(res.deep_view()[i] == res@[i].deep_view());
        }
    }
    res
}

}
