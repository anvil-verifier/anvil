use vstd::prelude::*;

verus! {
pub struct Concrete {
    pub a: u64,
}

pub struct Abstract {
    pub a: nat,
}

impl View for Concrete {
    type V = Abstract;

    open spec fn view(&self) -> <Self as vstd::string::View>::V {
        Abstract { a: self.a as nat }
    }
}

impl Concrete {
    // fn add1_a(&mut self)
    //     requires old(self).a < u64::MAX - 1
    // {
    //     self.a = self.a + 1;
    // }

    // In Anvil, we would actually write this with signature `fn add1_b(&mut self)`
    #[verifier::when_used_as_spec(spec_add1_b)]
    fn add1_b(self) -> (r: Self)
        requires self@.a < u64::MAX - 1
        ensures r@ == self@.add1_b()
    {
        Self { a: self.a + 1 }
    }

    spec fn spec_add1_b(self) -> Self; // {
    //     self@.add1_b()
    // }
    // Cannot write this body, because we need to return `Self` not `Self::V`

    broadcast proof fn view_add1_b_matches_spec_add1_b(self)
        ensures #![auto] self.spec_add1_b()@ == self@.add1_b()
    {
        admit();
    }
}

impl Abstract {
    spec fn add1_b(self) -> Self {
        Self { a: self.a + 1 }
    }
}

mod m1 {

    use super::*;
    broadcast use Concrete::view_add1_b_matches_spec_add1_b;

    // The following two functions would be emitted by e.g. a macro based on input like:
    // specexec fn do(c0: Concrete) -> (c1: Concrete)
    //   requires c0@.a == 10
    // {
    //   c0.add1_b()
    // }
    // Of course, we don't yet know how to handle `&mut` arguments or `mut` variables

    // In Anvil, we would actually write this with signature `fn exec_do(c: &mut Concrete)`
    fn exec_do(c0: Concrete) -> (c1: Concrete)
        requires c0@.a == 10,
        ensures c1@ == spec_do(c0@), // this should be generated, can it? (do we know where to
                                     // `.view()`?
    {
        c0.add1_b()
    }

    spec fn spec_do(c0: Abstract) -> (c1: Abstract)
        // Should the precondition be a `recommends` instead?
    {
        if c0.a == 10 { // <-- c0@.a == 10 (is this a possible automatic syntactic transform?)
            c0.add1_b() // the body matches exactly here, which bodes well for auto-translation,
                        // thanks to `when_used_as_spec`, but we may need a more flexible version
                        // of it for things like `&mut`?
        } else {
            arbitrary()
        }
    }

}

} // verus!
