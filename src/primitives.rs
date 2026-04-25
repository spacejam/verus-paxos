use vstd::prelude::*;

verus! {
    spec fn always_true() -> bool { true }

    proof fn smoke_test()
        ensures always_true()
    {}
}
