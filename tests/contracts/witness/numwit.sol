// Numeric witnesses (`numwit.py`): an existential over a uint, and one under old(...).
// No property has a cutoff (an address universal under the existentials), so a proof for
// every number of users comes from an instance only.
contract Counter {
    int v;

    constructor(int initial_v) {
        v = initial_v
    }

    function add(int c) {
        v = v + c
    }
}

// false: for c = -1, no natural d gives v + d == v + c; the instance d := c holds where
// c >= 0 only, so it must carry the conjunct c >= 0 (it is then refuted)
property Uint_false {
    forall c : int .
    exists d : uint .
    forall addr : address .
    is_EOA(addr) -> (<< addr : Counter . add(d) $ 0 >> (v == old(v) + c))
}

// true, with d := c * c, a natural
property Uint_true {
    forall c : int .
    exists d : uint .
    forall addr : address .
    is_EOA(addr) -> (<< addr : Counter . add(d) $ 0 >> (v == old(v) + c * c))
}

// true, with y := v: old(y) is at the state of the existential, where y is v (not old(v))
property Old_true {
    forall c : int .
    exists y : int .
    forall addr : address .
    is_EOA(addr) -> (<< addr : Counter . add(c) $ 0 >> (old(y) == old(v)))
}
