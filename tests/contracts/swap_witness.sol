// The swap pool of swap_pool.sol, with properties that have an existential over a real in
// positive position: the checks on free states go to z3 directly (DESIGN.md, Sect. 6,
// "Existentials over numbers"); through Kind 2 they stay unknown.
pragma balance real;

contract Pool {
    mapping (address => real) t0;
    mapping (address => real) t1;
    real r0;
    real r1;
    real out;

    constructor(real s0, real s1) {
        require(s0 > 0 && s1 > 0);
        t0[msg.sender] = s0;
        t1[msg.sender] = s1
    }

    function init(real x0, real x1) {
        require(r0 == 0 && x0 > 0 && x1 > 0);
        require(t0[msg.sender] >= x0 && t1[msg.sender] >= x1);
        t0[msg.sender] -= x0;
        t1[msg.sender] -= x1;
        r0 = x0;
        r1 = x1
    }

    function swap0(real x) {
        require(r0 > 0 && x > 0 && t0[msg.sender] >= x);
        out = x * r1 / (r0 + x);
        t0[msg.sender] -= x;
        r0 += x;
        r1 -= out;
        t1[msg.sender] += out
    }

    function swap1(real x) {
        require(r1 > 0 && x > 0 && t1[msg.sender] >= x);
        out = x * r0 / (r1 + x);
        t1[msg.sender] -= x;
        r1 += x;
        r0 -= out;
        t0[msg.sender] += out
    }
}

// @groundtruth: True
invariant Inv {
    (forall u : address . t0[u] >= 0 && t1[u] >= 0)
    && r0 >= 0 && r1 >= 0 && (r0 > 0) == (r1 > 0)
}

// A swap can be undone by an opposite swap (the witness: what the first swap paid).
// @groundtruth: True
property Swap_reversibility {
    forall a : address . forall x : real . exists y : real .
    << a : Pool.swap0(x) >>
        (lastReverted ||
         << a : Pool.swap1(y) >>
            (t0[a] == old(old(t0[a])) && t1[a] == old(old(t1[a]))))
}

// If the price of T0 in the pool is above p, some swap increases the wealth at price p (the
// witness depends on the state: all of t0[a], or less).
// @groundtruth: True
property Arbitrage_exists {
    forall a : address . forall p : real .
    (is_EOA(a) && p > 0 && r0 > 0 && t0[a] > 0 && r1 > p * r0) ->
    exists x : real .
    << a : Pool.swap0(x) >> (p * t0[a] + t1[a] > old(p * t0[a] + t1[a]))
}

// False: at the price p = r1 / r0, no swap is profitable.
// @groundtruth: False
property Arbitrage_exists_at_the_price {
    forall a : address . forall p : real .
    (is_EOA(a) && p > 0 && r0 > 0 && t0[a] > 0 && r1 >= p * r0) ->
    exists x : real .
    << a : Pool.swap0(x) >> (p * t0[a] + t1[a] > old(p * t0[a] + t1[a]))
}
