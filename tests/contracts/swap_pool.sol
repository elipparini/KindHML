// A constant-product swap pool with real amounts and embedded tokens, for the tests of the
// invariant-assisted checks (DESIGN.md, "Invariants"): Kind 2 alone does not prove
// Swap_reversibility (nonlinear arithmetic); on a free state satisfying Inv, z3 does.
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

    function transfer0(address to, real n) {
        require(n > 0 && t0[msg.sender] >= n);
        t0[msg.sender] -= n;
        t0[to] += n
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

// False (init can create larger reserves): the tool drops it from the invariants it assumes.
// @groundtruth: False
invariant Small_reserves {
    r0 <= 1000
}

// @groundtruth: True
rule Swap_reversibility {
    forall a : address . forall x : real .
    << a : Pool.swap0(x) >>
        (lastReverted ||
         << a : Pool.swap1(out) >>
            (t0[a] == old(old(t0[a])) && t1[a] == old(old(t1[a]))))
}

// @groundtruth: False
rule Swap_takes_everything {
    forall a : address . forall x : real .
    << a : Pool.swap0(x) >> (lastReverted || r1 == 0)
}
