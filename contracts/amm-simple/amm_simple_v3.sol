// mutation: linear price (the output of a swap is x * r_out / r_in), which drains the pool
// Simplified constant-product AMM: the swaps of contracts/amm/amm.sol, without liquidity
// tokens (the constructor creates the pool with the reserves x0, x1). The existential rules
// of amm.sol (Sandwich, Arbitrage) are stated with an explicit strategy, which the tool
// checks (a winning strategy is a witness of the existential).
pragma balance real;

contract AMM {
    mapping (address => real) t0;
    mapping (address => real) t1;
    real r0;                            // reserves
    real r1;
    real out0;                          // amounts paid by the last swap
    real out1;

    constructor(real s0, real s1, real x0, real x1) {
        require(s0 >= 0 && s1 >= 0 && x0 > 0 && x1 > 0);
        t0[msg.sender] = s0;
        t1[msg.sender] = s1;
        r0 = x0;
        r1 = x1
    }

    function transfer0(address to, real n) {
        require(n > 0 && t0[msg.sender] >= n);
        t0[msg.sender] -= n;
        t0[to] += n
    }

    function transfer1(address to, real n) {
        require(n > 0 && t1[msg.sender] >= n);
        t1[msg.sender] -= n;
        t1[to] += n
    }

    // sells x tokens T0 for at least ymin tokens T1
    function swap0(real x, real ymin) {
        require(x > 0 && t0[msg.sender] >= x && r0 > 0 && r1 > 0);
        out1 = x * r1 / r0;
        require(out1 >= ymin);
        t0[msg.sender] -= x;
        r0 += x;
        r1 -= out1;
        t1[msg.sender] += out1
    }

    // sells x tokens T1 for at least ymin tokens T0
    function swap1(real x, real ymin) {
        require(x > 0 && t1[msg.sender] >= x && r0 > 0 && r1 > 0);
        out0 = x * r0 / r1;
        require(out0 >= ymin);
        t1[msg.sender] -= x;
        r1 += x;
        r0 -= out0;
        t0[msg.sender] += out0
    }
}

// The reserves are positive in every state after the construction (rules and invariants are
// checked only in such states).
// False here: a swap of more than the reserve r0 makes r1 negative.
// @groundtruth: False
invariant Nonnegative {
    (forall u : address . t0[u] >= 0 && t1[u] >= 0) && r0 > 0 && r1 > 0
}

// Slippage protection: a swap that succeeds pays at least ymin.
// @groundtruth: True
rule Slippage {
    forall a : address . forall x : real . forall ymin : real .
    << a : AMM.swap0(x, ymin) >> (lastReverted || t1[a] >= old(t1[a]) + ymin)
}

// Sandwich attack, with an explicit strategy: adv front-runs with all its tokens T0.
// False here: if adv holds at least r0 tokens T0, its front-run makes r1 nonpositive, and the
// back-run reverts.
// @groundtruth: False
rule Sandwich {
    forall a : address . forall adv : address . forall x : real .
    (is_EOA(a) && is_EOA(adv) && a != adv && x > 0 && t0[a] >= x && t0[adv] > 0) ->
    << adv : AMM.swap0(t0[adv], 0) >> << a : AMM.swap0(x, 0) >>
    << adv : AMM.swap1(t1[adv] - old(old(t1[adv])), 0) >>
        (t0[adv] > old(old(old(t0[adv]))) && t1[adv] == old(old(old(t1[adv]))))
}

// Sandwich attack against a slippage bound: if the victim accepts less than what its swap
// would pay now (ymin < x * r1 / (r0 + x)), any other user with tokens T0 can front-run it
// with some amount z (small enough for the victim's swap to succeed) and gain.
// False here: if x >= 2 * r0, every front-run that lets the victim's swap succeed
// leaves r1 nonpositive after it, and the back-run reverts.
// @groundtruth: False
rule Sandwich_slippage {
    forall a : address . forall adv : address . forall x : real . forall ymin : real .
    (is_EOA(a) && is_EOA(adv) && a != adv && x > 0 && t0[a] >= x && t0[adv] > 0
     && ymin * (r0 + x) < x * r1) ->
    exists z : real .
    << adv : AMM.swap0(z, 0) >> << a : AMM.swap0(x, ymin) >>
        (!lastReverted
         && << adv : AMM.swap1(t1[adv] - old(old(t1[adv])), 0) >>
            (t0[adv] > old(old(old(t0[adv]))) && t1[adv] == old(old(old(t1[adv])))))
}

// Splitting a swap gives the same as a single swap.
// @groundtruth: False
rule Swap_additivity {
    forall a : address . forall x1 : real . forall x2 : real .
    exists v12 : real . exists v3 : real .
    exists q1 : bool . exists q2 : bool . exists q3 : bool .
    (<< a : AMM.swap0(x1, 0) >> (q1 == lastReverted &&
        << a : AMM.swap0(x2, 0) >> (q2 == lastReverted && v12 == t1[a])))
    && (<< a : AMM.swap0(x1 + x2, 0) >> (q3 == lastReverted && v3 == t1[a]))
    && (q1 || q2 || (!q3 && v12 == v3))
}

// A swap can be undone by an opposite swap.
// @groundtruth: False
rule Swap_reversibility {
    forall a : address . forall x : real . exists y : real .
    << a : AMM.swap0(x, 0) >>
        (lastReverted ||
         << a : AMM.swap1(y, 0) >>
            (t0[a] == old(old(t0[a])) && t1[a] == old(old(t1[a]))))
}

// No round trip of swaps is profitable.
// @groundtruth: False
rule No_money_pump {
    forall a : address . forall x : real . forall y : real .
    << a : AMM.swap0(x, 0) >> << a : AMM.swap1(y, 0) >>
        (!(t0[a] > old(old(t0[a])) && t1[a] >= old(old(t1[a])))
         && !(t0[a] >= old(old(t0[a])) && t1[a] > old(old(t1[a]))))
}

// Arbitrage, with an explicit strategy: if the AMM price of T0 is above the external price
// p, selling x < r1 / p - r0 tokens T0 increases the wealth at price p; a sells all its
// tokens T0 if they are fewer, half of the bound otherwise.
// @groundtruth: True
rule Arbitrage {
    forall a : address . forall p : real .
    (is_EOA(a) && p > 0 && r0 > 0 && t0[a] > 0 && r1 > p * r0) ->
    ((t0[a] < r1 / p - r0 ->
        << a : AMM.swap0(t0[a], 0) >> (p * t0[a] + t1[a] > old(p * t0[a] + t1[a])))
     && (t0[a] >= r1 / p - r0 ->
        << a : AMM.swap0((r1 / p - r0) / 2, 0) >> (p * t0[a] + t1[a] > old(p * t0[a] + t1[a]))))
}

// Arbitrage: if the AMM price of T0 is above the external price p, some swap increases the
// wealth at price p.
// @groundtruth: True
rule Arbitrage_exists {
    forall a : address . forall p : real .
    (is_EOA(a) && p > 0 && r0 > 0 && t0[a] > 0 && r1 > p * r0) ->
    exists x : real .
    << a : AMM.swap0(x, 0) >> (p * t0[a] + t1[a] > old(p * t0[a] + t1[a]))
}
