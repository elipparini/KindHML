// variant: integer amounts, as in Solidity (divisions round down)
// Simplified constant-product AMM: the swaps of contracts/amm/amm.sol, without liquidity
// tokens (the constructor creates the pool with the reserves x0, x1). The existential rules
// of amm.sol (Sandwich, Arbitrage) are stated with an explicit strategy, which the tool
// checks (a winning strategy is a witness of the existential).

contract AMM {
    mapping (address => int) t0;
    mapping (address => int) t1;
    int r0;                             // reserves
    int r1;
    int out0;                           // amounts paid by the last swap
    int out1;

    constructor(int s0, int s1, int x0, int x1) {
        require(s0 >= 0 && s1 >= 0 && x0 > 0 && x1 > 0);
        t0[msg.sender] = s0;
        t1[msg.sender] = s1;
        r0 = x0;
        r1 = x1
    }

    function transfer0(address to, int n) {
        require(n > 0 && t0[msg.sender] >= n);
        t0[msg.sender] -= n;
        t0[to] += n
    }

    function transfer1(address to, int n) {
        require(n > 0 && t1[msg.sender] >= n);
        t1[msg.sender] -= n;
        t1[to] += n
    }

    // sells x tokens T0 for at least ymin tokens T1
    function swap0(int x, int ymin) {
        require(x > 0 && t0[msg.sender] >= x && r0 > 0 && r1 > 0);
        out1 = x * r1 / (r0 + x);
        require(out1 >= ymin);
        t0[msg.sender] -= x;
        r0 += x;
        r1 -= out1;
        t1[msg.sender] += out1
    }

    // sells x tokens T1 for at least ymin tokens T0
    function swap1(int x, int ymin) {
        require(x > 0 && t1[msg.sender] >= x && r0 > 0 && r1 > 0);
        out0 = x * r0 / (r1 + x);
        require(out0 >= ymin);
        t1[msg.sender] -= x;
        r1 += x;
        r0 -= out0;
        t0[msg.sender] += out0
    }
}

// @groundtruth: True
invariant Nonnegative {
    (forall u : address . t0[u] >= 0 && t1[u] >= 0)
    && r0 >= 0 && r1 >= 0 && (r0 > 0) == (r1 > 0)
}

// Slippage protection against front-running (as in amm.sol).
// @groundtruth: True
rule Slippage {
    forall a : address . forall b : address .
    forall f : method . forall args : calldataargs .
    forall x : int . forall ymin : int .
    is_EOA(a) ->
    << b : AMM.f(args) >> << a : AMM.swap0(x, ymin) >>
        (lastReverted || t1[a] >= old(t1[a]) + ymin)
}

// Sandwich attack, with an explicit strategy: b front-runs with all its tokens T0.
// False here: for a small x, rounding leaves b nothing to gain.
// @groundtruth: False
rule Sandwich {
    forall a : address . forall b : address . forall x : int .
    (is_EOA(a) && is_EOA(b) && a != b && r0 > 0 && r1 > 0 && x > 0 && t0[a] >= x
     && t0[b] > 0) ->
    << b : AMM.swap0(t0[b], 0) >> << a : AMM.swap0(x, 0) >>
    << b : AMM.swap1(t1[b] - old(old(t1[b])), 0) >>
        (t0[b] > old(old(old(t0[b]))) && t1[b] == old(old(old(t1[b]))))
}

// Splitting a swap gives the same as a single swap.
// False here: rounding.
// @groundtruth: False
rule Swap_additivity {
    forall a : address . forall x1 : int . forall x2 : int .
    exists v12 : int . exists v3 : int .
    exists q1 : bool . exists q2 : bool . exists q3 : bool .
    (<< a : AMM.swap0(x1, 0) >> (q1 == lastReverted &&
        << a : AMM.swap0(x2, 0) >> (q2 == lastReverted && v12 == t1[a])))
    && (<< a : AMM.swap0(x1 + x2, 0) >> (q3 == lastReverted && v3 == t1[a]))
    && (q1 || q2 || (!q3 && v12 == v3))
}

// A swap can be undone by the opposite swap of its output.
// False here: rounding.
// @groundtruth: False
rule Swap_reversibility {
    forall a : address . forall x : int .
    << a : AMM.swap0(x, 0) >>
        (lastReverted ||
         << a : AMM.swap1(out1, 0) >>
            (t0[a] == old(old(t0[a])) && t1[a] == old(old(t1[a]))))
}

// No round trip of swaps is profitable.
// @groundtruth: True
rule No_money_pump {
    forall a : address . forall x : int . forall y : int .
    << a : AMM.swap0(x, 0) >> << a : AMM.swap1(y, 0) >>
        !(t0[a] > old(old(t0[a])) && t1[a] >= old(old(t1[a])))
}

// Arbitrage, with an explicit strategy (as in amm_simple.sol; amounts rounded down).
// False here: rounding (e.g. r0 = 1, r1 = 3, p = 1, t0[a] = 1: the swap gains nothing).
// @groundtruth: False
rule Arbitrage {
    forall a : address . forall p : int .
    (is_EOA(a) && p > 0 && r0 > 0 && t0[a] > 0 && r1 > p * r0) ->
    ((t0[a] < r1 / p - r0 ->
        << a : AMM.swap0(t0[a], 0) >> (p * t0[a] + t1[a] > old(p * t0[a] + t1[a])))
     && (t0[a] >= r1 / p - r0 ->
        << a : AMM.swap0((r1 / p - r0) / 2, 0) >> (p * t0[a] + t1[a] > old(p * t0[a] + t1[a]))))
}
