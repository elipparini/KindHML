// version: integer amounts, as in Solidity (fixed point: the exchange rate xr0 and the
// interest index idx are scaled by 1000; divisions round down)
// Lending protocol in the style of Aave and Compound, after the model of
// M. Bartoletti, E. Lipparini, "A theory of Lending Protocols in DeFi" (arXiv 2506.15295),
// and the use case of https://github.com/bitbart/contracts-verification-benchmark (FC26).
// See lending.sol for the description; here a is healthy if
// (c0[a] * xr0 / 1000 + c1[a] * p1) * 4 >= sdebt[a] * idx / 1000 * 5.

contract Lending {
    address oracle;
    int p1;                             // price of T1
    mapping (address => int) w0;        // wallets
    mapping (address => int) w1;
    int res0;                           // reserves of T0
    mapping (address => int) c0;        // credits in T0
    int sc0;                            // total credits
    int xr0;                            // exchange rate of the credits (x 1000)
    mapping (address => int) c1;        // collateral in T1
    mapping (address => int) sdebt;     // scaled debts in T0
    int ssdebt;                         // total scaled debt
    int idx;                            // interest index (x 1000)
    int amt;                            // temporary

    constructor(address oracle_, int s0, int s1, int p) {
        require(s0 > 0 && s1 > 0 && p > 0);
        oracle = oracle_;
        p1 = p;
        idx = 1000;
        xr0 = 1000;
        w0[msg.sender] = s0;
        w1[msg.sender] = s1
    }

    function transfer0(address to, int n) {
        require(n > 0 && w0[msg.sender] >= n);
        w0[msg.sender] -= n;
        w0[to] += n
    }

    function transfer1(address to, int n) {
        require(n > 0 && w1[msg.sender] >= n);
        w1[msg.sender] -= n;
        w1[to] += n
    }

    function deposit0(int v) {
        require(v > 0 && w0[msg.sender] >= v);
        c0[msg.sender] += v * 1000 / xr0;
        sc0 += v * 1000 / xr0;
        w0[msg.sender] -= v;
        res0 += v
    }

    // redeems v credits
    function redeem0(int v) {
        require(v > 0 && c0[msg.sender] >= v);
        amt = v * xr0 / 1000;
        require(res0 >= amt);
        c0[msg.sender] -= v;
        sc0 -= v;
        res0 -= amt;
        w0[msg.sender] += amt;
        if (sc0 == 0) { xr0 = 1000 };
        require((c0[msg.sender] * xr0 / 1000 + c1[msg.sender] * p1) * 4
                >= sdebt[msg.sender] * idx / 1000 * 5)
    }

    function deposit1(int v) {
        require(v > 0 && w1[msg.sender] >= v);
        w1[msg.sender] -= v;
        c1[msg.sender] += v
    }

    function redeem1(int v) {
        require(v > 0 && c1[msg.sender] >= v);
        c1[msg.sender] -= v;
        w1[msg.sender] += v;
        require((c0[msg.sender] * xr0 / 1000 + c1[msg.sender] * p1) * 4
                >= sdebt[msg.sender] * idx / 1000 * 5)
    }

    function borrow(int v) {
        require(v > 0 && res0 >= v);
        res0 -= v;
        sdebt[msg.sender] += v * 1000 / idx;
        ssdebt += v * 1000 / idx;
        w0[msg.sender] += v;
        require((c0[msg.sender] * xr0 / 1000 + c1[msg.sender] * p1) * 4
                >= sdebt[msg.sender] * idx / 1000 * 5)
    }

    function repay(int v) {
        require(v > 0 && w0[msg.sender] >= v && sdebt[msg.sender] * idx / 1000 >= v);
        w0[msg.sender] -= v;
        res0 += v;
        sdebt[msg.sender] -= v * 1000 / idx;
        ssdebt -= v * 1000 / idx
    }

    // repays v of the debt of b, and seizes collateral of b worth 1.1 * v
    function liquidate(address b, int v) {
        require(msg.sender != b && v > 0 && w0[msg.sender] >= v
                && sdebt[b] * idx / 1000 >= v);
        require((c0[b] * xr0 / 1000 + c1[b] * p1) * 4 < sdebt[b] * idx / 1000 * 5);
        amt = 11 * v / (10 * p1);
        require(c1[b] >= amt);
        w0[msg.sender] -= v;
        res0 += v;
        sdebt[b] -= v * 1000 / idx;
        ssdebt -= v * 1000 / idx;
        c1[b] -= amt;
        c1[msg.sender] += amt;
        require((c0[b] * xr0 / 1000 + c1[b] * p1) * 4 <= sdebt[b] * idx / 1000 * 5)
    }

    function accrue() {
        require(msg.sender == oracle);
        idx = idx * 11 / 10;
        if (sc0 > 0) { xr0 = (res0 + ssdebt * idx / 1000) * 1000 / sc0 }
    }

    function setPrice(int p) {
        require(msg.sender == oracle && p > 0);
        p1 = p
    }
}

// ------------------------------------------------------------------ invariants

// @groundtruth: True
invariant Nonnegative {
    (forall u : address . w0[u] >= 0 && w1[u] >= 0 && c0[u] >= 0 && c1[u] >= 0
                          && sdebt[u] >= 0)
    && res0 >= 0 && sc0 >= 0 && ssdebt >= 0 && idx >= 1000 && p1 > 0
}

// Only users hold credits and debts; with two users, the totals bound any two of them.
// @groundtruth: True
invariant Totals {
    (forall w : address . !is_EOA(w) -> c0[w] == 0 && sdebt[w] == 0)
    && forall u : address . forall v : address . u != v ->
        (c0[u] + c0[v] <= sc0 && sdebt[u] + sdebt[v] <= ssdebt)
}

// ------------------------------------------------------------------ rules

// @groundtruth: True
rule Health_non_interference {
    forall a : address . forall b : address .
    forall f : method . forall args : calldataargs .
    (is_EOA(a) && a != b && b != oracle
     && (c0[a] * xr0 / 1000 + c1[a] * p1) * 4 >= sdebt[a] * idx / 1000 * 5) ->
    << b : Lending.f(args) >> (c0[a] * xr0 / 1000 + c1[a] * p1) * 4 >= sdebt[a] * idx / 1000 * 5
}

// Repaying the whole debt (sdebt[a] * idx / 1000) may leave a remainder of the scaled debt.
// @groundtruth: False
rule Liquidation_defence {
    forall a : address .
    (is_EOA(a) && (c0[a] * xr0 / 1000 + c1[a] * p1) * 4 < sdebt[a] * idx / 1000 * 5
     && w0[a] >= sdebt[a] * idx / 1000) ->
    exists f : method . exists args : calldataargs .
    << a : Lending.f(args) >>
        forall b : address . forall v : int . << b : Lending.liquidate(a, v) >> lastReverted
}

// @groundtruth: False
rule Liquidation_attack {
    forall a : address . forall b : address .
    (is_EOA(a) && is_EOA(b) && a != b && a != oracle && w0[a] > 0
     && sdebt[b] > 0 && c1[b] > 0 && c0[b] == 0
     && (c0[b] * xr0 / 1000 + c1[b] * p1) * 4 >= sdebt[b] * idx / 1000 * 5) ->
    exists p : int . exists v : int .
    << a : Lending.setPrice(p) >> << a : Lending.liquidate(b, v) >>
    << a : Lending.setPrice(old(old(p1))) >>
        w0[a] + w1[a] * p1 + c0[a] * xr0 / 1000 + c1[a] * p1 - sdebt[a] * idx / 1000 >
        old(old(old(w0[a] + w1[a] * p1 + c0[a] * xr0 / 1000 + c1[a] * p1
                    - sdebt[a] * idx / 1000)))
}

// Rounding: accrue recomputes the exchange rate from rounded values.
// @groundtruth: False
rule Exchange_rate_monotone {
    forall a : address . forall f : method . forall args : calldataargs .
    << a : Lending.f(args) >> xr0 >= old(xr0)
}

// Rounding: a deposit gives v * 1000 / xr0 credits, rounded down.
// @groundtruth: False
rule Net_worth_preserved {
    forall a : address . forall b : address . forall f : method . forall args : calldataargs .
    (f == Lending.deposit0 || f == Lending.redeem0 || f == Lending.deposit1
     || f == Lending.redeem1 || f == Lending.borrow || f == Lending.repay) ->
    << b : Lending.f(args) >>
        w0[a] + w1[a] * p1 + c0[a] * xr0 / 1000 + c1[a] * p1 - sdebt[a] * idx / 1000 ==
        old(w0[a] + w1[a] * p1 + c0[a] * xr0 / 1000 + c1[a] * p1 - sdebt[a] * idx / 1000)
}

// Rounding: redeeming the credits of a deposit gives back less.
// @groundtruth: False
rule Deposit_reversibility {
    forall a : address . forall v : int .
    ((c0[a] * xr0 / 1000 + c1[a] * p1) * 4 >= sdebt[a] * idx / 1000 * 5) ->
    << a : Lending.deposit0(v) >>
        (lastReverted ||
         << a : Lending.redeem0(c0[a] - old(c0[a])) >>
            (w0[a] == old(old(w0[a])) && c0[a] == old(old(c0[a]))))
}

// @groundtruth: True
rule Borrow_safe {
    forall a : address . forall v : int .
    << a : Lending.borrow(v) >>
        (lastReverted || (c0[a] * xr0 / 1000 + c1[a] * p1) * 4 >= sdebt[a] * idx / 1000 * 5)
}

// @groundtruth: True
rule Liquidation_only_unhealthy {
    forall a : address . forall b : address . forall v : int .
    ((c0[b] * xr0 / 1000 + c1[b] * p1) * 4 >= sdebt[b] * idx / 1000 * 5) ->
    << a : Lending.liquidate(b, v) >> lastReverted
}
