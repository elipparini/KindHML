// Simplified lending protocol: contracts/lending/lending.sol without interest (the exchange
// rate of the credits and the interest index are 1, so credits are deposits and debts are
// not scaled). a is healthy if (c0[a] + c1[a] * p1) * 0.8 >= debt[a]. The existential rules
// of lending.sol are stated with an explicit strategy, which the tool checks.
pragma balance real;

contract Lending {
    address oracle;
    real p1;                            // price of T1
    mapping (address => real) w0;       // wallets
    mapping (address => real) w1;
    real res0;                          // reserves of T0
    mapping (address => real) c0;       // deposits of T0
    mapping (address => real) c1;       // collateral in T1
    mapping (address => real) debt;     // debts in T0
    real amt;                           // temporary

    constructor(address oracle_, real s0, real s1, real p) {
        require(s0 > 0 && s1 > 0 && p > 0);
        oracle = oracle_;
        p1 = p;
        w0[msg.sender] = s0;
        w1[msg.sender] = s1
    }

    function transfer0(address to, real n) {
        require(n > 0 && w0[msg.sender] >= n);
        w0[msg.sender] -= n;
        w0[to] += n
    }

    function transfer1(address to, real n) {
        require(n > 0 && w1[msg.sender] >= n);
        w1[msg.sender] -= n;
        w1[to] += n
    }

    function deposit0(real v) {
        require(v > 0 && w0[msg.sender] >= v);
        c0[msg.sender] += v;
        w0[msg.sender] -= v;
        res0 += v
    }

    function redeem0(real v) {
        require(v > 0 && c0[msg.sender] >= v && res0 >= v);
        c0[msg.sender] -= v;
        res0 -= v;
        w0[msg.sender] += v;
        require((c0[msg.sender] + c1[msg.sender] * p1) * 0.8 >= debt[msg.sender])
    }

    function deposit1(real v) {
        require(v > 0 && w1[msg.sender] >= v);
        w1[msg.sender] -= v;
        c1[msg.sender] += v
    }

    function redeem1(real v) {
        require(v > 0 && c1[msg.sender] >= v);
        c1[msg.sender] -= v;
        w1[msg.sender] += v;
        require((c0[msg.sender] + c1[msg.sender] * p1) * 0.8 >= debt[msg.sender])
    }

    function borrow(real v) {
        require(v > 0 && res0 >= v);
        res0 -= v;
        debt[msg.sender] += v;
        w0[msg.sender] += v;
        require((c0[msg.sender] + c1[msg.sender] * p1) * 0.8 >= debt[msg.sender])
    }

    function repay(real v) {
        require(v > 0 && w0[msg.sender] >= v && debt[msg.sender] >= v);
        w0[msg.sender] -= v;
        res0 += v;
        debt[msg.sender] -= v
    }

    // repays v of the debt of b, and seizes collateral of b worth 1.1 * v
    function liquidate(address b, real v) {
        require(msg.sender != b && v > 0 && w0[msg.sender] >= v && debt[b] >= v);
        require((c0[b] + c1[b] * p1) * 0.8 < debt[b]);
        amt = 1.1 * v / p1;
        require(c1[b] >= amt);
        w0[msg.sender] -= v;
        res0 += v;
        debt[b] -= v;
        c1[b] -= amt;
        c1[msg.sender] += amt;
        require((c0[b] + c1[b] * p1) * 0.8 <= debt[b])
    }

    function setPrice(real p) {
        require(msg.sender == oracle && p > 0);
        p1 = p
    }
}

// @groundtruth: True
invariant Nonnegative {
    (forall u : address . w0[u] >= 0 && w1[u] >= 0 && c0[u] >= 0 && c1[u] >= 0
                          && debt[u] >= 0)
    && res0 >= 0 && p1 > 0
}

// No user other than the oracle can make a healthy user unhealthy.
// @groundtruth: True
rule Health_non_interference {
    forall a : address . forall b : address .
    forall f : method . forall args : calldataargs .
    (is_EOA(a) && a != b && b != oracle && (c0[a] + c1[a] * p1) * 0.8 >= debt[a]) ->
    << b : Lending.f(args) >> (c0[a] + c1[a] * p1) * 0.8 >= debt[a]
}

// Defence against liquidation (Thm 5.1), with an explicit strategy: repay the whole debt.
// @groundtruth: True
rule Liquidation_defence {
    forall a : address .
    (is_EOA(a) && (c0[a] + c1[a] * p1) * 0.8 < debt[a] && w0[a] >= debt[a]) ->
    << a : Lending.repay(debt[a]) >>
        forall b : address . forall v : real . << b : Lending.liquidate(a, v) >> lastReverted
}

// Liquidation attack (Thm 6.2), with an explicit strategy: set the price to
// debt[b] / (2 * c1[b]) (b becomes unhealthy), liquidate debt[b] / 4, restore the price.
// False here: only the oracle sets the price.
// @groundtruth: False
rule Liquidation_attack {
    forall a : address . forall b : address .
    (is_EOA(a) && is_EOA(b) && a != b && a != oracle && w0[a] >= debt[b] / 4
     && debt[b] > 0 && c1[b] > 0 && c0[b] == 0
     && (c0[b] + c1[b] * p1) * 0.8 >= debt[b]) ->
    << a : Lending.setPrice(debt[b] / (2 * c1[b])) >> << a : Lending.liquidate(b, debt[b] / 4) >>
    << a : Lending.setPrice(old(old(p1))) >>
        w0[a] + w1[a] * p1 + c0[a] + c1[a] * p1 - debt[a] >
        old(old(old(w0[a] + w1[a] * p1 + c0[a] + c1[a] * p1 - debt[a])))
}

// Deposits, redeems, borrows and repays do not change the net worth of anyone.
// @groundtruth: True
rule Net_worth_preserved {
    forall a : address . forall b : address . forall f : method . forall args : calldataargs .
    (f == Lending.deposit0 || f == Lending.redeem0 || f == Lending.deposit1
     || f == Lending.redeem1 || f == Lending.borrow || f == Lending.repay) ->
    << b : Lending.f(args) >>
        w0[a] + w1[a] * p1 + c0[a] + c1[a] * p1 - debt[a] ==
        old(w0[a] + w1[a] * p1 + c0[a] + c1[a] * p1 - debt[a])
}

// A healthy user can undo a deposit.
// @groundtruth: True
rule Deposit_reversibility {
    forall a : address . forall v : real .
    ((c0[a] + c1[a] * p1) * 0.8 >= debt[a]) ->
    << a : Lending.deposit0(v) >>
        (lastReverted ||
         << a : Lending.redeem0(v) >> (w0[a] == old(old(w0[a])) && c0[a] == old(old(c0[a]))))
}

// A borrower is healthy after borrowing.
// @groundtruth: True
rule Borrow_safe {
    forall a : address . forall v : real .
    << a : Lending.borrow(v) >> (lastReverted || (c0[a] + c1[a] * p1) * 0.8 >= debt[a])
}

// Only unhealthy users can be liquidated.
// @groundtruth: True
rule Liquidation_only_unhealthy {
    forall a : address . forall b : address . forall v : real .
    ((c0[b] + c1[b] * p1) * 0.8 >= debt[b]) ->
    << a : Lending.liquidate(b, v) >> lastReverted
}
