// Disjunctive instances (DESIGN.md, Sect. 7.8): a debtor a defends itself from seize if one
// call of a makes every seize of a revert. No single call does it: with c[a] == 0, the price 1
// makes seize revert by its second require; with c[a] >= 1, the price d[a] * r makes a
// healthy (a product of terms). Defence_cases holds through the disjunction of the two
// instances price(1) and price(d[a] * r), as lending_int_v2 Liquidation_defence.

contract C {
    mapping (address => int) w;     // wallets
    mapping (address => int) c;     // collateral
    mapping (address => int) d;     // debts
    int p;                          // price of the collateral
    int r;                          // interest rate

    constructor(int s) {
        require(s > 0);
        w[msg.sender] = s;
        p = 1;
        r = 1
    }

    function give(address to, int v) {
        require(v > 0 && w[msg.sender] >= v);
        w[msg.sender] -= v;
        w[to] += v
    }

    function put(int v) {
        require(v > 0 && w[msg.sender] >= v);
        w[msg.sender] -= v;
        c[msg.sender] += v
    }

    function owe(int v) {
        require(v > 0);
        d[msg.sender] += v
    }

    function grow() {
        r = r * 2
    }

    function price(int v) {
        require(v > 0);
        p = v
    }

    function seize(address x) {
        require(c[x] * p < d[x] * r);
        require(p >= 2 || c[x] > 0)
    }
}

// @groundtruth: True
invariant Nonnegative {
    (forall u : address . w[u] >= 0 && c[u] >= 0 && d[u] >= 0) && p > 0 && r > 0
}

// @groundtruth: True
property Defence_cases {
    forall a : address . (is_EOA(a) && c[a] * p < d[a] * r) ->
    exists f : method . exists args : calldataargs .
    << a : C.f(args) >> forall b : address . << b : C.seize(a) >> lastReverted
}
