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

// copies of lending-simple-real Liquidation_attack_any with 1, 2 and 3 nested modalities
property Any1 {
    forall a : address . forall b : address .
    (is_EOA(a) && is_EOA(b) && a != b && a != oracle && w0[a] > 0
     && debt[b] > 0 && c1[b] > 0 && c0[b] == 0
     && (c0[b] + c1[b] * p1) * 0.8 >= debt[b]) ->
    exists f1 : method . exists args1 : calldataargs .
    << a : Lending.f1(args1) >>
        w0[a] + w1[a] * p1 + c0[a] + c1[a] * p1 - debt[a] >
        old(w0[a] + w1[a] * p1 + c0[a] + c1[a] * p1 - debt[a])
}

property Any2 {
    forall a : address . forall b : address .
    (is_EOA(a) && is_EOA(b) && a != b && a != oracle && w0[a] > 0
     && debt[b] > 0 && c1[b] > 0 && c0[b] == 0
     && (c0[b] + c1[b] * p1) * 0.8 >= debt[b]) ->
    exists f1 : method . exists args1 : calldataargs .
    exists f2 : method . exists args2 : calldataargs .
    << a : Lending.f1(args1) >> << a : Lending.f2(args2) >>
        w0[a] + w1[a] * p1 + c0[a] + c1[a] * p1 - debt[a] >
        old(old(w0[a] + w1[a] * p1 + c0[a] + c1[a] * p1 - debt[a]))
}

property Any3 {
    forall a : address . forall b : address .
    (is_EOA(a) && is_EOA(b) && a != b && a != oracle && w0[a] > 0
     && debt[b] > 0 && c1[b] > 0 && c0[b] == 0
     && (c0[b] + c1[b] * p1) * 0.8 >= debt[b]) ->
    exists f1 : method . exists args1 : calldataargs .
    exists f2 : method . exists args2 : calldataargs .
    exists f3 : method . exists args3 : calldataargs .
    << a : Lending.f1(args1) >> << a : Lending.f2(args2) >> << a : Lending.f3(args3) >>
        w0[a] + w1[a] * p1 + c0[a] + c1[a] * p1 - debt[a] >
        old(old(old(w0[a] + w1[a] * p1 + c0[a] + c1[a] * p1 - debt[a])))
}
