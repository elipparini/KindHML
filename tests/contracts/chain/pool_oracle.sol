// Crafted (2026-10-25, chain witnesses): pool.sol, but only the oracle sets the price, and the
// attacker a is not the oracle. The property is false: a cannot make the healthy borrower b
// liquidatable, and no other call of a increases its net worth (deposits, withdrawals, loans
// and repayments leave it unchanged; transfers decrease it).
pragma balance real;

contract Pool {
    address oracle;
    real p;                             // price of the collateral token T1
    mapping (address => real) w0;       // wallets of the loan token T0
    mapping (address => real) w1;       // wallets of T1
    mapping (address => real) c;        // collateral in T1
    mapping (address => real) debt;     // debts in T0
    real res;                           // reserves of T0
    real amt;                           // temporary

    constructor(address oracle_, real s0, real s1, real p0) {
        require(s0 > 0 && s1 > 0 && p0 > 0);
        oracle = oracle_;
        p = p0;
        res = s0;
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

    function deposit(real v) {
        require(v > 0 && w1[msg.sender] >= v);
        w1[msg.sender] -= v;
        c[msg.sender] += v
    }

    function withdraw(real v) {
        require(v > 0 && c[msg.sender] >= v);
        c[msg.sender] -= v;
        w1[msg.sender] += v;
        require(c[msg.sender] * p * 0.8 >= debt[msg.sender])
    }

    function borrow(real v) {
        require(v > 0 && res >= v);
        res -= v;
        debt[msg.sender] += v;
        w0[msg.sender] += v;
        require(c[msg.sender] * p * 0.8 >= debt[msg.sender])
    }

    function repay(real v) {
        require(v > 0 && w0[msg.sender] >= v && debt[msg.sender] >= v);
        w0[msg.sender] -= v;
        res += v;
        debt[msg.sender] -= v
    }

    function liquidate(address b, real v) {
        require(msg.sender != b && v > 0 && w0[msg.sender] >= v && debt[b] >= v);
        require(c[b] * p * 0.8 < debt[b]);
        amt = 1.1 * v / p;
        require(c[b] >= amt);
        w0[msg.sender] -= v;
        res += v;
        debt[b] -= v;
        c[b] -= amt;
        c[msg.sender] += amt
    }

    function setPrice(real q) {
        require(q > 0 && msg.sender == oracle);
        p = q
    }
}

// @groundtruth: False
property Attack_any {
    forall a : address . forall b : address .
    (is_EOA(a) && is_EOA(b) && a != b && a != oracle && w0[a] > 0
     && debt[b] > 0 && c[b] > 0 && c[b] * p * 0.8 >= debt[b]) ->
    exists f1 : method . exists args1 : calldataargs .
    exists f2 : method . exists args2 : calldataargs .
    exists f3 : method . exists args3 : calldataargs .
    << a : Pool.f1(args1) >> << a : Pool.f2(args2) >> << a : Pool.f3(args3) >>
        w0[a] + (w1[a] + c[a]) * p - debt[a] >
        old(old(old(w0[a] + (w1[a] + c[a]) * p - debt[a])))
}
