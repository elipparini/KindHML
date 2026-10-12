// version: anyone can set the price (a manipulable on-chain oracle, e.g. the price of an AMM)
// Lending protocol in the style of Aave and Compound, after the model of
// M. Bartoletti, E. Lipparini, "A theory of Lending Protocols in DeFi" (arXiv 2506.15295),
// and the use case of https://github.com/bitbart/contracts-verification-benchmark (FC26).
// Two embedded tokens (wallets w0, w1): T0 can be deposited, redeemed, borrowed and repaid,
// and is the numeraire (price 1); T1 is collateral only, with price p1 set by the oracle.
// Deposits of T0 give credits c0, redeemed at the exchange rate xr0 = (res0 + debts) / sc0
// (1 if there are no credits). Debts accrue interest through an index (Aave): the debt of
// a is sdebt[a] * idx, and accrue() multiplies idx by 1.1 (the oracle calls it, as the
// environment). a is healthy if (c0[a] * xr0 + c1[a] * p1) * 0.8 >= sdebt[a] * idx
// (liquidation threshold 0.8). A liquidator repays v of the debt of an unhealthy b and
// receives collateral of b worth 1.1 * v (liquidation reward 1.1), but cannot make b
// healthy. Amounts are real numbers, as in the paper.
pragma balance real;

contract Lending {
    address oracle;
    real p1;                            // price of T1
    mapping (address => real) w0;       // wallets
    mapping (address => real) w1;
    real res0;                          // reserves of T0
    mapping (address => real) c0;       // credits in T0
    real sc0;                           // total credits
    real xr0;                           // exchange rate of the credits
    mapping (address => real) c1;       // collateral in T1
    mapping (address => real) sdebt;    // scaled debts in T0
    real ssdebt;                        // total scaled debt
    real idx;                           // interest index
    real amt;                           // temporary

    constructor(address oracle_, real s0, real s1, real p) {
        require(s0 > 0 && s1 > 0 && p > 0);
        oracle = oracle_;
        p1 = p;
        idx = 1;
        xr0 = 1;
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
        c0[msg.sender] += v / xr0;
        sc0 += v / xr0;
        w0[msg.sender] -= v;
        res0 += v
    }

    // redeems v credits
    function redeem0(real v) {
        require(v > 0 && c0[msg.sender] >= v);
        amt = v * xr0;
        require(res0 >= amt);
        c0[msg.sender] -= v;
        sc0 -= v;
        res0 -= amt;
        w0[msg.sender] += amt;
        if (sc0 == 0) { xr0 = 1 };
        require((c0[msg.sender] * xr0 + c1[msg.sender] * p1) * 0.8 >= sdebt[msg.sender] * idx)
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
        require((c0[msg.sender] * xr0 + c1[msg.sender] * p1) * 0.8 >= sdebt[msg.sender] * idx)
    }

    function borrow(real v) {
        require(v > 0 && res0 >= v);
        res0 -= v;
        sdebt[msg.sender] += v / idx;
        ssdebt += v / idx;
        w0[msg.sender] += v;
        require((c0[msg.sender] * xr0 + c1[msg.sender] * p1) * 0.8 >= sdebt[msg.sender] * idx)
    }

    function repay(real v) {
        require(v > 0 && w0[msg.sender] >= v && sdebt[msg.sender] * idx >= v);
        w0[msg.sender] -= v;
        res0 += v;
        sdebt[msg.sender] -= v / idx;
        ssdebt -= v / idx
    }

    // repays v of the debt of b, and seizes collateral of b worth 1.1 * v
    function liquidate(address b, real v) {
        require(msg.sender != b && v > 0 && w0[msg.sender] >= v && sdebt[b] * idx >= v);
        require((c0[b] * xr0 + c1[b] * p1) * 0.8 < sdebt[b] * idx);
        amt = 1.1 * v / p1;
        require(c1[b] >= amt);
        w0[msg.sender] -= v;
        res0 += v;
        sdebt[b] -= v / idx;
        ssdebt -= v / idx;
        c1[b] -= amt;
        c1[msg.sender] += amt;
        require((c0[b] * xr0 + c1[b] * p1) * 0.8 <= sdebt[b] * idx)
    }

    function accrue() {
        require(msg.sender == oracle);
        idx = idx * 1.1;
        if (sc0 > 0) { xr0 = (res0 + ssdebt * idx) / sc0 }
    }

    function setPrice(real p) {
        require(p > 0);
        p1 = p
    }
}

// ------------------------------------------------------------------ invariants
