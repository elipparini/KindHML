// variant: integer amounts, as in Solidity (divisions round down)
// Simplified lending protocol: contracts/lending-simple-real/lending_simple_real.sol with
// integer amounts. a is healthy if (c0[a] + c1[a] * p1) * 4 >= debt[a] * 5, as in the real
// version; the only rounding is in liquidate, which seizes 11 * v / (10 * p1) tokens T1.

contract Lending {
    address oracle;
    int p1;                             // price of T1
    mapping (address => int) w0;        // wallets
    mapping (address => int) w1;
    int res0;                           // reserves of T0
    mapping (address => int) c0;        // deposits of T0
    mapping (address => int) c1;        // collateral in T1
    mapping (address => int) debt;      // debts in T0
    int amt;                            // temporary

    constructor(address oracle_, int s0, int s1, int p) {
        require(s0 > 0 && s1 > 0 && p > 0);
        oracle = oracle_;
        p1 = p;
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
        c0[msg.sender] += v;
        w0[msg.sender] -= v;
        res0 += v
    }

    function redeem0(int v) {
        require(v > 0 && c0[msg.sender] >= v && res0 >= v);
        c0[msg.sender] -= v;
        res0 -= v;
        w0[msg.sender] += v;
        require((c0[msg.sender] + c1[msg.sender] * p1) * 4 >= debt[msg.sender] * 5)
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
        require((c0[msg.sender] + c1[msg.sender] * p1) * 4 >= debt[msg.sender] * 5)
    }

    function borrow(int v) {
        require(v > 0 && res0 >= v);
        res0 -= v;
        debt[msg.sender] += v;
        w0[msg.sender] += v;
        require((c0[msg.sender] + c1[msg.sender] * p1) * 4 >= debt[msg.sender] * 5)
    }

    function repay(int v) {
        require(v > 0 && w0[msg.sender] >= v && debt[msg.sender] >= v);
        w0[msg.sender] -= v;
        res0 += v;
        debt[msg.sender] -= v
    }

    // repays v of the debt of b, and seizes collateral of b worth 1.1 * v
    function liquidate(address b, int v) {
        require(msg.sender != b && v > 0 && w0[msg.sender] >= v && debt[b] >= v);
        require((c0[b] + c1[b] * p1) * 4 < debt[b] * 5);
        amt = 11 * v / (10 * p1);
        require(c1[b] >= amt);
        w0[msg.sender] -= v;
        res0 += v;
        debt[b] -= v;
        c1[b] -= amt;
        c1[msg.sender] += amt;
        require((c0[b] + c1[b] * p1) * 4 <= debt[b] * 5)
    }

    function setPrice(int p) {
        require(msg.sender == oracle && p > 0);
        p1 = p
    }
}
