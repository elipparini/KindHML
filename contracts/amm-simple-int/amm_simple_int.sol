// variant: integer amounts, as in Solidity (divisions round down)
// Simplified constant-product AMM: the swaps of contracts/amm-real/amm_real.sol, without liquidity
// tokens (the constructor creates the pool with the reserves x0, x1). The existential properties
// of amm_real.sol (Sandwich, Arbitrage) are stated with an explicit strategy, which the tool
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
