// mutation: redeem requires x < supply, so the last liquidity provider cannot exit
// Constant-product AMM (Uniswap v2 style, without fee), adapted from:
// https://github.com/bitbart/contracts-verification-benchmark/tree/main/contracts/amm
// The two tokens T0, T1 are embedded: t0[a] and t1[a] are the wallets of a. The constructor
// mints an initial supply to the deployer; users redistribute it with transfer0/transfer1.
// Amounts are real numbers, as in the theory of AMMs (Bartoletti et al., LMCS 2022); the
// pragma makes the ETH balances real too (unused here), so that the queries are over reals
// only (DESIGN.md, Sect. 6).
pragma balance real;

contract AMM {
    mapping (address => real) t0;
    mapping (address => real) t1;
    real r0;                            // reserves
    real r1;
    real supply;                        // liquidity tokens
    mapping (address => real) minted;
    real liq;                           // temporaries: liquidity minted, amounts paid
    real out0;
    real out1;

    constructor(real s0, real s1) {
        require(s0 > 0 && s1 > 0);
        t0[msg.sender] = s0;
        t1[msg.sender] = s1
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

    function deposit(real x0, real x1) {
        require(x0 > 0 && x1 > 0);
        require(t0[msg.sender] >= x0 && t1[msg.sender] >= x1);
        if (supply == 0) {
            liq = x0
        } else {
            require(r0 > 0 && r0 * x1 == r1 * x0);
            liq = x0 * supply / r0
        };
        minted[msg.sender] += liq;
        supply += liq;
        t0[msg.sender] -= x0;
        t1[msg.sender] -= x1;
        r0 += x0;
        r1 += x1
    }

    function redeem(real x) {
        require(x > 0 && minted[msg.sender] >= x && x < supply);
        out0 = x * r0 / supply;
        out1 = x * r1 / supply;
        minted[msg.sender] -= x;
        supply -= x;
        r0 -= out0;
        r1 -= out1;
        t0[msg.sender] += out0;
        t1[msg.sender] += out1
    }

    // sells x tokens T0 for at least ymin tokens T1
    function swap0(real x, real ymin) {
        require(x > 0 && t0[msg.sender] >= x && r0 > 0 && r1 > 0);
        out1 = x * r1 / (r0 + x);
        require(out1 >= ymin);
        t0[msg.sender] -= x;
        r0 += x;
        r1 -= out1;
        t1[msg.sender] += out1
    }

    // sells x tokens T1 for at least ymin tokens T0
    function swap1(real x, real ymin) {
        require(x > 0 && t1[msg.sender] >= x && r0 > 0 && r1 > 0);
        out0 = x * r0 / (r1 + x);
        require(out0 >= ymin);
        t1[msg.sender] -= x;
        r1 += x;
        r0 -= out0;
        t0[msg.sender] += out0
    }
}
