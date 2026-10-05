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

// Invariants, proved inductive by the tool and assumed when checking the rules.
// @groundtruth: True
invariant Nonnegative {
    (forall u : address . t0[u] >= 0 && t1[u] >= 0 && minted[u] >= 0)
    && r0 >= 0 && r1 >= 0 && supply >= 0
    && (r0 > 0) == (r1 > 0) && (supply > 0) == (r0 > 0)
}

// Only users hold liquidity, and the minted liquidity of any two addresses is at most the
// supply (with two users, the supply is the sum of the minted liquidity).
// @groundtruth: True
invariant Shares {
    (forall w : address . !is_EOA(w) -> minted[w] == 0)
    && forall u : address . forall v : address . u != v -> minted[u] + minted[v] <= supply
}

// Slippage protection against front-running: whatever transaction an adversary b
// inserts before a's swap, either the swap reverts or a gets at least ymin.
// @groundtruth: True
rule Slippage {
    forall a : address . forall b : address .
    forall f : method . forall args : calldataargs .
    forall x : real . forall ymin : real .
    is_EOA(a) ->
    << b : AMM.f(args) >> << a : AMM.swap0(x, ymin) >>
        (lastReverted || t1[a] >= old(t1[a]) + ymin)
}

// Sandwich attack: if a sells x tokens T0 without slippage protection, an adversary b
// holding tokens T0 can front-run and back-run a's swap and end with more tokens T0
// (and the same tokens T1).
// @groundtruth: True
rule Sandwich {
    forall a : address . forall b : address . forall x : real .
    (is_EOA(a) && is_EOA(b) && a != b && r0 > 0 && r1 > 0 && x > 0 && t0[a] >= x
     && t0[b] > 0) ->
    exists y : real .
    << b : AMM.swap0(y, 0) >> << a : AMM.swap0(x, 0) >>
    << b : AMM.swap1(t1[b] - old(old(t1[b])), 0) >>
        (t0[b] > old(old(old(t0[b]))) && t1[b] == old(old(old(t1[b]))))
}

// Splitting a swap gives the same as a single swap (no incentive to split).
// @groundtruth: True
rule Swap_additivity {
    forall a : address . forall x1 : real . forall x2 : real .
    exists v12 : real . exists v3 : real .
    exists q1 : bool . exists q2 : bool . exists q3 : bool .
    (<< a : AMM.swap0(x1, 0) >> (q1 == lastReverted &&
        << a : AMM.swap0(x2, 0) >> (q2 == lastReverted && v12 == t1[a])))
    && (<< a : AMM.swap0(x1 + x2, 0) >> (q3 == lastReverted && v3 == t1[a]))
    && (q1 || q2 || (!q3 && v12 == v3))
}

// A swap can be undone by the opposite swap of its output.
// @groundtruth: True
rule Swap_reversibility {
    forall a : address . forall x : real .
    << a : AMM.swap0(x, 0) >>
        (lastReverted ||
         << a : AMM.swap1(out1, 0) >>
            (t0[a] == old(old(t0[a])) && t1[a] == old(old(t1[a]))))
}

// A deposit can be undone by redeeming the minted liquidity.
// False here: not the first deposit, which mints the whole supply.
// @groundtruth: False
rule Deposit_reversibility {
    forall a : address . forall x0 : real . forall x1 : real .
    << a : AMM.deposit(x0, x1) >>
        (lastReverted ||
         << a : AMM.redeem(liq) >>
            (t0[a] == old(old(t0[a])) && t1[a] == old(old(t1[a]))))
}

// A liquidity provider can always exit, whatever an adversary does first.
// False here: not the only liquidity provider.
// @groundtruth: False
rule LP_exit {
    forall a : address . forall b : address .
    forall f : method . forall args : calldataargs .
    (is_EOA(a) && a != b && minted[a] > 0) ->
    << b : AMM.f(args) >> << a : AMM.redeem(minted[a]) >>
        (!lastReverted && minted[a] == 0)
}

// No round trip of swaps is profitable (no money pump).
// @groundtruth: True
rule No_money_pump {
    forall a : address . forall x : real . forall y : real .
    << a : AMM.swap0(x, 0) >> << a : AMM.swap1(y, 0) >>
        !(t0[a] > old(old(t0[a])) && t1[a] >= old(old(t1[a])))
}

// Arbitrage: if the AMM price of T0 (r1/r0) is above an external price p, a user holding
// tokens T0 can increase her wealth at price p with a swap.
// @groundtruth: True
rule Arbitrage {
    forall a : address . forall p : real .
    (is_EOA(a) && p > 0 && r0 > 0 && t0[a] > 0 && r1 > p * r0) ->
    exists x : real .
    << a : AMM.swap0(x, 0) >> (p * t0[a] + t1[a] > old(p * t0[a] + t1[a]))
}
