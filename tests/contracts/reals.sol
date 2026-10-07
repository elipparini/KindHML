// Real fields, mappings and parameters, with integer balances: conversions from int to
// real, division of reals (guarded against 0), and integer division converted to real.
contract Pool {
    real rate;
    real total;
    int count;
    mapping (address => real) share;

    constructor(real r) {
        require(r > 0);
        rate = r
    }

    function deposit(real a) {
        require(a > 0);
        share[msg.sender] += a;
        total = total + a;
        count += 1
    }

    function scale(real k) {
        rate = rate / k
    }

    function average() {
        require(count > 0);
        rate = total / count
    }

    function halve(int n) {
        rate = n / 2
    }
}

// @groundtruth: True
rule Total_nonnegative {
    total >= 0 && count >= 0
}

// The total is the sum of the shares (sum over all addresses).
// @groundtruth: True
invariant Shares_total {
    sum(share) == total
}

// @groundtruth: False
rule Rate_positive {
    rate > 0
}

// The division of reals is exact.
// @groundtruth: True
rule Scale_halves {
    forall u : address . is_EOA(u) ->
        << u : Pool.scale(2) >> rate == old(rate) / 2
}

// A division by 0 reverts.
// @groundtruth: True
rule Scale_by_nonzero_succeeds {
    forall u : address . forall k : real . (is_EOA(u) && k != 0) ->
        << u : Pool.scale(k) >> !lastReverted
}

// @groundtruth: False
rule Scale_succeeds {
    forall u : address . forall k : real . is_EOA(u) ->
        << u : Pool.scale(k) >> !lastReverted
}

// n / 2 is the integer division (3 / 2 = 1), then converted to real.
// @groundtruth: True
rule Halve_is_integer_division {
    forall u : address . is_EOA(u) -> << u : Pool.halve(3) >> rate == 1
}

// @groundtruth: False
rule Halve_is_real_division {
    forall u : address . is_EOA(u) -> << u : Pool.halve(3) >> rate == 1.5
}

// Deposits can be arbitrarily small (false with integers).
// @groundtruth: True
rule Small_deposit {
    exists u : address . exists a : real .
        << u : Pool.deposit(a) >> (total > old(total) && total < old(total) + 0.001)
}

// @groundtruth: True
rule Average_succeeds {
    forall u : address . (is_EOA(u) && count > 0) ->
        << u : Pool.average() >> !lastReverted
}
