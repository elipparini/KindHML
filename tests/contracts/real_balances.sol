// Real balances: balances, values and amounts are real.
pragma balance real;

contract Splitter {
    address a;
    address b;
    int splits;

    constructor(address a_, address b_) {
        require(a_ != b_);
        a = a_;
        b = b_
    }

    function receive() payable { skip }

    function split() {
        a.transfer(balance / 2);
        b.transfer(balance);
        splits += 1
    }

    function give(uint k) {
        a.transfer(k)
    }
}

// @groundtruth: True
rule Split_empties {
    forall u : address . (is_EOA(u) && a != Splitter && b != Splitter) ->
        << u : Splitter.split() >> balance == 0
}

// The two shares are equal (false with integer balances: an odd balance).
// @groundtruth: True
rule Split_is_fair {
    forall u : address . (is_EOA(u) && a != Splitter && b != Splitter) ->
        << u : Splitter.split() >>
            balance[a] - old(balance[a]) == balance[b] - old(balance[b])
}

// a may be the contract itself, and a transfer to oneself reverts.
// @groundtruth: False
rule Split_succeeds {
    forall u : address . is_EOA(u) -> << u : Splitter.split() >> !lastReverted
}

// A non-payable procedure requires the value 0.
// @groundtruth: True
rule Split_not_payable {
    forall u : address . << u : Splitter.split() $ 0.5 >> lastReverted
}

// Payments can be arbitrarily small, if some user has tokens (false with integers).
// @groundtruth: True
rule Small_payment {
    (exists v : address . is_EOA(v) && balance[v] > 0) ->
    exists u : address . exists x : real .
        << u : Splitter.receive() $ x >> (balance > old(balance) && balance < old(balance) + 0.5)
}

// @groundtruth: True
rule Balance_nonnegative {
    balance >= 0 && splits >= 0
}
