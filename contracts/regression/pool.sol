// Every number of users (DESIGN.md, Sect. 7.3): Someone_deposited holds for every number of
// users. In the checks with the cutoff, sum(deposit) is a variable; without the witness
// premise of the sum (if the entries at null and at the contracts do not add up to it, a user
// has a nonzero entry), the check of Someone_deposited has the counterexample to induction
// where every entry of the system is 0 and total = sum(deposit) = 1.

contract Pool {
    mapping (address => int) deposit;
    int total;

    constructor () {
        total = 0
    }

    function put(int x) {
        require(x > 0);
        deposit[msg.sender] = deposit[msg.sender] + x;
        total = total + x
    }

    function take() {
        require(deposit[msg.sender] > 0);
        total = total - deposit[msg.sender];
        deposit[msg.sender] = 0
    }
}

// @groundtruth: True
invariant Sum { sum(deposit) == total }

// @groundtruth: True
invariant Nonnegative { forall u : address . deposit[u] >= 0 }

// @groundtruth: True
property Someone_deposited { total == 0 || exists a : address . deposit[a] > 0 }
