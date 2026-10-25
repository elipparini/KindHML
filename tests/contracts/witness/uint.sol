// Crafted (regression, 2026-10-25): a candidate witness of type int given to a uint parameter
// (witness.candidates offered the int map entries for uint parameters, and the tool proved the
// false property below). The instance f(m[a]) is valid: m[a] < 0, so the call fails its uint
// guard and reverts. The property is false: the arguments of a uint parameter
// range over the naturals (encode_formula.domain), no call of setm or f reverts, and
// setm(-1) reaches a state where m[a] < 0. No cutoff: b is existential under the universal over
// the arguments in the negation.
contract C {
    mapping (address => int) m;
    int k;

    constructor() {
    }

    function setm(int x) {
        m[msg.sender] = x
    }

    function f(uint x) {
        k = k + 1
    }
}

// @groundtruth: False
property Revertible {
    forall a : address .
    (is_EOA(a) && m[a] < 0) ->
    exists g : method . exists args : calldataargs .
    << a : C.g(args) >> (lastReverted && forall b : address . m[b] == m[b])
}
