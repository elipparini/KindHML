// Two modalities with the same record of arguments call set with the same value, so the
// second call reverts (with independent arguments, the property would be true).
contract D {
    int last;

    constructor() {
    }

    function set(int a) {
        require(a != last);
        last = a
    }
}

// @groundtruth: False
property Second_call_succeeds {
    forall u : address . is_EOA(u) ->
    exists f : method . exists x : calldataargs .
    << u : D.f(x) >> << u : D.f(x) >> !lastReverted
}
