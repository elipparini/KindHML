// A value of type calldataargs is a record with one value per parameter of every procedure
// (2026-10-29, with the user), so it does not depend on the order of the quantifiers, and a
// variable may be used in several modalities.
contract C {
    constructor() {
    }

    function g(int a) {
        require(a == 1)
    }

    function h(int b) {
        require(b == 2)
    }
}

// The record with g.a = 1 and h.b = 2 (no single sequence of arguments fits both).
// @groundtruth: True
property Args_outside {
    forall u : address . is_EOA(u) ->
    exists x : calldataargs . forall f : method . << u : C.f(x) >> !lastReverted
}

// @groundtruth: True
property Two_uses {
    forall u : address . is_EOA(u) ->
    exists x : calldataargs . forall f : method .
    (<< u : C.f(x) >> !lastReverted) && (<< u : C.f(x) >> << u : C.f(x) >> !lastReverted)
}
