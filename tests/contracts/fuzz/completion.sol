// Crafted (2026-11-05, extend.py): Never_target fails only after set(1000003), an amount that
// random values do not hit (no require compares v with a term, so there is no boundary value);
// from any state, the completion query of set finds it. The contract is nonlinear (v * k,
// k * k), so the tool completes its states.

contract C {
    int k;
    int x;

    constructor(int k0) {
        require(k0 > 1);
        k = k0
    }

    function scale() {
        k = k * k
    }

    function set(int v) {
        x = v * k
    }
}

// @groundtruth: False
property Never_target { x != 1000003 * k }

// k > 1 in every reachable state, and k * k >= k then
// @groundtruth: True
property Scale_grows { forall a : address . << a : C.scale() >> (lastReverted || k >= old(k)) }

// lastReverted outside a modality: not completed (it would denote the added transaction)
// @groundtruth: True
property Top_reverted { lastReverted || k > 1 }
