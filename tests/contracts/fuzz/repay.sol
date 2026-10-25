// Crafted (2026-10-25, fuzz.boundaries): a debt with interest is repaid in full only by an amount
// equal to debt * rate, a product of two fields, which random amounts do not hit.
pragma balance real;

contract C {
    real debt;
    real rate;
    bool repaid;

    constructor() {
        debt = 0.3;
        rate = 1.1
    }

    function grow() {
        rate = rate * 1.1
    }

    function pay(real v) {
        require(v > 0 && debt * rate >= v);
        debt -= v / rate;
        if (debt == 0) { repaid = true }
    }
}

property Never_repaid { !repaid }
