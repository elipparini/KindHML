// A transaction may pass null as an address argument (only the sender cannot be null). The
// steps of Houdini once let the parameters range over the addresses but null: Owner_set was
// proved inductive, and Owner_kept valid from it (audit of 2026-10-25). The guard on k keeps
// random testing from finding the call setOwner(null, 91).
contract C {
    address owner;

    constructor() {
        owner = msg.sender
    }

    function setOwner(address a, int k) {
        require(msg.sender == owner);
        require(k * k == 8281);
        owner = a
    }
}

// @groundtruth: False
invariant Owner_set { owner != null }

// After setOwner(null, 91), every call of setOwner reverts.
// @groundtruth: False
property Owner_kept {
    forall u : address . is_EOA(u) -> << u : C.setOwner(u, 91) >> owner != null
}
