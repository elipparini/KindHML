// Milestone D (DESIGN.md, Sect. 7.8): Defence_exists has no cutoff (in its negation, the
// caller b of take is existential under the universal over the arguments); its instance with
// lock(true) has one, and holds for every number of users.
pragma balance real;

contract C {
    mapping (address => bool) locked;

    constructor() {
    }

    function lock(bool x) {
        locked[msg.sender] = x
    }

    function take(address x) {
        require(!locked[x])
    }
}

property Defence_exists {
    forall a : address . is_EOA(a) ->
    exists f : method . exists args : calldataargs .
    << a : C.f(args) >> forall b : address . << b : C.take(a) >> lastReverted
}
