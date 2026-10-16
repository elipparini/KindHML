// Parameterized mode, Lemma 7.6 (DESIGN.md, Sect. 7.4): counterexamples of properties with an
// address existential extend to more users only if they leave enough idle users.

contract Registry {
    mapping (address => int) registered;
    int count;

    constructor () {
        count = 0
    }

    // at most two users register
    function register() {
        require(count < 2);
        require(registered[msg.sender] == 0);
        registered[msg.sender] = 1;
        count = count + 1
    }
}

// False for every number of users (just after the constructor), where every user is idle:
// a counterexample extends to every larger number of users.
property Someone_registered { exists u : address . registered[u] == 1 }

// False with 2 users (both registered), true with 3 or more: a counterexample has no idle
// user, and must not be extended.
property Someone_unregistered { exists u : address . is_EOA(u) && registered[u] == 0 }
