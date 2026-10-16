// Parameterized mode (DESIGN.md, Sect. 7). The cutoff of the checks is 2. The properties other
// than At_most_two hold for every number of users, and are proved with 2 users (the proof
// of Registered_bounded needs sum(registered) == count). At_most_two holds with at most 2
// users and fails with 3 or more: it is proved with 2 users without parameterized mode,
// and it is not proved in parameterized mode, whatever the number of users.
// Not in tests/contracts, whose properties are checked with 2 users only (test_regressions.py).

contract Registry {
    mapping (address => int) registered;
    int count;

    constructor () {
        count = 0
    }

    function register() {
        require(registered[msg.sender] == 0);
        registered[msg.sender] = 1;
        count = count + 1
    }

    function unregister() {
        require(registered[msg.sender] == 1);
        registered[msg.sender] = 0;
        count = count - 1
    }
}

invariant Flags { forall u : address . registered[u] == 0 || registered[u] == 1 }

property Count_nonnegative { count >= 0 }

property Registered_bounded { forall u : address . registered[u] <= count }

property At_most_two { count <= 2 }
