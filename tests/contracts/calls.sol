// Contract-to-contract calls (unfolding), for the differential tests and the end-to-end tests.
contract Token {
    mapping (address => int) bal;
    int supply;

    function mint(address to, int n) payable {
        require(n > 0);
        bal[to] += n;
        supply += n
    }

    function seen(int b) payable {
        // b is evaluated at the call point, before the transfer of msg.value
        supply = b
    }

    function give(address to, int n) {
        require(bal[msg.sender] >= n);
        bal[msg.sender] -= n;
        bal[to] += n
    }
}

contract Shop {
    int sold;
    address last;

    constructor() payable {
        skip
    }

    function buy(int n) payable {
        require(msg.value == n);
        sold += n;
        last = msg.sender;
        Token.mint(msg.sender, n) $ msg.value
    }

    function fund() payable {
        skip
    }

    function report() {
        Token.seen(balance) $ 1
    }

    function relay(int n) {
        Router.forward(n);
        sold = sold - n
    }
}

contract Router {
    int hops;

    function forward(int n) {
        hops += 1;
        Token.give(this, n)
    }

    function pay(int n) payable {
        Token.mint(msg.sender, 10 / n) $ msg.value
    }
}

// @groundtruth: True
property Buy_mints {
    forall a : address . forall n : int .
    (is_EOA(a) && n > 0 && balance[a] >= n) ->
    << a : Shop . buy(n) $ n >> Token.bal[a] == old(Token.bal[a]) + n
}

// The argument `balance` of Token.seen is evaluated before the transfer of 1 token.
// @groundtruth: True
property Report_sees_balance_at_call_point {
    forall a : address . is_EOA(a) ->
    << a : Shop . report() $ 0 >> (!lastReverted -> Token.supply == old(Shop.balance))
}

// Counterexample: the constructors (Shop's with a positive value), then report().
// @groundtruth: False
property Report_sees_balance_after_transfer {
    forall a : address . is_EOA(a) ->
    << a : Shop . report() $ 0 >> (!lastReverted -> Token.supply == Shop.balance)
}

// Router has no tokens of its own, so Token.give fails.
// @groundtruth: False
property Relay_never_reverts {
    forall a : address . is_EOA(a) ->
    << a : Shop . relay(1) $ 0 >> !lastReverted
}

// Division by zero in an argument reverts the whole transaction.
// @groundtruth: True
property Pay_zero_reverts {
    forall a : address . << a : Router . pay(0) $ 0 >> lastReverted
}
