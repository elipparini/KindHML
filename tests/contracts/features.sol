// A contract exercising the constructs of the language, for the differential tests.
contract Features {
    int x;
    uint u;
    bool flag;
    address who;
    mapping (address => bool) seen;
    mapping (address => address) next;
    mapping (address => uint) credit;

    constructor(address w, uint u0) payable {
        who = w;
        u = u0
    }

    function nested(int a, int b) {
        if (a > b) {
            if (a > 2 * b) { x = a; flag = true } else { x = b }
        } else {
            x = x + 1;
            u = u - 1;
            seen[msg.sender] = true
        }
    }

    function divide(int d) {
        x = x / d;
        u += x % 2
    }

    function pay(address to, uint n) payable {
        require(seen[msg.sender] || msg.value > 0);
        credit[to] += n;
        next[msg.sender] = to;
        if (credit[to] > 3) to.transfer(n)
    }

    function refund() {
        require(credit[msg.sender] > 0);
        credit[msg.sender] -= 1;
        payable(msg.sender).transfer(1)
    }

    function self() {
        this.transfer(0)
    }
}

// @groundtruth: True
rule Trivial { true }
