// Adapted from: https://github.com/fsainas/contracts-verification-benchmark/tree/main/contracts/bank
// mutation: withdraws must be previously enabled by the owner

contract Bank {
    mapping (address => int) funds;
    address owner;
    bool withdrawalAllowed;

    constructor() {
        owner = msg.sender;
        withdrawalAllowed = false
    }

    function deposit() payable {
        require(msg.value > 0);
        funds[msg.sender] = funds[msg.sender] + msg.value
    }

    function allow_withdraw() {
        require(msg.sender == owner);
        withdrawalAllowed = true
    }

    function withdraw(int amount) {
        require(amount > 0);
        require(amount <= funds[msg.sender]);
        require(withdrawalAllowed);

        funds[msg.sender] = funds[msg.sender] - amount;
        msg.sender.transfer(amount)
    }
}
