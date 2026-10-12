// Adapted from: https://github.com/fsainas/contracts-verification-benchmark/tree/main/contracts/bank
// mutation: the contract keeps track of the total funds, with a cap of 100

contract Bank {
    mapping (address => int) funds;
    int total_funds;

    constructor() {
        total_funds = 0
    }

    function deposit() payable {
        require(msg.value > 0);
        funds[msg.sender] = funds[msg.sender] + msg.value;
        total_funds = total_funds + msg.value;
        require(total_funds <= 100)
    }


    function withdraw(int amount) {
        require(amount > 0);
        require(amount <= funds[msg.sender]);
        funds[msg.sender] = funds[msg.sender] - amount;
        total_funds = total_funds - msg.value;
        msg.sender.transfer(amount)
    }
}
