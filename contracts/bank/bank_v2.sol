// Adapted from: https://github.com/fsainas/contracts-verification-benchmark/tree/main/contracts/bank
// mutation: in deposit the contract subtracts 1 from the deposited amount

contract Bank {
    mapping (address => int) funds

    constructor() {
        skip
    }

    function deposit() payable {
        require(msg.value > 0);
        funds[msg.sender] = funds[msg.sender] + msg.value - 1
    }


    function withdraw(int amount) {
        require(amount > 0);
        require(amount <= funds[msg.sender]);

        funds[msg.sender] = funds[msg.sender] - amount;
        msg.sender.transfer(amount)
    }
}
