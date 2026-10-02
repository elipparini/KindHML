// Adapted from: https://github.com/fsainas/contracts-verification-benchmark/tree/main/contracts/vault
// mutation: no wait_time requirement in finalize

contract Vault {
    address owner;
    address recovery;
    uint wait_time;

    address receiver;
    int request_time;
    int amount;
    int state;
    // 0 = IDLE
    // 1 = REQ
   
    constructor (address recovery_, int wait_time_) payable {
    	require(msg.sender != recovery_);
      require(wait_time_ >= 0);
        owner = msg.sender;
        recovery = recovery_;
        wait_time = wait_time_;
        state = 0 // IDLE
    }

    function withdraw(address receiver_, int amount_) {
        require(state == 0); // IDLE
        require(amount_ <= balance);
        require(msg.sender == owner);

        request_time = block.number;
        amount = amount_;
        receiver = receiver_;
        state = 1 // REQ
    }

    function finalize() {
        require(state == 1); // REQ
        require(msg.sender == owner);

        state = 0; // IDLE	
        receiver.transfer(amount)
    }

    function cancel() {
        require(state == 1); // REQ
        require(msg.sender == recovery);
        state = 0 // IDLE
    }
}

// @groundtruth: True
rule Two_steps_drainability {
    (state == 0) ->
    (exists addr: address .
    exists recipient: address .
    exists f1: method .
    exists args1: calldataargs .
    exists msgvalue1 : int .
    exists f2: method .
    exists args2: calldataargs .
    exists msgvalue2 : int .
    exists d1 : uint .
    exists d2 : uint .
    (<< addr : Vault . f1(args1) $ msgvalue1 @ d1 >>
        << addr : Vault . f2(args2) $ msgvalue2 @ d2 >>
              (balance[recipient] ==  old(old(balance[recipient] +balance)))
    ))
}

// Two transactions within less than wait_time blocks do not increase any balance
// (d1, d2: the increases of the block number made by the two transactions).
// @groundtruth: False
rule Two_steps_drainability_non_inflation {
    (state == 0) ->
    forall a : address . forall b : address . forall c : address .
    forall f1 : method . forall f2 : method .
    forall args1 : calldataargs . forall args2 : calldataargs .
    forall msgvalue1 : int . forall msgvalue2 : int .
    forall d1 : uint . forall d2 : uint .
    (d1 + d2 < wait_time) ->
    << a : Vault . f1(args1) $ msgvalue1 @ d1 >>
        << b : Vault . f2(args2) $ msgvalue2 @ d2 >>
            balance[c] == old(old(balance[c]))
}

