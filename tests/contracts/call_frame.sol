// The arguments of a contract call are evaluated in the frame of the caller, at the call point
// (Lemma `lem:statements` with frames): msg.sender and msg.value are those of the caller, and
// balance is the caller's before the callee pays it back, for the differential tests and the
// end-to-end tests.
contract Store {
    address who;
    int paid;
    int seen;

    function fund() payable {
        skip
    }

    function save(address w, int p, int b) payable {
        msg.sender.transfer(msg.value + 1);
        who = w;
        paid = p;
        seen = b
    }
}

contract Caller {
    function run() payable {
        Store.save(msg.sender, msg.value, balance) $ 1
    }
}

// In the callee, msg.sender is Caller, msg.value is 1, and the balance of Caller has grown by 1.
// @groundtruth: True
property Run_reads_the_caller_frame {
    forall a : address . forall n : int . (is_EOA(a) && n >= 0) ->
    << a : Caller . run() $ n >>
    (!lastReverted -> (Store.who == a && Store.paid == n && Store.seen == old(Caller.balance) + n))
}
