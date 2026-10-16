contract C4 {
  
  constructor () {
    skip
  }

  function pay(int amount) {
    require (amount<=(balance - 1));
    payable(sender).transfer(amount)
  }
}


property P1_false {
  forall addr : address .
  exists v : int .   
    << addr : C4 . pay(v) $ 0 >>		
      balance[addr] == old(balance[addr]) + 1
}

property P2_true {
  forall addr : address .
  is_EOA(addr) ->
  exists v : int .   
  balance > 1 ->		
    << addr : C4 . pay(v) $ 0 >>
      balance[addr] == old(balance[addr]) + 1
}


property P3_false {
  forall addr : address .
  exists v : int .   
    << addr : C4 . pay(v) $ 0 >>		
      balance[addr] == old(balance[addr]) + (balance - 1)
}

property P4_true {
  forall addr : address .
  is_EOA(addr) ->
  exists v : int .   
  balance > 1 ->		
    << addr : C4 . pay(v) $ 0 >>
      balance[addr] == old(balance[addr]) + (old(balance) - 1)
}


property P5_false {
  forall addr : address .
  exists v : int .   
  << addr : C4 . pay(v) $ 0 >>
    balance[addr] == old(balance[addr]) + (old(balance) - 1)
}


// properties P6 and P7 are the same as P4 and P5 except for the "-1" inside/outside the scope of old()  
property P6_true {
  forall addr : address .
  is_EOA(addr) ->
  exists v : int .   
  balance > 1 ->		
    << addr : C4 . pay(v) $ 0 >>
      balance[addr] == old(balance[addr]) + old(balance - 1)
}


property P7_false {
  forall addr : address .
  exists v : int .   
  << addr : C4 . pay(v) $ 0 >>
    balance[addr] == old(balance[addr]) + old(balance - 1)
}


property P8_true {
  forall addr : address .
  exists v : int .   
  << addr : C4 . pay(v) $ 0 >>
    balance[addr] == old(balance[addr]) + old(balance) - balance
}


property P9_false {
  forall addr : address .
  exists v : int .   
  balance > 1 ->		
    << addr : C4 . pay(v) $ 0 >>
      balance[addr] == old(balance[addr]) + (balance - 1) // note: we are using current balance 
}



property P10_true {
  forall addr : address .
  exists v : int .   
  << addr : C4 . pay(v) $ 0 >>
    !lastReverted ->
    balance[addr] == old(balance[addr]) + old(balance) - 1 
}


property P11_false {
  forall addr : address .
  exists v : int .   
  << addr : C4 . pay(v) $ 0 >>
    lastReverted &&
    balance[addr] == old(balance[addr]) + old(balance) - 1
}


property P12_true {
  forall addr : address .
  is_EOA(addr) ->
  exists v : int .   
  balance > 1 ->		
    << addr : C4 . pay(v) $ 0 >>
      balance[addr] == old(balance[addr]) + old(balance) - 1
}

property P13_false {
  forall addr : address .
  exists v : int .   
  balance > 1 ->		
    << addr : C4 . pay(v) $ 2 >>
      balance[addr] == old(balance[addr]) + old(balance) - 1
}

property P14_true {
  forall addr : address .
  is_EOA(addr) ->
  exists v : int .   
  exists xn : int .   
  balance > 1 ->		
    << addr : C4 . pay(v) $ xn >>
      balance[addr] == old(balance[addr]) + old(balance) - 1
}

property P15_false {
  forall addr : address .
  exists v : int .
  balance > 1 ->		
    << addr : C4 . pay(v) $ v >>
      balance[addr] == old(balance[addr]) + old(balance) - 1
}

/*
property P15_false {
  forall addr : address .
  forall f : method .   
  forall arg1 : calldataargs .
  forall arg2 : calldataargs .
    << addr : C4 . f(arg1) $ 0 >>
      << addr : C4 . wd(args2) $ 0 >>
        balance[addr] == old(balance[addr]) + old(balance) - 1
}*/