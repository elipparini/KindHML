// mutation: a deadline is added, and the win function is only callable before the deadline.

contract Bet {

    bool player_has_joined;
    address owner;
    address oracle;
    address player;
    int rate;
    int deadline

    constructor(address oracle_addr, int initial_rate, int _timeout) payable {
        require(oracle_addr != this);
        require(oracle_addr != null);
        require(_timeout > 0);
        owner = msg.sender;
        oracle = oracle_addr; 
        rate = initial_rate ;
        deadline = block.number + _timeout
    }

    function join() payable {
        require (balance == 2 * msg.value && !player_has_joined) ;
        player = msg.sender ;
        player_has_joined = true 
    }
    function win() {
        require(rate >100);
        require(player_has_joined);
        require(block.number < deadline);
        player.transfer(balance) 
    }

    function set(int x) {
        require (msg.sender == oracle) ;
        rate = x 
    }
}
