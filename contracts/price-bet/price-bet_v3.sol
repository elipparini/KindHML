contract Bet {

    bool player_has_joined;
    address owner;
    address oracle;
    address player;
    int rate;
    bool player_won

    constructor(address oracle_addr, int initial_rate) payable {
        require(oracle_addr != this);
        require(oracle_addr != null);
        owner = msg.sender;
        oracle = oracle_addr; 
        rate = initial_rate;
        player_has_joined = false;
        player_won = false
    }

    function join() payable {
        require (balance == 2 * msg.value && !player_has_joined) ;
        player = msg.sender ;
        player_has_joined = true 
    }
    function win() {
        require(player_won);
        player.transfer(balance) 
    }
    function set() {
        require (msg.sender == oracle) ;
        player_won = true
    }
}
