// mutation: the constructor does not require a non-null oracle.
// With oracle = null nobody can call set (null sends no transaction), so a rate <= 100 never
// changes.

contract Bet {

    bool player_has_joined;
    address owner;
    address oracle;
    address player;
    int rate

    constructor(address oracle_addr, int initial_rate) payable {
        require(oracle_addr != this);
        owner = msg.sender;
        oracle = oracle_addr;
        rate = initial_rate;
        player_has_joined = false
    }

    function join() payable {
        require (balance == 2 * msg.value && !player_has_joined) ;
        player = msg.sender ;
        player_has_joined = true
    }
    function win() {
        require(rate >100);
        require(player_has_joined);
        player.transfer(balance)
    }

    function set(int x) {
        require (msg.sender == oracle) ;
        rate = x
    }
}
