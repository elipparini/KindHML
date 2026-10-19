// Parameterized mode, sums as state variables (DESIGN.md, Sect. 7.3): the liquidity shares of
// the AMM (contracts/amm-real), reduced. Pairs is inductive with Total and Nonnegative; its
// step for redeem needs 3 users, and is valid only with the bound of the sum of all the entries
// by sum(minted): the bounds of single entries and of pairs of entries admit minted[u] = 2 for
// three users with sum(minted) = supply = 4, from which a redeem of 2 breaks Pairs.

contract Pool {
    mapping (address => int) minted;
    int supply;

    constructor () {
        supply = 0
    }

    function deposit(int x) {
        require(x > 0);
        minted[msg.sender] += x;
        supply += x
    }

    function redeem(int x) {
        require(x > 0 && minted[msg.sender] >= x);
        minted[msg.sender] -= x;
        supply -= x
    }
}

invariant Nonnegative { (forall u : address . minted[u] >= 0) && minted[null] == 0 }

invariant Total { sum(minted) == supply }

invariant Pairs {
    forall u : address . forall v : address . u != v -> minted[u] + minted[v] <= supply
}
