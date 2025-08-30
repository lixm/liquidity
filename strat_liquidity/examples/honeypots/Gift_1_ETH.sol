// contract address: 0xd8993F49F372BB014fB088eaBec95cfDC795CBF6

// SPDX-License-Identifier: MIT
pragma solidity ^0.8.0;

contract Gift_1_ETH {
    bool public passHasBeenSet = false;
    bytes32 public hashPass;

    // 1. get passwork hash
    function GetHash(bytes memory pass) public pure returns (bytes32) {
        return keccak256(pass);
    }

    // 2. set password (hash)
    function SetPass(bytes32 hash) public payable {
        require(!passHasBeenSet, "Password has already been set");
        require(msg.value >= 1 ether, "At least 1 ETH required");

        hashPass = hash;
        passHasBeenSet = true;
    }

    // 3. get the reward
    function GetGift(bytes memory pass) public returns (bytes32) {
        require(hashPass != 0, "Password not set yet");
        if (hashPass == keccak256(pass)) {
            uint256 amount = address(this).balance;
            payable(msg.sender).transfer(amount);
        }
        return keccak256(pass);
    }

    // 4. lock the password
    function PassHasBeenSet(bytes32 hash) public {
        if (hash == hashPass) {
            passHasBeenSet = true;
        }
    }

    // 5. query the balance
    function contractBalance() public view returns (uint256) {
        return address(this).balance;
    }
}
