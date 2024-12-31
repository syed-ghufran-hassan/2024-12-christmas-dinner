//SPDX-License-Identifier: MIT

pragma solidity >=0.6.2 <0.9.0;

import {Test, console} from "forge-std/Test.sol";
import {ChristmasDinner} from "../src/ChristmasDinner.sol";
import {ERC20Mock} from "../lib/openzeppelin-contracts/contracts/mocks/token/ERC20Mock.sol";

contract ChristmasDinnerTest is Test {
    ChristmasDinner cd;
    ERC20Mock wbtc;
    ERC20Mock weth;
    ERC20Mock usdc;

    uint256 constant DEADLINE = 7;
    address deployer = makeAddr("deployer");
    address user1;
    address user2;
    address user3;

    function setUp() public {
        wbtc = new ERC20Mock();
        weth = new ERC20Mock();
        usdc = new ERC20Mock();
        vm.startPrank(deployer);
        cd = new ChristmasDinner(address(wbtc), address(weth), address(usdc));
        vm.warp(1);
        cd.setDeadline(DEADLINE);
        vm.stopPrank();
        _makeParticipants();
    }

    ////////////////////////////////////////////////////////////////
    //////////////////    Deadline Shenenigans     /////////////////
    ////////////////////////////////////////////////////////////////

    // Try resetting Deadline
    function test_tryResettingDeadlineAsHost() public {
        vm.startPrank(deployer);
        cd.setDeadline(8 days);
        vm.stopPrank();
    }

    function test_participationStatusToggleBeforeAndAfterDeadline() public {
        vm.startPrank(user1);
        cd.deposit(address(weth), 1e18);

        // Initial status should be true
        assertEq(cd.getParticipationStatus(user1), true);

        // Toggle status to false before deadline
        cd.changeParticipationStatus();
        assertEq(cd.getParticipationStatus(user1), false);

        // Toggle status back to true before deadline
        cd.changeParticipationStatus();
        assertEq(cd.getParticipationStatus(user1), true);

        // Advance time to after the deadline
        vm.warp(1 + 8 days);

        // Attempt to toggle status after deadline
        vm.expectRevert();
        cd.changeParticipationStatus();
        assertEq(cd.getParticipationStatus(user1), true);

        vm.stopPrank();
    }


    function test_settingDeadlineAsUser() public {
        vm.startPrank(user1);
        vm.expectRevert();
        cd.setDeadline(3);
        vm.stopPrank();
    }

    // Refund Scenarios
    function test_refundAfterDeadline() public {
        uint256 depositAmount = 1e18;
        vm.startPrank(user1);
        cd.deposit(address(wbtc), depositAmount);
        assertEq(wbtc.balanceOf(address(cd)), depositAmount);
        vm.warp(1 + 8 days);
        vm.expectRevert();
        cd.refund();
        vm.stopPrank();
        assertEq(wbtc.balanceOf(address(cd)), depositAmount);
    }

    function test_refundWithinDeadline() public {
        uint256 depositAmount = 1e18;
        uint256 userBalanceBefore = weth.balanceOf(user1);
        vm.startPrank(user1);
        cd.deposit(address(weth), depositAmount);
        assertEq(weth.balanceOf(address(cd)), depositAmount);
        assertEq(weth.balanceOf(user1), userBalanceBefore - depositAmount);
        vm.warp(1 + 3 days);
        cd.refund();
        assertEq(weth.balanceOf(address(cd)), 0);
        assertEq(weth.balanceOf(user1), userBalanceBefore);
    }

    function test_refundWithEther() public {
        address payable _cd = payable(address(cd));
        vm.deal(user1, 10e18);
        vm.prank(user1);
        (bool sent,) = _cd.call{value: 1e18}("");
        require(sent, "transfer failed");
        assertEq(user1.balance, 9e18);
        assertEq(address(cd).balance, 1e18);
        vm.prank(user1);
        cd.refund();
        assertEq(user1.balance, 10e18);
        assertEq(address(cd).balance, 0);
    }

    // Change Participation Status Scenarios
    function test_participationStatusAfterDeadlineToFalse() public {
        vm.startPrank(user1);
        cd.deposit(address(weth), 1e18);
        assertEq(cd.getParticipationStatus(user1), true);
        vm.warp(1 + 8 days);
        cd.changeParticipationStatus();
        assertEq(cd.getParticipationStatus(user1), false);
    }

    function test_participationStatusAfterDeadlineToTrue() public {
        vm.startPrank(user1);
        cd.deposit(address(weth), 1e18);
        assertEq(cd.getParticipationStatus(user1), true);
        cd.changeParticipationStatus();
        assertEq(cd.getParticipationStatus(user1), false);
        vm.warp(1 + 8 days);
        vm.expectRevert();
        cd.changeParticipationStatus();
        assertEq(cd.getParticipationStatus(user1), false);
    }

    function test_participationStatusBeforeDeadline() public {
        vm.startPrank(user1);
        cd.deposit(address(weth), 1e18);
        assertEq(cd.getParticipationStatus(user1), true);
        cd.changeParticipationStatus();
        assertEq(cd.getParticipationStatus(user1), false);
    }

    // Deposit Scenarios
    function test_depositBeforeDeadline() public {
        vm.warp(1 + 3 days);
        vm.startPrank(user1);
        cd.deposit(address(wbtc), 1e18);
        assertEq(wbtc.balanceOf(user1), 1e18);
        assertEq(wbtc.balanceOf(address(cd)), 1e18);
        vm.stopPrank();
    }

    function test_depositAfterDeadline() public {
        vm.warp(1 + 8 days);
        vm.startPrank(user1);
        vm.expectRevert();
        cd.deposit(address(wbtc), 1e18);
        vm.stopPrank();
    }

    function test_depositNonWhitelistedToken() public {
        ERC20Mock usdt = new ERC20Mock();
        usdt.mint(user1, 1e19);
        vm.startPrank(user1);
        usdt.approve(address(cd), type(uint256).max);
        vm.expectRevert();
        cd.deposit(address(usdt), 1e18);
        vm.stopPrank();
    }

    function test_depositGenerousAdditionalContribution() public {
        vm.startPrank(user1);
        cd.deposit(address(wbtc), 1e18);
        cd.deposit(address(weth), 2e18);
        assertEq(weth.balanceOf(address(cd)), 2e18);
        assertEq(wbtc.balanceOf(address(cd)), 1e18);
    }

    function test_depositEther() public {
        address payable _cd = payable(address(cd));
        vm.deal(user1, 10e18);
        vm.prank(user1);
        (bool sent,) = _cd.call{value: 1e18}("");
        require(sent, "transfer failed");
        assertEq(user1.balance, 9e18);
        assertEq(address(cd).balance, 1e18);
    }

    ////////////////////////////////////////////////////////////////
    ////////////////// Access Controll Shenenigans /////////////////
    ////////////////////////////////////////////////////////////////

    // Change Host Scenarios
    function test_changeHostFail() public {
        vm.startPrank(user1);
        vm.expectRevert();
        cd.changeHost(user1);
        vm.stopPrank();
    }

    function test_changeHostFailNonParticipant() public {
        vm.startPrank(deployer);
        vm.expectRevert();
        cd.changeHost(user1);
        vm.stopPrank();
    }

    function test_changeHostSuccess() public {
        vm.startPrank(user1);
        cd.deposit(address(wbtc), 1e18);
        vm.stopPrank();
        vm.startPrank(deployer);
        cd.changeHost(user1);
        vm.stopPrank();
        address newHost = cd.getHost();
        assertEq(newHost, user1);
    }

    // Withdraw Scenarios
    function test_withdrawAsNonHost() public {
        vm.startPrank(user2);
        cd.deposit(address(weth), 1e18);
        vm.stopPrank();
        vm.startPrank(user1);
        vm.expectRevert();
        cd.withdraw();
        vm.stopPrank();
    }

    function test_withdrawAsHost() public {
        uint256 wethAmount;
        uint256 wbtcAmount;
        uint256 usdcAmount;
        vm.startPrank(user1);
        cd.deposit(address(wbtc), 0.5e18);
        wbtcAmount += 0.5e18;
        cd.deposit(address(weth), 2e18);
        wethAmount += 2e18;
        vm.stopPrank();
        vm.startPrank(user2);
        cd.deposit(address(usdc), 2e18);
        usdcAmount += 2e18;
        cd.deposit(address(wbtc), 1e18);
        wbtcAmount += 1e18;
        vm.stopPrank();
        vm.startPrank(deployer);
        cd.withdraw();
        vm.stopPrank();
        assertEq(wbtc.balanceOf(deployer), wbtcAmount);
        assertEq(weth.balanceOf(deployer), wethAmount);
        assertEq(usdc.balanceOf(deployer), usdcAmount);
    }

     function test_withdrawWithNoBalances() public {
        // Start as the deployer (host)
        vm.startPrank(deployer);
        
        // Attempt to withdraw when there are no balances in the contract
        cd.withdraw();
        
        // Assert that no reverts occurred and balances remain zero
        assertEq(wbtc.balanceOf(deployer), 0);
        assertEq(weth.balanceOf(deployer), 0);
        assertEq(usdc.balanceOf(deployer), 0);
        assertEq(wbtc.balanceOf(address(cd)), 0);
        assertEq(weth.balanceOf(address(cd)), 0);
        assertEq(usdc.balanceOf(address(cd)), 0);
        
        vm.stopPrank();
    }

    function test_setDeadlineZeroDays() public {
   // Start as the deployer (host)
    vm.startPrank(deployer);

    // Get the current timestamp
    uint256 currentTimestamp = block.timestamp;

    // Set the deadline to 0 days
    cd.setDeadline(0);

    // Retrieve the deadline from the contract
    uint256 deadline = cd.deadline();

    // Assert that the deadline is correctly set to block.timestamp
    assertEq(deadline, currentTimestamp);

    // Additional assertions:
    // Ensure an action that depends on the deadline reverts
    vm.expectRevert(); // Match the revert message from your modifier
   

    vm.stopPrank();
}

// Test Ether deposit and refund
function test_depositAndRefundEther() public {
     address payable _cd = payable(address(cd));
    
    // Check initial balances
    uint256 initialUserBalance = user1.balance;
    uint256 initialContractBalance = address(cd).balance;

    // Log the initial balances
    console.log("Initial user balance: ", initialUserBalance);
    console.log("Initial contract balance: ", initialContractBalance);

    // Ensure no underflow before giving Ether to user1
    require(initialUserBalance >= 0, "Initial user balance cannot be negative");

    // Give some Ether to user1
    vm.deal(user1, 10e18);

    // Log user balance after receiving Ether
    console.log("User balance after receiving 10 ETH: ", user1.balance);
    
    // Ensure no overflow before depositing Ether
    require(user1.balance == initialUserBalance + 10e18, "User balance after deposit is incorrect");

    // User deposits Ether into the contract
    vm.prank(user1);
    (bool sent,) = _cd.call{value: 1e18}("");
    require(sent, "Ether transfer failed");

    // Assert contract's balance after deposit
    uint256 contractBalanceAfterDeposit = address(cd).balance;
    require(contractBalanceAfterDeposit == initialContractBalance + 1e18, "Contract balance after deposit is incorrect");

    // Log contract balance after deposit
    console.log("Contract balance after deposit: ", contractBalanceAfterDeposit);
    
    // Assert user balance after deposit
    uint256 userBalanceAfterDeposit = user1.balance;
    require(userBalanceAfterDeposit == initialUserBalance + 10e18 - 1e18, "User balance after deposit is incorrect");

    // Log user balance after deposit
    console.log("User balance after deposit: ", userBalanceAfterDeposit);

    // Refund Ether
    vm.prank(user1);
    cd.refund();

    // Assert contract balance after refund
    uint256 contractBalanceAfterRefund = address(cd).balance;
    require(contractBalanceAfterRefund == 0, "Contract balance after refund is incorrect");

    // Log contract balance after refund
    console.log("Contract balance after refund: ", contractBalanceAfterRefund);

    // Assert user balance after refund (user should get refunded)
    uint256 finalUserBalance = user1.balance;
    require(finalUserBalance == initialUserBalance + 10e18, "User balance after refund is incorrect");
    
    // Log final user balance after refund
    console.log("Final user balance after refund: ", finalUserBalance);

}


// Test refund with Ether after the deadline (should fail)
function test_refundWithEtherAfterDeadline() public {
    // Ensure no overflow or underflow before transferring Ether
    vm.deal(user1, 10e18); // Give user1 10 ETH
    uint256 initialBalance = user1.balance;
    address payable _cd = payable(address(cd));

    // Log initial balance
    console.log("Initial user1 balance:", initialBalance);

    // Send 1e18 Ether to the contract from user1
    vm.prank(user1);
    (bool sent,) = _cd.call{value: 1e18}("");
    require(sent, "Transfer failed");

    // Check balances after the transfer to ensure no underflow occurred
    uint256 newUserBalance = user1.balance;
    uint256 contractBalance = address(cd).balance;
    
    // Log balances after transfer
    console.log("New user1 balance after transfer:", newUserBalance);
    console.log("Contract balance after deposit:", contractBalance);

    require(newUserBalance == initialBalance - 1e18, "Balance after transfer is incorrect");
    require(contractBalance == 1e18, "Contract balance after deposit is incorrect");

    // Set a deadline before the warp
    uint256 daysToDeadline = 7; // You can set this to a value less than 8 days for testing purposes
    cd.setDeadline(daysToDeadline);

    // Log the deadline being set
    console.log("Deadline set to:", block.timestamp + 8 days);

    // Warp time past the deadline
    vm.warp(block.timestamp + 8 days);

    // Attempt to refund after the deadline (should fail)
    vm.startPrank(user1);
    vm.expectRevert("BeyondDeadline()");
    cd.refund();
    vm.stopPrank();

    // Log contract balance after refund attempt
    uint256 finalContractBalance = address(cd).balance;
    console.log("Contract balance after refund attempt:", finalContractBalance);

    // Contract balance should remain the same since refund failed
    require(finalContractBalance == 1e18, "Contract balance changed unexpectedly");

    // Ensure user1's balance is still correct (check for underflow/overflow)
    uint256 finalUserBalance = user1.balance;
    console.log("User1 final balance:", finalUserBalance);

    require(finalUserBalance == newUserBalance, "User's balance changed unexpectedly");
}

// Test for front-running deposit
function test_frontRunningDeposit() public {
      uint256 depositAmount = 1e18;
    
    // User1 deposits first
    vm.startPrank(user1);
    console.log("User1 depositing %s WBTC", depositAmount);
    cd.deposit(address(wbtc), depositAmount);
    assertEq(wbtc.balanceOf(address(cd)), depositAmount);
    console.log("User1 deposit successful, WBTC balance of contract: %s", wbtc.balanceOf(address(cd)));
    vm.stopPrank();

    // User2 tries to deposit a higher amount, simulating front-running
    uint256 frontRunAmount = 2e18;
    vm.startPrank(user2);
    console.log("User2 attempting to front-run with a deposit of %s WBTC", frontRunAmount);
    cd.deposit(address(wbtc), frontRunAmount);
    assertEq(wbtc.balanceOf(address(cd)), depositAmount + frontRunAmount);
    console.log("User2 deposit successful, WBTC balance of contract: %s", wbtc.balanceOf(address(cd)));
    vm.stopPrank();
}

function test_frontRunningTakeEntireBalanceWithRefund() public {
    uint256 depositAmount = 1e18;
    
    // User1 deposits first
    vm.startPrank(user1);
    console.log("User1 depositing %s WBTC", depositAmount);
    cd.deposit(address(wbtc), depositAmount);
    assertEq(wbtc.balanceOf(address(cd)), depositAmount);
    console.log("User1 deposit successful, WBTC balance of contract: %s", wbtc.balanceOf(address(cd)));
    vm.stopPrank();

    // User2 tries to front-run with a higher deposit amount
    uint256 frontRunAmount = 2e18;
    vm.startPrank(user2);
    console.log("User2 attempting to front-run with a deposit of %s WBTC", frontRunAmount);
    cd.deposit(address(wbtc), frontRunAmount);
    assertEq(wbtc.balanceOf(address(cd)), depositAmount + frontRunAmount);
    console.log("User2 deposit successful, WBTC balance of contract: %s", wbtc.balanceOf(address(cd)));
    vm.stopPrank();

    // User2 attempts to refund the entire balance
  //  uint256 contractBalance = wbtc.balanceOf(address(cd));
    console.log("User2 attempting to refund the entire contract balance of %s WBTC", wbtc.balanceOf(address(cd)));

    // Refund attempt
    vm.startPrank(user2);
    cd.refund();  // Assuming refund is implemented in your contract
    uint256 finalBalance = wbtc.balanceOf(address(cd));
    console.log("User2 refunded the entire contract balance, WBTC balance of contract: %s", finalBalance);
    
    // Check if the contract balance is 0 after refund
  //  assertEq(finalBalance, 0, "Refund failed, contract balance not zero");
    
    // Assert User2's balance after refund
    uint256 user2BalanceAfterRefund = wbtc.balanceOf(user2);
    console.log("User2's balance after refund: %s WBTC", user2BalanceAfterRefund);
    assertEq(user2BalanceAfterRefund, frontRunAmount, "User2's refund balance mismatch");

    uint256 user1BalanceAfterRefund = wbtc.balanceOf(user1);
    console.log("User1's balance after refund: %s WBTC", user1BalanceAfterRefund);
    assertEq(user1BalanceAfterRefund, depositAmount, "User1's balance mismatch");

    vm.stopPrank();

}


function test_backRunningTakeEntireBalanceWithRefund1() public {
  // Simulate deposit and refund setup
    vm.deal(address(user1), 2 ether); // Provide 2 ether to user1
   // cd.setRefund(address(user1), 1 ether); // Simulate refund amount

    uint256 initialUserBalance = address(user1).balance;

    // Simulate refund logic
    vm.prank(address(user1)); // Set msg.sender to user1
    cd.refund();

    // Assert final balances
    uint256 refundAmount = 1 ether;
    uint256 expectedBalance = initialUserBalance + refundAmount;
    uint256 finalBalance = address(user1).balance;

    console.log("Initial User1 Balance:", initialUserBalance);
    console.log("Refund Amount:", refundAmount);
    console.log("Final User1 Balance:", finalBalance);
    console.log("Expected Balance:", expectedBalance);

    assertEq(finalBalance, expectedBalance, "User1's balance mismatch after refund");
}

function test_backRunningTakeEntireBalanceWithRefund() public {
    uint256 depositAmount = 1e18;

// User1 deposits first
vm.startPrank(user1);
console.log("User1 depositing %s WBTC", depositAmount);
cd.deposit(address(wbtc), depositAmount);
assertEq(wbtc.balanceOf(address(cd)), depositAmount);
console.log("User1 deposit successful, WBTC balance of contract: %s", wbtc.balanceOf(address(cd)));
vm.stopPrank();

// Now User2 attempts to back-run by observing User1's deposit
uint256 backRunAmount = 2e18; // Assume User2 decides to deposit more to take advantage
vm.startPrank(user2);
console.log("User2 back-running with a deposit of %s WBTC", backRunAmount);
cd.deposit(address(wbtc), backRunAmount);
assertEq(wbtc.balanceOf(address(cd)), depositAmount + backRunAmount);
console.log("User2 deposit successful, WBTC balance of contract: %s", wbtc.balanceOf(address(cd)));
vm.stopPrank();

// Now, User2 attempts to refund the entire balance
uint256 contractBalanceBeforeRefund = wbtc.balanceOf(address(cd));
console.log("User2 attempting to refund the entire contract balance of %s WBTC", contractBalanceBeforeRefund);

// Refund attempt by User2
vm.startPrank(user2);
cd.refund();  // User2 should receive a proportional refund
uint256 user2BalanceAfterRefund = wbtc.balanceOf(user2);
console.log("User2's balance after refund: %s WBTC", user2BalanceAfterRefund);

// Calculate expected refund for User2 based on their proportion of the total deposit
uint256 expectedUser2Refund = (contractBalanceBeforeRefund * backRunAmount) / (depositAmount + backRunAmount);
assertEq(user2BalanceAfterRefund, expectedUser2Refund, "User2's refund balance mismatch");

// Now User1 attempts to refund their own balance
vm.startPrank(user1);
cd.refund();  // User1 should also receive a proportional refund
uint256 user1BalanceAfterRefund = wbtc.balanceOf(user1);
console.log("User1's balance after refund: %s WBTC", user1BalanceAfterRefund);

// Calculate expected refund for User1 based on their proportion of the total deposit
uint256 expectedUser1Refund = (contractBalanceBeforeRefund * depositAmount) / (depositAmount + backRunAmount);
assertEq(user1BalanceAfterRefund, expectedUser1Refund, "User1's balance mismatch after refund");

// Check if contract balance is zero after refund
uint256 finalContractBalance = wbtc.balanceOf(address(cd));
assertEq(finalContractBalance, 0, "Refund failed, contract balance not zero");

vm.stopPrank();
}






// Test for front-running participation status
function test_frontRunningParticipationStatus() public {
    uint256 depositAmount = 1e18;

    // User1 deposits and is the first to participate
    vm.startPrank(user1);
    cd.deposit(address(weth), depositAmount);
    cd.changeParticipationStatus(); // User1 changes status to participate
    assertEq(cd.getParticipationStatus(user1), true);
    vm.stopPrank();

    // Simulate User2 trying to change the participation status before the deadline
    vm.startPrank(user2);
    cd.deposit(address(weth), depositAmount);  // User2 also deposits to join
    cd.changeParticipationStatus(); // User2 tries to participate
    assertEq(cd.getParticipationStatus(user2), true);
    vm.stopPrank();

    // User1 attempts to change status after User2, simulating a front-run situation
    vm.startPrank(user1);
    cd.changeParticipationStatus();  // User1 tries to change status again
    assertEq(cd.getParticipationStatus(user1), false); // Should fail if front-run by User2
    vm.stopPrank();
}




    ////////////////////////////////////////////////////////////////
    //////////////////    Internal Helper Elves    /////////////////
    ////////////////////////////////////////////////////////////////

    function _makeParticipants() internal {
        user1 = makeAddr("user1");
        wbtc.mint(user1, 2e18);
        weth.mint(user1, 2e18);
        usdc.mint(user1, 2e18);
        vm.startPrank(user1);
        wbtc.approve(address(cd), 2e18);
        weth.approve(address(cd), 2e18);
        usdc.approve(address(cd), 2e18);
        vm.stopPrank();
        user2 = makeAddr("user2");
        wbtc.mint(user2, 2e18);
        weth.mint(user2, 2e18);
        usdc.mint(user2, 2e18);
        vm.startPrank(user2);
        wbtc.approve(address(cd), 2e18);
        weth.approve(address(cd), 2e18);
        usdc.approve(address(cd), 2e18);
        vm.stopPrank();
        user3 = makeAddr("user3");
        wbtc.mint(user3, 2e18);
        weth.mint(user3, 2e18);
        usdc.mint(user3, 2e18);
        vm.startPrank(user3);
        wbtc.approve(address(cd), 2e18);
        weth.approve(address(cd), 2e18);
        usdc.approve(address(cd), 2e18);
        vm.stopPrank();
    }
}
