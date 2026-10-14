# pragma version ^0.4.3
"""
@title Ether vault
@notice Deposits are credited to the sender; withdrawals pay out with `send`.
"""

event Deposited:
    account: indexed(address)
    amount: uint256

event Withdrawn:
    account: indexed(address)
    amount: uint256

OWNER: immutable(address)
FEE_BPS: constant(uint256) = 25

balances: public(HashMap[address, uint256])
totalDeposits: public(uint256)
feesCollected: public(uint256)
paused: public(bool)

@deploy
def __init__():
    OWNER = msg.sender

@external
@payable
def deposit():
    assert not self.paused, "paused"
    assert msg.value > 0, "zero deposit"
    fee: uint256 = msg.value * FEE_BPS // 10000
    credited: uint256 = msg.value - fee
    self.balances[msg.sender] += credited
    self.totalDeposits += credited
    self.feesCollected += fee
    log Deposited(account=msg.sender, amount=credited)

@external
@nonreentrant
def withdraw(amount: uint256):
    assert self.balances[msg.sender] >= amount, "insufficient"
    self.balances[msg.sender] -= amount
    self.totalDeposits -= amount
    send(msg.sender, amount)
    log Withdrawn(account=msg.sender, amount=amount)

@external
def setPaused(flag: bool):
    assert msg.sender == OWNER, "not owner"
    self.paused = flag

@external
@nonreentrant
def collectFees() -> uint256:
    assert msg.sender == OWNER, "not owner"
    amount: uint256 = self.feesCollected
    self.feesCollected = 0
    send(OWNER, amount)
    return amount

@external
@view
def owner() -> address:
    return OWNER

@external
@view
def available(account: address) -> uint256:
    return min(self.balances[account], self.balance)
