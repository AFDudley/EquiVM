# pragma version ^0.4.3

event OwnershipTransferred:
    previous_owner: indexed(address)
    new_owner: indexed(address)

owner: public(address)

@deploy
def __init__():
    self.owner = msg.sender

@internal
def _check_owner():
    assert msg.sender == self.owner, "not owner"

@external
def transfer_ownership(new_owner: address):
    self._check_owner()
    assert new_owner != empty(address), "zero owner"
    previous: address = self.owner
    self.owner = new_owner
    log OwnershipTransferred(previous_owner=previous, new_owner=new_owner)
