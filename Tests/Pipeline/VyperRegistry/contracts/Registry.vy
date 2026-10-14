# pragma version ^0.4.3
from lib import ownable

initializes: ownable
exports: (ownable.transfer_ownership, ownable.owner)

struct Entry:
    account: address
    weight: uint256
    active: bool

event Registered:
    id: indexed(uint256)
    account: indexed(address)
    weight: uint256

MAX_ENTRIES: constant(uint256) = 16

entries: public(HashMap[uint256, Entry])
ids: public(DynArray[uint256, MAX_ENTRIES])
nextId: public(uint256)
totalWeight: public(uint256)

@deploy
def __init__():
    ownable.__init__()
    self.nextId = 1

@external
def register(account: address, weight: uint256 = 1) -> uint256:
    ownable._check_owner()
    assert weight > 0, "zero weight"
    id: uint256 = self.nextId
    self.nextId = id + 1
    self.entries[id] = Entry(account=account, weight=weight, active=True)
    self.ids.append(id)
    self.totalWeight += weight
    log Registered(id=id, account=account, weight=weight)
    return id

@external
def deactivate(id: uint256):
    ownable._check_owner()
    entry: Entry = self.entries[id]
    assert entry.active, "inactive"
    self.entries[id].active = False
    self.totalWeight -= entry.weight

@external
def pop_last() -> uint256:
    ownable._check_owner()
    assert len(self.ids) > 0, "empty"
    id: uint256 = self.ids.pop()
    if self.entries[id].active:
        self.totalWeight -= self.entries[id].weight
    self.entries[id] = empty(Entry)
    return id

@external
@view
def active_weight() -> uint256:
    total: uint256 = 0
    for id: uint256 in self.ids:
        if self.entries[id].active:
            total += self.entries[id].weight
    return total

@external
@view
def count() -> uint256:
    return len(self.ids)
