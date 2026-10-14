# pragma version ^0.4.3

OWNER: immutable(address)
LIMIT: immutable(uint256)
TAG: immutable(bytes4)

@deploy
def __init__(owner: address, limit: uint256, tag: bytes4):
    OWNER = owner
    LIMIT = limit
    TAG = tag

@external
@view
def read() -> (address, uint256, bytes4):
    return OWNER, LIMIT, TAG

@external
@view
def owner() -> address:
    return OWNER

@external
@view
def matches_limit(candidate: uint256) -> bool:
    return candidate == LIMIT
