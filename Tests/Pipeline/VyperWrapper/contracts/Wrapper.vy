# pragma version ^0.4.3

interface IERC20:
    def balanceOf(owner: address) -> uint256: view
    def transfer(to: address, amount: uint256) -> bool: nonpayable
    def transferFrom(sender: address, to: address, amount: uint256) -> bool: nonpayable

interface IHook:
    def onWrap(account: address, amount: uint256): nonpayable

event Wrapped:
    account: indexed(address)
    amount: uint256

event Unwrapped:
    account: indexed(address)
    amount: uint256

TOKEN: immutable(address)
hook: public(address)
shares: public(HashMap[address, uint256])
totalShares: public(uint256)

@deploy
def __init__(token: address):
    TOKEN = token

@external
def setHook(target: address):
    assert self.hook == empty(address), "hook set"
    self.hook = target

@external
def wrap(amount: uint256) -> uint256:
    assert amount > 0, "zero"
    ok: bool = extcall IERC20(TOKEN).transferFrom(msg.sender, self, amount)
    assert ok, "transfer failed"
    minted: uint256 = amount
    held: uint256 = staticcall IERC20(TOKEN).balanceOf(self)
    if self.totalShares > 0 and held > amount:
        minted = amount * self.totalShares // (held - amount)
    self.shares[msg.sender] += minted
    self.totalShares += minted
    if self.hook != empty(address):
        extcall IHook(self.hook).onWrap(msg.sender, minted)
    log Wrapped(account=msg.sender, amount=minted)
    return minted

@external
def unwrap(sharesOut: uint256) -> uint256:
    assert self.shares[msg.sender] >= sharesOut, "insufficient"
    held: uint256 = staticcall IERC20(TOKEN).balanceOf(self)
    amount: uint256 = sharesOut * held // self.totalShares
    self.shares[msg.sender] -= sharesOut
    self.totalShares -= sharesOut
    ok: bool = extcall IERC20(TOKEN).transfer(msg.sender, amount)
    assert ok, "transfer failed"
    log Unwrapped(account=msg.sender, amount=amount)
    return amount

@external
@view
def token() -> address:
    return TOKEN

@external
@view
def previewUnwrap(sharesOut: uint256) -> uint256:
    if self.totalShares == 0:
        return 0
    held: uint256 = staticcall IERC20(TOKEN).balanceOf(self)
    return sharesOut * held // self.totalShares
