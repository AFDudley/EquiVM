import Stele.Notation

/-!
# Curve lending Vault, from the pinned Vyper 0.4.3 source and Cancun bytecode

Drafted by `scripts/vy2stele.py`; translation holes are closed below.
The storage capacities and return decoders are configured in `Spec.lean`.
`HANDOFF.md` records the selector/block audit and compiler provenance.
-/

open Stele Stele.Notation

namespace Benchmarks.CurveVault.Syntax

def contractSyntax : ContractDecl := solidity% contract Vault {
  struct EncodedSymbol {
    uint256 size;
    bytes32 data;
  }

  address _borrowed_token;
  address _collateral_token;
  address _amm;
  -- Retain the full stored word when it becomes a transferFrom argument.
  uint256 _controller;
  address _factory;
  uint256 maxSupply;
  string name;
  string symbol;
  mapping(address => mapping(address => uint256)) allowance;
  mapping(address => uint256) balanceOf;
  uint256 totalSupply;
  uint256 precision;
  uint256 transient nonreentrant_lock;

  -- No source constructor: Vyper's creation prefix only copies and returns runtime code.
  constructor() payable { }

  event Transfer(address indexed sender, address indexed receiver, uint256 value);
  event Approval(address indexed owner, address indexed spender, uint256 value);
  event SetMaxSupply(uint256 max_supply);
  event Deposit(address indexed sender, address indexed owner, uint256 assets, uint256 shares);
  event Withdraw(address indexed sender, address indexed receiver, address indexed owner, uint256 assets, uint256 shares);

  function set_max_supply_body(uint256 _max_supply) internal {
    address factory_admin = _factory.admin{view}();
    require(msg.sender == factory_admin || msg.sender == _factory);
    maxSupply = _max_supply;
    emit SetMaxSupply(_max_supply);
  }

  function borrow_apr_body() internal returns (uint256) {
    var __c0 = _amm.rate{view}();
    return (__c0 * ((365 * 86400) as uint256)) as uint256;
  }

  function lend_apr_body() internal returns (uint256) {
    address controller_total_debt = address(_controller);
    uint256 debt = controller_total_debt.total_debt{view}();
    if (debt == 0) {
      return 0;
    }
    var __c1 = _amm.rate{view}();
    uint256 numerator = (((__c1 * 31536000) as uint256) * debt) as uint256;
    var __c2 = _total_assets();
    uint256 gross_apr = numerator / __c2;
    address controller_admin_percentage = address(_controller);
    uint256 admin_pct = controller_admin_percentage.admin_percentage{view}();
    return ((gross_apr * ((1000000000000000000 - admin_pct) as uint256)) as uint256) / 1000000000000000000;
  }

  function asset_body() internal returns (address) {
    return _borrowed_token;
  }

  function totalAssets_body() internal returns (uint256) {
    var __c0 = _total_assets();
    return __c0;
  }

  function pricePerShare_body(bool _is_floor) internal returns (uint256) {
    uint256 supply = totalSupply;
    if (supply == 0) {
      return ((10 ** 18) as uint256) / 1000;
    } else {
      uint256 precision_ = precision;
      var __c0 = _total_assets();
      uint256 numerator = (((10 ** 18) as uint256) * ((((__c0 * precision_) as uint256) + 1) as uint256)) as uint256;
      uint256 denominator = (supply + 1000) as uint256;
      uint256 pps = 0;
      if (_is_floor) {
        pps = numerator / denominator;
      } else {
        var __c1 = math__ceil_div(numerator, denominator);
        pps = __c1;
      }
      require(pps > 0);
      return pps;
    }
  }

  function convertToShares_body(uint256 _assets) internal returns (uint256) {
    var __c0 = _convert_to_shares(_assets, true, type(uint256).max);
    return __c0;
  }

  function convertToAssets_body(uint256 _shares) internal returns (uint256) {
    var __c0 = _convert_to_assets(_shares, true, type(uint256).max);
    return __c0;
  }

  function maxDeposit_body(address _receiver) internal returns (uint256) {
    uint256 max_supply = maxSupply;
    if (max_supply == type(uint256).max) {
      return max_supply;
    } else {
      uint256 assets = _total_assets();
      return ((max_supply > assets ? max_supply : assets) - assets) as uint256;
    }
  }

  function previewDeposit_body(uint256 _assets) internal returns (uint256) {
    var __c0 = _convert_to_shares(_assets, true, type(uint256).max);
    return __c0;
  }

  function deposit_body(uint256 _assets, address _receiver) internal returns (uint256) {
    uint256 controller_word = _controller;
    address controller = address(controller_word);
    uint256 total_assets = _total_assets();
    require(((total_assets + _assets) as uint256) >= 10000);
    uint256 max_supply = maxSupply;
    require(((total_assets + _assets) as uint256) <= max_supply);
    uint256 to_mint = _convert_to_shares(_assets, true, total_assets);
    require(to_mint > 0);
    require(controller.code.length > 0);
    var __ignored_transfer = controller.on_borrowed_token_transfer_in(_assets);
    var __ignored_transfer = tkn_transfer_from(_borrowed_token, uint256(msg.sender), controller_word, _assets);
    var __c2 = _mint(_receiver, to_mint);
    require(controller.code.length > 0);
    var __c3 = controller.save_rate();
    emit Deposit(msg.sender, _receiver, _assets, to_mint);
    return to_mint;
  }

  function maxMint_body(address _receiver) internal returns (uint256) {
    uint256 max_supply = maxSupply;
    if (max_supply == type(uint256).max) {
      return max_supply;
    } else {
      uint256 assets = _total_assets();
      var __c1 = _convert_to_shares((((max_supply > assets ? max_supply : assets) - assets) as uint256), true, type(uint256).max);
      return __c1;
    }
  }

  function previewMint_body(uint256 _shares) internal returns (uint256) {
    var __c0 = _convert_to_assets(_shares, false, type(uint256).max);
    return __c0;
  }

  function mint_body(uint256 _shares, address _receiver) internal returns (uint256) {
    require(_shares > 0);
    uint256 controller_word = _controller;
    address controller = address(controller_word);
    uint256 total_assets = _total_assets();
    uint256 assets = _convert_to_assets(_shares, false, total_assets);
    require(((total_assets + assets) as uint256) >= 10000);
    uint256 max_supply = maxSupply;
    require(((total_assets + assets) as uint256) <= max_supply);
    require(controller.code.length > 0);
    var __ignored_transfer = controller.on_borrowed_token_transfer_in(assets);
    var __ignored_transfer = tkn_transfer_from(_borrowed_token, uint256(msg.sender), controller_word, assets);
    var __c2 = _mint(_receiver, _shares);
    require(controller.code.length > 0);
    var __c3 = controller.save_rate();
    emit Deposit(msg.sender, _receiver, assets, _shares);
    return assets;
  }

  function maxWithdraw_body(address _owner) internal returns (uint256) {
    var __c0 = _convert_to_assets(balanceOf[_owner], true, type(uint256).max);
    var __c1 = _available_balance();
    return __c0 < __c1 ? __c0 : __c1;
  }

  function previewWithdraw_body(uint256 _assets) internal returns (uint256) {
    var __c0 = _convert_to_shares(_assets, false, type(uint256).max);
    return __c0;
  }

  function withdraw_body(uint256 _assets, address _receiver, address _owner) internal returns (uint256) {
    uint256 total_assets = _total_assets();
    require((((total_assets - _assets) as uint256) >= 10000) || (total_assets == _assets));
    uint256 shares = _convert_to_shares(_assets, false, total_assets);
    if (_owner != msg.sender) {
      uint256 allowance_ = allowance[_owner][msg.sender];
      if (allowance_ != type(uint256).max) {
        var __c2 = _approve(_owner, msg.sender, ((allowance_ - shares) as uint256));
      }
    }
    uint256 controller_word = _controller;
    address controller = address(controller_word);
    var __c3 = _burn(_owner, shares);
    require(controller.code.length > 0);
    var __ignored_transfer = controller.on_borrowed_token_transfer_out(_assets);
    var __ignored_transfer = tkn_transfer_from(_borrowed_token, controller_word, uint256(_receiver), _assets);
    require(controller.code.length > 0);
    var __c4 = controller.save_rate();
    emit Withdraw(msg.sender, _receiver, _owner, _assets, shares);
    return shares;
  }

  function maxRedeem_body(address _owner) internal returns (uint256) {
    var __c0 = _available_balance();
    var __c1 = _convert_to_shares(__c0, false, type(uint256).max);
    uint256 __v2 = balanceOf[_owner];
    return __c1 < __v2 ? __c1 : __v2;
  }

  function previewRedeem_body(uint256 _shares) internal returns (uint256) {
    var __c0 = _convert_to_assets(_shares, true, type(uint256).max);
    return __c0;
  }

  function redeem_body(uint256 _shares, address _receiver, address _owner) internal returns (uint256) {
    if (_owner != msg.sender) {
      uint256 allowance_ = allowance[_owner][msg.sender];
      if (allowance_ != type(uint256).max) {
        var __c0 = _approve(_owner, msg.sender, ((allowance_ - _shares) as uint256));
      }
    }
    uint256 total_assets = _total_assets();
    uint256 assets_to_redeem = _convert_to_assets(_shares, true, total_assets);
    require((((total_assets - assets_to_redeem) as uint256) >= 10000) || (total_assets == assets_to_redeem));
    var __c3 = _burn(_owner, _shares);
    uint256 controller_word = _controller;
    address controller = address(controller_word);
    require(controller.code.length > 0);
    var __ignored_transfer = controller.on_borrowed_token_transfer_out(assets_to_redeem);
    var __ignored_transfer = tkn_transfer_from(_borrowed_token, controller_word, uint256(_receiver), assets_to_redeem);
    require(controller.code.length > 0);
    var __c4 = controller.save_rate();
    emit Withdraw(msg.sender, _receiver, _owner, assets_to_redeem, _shares);
    return assets_to_redeem;
  }

  function transferFrom_body(address _from, address _to, uint256 _value) internal returns (bool) {
    uint256 allowance_ = allowance[_from][msg.sender];
    if (allowance_ != type(uint256).max) {
      var __c0 = _approve(_from, msg.sender, ((allowance_ - _value) as uint256));
    }
    var __c1 = _transfer(_from, _to, _value);
    return true;
  }

  function transfer_body(address _to, uint256 _value) internal returns (bool) {
    var __c0 = _transfer(msg.sender, _to, _value);
    return true;
  }

  function approve_body(address _spender, uint256 _value) internal returns (bool) {
    var __c0 = _approve(msg.sender, _spender, _value);
    return true;
  }

  function increaseAllowance_body(address _spender, uint256 _add_value) internal returns (bool) {
    uint256 cached_allowance = allowance[msg.sender][_spender];
    uint256 allowance_ = uint256(cached_allowance + _add_value);
    if (allowance_ < cached_allowance) {
      allowance_ = type(uint256).max;
    }
    if (allowance_ != cached_allowance) {
      var __c0 = _approve(msg.sender, _spender, allowance_);
    }
    return true;
  }

  function decreaseAllowance_body(address _spender, uint256 _sub_value) internal returns (bool) {
    uint256 cached_allowance = allowance[msg.sender][_spender];
    uint256 allowance_ = uint256(cached_allowance - _sub_value);
    if (cached_allowance < allowance_) {
      allowance_ = 0;
    }
    if (allowance_ != cached_allowance) {
      var __c0 = _approve(msg.sender, _spender, allowance_);
    }
    return true;
  }

  function admin_body() internal returns (address) {
    var __c0 = _factory.admin{view}();
    return __c0;
  }

  function _total_assets() internal returns (uint256) {
    address controller_available_balance = address(_controller);
    var __c0 = controller_available_balance.available_balance{view}();
    address controller_total_debt = address(_controller);
    var __c1 = controller_total_debt.total_debt{view}();
    uint256 subtotal = (__c0 + __c1) as uint256;
    address controller_admin_fees = address(_controller);
    var __c2 = controller_admin_fees.admin_fees{view}();
    return (subtotal - __c2) as uint256;
  }

  function math__ceil_div(uint256 x, uint256 y) internal returns (uint256) {
    require(y != 0);
    return (x == 0) ? 0 : uint256((y == 0 ? 0 : (((x - 1) as uint256) / y)) + 1);
  }

  function _convert_to_shares(uint256 _assets, bool _is_floor, uint256 _total_assets) internal returns (uint256) {
    uint256 total_assets = _total_assets;
    if (total_assets == type(uint256).max) {
      var __c0 = _total_assets();
      total_assets = __c0;
    }
    uint256 precision_ = precision;
    uint256 numerator = (((((totalSupply + 1000) as uint256) * _assets) as uint256) * precision_) as uint256;
    uint256 denominator = (((total_assets * precision_) as uint256) + 1) as uint256;
    if (_is_floor) {
      return numerator / denominator;
    } else {
      var __c1 = math__ceil_div(numerator, denominator);
      return __c1;
    }
  }

  function _convert_to_assets(uint256 _shares, bool _is_floor, uint256 _total_assets) internal returns (uint256) {
    uint256 total_assets = _total_assets;
    if (total_assets == type(uint256).max) {
      var __c0 = _total_assets();
      total_assets = __c0;
    }
    uint256 precision_ = precision;
    uint256 numerator = (_shares * ((((total_assets * precision_) as uint256) + 1) as uint256)) as uint256;
    uint256 denominator = (((totalSupply + 1000) as uint256) * precision_) as uint256;
    if (_is_floor) {
      return numerator / denominator;
    } else {
      var __c1 = math__ceil_div(numerator, denominator);
      return __c1;
    }
  }

  function tkn_transfer_from(address token, uint256 _from, uint256 _to, uint256 amount) internal {
    if (amount > 0) {
      bytes payload = abi.encodeWithSelector(transferFrom, _from, _to, amount);
      (bool success, bytes returned) = token.call(payload);
      require(success);
      if (returned.length == 0) {
        require(token.code.length > 0);
      } else {
        bool transferred = abi.decode(returned, (bool));
        require(transferred);
      }
    }
  }

  function _mint(address _to, uint256 _value) internal {
    balanceOf[_to] = ((balanceOf[_to] + _value) as uint256);
    totalSupply = ((totalSupply + _value) as uint256);
    emit Transfer(address(0), _to, _value);
  }

  function _available_balance() internal returns (uint256) {
    address controller_available_balance = address(_controller);
    var __c0 = controller_available_balance.available_balance{view}();
    address controller_admin_fees = address(_controller);
    var __c1 = controller_admin_fees.admin_fees{view}();
    var __c2 = crv_math_sub_or_zero(__c0, __c1);
    return __c2;
  }

  function _approve(address _owner, address _spender, uint256 _value) internal {
    allowance[_owner][_spender] = _value;
    emit Approval(_owner, _spender, _value);
  }

  function _burn(address _from, uint256 _value) internal {
    balanceOf[_from] = ((balanceOf[_from] - _value) as uint256);
    totalSupply = ((totalSupply - _value) as uint256);
    emit Transfer(_from, address(0), _value);
  }

  function _transfer(address _from, address _to, uint256 _value) internal {
    require(_to != address(this) && _to != address(0));
    balanceOf[_from] = ((balanceOf[_from] - _value) as uint256);
    balanceOf[_to] = ((balanceOf[_to] + _value) as uint256);
    emit Transfer(_from, _to, _value);
  }

  function crv_math_sub_or_zero(uint256 a, uint256 b) internal returns (uint256) {
    return uint256((a > b ? a : b) - b);
  }

  function withdraw(uint256 _assets, address _receiver) external returns (uint256) {
    address _owner = msg.sender;
    require(nonreentrant_lock != 1);
    nonreentrant_lock = 1;
    var __r = withdraw_body(_assets, _receiver, _owner);
    nonreentrant_lock = 0;
    return __r;
  }

  function withdraw(uint256 _assets) external returns (uint256) {
    address _receiver = msg.sender;
    address _owner = msg.sender;
    require(nonreentrant_lock != 1);
    nonreentrant_lock = 1;
    var __r = withdraw_body(_assets, _receiver, _owner);
    nonreentrant_lock = 0;
    return __r;
  }

  function withdraw(uint256 _assets, address _receiver, address _owner) external returns (uint256) {
    require(nonreentrant_lock != 1);
    nonreentrant_lock = 1;
    var __r = withdraw_body(_assets, _receiver, _owner);
    nonreentrant_lock = 0;
    return __r;
  }

  function totalAssets() external returns (uint256) {
    require(nonreentrant_lock != 1);
    var __r = totalAssets_body();
    return __r;
  }

  function name() external returns (string memory) {
    uint256 stored_length = name.length;
    -- Wrapped loop bounds accept these corrupted headers as an empty string.
    if (stored_length >= type(uint256).max - 62 && stored_length <= type(uint256).max - 31) {
      return "";
    }
    -- Other oversized headers revert; the top 31 headers necessarily exhaust gas.
    require(stored_length <= 64);
    return name;
  }

  function convertToAssets(uint256 _shares) external returns (uint256) {
    require(nonreentrant_lock != 1);
    var __r = convertToAssets_body(_shares);
    return __r;
  }

  function approve(address _spender, uint256 _value) external returns (bool) {
    require(nonreentrant_lock != 1);
    nonreentrant_lock = 1;
    var __r = approve_body(_spender, _value);
    nonreentrant_lock = 0;
    return __r;
  }

  function previewWithdraw(uint256 _assets) external returns (uint256) {
    require(nonreentrant_lock != 1);
    var __r = previewWithdraw_body(_assets);
    return __r;
  }

  function totalSupply() external returns (uint256) {
    return totalSupply;
  }

  function transferFrom(address _from, address _to, uint256 _value) external returns (bool) {
    require(nonreentrant_lock != 1);
    nonreentrant_lock = 1;
    var __r = transferFrom_body(_from, _to, _value);
    nonreentrant_lock = 0;
    return __r;
  }

  function collateral_token() external returns (address) {
    return _collateral_token;
  }

  function pricePerShare(bool _is_floor) external returns (uint256) {
    require(nonreentrant_lock != 1);
    var __r = pricePerShare_body(_is_floor);
    return __r;
  }

  function pricePerShare() external returns (uint256) {
    bool _is_floor = true;
    require(nonreentrant_lock != 1);
    var __r = pricePerShare_body(_is_floor);
    return __r;
  }

  function amm() external returns (address) {
    return _amm;
  }

  function decimals() external returns (uint8) {
    return 18;
  }

  function asset() external returns (address) {
    require(nonreentrant_lock != 1);
    var __r = asset_body();
    return __r;
  }

  function increaseAllowance(address _spender, uint256 _add_value) external returns (bool) {
    require(nonreentrant_lock != 1);
    nonreentrant_lock = 1;
    var __r = increaseAllowance_body(_spender, _add_value);
    nonreentrant_lock = 0;
    return __r;
  }

  function maxDeposit(address _receiver) external returns (uint256) {
    require(nonreentrant_lock != 1);
    var __r = maxDeposit_body(_receiver);
    return __r;
  }

  function previewRedeem(uint256 _shares) external returns (uint256) {
    require(nonreentrant_lock != 1);
    var __r = previewRedeem_body(_shares);
    return __r;
  }

  function deposit(uint256 _assets, address _receiver) external returns (uint256) {
    require(nonreentrant_lock != 1);
    nonreentrant_lock = 1;
    var __r = deposit_body(_assets, _receiver);
    nonreentrant_lock = 0;
    return __r;
  }

  function deposit(uint256 _assets) external returns (uint256) {
    address _receiver = msg.sender;
    require(nonreentrant_lock != 1);
    nonreentrant_lock = 1;
    var __r = deposit_body(_assets, _receiver);
    nonreentrant_lock = 0;
    return __r;
  }

  function balanceOf(address arg0) external returns (uint256) {
    return balanceOf[arg0];
  }

  function borrowed_token() external returns (address) {
    return _borrowed_token;
  }

  function redeem(uint256 _shares, address _receiver) external returns (uint256) {
    address _owner = msg.sender;
    require(nonreentrant_lock != 1);
    nonreentrant_lock = 1;
    var __r = redeem_body(_shares, _receiver, _owner);
    nonreentrant_lock = 0;
    return __r;
  }

  function redeem(uint256 _shares, address _receiver, address _owner) external returns (uint256) {
    require(nonreentrant_lock != 1);
    nonreentrant_lock = 1;
    var __r = redeem_body(_shares, _receiver, _owner);
    nonreentrant_lock = 0;
    return __r;
  }

  function redeem(uint256 _shares) external returns (uint256) {
    address _receiver = msg.sender;
    address _owner = msg.sender;
    require(nonreentrant_lock != 1);
    nonreentrant_lock = 1;
    var __r = redeem_body(_shares, _receiver, _owner);
    nonreentrant_lock = 0;
    return __r;
  }

  function set_max_supply(uint256 _max_supply) external {
    require(nonreentrant_lock != 1);
    nonreentrant_lock = 1;
    var __r = set_max_supply_body(_max_supply);
    nonreentrant_lock = 0;
  }

  function mint(uint256 _shares, address _receiver) external returns (uint256) {
    require(nonreentrant_lock != 1);
    nonreentrant_lock = 1;
    var __r = mint_body(_shares, _receiver);
    nonreentrant_lock = 0;
    return __r;
  }

  function mint(uint256 _shares) external returns (uint256) {
    address _receiver = msg.sender;
    require(nonreentrant_lock != 1);
    nonreentrant_lock = 1;
    var __r = mint_body(_shares, _receiver);
    nonreentrant_lock = 0;
    return __r;
  }

  function symbol() external returns (string memory) {
    uint256 stored_length = symbol.length;
    if (stored_length >= type(uint256).max - 62 && stored_length <= type(uint256).max - 31) {
      return "";
    }
    require(stored_length <= 64);
    return symbol;
  }

  function decreaseAllowance(address _spender, uint256 _sub_value) external returns (bool) {
    require(nonreentrant_lock != 1);
    nonreentrant_lock = 1;
    var __r = decreaseAllowance_body(_spender, _sub_value);
    nonreentrant_lock = 0;
    return __r;
  }

  function transfer(address _to, uint256 _value) external returns (bool) {
    require(nonreentrant_lock != 1);
    nonreentrant_lock = 1;
    var __r = transfer_body(_to, _value);
    nonreentrant_lock = 0;
    return __r;
  }

  function lend_apr() external returns (uint256) {
    require(nonreentrant_lock != 1);
    var __r = lend_apr_body();
    return __r;
  }

  function previewMint(uint256 _shares) external returns (uint256) {
    require(nonreentrant_lock != 1);
    var __r = previewMint_body(_shares);
    return __r;
  }

  function borrow_apr() external returns (uint256) {
    require(nonreentrant_lock != 1);
    var __r = borrow_apr_body();
    return __r;
  }

  function factory() external returns (address) {
    return _factory;
  }

  function maxMint(address _receiver) external returns (uint256) {
    require(nonreentrant_lock != 1);
    var __r = maxMint_body(_receiver);
    return __r;
  }

  function convertToShares(uint256 _assets) external returns (uint256) {
    require(nonreentrant_lock != 1);
    var __r = convertToShares_body(_assets);
    return __r;
  }

  function maxWithdraw(address _owner) external returns (uint256) {
    require(nonreentrant_lock != 1);
    var __r = maxWithdraw_body(_owner);
    return __r;
  }

  function maxSupply() external returns (uint256) {
    return maxSupply;
  }

  function maxRedeem(address _owner) external returns (uint256) {
    require(nonreentrant_lock != 1);
    var __r = maxRedeem_body(_owner);
    return __r;
  }

  function allowance(address arg0, address arg1) external returns (uint256) {
    return allowance[arg0][arg1];
  }

  function previewDeposit(uint256 _assets) external returns (uint256) {
    require(nonreentrant_lock != 1);
    var __r = previewDeposit_body(_assets);
    return __r;
  }

  function controller() external returns (address) {
    return address(_controller);
  }

  function admin() external returns (address) {
    require(nonreentrant_lock != 1);
    var __r = admin_body();
    return __r;
  }

  function «initialize»(address _amm_, address _controller_, address _borrowed_token_, address _collateral_token_) external {
    require(_borrowed_token == address(0));
    _borrowed_token = _borrowed_token_;
    var __c0 = _borrowed_token_.decimals{view}();
    uint256 borrowed_precision = (10 ** ((18 - __c0) as uint256)) as uint256;
    _collateral_token = _collateral_token_;
    _factory = msg.sender;
    _amm = _amm_;
    _controller = uint256(_controller_);
    precision = borrowed_precision;
    -- Preserve the bounded symbol's encoded data word, including noncanonical
    -- padding: the compiler persists those bytes. The ABI adapter returns its
    -- length and data word, and the storage adapter accepts (length, word bytes).
    EncodedSymbol borrowed_symbol = _borrowed_token_.symbol{view}();
    uint256 symbol_size = borrowed_symbol.size;
    bytes32 symbol_word = borrowed_symbol.data;
    bytes encoded_symbol = abi.encodePacked(bytes32(symbol_word));
    name = tuple(symbol_size + 16,
      abi.encodePacked(string("Curve Vault for "), bytes32(symbol_word), uint128(symbol_size)));
    symbol = tuple(symbol_size + 2,
      abi.encodePacked(string("cv"), bytes32(symbol_word), bytes(encoded_symbol[18 : 32]), uint128(symbol_size)));
    maxSupply = type(uint256).max;
  }

}

end Benchmarks.CurveVault.Syntax
