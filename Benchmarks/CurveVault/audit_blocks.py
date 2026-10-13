#!/usr/bin/env python3
"""Render the manually reviewed statement map against every reported runtime block.

The descriptions below are audit findings, not inferred from test coverage.
The source lookup uses source IDs as well as node IDs: imported helper positions
in the generic report otherwise look like unrelated lines of Vault.vy.
"""
from bisect import bisect_right
from pathlib import Path
import csv
import json
import re

directory = Path(__file__).resolve().parent
build = json.loads((directory / "Vault.build.json").read_text())

# Each entry owns instructions up to the next entry. Encoding/copy instructions
# serve the stated operation; they do not introduce memory operations in Solm.
review = [
    (0, "dispatch", "Two-stage perfect hash; compare selector and require calldata size >= 4; otherwise revert at 6768"),
    (73, "dispatch", "Selected record: minimum calldata and zero callvalue; otherwise revert at 8284"),
    (90, "dispatch", "Extract the selected entry and jump; all 46 entries checked in dispatcher.json"),
    (99, "borrowed_token", "Read raw slot 0 and ABI-return address under storageWF"),
    (110, "collateral_token", "Read raw slot 1 and ABI-return address under storageWF"),
    (122, "amm", "Read raw slot 2 and ABI-return address under storageWF"),
    (134, "controller", "Read raw slot 3 and ABI-return address under storageWF"),
    (146, "factory", "Read raw slot 4 and ABI-return address under storageWF"),
    (158, "initialize", "Validate four uint160 calldata words before any state change; no lock"),
    (212, "initialize", "Require borrowed-token slot 0 to be zero"),
    (221, "initialize", "Write borrowed token slot 0; STATICCALL its decimals(); propagate failure as revert"),
    (259, "initialize", "Require at least 32 return bytes, canonical uint8, checked 18-decimals, checked power of 10"),
    (327, "initialize", "Compute precision; write slots 1,4,2,3,15 in that order; STATICCALL token.symbol(); revert on failure"),
    (400, "initialize", "Decode at most 96 bytes: full offset word, nonwrapping offset, logical extent within copied bytes, length <= 32"),
    (476, "initialize", "Construct name value and preserve its raw padding; bounded string assignment guard"),
    (621, "initialize", "Write name header then one/two data words to slots 6,7,8; no clearing beyond written words"),
    (651, "initialize", "Construct symbol value and preserve its raw padding; bounded string assignment guard"),
    (779, "initialize", "Write symbol header then one/two data words to slots 9,10,11"),
    (809, "initialize", "Set slot 5 to MAX_UINT256 and return void"),
    (851, "set_max_supply", "Check transient lock, set it to 1, read factory and STATICCALL admin; revert on call failure"),
    (898, "set_max_supply", "Validate at least 32 return bytes and canonical uint160 admin"),
    (932, "set_max_supply", "Caller equals admin OR (only if false) re-read factory slot 4 and compare; require authorized"),
    (966, "set_max_supply", "Write maxSupply slot 5, emit SetMaxSupply, clear lock, stop"),
    (1020, "borrow_apr", "View lock check; read AMM slot 2; STATICCALL rate and require at least 32 bytes"),
    (1072, "borrow_apr", "Checked rate*31536000, then ABI-return uint256"),
    (1107, "lend_apr", "View lock check; controller total_debt STATICCALL and strict word result; zero debt returns zero"),
    (1194, "lend_apr", "Read AMM and STATICCALL rate; strict word result"),
    (1240, "lend_apr", "Check rate*31536000 then result*debt BEFORE calling _total_assets"),
    (1288, "lend_apr", "Call _total_assets; require nonzero denominator; divide; re-read controller and call admin_percentage"),
    (1360, "lend_apr", "Strict word result; checked WAD-admin_pct, checked gross*net, divide by WAD, return"),
    (1459, "asset", "View lock check; read slot 0; ABI-return address under storageWF"),
    (1479, "totalAssets", "View lock check; call _total_assets; return its uint256"),
    (1506, "pricePerShare", "No-argument entry supplies true; explicit bool entry validates 0 or 1"),
    (1533, "pricePerShare", "View lock check; read supply; zero supply returns 10^15"),
    (1579, "pricePerShare", "Read precision BEFORE _total_assets; checked assets*precision,+1,*10^18; checked supply+1000"),
    (1700, "pricePerShare", "Select floor division or _ceil_div; require positive result; return"),
    (1782, "convertToShares", "View lock check; _convert_to_shares(assets,true,MAX); return"),
    (1859, "convertToAssets", "View lock check; _convert_to_assets(shares,true,MAX); return"),
    (1936, "maxDeposit", "Validate unused receiver; view lock check; read maxSupply; MAX returns immediately"),
    (1986, "maxDeposit", "_total_assets then checked max(maxSupply,assets)-assets; return"),
    (2056, "previewDeposit", "View lock check; _convert_to_shares(assets,true,MAX); return"),
    (2133, "deposit", "Default receiver=caller or validate explicit address; check and set lock"),
    (2173, "deposit", "Cache full controller word; _total_assets; checked addition; require resulting assets >= 10000"),
    (2348, "deposit", "Read maxSupply BEFORE second checked addition; require sum <= maximum"),
    (2498, "deposit", "Convert to shares using cached assets; require nonzero shares"),
    (2666, "deposit", "EXTCODESIZE guard then CALL controller.on_borrowed_token_transfer_in(assets); require success"),
    (2718, "deposit", "Re-read borrowed-token slot 0 AFTER hook; tkn_transfer_from(token,caller,raw controller word,assets)"),
    (2749, "deposit", "_mint(receiver,shares); then controller.save_rate EXTCODESIZE guard/CALL/success"),
    (2816, "deposit", "Emit Deposit(caller,receiver,assets,shares); clear lock; return shares"),
    (2886, "maxMint", "Validate unused receiver; view lock check; maxSupply==MAX returns MAX"),
    (2936, "maxMint", "_total_assets; checked max(maxSupply,assets)-assets; _convert_to_shares with MAX sentinel (repeats asset calls); return"),
    (3060, "previewMint", "View lock check; _convert_to_assets(shares,false,MAX); return"),
    (3136, "mint", "Default receiver=caller or validate address; check and set lock; require shares>0"),
    (3302, "mint", "Cache controller; _total_assets; ceil _convert_to_assets with cached assets; checked sum and minimum 10000"),
    (3518, "mint", "Read maxSupply before second checked sum; require supply limit"),
    (3669, "mint", "Controller transfer-in hook: EXTCODESIZE guard, CALL, success check"),
    (3722, "mint", "Re-read token after hook; transferFrom with cached raw controller word"),
    (3754, "mint", "_mint(receiver,shares); controller.save_rate guard/CALL/success"),
    (3820, "mint", "Emit Deposit, clear lock, return assets"),
    (3890, "maxWithdraw", "Validate owner; view lock; read balance mapping BEFORE _convert_to_assets"),
    (3988, "maxWithdraw", "Call _available_balance AFTER conversion; return min(converted,available)"),
    (4031, "previewWithdraw", "View lock; _convert_to_shares(assets,false,MAX); return"),
    (4107, "withdraw", "Three selector variants bind caller defaults or validate receiver/owner; check and set lock"),
    (4192, "withdraw", "_total_assets; checked subtraction BEFORE short-circuit minimum-or-exact-exhaustion guard"),
    (4381, "withdraw", "Ceil share conversion; if owner differs from caller, read nested allowance"),
    (4506, "withdraw", "For finite allowance, checked subtraction then _approve (write and event)"),
    (4549, "withdraw", "Read/cache full controller word AFTER allowance update, BEFORE _burn"),
    (4578, "withdraw", "Controller transfer-out hook guard/CALL/success"),
    (4630, "withdraw", "Re-read token AFTER hook; transferFrom(raw controller word,receiver,assets)"),
    (4664, "withdraw", "save_rate guard/CALL/success; emit Withdraw; clear lock; return shares"),
    (4783, "maxRedeem", "Validate owner; view lock; _available_balance then ceil _convert_to_shares with MAX sentinel"),
    (4888, "maxRedeem", "Read balance mapping AFTER both helpers; return min(converted,balance)"),
    (4932, "previewRedeem", "View lock; _convert_to_assets(shares,true,MAX); return"),
    (5009, "redeem", "Three selector variants bind caller defaults or validate addresses; check and set lock"),
    (5094, "redeem", "Owner!=caller: read allowance; finite allowance checked subtraction and _approve BEFORE asset calls"),
    (5221, "redeem", "_total_assets then floor asset conversion; checked subtraction before minimum-or-exhaustion guard"),
    (5453, "redeem", "_burn BEFORE reading controller slot 3"),
    (5474, "redeem", "Cache raw controller word; transfer-out hook guard/CALL/success"),
    (5534, "redeem", "Re-read token after hook; transferFrom(raw controller word,receiver,assets)"),
    (5569, "redeem", "save_rate guard/CALL/success; emit Withdraw; clear lock; return assets"),
    (5688, "transferFrom", "Validate both addresses; check and set lock; read nested allowance even if owner==caller"),
    (5804, "transferFrom", "Finite allowance: checked subtraction and _approve BEFORE _transfer"),
    (5845, "transferFrom", "_transfer(from,to,value); clear lock; return true"),
    (5882, "transfer", "Validate recipient; check/set lock; _transfer(caller,to,value); clear lock; return true"),
    (5947, "approve", "Validate spender; check/set lock; _approve(caller,spender,value); clear lock; return true"),
    (6012, "increaseAllowance", "Validate spender; check/set lock; read allowance; WRAPPING addition; overflow clamps to MAX"),
    (6132, "increaseAllowance", "Only changed value calls _approve; clear lock; return true"),
    (6185, "decreaseAllowance", "Validate spender; check/set lock; read allowance; WRAPPING subtraction; underflow clamps to zero"),
    (6273, "decreaseAllowance", "Only changed value calls _approve; clear lock; return true"),
    (6326, "admin", "View lock; read factory; STATICCALL admin; strict uint160 result; ABI-return address"),
    (6414, "maxSupply", "No lock; read slot 5 and return uint256"),
    (6426, "decimals", "No lock; return constant uint8 18"),
    (6437, "name", "No lock; read raw length; checked three-word loop bound (including wrapping headers), header then inline words, ABI string return; see gas audit"),
    (6544, "symbol", "Same getter guard as name permits 0..64, despite declared capacity 34; wrapping empty cases and unavoidable OOG cases; see gas audit"),
    (6651, "allowance", "Validate owner/spender; hash slot12||owner then inner||spender; read and return raw uint256; no lock"),
    (6718, "balanceOf", "Validate owner; hash slot13||owner; read and return uint256; no lock"),
    (6756, "totalSupply", "Read slot14 and return uint256; no lock"),
    (6768, "unmatched selector", "Unconditional empty revert; no source fallback/receive"),
    (6772, "_total_assets", "Read controller; STATICCALL available_balance; require success and >=32 return bytes"),
    (6815, "_total_assets", "Re-read controller; STATICCALL total_debt; strict word result; checked sum BEFORE next call"),
    (6877, "_total_assets", "Re-read controller; STATICCALL admin_fees; strict word result; checked subtraction; return"),
    (6946, "math__ceil_div", "Require y!=0 (revert payload ignored); x==0 returns zero"),
    (7079, "math__ceil_div", "Checked x-1, EVM DIV by known-nonzero y, wrapping +1; return"),
    (7108, "_convert_to_shares", "MAX total-assets sentinel invokes _total_assets; otherwise use supplied value"),
    (7145, "_convert_to_shares", "Read precision then totalSupply; checked supply+1000, times assets, times precision; checked assets*precision+1"),
    (7267, "_convert_to_shares", "Floor division with zero guard or shared ceil helper; return"),
    (7332, "_convert_to_assets", "MAX sentinel invokes _total_assets; otherwise use supplied value"),
    (7369, "_convert_to_assets", "Read precision; checked total_assets*precision,+1,*shares; THEN read supply; checked supply+1000 and times precision"),
    (7491, "_convert_to_assets", "Floor division with zero guard or shared ceil helper; return"),
    (7556, "tkn_transfer_from", "Zero amount skips call; otherwise CALL token.transferFrom with two full address argument words and uint256 amount"),
    (7599, "tkn_transfer_from", "Call failure reverts; successful empty result requires token EXTCODESIZE>0"),
    (7629, "tkn_transfer_from", "Nonempty result requires >=32 bytes, canonical bool 0/1; require true; extra bytes ignored"),
    (7680, "tkn_transfer_from", "Return void"),
    (7682, "_mint", "Hash slot13||recipient; read balance, checked add, WRITE balance BEFORE read/checked-add/write totalSupply; emit Transfer(zero,to,value)"),
    (7791, "crv_math_sub_or_zero", "Return wrapping max(a,b)-b; subtraction is mathematically nonnegative"),
    (7819, "_available_balance", "Read controller; STATICCALL available_balance and validate word"),
    (7862, "_available_balance", "Re-read controller; STATICCALL admin_fees and validate word; shared saturating subtraction helper; return"),
    (7939, "_approve", "Hash slot12||owner then inner||spender; WRITE allowance; emit Approval; return"),
    (8024, "_burn", "Hash slot13||owner; read/checked-subtract/WRITE balance BEFORE read/checked-subtract/write supply; emit Transfer(from,zero,value)"),
    (8133, "_transfer", "Require recipient!=this AND recipient!=zero, short-circuit in that order"),
    (8161, "_transfer", "Hash/read/decrement/WRITE sender balance BEFORE hash/read/increment/write recipient balance; checked arithmetic; emit Transfer; return"),
    (8284, "common revert", "All compiler/source guard failures targeting this block revert"),
    (8288, "dispatcher data", "Five 5-byte headers and 46 7-byte records; copied by dispatcher; never executable"),
]
assert [r[0] for r in review] == sorted({r[0] for r in review})

nodes = {}
for unit in [build["ast"]["ast"]] + build["ast"]["imports"]:
    sid = unit["source_id"]
    path = unit["resolved_path"]
    def walk(node, function=""):
        if isinstance(node, dict):
            if node.get("ast_type") == "FunctionDef":
                function = node["name"]
            if "ast_type" in node and "node_id" in node:
                nodes[(sid, node["node_id"])] = (path, node.get("lineno", 0), function)
            for value in node.values():
                walk(value, function)
        elif isinstance(node, list):
            for value in node:
                walk(value, function)
    walk(unit)

report = (directory / "Vault.report.md").read_text().split("## Runtime basic blocks", 1)[1].split("```", 2)[1]
starts = [r[0] for r in review]
pc_map = build["sourceMap"]["runtime"]["pc_ast_map"]
effects = {"SLOAD", "SSTORE", "TLOAD", "TSTORE", "CALL", "STATICCALL", "EXTCODESIZE", "CALLER", "CALLVALUE", "ADDRESS", "GAS", "RETURN", "REVERT", "STOP", "KECCAK256"}
rows = []
for line in report.splitlines():
    insns = [(int(pc), op) for pc, op in re.findall(r"(?:^|\| )(\d+): ([A-Z0-9_]+)", line)]
    if not insns:
        continue
    pc = insns[0][0]
    if pc >= 8288:
        continue
    descriptions, owners, sources = [], [], []
    for ip, op in insns:
        _, owner, description = review[bisect_right(starts, ip)-1]
        if owner not in owners:
            owners.append(owner)
        if description not in descriptions:
            descriptions.append(description)
        if str(ip) in pc_map:
            source = nodes.get(tuple(pc_map[str(ip)]))
            if source and source not in sources:
                sources.append(source)
    rows.append([pc, insns[-1][0], "; ".join(owners), " | ".join(descriptions),
        "; ".join(f"{ip}:{op}" for ip, op in insns if op in effects or op.startswith("LOG")),
        "; ".join(f"{path}:{n} ({fn})" for path, n, fn in sources)])
assert rows[0][0] == 0 and rows[-1][0] == 8284
with (directory / "block-audit.tsv").open("w") as output:
    writer = csv.writer(output, delimiter="\t")
    writer.writerow(["block_start", "last_instruction", "spec_function", "audited_statement", "effects_in_order", "source_refs"])
    writer.writerows(rows)
    writer.writerow([8288, 8634, "dispatcher data", review[-1][2], "CODECOPY source only", ""])
    writer.writerow(["creation:0", "creation:16", "constructor() payable", "Copy and return runtime bytes from creation offset 17; no guards, storage, calls, events or immutable writes", "CODECOPY; RETURN", "no source constructor"])
    writer.writerow(["creation:17", "creation:8651", "runtime payload", "Unreachable as creation instructions; returned as runtime", "data", ""])
    writer.writerow(["creation:8652", "creation:8716", "compiler metadata", "Unreachable trailer; excluded from returned runtime", "data", ""])
print(f"Audited {len(rows)} executable runtime blocks, all 8288 executable bytes; 347 dispatcher-data bytes; creation prefix and both data regions")
