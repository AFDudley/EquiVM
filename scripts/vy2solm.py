#!/usr/bin/env python3
"""Draft a Solm specification in `solidity%` surface syntax from the Vyper 0.4 annotated AST.

Input is the annotated AST Vyper emits (``vyper -f annotated_ast``: the ``ast`` map of
``<Name>.build.json`` written by ``scaffold.py compile --vyper``, or a single
``<Name>.vy.ast.json``).  Output is a ``SpecSyntax.lean`` draft: storage (persistent and
transient, in the compiler's layout order when ``<Name>.storage.json`` is present), structs,
immutables, events, the constructor (module ``__init__`` calls become internal calls), every
selector (one transition per default-argument variant, public getters generated, module exports
included), the fallback, and the internal functions they reach (module functions included, with
the module alias as a name prefix).

What the draft encodes mechanically:
  * Vyper's checked arithmetic as ``(a op b) as T`` from the static type of each operation, and
    ``unsafe_*`` builtins as wrapping casts ``T(a op b)``;
  * ``convert`` as range assertions (``as T``) or casts, by the source and target types;
  * ``assert``/``raise`` as ``require``; ``@nonreentrant`` as the compiler's lock protocol around an
    internal ``<f>_body`` (transient slot on Cancun and later, a storage word before);
  * ``extcall``/``staticcall`` bound as ``var r = x.f{view}(args)`` with Vyper's EXTCODESIZE guard
    for calls without return data, ``send``/``raw_call`` as low-level value calls;
  * ``for … in range(...)`` with its bound checks, ``for … in list`` as an index loop;
  * calls in expression position hoisted into ``var __cN = …`` bindings before the statement.

What it cannot know goes into HOLES (``abi_encode``/``abi_decode``, ``create_*``, decimals,
bytes/list literals, ``extract32``, ``sha256``, ``ecrecover``, …).  Each hole is a ``${hole "…"}``
splice, which fails to elaborate until replaced; ``--comment-holes`` writes them as comments
instead so the rest of the file can be checked.  The agent's audit against the bytecode report
still decides storage read order, compiler guards, and everything the compiler optimised.

Example:
  scripts/vy2solm.py Examples/VyperImmutable --namespace Examples.VyperImmutable \
      --output Examples/VyperImmutable/SpecSyntax.lean --spec-json Examples/VyperImmutable/Immutable.spec.json
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from sol2solm import Hole, Stmts, ident, unparen  # noqa: E402

EVM_VERSIONS = ["istanbul", "berlin", "paris", "shanghai", "cancun", "prague", "osaka"]
COMPARE = {"Lt": "<", "LtE": "<=", "Gt": ">", "GtE": ">=", "Eq": "==", "NotEq": "!="}
CHECKED = {"Add": "+", "Sub": "-", "Mult": "*", "Pow": "**"}
BITWISE = {"BitAnd": "&", "BitOr": "|", "BitXor": "^", "LShift": "<<", "RShift": ">>"}
ENV_VARS = {
    ("msg", "sender"): "msg.sender", ("msg", "value"): "msg.value", ("msg", "data"): "msg.data",
    ("tx", "origin"): "tx.origin", ("tx", "gasprice"): "tx.gasprice",
    ("block", "timestamp"): "block.timestamp", ("block", "number"): "block.number",
    ("block", "coinbase"): "block.coinbase", ("block", "gaslimit"): "block.gaslimit",
    ("block", "prevrandao"): "block.prevrandao", ("block", "difficulty"): "block.prevrandao",
    ("block", "basefee"): "block.basefee", ("chain", "id"): "block.chainid",
}
WEI_UNITS = {"wei": 1, "femtoether": 10 ** 3, "kwei": 10 ** 3, "babbage": 10 ** 3,
             "picoether": 10 ** 6, "mwei": 10 ** 6, "lovelace": 10 ** 6,
             "nanoether": 10 ** 9, "gwei": 10 ** 9, "shannon": 10 ** 9,
             "microether": 10 ** 12, "szabo": 10 ** 12, "milliether": 10 ** 15, "finney": 10 ** 15,
             "ether": 10 ** 18, "kether": 10 ** 21, "grand": 10 ** 21, "mether": 10 ** 24,
             "gether": 10 ** 27, "tether": 10 ** 30}
LOCK_NAME = "nonreentrant_lock"


# ------------------------------------------------------------------------------------ types

@dataclass(frozen=True)
class VType:
    """A Vyper type, from an annotated ``type`` dict or from a declaration annotation."""
    kind: str                      # int bool address bytesM bytes string dynarray sarray hashmap
                                   # struct interface flag tuple decimal void
    name: str = ""                 # struct/interface/flag name, or the elementary name
    bits: int = 0                  # int width, or bytesM width in bytes
    signed: bool = False
    length: int = 0                # capacity of dynarray/bytes/string, length of sarray
    key: "VType | None" = None
    value: "VType | None" = None
    members: tuple = ()            # tuple component types
    decl: tuple | None = None      # (source_id, node_id) of a struct/interface/flag definition

    @property
    def is_int(self) -> bool:
        return self.kind == "int"

    @property
    def surface_int(self) -> str:
        return f"{'int' if self.signed else 'uint'}{self.bits}"

    @property
    def lo(self) -> int:
        return -(1 << (self.bits - 1)) if self.signed else 0

    @property
    def hi(self) -> int:
        return (1 << (self.bits - 1)) - 1 if self.signed else (1 << self.bits) - 1


def int_type(bits: int, signed: bool) -> VType:
    return VType("int", f"{'int' if signed else 'uint'}{bits}", bits, signed)


UINT256 = int_type(256, False)
BOOL = VType("bool", "bool")
ADDRESS = VType("address", "address")


def decl_key(d: dict | None) -> tuple | None:
    return (d.get("source_id", 0), d.get("node_id", 0)) if d else None


def type_of_dict(d: dict | None) -> VType | None:
    """The VType of an annotated AST ``type`` dict."""
    if not d:
        return None
    if "type_t" in d:
        return None   # a type used as a value (struct constructor, convert target)
    tc = d.get("typeclass")
    name = d.get("name", "")
    if tc == "integer":
        return int_type(d["bits"], d["is_signed"])
    if tc == "bytes_m":
        return VType("bytesM", name, d["m"])
    if tc == "bytes":
        return VType("bytes", "bytes", length=d.get("length", 0))
    if tc == "string":
        return VType("string", "string", length=d.get("length", 0))
    if tc == "dynamic_array":
        return VType("dynarray", "DynArray", length=d["length"], value=type_of_dict(d["value_type"]))
    if tc == "static_array":
        return VType("sarray", "$SArray", length=d["length"], value=type_of_dict(d["value_type"]))
    if tc == "hashmap":
        return VType("hashmap", "HashMap", key=type_of_dict(d["key_type"]), value=type_of_dict(d["value_type"]))
    if tc == "struct":
        return VType("struct", name, decl=decl_key(d.get("type_decl_node")))
    if tc == "interface":
        return VType("interface", name, decl=decl_key(d.get("type_decl_node")))
    if tc == "flag":
        return VType("flag", name, decl=decl_key(d.get("type_decl_node")))
    if tc == "tuple":
        return VType("tuple", "$Tuple")   # component types come from the elements
    if tc == "decimal":
        return VType("decimal", "decimal")
    if tc in ("module", "event", "contract_function", "builtin_function", "member_function"):
        return VType(tc, name, decl=decl_key(d.get("type_decl_node")))
    if name == "bool":
        return BOOL
    if name == "address":
        return ADDRESS
    if name == "(void)":
        return VType("void")
    if name in ("msg", "block", "tx", "chain", "self"):
        return VType("env", name)
    if d.get("generic") == "string":
        return VType("string", "string")
    return VType(tc or name, name)


def int_type_of_name(name: str) -> VType | None:
    m = re.fullmatch(r"(u?)int(\d+)", name)
    if m:
        return int_type(int(m.group(2)), m.group(1) == "")
    return None


def node_int(node: dict) -> int | None:
    """The value of an integer literal node (folded constants included)."""
    if node.get("ast_type") == "Int":
        return int(node["value"])
    if node.get("ast_type") == "UnaryOp" and node["op"]["ast_type"] == "USub":
        inner = node_int(node["operand"])
        return -inner if inner is not None else None
    return None


# ------------------------------------------------------------------------------------ modules

@dataclass
class Module:
    """One Vyper module (the main contract or an imported module) and its declarations."""
    node: dict
    source_id: int
    alias_path: tuple[str, ...]        # () for the main module, ("lib",) for `import lib`
    is_interface: bool = False
    variables: dict[str, dict] = field(default_factory=dict)     # name -> VariableDecl
    functions: dict[str, dict] = field(default_factory=dict)     # name -> FunctionDef
    structs: dict[str, dict] = field(default_factory=dict)
    events: dict[str, dict] = field(default_factory=dict)
    flags: dict[str, dict] = field(default_factory=dict)
    interfaces: dict[str, dict] = field(default_factory=dict)
    imports: dict[str, "Module"] = field(default_factory=dict)    # alias -> module
    initializes: list[str] = field(default_factory=list)          # aliases, in source order
    exports: list[tuple[str, str]] = field(default_factory=list)  # (alias, name or __interface__)
    nonreentrant_pragma: bool = False

    @property
    def prefix(self) -> str:
        return "".join(a + "_" for a in self.alias_path)

    def var_name(self, name: str) -> str:
        return ident(self.prefix + name)

    def fn_name(self, name: str) -> str:
        return ident(self.prefix + name)


@dataclass
class FnCtx:
    module: Module
    fn: dict | None
    returns: VType | None
    depth: int = 1
    tmp: int = 0
    locals: dict[str, VType] = field(default_factory=dict)
    in_ctor: bool = False
    calldata_bound: bool = False
    renames: dict[str, str] = field(default_factory=dict)   # source local name -> surface name

    def local(self, name: str) -> str:
        return ident(self.renames.get(name, name))


class Translator:
    def __init__(self, annotated: dict, comment_holes: bool, evm_version: str,
                 layout: dict | None, method_identifiers: dict[str, str] | None) -> None:
        self.comment_holes = comment_holes
        self.evm_version = evm_version or "prague"
        self.layout = layout or {}
        self.method_identifiers = method_identifiers or {}
        self.holes: list[str] = []
        self.notes: list[str] = []
        self.external_calls: dict[str, dict] = {}
        self.needed: list[tuple[Module, dict]] = []       # internal functions to emit
        self.needed_keys: set[tuple] = set()
        self.used_structs: list[tuple[Module, dict]] = []
        self.struct_names: dict[tuple, str] = {}
        self.lock_wrapped: list[tuple[Module, dict]] = []  # nonreentrant bodies to emit
        self.nodes: dict[tuple, dict] = {}
        self.modules_by_source: dict[int, Module] = {}
        sources = {annotated["ast"]["source_id"]: annotated["ast"]}
        for imp in annotated.get("imports", []):
            sources[imp["source_id"]] = imp
        for sid, unit in sources.items():
            for node in walk(unit):
                if isinstance(node.get("node_id"), int) and "ast_type" in node:
                    self.nodes[(sid, node["node_id"])] = node
        self.sources = sources
        self.main = self.build_module(annotated["ast"], ())
        self.name = Path(annotated.get("contract_name") or annotated["ast"].get("path") or "Contract").stem
        self.main_name = re.sub(r"[^A-Za-z0-9_]", "_", self.name)
        self.uses_transient_lock = self.cancun_or_later()
        self.lock_used = False
        self.has_default = False
        self.variants: list[dict] = []   # selector facts for the spec json
        self.storage_facts: list[dict] = []
        self.reserved_names: set[str] = {LOCK_NAME}
        self.storage_names: set[str] = {LOCK_NAME}   # names the notation resolves as storage paths
        for mod in self.all_modules(self.main):
            for name, var in mod.variables.items():
                if not var.get("is_constant"):
                    self.reserved_names.add(mod.prefix + name)
                    if not var.get("is_immutable"):
                        self.storage_names.add(mod.prefix + name)

    def declare_local(self, ctx: FnCtx, name: str, ty: VType) -> str:
        """Bind a source local; a name that shadows a contract-level declaration is renamed."""
        ctx.locals[name] = ty
        if name in self.reserved_names:
            ctx.renames[name] = name + "_"
            self.note(f"local {name} renamed to {name}_ (shadows a state variable)")
        return ctx.local(name)

    # ---------------------------------------------------------------- module construction

    def build_module(self, unit: dict, alias_path: tuple[str, ...], seen: dict | None = None) -> Module:
        seen = seen if seen is not None else {}
        sid = unit["source_id"]
        mod = Module(unit, sid, alias_path, bool(unit.get("is_interface")))
        self.modules_by_source.setdefault(sid, mod)
        for item in unit.get("body", []):
            kind = item.get("ast_type")
            if kind == "VariableDecl":
                mod.variables[item["target"]["id"]] = item
            elif kind == "FunctionDef":
                mod.functions[item["name"]] = item
            elif kind == "StructDef":
                mod.structs[item["name"]] = item
            elif kind == "EventDef":
                mod.events[item["name"]] = item
            elif kind == "FlagDef":
                mod.flags[item["name"]] = item
            elif kind == "InterfaceDef":
                mod.interfaces[item["name"]] = item
            elif kind in ("Import", "ImportFrom"):
                info = item.get("import_info") or {}
                alias = info.get("alias") or item.get("alias") or item.get("name")
                target_sid = info.get("source_id")
                if alias and target_sid in self.sources:
                    if (target_sid, alias_path + (alias,)) in seen:
                        mod.imports[alias] = seen[(target_sid, alias_path + (alias,))]
                    else:
                        sub = self.build_module(self.sources[target_sid], alias_path + (alias,), seen)
                        seen[(target_sid, alias_path + (alias,))] = sub
                        mod.imports[alias] = sub
            elif kind == "InitializesDecl":
                ann = item["annotation"]
                base = ann["value"] if ann.get("ast_type") == "Subscript" else ann
                if base.get("ast_type") == "Name":
                    mod.initializes.append(base["id"])
            elif kind == "ExportsDecl":
                ann = item["annotation"]
                elems = ann["elements"] if ann.get("ast_type") == "Tuple" else [ann]
                for e in elems:
                    if e.get("ast_type") == "Attribute" and e["value"].get("ast_type") == "Name":
                        mod.exports.append((e["value"]["id"], e["attr"]))
                    else:
                        self.holes.append(f"exports entry {describe(e)}")
            elif kind == "PragmaDirective" or kind == "UsesDecl" or kind == "ImplementsDecl":
                pass
        return mod

    def cancun_or_later(self) -> bool:
        v = self.evm_version.lower()
        return v not in EVM_VERSIONS or EVM_VERSIONS.index(v) >= EVM_VERSIONS.index("cancun")

    # ---------------------------------------------------------------- holes and notes

    def hole(self, what: str, src: dict | None = None) -> str:
        loc = f" @{src['lineno']}" if src and src.get("lineno") else ""
        self.holes.append(what + loc)
        text = (what + loc).replace('"', "'")
        return f"-- HOLE: {text}" if self.comment_holes else f"${{hole \"{text}\"}}"

    def note(self, text: str) -> None:
        if text not in self.notes:
            self.notes.append(text)

    # ---------------------------------------------------------------- type resolution

    def ntype(self, node: dict) -> VType | None:
        return type_of_dict(node.get("type"))

    def struct_def(self, ty: VType, mod: Module) -> tuple[Module, dict] | None:
        node = self.nodes.get(ty.decl) if ty.decl else None
        if node is not None and node.get("ast_type") == "StructDef":
            return self.modules_by_source.get(ty.decl[0], mod), node
        for m in self.all_modules(mod):
            if ty.name in m.structs:
                return m, m.structs[ty.name]
        return None

    def all_modules(self, start: Module) -> list[Module]:
        out, todo = [], [self.main, start]
        while todo:
            m = todo.pop()
            if any(m is o for o in out):
                continue
            out.append(m)
            todo.extend(m.imports.values())
        return out

    def struct_name(self, ty: VType, mod: Module) -> str:
        found = self.struct_def(ty, mod)
        if found is None:
            raise Hole(f"unresolved struct {ty.name}")
        smod, sdef = found
        key = (smod.source_id, sdef["node_id"])
        if key not in self.struct_names:
            name = sdef["name"]
            if name in self.struct_names.values():
                name = smod.prefix + name if smod.prefix else f"{name}_{sdef['node_id']}"
            self.struct_names[key] = name
            self.used_structs.append((smod, sdef))
        return self.struct_names[key]

    def struct_fields(self, sdef: dict, smod: Module) -> list[tuple[str, VType]]:
        fields = []
        for member in sdef.get("body", []):
            if member.get("ast_type") == "AnnAssign":
                fields.append((member["target"]["id"], self.type_of_annotation(member["annotation"], smod)))
        return fields

    def type_of_annotation(self, ann: dict, mod: Module) -> VType:
        """The VType of a declaration annotation (``uint256``, ``HashMap[K, V]``, ``public(T)``…)."""
        kind = ann.get("ast_type")
        if kind == "Name":
            name = ann["id"]
            it = int_type_of_name(name)
            if it:
                return it
            if name == "bool":
                return BOOL
            if name == "address":
                return ADDRESS
            m = re.fullmatch(r"bytes(\d+)", name)
            if m:
                return VType("bytesM", name, int(m.group(1)))
            if name == "decimal":
                return VType("decimal", "decimal")
            for m_ in self.all_modules(mod):
                if name in m_.structs:
                    return VType("struct", name, decl=(m_.source_id, m_.structs[name]["node_id"]))
                if name in m_.flags:
                    return VType("flag", name, decl=(m_.source_id, m_.flags[name]["node_id"]))
                if name in m_.interfaces:
                    return VType("interface", name, decl=(m_.source_id, m_.interfaces[name]["node_id"]))
            # an imported interface module (`from ethereum.ercs import IERC20`)
            for m_ in self.all_modules(mod):
                if name in m_.imports and m_.imports[name].is_interface:
                    return VType("interface", name, decl=(m_.imports[name].source_id, 0))
            raise Hole(f"unknown type {name}")
        if kind == "Subscript":
            base = ann["value"]
            if base.get("ast_type") == "Name":
                bname = base["id"]
                sl = ann["slice"]
                elems = sl["elements"] if sl.get("ast_type") == "Tuple" else [sl]
                if bname == "HashMap":
                    return VType("hashmap", "HashMap", key=self.type_of_annotation(elems[0], mod),
                                 value=self.type_of_annotation(elems[1], mod))
                if bname == "DynArray":
                    return VType("dynarray", "DynArray", length=self.const_int(elems[1], mod),
                                 value=self.type_of_annotation(elems[0], mod))
                if bname == "Bytes":
                    return VType("bytes", "bytes", length=self.const_int(elems[0], mod))
                if bname == "String":
                    return VType("string", "string", length=self.const_int(elems[0], mod))
            return VType("sarray", "$SArray", length=self.const_int(ann["slice"], mod),
                         value=self.type_of_annotation(base, mod))
        if kind == "Call":
            fname = ann["func"].get("id")
            if fname in ("public", "immutable", "constant", "transient", "indexed", "reentrant"):
                return self.type_of_annotation(ann["args"][0], mod)
            raise Hole(f"type annotation {fname}(…)")
        if kind == "Tuple":
            return VType("tuple", "$Tuple", members=tuple(self.type_of_annotation(e, mod) for e in ann["elements"]))
        if kind == "Attribute":
            # module.Struct / module.Flag
            base = ann["value"]
            if base.get("ast_type") == "Name" and base["id"] in mod.imports:
                return self.type_of_annotation({"ast_type": "Name", "id": ann["attr"]}, mod.imports[base["id"]])
            raise Hole(f"type annotation {describe(ann)}")
        raise Hole(f"type annotation {kind}")

    def const_int(self, node: dict, mod: Module) -> int:
        value = node_int(node)
        if value is not None:
            return value
        if node.get("ast_type") == "Name":
            var = self.find_constant(node["id"], mod)
            if var is not None and var.get("value") is not None:
                return self.const_int(var["value"], mod)
        if node.get("ast_type") == "Attribute" and node["value"].get("ast_type") == "Name" \
                and node["value"]["id"] in mod.imports:
            return self.const_int({"ast_type": "Name", "id": node["attr"]}, mod.imports[node["value"]["id"]])
        if node.get("ast_type") == "BinOp":
            a, b = self.const_int(node["left"], mod), self.const_int(node["right"], mod)
            op = node["op"]["ast_type"]
            return {"Add": a + b, "Sub": a - b, "Mult": a * b, "FloorDiv": a // b, "Pow": a ** b,
                    "Mod": a % b}[op]
        raise Hole(f"non-constant length {describe(node)}")

    def find_constant(self, name: str, mod: Module) -> dict | None:
        var = mod.variables.get(name)
        if var is not None and var.get("is_constant"):
            return var
        return None

    def stype(self, ty: VType | None, mod: Module) -> str:
        """Surface type for a VType."""
        if ty is None:
            raise Hole("untyped expression")
        if ty.kind == "int":
            return ty.surface_int
        if ty.kind in ("bool", "address"):
            return ty.kind
        if ty.kind == "bytesM":
            return f"bytes{ty.bits}"
        if ty.kind in ("bytes", "string"):
            return ty.kind
        if ty.kind == "dynarray":
            return f"{self.stype(ty.value, mod)}[]"
        if ty.kind == "sarray":
            return f"{self.stype(ty.value, mod)}[{ty.length}]"
        if ty.kind == "hashmap":
            return f"mapping({self.stype(ty.key, mod)} => {self.stype(ty.value, mod)})"
        if ty.kind == "struct":
            return self.struct_name(ty, mod)
        if ty.kind == "interface":
            return "address"
        if ty.kind == "flag":
            return "uint256"
        if ty.kind == "tuple":
            return "(" + ", ".join(self.stype(m, mod) for m in ty.members) + ")"
        if ty.kind == "decimal":
            raise Hole("decimal type")
        raise Hole(f"type {ty.kind} {ty.name}")

    def abi_type(self, ty: VType, mod: Module) -> str:
        if ty.kind == "int":
            return ty.surface_int
        if ty.kind in ("bool", "address", "bytes", "string"):
            return ty.kind
        if ty.kind == "bytesM":
            return f"bytes{ty.bits}"
        if ty.kind == "dynarray":
            return f"{self.abi_type(ty.value, mod)}[]"
        if ty.kind == "sarray":
            return f"{self.abi_type(ty.value, mod)}[{ty.length}]"
        if ty.kind == "struct":
            found = self.struct_def(ty, mod)
            if found is None:
                raise Hole(f"unresolved struct {ty.name}")
            smod, sdef = found
            return "(" + ",".join(self.abi_type(t, smod) for _, t in self.struct_fields(sdef, smod)) + ")"
        if ty.kind == "interface":
            return "address"
        if ty.kind == "flag":
            return "uint256"
        if ty.kind == "tuple":
            return "(" + ",".join(self.abi_type(m, mod) for m in ty.members) + ")"
        if ty.kind == "decimal":
            return "int168"
        raise Hole(f"ABI type {ty.kind}")

    def is_memory(self, ty: VType) -> bool:
        return ty.kind in ("bytes", "string", "dynarray", "sarray", "struct", "tuple")

    def local_decl(self, ty: VType, name: str, mod: Module, ctx: FnCtx | None = None) -> str:
        t = self.stype(ty, mod)
        surface = ctx.local(name) if ctx is not None else ident(name)
        return f"{t}{' memory' if self.is_memory(ty) else ''} {surface}"

    def zero_value(self, ty: VType, mod: Module) -> str:
        if ty.kind == "int" or ty.kind == "flag":
            return "0"
        if ty.kind == "bool":
            return "false"
        if ty.kind in ("address", "interface"):
            return "address(0)"
        if ty.kind == "bytesM":
            return f"bytes{ty.bits}(0)"
        if ty.kind == "bytes":
            return "new bytes(0)"
        if ty.kind == "string":
            return '""'
        if ty.kind == "dynarray":
            return f"new {self.stype(ty.value, mod)}[](0)"
        if ty.kind == "struct":
            found = self.struct_def(ty, mod)
            if found is None:
                raise Hole(f"unresolved struct {ty.name}")
            smod, sdef = found
            fields = ", ".join(f"{ident(n)}: {self.zero_value(t, smod)}" for n, t in self.struct_fields(sdef, smod))
            return f"{self.struct_name(ty, mod)}({{{fields}}})"
        raise Hole(f"empty({ty.name})")

    # ---------------------------------------------------------------- expressions

    def expr(self, node: dict, ctx: FnCtx, pre: Stmts) -> str:
        kind = node["ast_type"]
        handler = getattr(self, f"expr_{kind}", None)
        if handler is None:
            raise Hole(f"expression {kind}")
        return handler(node, ctx, pre)

    def expr_Int(self, node: dict, ctx: FnCtx, pre: Stmts) -> str:
        v = int(node["value"])
        return str(v) if v >= 0 else f"(0 - {-v})"

    def expr_Decimal(self, node: dict, ctx: FnCtx, pre: Stmts) -> str:
        raise Hole("decimal literal")

    def expr_Hex(self, node: dict, ctx: FnCtx, pre: Stmts) -> str:
        ty = self.ntype(node)
        text = node["value"]
        if ty and ty.kind == "address":
            return f"address({text})"
        if ty and ty.kind == "bytesM":
            return f"bytes{ty.bits}({text})"
        return str(int(text, 16))

    def expr_Str(self, node: dict, ctx: FnCtx, pre: Stmts) -> str:
        value = node.get("value", "")
        if any(ord(ch) < 32 or ord(ch) > 126 or ch in '"\\' for ch in value):
            raise Hole("string literal with escapes")
        return f"\"{value}\""

    def expr_Bytes(self, node: dict, ctx: FnCtx, pre: Stmts) -> str:
        text = node.get("value", "")
        raw = bytes.fromhex(text[2:]) if text.startswith("0x") else text.encode("latin-1")
        if not raw:
            return "new bytes(0)"
        if all(32 <= b <= 126 and chr(b) not in '"\\' for b in raw):
            return f"\"{raw.decode('ascii')}\""
        raise Hole("bytes literal")

    expr_HexBytes = expr_Bytes

    def expr_NameConstant(self, node: dict, ctx: FnCtx, pre: Stmts) -> str:
        v = node.get("value")
        if v is True:
            return "true"
        if v is False:
            return "false"
        raise Hole(f"constant {v}")

    def expr_Name(self, node: dict, ctx: FnCtx, pre: Stmts) -> str:
        name = node["id"]
        if name in ctx.locals:
            return ctx.local(name)
        if name == "self":
            return "address(this)"
        var = ctx.module.variables.get(name)
        if var is not None and var.get("is_constant"):
            return self.constant_text(var, ctx.module, ctx, pre)
        if var is not None and var.get("is_immutable"):
            return ctx.module.var_name(name)
        raise Hole(f"identifier {name}")

    def constant_text(self, var: dict, mod: Module, ctx: FnCtx, pre: Stmts) -> str:
        value = var.get("value")
        if value is None:
            raise Hole(f"constant {var['target']['id']} without a value")
        inner = Stmts()
        text = self.expr(value, FnCtx(mod, None, None), inner)
        if inner.lines:
            raise Hole(f"constant {var['target']['id']} with a call in its initialiser")
        self.note(f"constant {mod.prefix}{var['target']['id']} = {text} inlined")
        return text if re.fullmatch(r"[A-Za-z0-9_«»\"().]+", text) else f"({text})"

    def expr_Attribute(self, node: dict, ctx: FnCtx, pre: Stmts) -> str:
        attr = node["attr"]
        base = node["value"]
        bty = self.ntype(base)
        if base.get("ast_type") == "Name":
            bname = base["id"]
            if bname == "self" and bname not in ctx.locals:
                if attr == "balance":
                    return "address(this).balance"
                if attr in ("codehash", "codesize", "is_contract", "code"):
                    raise Hole(f"self.{attr}")
                var = ctx.module.variables.get(attr)
                if var is None:
                    raise Hole(f"self.{attr}")
                return self.var_ref(var, ctx.module, ctx, pre)
            if (bname, attr) in ENV_VARS and bname not in ctx.locals:
                return ENV_VARS[(bname, attr)]
            if bname in ("msg", "block", "tx", "chain") and bname not in ctx.locals:
                raise Hole(f"{bname}.{attr}")
            if bty is not None and bty.kind == "module":
                mod = self.module_of_name(bname, ctx.module)
                var = mod.variables.get(attr) if mod else None
                if var is None:
                    raise Hole(f"module member {bname}.{attr}")
                return self.var_ref(var, mod, ctx, pre)
            if base.get("type", {}).get("type_t", {}).get("typeclass") == "flag":
                return str(self.flag_value(base["type"]["type_t"], attr, ctx.module))
        if bty is not None and bty.kind in ("address", "interface"):
            inner = self.expr(base, ctx, pre)
            if attr == "balance":
                return f"{inner}.balance"
            if attr == "codehash":
                return f"{inner}.codehash"
            if attr == "codesize":
                return f"{inner}.code.length"
            if attr == "is_contract":
                return f"({inner}.code.length > 0)"
            raise Hole(f"address member {attr}")
        if bty is not None and bty.kind == "struct":
            return f"{self.expr(base, ctx, pre)}.{ident(attr)}"
        raise Hole(f"member access .{attr} on {bty.kind if bty else '?'}")

    def flag_value(self, type_t: dict, member: str, mod: Module) -> int:
        key = decl_key(type_t.get("type_decl_node"))
        fdef = self.nodes.get(key) if key else None
        if fdef is None or fdef.get("ast_type") != "FlagDef":
            fdef = None
            for m in self.all_modules(mod):
                fdef = m.flags.get(type_t.get("name"))
                if fdef:
                    break
        if fdef is None:
            raise Hole(f"flag {type_t.get('name')}")
        members = [e["value"]["id"] for e in fdef["body"] if e.get("ast_type") == "Expr"]
        return 1 << members.index(member)

    def module_of_name(self, name: str, mod: Module) -> Module | None:
        return mod.imports.get(name)

    def var_ref(self, var: dict, mod: Module, ctx: FnCtx, pre: Stmts) -> str:
        if var.get("is_constant"):
            return self.constant_text(var, mod, ctx, pre)
        return mod.var_name(var["target"]["id"])

    def expr_Subscript(self, node: dict, ctx: FnCtx, pre: Stmts) -> str:
        base = self.expr(node["value"], ctx, pre)
        bty = self.ntype(node["value"])
        if bty is not None and bty.kind in ("bytes", "string"):
            raise Hole("byte indexing")
        index = self.expr(node["slice"], ctx, pre)
        return f"{base}[{index}]"

    def expr_Tuple(self, node: dict, ctx: FnCtx, pre: Stmts) -> str:
        return "tuple(" + ", ".join(self.expr(e, ctx, pre) for e in node["elements"]) + ")"

    def expr_List(self, node: dict, ctx: FnCtx, pre: Stmts) -> str:
        raise Hole("list literal")

    def expr_IfExp(self, node: dict, ctx: FnCtx, pre: Stmts) -> str:
        c = self.expr(node["test"], ctx, pre)
        a = self.expr(node["body"], ctx, pre)
        b = self.expr(node["orelse"], ctx, pre)
        return f"({c} ? {a} : {b})"

    def expr_BoolOp(self, node: dict, ctx: FnCtx, pre: Stmts) -> str:
        op = " && " if node["op"]["ast_type"] == "And" else " || "
        return "(" + op.join(self.expr(v, ctx, pre) for v in node["values"]) + ")"

    def expr_UnaryOp(self, node: dict, ctx: FnCtx, pre: Stmts) -> str:
        op = node["op"]["ast_type"]
        ty = self.ntype(node)
        inner = self.expr(node["operand"], ctx, pre)
        if op == "Not":
            return f"!({inner})"
        if op == "USub":
            if ty and ty.is_int:
                return f"((0 - {inner}) as {ty.surface_int})"
            raise Hole("negation of a non-integer")
        if op == "Invert":
            if ty and ty.is_int:
                return f"(~[{ty.surface_int}] {inner})"
            if ty and ty.kind == "flag":
                return f"((~[uint256] {inner}) &[uint256] {self.flag_mask(ty, ctx.module)})"
            raise Hole("bitwise not of a non-integer")
        raise Hole(f"unary operator {op}")

    def flag_mask(self, ty: VType, mod: Module) -> int:
        fdef = self.nodes.get(ty.decl) if ty.decl else None
        if fdef is None or fdef.get("ast_type") != "FlagDef":
            fdef = next((m.flags[ty.name] for m in self.all_modules(mod) if ty.name in m.flags), None)
        if fdef is None:
            raise Hole(f"flag {ty.name}")
        return (1 << len([e for e in fdef["body"] if e.get("ast_type") == "Expr"])) - 1

    def expr_BinOp(self, node: dict, ctx: FnCtx, pre: Stmts) -> str:
        op = node["op"]["ast_type"]
        ty = self.ntype(node)
        a = self.expr(node["left"], ctx, pre)
        b = self.expr(node["right"], ctx, pre)
        if ty is not None and ty.kind == "flag":
            if op in ("BitAnd", "BitOr", "BitXor"):
                return f"({a} {BITWISE[op]}[uint256] {b})"
            raise Hole(f"flag operator {op}")
        if ty is None or not ty.is_int:
            if ty is not None and ty.kind == "decimal":
                raise Hole("decimal arithmetic")
            raise Hole(f"operator {op} on {ty.name if ty else '?'}")
        t = ty.surface_int
        if op in CHECKED:
            return f"(({a} {CHECKED[op]} {b}) as {t})"
        if op == "FloorDiv":
            return f"sdiv({a}, {b})" if ty.signed else f"({a} / {b})"
        if op == "Mod":
            return f"srem({a}, {b})" if ty.signed else f"({a} % {b})"
        if op == "Div":
            raise Hole("decimal division")
        if op in BITWISE:
            return f"({a} {BITWISE[op]}[{t}] {b})"
        raise Hole(f"binary operator {op}")

    def expr_Compare(self, node: dict, ctx: FnCtx, pre: Stmts) -> str:
        op = node["op"]["ast_type"]
        if op in COMPARE:
            a = self.expr(node["left"], ctx, pre)
            b = self.expr(node["right"], ctx, pre)
            return f"({a} {COMPARE[op]} {b})"
        if op in ("In", "NotIn"):
            rty = self.ntype(node["right"])
            a = self.expr(node["left"], ctx, pre)
            if rty is not None and rty.kind == "flag":
                b = self.expr(node["right"], ctx, pre)
                test = f"(({b} &[uint256] {a}) != 0)"
                return test if op == "In" else f"!{test}"
            elems = self.list_elements(node["right"], ctx)
            if elems is None:
                raise Hole(f"{op} on a non-literal list")
            tests = [f"{a} == {self.expr(e, ctx, pre)}" for e in elems]
            if op == "In":
                return "(" + " || ".join(tests) + ")" if tests else "false"
            return "(" + " && ".join(t.replace(" == ", " != ", 1) for t in tests) + ")" if tests else "true"
        raise Hole(f"comparison {op}")

    def list_elements(self, node: dict, ctx: FnCtx) -> list[dict] | None:
        if node.get("ast_type") == "List":
            return node["elements"]
        if node.get("ast_type") == "Name":
            var = self.find_constant(node["id"], ctx.module)
            if var is not None and var.get("value", {}).get("ast_type") == "List":
                return var["value"]["elements"]
        return None

    # ---------------------------------------------------------------- calls

    def expr_Call(self, node: dict, ctx: FnCtx, pre: Stmts) -> str:
        func = node["func"]
        fty = func.get("type") or {}
        if "type_t" in fty:
            return self.type_call(node, fty["type_t"], ctx, pre)
        tc = fty.get("typeclass")
        if func.get("ast_type") == "Name":
            if tc == "builtin_function" or "type" not in func:
                return self.builtin(func["id"], node, ctx, pre)
            raise Hole(f"call to {func['id']}")
        if func.get("ast_type") == "Attribute":
            base = func["value"]
            bty = self.ntype(base)
            if tc == "contract_function":
                if base.get("ast_type") == "Name" and base["id"] == "self":
                    return self.hoist_internal_call(node, ctx.module, func["attr"], ctx, pre)
                if bty is not None and bty.kind == "module":
                    mod = self.module_of_name(base["id"], ctx.module)
                    if mod is None:
                        raise Hole(f"module {base['id']}")
                    return self.hoist_internal_call(node, mod, func["attr"], ctx, pre)
                if bty is not None and bty.kind == "interface":
                    raise Hole("external call without extcall/staticcall")
            if tc == "member_function":
                raise Hole(f"method {func['attr']} in expression position")
        raise Hole(f"call {describe(func)}")

    def type_call(self, node: dict, type_t: dict, ctx: FnCtx, pre: Stmts) -> str:
        tc = type_t.get("typeclass")
        args = node.get("args", [])
        if tc == "struct":
            ty = type_of_dict(type_t)
            found = self.struct_def(ty, ctx.module)
            if found is None:
                raise Hole(f"unresolved struct {ty.name}")
            smod, sdef = found
            names = [n for n, _ in self.struct_fields(sdef, smod)]
            values: dict[str, str] = {}
            for kw in node.get("keywords", []):
                values[kw["arg"]] = self.expr(kw["value"], ctx, pre)
            for n, a in zip(names, args):
                values[n] = self.expr(a, ctx, pre)
            fields = ", ".join(f"{ident(n)}: {values[n]}" for n in names if n in values)
            return f"{self.struct_name(ty, ctx.module)}({{{fields}}})"
        if tc == "interface":
            return self.expr(args[0], ctx, pre)   # IFace(addr): an address
        raise Hole(f"constructor of {type_t.get('name')}")

    def kwargs(self, node: dict) -> dict[str, dict]:
        return {kw["arg"]: kw["value"] for kw in node.get("keywords", [])}

    def builtin(self, name: str, node: dict, ctx: FnCtx, pre: Stmts) -> str:
        args = node.get("args", [])
        kw = self.kwargs(node)
        ty = self.ntype(node)

        def arg(i: int) -> str:
            return self.expr(args[i], ctx, pre)

        if name == "empty":
            target = self.type_of_annotation(args[0], ctx.module)
            return self.zero_value(target, ctx.module)
        if name in ("max_value", "min_value"):
            target = self.type_of_annotation(args[0], ctx.module)
            if not target.is_int:
                raise Hole(f"{name} of {target.name}")
            return f"type({target.surface_int}).{name[:3]}"
        if name == "convert":
            return self.convert(args[0], self.type_of_annotation(args[1], ctx.module), ctx, pre)
        if name == "len":
            aty = self.ntype(args[0])
            if is_msg_data(args[0]):
                return f"{self.calldata(ctx, pre)}.length"
            if aty is not None and aty.kind == "sarray":
                return str(aty.length)
            return f"{arg(0)}.length"
        if name in ("min", "max"):
            a, b = self.atom(args[0], ctx, pre), self.atom(args[1], ctx, pre)
            return f"({a} {'<' if name == 'min' else '>'} {b} ? {a} : {b})" if a != b else a
        if name == "abs":
            a = self.atom(args[0], ctx, pre)
            return f"(({a} < 0 ? (0 - {a}) : {a}) as int256)"
        if name in ("unsafe_add", "unsafe_sub", "unsafe_mul", "unsafe_div"):
            if ty is None or not ty.is_int:
                raise Hole(f"{name} on a non-integer")
            a, b = arg(0), arg(1)
            t = ty.surface_int
            if name == "unsafe_div":
                div = f"sdiv({a}, {b})" if ty.signed else f"({a} / {b})"
                return f"({b} == 0 ? 0 : {div})"
            op = {"unsafe_add": "+", "unsafe_sub": "-", "unsafe_mul": "*"}[name]
            return f"{t}({a} {op} {b})"
        if name == "keccak256":
            if is_msg_data(args[0]):
                return f"keccak256({self.calldata(ctx, pre)})"
            aty = self.ntype(args[0])
            if aty is not None and aty.kind == "bytesM":
                self.note("keccak256 of a bytes32 value hashes its 32 bytes")
            return f"keccak256({arg(0)})"
        if name == "blockhash":
            return f"blockhash({arg(0)})"
        if name == "method_id":
            lit = args[0]
            if lit.get("ast_type") != "Str":
                raise Hole("method_id of a non-literal")
            from evm_tools import selector
            sel = selector(lit["value"]).hex()
            out = kw.get("output_type")
            if ty is not None and ty.kind == "bytesM" and ty.bits == 4:
                return f"bytes4(0x{sel})"
            if ty is not None and ty.kind == "bytesM" and ty.bits == 32:
                return f"bytes32(0x{sel}{'00' * 28})"
            raise Hole(f"method_id as {self.stype(ty, ctx.module) if ty else '?'}; use output_type=bytes4"
                       + ("" if out is None else ""))
        if name in ("uint256_addmod", "uint256_mulmod"):
            a, b, n = arg(0), arg(1), arg(2)
            op = "+" if name == "uint256_addmod" else "*"
            self.note(f"{name} translated as (a {op} b) % n: differs for n == 0 (EVM gives 0)")
            return f"(({a} {op} {b}) % {n})"
        if name == "as_wei_value":
            unit = args[1]
            if unit.get("ast_type") != "Str" or unit["value"] not in WEI_UNITS:
                raise Hole("as_wei_value unit")
            return f"(({arg(0)} * {WEI_UNITS[unit['value']]}) as uint256)"
        if name == "slice":
            return self.slice_expr(args, ctx, pre)
        if name == "concat":
            parts = []
            for a in args:
                aty = self.ntype(a)
                if aty is None or aty.kind not in ("bytes", "string", "bytesM"):
                    raise Hole("concat argument type")
                t = self.stype(aty, ctx.module)
                parts.append(f"{t}({arg(args.index(a))})")
            return f"abi.encodePacked({', '.join(parts)})"
        if name == "raw_call":
            return self.raw_call(node, ctx, pre, None)[0]
        if name in ("send", "raw_log", "raw_revert", "selfdestruct", "print", "breakpoint"):
            raise Hole(f"{name} in expression position")
        if name in ("sha256", "ecrecover", "ecadd", "ecmul", "extract32", "abi_encode", "_abi_encode",
                    "abi_decode", "_abi_decode", "create_minimal_proxy_to", "create_copy_of",
                    "create_from_blueprint", "raw_create", "pow_mod256", "isqrt", "floor", "ceil",
                    "epsilon", "sqrt", "blobhash", "uint2str", "shift", "gasleft"):
            raise Hole(f"builtin {name}()")
        raise Hole(f"builtin {name}()")

    def atom(self, node: dict, ctx: FnCtx, pre: Stmts) -> str:
        """An expression that may be repeated: a name or literal as is, anything else bound first."""
        text = self.expr(node, ctx, pre)
        if re.fullmatch(r"[A-Za-z_«»][A-Za-z0-9_«».]*|\d+", text):
            return text
        ty = self.ntype(node)
        tmp = f"__v{ctx.tmp}"
        ctx.tmp += 1
        decl = self.local_decl(ty, tmp, ctx.module) if ty is not None else f"var {tmp}"
        pre.add(f"{decl} = {unparen(text)};", ctx.depth)
        return tmp

    def calldata(self, ctx: FnCtx, pre: Stmts) -> str:
        if not ctx.calldata_bound:
            pre.add("bytes __calldata = msg.data;", ctx.depth)
            ctx.calldata_bound = True
        return "__calldata"

    def slice_expr(self, args: list[dict], ctx: FnCtx, pre: Stmts) -> str:
        aty = self.ntype(args[0])
        if is_msg_data(args[0]):
            base = self.calldata(ctx, pre)
        elif aty is not None and aty.kind in ("bytes", "string"):
            base = self.expr(args[0], ctx, pre)
        else:
            raise Hole("slice of a non-bytes value")
        start = self.expr(args[1], ctx, pre)
        length = self.expr(args[2], ctx, pre)
        pre.add(f"require(({start} + {length}) <= {base}.length);", ctx.depth)
        return f"{base}[{start} : {start} + {length}]"

    def convert(self, arg: dict, out: VType, ctx: FnCtx, pre: Stmts) -> str:
        aty = self.ntype(arg)
        if aty is None:
            raise Hole("convert of an untyped value")
        e = self.expr(arg, ctx, pre)
        src = aty
        if src.kind == "flag":
            src = UINT256
        if src.is_int and out.is_int:
            if out.lo <= src.lo and src.hi <= out.hi:
                return e
            return f"({e} as {out.surface_int})"
        if src.is_int and out.kind == "bool":
            return f"({e} != 0)"
        if src.kind == "bool" and out.is_int:
            return f"({e} ? 1 : 0)"
        if src.is_int and out.kind == "address":
            return f"address(({e} as uint160))" if src.hi > (1 << 160) - 1 or src.signed else f"address({e})"
        if src.kind in ("address", "interface") and out.is_int and not out.signed and out.bits >= 160:
            return f"uint256({e})" if out.bits == 256 else f"(uint256({e}) as {out.surface_int})"
        if src.kind in ("address", "interface") and out.kind in ("address", "interface"):
            return e
        if src.kind == "bytesM" and out.is_int and not out.signed and out.bits == 8 * src.bits:
            return f"{out.surface_int}({e})"
        if src.kind == "bytesM" and out.is_int and not out.signed and out.bits > 8 * src.bits:
            raise Hole(f"convert(bytes{src.bits}, {out.surface_int}): widening bytes cast")
        if src.is_int and not src.signed and out.kind == "bytesM" and out.bits * 8 >= src.bits:
            return f"bytes{out.bits}({e})"
        if src.kind == "bytesM" and out.kind == "bytesM" and src.bits == out.bits:
            return e
        raise Hole(f"convert({src.name}, {out.name})")

    def hoist_internal_call(self, node: dict, mod: Module, fname: str, ctx: FnCtx, pre: Stmts) -> str:
        fn = mod.functions.get(fname)
        if fn is None:
            raise Hole(f"internal function {mod.prefix}{fname}")
        name = self.require_internal(mod, fn)
        params = fn["args"]["args"]
        defaults = fn["args"].get("defaults") or []
        args = [self.expr(a, ctx, pre) for a in node.get("args", [])]
        kw = self.kwargs(node)
        for i, p in enumerate(params[len(args):], start=len(args)):
            if p["arg"] in kw:
                args.append(self.expr(kw[p["arg"]], ctx, pre))
            else:
                d = defaults[i - (len(params) - len(defaults))]
                args.append(self.expr(d, FnCtx(mod, fn, None), pre))
        tmp = f"__c{ctx.tmp}"
        ctx.tmp += 1
        pre.add(f"var {tmp} = {name}({', '.join(args)});", ctx.depth)
        return tmp

    def require_internal(self, mod: Module, fn: dict) -> str:
        key = (mod.source_id, mod.alias_path, fn["node_id"])
        if key not in self.needed_keys:
            self.needed_keys.add(key)
            self.needed.append((mod, fn))
        return mod.fn_name(fn["name"]) + ("_body" if self.is_nonreentrant(fn, mod) else "")

    def expr_ExtCall(self, node: dict, ctx: FnCtx, pre: Stmts) -> str:
        return self.hoist_external_call(node["value"], False, ctx, pre)

    def expr_StaticCall(self, node: dict, ctx: FnCtx, pre: Stmts) -> str:
        return self.hoist_external_call(node["value"], True, ctx, pre)

    def hoist_external_call(self, call: dict, view: bool, ctx: FnCtx, pre: Stmts) -> str:
        func = call["func"]
        if func.get("ast_type") != "Attribute":
            raise Hole("external call without a receiver")
        method = func["attr"]
        receiver = self.receiver(func["value"], ctx, pre)
        kw = self.kwargs(call)
        args = [self.expr(a, ctx, pre) for a in call.get("args", [])]
        opts = []
        if "value" in kw:
            opts.append(f"value: {self.expr(kw['value'], ctx, pre)}")
        if "gas" in kw:
            self.note(f"call option gas dropped — line {call.get('lineno')}")
        if view:
            opts.append("view")
        skip_check = kw.get("skip_contract_check", {}).get("value") is True
        default_return = kw.get("default_return_value")
        rty = self.ntype(call)
        has_return = rty is not None and rty.kind != "void"
        self.record_external_call(method, func, call, rty, view, ctx)
        if default_return is not None:
            raise Hole(f"default_return_value on {method}")
        if not has_return and not skip_check:
            pre.add(f"require({receiver}.code.length > 0);", ctx.depth)
        tmp = f"__c{ctx.tmp}"
        ctx.tmp += 1
        opt_text = f"{{{', '.join(opts)}}}" if opts else ""
        pre.add(f"var {tmp} = {receiver}.{method}{opt_text}({', '.join(args)});", ctx.depth)
        return tmp

    def receiver(self, node: dict, ctx: FnCtx, pre: Stmts) -> str:
        """A call target the notation resolves: a local or a storage path as is; an immutable, a
        constant, `address(this)`, `msg.sender` or a computed address bound to a local first."""
        text = self.expr(node, ctx, pre)
        head = re.sub(r"[«»]", "", text.split(".")[0].split("[")[0])
        resolvable = re.fullmatch(r"[A-Za-z_«»][A-Za-z0-9_«».]*", text) is not None and (
            head in {re.sub(r"[«»]", "", ctx.local(n)) for n in ctx.locals} or head in self.storage_names
            or text == "msg.sender")
        if resolvable:
            return text
        tmp = f"__a{ctx.tmp}"
        ctx.tmp += 1
        pre.add(f"address {tmp} = {text};", ctx.depth)
        return tmp

    def record_external_call(self, method: str, func: dict, call: dict, rty: VType | None,
                             view: bool, ctx: FnCtx) -> None:
        fkey = decl_key((func.get("type") or {}).get("type_decl_node"))
        fdef = self.nodes.get(fkey) if fkey else None
        params: list[str] = []
        rets: list[str] = []
        try:
            if fdef is not None and fdef.get("ast_type") == "FunctionDef":
                imod = self.modules_by_source.get(fkey[0], ctx.module)
                params = [self.stype(self.type_of_annotation(a["annotation"], imod), imod) for a in fdef["args"]["args"]]
                if fdef.get("returns") is not None:
                    r = self.type_of_annotation(fdef["returns"], imod)
                    rets = [self.stype(m, imod) for m in r.members] if r.kind == "tuple" else [self.stype(r, imod)]
            else:
                params = [self.stype(self.ntype(a), ctx.module) for a in call.get("args", [])]
                if rty is not None and rty.kind != "void":
                    rets = [self.stype(rty, ctx.module)]
        except Hole:
            pass
        self.external_calls.setdefault(method, {"name": method, "params": params, "returns": rets, "view": view})

    def raw_call(self, node: dict, ctx: FnCtx, pre: Stmts, binders: list[str] | None) -> tuple[str, str, str]:
        """``raw_call`` as a low-level call; returns (value expression, ok binder, data binder)."""
        args = node.get("args", [])
        kw = self.kwargs(node)
        to = self.receiver(args[0], ctx, pre)
        data = self.expr(args[1], ctx, pre)
        if "gas" in kw:
            self.note(f"raw_call gas dropped — line {node.get('lineno')}")
        outsize = self.const_int(kw["max_outsize"], ctx.module) if "max_outsize" in kw else 0
        revert = kw.get("revert_on_failure", {}).get("value", True) is not False
        static = kw.get("is_static_call", {}).get("value") is True
        delegate = kw.get("is_delegate_call", {}).get("value") is True
        value = self.expr(kw["value"], ctx, pre) if "value" in kw else None
        names = binders or [f"__ok{ctx.tmp}", f"__data{ctx.tmp}"]
        if binders is None:
            ctx.tmp += 1
        method = "delegatecall" if delegate else "staticcall" if static else "call"
        opt = f"{{value: {value}}}" if value is not None and not delegate and not static else ""
        pre.add(f"(bool {names[0]}, bytes memory {names[1]}) = {to}.{method}{opt}({data});", ctx.depth)
        if revert:
            pre.add(f"require({names[0]});", ctx.depth)
        if outsize:
            self.note(f"raw_call max_outsize={outsize}: the bound data is the full return data, "
                      f"Vyper keeps its first {outsize} bytes — line {node.get('lineno')}")
        if outsize and not revert:
            return f"tuple({names[0]}, {names[1]})", names[0], names[1]
        if outsize:
            return names[1], names[0], names[1]
        return names[0], names[0], names[1]

    # ---------------------------------------------------------------- statements

    def stmt(self, node: dict, ctx: FnCtx, out: Stmts) -> None:
        kind = node["ast_type"]
        handler = getattr(self, f"stmt_{kind}", None)
        try:
            if handler is None:
                raise Hole(f"statement {kind}")
            handler(node, ctx, out)
        except Hole as hole:
            out.add(self.hole(str(hole), node), ctx.depth)

    def body(self, stmts: list[dict], ctx: FnCtx, out: Stmts) -> None:
        for s in stmts:
            self.stmt(s, ctx, out)

    def with_pre(self, ctx: FnCtx, out: Stmts, build) -> None:
        pre = Stmts()
        text = build(pre)
        out.lines.extend(pre.lines)
        if text is not None:
            out.add(text, ctx.depth)

    def stmt_Pass(self, node: dict, ctx: FnCtx, out: Stmts) -> None:
        pass

    def stmt_Break(self, node: dict, ctx: FnCtx, out: Stmts) -> None:
        out.add("break;", ctx.depth)

    def stmt_Continue(self, node: dict, ctx: FnCtx, out: Stmts) -> None:
        out.add("continue;", ctx.depth)

    def stmt_Assert(self, node: dict, ctx: FnCtx, out: Stmts) -> None:
        msg = node.get("msg")
        if msg is not None and msg.get("ast_type") == "Name" and msg.get("id") == "UNREACHABLE":
            self.note(f"assert …, UNREACHABLE compiles to INVALID (consumes all gas) — line {node.get('lineno')}")
        self.with_pre(ctx, out, lambda pre: f"require({unparen(self.expr(node['test'], ctx, pre))});")

    def stmt_Raise(self, node: dict, ctx: FnCtx, out: Stmts) -> None:
        exc = node.get("exc")
        if exc is not None and exc.get("ast_type") == "Name" and exc.get("id") == "UNREACHABLE":
            self.note(f"raise UNREACHABLE compiles to INVALID (consumes all gas) — line {node.get('lineno')}")
        out.add("require(false);", ctx.depth)

    def bind_call(self, decl: str, surface: str, value: str, pre: Stmts) -> str | None:
        """Bind a hoisted call directly to the declared name when it is the last hoisted binding."""
        if pre.lines and value.startswith("__c"):
            last = pre.lines[-1]
            if f"var {value} = " in last:
                pre.lines[-1] = last.replace(f"var {value} = ", f"{decl} {surface} = ", 1)
                return None
        return f"{decl} {surface} = {unparen(value)};"

    def stmt_AnnAssign(self, node: dict, ctx: FnCtx, out: Stmts) -> None:
        name = node["target"]["id"]
        ty = self.type_of_annotation(node["annotation"], ctx.module)
        value = node.get("value")
        if value is None:
            raise Hole(f"declaration of {name} without a value")
        decl = self.local_decl(ty, name, ctx.module).rsplit(" ", 1)[0]
        if is_builtin_call(value, "raw_call"):
            def build_raw(pre: Stmts) -> str | None:
                text, ok, data = self.raw_call(value, ctx, pre, None)
                surface = self.declare_local(ctx, name, ty)
                if text.startswith("tuple("):
                    raise Hole("raw_call with two results bound to one name")
                return f"{decl} {surface} = {text};"
            self.with_pre(ctx, out, build_raw)
            return
        if value.get("ast_type") == "Call" and value["func"].get("ast_type") == "Attribute" \
                and value["func"]["attr"] == "pop" and (value["func"].get("type") or {}).get("typeclass") == "member_function":
            self.pop_binding(decl, name, value, ctx, out, ty)
            return

        def build(pre: Stmts) -> str | None:
            text = self.expr(value, ctx, pre)
            surface = self.declare_local(ctx, name, ty)
            return self.bind_call(decl, surface, text, pre)
        self.with_pre(ctx, out, build)

    def pop_binding(self, decl: str, name: str, value: dict, ctx: FnCtx, out: Stmts, ty: VType) -> None:
        def build(pre: Stmts) -> str:
            target = self.expr(value["func"]["value"], ctx, pre)
            surface = self.declare_local(ctx, name, ty)
            pre.add(f"{decl} {surface} = {target}[{target}.length - 1];", ctx.depth)
            return f"{target}.pop();"
        self.with_pre(ctx, out, build)

    def stmt_Assign(self, node: dict, ctx: FnCtx, out: Stmts) -> None:
        target = node["target"]
        value = node["value"]
        if target.get("ast_type") == "Tuple":
            self.tuple_assign(target["elements"], value, ctx, out)
            return
        if is_builtin_call(value, "raw_call"):
            def build_raw(pre: Stmts) -> str:
                text, _, _ = self.raw_call(value, ctx, pre, None)
                return f"{self.lvalue(target, ctx, pre)} = {text};"
            self.with_pre(ctx, out, build_raw)
            return

        def build(pre: Stmts) -> str:
            text = self.expr(value, ctx, pre)
            return f"{self.lvalue(target, ctx, pre)} = {unparen(text)};"
        self.with_pre(ctx, out, build)

    def tuple_assign(self, targets: list[dict], value: dict, ctx: FnCtx, out: Stmts) -> None:
        def build(pre: Stmts) -> None:
            if is_builtin_call(value, "raw_call"):
                _, ok, data = self.raw_call(value, ctx, pre, None)
                parts = [ok, data]
            elif value.get("ast_type") == "Tuple":
                parts = []
                for e in value["elements"]:
                    tmp = f"__t{ctx.tmp}"
                    ctx.tmp += 1
                    pre.add(f"var {tmp} = {unparen(self.expr(e, ctx, pre))};", ctx.depth)
                    parts.append(tmp)
            else:
                text = self.expr(value, ctx, pre)
                parts = [f"{text}.{i}" for i in range(len(targets))]
            for t, p in zip(targets, parts):
                pre.add(f"{self.lvalue(t, ctx, pre)} = {p};", ctx.depth)
            return None
        self.with_pre(ctx, out, build)

    def lvalue(self, target: dict, ctx: FnCtx, pre: Stmts) -> str:
        kind = target.get("ast_type")
        if kind == "Name":
            name = target["id"]
            if name in ctx.locals:
                return ctx.local(name)
            var = ctx.module.variables.get(name)
            if var is not None and var.get("is_immutable"):
                return ctx.module.var_name(name)
            raise Hole(f"assignment target {name}")
        if kind in ("Attribute", "Subscript"):
            return self.expr(target, ctx, pre)
        raise Hole(f"assignment target {kind}")

    def stmt_AugAssign(self, node: dict, ctx: FnCtx, out: Stmts) -> None:
        op = node["op"]["ast_type"]
        ty = self.ntype(node["target"])

        def build(pre: Stmts) -> str:
            lhs = self.lvalue(node["target"], ctx, pre)
            rhs = self.expr(node["value"], ctx, pre)
            if ty is not None and ty.kind == "flag" and op in ("BitAnd", "BitOr", "BitXor"):
                return f"{lhs} = ({lhs} {BITWISE[op]}[uint256] {rhs});"
            if ty is None or not ty.is_int:
                raise Hole(f"augmented assignment on {ty.name if ty else '?'}")
            t = ty.surface_int
            if op in CHECKED:
                return f"{lhs} = (({lhs} {CHECKED[op]} {rhs}) as {t});"
            if op == "FloorDiv":
                return f"{lhs} = {'sdiv(' + lhs + ', ' + rhs + ')' if ty.signed else '(' + lhs + ' / ' + rhs + ')'};"
            if op == "Mod":
                return f"{lhs} = {'srem(' + lhs + ', ' + rhs + ')' if ty.signed else '(' + lhs + ' % ' + rhs + ')'};"
            if op in BITWISE:
                return f"{lhs} = ({lhs} {BITWISE[op]}[{t}] {rhs});"
            raise Hole(f"augmented operator {op}")
        self.with_pre(ctx, out, build)

    def stmt_If(self, node: dict, ctx: FnCtx, out: Stmts) -> None:
        pre = Stmts()
        cond = self.expr(node["test"], ctx, pre)
        out.lines.extend(pre.lines)
        out.add(f"if ({unparen(cond)}) {{", ctx.depth)
        self.nested(node["body"], ctx, out)
        orelse = node.get("orelse") or []
        while orelse:
            if len(orelse) == 1 and orelse[0].get("ast_type") == "If":
                sub = orelse[0]
                pre = Stmts()
                cond = self.expr(sub["test"], ctx, pre)
                if pre.lines:
                    # hoisted calls in an elif condition: nest the chain under else
                    out.add("} else {", ctx.depth)
                    ctx.depth += 1
                    out.lines.extend(pre.lines)
                    out.add(f"if ({unparen(cond)}) {{", ctx.depth)
                    self.nested(sub["body"], ctx, out)
                    if sub.get("orelse"):
                        out.add("} else {", ctx.depth)
                        self.nested(sub["orelse"], ctx, out)
                    out.add("}", ctx.depth)
                    ctx.depth -= 1
                    orelse = []
                    break
                out.add(f"}} else if ({unparen(cond)}) {{", ctx.depth)
                self.nested(sub["body"], ctx, out)
                orelse = sub.get("orelse") or []
            else:
                out.add("} else {", ctx.depth)
                self.nested(orelse, ctx, out)
                orelse = []
        out.add("}", ctx.depth)

    def nested(self, stmts: list[dict], ctx: FnCtx, out: Stmts) -> None:
        ctx.depth += 1
        self.body(stmts, ctx, out)
        ctx.depth -= 1

    def stmt_For(self, node: dict, ctx: FnCtx, out: Stmts) -> None:
        target = node["target"]
        var = target["target"]["id"]
        vty = self.type_of_annotation(target["annotation"], ctx.module)
        it = node["iter"]
        pre = Stmts()
        if it.get("ast_type") == "Call" and it["func"].get("ast_type") == "Name" and it["func"]["id"] == "range":
            args = it.get("args", [])
            kw = self.kwargs(it)
            t = self.stype(vty, ctx.module)
            if len(args) == 1:
                start, stop = "0", self.expr(args[0], ctx, pre)
            else:
                start, stop = self.expr(args[0], ctx, pre), self.expr(args[1], ctx, pre)
            if "bound" in kw:
                bound = self.const_int(kw["bound"], ctx.module)
                if len(args) == 1:
                    pre.add(f"require({stop} <= {bound});", ctx.depth)
                else:
                    pre.add(f"require({start} <= {stop});", ctx.depth)
                    pre.add(f"require({stop} - {start} <= {bound});", ctx.depth)
            elif len(args) == 2 and node_int(args[0]) is None:
                # range(x, x + N): the end is checked arithmetic, iterations are exactly N
                pass
            out.lines.extend(pre.lines)
            v = self.declare_local(ctx, var, vty)
            out.add(f"for ({t} {v} = {start}; {v} < {stop}; {v}++) {{", ctx.depth)
            self.nested(node["body"], ctx, out)
            out.add("}", ctx.depth)
            return
        ity = self.ntype(it)
        if ity is None or ity.kind not in ("dynarray", "sarray"):
            raise Hole("for over a non-array")
        elems = self.list_elements(it, ctx)
        if elems is not None and it.get("ast_type") == "List":
            raise Hole("for over a list literal")
        seq = self.expr(it, ctx, pre)
        idx = f"__i{ctx.tmp}"
        n = f"__n{ctx.tmp}"
        ctx.tmp += 1
        out.lines.extend(pre.lines)
        length = str(ity.length) if ity.kind == "sarray" else f"{seq}.length"
        out.add(f"uint256 {n} = {length};", ctx.depth)
        self.note(f"for … in {seq}: Vyper iterates over the array as read at loop entry — line {node.get('lineno')}")
        out.add(f"for (uint256 {idx} = 0; {idx} < {n}; {idx}++) {{", ctx.depth)
        ctx.depth += 1
        self.declare_local(ctx, var, vty)
        out.add(f"{self.local_decl(vty, var, ctx.module, ctx)} = {seq}[{idx}];", ctx.depth)
        self.body(node["body"], ctx, out)
        ctx.depth -= 1
        out.add("}", ctx.depth)

    def stmt_Return(self, node: dict, ctx: FnCtx, out: Stmts) -> None:
        value = node.get("value")
        if value is None:
            out.add("return;", ctx.depth)
            return

        def build(pre: Stmts) -> str:
            if value.get("ast_type") == "Tuple":
                parts = [unparen(self.expr(e, ctx, pre)) for e in value["elements"]]
                return f"return ({', '.join(parts)});"
            text = self.expr(value, ctx, pre)
            if ctx.returns is not None and ctx.returns.kind == "tuple" and text.startswith("__c"):
                parts = [f"{text}.{i}" for i in range(len(ctx.returns.members))]
                return f"return ({', '.join(parts)});"
            return f"return {unparen(text)};"
        self.with_pre(ctx, out, build)

    def stmt_Log(self, node: dict, ctx: FnCtx, out: Stmts) -> None:
        call = node["value"]
        ety = call["func"].get("type", {}).get("type_t") or node.get("type") or {}
        ekey = decl_key(ety.get("type_decl_node"))
        edef = self.nodes.get(ekey) if ekey else None
        if edef is None or edef.get("ast_type") != "EventDef":
            edef = next((m.events[ety.get("name")] for m in self.all_modules(ctx.module)
                         if ety.get("name") in m.events), None)
        if edef is None:
            raise Hole(f"event {ety.get('name')}")
        names = [m["target"]["id"] for m in edef["body"] if m.get("ast_type") == "AnnAssign"]

        def build(pre: Stmts) -> str:
            values: dict[str, str] = {}
            for n, a in zip(names, call.get("args", [])):
                values[n] = self.expr(a, ctx, pre)
            for kw in call.get("keywords", []):
                values[kw["arg"]] = self.expr(kw["value"], ctx, pre)
            return f"emit {edef['name']}({', '.join(values[n] for n in names)});"
        self.with_pre(ctx, out, build)

    def stmt_Expr(self, node: dict, ctx: FnCtx, out: Stmts) -> None:
        e = node["value"]
        kind = e.get("ast_type")
        if kind == "Call":
            func = e["func"]
            if func.get("ast_type") == "Name":
                name = func["id"]
                if name == "send":
                    def build_send(pre: Stmts) -> None:
                        to = self.receiver(e["args"][0], ctx, pre)
                        value = self.expr(e["args"][1], ctx, pre)
                        kw = self.kwargs(e)
                        if "gas" in kw:
                            self.note(f"send gas option dropped — line {e.get('lineno')}")
                        pre.add(f"(bool __ok{ctx.tmp}, bytes memory __data{ctx.tmp}) = {to}.call{{value: {value}}}(new bytes(0));", ctx.depth)
                        pre.add(f"require(__ok{ctx.tmp});", ctx.depth)
                        ctx.tmp += 1
                        self.note("send(to, value) forwards no gas beyond the EVM stipend")
                        return None
                    self.with_pre(ctx, out, build_send)
                    return
                if name == "raw_call":
                    self.with_pre(ctx, out, lambda pre: self.raw_call(e, ctx, pre, None) and None)
                    return
                if name == "raw_revert":
                    out.add("require(false);", ctx.depth)
                    return
                if name in ("print", "breakpoint"):
                    return
                if name in ("raw_log", "selfdestruct"):
                    raise Hole(f"{name}()")
            if func.get("ast_type") == "Attribute" and (func.get("type") or {}).get("typeclass") == "member_function":
                member = func["attr"]
                if member == "append":
                    def build_push(pre: Stmts) -> str:
                        target = self.expr(func["value"], ctx, pre)
                        return f"{target}.push({self.expr(e['args'][0], ctx, pre)});"
                    self.with_pre(ctx, out, build_push)
                    return
                if member == "pop":
                    self.with_pre(ctx, out, lambda pre: f"{self.expr(func['value'], ctx, pre)}.pop();")
                    return
                raise Hole(f"method {member}")
        if kind in ("Call", "ExtCall", "StaticCall"):
            def build_call(pre: Stmts) -> None:
                self.expr(e, ctx, pre)
                return None
            self.with_pre(ctx, out, build_call)
            return
        raise Hole(f"expression statement {kind}")

    # ---------------------------------------------------------------- functions

    @staticmethod
    def decorators(fn: dict) -> list[str]:
        names = []
        for d in fn.get("decorator_list", []):
            if d.get("ast_type") == "Name":
                names.append(d["id"])
            elif d.get("ast_type") == "Call" and d["func"].get("ast_type") == "Name":
                names.append(d["func"]["id"])
        return names

    def is_nonreentrant(self, fn: dict, mod: Module) -> bool:
        decs = self.decorators(fn)
        if "nonreentrant" in decs:
            return True
        if mod.nonreentrant_pragma and "reentrant" not in decs and "external" in decs \
                and fn["name"] != "__init__":
            return True
        return False

    def mutability(self, fn: dict) -> str:
        decs = self.decorators(fn)
        for m in ("payable", "view", "pure"):
            if m in decs:
                return m
        return "nonpayable"

    def param_types(self, fn: dict, mod: Module) -> list[tuple[str, VType]]:
        return [(a["arg"], self.type_of_annotation(a["annotation"], mod)) for a in fn["args"]["args"]]

    def return_type(self, fn: dict, mod: Module) -> VType | None:
        if fn.get("returns") is None:
            return None
        return self.type_of_annotation(fn["returns"], mod)

    def returns_text(self, rty: VType | None, mod: Module) -> str:
        if rty is None:
            return ""
        if rty.kind == "tuple":
            return ", ".join(self.stype(m, mod) + (" memory" if self.is_memory(m) else "") for m in rty.members)
        return self.stype(rty, mod) + (" memory" if self.is_memory(rty) else "")

    def params_text(self, params: list[tuple[str, VType]], mod: Module, ctx: FnCtx | None = None) -> str:
        return ", ".join(self.local_decl(t, n, mod, ctx) for n, t in params)

    def lock_values(self) -> tuple[int, int]:
        """(temporary value while locked, final value after) of the compiler's lock protocol."""
        return (1, 0) if self.uses_transient_lock else (2, 3)

    def render_function(self, mod: Module, fn: dict, external: bool, name: str,
                        arity: int | None = None) -> list[str]:
        params = self.param_types(fn, mod)
        defaults = fn["args"].get("defaults") or []
        n_required = len(params) - len(defaults)
        arity = len(params) if arity is None else arity
        rty = self.return_type(fn, mod)
        ctx = FnCtx(mod, fn, rty)
        for n, t in params:
            self.declare_local(ctx, n, t)
        locked = self.is_nonreentrant(fn, mod)
        body_name = f"{name}_body"
        vis = "external" if external else "internal"
        mods = [vis] + (["payable"] if external and self.mutability(fn) == "payable" else [])
        head = f"function {ident(name)}({self.params_text(params[:arity], mod, ctx)}) {' '.join(mods)}"
        try:
            ret_text = self.returns_text(rty, mod)
        except Hole as hole:
            ret_text = ""
            head = f"{self.hole(str(hole), fn)}\n  " + head
        if ret_text:
            head += f" returns ({ret_text})"
        out = Stmts()
        for i in range(arity, len(params)):
            n, t = params[i]
            try:
                self.with_pre(ctx, out, lambda pre, n=n, t=t, i=i: self.bind_call(
                    self.local_decl(t, n, mod).rsplit(" ", 1)[0], ctx.local(n),
                    self.expr(defaults[i - n_required], ctx, pre), pre))
            except Hole as hole:
                out.add(self.hole(f"default of {n}: {hole}", fn), 1)
        if locked:
            self.lock_used = True
            temp, final = self.lock_values()
            view = self.mutability(fn) in ("view", "pure")
            out.add(f"require({LOCK_NAME} != {temp});", 1)
            if not view:
                out.add(f"{LOCK_NAME} = {temp};", 1)
            args = ", ".join(ctx.local(n) for n, _ in params)
            out.add(f"var __r = {ident(body_name)}({args});", 1)
            if not view:
                out.add(f"{LOCK_NAME} = {final};", 1)
            if rty is not None:
                if rty.kind == "tuple":
                    out.add(f"return ({', '.join(f'__r.{i}' for i in range(len(rty.members)))});", 1)
                else:
                    out.add("return __r;", 1)
            key = (mod.source_id, mod.alias_path, fn["node_id"], "body")
            if key not in self.needed_keys:
                self.needed_keys.add(key)
                self.lock_wrapped.append((mod, fn))
        else:
            try:
                self.body(fn.get("body", []), ctx, out)
            except Hole as hole:
                out.add(self.hole(str(hole), fn), 1)
        return [f"  {head} {{", *["  " + l for l in out.lines], "  }", ""]

    def render_body_function(self, mod: Module, fn: dict, name: str) -> list[str]:
        """The unlocked body of a nonreentrant function, as an internal function."""
        params = self.param_types(fn, mod)
        rty = self.return_type(fn, mod)
        ctx = FnCtx(mod, fn, rty)
        for n, t in params:
            self.declare_local(ctx, n, t)
        head = f"function {ident(name)}_body({self.params_text(params, mod, ctx)}) internal"
        ret_text = self.returns_text(rty, mod)
        if ret_text:
            head += f" returns ({ret_text})"
        out = Stmts()
        try:
            self.body(fn.get("body", []), ctx, out)
        except Hole as hole:
            out.add(self.hole(str(hole), fn), 1)
        return [f"  {head} {{", *["  " + l for l in out.lines], "  }", ""]

    def render_getter(self, mod: Module, var: dict, name: str) -> tuple[str, list[str]]:
        ty = self.type_of_annotation(var["annotation"], mod)
        params: list[str] = []
        abi_params: list[str] = []
        path = mod.var_name(var["target"]["id"])
        depth = 0
        while True:
            if ty.kind == "hashmap":
                params.append(f"{self.stype(ty.key, mod)} arg{depth}")
                abi_params.append(self.abi_type(ty.key, mod))
                path += f"[arg{depth}]"
                ty = ty.value
            elif ty.kind in ("dynarray", "sarray"):
                params.append(f"uint256 arg{depth}")
                abi_params.append("uint256")
                path += f"[arg{depth}]"
                ty = ty.value
            else:
                break
            depth += 1
        if ty.kind == "struct":
            # Vyper returns the struct as an ABI tuple; with static members that is the
            # concatenation of the fields, which the spec returns one by one (read in order).
            found = self.struct_def(ty, mod)
            if found is None:
                raise Hole(f"unresolved struct {ty.name}")
            smod, sdef = found
            fields = self.struct_fields(sdef, smod)
            if all(not self.is_memory(t) for _, t in fields):
                ret_text = ", ".join(self.stype(t, smod) for _, t in fields)
                values = ", ".join(f"{path}.{ident(n)}" for n, _ in fields)
                body = f"return ({values});" if len(fields) > 1 else f"return {values};"
                head = f"function {ident(name)}({', '.join(params)}) external returns ({ret_text})"
                return f"{name}({','.join(abi_params)})", [f"  {head} {{", f"    {body}", "  }", ""]
            self.note(f"getter {name} returns a struct with dynamic members: the ABI tuple encoding "
                      "carries a head offset the flat return does not")
        ret_text = self.returns_text(ty, mod)
        head = f"function {ident(name)}({', '.join(params)}) external returns ({ret_text})"
        lines = [f"  {head} {{", f"    return {path};", "  }", ""]
        return f"{name}({','.join(abi_params)})", lines

    def canonical_signature(self, name: str, params: list[tuple[str, VType]], mod: Module) -> str:
        return f"{name}({','.join(self.abi_type(t, mod) for _, t in params)})"

    def selector_value(self, sig: str) -> int:
        if sig in self.method_identifiers:
            return int(self.method_identifiers[sig], 16)
        from evm_tools import selector
        return int.from_bytes(selector(sig), "big")

    # ---------------------------------------------------------------- the external surface

    def external_entries(self) -> list[tuple[str, list[str]]]:
        """(canonical signature, rendered transition) for every selector."""
        entries: list[tuple[str, list[str]]] = []
        surface: list[tuple[Module, str, dict]] = []     # (module, ABI name, FunctionDef)
        getters: list[tuple[Module, str, dict]] = []
        for fname, fn in self.main.functions.items():
            if "external" in self.decorators(fn) and fname != "__default__":
                surface.append((self.main, fname, fn))
        for vname, var in self.main.variables.items():
            if var.get("is_public") and not var.get("is_constant"):
                getters.append((self.main, vname, var))
        for alias, member in self.main.exports:
            mod = self.main.imports.get(alias)
            if mod is None:
                self.holes.append(f"exports from unknown module {alias}")
                continue
            if member == "__interface__":
                for fname, fn in mod.functions.items():
                    if "external" in self.decorators(fn) and fname != "__default__":
                        surface.append((mod, fname, fn))
                for vname, var in mod.variables.items():
                    if var.get("is_public") and not var.get("is_constant"):
                        getters.append((mod, vname, var))
            elif member in mod.functions:
                surface.append((mod, member, mod.functions[member]))
            elif member in mod.variables:
                getters.append((mod, member, mod.variables[member]))
            else:
                self.holes.append(f"exports {alias}.{member} not found")
        for mod, vname, var in getters:
            try:
                sig, lines = self.render_getter(mod, var, vname)
                entries.append((sig, lines))
                self.variants.append({"signature": sig, "name": vname, "params": [], "getter": True})
            except Hole as hole:
                entries.append((f"{vname}()", ["  " + self.hole(f"getter {vname}: {hole}", var), ""]))
        for mod, fname, fn in surface:
            try:
                params = self.param_types(fn, mod)
            except Hole as hole:
                entries.append((f"{fname}()", ["  " + self.hole(f"{fname}: {hole}", fn), ""]))
                continue
            n_defaults = len(fn["args"].get("defaults") or [])
            for arity in range(len(params) - n_defaults, len(params) + 1):
                sig = self.canonical_signature(fname, params[:arity], mod)
                entries.append((sig, self.render_function(mod, fn, True, fname, arity)))
                bounded = [(n, self.capacity_text(t)) for n, t in params[:arity] if self.has_capacity(t)]
                self.variants.append({"signature": sig, "name": fname,
                                      "params": [{"name": n, "type": self.abi_type(t, mod),
                                                  "vyperType": self.vyper_type_text(t, mod)} for n, t in params[:arity]],
                                      "bounded": [n for n, _ in bounded]})
                if bounded:
                    self.note(f"{sig}: bounded parameters " + ", ".join(f"{n}: {c}" for n, c in bounded)
                              + " (declare them for externalABI.withVyperABI)")
        # Selector order, with the variants of one source name adjacent at the first one's
        # position: the order `scaffold.py`'s selector table derives from `SpecSyntax.lean`.
        entries.sort(key=lambda e: self.selector_value(e[0]))
        grouped: list[tuple[str, list[str]]] = []
        seen: set[str] = set()
        for sig, _ in entries:
            name = sig.split("(", 1)[0]
            if name in seen:
                continue
            seen.add(name)
            grouped += [e for e in entries if e[0].split("(", 1)[0] == name]
        return grouped

    @staticmethod
    def has_capacity(t: VType) -> bool:
        if t.kind in ("dynarray", "bytes", "string"):
            return True
        if t.kind in ("sarray",) and t.value is not None:
            return Translator.has_capacity(t.value)
        return False

    def capacity_text(self, t: VType) -> str:
        return self.vyper_type_text(t, self.main)

    def vyper_type_text(self, t: VType, mod: Module) -> str:
        if t.kind == "dynarray":
            return f"DynArray[{self.vyper_type_text(t.value, mod)}, {t.length}]"
        if t.kind == "bytes":
            return f"Bytes[{t.length}]"
        if t.kind == "string":
            return f"String[{t.length}]"
        if t.kind == "sarray":
            return f"{self.vyper_type_text(t.value, mod)}[{t.length}]"
        if t.kind == "hashmap":
            return f"HashMap[{self.vyper_type_text(t.key, mod)}, {self.vyper_type_text(t.value, mod)}]"
        if t.kind == "bytesM":
            return f"bytes{t.bits}"
        return t.name

    def render_constructor(self) -> list[str]:
        fn = self.main.functions.get("__init__")
        if fn is None:
            return []
        params = self.param_types(fn, self.main)
        ctx = FnCtx(self.main, fn, None, in_ctor=True)
        for n, t in params:
            self.declare_local(ctx, n, t)
        out = Stmts()
        try:
            self.body(fn.get("body", []), ctx, out)
        except Hole as hole:
            out.add(self.hole(str(hole), fn), 1)
        mods = " payable" if self.mutability(fn) == "payable" else ""
        if not out.lines and not params:
            return []
        return [f"  constructor({self.params_text(params, self.main, ctx)}){mods} {{", *["  " + l for l in out.lines], "  }", ""]

    def render_default(self) -> list[str]:
        fn = self.main.functions.get("__default__")
        if fn is None:
            return []
        self.has_default = True
        ctx = FnCtx(self.main, fn, None)
        out = Stmts()
        locked = self.is_nonreentrant(fn, self.main)
        if locked:
            self.lock_used = True
            temp, final = self.lock_values()
            out.add(f"require({LOCK_NAME} != {temp});", 1)
            out.add(f"{LOCK_NAME} = {temp};", 1)
            out.add("var __r = __default___body();", 1)
            out.add(f"{LOCK_NAME} = {final};", 1)
            self.lock_wrapped.append((self.main, fn))
        else:
            try:
                self.body(fn.get("body", []), ctx, out)
            except Hole as hole:
                out.add(self.hole(str(hole), fn), 1)
        mods = ["external"] + (["payable"] if self.mutability(fn) == "payable" else [])
        return [f"  fallback() {' '.join(mods)} {{", *["  " + l for l in out.lines], "  }", ""]

    # ---------------------------------------------------------------- storage

    def storage_items(self) -> tuple[list[str], list[str]]:
        """(persistent declarations, transient declarations) in the compiler's layout order."""
        persistent: list[tuple[int, str, Module, dict | None]] = []
        transient: list[tuple[int, str, Module, dict | None]] = []

        def collect(layout: dict, mod: Module, out: list) -> None:
            for key, entry in layout.items():
                if key == "$.nonreentrant_key":
                    out.append((entry.get("slot", 0), LOCK_NAME, mod, None))
                elif isinstance(entry, dict) and "slot" in entry:
                    var = mod.variables.get(key)
                    if var is None:
                        self.holes.append(f"layout entry {mod.prefix}{key} has no declaration")
                        continue
                    out.append((entry["slot"], key, mod, var))
                elif isinstance(entry, dict) and key in mod.imports:
                    collect(entry, mod.imports[key], out)
                else:
                    self.holes.append(f"layout entry {key} not understood")
        if self.layout:
            collect(self.layout.get("storage_layout", {}), self.main, persistent)
            collect(self.layout.get("transient_storage_layout", {}), self.main, transient)
            persistent.sort(key=lambda p: p[0])
            transient.sort(key=lambda p: p[0])
            persistent = self.fill_gaps(persistent, self.layout.get("storage_layout", {}))
            transient = self.fill_gaps(transient, self.layout.get("transient_storage_layout", {}))
        else:
            self.note("no <Name>.storage.json: storage is in source order (modules at their `initializes`)")
            self.source_order(self.main, persistent, transient)
        lines_p = [self.storage_line(k, m, v, False) for _, k, m, v in persistent]
        lines_t = [self.storage_line(k, m, v, True) for _, k, m, v in transient]
        def fact(slot: int, k: str, m: Module, v: dict | None, transient: bool) -> dict:
            if v is None:
                kind = "nonreentrant lock"
            elif v.get("reserved"):
                kind = "reserved"
            else:
                kind = self.vyper_type_text(self.type_of_annotation(v["annotation"], m), m)
            return {"name": k if v is None or v.get("reserved") else m.var_name(k), "slot": slot,
                    "transient": transient, "vyperType": kind}
        self.storage_facts = [fact(slot, k, m, v, False) for slot, k, m, v in persistent] + \
                             [fact(slot, k, m, v, True) for slot, k, m, v in transient]
        if self.lock_used and not any(k == LOCK_NAME for _, k, _, _ in persistent + transient):
            if self.uses_transient_lock:
                lines_t.insert(0, f"  uint256 transient {LOCK_NAME};")
            else:
                lines_p.insert(0, f"  uint256 {LOCK_NAME};")
        return lines_p, lines_t

    def fill_gaps(self, items: list, layout: dict) -> list:
        """Pad slots the compiler reserved but declared nothing in (pre-Cancun Vyper keeps slot 0
        for the reentrancy key even when no function is nonreentrant), so that `vyperStorage!`
        on the declaration order reproduces the layout."""
        sizes: dict[tuple[str, int], int] = {}

        def collect(node: dict, mod: Module) -> None:
            for key, entry in node.items():
                if isinstance(entry, dict) and "slot" in entry:
                    sizes[(LOCK_NAME if key == "$.nonreentrant_key" else key, id(mod))] = entry.get("n_slots", 1)
                elif isinstance(entry, dict) and key in mod.imports:
                    collect(entry, mod.imports[key])
        collect(layout, self.main)
        out: list = []
        expected = 0
        for slot, key, mod, var in items:
            while expected < slot:
                out.append((expected, f"__reserved_{expected}", mod, {"reserved": True}))
                self.note(f"storage slot {expected} is reserved by the compiler (padded with __reserved_{expected})")
                expected += 1
            out.append((slot, key, mod, var))
            expected = slot + sizes.get((key, id(mod)), 1)
        return out

    def source_order(self, mod: Module, persistent: list, transient: list) -> None:
        for item in mod.node.get("body", []):
            kind = item.get("ast_type")
            if kind == "VariableDecl" and not item.get("is_constant") and not item.get("is_immutable"):
                (transient if item.get("is_transient") else persistent).append((0, item["target"]["id"], mod, item))
            elif kind == "InitializesDecl":
                ann = item["annotation"]
                base = ann["value"] if ann.get("ast_type") == "Subscript" else ann
                sub = mod.imports.get(base.get("id"))
                if sub is not None:
                    self.source_order(sub, persistent, transient)

    def storage_line(self, key: str, mod: Module, var: dict | None, transient: bool) -> str:
        if var is None:
            return f"  uint256{' transient' if transient else ''} {LOCK_NAME};"
        if var.get("reserved"):
            return f"  uint256{' transient' if transient else ''} {key};"
        try:
            t = self.stype(self.type_of_annotation(var["annotation"], mod), mod)
        except Hole as hole:
            return "  " + self.hole(f"storage {mod.prefix}{key}: {hole}", var)
        return f"  {t}{' transient' if transient else ''} {mod.var_name(key)};"

    def immutable_items(self) -> list[str]:
        lines = []
        for mod in self.all_modules(self.main):
            for name, var in mod.variables.items():
                if var.get("is_immutable"):
                    try:
                        ty = self.type_of_annotation(var["annotation"], mod)
                        if ty.kind not in ("int", "bool", "address", "bytesM", "interface", "flag"):
                            raise Hole(f"immutable {mod.prefix}{name} of type {self.vyper_type_text(ty, mod)}")
                        lines.append(f"  {self.stype(ty, mod)} immutable {mod.var_name(name)};")
                    except Hole as hole:
                        lines.append("  " + self.hole(str(hole), var))
        return lines

    def event_items(self) -> list[str]:
        lines = []
        for mod in self.all_modules(self.main):
            for name, ev in mod.events.items():
                ps = []
                for m in ev.get("body", []):
                    if m.get("ast_type") != "AnnAssign":
                        continue
                    ann = m["annotation"]
                    indexed = ann.get("ast_type") == "Call" and ann["func"].get("id") == "indexed"
                    try:
                        t = self.stype(self.type_of_annotation(ann, mod), mod)
                    except Hole:
                        t = "uint256"
                    ps.append(f"{t}{' indexed' if indexed else ''} {ident(m['target']['id'])}")
                lines.append(f"  event {name}({', '.join(ps)});")
        return lines

    # ---------------------------------------------------------------- rendering

    def render(self, namespace: str, order: str) -> str:
        for mod in self.all_modules(self.main):
            if (mod.node.get("settings") or {}).get("nonreentrancy_by_default"):
                mod.nonreentrant_pragma = True   # `# pragma nonreentrancy on`
        entries = self.external_entries()
        ctor_lines = self.render_constructor()
        default_lines = self.render_default()
        internal_lines: list[str] = []
        done: set = set()
        while True:
            pending = [(m, f) for m, f in self.needed if (m.source_id, m.alias_path, f["node_id"]) not in done]
            pending_bodies = [(m, f) for m, f in self.lock_wrapped if (m.source_id, m.alias_path, f["node_id"], "b") not in done]
            if not pending and not pending_bodies:
                break
            for m, f in pending:
                done.add((m.source_id, m.alias_path, f["node_id"]))
                internal_lines += self.render_function(m, f, False, m.fn_name(f["name"]))
            for m, f in pending_bodies:
                done.add((m.source_id, m.alias_path, f["node_id"], "b"))
                internal_lines += self.render_body_function(m, f, m.fn_name(f["name"]))
        storage_lines, transient_lines = self.storage_items()
        immutable_lines = self.immutable_items()
        event_lines = self.event_items()
        struct_lines: list[str] = []
        emitted = 0
        while emitted < len(self.used_structs):
            smod, sdef = self.used_structs[emitted]
            emitted += 1
            struct_lines.append(f"  struct {self.struct_names[(smod.source_id, sdef['node_id'])]} {{")
            for n, t in self.struct_fields(sdef, smod):
                try:
                    struct_lines.append(f"    {self.stype(t, smod)} {ident(n)};")
                except Hole as hole:
                    struct_lines.append("    " + self.hole(str(hole), sdef))
            struct_lines += ["  }", ""]
        header = ["/-!", f"# {self.main_name} spec draft (generated by `scripts/vy2solm.py`)", ""]
        header.append(f"Source `{module_path(self.main)}`, Vyper 0.4 annotated AST, EVM version "
                      f"{self.evm_version}; modules: "
                      + (", ".join(module_path(m) for m in self.all_modules(self.main) if m is not self.main) or "none") + ".")
        header.append("Transitions are in selector order, the variants of one source function adjacent.")
        if self.lock_used:
            temp, final = self.lock_values()
            where = "transient slot" if self.uses_transient_lock else "storage slot"
            header.append(f"`@nonreentrant` uses the compiler's lock in `{LOCK_NAME}` ({where}, {temp} while locked, "
                          f"{final} after; view functions only check).")
        if self.holes:
            header += ["", f"HOLES ({len(self.holes)}):"] + [f"  - {h}" for h in self.holes]
        if self.notes:
            header += ["", "NOTES:"] + [f"  - {n}" for n in self.notes]
        if self.external_calls:
            header += ["", "External calls (for the spec's `ExternalCallABI`):"]
            for call in self.external_calls.values():
                header.append(f"  - {call['name']}({', '.join(call['params'])})"
                              f"{' view' if call['view'] else ''} returns ({', '.join(call['returns'])})")
        header.append("-/")
        header = [h.replace("/-", "/ -").replace("-/", "- /") if i not in (0, len(header) - 1) else h
                  for i, h in enumerate(header)]
        items = storage_lines + transient_lines + immutable_lines
        body = [*struct_lines, *items, "", *event_lines, "" if event_lines else "", *ctor_lines, *internal_lines]
        for _, lines in entries:
            body += lines
        body += default_lines
        text = ["import Solm.Notation", "", *header, "", "open Solm Solm.Notation", "",
                f"namespace {namespace}.Syntax", "",
                f"def contractSyntax : ContractDecl := solidity% contract {self.main_name} {{",
                *body, "}", "", f"end {namespace}.Syntax", ""]
        return "\n".join(l for l in text)


# ------------------------------------------------------------------------------------ helpers

def walk(node: object):
    if isinstance(node, dict):
        yield node
        for v in node.values():
            yield from walk(v)
    elif isinstance(node, list):
        for v in node:
            yield from walk(v)


def module_path(mod: Module) -> str:
    """The module's source path, relative when the compiler recorded an absolute one."""
    for key in ("resolved_path", "path"):
        text = mod.node.get(key)
        if text and not Path(text).is_absolute():
            return text
    text = mod.node.get("path") or mod.node.get("resolved_path") or mod.node.get("name") or "?"
    return Path(text).name


def describe(node: dict) -> str:
    kind = node.get("ast_type", "?")
    if kind == "Name":
        return node.get("id", "?")
    if kind == "Attribute":
        return f"{describe(node['value'])}.{node['attr']}"
    if kind == "Call":
        return f"{describe(node['func'])}(…)"
    return kind


def is_msg_data(node: dict) -> bool:
    return node.get("ast_type") == "Attribute" and node["attr"] == "data" \
        and node["value"].get("ast_type") == "Name" and node["value"]["id"] == "msg"


def is_builtin_call(node: dict, name: str) -> bool:
    return node.get("ast_type") == "Call" and node["func"].get("ast_type") == "Name" \
        and node["func"].get("id") == name


def load_annotated(directory: Path, contract: str | None) -> tuple[dict, dict, str, dict, dict[str, str]]:
    """(annotated AST, build json, EVM version, storage layout, method identifiers)."""
    builds = sorted(directory.glob("*.build.json"))
    build: dict = {}
    annotated: dict | None = None
    for path in builds:
        candidate = json.loads(path.read_text(encoding="utf-8"))
        if candidate.get("compiler", {}).get("kind") != "vyper":
            continue
        if contract and candidate.get("contract") != contract:
            continue
        build = candidate
        annotated = build.get("ast")
        contract = build.get("contract")
        break
    if annotated is None:
        asts = sorted(directory.glob("*.vy.ast.json"))
        if contract:
            asts = [p for p in asts if p.name == f"{contract}.vy.ast.json"] or asts
        if not asts:
            raise SystemExit(f"{directory}: no Vyper *.build.json with an `ast` entry and no *.vy.ast.json "
                             "(rerun scaffold.py compile --vyper, or save `vyper -f annotated_ast`)")
        annotated = json.loads(asts[0].read_text(encoding="utf-8"))
        contract = contract or asts[0].name.split(".")[0]
    if "ast" not in annotated:
        annotated = {"contract_name": contract, "ast": annotated, "imports": []}
    annotated.setdefault("contract_name", contract)
    evm = build.get("settings", {}).get("evmVersion", "prague")
    layout: dict = {}
    layout_path = directory / f"{contract}.storage.json"
    if layout_path.exists():
        layout = json.loads(layout_path.read_text(encoding="utf-8"))
    return annotated, build, evm, layout, build.get("methodIdentifiers", {})


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("directory", type=Path, help="contract directory with *.build.json or *.vy.ast.json")
    parser.add_argument("--contract", help="contract name (default: from the build json)")
    parser.add_argument("--namespace", help="Lean namespace (default: derived from the directory)")
    parser.add_argument("--output", "-o", type=Path, help="output file (default: stdout)")
    parser.add_argument("--comment-holes", action="store_true",
                        help="write holes as comments instead of failing `${hole …}` splices")
    parser.add_argument("--evm-version", help="override the EVM version (decides the reentrancy lock location)")
    parser.add_argument("--spec-json", type=Path, help="also write external-call and selector facts as JSON")
    args = parser.parse_args(argv)
    annotated, build, evm, layout, method_ids = load_annotated(args.directory, args.contract)
    namespace = args.namespace or ".".join(args.directory.resolve().parts[-2:])
    t = Translator(annotated, args.comment_holes, args.evm_version or evm, layout, method_ids)
    text = t.render(namespace, "selector")
    if args.output:
        args.output.write_text(text, encoding="utf-8")
        print(f"{args.output}: {len(t.holes)} holes, {len(t.notes)} notes")
    else:
        sys.stdout.write(text)
    if args.spec_json:
        args.spec_json.write_text(json.dumps({
            "contract": annotated.get("contract_name"), "compiler": "vyper", "evmVersion": t.evm_version,
            "externalCalls": list(t.external_calls.values()), "selectors": t.variants,
            "storage": t.storage_facts,
            "nonreentrantLock": {"name": LOCK_NAME, "transient": t.uses_transient_lock,
                                 "locked": t.lock_values()[0], "unlocked": t.lock_values()[1]} if t.lock_used else None,
            "holes": t.holes, "notes": t.notes}, indent=2) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
