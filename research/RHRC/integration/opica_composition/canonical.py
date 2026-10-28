"""Closed JSON and content identities for the proposed composition protocol.

No float, repr fallback, arbitrary Python object, duplicate key or path alias is
admitted. This codec is deliberately separate from the existing Lean Expr codec;
do not change existing compiler hashes to this format.
"""
from __future__ import annotations
import hashlib
import json
import re
from pathlib import PurePosixPath
from typing import Any, Iterable

class ContractError(ValueError):
    pass

MAX_BYTES = 8 * 1024 * 1024
MAX_DEPTH = 64
MAX_NODES = 100_000
HEX64 = re.compile(r"[0-9a-f]{64}\Z")


def require(ok: bool, message: str) -> None:
    if not ok:
        raise ContractError(message)


def closed_keys(obj: Any, keys: set[str]) -> dict[str, Any]:
    require(type(obj) is dict and set(obj) == keys, "closed field set differs")
    return obj


def nonempty_text(value: Any, label: str) -> str:
    require(type(value) is str and bool(value.strip()), f"{label}: nonempty text required")
    try:
        value.encode("utf-8", errors="strict")
    except UnicodeError as exc:
        raise ContractError(f"{label}: invalid Unicode") from exc
    return value


def digest_text(value: Any, label: str = "digest") -> str:
    require(type(value) is str and HEX64.fullmatch(value) is not None, f"{label}: lowercase sha256 required")
    return value


MAX_PATH_CHARS = 1024
MAX_COMPONENT_CHARS = 255
MAX_PATH_INVENTORY = 100_000
_COMPONENT = re.compile(r"[A-Za-z0-9_.-]+\Z")
_RESERVED = {"CON", "PRN", "AUX", "NUL"} | {
    prefix + str(i) for prefix in ("COM", "LPT") for i in range(1, 10)
}


def relative_path(value: Any) -> str:
    """Portable *logical* path, not a native-filesystem security guarantee.

    Strict ASCII POSIX components avoid Unicode, drive, ADS, short-name and
    Win32 trailing-dot/space aliases. No spelling is trimmed or normalized.
    Use validate_path_inventory before mapping a whole set to native files.
    Production still needs a fresh root, no links/reparse points, race-safe I/O
    and native length/capability checks. Historical Git paths are not renamed.
    """
    nonempty_text(value, "path")
    require(len(value) <= MAX_PATH_CHARS, "logical path budget exceeded")
    parts = value.split("/")
    for part in parts:
        require(part not in {"", ".", ".."}, "path alias or traversal")
        require(len(part) <= MAX_COMPONENT_CHARS, "path component budget exceeded")
        require(_COMPONENT.fullmatch(part) is not None, "nonportable path character")
        require(not part.endswith("."), "trailing-dot path alias")
        require(part.split(".", 1)[0].upper() not in _RESERVED, "reserved device path")
    path = PurePosixPath(value)
    require(not path.is_absolute() and path.as_posix() == value, "absolute or noncanonical path")
    return value


def validate_path_inventory(values: Iterable[str]) -> tuple[str, ...]:
    """Reject case aliases in files AND directory prefixes, and file/dir overlap.

    Input is a complete finite file inventory. It is not an authorization list
    and does not authenticate a checkout or perform filesystem writes.
    """
    files: set[str] = set()
    spellings: dict[str, str] = {}
    for ordinal, value in enumerate(values):
        require(ordinal < MAX_PATH_INVENTORY, "path inventory budget exceeded")
        path = relative_path(value)
        require(path not in files, "duplicate file path")
        files.add(path)
        parts = path.split("/")
        for end in range(1, len(parts) + 1):
            prefix = "/".join(parts[:end])
            key = prefix.casefold()
            require(key not in spellings or spellings[key] == prefix, "case-insensitive path alias")
            spellings[key] = prefix
    for path in files:
        parts = path.split("/")
        require(not any("/".join(parts[:end]) in files for end in range(1, len(parts))),
                "file path is also a directory prefix")
    return tuple(sorted(files))


def _validate(value: Any) -> None:
    pending = [(value, 0)]
    count = 0
    while pending:
        item, depth = pending.pop()
        count += 1
        require(count <= MAX_NODES and depth <= MAX_DEPTH, "JSON structural budget exceeded")
        if item is None or type(item) is bool:
            continue
        if type(item) is int:
            require(len(str(abs(item))) <= 256, "integer budget exceeded")
        elif type(item) is str:
            try:
                require(len(item.encode("utf-8", errors="strict")) <= MAX_BYTES, "text budget exceeded")
            except UnicodeError as exc:
                raise ContractError("invalid Unicode") from exc
        elif type(item) is list:
            pending.extend((v, depth + 1) for v in item)
        elif type(item) is dict:
            require(all(type(k) is str for k in item), "JSON keys must be strings")
            pending.extend((k, depth + 1) for k in item)
            pending.extend((v, depth + 1) for v in item.values())
        else:
            raise ContractError("unsupported JSON value type: " + type(item).__name__)


def canonical_bytes(value: Any) -> bytes:
    _validate(value)
    try:
        result = json.dumps(value, sort_keys=True, ensure_ascii=False,
                            separators=(",", ":"), allow_nan=False).encode("utf-8")
    except (UnicodeError, RecursionError, TypeError, ValueError) as exc:
        raise ContractError("canonical serialization failed") from exc
    require(len(result) <= MAX_BYTES, "JSON byte budget exceeded")
    return result


def load_bytes(raw: bytes) -> Any:
    require(type(raw) is bytes and len(raw) <= MAX_BYTES, "JSON bytes required within budget")
    def pairs(items):
        out = {}
        for key, value in items:
            require(key not in out, "duplicate JSON key")
            out[key] = value
        return out
    def no_float(_):
        raise ContractError("floats and nonfinite constants are forbidden")
    def integer(text):
        require(len(text.lstrip("-")) <= 256, "integer budget exceeded")
        return int(text)
    try:
        value = json.loads(raw.decode("utf-8", errors="strict"), object_pairs_hook=pairs,
                           parse_float=no_float, parse_constant=no_float, parse_int=integer)
    except (UnicodeError, json.JSONDecodeError, RecursionError) as exc:
        raise ContractError("invalid JSON") from exc
    _validate(value)
    return value


def digest(value: Any, *, domain: str) -> str:
    nonempty_text(domain, "hash domain")
    require("\0" not in domain, "hash-domain separator forbidden")
    return hashlib.sha256(domain.encode("utf-8") + b"\0" + canonical_bytes(value)).hexdigest()


# Explicit evaluator-only native evidence envelope. The finite proposal codec
# above remains at 8 MiB / 100,000 nodes. Complete multi-cohort inventories are
# larger than the kit's small message examples; no Expr serialization changes.
NATIVE_EVIDENCE_CODEC = "OPICA_NATIVE_EVIDENCE_JSON_V1"
NATIVE_MAX_BYTES = 128 * 1024 * 1024
NATIVE_MAX_NODES = 8_000_000

def _validate_native(value: Any) -> None:
    pending=[(value,0)]; count=0
    while pending:
        item,depth=pending.pop(); count+=1
        require(count<=NATIVE_MAX_NODES and depth<=MAX_DEPTH,"native evidence structural budget exceeded")
        if item is None or type(item)is bool: continue
        if type(item)is int: require(len(str(abs(item)))<=256,"native integer budget exceeded")
        elif type(item)is str:
            try: require(len(item.encode("utf-8",errors="strict"))<=NATIVE_MAX_BYTES,"native text budget exceeded")
            except UnicodeError as exc: raise ContractError("native invalid Unicode") from exc
        elif type(item)is list: pending.extend((v,depth+1) for v in item)
        elif type(item)is dict:
            require(all(type(k)is str for k in item),"native JSON key type differs")
            pending.extend((v,depth+1) for pair in item.items() for v in pair)
        else: raise ContractError("unsupported native evidence JSON value")

def native_evidence_bytes(value: Any) -> bytes:
    _validate_native(value)
    raw=json.dumps(value,sort_keys=True,ensure_ascii=False,separators=(",",":"),allow_nan=False).encode("utf-8")
    require(len(raw)<=NATIVE_MAX_BYTES,"native evidence byte budget exceeded")
    return raw

def load_native_evidence(raw: bytes) -> Any:
    require(type(raw)is bytes and len(raw)<=NATIVE_MAX_BYTES,"native evidence bytes/budget required")
    def pairs(items):
        out={}
        for k,v in items:
            require(k not in out,"duplicate native JSON key"); out[k]=v
        return out
    def no_float(_): raise ContractError("native floats/nonfinite forbidden")
    def integer(text):
        require(len(text.lstrip("-"))<=256,"native integer budget exceeded"); return int(text)
    try:
        value=json.loads(raw.decode("utf-8",errors="strict"),object_pairs_hook=pairs,
                         parse_float=no_float,parse_constant=no_float,parse_int=integer)
    except (UnicodeError,json.JSONDecodeError,RecursionError) as exc:
        raise ContractError("invalid native evidence JSON") from exc
    _validate_native(value)
    return value
