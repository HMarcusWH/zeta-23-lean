"""Lossless storage for the schema-0.4 registered compiler dependency rows.

The original receipt path is a small, versioned index. Sixteen fixed shards
are keyed by the first hexadecimal digit of SHA256(UTF8(declaration)). Their
strictly sorted merge is the original canonical, globally sorted JSONL stream.
Legacy monolithic receipts remain readable; an invalid index never falls back
to a different representation. This changes storage, not compiler authority.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

RHRC = Path(__file__).resolve().parents[1]
REPO = RHRC.parents[1]
ROW_SCHEMA = "RHKG-phase2b-compiler-dependencies-0.4"
INDEX_SCHEMA = "RHKG_REGISTERED_DEPENDENCY_SHARDS_V1"
INDEX_PATH = "research/RHRC/graph/compiler/REGISTERED_DECLARATION_DEPENDENCIES.jsonl"
SHARD_KEYS = "0123456789abcdef"
SHARD_DIR = "research/RHRC/graph/compiler/registered_dependencies"
SHARD_PATHS = [f"{SHARD_DIR}/REGISTERED_DECLARATION_DEPENDENCIES-{key}.jsonl" for key in SHARD_KEYS]
SHARD_MAX_BYTES = 50 * 1024 * 1024
SHARD_RULE = "SHA256_UTF8_DECLARATION_FIRST_HEX_NIBBLE"
INDEX_KEYS = {"schema", "row_schema_version", "shard_key", "declaration_count",
              "logical_bytes", "logical_sha256", "shards"}
ROW_KEYS = {"schema_version", "declaration", "module", "repository_scope", "graph_role",
            "declaration_kind", "private_or_internal", "dependencies"}


def require(ok: bool, message: str) -> None:
    if not ok:
        raise ValueError("registered_dependency_shards: " + message)


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _json(data: bytes):
    def pairs(items):
        result = {}
        for key, value in items:
            require(key not in result, "duplicate JSON key: " + key)
            result[key] = value
        return result
    def constant(value):
        raise ValueError("registered_dependency_shards: nonfinite JSON constant: " + value)
    return json.loads(data.decode("utf-8"), object_pairs_hook=pairs, parse_constant=constant)


def shard_key(declaration: str) -> str:
    return hashlib.sha256(declaration.encode("utf-8")).hexdigest()[0]


def render_row(row: dict) -> str:
    return json.dumps(row, sort_keys=True, separators=(",", ":"), ensure_ascii=False,
                      allow_nan=False) + "\n"


def _name(row: dict) -> str:
    require(isinstance(row, dict), "dependency row is not an object")
    expected = ROW_KEYS | ({"registered_claim_id"} if row.get("graph_role") == "REGISTERED_CLAIM_ROOT" else set())
    require(set(row) == expected and row.get("schema_version") == ROW_SCHEMA,
            "dependency row keys or schema differ from schema0.4")
    name = row["declaration"]
    require(isinstance(name, str) and bool(name), "invalid declaration name")
    require(isinstance(row["dependencies"], list), "dependencies is not a list")
    previous = None
    for dep in row["dependencies"]:
        require(isinstance(dep, dict) and set(dep) == {"constant", "used_in_type", "used_in_value", "used_in_structure"},
                "dependency channel fields differ")
        target = dep["constant"]
        require(isinstance(target, str) and bool(target), "invalid dependency constant")
        require(previous is None or previous < target, "dependency constants are not strictly sorted")
        previous = target
        flags = [dep[key] for key in ["used_in_type", "used_in_value", "used_in_structure"]]
        require(all(type(flag) is bool for flag in flags) and any(flags), "invalid dependency channel flags")
    return name


def _ordered(rows: list[dict]) -> list[dict]:
    names = [_name(row) for row in rows]
    require(len(names) == len(set(names)), "duplicate declaration")
    return sorted(rows, key=lambda row: row["declaration"])


def logical_digest(rows: list[dict]) -> tuple[str, int]:
    hasher = hashlib.sha256(); size = 0
    for row in _ordered(rows):
        data = render_row(row).encode("utf-8")
        hasher.update(data); size += len(data)
    return hasher.hexdigest(), size


def render_storage(rows: list[dict]) -> dict[str, bytes]:
    """Render the original path as an index and all sixteen fixed shards."""
    ordered = _ordered(rows)
    buckets = {key: bytearray() for key in SHARD_KEYS}
    counts = {key: 0 for key in SHARD_KEYS}
    logical = hashlib.sha256(); size = 0
    for row in ordered:
        data = render_row(row).encode("utf-8"); key = shard_key(row["declaration"])
        buckets[key].extend(data); counts[key] += 1
        logical.update(data); size += len(data)
    payload = {path: bytes(buckets[key]) for key, path in zip(SHARD_KEYS, SHARD_PATHS)}
    require(all(len(data) <= SHARD_MAX_BYTES for data in payload.values()), "registered shard exceeds byte cap")
    index = {"schema": INDEX_SCHEMA, "row_schema_version": ROW_SCHEMA, "shard_key": SHARD_RULE,
        "declaration_count": len(ordered), "logical_bytes": size, "logical_sha256": logical.hexdigest(),
        "shards": [{"path": path, "bytes": len(payload[path]), "declaration_count": counts[key],
                    "sha256": digest(payload[path])} for key, path in zip(SHARD_KEYS, SHARD_PATHS)]}
    return {INDEX_PATH: (json.dumps(index, sort_keys=True, indent=2, ensure_ascii=False) + "\n").encode("utf-8"),
            **payload}


def _parse_lines(data: bytes, *, key: str | None = None) -> list[dict]:
    rows = []; previous = None
    for line in data.splitlines(keepends=True):
        if key is None and not line.strip():
            continue
        row = _json(line); name = _name(row)
        require(previous is None or previous < name, "receipt is not strictly declaration-sorted")
        previous = name
        if key is not None:
            require(shard_key(name) == key, "declaration is in the wrong shard: " + name)
            require(line == render_row(row).encode("utf-8"), "shard row is not canonical UTF8 JSONL")
        rows.append(row)
    return rows


def _index(data: bytes) -> dict | None:
    # Legacy dispatch is allowed only for an actual schema0.4 declaration row.
    # Broken/unknown index objects are never reinterpreted as legacy receipts.
    first = None; position = 0
    while position < len(data):
        end = data.find(b"\n", position)
        if end < 0:
            end = len(data)
        line = data[position:end]; position = end + 1
        if line.strip():
            first = line
            break
    if first is None:
        return None
    try:
        value = _json(first)
    except (ValueError, UnicodeError):
        value = None
    if isinstance(value, dict) and "declaration" in value:
        _name(value)
        return None
    index = _json(data)
    require(isinstance(index, dict) and set(index) == INDEX_KEYS, "invalid shard index keys")
    require(index["schema"] == INDEX_SCHEMA and index["row_schema_version"] == ROW_SCHEMA
            and index["shard_key"] == SHARD_RULE, "unknown shard index version or layout")
    require(type(index["declaration_count"]) is int and index["declaration_count"] >= 0
            and type(index["logical_bytes"]) is int and index["logical_bytes"] >= 0,
            "invalid logical counts")
    require(_sha(index["logical_sha256"]), "invalid logical SHA256")
    require(isinstance(index["shards"], list) and len(index["shards"]) == 16, "exactly sixteen shards required")
    for expected, row in zip(SHARD_PATHS, index["shards"]):
        require(isinstance(row, dict) and set(row) == {"path", "bytes", "declaration_count", "sha256"}
                and row["path"] == expected, "index shard paths or order differ")
        require(type(row["bytes"]) is int and 0 <= row["bytes"] <= SHARD_MAX_BYTES
                and type(row["declaration_count"]) is int and row["declaration_count"] >= 0
                and _sha(row["sha256"]), "invalid shard metadata")
    return index


def _sha(value) -> bool:
    return isinstance(value, str) and len(value) == 64 and all(c in "0123456789abcdef" for c in value)


def load_from_reader(read_bytes) -> list[dict]:
    """Read actual bytes (filesystem or immutable Git) through one strict API."""
    data = read_bytes(INDEX_PATH); index = _index(data)
    if index is None:
        return _parse_lines(data)
    rows = []
    for key, meta in zip(SHARD_KEYS, index["shards"]):
        shard = read_bytes(meta["path"])
        require(len(shard) == meta["bytes"] and digest(shard) == meta["sha256"],
                "shard SHA256 or byte count differs: " + meta["path"])
        current = _parse_lines(shard, key=key)
        require(len(current) == meta["declaration_count"], "shard declaration count differs: " + meta["path"])
        rows.extend(current)
    rows = _ordered(rows)
    checksum, size = logical_digest(rows)
    require(len(rows) == index["declaration_count"] and size == index["logical_bytes"]
            and checksum == index["logical_sha256"], "logical canonical receipt digest or counts differ")
    return rows


def _regular(repo: Path, relative: str) -> Path:
    path = repo / relative
    for ancestor in [path, *path.parents]:
        if ancestor == repo:
            break
        require(not ancestor.is_symlink() and not getattr(ancestor, "is_junction", lambda: False)(),
                "linked receipt file or directory: " + relative)
    require(path.is_file() and path.resolve().is_relative_to(repo.resolve()), "missing or escaped receipt: " + relative)
    return path


def shard_file_errors(repo: Path = REPO) -> list[str]:
    """Check the exact physical shard set when indexed storage is present."""
    repo = Path(repo).resolve(); directory = repo / SHARD_DIR
    if not directory.exists():
        return []  # Historical monolithic checkouts have no shard directory.
    present = {p.relative_to(repo).as_posix() for p in directory.rglob("*") if p.is_file() or p.is_symlink()}
    expected = set(SHARD_PATHS)
    errors = []
    if present != expected:
        errors.append(f"registered shard set drift: missing={sorted(expected - present)}, extra={sorted(present - expected)}")
    for path in SHARD_PATHS:
        try:
            full = _regular(repo, path)
            if full.stat().st_size > SHARD_MAX_BYTES:
                errors.append("registered shard exceeds byte cap: " + path)
        except ValueError as exc:
            errors.append(str(exc))
    return errors


def load_rows(repo: Path = REPO) -> list[dict]:
    repo = Path(repo).resolve()
    data = _regular(repo, INDEX_PATH).read_bytes(); index = _index(data)
    if index is None:
        require(not (repo / SHARD_DIR).exists(), "legacy receipt has unexpected shard directory")
    else:
        require((repo / SHARD_DIR).is_dir(), "indexed receipt has no shard directory")
        errors = shard_file_errors(repo)
        require(not errors, "; ".join(errors))
    return load_from_reader(lambda path: data if path == INDEX_PATH else _regular(repo, path).read_bytes())


def logical_sha256(repo: Path = REPO) -> str:
    return logical_digest(load_rows(repo))[0]


def check_storage(rendered: dict[str, bytes], repo: Path = REPO) -> None:
    """Check exact canonical indexed bytes against a fresh compiler rendering."""
    repo = Path(repo).resolve()
    require(set(rendered) == {INDEX_PATH, *SHARD_PATHS}, "incorrect rendered storage inventory")
    errors = shard_file_errors(repo)
    require(not errors, "; ".join(errors))
    for path, expected in rendered.items():
        require(_regular(repo, path).read_bytes() == expected, "stale or missing compiler receipt: " + path)


def write_rows(rows: list[dict], repo: Path = REPO) -> dict[str, bytes]:
    """Write all fixed shards, then publish their index; never delete old paths."""
    repo = Path(repo).resolve(); rendered = render_storage(rows)
    directory = repo / SHARD_DIR
    if directory.exists():
        extra = {p.relative_to(repo).as_posix() for p in directory.rglob("*") if p.is_file() or p.is_symlink()} - set(SHARD_PATHS)
        require(not extra, "unexpected existing registered shard files: " + str(sorted(extra)))
    for path in [*SHARD_PATHS, INDEX_PATH]:
        target = repo / path
        for ancestor in [target, *target.parents]:
            if ancestor == repo:
                break
            require(not ancestor.is_symlink() and not getattr(ancestor, "is_junction", lambda: False)(),
                    "linked receipt destination: " + path)
    for path in [*SHARD_PATHS, INDEX_PATH]:
        target = repo / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(rendered[path])
    return rendered
