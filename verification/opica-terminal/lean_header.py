"""Conservative Lean module-header reader for the source preflight.

Only the header is scanned, following Lean.Parser.Module's grammar:
[module] [prelude] ([public] [meta] import [all] ident)*.
The actual Lean compiler remains authoritative. No declaration body, quoted
example, or prose is interpreted as an import. Rewrites use identifier spans.
"""
from dataclasses import dataclass
import re

_IDENT = re.compile(r"[^\W\d][\w'!?]*", re.UNICODE)

@dataclass(frozen=True)
class Import:
    name: str
    start: int
    end: int
    line: int

def _error(source, text, pos, message):
    line = text.count("\n", 0, pos) + 1
    raise RuntimeError(f"{source}:{line}: {message}")

def _trivia(text, pos, source):
    n = len(text)
    while pos < n:
        if text[pos].isspace() or (pos == 0 and text[pos] == "\ufeff"):
            pos += 1
        elif text.startswith("--", pos):
            end = text.find("\n", pos)
            pos = n if end == -1 else end + 1
        elif text.startswith("/-", pos):
            start = pos
            pos += 2
            depth = 1
            while pos < n and depth:
                if text.startswith("/-", pos):
                    depth += 1
                    pos += 2
                elif text.startswith("-/", pos):
                    depth -= 1
                    pos += 2
                else:
                    pos += 1
            if depth:
                _error(source, text, start, "unterminated header comment")
        else:
            break
    return pos

def _component(text, pos, source):
    if text.startswith("«", pos):
        end = text.find("»", pos + 1)
        if end < 0:
            _error(source, text, pos, "unterminated quoted identifier")
        part = text[pos+1:end]
        if not part or any(c in part for c in "./\\\x00\r\n«»"):
            _error(source, text, pos, "unsupported quoted module path component")
        return part, end + 1
    match = _IDENT.match(text, pos)
    return (match.group(), match.end()) if match else (None, pos)

def _name(text, pos, source):
    pos = _trivia(text, pos, source)
    start = pos
    part, pos = _component(text, pos, source)
    if part is None:
        return None, start, start
    parts = [part]
    while pos < len(text) and text[pos] == ".":
        part, end = _component(text, pos + 1, source)
        if part is None:
            _error(source, text, pos, "malformed qualified module name")
        parts.append(part)
        pos = end
    return ".".join(parts), start, pos

def _keyword(text, pos, keyword, source):
    name, start, end = _name(text, pos, source)
    # Quoted identifiers are not keywords.
    return end if name == keyword and text[start:end] == keyword else None

def imports(text, source="<source>"):
    pos = _trivia(text, 0, source)
    module = _keyword(text, pos, "module", source)
    if module is not None:
        pos = module
    prelude = _keyword(text, pos, "prelude", source)
    if prelude is not None:
        pos = prelude
    result = []
    while True:
        start = _trivia(text, pos, source)
        cursor = start
        pub = _keyword(text, cursor, "public", source)
        if pub is not None:
            cursor = pub
        meta = _keyword(text, cursor, "meta", source)
        if meta is not None:
            cursor = meta
        directive = _keyword(text, cursor, "import", source)
        if directive is None:
            return result
        all_ = _keyword(text, directive, "all", source)
        if module is None and any(k is not None for k in (pub, meta, all_)):
            _error(source, text, start, "qualified import requires module header")
        if pub is not None and all_ is not None:
            _error(source, text, start, "public import all is invalid")
        name, a, b = _name(text, directive if all_ is None else all_, source)
        if not name or name in {"module", "prelude", "public", "meta", "import", "all", "section"}:
            _error(source, text, start, "missing or invalid import name")
        result.append(Import(name, a, b, text.count("\n", 0, a) + 1))
        pos = b

def rewrite_imports(text, old, new, source="<source>"):
    edits = [(i.start, i.end, new+i.name[len(old):])
             for i in imports(text, source) if i.name.startswith(old)]
    for start, end, replacement in reversed(edits):
        text = text[:start] + replacement + text[end:]
    return text
