"""Validate complete Lean type DAGs without expanding shared subexpressions.

This checks the compiler export protocol, not mathematical truth. Constant
origins, proof validity and source identity are checked by the compiler receipt.
All references are topological; closedness and reachability take linear time.
"""
from __future__ import annotations

import json
import re

FORMAT = 'LEAN_EXPR_DAG_V1'
NAT = re.compile(r'(?:0|[1-9][0-9]*)\Z')
INT = re.compile(r'(?:0|-?[1-9][0-9]*)\Z')


def _require(ok, message):
    if not ok:
        raise ValueError('invalid Lean type DAG: ' + message)


def _array(value, length=None):
    _require(isinstance(value, list) and (length is None or len(value) == length),
             'array shape')
    return value


def _text(value):
    _require(isinstance(value, str), 'string payload')


def _nat(value):
    _require(isinstance(value, str) and NAT.fullmatch(value) is not None,
             'canonical natural-number string')


def _bool(value):
    _require(type(value) is bool, 'Boolean payload')


def _name(value):
    _array(value)
    _require(bool(value), 'empty Name')
    if value[0] == 'anonymous':
        _array(value, 1)
    elif value[0] in ('str', 'num'):
        _array(value, 3)
        _name(value[1])
        (_text if value[0] == 'str' else _nat)(value[2])
    else:
        raise ValueError('invalid Lean type DAG: Name tag')


def _level(value):
    _array(value)
    _require(bool(value), 'empty Level')
    tag = value[0]
    if tag == 'zero':
        _array(value, 1)
    elif tag == 'succ':
        _array(value, 2)
        _level(value[1])
    elif tag in ('max', 'imax'):
        _array(value, 3)
        _level(value[1])
        _level(value[2])
    elif tag == 'param':
        _array(value, 2)
        _name(value[1])
    else:
        raise ValueError('invalid Lean type DAG: Level tag or unresolved metavariable')


def _substring(value):
    _array(value, 4)
    _require(value[0] == 'substring', 'Substring tag')
    _text(value[1])
    _nat(value[2])
    _nat(value[3])


def _source_info(value):
    _array(value)
    _require(bool(value), 'empty SourceInfo')
    if value[0] == 'none':
        _array(value, 1)
    elif value[0] == 'original':
        _array(value, 5)
        _substring(value[1])
        _nat(value[2])
        _substring(value[3])
        _nat(value[4])
    elif value[0] == 'synthetic':
        _array(value, 4)
        _nat(value[1])
        _nat(value[2])
        _bool(value[3])
    else:
        raise ValueError('invalid Lean type DAG: SourceInfo tag')


def _preresolved(value):
    _array(value)
    _require(bool(value), 'empty preresolved identifier')
    if value[0] == 'namespace':
        _array(value, 2)
        _name(value[1])
    elif value[0] == 'decl':
        _array(value, 3)
        _name(value[1])
        for field in _array(value[2]):
            _text(field)
    else:
        raise ValueError('invalid Lean type DAG: preresolved identifier tag')


def _syntax(value):
    _array(value)
    _require(bool(value), 'empty Syntax')
    tag = value[0]
    if tag == 'missing':
        _array(value, 1)
    elif tag == 'node':
        _array(value, 4)
        _source_info(value[1])
        _name(value[2])
        for arg in _array(value[3]):
            _syntax(arg)
    elif tag == 'atom':
        _array(value, 3)
        _source_info(value[1])
        _text(value[2])
    elif tag == 'ident':
        _array(value, 5)
        _source_info(value[1])
        _substring(value[2])
        _name(value[3])
        for item in _array(value[4]):
            _preresolved(item)
    else:
        raise ValueError('invalid Lean type DAG: Syntax tag')


def _data_value(value):
    _array(value, 2)
    tag, payload = value
    if tag == 'string':
        _text(payload)
    elif tag == 'bool':
        _bool(payload)
    elif tag == 'name':
        _name(payload)
    elif tag == 'nat':
        _nat(payload)
    elif tag == 'int':
        _require(isinstance(payload, str) and INT.fullmatch(payload) is not None,
                 'canonical integer string')
    elif tag == 'syntax':
        _syntax(payload)
    else:
        raise ValueError('invalid Lean type DAG: DataValue tag')


def _metadata(value):
    for entry in _array(value):
        _array(entry, 2)
        _name(entry[0])
        _data_value(entry[1])


def _object_pairs(pairs):
    result = {}
    for key, value in pairs:
        _require(key not in result, 'duplicate JSON key')
        result[key] = value
    return result


def validate_expression(expression):
    """Return compact metrics, rejecting malformed, open or lossy DAG payloads."""
    _require(isinstance(expression, str) and bool(expression.strip()), 'empty payload')
    try:
        data = json.loads(expression, object_pairs_hook=_object_pairs,
                          parse_constant=lambda _: (_ for _ in ()).throw(
                              ValueError('invalid Lean type DAG: nonfinite JSON value')))
    except (json.JSONDecodeError, RecursionError) as exc:
        raise ValueError('invalid Lean type DAG: malformed JSON') from exc
    _require(isinstance(data, dict) and set(data) == {'format', 'root', 'nodes'},
             'top-level fields')
    _require(data['format'] == FORMAT, 'format')
    nodes = _array(data['nodes'])
    _require(bool(nodes), 'empty node inventory')
    _nat(data['root'])
    _require(data['root'] == str(len(nodes) - 1), 'root must be the final node')
    free_ranges, edges, unique_nodes = [], [], set()

    def ref(value, current):
        _nat(value)
        _require(len(value) <= len(str(current)), 'reference out of bounds')
        number = int(value)
        _require(number < current, 'forward, cyclic or out-of-bounds reference')
        return number

    for index, node in enumerate(nodes):
        _array(node)
        _require(bool(node), 'empty expression node')
        tag, children, free = node[0], [], 0
        if tag == 'bvar':
            _array(node, 2)
            _nat(node[1])
            _require(len(node[1]) <= len(str(len(nodes))), 'unbound variable')
            free = int(node[1]) + 1
        elif tag == 'sort':
            _array(node, 2)
            _level(node[1])
        elif tag == 'const':
            _array(node, 3)
            _name(node[1])
            for level in _array(node[2]):
                _level(level)
        elif tag == 'app':
            _array(node, 3)
            children = [ref(node[1], index), ref(node[2], index)]
            free = max(free_ranges[k] for k in children)
        elif tag in ('lam', 'forall'):
            _array(node, 5)
            _name(node[1])
            _require(node[2] in ('default', 'implicit', 'strictImplicit', 'instImplicit'),
                     'BinderInfo tag')
            children = [ref(node[3], index), ref(node[4], index)]
            free = max(free_ranges[children[0]], max(0, free_ranges[children[1]] - 1))
        elif tag == 'let':
            _array(node, 6)
            _name(node[1])
            children = [ref(node[k], index) for k in (2, 3, 4)]
            _bool(node[5])
            free = max(free_ranges[children[0]], free_ranges[children[1]],
                       max(0, free_ranges[children[2]] - 1))
        elif tag == 'nat':
            _array(node, 2)
            _nat(node[1])
        elif tag == 'string':
            _array(node, 2)
            _text(node[1])
        elif tag == 'mdata':
            _array(node, 3)
            _metadata(node[1])
            children = [ref(node[2], index)]
            free = free_ranges[children[0]]
        elif tag == 'proj':
            _array(node, 4)
            _name(node[1])
            _nat(node[2])
            children = [ref(node[3], index)]
            free = free_ranges[children[0]]
        else:
            raise ValueError('invalid Lean type DAG: Expr tag or unresolved metavariable')
        key = json.dumps(node, ensure_ascii=False, separators=(',', ':'))
        _require(key not in unique_nodes, 'duplicate canonical node')
        unique_nodes.add(key)
        free_ranges.append(free)
        edges.append(children)
    _require(free_ranges[-1] == 0, 'root has loose bound variables')
    reachable, pending = set(), [len(nodes) - 1]
    while pending:
        current = pending.pop()
        if current not in reachable:
            reachable.add(current)
            pending.extend(edges[current])
    _require(len(reachable) == len(nodes), 'unreachable nodes')
    return {'format': FORMAT, 'unique_nodes': len(nodes), 'closed': True}
