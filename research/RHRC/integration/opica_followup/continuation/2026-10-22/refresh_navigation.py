"""Generate a documentation-only module table from the exact current root ledger."""
from __future__ import annotations

import argparse
from collections import Counter, defaultdict
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[5]
COLUMNS = (
    ('PROVED_IN_ORIGINAL_41_ROOT_SOURCE_BOUND_SUBSET', 'Historical'),
    ('PROVED_NARROW_LOCAL_GATES_AGGREGATE_PENDING', 'Narrow local'),
    ('PRIOR_CANDIDATE_FAILED_OR_BLOCKED_UNACCEPTED', 'WIP'),
    ('OPEN_NO_COMPLETE_CANDIDATE', 'Absent'),
)


def render() -> str:
    source = HERE/'ROOT_LEDGER_100.json'
    payload = source.read_bytes()
    ledger = json.loads(payload)
    rows = ledger['roots']
    if len(rows) != 100 or len({row['id'] for row in rows}) != 100:
        raise ValueError('Exact 100-root ledger required')
    if ledger['current_aggregate_accepted'] is not False:
        raise ValueError('Review documentation authority before aggregate promotion')
    groups = defaultdict(list)
    for row in rows:
        if row['current_status'] not in dict(COLUMNS):
            raise ValueError('New ledger state needs explicit documentation review')
        groups[row['path']].append(row)
    lines = [
        '# OPICA module status — navigation only', '',
        'Generated from [ROOT_LEDGER_100.json](ROOT_LEDGER_100.json) and actual source presence.',
        'Ledger SHA256: `'+hashlib.sha256(payload).hexdigest()+'`.', '',
        'The original target remains 100 primary roots / 28 acceptance units. Historical',
        'and narrow local evidence remain separate; every current aggregate/full-release',
        'gate is OPEN. File presence does not establish proof or type coverage.', '',
        '| Planned module | Roots | Historical | Narrow local | WIP | Absent | Source |',
        '| --- | ---: | ---: | ---: | ---: | ---: | --- |',
    ]
    total = Counter()
    for path, roots in sorted(groups.items()):
        counts = Counter(row['current_status'] for row in roots)
        total.update(counts)
        module = Path(path).stem
        file = REPO/path
        presence = '[present](../../../../../../'+path+')' if file.is_file() else 'planned / missing'
        values = [str(counts[key]) for key, _ in COLUMNS]
        lines.append('| `'+module+'` | '+str(len(roots))+' | '+' | '.join(values)+' | '+presence+' |')
    lines += ['| **Total** | **100** | '+' | '.join('**'+str(total[key])+'**' for key, _ in COLUMNS)+' | |', '',
              'Regenerate with `python refresh_navigation.py --write`; verify with `--check`.',
              'Read the [named remaining work](REMAINING_WORK.md) and [next-agent task](NEXT_AGENT_PROMPT.md)',
              'before choosing a module. RH, Step 4 and the independent closing inequalities remain OPEN.', '']
    return '\n'.join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    expected = render().encode('utf-8')
    target = HERE/'MODULE_STATUS.md'
    if args.write:
        target.write_bytes(expected)
    elif not target.is_file() or target.read_bytes() != expected:
        raise SystemExit('Stale module navigation table; review ledger and regenerate')
    print('PASS_DOCUMENTATION_ONLY: module table '+('written' if args.write else 'current'))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
