"""Seal the completed source-pinned native31-control replay, excluding objects."""
from pathlib import Path
import hashlib
import json
import zipfile

HERE = Path(__file__).resolve().parent
RESULT = HERE.parent / 'opica-stage22/clean-controls'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
receipt = json.loads((RESULT / 'CHECK_RESULT.json').read_bytes())
if not (receipt['status'] == 'PASS_CONTROLS_ONLY' and receipt['source_unchanged'] and
        receipt['shared_build_cache_unchanged'] and len(receipt['controls']) == 31 and
        all(row['passed'] for row in receipt['controls'])):
    raise ValueError('complete source/cache-preserved31-control replay required')
sources = [HERE / name for name in ['prepare.py', 'run_controls.py', 'test_runner.py', 'seal.py',
           'CONTROL_PLAN.json', 'planned-source-manifest.json', 'README.md',
           'REPORT_MATH_SKIM_2026-10-24.md', 'PARSER_TEST_RECEIPT.json',
           'parser-tests.normal.log', 'parser-tests.optimized.log']]
sources += sorted((HERE / 'sources').glob('*.lean'))
evidence = sorted(p for p in RESULT.iterdir() if p.is_file())
entries = [('proposal/' + p.relative_to(HERE).as_posix(), p) for p in sources]
entries += [('native-replay/' + p.relative_to(RESULT).as_posix(), p) for p in evidence]
entries += [('native-replay/sources/' + p.name, p) for p in sorted((RESULT / 'sources').glob('*.lean'))]
archive = HERE / 'OPICA_STAGE22_31_CONTROL_REPLAY_2026-10-24.zip'
if archive.exists():
    raise ValueError('immutable fresh seal required')
manifest = {name: {'sha256': sha(path), 'bytes': path.stat().st_size} for name, path in entries}
data = (json.dumps(manifest, indent=2) + '\n').encode()
(HERE / 'SEALED_FILE_MANIFEST.json').write_bytes(data)
with zipfile.ZipFile(archive, 'x', compression=zipfile.ZIP_DEFLATED) as bundle:
    for name, path in entries:
        bundle.write(path, name)
    bundle.writestr('SEALED_FILE_MANIFEST.json', data)
delivery = {'status': 'PASS_CONTROLS_ONLY', 'checked_commit': receipt['checked_commit'],
            'checked_tree': receipt['checked_tree'], 'source_count': 31, 'negative': 27,
            'positive': 4, 'positive_standard_axiom_closures': 8,
            'source_unchanged': True, 'shared_build_cache_unchanged': True,
            'archive': str(archive), 'archive_sha256': sha(archive),
            'receipt': str(RESULT / 'CHECK_RESULT.json'), 'receipt_sha256': sha(RESULT / 'CHECK_RESULT.json'),
            'runner': str(HERE / 'run_controls.py'), 'runner_sha256': sha(HERE / 'run_controls.py'),
            'new_primary_roots': 0, 'aggregate_accepted': False, 'independent_review': 'NOT_ESTABLISHED',
            'RH': 'OPEN', 'Step4': 'OPEN'}
(HERE / 'DELIVERY.json').write_text(json.dumps(delivery, indent=2) + '\n', encoding='utf-8')
print(json.dumps(delivery))
