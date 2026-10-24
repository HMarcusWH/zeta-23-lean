from pathlib import Path
import concurrent.futures, hashlib, json, re, subprocess, time

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT / 'opica-followup-repo'
C = REPO / 'research/RHRC/integration/opica_followup/continuation/2026-10-22'
OUT = Path(__file__).resolve().parent / 'clean-workflow-consumers'
LAKE = Path('C:/Users/macka/.elan/toolchains/leanprover--lean4---v4.33.0-rc2/bin/lake.exe')
def git(*args):
    return subprocess.check_output(['git', '-C', str(REPO), *args], text=True).strip()
def sha(data):
    return hashlib.sha256(data).hexdigest()
head, tree, dirty = git('rev-parse', 'HEAD'), git('rev-parse', 'HEAD^{tree}'), git('status', '--porcelain')
assert head == '59ff485551771c0ab6322562d18fb8e9d4166da4' and not dirty
OUT.mkdir(exist_ok=False)
def run(name, expected):
    source = (C / 'evidence/current-codex/stage5/consumers' / (name + '.lean')).read_bytes()
    target = OUT / (name + '.lean')
    target.write_bytes(source)
    command = [str(LAKE), 'env', 'lean', '-DmaxHeartbeats=800000', '-DrelaxedAutoImplicit=false', str(target)]
    start = time.monotonic()
    result = subprocess.run(command, cwd=REPO, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    log = result.stdout
    (OUT / (name + '.log')).write_bytes(log)
    requested = re.findall(r'^#print axioms (\S+)\s*$', source.decode(), re.M)
    parsed = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log.decode('utf-8', errors='replace'))
    assert result.returncode == 0 and len(parsed) == len(requested) == expected
    assert set(requested) == {x[0] for x in parsed}
    assert all(set(x.strip() for x in axioms.split(',') if x.strip()) <= {'propext', 'Classical.choice', 'Quot.sound'} for _, axioms in parsed)
    assert 'sorryAx' not in log.decode('utf-8', errors='replace')
    return dict(name=name, command=command, exit_code=result.returncode, seconds=time.monotonic()-start,
                source_sha256=sha(source), log_sha256=sha(log), printed_closures=expected,
                axioms={n: [a.strip() for a in xs.split(',') if a.strip()] for n, xs in parsed})
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool:
    rows = list(pool.map(lambda pair: run(*pair), [('opica-w04-w07-expected', 52), ('opica-w06-expected', 14)]))
assert not git('status', '--porcelain') and git('rev-parse', 'HEAD') == head
receipt = dict(schema='OPICA_STAGE19_CLEAN_WORKFLOW_CONSUMERS_V1', status='PASS_NARROW_WORKFLOW_CONSUMERS_ONLY',
               checked_commit=head, checked_tree=tree, dirty_status_during_checks=dirty, source_unchanged=True,
               consumers=rows, aggregate_accepted=False, RH='OPEN', Step4='OPEN')
(OUT / 'CHECK_RESULT.json').write_text(json.dumps(receipt, indent=2)+'\n', encoding='utf-8')
print(json.dumps(receipt, indent=2))
