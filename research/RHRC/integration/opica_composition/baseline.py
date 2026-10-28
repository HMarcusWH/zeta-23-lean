"""Frozen parent replay in a separate checkout, never by mutating live source."""
from __future__ import annotations
import hashlib
from pathlib import Path
import subprocess
import tempfile
from .canonical import require, digest
from .descendant import BASE, BASE_TREE, git
from .snapshot import unlinked, file_hash

BASELINES = {
    "ROUND3": (BASE, BASE_TREE),
    "ROUND2": ("775692f2e72d76b6a97cf66926a86cc96342c109", "acd548eb97ddaee68eb6c9df73f82756ee10d13f"),
}

def select_replay_scope(label: str, *, requested_child: str, requested_tree: str) -> dict:
    require(label in BASELINES, "unknown frozen parent")
    commit, tree = BASELINES[label]
    return {"scope": "FROZEN_BASELINE", "baseline": label, "checked_commit": commit,
            "checked_tree": tree, "requested_child": requested_child, "requested_child_tree": requested_tree,
            "current_child_compiler_accepted": False}

def replay_parent(repo: Path, output: Path, label="ROUND3", *, timeout=1800) -> dict:
    require(label in BASELINES, "unknown frozen baseline")
    repo = Path(repo).resolve(); output = unlinked(output).absolute()
    require(not output.exists() and not output.is_relative_to(repo), "fresh external parent checkout required")
    commit, tree = BASELINES[label]
    output.mkdir(parents=True)
    # The disposable checkout is not an evidence artifact: it contains .git and
    # all historical source. Only immutable pins, command logs and dispositions
    # belong in the downloadable lane bundle.
    temporary = tempfile.TemporaryDirectory(prefix='opica4-parent-')
    checkout = unlinked(Path(temporary.name)/"checkout").resolve()
    require(not checkout.is_relative_to(repo) and not checkout.is_relative_to(output),
            "parent clone must stay outside live source and evidence inventory")
    # A local shared clone has its own HEAD/index/working tree; no shared proof outputs.
    command = ["git", "clone", "--shared", "--no-checkout", str(repo), str(checkout)]
    p = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=timeout)
    (output/"clone.log").write_bytes(p.stdout); require(p.returncode == 0, "parent checkout creation failed")
    p = subprocess.run(["git", "checkout", "--detach", commit], cwd=checkout,
                       stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=timeout)
    (output/"checkout.log").write_bytes(p.stdout); require(p.returncode == 0, "parent checkout failed")
    require(git(checkout,"rev-parse","HEAD") == commit and git(checkout,"rev-parse","HEAD^{tree}") == tree,
            "wrong parent checkout")
    recipe = ["python", "-B", "research/RHRC/integration/opica_round3/validate_contract.py"] if label=="ROUND3" else ["python", "-B", "research/RHRC/integration/opica_round2/validate_contract.py"]
    import sys
    recipe[0] = sys.executable
    p = subprocess.run(recipe, cwd=checkout, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=timeout)
    (output/"parent-contract.log").write_bytes(p.stdout)
    require(p.returncode == 0, "unchanged historical source predicate failed")
    require(not git(checkout,"status","--porcelain"), "parent source changed during replay")
    temporary.cleanup()
    return {"schema":"OPICA4_FROZEN_PARENT_REPLAY_V1", "scope":"FROZEN_BASELINE",
            "checked_commit":commit,"checked_tree":tree,"predicate":recipe,
            "exit_code":p.returncode,"log_sha256":file_hash(output/"parent-contract.log"),
            "current_child_compiler_accepted":False,"compiler_accepted":False,
            "status":"PASS_HISTORICAL_SOURCE_CONTRACT_ONLY"}

def compare_parent_contracts(repo: Path, paths: list[str]) -> dict:
    for path in paths:
        old = subprocess.check_output(["git","-C",str(repo),"show",BASE+":"+path])
        require_unchanged(old,(Path(repo)/path).read_bytes(),path)
    return {"status":"UNCHANGED_PARENT_PREDICATES","count":len(paths)}

def require_unchanged(expected:bytes,actual:bytes,path:str)->None:
    require(type(expected)is bytes and type(actual)is bytes and actual==expected,
            'frozen parent predicate/authority changed: '+path)
