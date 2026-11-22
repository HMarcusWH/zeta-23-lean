"""Two exact reviewed host tuples; runtime registration grants no proof authority."""
from __future__ import annotations
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import re
from types import MappingProxyType

from ..opica_composition.canonical import require
from ..opica_composition.snapshot import unlinked

REGISTRY = Path(__file__).with_name('RUNTIME_PROFILES.json')
REGISTRY_SHA256 = 'c57e878a343d943f943020b90573bfda953d525c5b3459cc869b96dca21516ae'
LEGACY_ID = 'NATIVE_4330RC2_RETAINED_V1'
COMMON_ID = 'STEP4_COMMON_4331_PROPOSED_V1'
LEGACY_LEAN_PIN = 'leanprover/lean4:v4.33.0-rc2'


@dataclass(frozen=True)
class RuntimeProfile:
    identity: str
    lean_pin: str
    compiler_version: str
    compiler_commit: str
    manifest_sha256: str
    package_revisions: object
    package_urls: object
    benchmark_blob: str

    @property
    def mathlib_commit(self):
        return self.package_revisions['mathlib']

    def check_compiler(self, text):
        match = re.fullmatch(r'Lean \(version ([^,\s]+), ([A-Za-z0-9_.-]+), commit ([0-9a-f]{40}), Release\)', text) if type(text) is str else None
        require(match is not None and match.group(1) == self.compiler_version and
                match.group(3) == self.compiler_commit,
                'Actual host compiler does not match the selected exact runtime profile')

    def record(self):
        return {'profile_id': self.identity, 'lean_pin': self.lean_pin,
                'compiler_commit': self.compiler_commit,
                'manifest_sha256': self.manifest_sha256,
                'authority': 'RUNTIME_IDENTITY_ONLY_NO_PROOF_ACCEPTANCE'}


def registry(raw=None):
    raw = unlinked(REGISTRY).read_bytes() if raw is None else raw
    require(type(raw) is bytes and hashlib.sha256(raw).hexdigest() == REGISTRY_SHA256,
            'Reviewed runtime registry bytes changed')
    value = json.loads(raw)
    require(set(value) == {'schema', 'authority', 'profiles'} and
            value['schema'] == 'OPICAS4_EXACT_RUNTIME_PROFILES_V1' and
            value['authority'] == 'REGISTRATION_ONLY_NO_PROOF_ACCEPTANCE' and
            list(value['profiles']) == [LEGACY_ID, COMMON_ID], 'Runtime profile inventory differs')
    return value


def select_profile(lean_raw, manifest_raw):
    """Match exact source bytes and every package tuple; never accept version ranges."""
    require(type(lean_raw) is bytes and type(manifest_raw) is bytes,
            'Exact runtime source bytes required')
    value = registry()
    matches = [(identity, row) for identity, row in value['profiles'].items()
               if lean_raw == row['lean_toolchain'].encode('utf-8') and
               hashlib.sha256(manifest_raw).hexdigest() == row['manifest_sha256']]
    require(len(matches) == 1, 'Unknown or mixed Lean/manifest tuple')
    identity, row = matches[0]
    manifest = json.loads(manifest_raw)
    packages = manifest['packages']
    require(manifest['packagesDir'] == '.lake/packages' and
            len(packages) == len(row['packages']) == 9 and
            len({p['name'] for p in packages}) == 9 and
            all(p['type'] == 'git' for p in packages), 'Exact nine Git package inventory required')
    actual = {p['name']: {'rev': p['rev'], 'url': p['url']} for p in packages}
    require(actual == row['packages'], 'Reviewed package tuple differs')
    return RuntimeProfile(identity, row['lean_toolchain'].strip(),
                          row['compiler_version'], row['compiler_commit'], row['manifest_sha256'],
                          MappingProxyType({name: p['rev'] for name, p in actual.items()}),
                          MappingProxyType({name: p['url'] for name, p in actual.items()}),
                          row['benchmark_blob'])


def runtime_for(repo):
    repo = unlinked(repo).resolve()
    return select_profile(unlinked(repo / 'lean-toolchain').read_bytes(),
                          unlinked(repo / 'lake-manifest.json').read_bytes())
