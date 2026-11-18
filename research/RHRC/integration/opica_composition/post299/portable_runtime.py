"""Candidate V2 *portable* runtime fingerprint gate for OPICA4 source replay.

Never edits the frozen post-299/PR299 V1 checker. The only admissible
cross-runner difference is the Linux kernel/platform string. No source,
precision, executable, python-flint, GMP, MPFR, FLINT, evidence, worker
receipt or interval comparison is forgiven here. This is NOT yet an
approved acceptance policy; its adoption needs independent review.
"""
from __future__ import annotations

import re
from pathlib import PurePosixPath

SCHEMA = "OPICA_POST300_PORTABLE_RUNTIME_CANDIDATE_V2"
AUTHORITY = "CANDIDATE_ONLY_NOT_RELEASE_APPROVAL"
FIELDS = frozenset((
    "python_executable",
    "python_executable_sha256",
    "python_version",
    "python_optimized",
    "python_flint_version",
    "python_flint_module_sha256",
    "flint_version",
    "native_library_sha256",
    "platform",
))
HEX64 = re.compile(r"[0-9a-f]{64}\Z", re.ASCII)
LINUX_PLATFORM = re.compile(
    r"Linux-([0-9][a-zA-Z0-9._+\-]*)-x86_64-with-glibc([0-9]+\.[0-9]+)\Z",
    re.ASCII,
)


class RuntimeMismatch(ValueError):
    """Failure is an actual gate failure, never a warning-to-PASS conversion."""


def _valid_absolute_path(value: object) -> bool:
    return (type(value) is str and value.startswith("/") and
            "\x00" not in value and
            all(x not in ("", "..") for x in PurePosixPath(value).parts[1:]))


def _validate(runtime: object) -> tuple[str, str]:
    if type(runtime) is not dict or set(runtime) != FIELDS:
        raise RuntimeMismatch("Closed runtime fingerprint field inventory differs")
    if not _valid_absolute_path(runtime["python_executable"]):
        raise RuntimeMismatch("Noncanonical Python executable path")
    if type(runtime["python_optimized"]) is not bool:
        raise RuntimeMismatch("Optimized-mode fingerprint type differs")
    for key in ("python_executable_sha256", "python_flint_module_sha256"):
        if type(runtime[key]) is not str or HEX64.fullmatch(runtime[key]) is None:
            raise RuntimeMismatch("Invalid sha256 in " + key)
    for key in ("python_version", "python_flint_version", "flint_version"):
        if type(runtime[key]) is not str or not runtime[key]:
            raise RuntimeMismatch("Missing runtime version in " + key)
    native = runtime["native_library_sha256"]
    if type(native) is not dict or not native:
        raise RuntimeMismatch("Native library inventory absent")
    for path, digest in native.items():
        if (not _valid_absolute_path(path) or type(digest) is not str
                or HEX64.fullmatch(digest) is None):
            raise RuntimeMismatch("Invalid native library SHA256 inventory")
    platform = runtime["platform"]
    if type(platform) is not str:
        raise RuntimeMismatch("Platform must be a string")
    match = LINUX_PLATFORM.fullmatch(platform)
    if match is None:
        raise RuntimeMismatch("Unsupported platform or architecture")
    return match.group(1), match.group(2)


def compare_runtime(producer: object, verifier: object) -> dict:
    """Explain the mismatch without claiming a historical V1 acceptance.

    All immutable fields must match *exactly*, including paths and SHA256s;
    platform may vary only between Linux x86_64 hosts with the same glibc ABI.
    """
    _, producer_glibc = _validate(producer)
    _, verifier_glibc = _validate(verifier)
    mismatches = sorted(
        key for key in FIELDS
        if type(producer[key]) is not type(verifier[key]) or
        producer[key] != verifier[key]
    )
    mismatch_nonhost = [key for key in mismatches if key != "platform"]
    candidate_match = not mismatch_nonhost and producer_glibc == verifier_glibc
    return {
        "schema": SCHEMA,
        "authority": AUTHORITY,
        "candidate_portable_match": candidate_match,
        "different_fields": mismatches,
        "forbidden_differences": mismatch_nonhost,
        "producer_platform": producer["platform"],
        "verifier_platform": verifier["platform"],
        "producer_glibc": producer_glibc,
        "verifier_glibc": verifier_glibc,
        "allowed_platform_drift_only": candidate_match and mismatches == ["platform"],
    }


def require_compatible(producer: object, verifier: object) -> dict:
    result = compare_runtime(producer, verifier)
    if not result["candidate_portable_match"]:
        raise RuntimeMismatch(
            "Cross-runner fingerprint diverged: "
            + ",".join(result["forbidden_differences"])
            + (";glibc" if result["producer_glibc"] != result["verifier_glibc"] else "")
        )
    return result
