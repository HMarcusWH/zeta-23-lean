from __future__ import annotations

import argparse
from pathlib import Path
import re
import sys

RHRC = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(RHRC / "tools"))

from lean_imports import strip_lean_comments


CLOSURE_ROOTS = [
    Path("Zeta23/CCM/SourceContraction.lean"),
    Path("Zeta23/CCM/SourceContractionLocalized.lean"),
    Path("Zeta23/CCM/CanonicalArchUpperBound.lean"),
    Path("Zeta23/CCM/DictionaryArchFiniteDensity.lean"),
    Path("Zeta23/CCM/CanonicalArchDensityClosure.lean"),
    Path("Zeta23/CCM/CanonicalPoleUniformBound.lean"),
    Path("Zeta23/CCM/CanonicalPoleSourceBound.lean"),
    Path("Zeta23/CCM/CanonicalSmallApertureCoercivity.lean"),
    Path("Zeta23/CCM/CanonicalSmallApertureGroundSpectrum.lean"),
    Path("Zeta23/CCM/CanonicalPrimeSeamTaylor.lean"),
    Path("Zeta23/CCM/ParityGroundPerturbation.lean"),
    Path("Zeta23/CCM/ParityRayleighPerturbation.lean"),
    Path("Zeta23/CCM/CanonicalSeamGroundTransfer.lean"),
    Path("Zeta23/CCM/GroundComparisonPrinciple.lean"),
    Path("Zeta23/CCM/CanonicalGroundPropagation.lean"),
    Path("Zeta23/CCM/CanonicalAllAperturePositivity.lean"),
    Path("Zeta23/CCM/CanonicalSchurCertificate.lean"),
    Path("Zeta23/CCM/CanonicalModeTailBound.lean"),
    Path("Zeta23/CCM/CanonicalUniformDomination.lean"),
    Path("Zeta23/CCM/CanonicalFullSpaceSourceBridge.lean"),
    Path("Zeta23/ExceptionalZero/QuantitativeDetectorFamily.lean"),
    Path("Zeta23/ExceptionalZero/QuantitativeCanonicalWitness.lean"),
    Path("Zeta23/ExceptionalZero/GlobalParityBottomSignOpposition.lean"),
    Path("Zeta23/CCM/CanonicalGroundContinuity.lean"),
    Path("Zeta23/CCM/GlobalParityBottomFirstContact.lean"),
    Path("Zeta23/CCM/GlobalParityBottomContactNormalForm.lean"),
    Path("Zeta23/ExceptionalZero/GlobalParityBottomFirstContact.lean"),
    Path("Zeta23/CCM/ParityFirstNegativeBoundary.lean"),
    Path("Zeta23/CCM/ParityZeroPlateau.lean"),
    Path("Zeta23/CCM/ParityKernelTower.lean"),
    Path("Zeta23/CCM/CanonicalParityFirstCrossingShell.lean"),
    Path("Zeta23/CCM/FirstCrossingContactRegime.lean"),
    Path("Zeta23/CCM/FirstCrossingContactEquations.lean"),
    Path("Zeta23/CCM/FirstCrossingSuccessorDeterminant.lean"),
    Path("Zeta23/CCM/FirstCrossingSchurReduction.lean"),
    Path("Zeta23/CCM/FirstCrossingSourceDynamics.lean"),
    Path("Zeta23/CCM/FirstCrossingBranchBridge.lean"),
    Path("Zeta23/CCM/FirstCrossingLiftedFeatures.lean"),
    Path("Zeta23/CCM/FirstCrossingStructuralCompatibility.lean"),
    Path("Zeta23/CCM/FirstCrossingArithmeticCompatibility.lean"),
    Path("Zeta23/CCM/FirstCrossingSourceCertificate.lean"),
    Path("Zeta23/CCM/FirstCrossingSourceQuotient.lean"),
    Path("Zeta23/CCM/FirstCrossingStrictEvenSourceEnergy.lean"),
    Path("Zeta23/CCM/FirstCrossingOptimizedCurvatureAlgebra.lean"),
    Path("Zeta23/CCM/FirstCrossingProductionArithmetic.lean"),
    Path("Zeta23/CCM/FirstCrossingProductionSaturation.lean"),
    Path("Zeta23/CCM/GlobalParityFirstNegativeBoundary.lean"),
    Path("Zeta23/CCM/FirstCrossingGlobalAlignment.lean"),
    Path("Zeta23/CCM/CanonicalCompressedApertureC2.lean"),
    Path("Zeta23/CCM/ProductionWeightedTestCalculus.lean"),
    Path("Zeta23/CCM/StationarySchurContact.lean"),
    Path("Zeta23/CCM/FirstCrossingInheritedStationarity.lean"),
    Path("Zeta23/RHRC/ContactCalculusContract.lean"),
    Path("Zeta23/CCM/FirstCrossingProductionTests.lean"),
    Path("Zeta23/CCM/FirstCrossingProductionRemainder.lean"),
    Path("Zeta23/CCM/FirstCrossingProductionFirstVariation.lean"),
    Path("Zeta23/CCM/FirstCrossingProductionResponse.lean"),
    Path("Zeta23/CCM/FirstCrossingProductionCurvatureBridge.lean"),
    Path("Zeta23/CCM/FirstCrossingGeneratedStrictEvenFrontier.lean"),
    Path("Zeta23/ExceptionalZero/GlobalParityFirstNegativeBoundary.lean"),
    Path("Zeta23/CCM/CanonicalApertureLocation.lean"),
    Path("Zeta23/CCM/CanonicalInteriorFirstCrossingBarrier.lean"),
    Path("Zeta23/CCM/CanonicalSeamFirstCrossingBarrier.lean"),
    Path("Zeta23/CCM/CanonicalFirstCrossingBarrier.lean"),
    Path("Zeta23/ExceptionalZero/CanonicalParityFirstCrossingShell.lean"),
    Path("Zeta23/ExceptionalZero/CanonicalFirstCrossingConditionalRH.lean"),
    Path("Zeta23/RHRC/ClosureObligationBindings.lean"),
    Path("Zeta23/RHRC/ClosureStrengthAudit.lean"),
    Path("Zeta23/Spectral.lean"),
]

FORBIDDEN = re.compile(r"(?m)(^|\\W)(axiom|sorry|admit)(?=\\W|$)")


def closure_roots() -> list[Path]:
    roots = list(CLOSURE_ROOTS)
    roots.extend(sorted(Path("Zeta23/Spectral").rglob("*.lean")))
    return roots


def promoted_roots() -> list[Path]:
    roots: list[Path] = []
    for root in (Path("Zeta23/CCM"), Path("Zeta23/ExceptionalZero"), Path("Zeta23/Spectral")):
        roots.extend(sorted(root.rglob("*.lean")))
    for root_file in (Path("Zeta23/CCM.lean"), Path("Zeta23/ExceptionalZero.lean"), Path("Zeta23/Spectral.lean")):
        if root_file.is_file():
            roots.append(root_file)
    return roots


def check(paths: list[Path]) -> None:
    missing = [str(path) for path in paths if not path.is_file()]
    if missing:
        raise SystemExit("CLOSURE PROOF-ESCAPE CHECK: FAIL\nmissing files:\n" + "\n".join(missing))

    bad: list[str] = []
    for path in paths:
        text = strip_lean_comments(path.read_text(encoding="utf-8"))
        match = FORBIDDEN.search(text)
        if match:
            bad.append(f"{path}: {match.group(2)}")

    if bad:
        raise SystemExit("CLOSURE PROOF-ESCAPE CHECK: FAIL\n" + "\n".join(bad))

    print(f"CLOSURE PROOF-ESCAPE CHECK: PASS ({len(paths)} files)")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--scope", choices=("closure", "promoted"), default="closure")
    args = parser.parse_args()
    roots = closure_roots() if args.scope == "closure" else promoted_roots()
    check(roots)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
