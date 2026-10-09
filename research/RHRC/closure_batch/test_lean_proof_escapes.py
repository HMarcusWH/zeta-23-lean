from pathlib import Path
import tempfile
import unittest

from check_lean_proof_escapes import FORBIDDEN, check, closure_roots
from lean_imports import strip_lean_comments


EXPECTED = {
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
    Path("Zeta23/CCM/CanonicalCompressedSeamJets.lean"),
    Path("Zeta23/CCM/CanonicalFrozenApertureC2.lean"),
    Path("Zeta23/CCM/CanonicalCompressedApertureC2.lean"),
    Path("Zeta23/CCM/ProductionWeightedTestCalculus.lean"),
    Path("Zeta23/CCM/ProductionWeightedGlobalTests.lean"),
    Path("Zeta23/CCM/ProductionNormalSourceAuthority.lean"),
    Path("Zeta23/CCM/FirstCrossingProductionRemainderAuthority.lean"),
    Path("Zeta23/CCM/ProductionPhysicalFunctionalCongruence.lean"),
    Path("Zeta23/CCM/FirstCrossingProductionRemainderValueAuthority.lean"),
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
    Path("Zeta23/Spectral/CanonicalCharacteristic.lean"),
    Path("Zeta23/Spectral/CanonicalOperator.lean"),
    Path("Zeta23/Spectral/CharacteristicCompactBounds.lean"),
    Path("Zeta23/Spectral/CharacteristicNormalization.lean"),
    Path("Zeta23/Spectral/CharacteristicXiIdentification.lean"),
    Path("Zeta23/Spectral/RealZeroLimitTransfer.lean"),
}


class LeanProofEscapeScopeTests(unittest.TestCase):
    def test_current_closure_validation_surface(self):
        roots = closure_roots()
        self.assertEqual(len(roots), len(set(roots)))
        self.assertEqual(set(roots), EXPECTED)
        self.assertEqual(len(roots), 82)
        for path in roots:
            self.assertTrue(path.is_file(), str(path))



class LeanProofEscapeBehaviorTests(unittest.TestCase):
    def test_rejects_escape_tokens_in_realistic_positions(self):
        cases = {
            "inline sorry": "theorem bogus : True := by sorry",
            "indented sorry": "theorem bogus : True := by\n  sorry",
            "inline admit": "example : True := by admit",
            "indented axiom": "  axiom bogus : True",
            "newline-separated": "theorem bogus : True := by\n    admit",
        }
        for label, source in cases.items():
            with self.subTest(label=label):
                self.assertIsNotNone(FORBIDDEN.search(strip_lean_comments(source)))

    def test_ignores_comments_and_longer_identifiers(self):
        source = (
            "-- sorry admit axiom\n"
            "/- axiom outside /- sorry nested -/ admit outside -/\n"
            "def sorryAx := True\n"
            "def axiomatic := True\n"
            "def admitted := True\n"
        )
        self.assertIsNone(FORBIDDEN.search(strip_lean_comments(source)))

    def test_mutated_lean_file_must_fail_audit(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = Path(tmpdir) / "ProofEscapeMutation.lean"
            path.write_text("theorem injected : True := by\n  sorry\n", encoding="utf-8")
            with self.assertRaises(SystemExit) as raised:
                check([path])
            self.assertIn("CLOSURE PROOF-ESCAPE CHECK: FAIL", str(raised.exception))


if __name__ == "__main__":
    unittest.main()
