import Zeta23.CCM.ParityZeroPlateau
import Zeta23.CCM.GoodSectorKernelAnnihilation

noncomputable section

namespace Zeta23.CCM

open Complex Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# Post-#278 parity kernel tower

A zero plateau is stronger than a list of zero Rayleigh values.  Exact centered
zero extension preserves the legal parity carrier and the canonical quadratic
energy.  Since every plateau successor sector is good, zero self-energy is
upgraded by `GoodSectorKernelAnnihilation` to an actual operator kernel
identity.

Thus one attained zero mode at the minimal plateau size extends to an exact
finite kernel tower through every larger plateau size.
-/

/-- Centered zero extension between successor parity carriers. -/
def parityPlateauExtend
    (p : ReversalParity)
    {n m : ℕ} (hnm : n ≤ m)
    (v : euclideanParityBoundaryFlatSubspace p (n + 1)) :
    euclideanParityBoundaryFlatSubspace p (m + 1) :=
  ⟨euclideanCenteredZeroExtend (Nat.succ_le_succ hnm)
      (v : EuclideanSpace ℂ (Fin (2 * (n + 1) + 1))),
    euclideanCenteredZeroExtend_mem_euclideanParityBoundaryFlatSubspace
      p (Nat.succ_le_succ hnm) v.property⟩

/-- Exact finite kernel-tower package carried by a parity zero plateau. -/
structure ParityKernelTower extends ParityZeroPlateau where
  seed : euclideanParityBoundaryFlatSubspace p (n + 1)
  seed_ne : seed ≠ 0
  seed_kernel :
    parityCompressedCanonical p Lstar (n + 1) seed = 0
  extended_kernel :
    ∀ m : ℕ, ∀ hnm : n ≤ m, ∀ _hmN : m ≤ N,
      parityCompressedCanonical p Lstar (m + 1)
        (parityPlateauExtend p hnm seed) = 0

/-- The minimal zero mode of a parity plateau extends to a genuine kernel mode
at every larger size in the plateau. -/
theorem ParityZeroPlateau.exists_kernelTower
    (z : ParityZeroPlateau) :
    ∃ t : ParityKernelTower,
      t.toParityZeroPlateau = z := by
  obtain ⟨v, hvne, hveig⟩ :=
    exists_eigenmode_at_parityRayleighBottom_succ
      z.p z.Lstar z.n z.one_le_n
  have hvkernel :
      parityCompressedCanonical z.p z.Lstar (z.n + 1) v = 0 := by
    rw [hveig, z.minimal_zero]
    simp

  have hext :
      ∀ m : ℕ, ∀ hnm : z.n ≤ m, ∀ hmN : m ≤ z.N,
        parityCompressedCanonical z.p z.Lstar (m + 1)
          (parityPlateauExtend z.p hnm v) = 0 := by
    intro m hnm hmN
    have hm1 : 1 ≤ m := le_trans z.one_le_n hnm
    have hmzero :
        paritySuccessorGround z.p m z.Lstar = 0 :=
      z.plateau_zero m hnm hmN
    have hgood : ¬ ParityBad z.p z.Lstar (m + 1) := by
      intro hbad
      have hneg := parityRayleighBottom_neg_of_parityBad hbad
      change paritySuccessorGround z.p m z.Lstar < 0 at hneg
      rw [hmzero] at hneg
      exact (lt_irrefl 0) hneg
    let w : euclideanParityBoundaryFlatSubspace z.p (m + 1) :=
      parityPlateauExtend z.p hnm v
    have henergy :
        Complex.re
          (inner ℂ
            (parityCompressedCanonical z.p z.Lstar (m + 1) w)
            w) = 0 := by
      have htransport :=
        re_inner_canonicalSourceMatrix_euclideanCenteredZeroExtend
          (lt_trans z.Lsmall_pos z.Lsmall_lt_Lstar)
          (Nat.succ_le_succ hnm)
          (v : EuclideanSpace ℂ (Fin (2 * (z.n + 1) + 1)))
      calc
        Complex.re
            (inner ℂ
              (parityCompressedCanonical z.p z.Lstar (m + 1) w)
              w)
            =
          Complex.re
            (inner ℂ
              ((canonicalSourceMatrix z.Lstar (m + 1)).toEuclideanLin
                (w : EuclideanSpace ℂ (Fin (2 * (m + 1) + 1))))
              (w : EuclideanSpace ℂ (Fin (2 * (m + 1) + 1)))) := by
                exact
                  re_inner_parityCompressedCanonical_self
                    z.p z.Lstar (m + 1) w
        _ =
          Complex.re
            (inner ℂ
              ((canonicalSourceMatrix z.Lstar (z.n + 1)).toEuclideanLin
                (v : EuclideanSpace ℂ (Fin (2 * (z.n + 1) + 1))))
              (v : EuclideanSpace ℂ (Fin (2 * (z.n + 1) + 1)))) := by
                simpa [w, parityPlateauExtend] using htransport
        _ =
          Complex.re
            (inner ℂ
              (parityCompressedCanonical z.p z.Lstar (z.n + 1) v)
              v) := by
                symm
                exact
                  re_inner_parityCompressedCanonical_self
                    z.p z.Lstar (z.n + 1) v
        _ = 0 := by
          rw [hvkernel]
          simp
    exact
      parityCompressedCanonical_eq_zero_of_not_parityBad_of_selfEnergy_eq_zero
        hgood w henergy

  let t : ParityKernelTower := {
    toParityZeroPlateau := z
    seed := v
    seed_ne := hvne
    seed_kernel := hvkernel
    extended_kernel := hext
  }
  exact ⟨t, rfl⟩

end Zeta23.CCM

#print axioms Zeta23.CCM.ParityZeroPlateau.exists_kernelTower
