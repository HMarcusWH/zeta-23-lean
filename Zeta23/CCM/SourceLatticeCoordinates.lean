import Zeta23.CCM.FiniteDictionary
import Zeta23.CCM.ConstrainedParityGeometry

noncomputable section

namespace Zeta23.CCM

open Matrix Finset
open scoped BigOperators ComplexConjugate

/-!
# POST284-M04/M17: integer-lattice coordinates for centered source vectors

Centered coefficient vectors `Fin (2N+1) → ℂ` are identified with functions
`ℤ → ℂ` supported in the integer box `[-N, N]`.  In these coordinates the
elementary source matrix at the half aperture `ω = 1/2` is the diagonal sign
`(-1)^n`, and centered zero-extension `K ≤ K'` preserves every centered moment
and the complete elementary source form at every source coordinate.

Everything here is elementary finite linear algebra about `sourceMatrix`.  No
statement concerns the canonical `Pole - Arch - Prime` operator, a contact
eigenvector, or RH.
-/

/-! ## Integer boxes and centered sums -/

/-- Integer box `[-N, N]` of centered Fourier indices. -/
def latticeBox (N : ℕ) : Finset ℤ :=
  Finset.Icc (-(N : ℤ)) N

@[simp] theorem mem_latticeBox {N : ℕ} {n : ℤ} :
    n ∈ latticeBox N ↔ -(N : ℤ) ≤ n ∧ n ≤ N :=
  Finset.mem_Icc

theorem latticeBox_mono {N N' : ℕ} (h : N ≤ N') :
    latticeBox N ⊆ latticeBox N' := by
  intro n hn
  rw [mem_latticeBox] at hn ⊢
  omega

theorem centeredIndex_mem_latticeBox (N : ℕ) (i : Fin (2 * N + 1)) :
    centeredIndex N i ∈ latticeBox N := by
  have hi := i.2
  rw [mem_latticeBox]
  unfold centeredIndex
  omega

/-- Centered `Fin` sums are integer box sums. -/
theorem sum_centeredIndex_eq_sum_latticeBox
    {M : Type*} [AddCommMonoid M] (N : ℕ) (g : ℤ → M) :
    ∑ i : Fin (2 * N + 1), g (centeredIndex N i) =
      ∑ n ∈ latticeBox N, g n := by
  refine Finset.sum_bij (fun i _ => centeredIndex N i)
    (fun i _ => centeredIndex_mem_latticeBox N i)
    (fun i _ j _ h => centeredIndex_injective N h) ?_ (fun _ _ => rfl)
  intro n hn
  rw [mem_latticeBox] at hn
  refine ⟨⟨(n + N).toNat, by omega⟩, Finset.mem_univ _, ?_⟩
  unfold centeredIndex
  simp only
  omega

/-- A box sum may be enlarged to any larger box when the summand vanishes
outside the smaller one. -/
theorem sum_latticeBox_eq_of_vanish
    {M : Type*} [AddCommMonoid M] {N N' : ℕ} (hNN : N ≤ N') (g : ℤ → M)
    (hg : ∀ n, n ∉ latticeBox N → g n = 0) :
    ∑ n ∈ latticeBox N', g n = ∑ n ∈ latticeBox N, g n := by
  symm
  exact Finset.sum_subset (latticeBox_mono hNN) (fun n _ hn => hg n hn)

/-! ## Lattice functions -/

/-- Support of a lattice function inside the box `[-N, N]`. -/
def LatticeSupported (N : ℕ) (f : ℤ → ℂ) : Prop :=
  ∀ n, n ∉ latticeBox N → f n = 0

theorem LatticeSupported.mono {N N' : ℕ} {f : ℤ → ℂ}
    (hf : LatticeSupported N f) (h : N ≤ N') :
    LatticeSupported N' f := by
  intro n hn
  apply hf n
  intro hmem
  exact hn (latticeBox_mono h hmem)

theorem LatticeSupported.add {N : ℕ} {f g : ℤ → ℂ}
    (hf : LatticeSupported N f) (hg : LatticeSupported N g) :
    LatticeSupported N (f + g) := by
  intro n hn
  simp [hf n hn, hg n hn]

theorem LatticeSupported.smul {N : ℕ} {f : ℤ → ℂ}
    (hf : LatticeSupported N f) (c : ℂ) :
    LatticeSupported N (c • f) := by
  intro n hn
  simp [hf n hn]

theorem LatticeSupported.zero (N : ℕ) : LatticeSupported N (0 : ℤ → ℂ) := by
  intro n _
  rfl

/-- Lattice view of a centered vector; zero outside the centered box. -/
def toLattice (N : ℕ) (u : Fin (2 * N + 1) → ℂ) : ℤ → ℂ :=
  fun n =>
    if h : -(N : ℤ) ≤ n ∧ n ≤ N then u ⟨(n + N).toNat, by omega⟩ else 0

/-- Restriction of a lattice function to the centered box. -/
def ofLattice (N : ℕ) (f : ℤ → ℂ) : Fin (2 * N + 1) → ℂ :=
  fun i => f (centeredIndex N i)

@[simp] theorem ofLattice_apply (N : ℕ) (f : ℤ → ℂ) (i : Fin (2 * N + 1)) :
    ofLattice N f i = f (centeredIndex N i) := rfl

theorem ofLattice_add (N : ℕ) (f g : ℤ → ℂ) :
    ofLattice N (f + g) = ofLattice N f + ofLattice N g := rfl

theorem ofLattice_smul (N : ℕ) (c : ℂ) (f : ℤ → ℂ) :
    ofLattice N (c • f) = c • ofLattice N f := rfl

/-- Restriction to the centered box as a complex-linear map. -/
def ofLatticeLinearMap (N : ℕ) : (ℤ → ℂ) →ₗ[ℂ] (Fin (2 * N + 1) → ℂ) where
  toFun := ofLattice N
  map_add' := ofLattice_add N
  map_smul' := ofLattice_smul N

@[simp] theorem ofLatticeLinearMap_apply (N : ℕ) (f : ℤ → ℂ) :
    ofLatticeLinearMap N f = ofLattice N f := rfl

theorem toLattice_centeredIndex (N : ℕ) (u : Fin (2 * N + 1) → ℂ)
    (i : Fin (2 * N + 1)) :
    toLattice N u (centeredIndex N i) = u i := by
  have hi := i.2
  have hmem : -(N : ℤ) ≤ centeredIndex N i ∧ centeredIndex N i ≤ N := by
    unfold centeredIndex
    omega
  rw [toLattice, dif_pos hmem]
  congr 1
  apply Fin.ext
  unfold centeredIndex
  simp only
  omega

@[simp] theorem ofLattice_toLattice (N : ℕ) (u : Fin (2 * N + 1) → ℂ) :
    ofLattice N (toLattice N u) = u := by
  funext i
  exact toLattice_centeredIndex N u i

theorem toLattice_supported (N : ℕ) (u : Fin (2 * N + 1) → ℂ) :
    LatticeSupported N (toLattice N u) := by
  intro n hn
  rw [mem_latticeBox] at hn
  rw [toLattice, dif_neg hn]

theorem toLattice_ofLattice {N : ℕ} {f : ℤ → ℂ}
    (hf : LatticeSupported N f) :
    toLattice N (ofLattice N f) = f := by
  funext n
  by_cases hn : -(N : ℤ) ≤ n ∧ n ≤ N
  · rw [toLattice, dif_pos hn, ofLattice_apply]
    congr 1
    unfold centeredIndex
    simp only
    omega
  · rw [toLattice, dif_neg hn, hf n (by rwa [mem_latticeBox])]

/-- Restriction is injective on box-supported lattice functions. -/
theorem eq_zero_of_ofLattice_eq_zero {N : ℕ} {f : ℤ → ℂ}
    (hf : LatticeSupported N f) (h : ofLattice N f = 0) : f = 0 := by
  rw [← toLattice_ofLattice hf, h]
  funext n
  by_cases hn : -(N : ℤ) ≤ n ∧ n ≤ N
  · rw [toLattice, dif_pos hn]
    rfl
  · rw [toLattice, dif_neg hn]
    rfl

/-! ## Moments, reversal and the elementary source form -/

theorem centeredMoment_ofLattice (N k : ℕ) (f : ℤ → ℂ) :
    centeredMoment N k (ofLattice N f) =
      ∑ n ∈ latticeBox N, (n : ℂ) ^ k * f n := by
  unfold centeredMoment
  exact sum_centeredIndex_eq_sum_latticeBox N (fun n => (n : ℂ) ^ k * f n)

theorem reverseCoefficients_ofLattice (N : ℕ) (f : ℤ → ℂ) :
    reverseCoefficients N (ofLattice N f) = ofLattice N (fun n => f (-n)) := by
  funext i
  simp [reverseCoefficients, ofLattice]

/-- Sesquilinear elementary source form, in the repository orientation
`∑ conj(u_i) S_ij v_j`. -/
def sourceSesq (ω : ℝ) (N : ℕ) (u v : Fin (2 * N + 1) → ℂ) : ℂ :=
  ∑ i, ∑ j, conj (u i) * sourceMatrix ω N i j * v j

theorem sourceSesq_self (ω : ℝ) (N : ℕ) (u : Fin (2 * N + 1) → ℂ) :
    sourceSesq ω N u u = quadraticForm (sourceMatrix ω N) u := rfl

theorem sourceSesq_add_left (ω : ℝ) (N : ℕ) (u u' v : Fin (2 * N + 1) → ℂ) :
    sourceSesq ω N (u + u') v = sourceSesq ω N u v + sourceSesq ω N u' v := by
  unfold sourceSesq
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Pi.add_apply, map_add]
  ring

theorem sourceSesq_add_right (ω : ℝ) (N : ℕ) (u v v' : Fin (2 * N + 1) → ℂ) :
    sourceSesq ω N u (v + v') = sourceSesq ω N u v + sourceSesq ω N u v' := by
  unfold sourceSesq
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Pi.add_apply]
  ring

theorem sourceSesq_ofLattice (ω : ℝ) (N : ℕ) (f g : ℤ → ℂ) :
    sourceSesq ω N (ofLattice N f) (ofLattice N g) =
      ∑ n ∈ latticeBox N, ∑ m ∈ latticeBox N,
        conj (f n) * sourceEntry ω n m * g m := by
  have hinner : ∀ n : ℤ,
      ∑ j : Fin (2 * N + 1),
          conj (f n) * sourceEntry ω n (centeredIndex N j) * g (centeredIndex N j) =
        ∑ m ∈ latticeBox N, conj (f n) * sourceEntry ω n m * g m :=
    fun n => sum_centeredIndex_eq_sum_latticeBox N
      (fun m => conj (f n) * sourceEntry ω n m * g m)
  simp only [sourceSesq, ofLattice_apply, sourceMatrix_apply, hinner]
  exact sum_centeredIndex_eq_sum_latticeBox N
    (fun n => ∑ m ∈ latticeBox N, conj (f n) * sourceEntry ω n m * g m)

/-! ## The half aperture -/

/-- The lattice sign `(-1)^n`. -/
def latticeSign (n : ℤ) : ℂ :=
  if Even n then 1 else -1

theorem latticeSign_of_even {n : ℤ} (h : Even n) : latticeSign n = 1 := by
  simp [latticeSign, h]

theorem latticeSign_of_odd {n : ℤ} (h : Odd n) : latticeSign n = -1 := by
  simp [latticeSign, Int.not_even_iff_odd.mpr h]

theorem latticeSign_add_one (n : ℤ) : latticeSign (n + 1) = -latticeSign n := by
  rcases Int.even_or_odd n with h | h
  · rw [latticeSign_of_even h, latticeSign_of_odd h.add_one]
  · rw [latticeSign_of_odd h, latticeSign_of_even h.add_one, neg_neg]

theorem latticeSign_sub_one (n : ℤ) : latticeSign (n - 1) = -latticeSign n := by
  have h := latticeSign_add_one (n - 1)
  rw [sub_add_cancel] at h
  rw [h, neg_neg]

theorem latticeSign_add_two (n : ℤ) : latticeSign (n + 2) = latticeSign n := by
  rw [show n + 2 = n + 1 + 1 by ring, latticeSign_add_one, latticeSign_add_one, neg_neg]

theorem latticeSign_sub_two (n : ℤ) : latticeSign (n - 2) = latticeSign n := by
  rw [show n - 2 = n - 1 - 1 by ring, latticeSign_sub_one, latticeSign_sub_one, neg_neg]

/-- At `ω = 1/2` the elementary source potential vanishes on the lattice. -/
theorem sourcePotential_half (n : ℤ) : sourcePotential (1 / 2) n = 0 := by
  unfold sourcePotential
  rw [show 2 * Real.pi * (n : ℝ) * (1 / 2) = (n : ℝ) * Real.pi by ring,
    Real.sin_int_mul_pi]
  simp

/-- At `ω = 1/2` the elementary source diagonal is the lattice sign. -/
theorem sourceDiagonal_half (n : ℤ) : sourceDiagonal (1 / 2) n = latticeSign n := by
  unfold sourceDiagonal
  rw [show 2 * Real.pi * (n : ℝ) * (1 / 2) = (n : ℝ) * Real.pi by ring,
    Real.cos_int_mul_pi]
  rcases Int.even_or_odd n with h | h
  · rw [latticeSign_of_even h, h.neg_one_zpow]
    norm_num
  · rw [latticeSign_of_odd h, h.neg_one_zpow]
    norm_num

/-- The elementary source matrix at `ω = 1/2` is `Diag((-1)^n)`. -/
theorem sourceEntry_half (n m : ℤ) :
    sourceEntry (1 / 2) n m = if n = m then latticeSign n else 0 := by
  by_cases h : n = m
  · subst h
    simp [sourceDiagonal_half]
  · rw [sourceEntry_of_ne _ h, sourcePotential_half, sourcePotential_half, if_neg h]
    simp

/-- Lattice form of the half-aperture source form. -/
theorem sourceSesq_half_ofLattice (N : ℕ) (f g : ℤ → ℂ) :
    sourceSesq (1 / 2) N (ofLattice N f) (ofLattice N g) =
      ∑ n ∈ latticeBox N, latticeSign n * (conj (f n) * g n) := by
  rw [sourceSesq_ofLattice]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [sourceEntry_half, mul_ite, ite_mul, mul_zero, zero_mul]
  rw [Finset.sum_ite_eq, if_pos hn]
  ring

/-- Coordinate form of the half-aperture source form. -/
theorem sourceSesq_half (N : ℕ) (u v : Fin (2 * N + 1) → ℂ) :
    sourceSesq (1 / 2) N u v =
      ∑ i, latticeSign (centeredIndex N i) * (conj (u i) * v i) := by
  rw [← ofLattice_toLattice N u, ← ofLattice_toLattice N v,
    sourceSesq_half_ofLattice]
  rw [← sum_centeredIndex_eq_sum_latticeBox]
  apply Finset.sum_congr rfl
  intro i _
  rw [toLattice_centeredIndex, toLattice_centeredIndex]

/-- The half-aperture source energy is the signed coefficient mass. -/
theorem quadraticForm_sourceMatrix_half (N : ℕ) (u : Fin (2 * N + 1) → ℂ) :
    quadraticForm (sourceMatrix (1 / 2) N) u =
      ∑ i, latticeSign (centeredIndex N i) * (conj (u i) * u i) := by
  rw [← sourceSesq_self, sourceSesq_half]

/-! ## Centered zero extension -/

/-- Centered zero extension from `[-K, K]` to `[-K', K']`. -/
def centeredZeroExtend (K K' : ℕ) (u : Fin (2 * K + 1) → ℂ) :
    Fin (2 * K' + 1) → ℂ :=
  ofLattice K' (toLattice K u)

theorem centeredMoment_centeredZeroExtend {K K' : ℕ} (h : K ≤ K')
    (k : ℕ) (u : Fin (2 * K + 1) → ℂ) :
    centeredMoment K' k (centeredZeroExtend K K' u) = centeredMoment K k u := by
  rw [centeredZeroExtend, centeredMoment_ofLattice]
  conv_rhs => rw [← ofLattice_toLattice K u, centeredMoment_ofLattice]
  apply sum_latticeBox_eq_of_vanish h
  intro n hn
  rw [toLattice_supported K u n hn, mul_zero]

/-- Centered zero extension preserves the complete elementary source form at
every source coordinate. -/
theorem sourceSesq_centeredZeroExtend {K K' : ℕ} (h : K ≤ K') (ω : ℝ)
    (u v : Fin (2 * K + 1) → ℂ) :
    sourceSesq ω K' (centeredZeroExtend K K' u) (centeredZeroExtend K K' v) =
      sourceSesq ω K u v := by
  unfold centeredZeroExtend
  rw [sourceSesq_ofLattice]
  conv_rhs => rw [← ofLattice_toLattice K u, ← ofLattice_toLattice K v,
    sourceSesq_ofLattice]
  rw [sum_latticeBox_eq_of_vanish h]
  · apply Finset.sum_congr rfl
    intro n _
    apply sum_latticeBox_eq_of_vanish h
    intro m hm
    rw [toLattice_supported K v m hm, mul_zero]
  · intro n hn
    rw [toLattice_supported K u n hn]
    simp

theorem quadraticForm_centeredZeroExtend {K K' : ℕ} (h : K ≤ K') (ω : ℝ)
    (u : Fin (2 * K + 1) → ℂ) :
    quadraticForm (sourceMatrix ω K') (centeredZeroExtend K K' u) =
      quadraticForm (sourceMatrix ω K) u := by
  rw [← sourceSesq_self, ← sourceSesq_self, sourceSesq_centeredZeroExtend h]

theorem toLattice_reverseCoefficients (K : ℕ) (u : Fin (2 * K + 1) → ℂ) :
    toLattice K (reverseCoefficients K u) = fun n => toLattice K u (-n) := by
  have hsupp : LatticeSupported K (fun n => toLattice K u (-n)) := by
    intro n hn
    apply toLattice_supported K u
    rw [mem_latticeBox] at hn ⊢
    omega
  conv_lhs => rw [← ofLattice_toLattice K u, reverseCoefficients_ofLattice]
  exact toLattice_ofLattice hsupp

theorem reverseCoefficients_centeredZeroExtend (K K' : ℕ)
    (u : Fin (2 * K + 1) → ℂ) :
    reverseCoefficients K' (centeredZeroExtend K K' u) =
      centeredZeroExtend K K' (reverseCoefficients K u) := by
  rw [centeredZeroExtend, centeredZeroExtend, reverseCoefficients_ofLattice,
    toLattice_reverseCoefficients]

theorem centeredZeroExtend_mem_evenCoefficientSubspace (K K' : ℕ)
    {u : Fin (2 * K + 1) → ℂ} (hu : u ∈ evenCoefficientSubspace K) :
    centeredZeroExtend K K' u ∈ evenCoefficientSubspace K' := by
  rw [mem_evenCoefficientSubspace_iff] at hu ⊢
  rw [reverseCoefficients_centeredZeroExtend, hu]

theorem centeredZeroExtend_mem_oddCoefficientSubspace (K K' : ℕ)
    {u : Fin (2 * K + 1) → ℂ} (hu : u ∈ oddCoefficientSubspace K) :
    centeredZeroExtend K K' u ∈ oddCoefficientSubspace K' := by
  rw [mem_oddCoefficientSubspace_iff] at hu ⊢
  rw [reverseCoefficients_centeredZeroExtend, hu]
  funext i
  simp [centeredZeroExtend, ofLattice, toLattice]
  split_ifs <;> simp

theorem centeredZeroExtend_mem_boundaryFlatSubspace {K K' : ℕ} (h : K ≤ K')
    {u : Fin (2 * K + 1) → ℂ} (hu : u ∈ boundaryFlatSubspace K) :
    centeredZeroExtend K K' u ∈ boundaryFlatSubspace K' := by
  rw [mem_boundaryFlatSubspace_iff] at hu ⊢
  obtain ⟨h0, h1, h2⟩ := hu
  exact ⟨by rw [centeredMoment_centeredZeroExtend h, h0],
    by rw [centeredMoment_centeredZeroExtend h, h1],
    by rw [centeredMoment_centeredZeroExtend h, h2]⟩

theorem centeredZeroExtend_mem_evenBoundaryFlatSubspace {K K' : ℕ} (h : K ≤ K')
    {u : Fin (2 * K + 1) → ℂ} (hu : u ∈ evenBoundaryFlatSubspace K) :
    centeredZeroExtend K K' u ∈ evenBoundaryFlatSubspace K' :=
  ⟨centeredZeroExtend_mem_boundaryFlatSubspace h hu.1,
    centeredZeroExtend_mem_evenCoefficientSubspace K K' hu.2⟩

theorem centeredZeroExtend_mem_oddBoundaryFlatSubspace {K K' : ℕ} (h : K ≤ K')
    {u : Fin (2 * K + 1) → ℂ} (hu : u ∈ oddBoundaryFlatSubspace K) :
    centeredZeroExtend K K' u ∈ oddBoundaryFlatSubspace K' :=
  ⟨centeredZeroExtend_mem_boundaryFlatSubspace h hu.1,
    centeredZeroExtend_mem_oddCoefficientSubspace K K' hu.2⟩

end Zeta23.CCM

#print axioms Zeta23.CCM.sum_centeredIndex_eq_sum_latticeBox
#print axioms Zeta23.CCM.sourceEntry_half
#print axioms Zeta23.CCM.quadraticForm_sourceMatrix_half
#print axioms Zeta23.CCM.sourceSesq_centeredZeroExtend
#print axioms Zeta23.CCM.centeredMoment_centeredZeroExtend
#print axioms Zeta23.CCM.centeredZeroExtend_mem_evenBoundaryFlatSubspace
#print axioms Zeta23.CCM.centeredZeroExtend_mem_oddBoundaryFlatSubspace
