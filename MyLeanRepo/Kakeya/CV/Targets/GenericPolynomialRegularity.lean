import MyLeanRepo.Kakeya.CV.Statements
import MyLeanRepo.Kakeya.CV.GenericPolynomialRegularity.DimensionLemmas
import MyLeanRepo.Kakeya.CV.GenericPolynomialRegularity.SquareFactor
import MyLeanRepo.Kakeya.CV.GenericPolynomialRegularity.MeasureZeroImage
import MyLeanRepo.Kakeya.CV.GenericPolynomialRegularity.SmoothMultiplication
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.OuterMeasure.AE

/-!
# Almost-everywhere regularity in coefficient space

Shows that the zero polynomial and repeated-factor locus have Lebesgue measure
zero in every positive-radius coefficient ball.

## Proof strategy

For `k ≤ 1`: every nonzero polynomial of total degree `≤ 1` is squarefree.
The zero polynomial locus is `{0}`, which has measure zero.

For `k ≥ 2`: the non-squarefree locus is contained in a finite union of images
of factorization maps `(q, r) ↦ q² * r` from lower-dimensional coefficient
spaces. Each image has measure zero by the Hausdorff dimension argument:
a `C¹` map from a lower-dimensional space has a range of Hausdorff dimension
strictly less than the ambient dimension, hence zero Lebesgue measure.
-/

noncomputable section

open MeasureTheory MvPolynomial

namespace Kakeya.CV

/-! ### Auxiliary lemmas -/

/-- If `p ≠ 0`, `p = q² * r`, `p.totalDegree ≤ k`, and `0 < q.totalDegree`,
then `r.totalDegree ≤ k - 2 * q.totalDegree`. -/
lemma cofactor_degree_le {p q r : MvPolynomial (Fin 3) ℝ} {k : ℕ}
    (hp : p ≠ 0) (hr_eq : p = q^2 * r) (hdeg : p.totalDegree ≤ k)
    (hq_pos : 0 < q.totalDegree) :
    r.totalDegree ≤ k - 2 * q.totalDegree := by
  have hq : q ≠ 0 := by
    by_contra h
    rw [h] at hr_eq
    simp at hr_eq
    exact hp hr_eq
  by_cases hr : r = 0
  · simp [hr] <;> omega
  · have hq2 : q^2 ≠ 0 := pow_ne_zero 2 hq
    have hdeg_mul : (q^2 * r).totalDegree = (q^2).totalDegree + r.totalDegree :=
      totalDegree_mul_of_isDomain hq2 hr
    have hdeg_q2 : (q^2).totalDegree = 2 * q.totalDegree := by
      have h : (q^2).totalDegree = (q * q).totalDegree := by ring_nf
      rw [h]
      have h2 := totalDegree_mul_of_isDomain hq hq
      linarith
    have h_eq : p.totalDegree = 2 * q.totalDegree + r.totalDegree := by
      rw [hr_eq, hdeg_mul, hdeg_q2]
    have h_le : 2 * q.totalDegree + r.totalDegree ≤ k := by
      rw [← h_eq]; exact hdeg
    omega

/-- `P.dim` equals the finrank of `degreeLESubmodule k`. -/
lemma param_dim_eq_finrank {k : ℕ} (P : PolynomialParameterization k) :
    P.dim = Module.finrank ℝ (degreeLESubmodule k) := by
  have h1 : Module.finrank ℝ (CoefficientSpace P.dim) = P.dim := by
    simp [CoefficientSpace, Module.finrank_pi] <;> rfl
  have h2 : Module.finrank ℝ (CoefficientSpace P.dim) =
      Module.finrank ℝ (degreeLESubmodule k) :=
    P.equiv.finrank_eq
  exact h1.symm.trans h2

/-- Degree bound for q * q * r variant. -/
lemma mul_square_degree_bound {k d : ℕ} (h2d : 2 * d ≤ k)
    {q r : MvPolynomial (Fin 3) ℝ} (hq : q.totalDegree ≤ d)
    (hr : r.totalDegree ≤ k - 2 * d) :
    (q * q * r).totalDegree ≤ k := by
  have h_eq : q * q * r = q^2 * r := by ring
  rw [h_eq]
  exact square_mul_degree_bound h2d hq hr

/-! ### Factorization image null -/

/-- The image of the factorization map `(q, r) ↦ q² * r` has measure zero
in coefficient space, proved via smoothness + Hausdorff dimension. -/
lemma factorization_image_null {k d : ℕ} {P : PolynomialParameterization k}
    (hk : 2 ≤ k) (hd : 1 ≤ d) (h2d : 2 * d ≤ k) :
    volume (Set.range (fun (z : (degreeLESubmodule d) × (degreeLESubmodule (k - 2 * d))) =>
      let q : MvPolynomial (Fin 3) ℝ := z.1.val
      let r : MvPolynomial (Fin 3) ℝ := z.2.val
      P.equiv.symm ⟨q ^ 2 * r, square_mul_degree_bound h2d z.1.prop z.2.prop⟩)) = 0 := by
  let E_d := EuclideanSpace ℝ (Fin (Module.finrank ℝ (degreeLESubmodule d)))
  let E_r := EuclideanSpace ℝ (Fin (Module.finrank ℝ (degreeLESubmodule (k - 2 * d))))

  -- The factorization map on Euclidean coefficient spaces
  let f : E_d × E_r → CoefficientSpace P.dim := fun p =>
    P.equiv.symm ⟨
      (degreeLEEquiv d p.1 : MvPolynomial (Fin 3) ℝ) *
      (degreeLEEquiv d p.1 : MvPolynomial (Fin 3) ℝ) *
      (degreeLEEquiv (k - 2 * d) p.2 : MvPolynomial (Fin 3) ℝ),
      mul_square_degree_bound h2d (degreeLEEquiv d p.1).prop
        (degreeLEEquiv (k - 2 * d) p.2).prop⟩

  -- f is smooth by factorizationMap_smooth
  have hf : ContDiff ℝ 1 f :=
    (factorizationMap_smooth h2d (degreeLEEquiv d) (degreeLEEquiv (k - 2 * d)) P.equiv).of_le le_top

  -- Range equality: range f = range of original submodule-based map
  have h_range : Set.range f = Set.range (fun (z : (degreeLESubmodule d) × (degreeLESubmodule (k - 2 * d))) =>
      let q : MvPolynomial (Fin 3) ℝ := z.1.val
      let r : MvPolynomial (Fin 3) ℝ := z.2.val
      P.equiv.symm ⟨q ^ 2 * r, square_mul_degree_bound h2d z.1.prop z.2.prop⟩) := by
    ext w
    simp only [Set.mem_range, f, Function.comp_apply]
    constructor
    · rintro ⟨p, rfl⟩
      let q : degreeLESubmodule d := degreeLEEquiv d p.1
      let r : degreeLESubmodule (k - 2 * d) := degreeLEEquiv (k - 2 * d) p.2
      have h_eq : (q.val * q.val * r.val) = (q.val ^ 2 * r.val) := by ring
      have h_sub : (⟨q.val * q.val * r.val, mul_square_degree_bound h2d q.prop r.prop⟩ : degreeLESubmodule k) =
          (⟨q.val ^ 2 * r.val, square_mul_degree_bound h2d q.prop r.prop⟩ : degreeLESubmodule k) := by
        apply Subtype.ext
        exact h_eq
      have h_main : P.equiv.symm ⟨q.val * q.val * r.val, mul_square_degree_bound h2d q.prop r.prop⟩ =
          P.equiv.symm ⟨q.val ^ 2 * r.val, square_mul_degree_bound h2d q.prop r.prop⟩ := by
        rw [h_sub]
      exact ⟨(q, r), h_main.symm⟩
    · rintro ⟨z, rfl⟩
      let q := z.1
      let r := z.2
      let x : E_d := (degreeLEEquiv d).symm q
      let y : E_r := (degreeLEEquiv (k - 2 * d)).symm r
      have h1 : degreeLEEquiv d x = q := (degreeLEEquiv d).apply_symm_apply q
      have h2 : degreeLEEquiv (k - 2 * d) y = r := (degreeLEEquiv (k - 2 * d)).apply_symm_apply r
      have h_eq : (q.val * q.val * r.val) = (q.val ^ 2 * r.val) := by ring
      have h_sub : (⟨q.val * q.val * r.val, mul_square_degree_bound h2d q.prop r.prop⟩ : degreeLESubmodule k) =
          (⟨q.val ^ 2 * r.val, square_mul_degree_bound h2d q.prop r.prop⟩ : degreeLESubmodule k) := by
        apply Subtype.ext
        exact h_eq
      have h_main : f (x, y) = P.equiv.symm ⟨q.val ^ 2 * r.val, square_mul_degree_bound h2d q.prop r.prop⟩ := by
        simp only [f, h1, h2]
        rw [h_sub]
      exact ⟨(x, y), h_main⟩

  -- Dimension inequality
  have h_dim : Module.finrank ℝ (E_d × E_r) < Module.finrank ℝ (CoefficientSpace P.dim) := by
    have h_eq_d : degreeLESubmodule d = MvPolynomial.restrictTotalDegree (Fin 3) ℝ d := by
      ext p; simp [degreeLESubmodule, MvPolynomial.mem_restrictTotalDegree]
    have h_eq_k2d : degreeLESubmodule (k - 2 * d) = MvPolynomial.restrictTotalDegree (Fin 3) ℝ (k - 2 * d) := by
      ext p; simp [degreeLESubmodule, MvPolynomial.mem_restrictTotalDegree]
    letI : Module.Finite ℝ (degreeLESubmodule d) := by
      exact h_eq_d ▸ inferInstanceAs (Module.Finite ℝ (MvPolynomial.restrictTotalDegree (Fin 3) ℝ d))
    letI : Module.Finite ℝ (degreeLESubmodule (k - 2 * d)) := by
      exact h_eq_k2d ▸ inferInstanceAs (Module.Finite ℝ (MvPolynomial.restrictTotalDegree (Fin 3) ℝ (k - 2 * d)))
    letI : Module.Free ℝ (degreeLESubmodule d) := by
      exact h_eq_d ▸ inferInstanceAs (Module.Free ℝ (MvPolynomial.restrictTotalDegree (Fin 3) ℝ d))
    letI : Module.Free ℝ (degreeLESubmodule (k - 2 * d)) := by
      exact h_eq_k2d ▸ inferInstanceAs (Module.Free ℝ (MvPolynomial.restrictTotalDegree (Fin 3) ℝ (k - 2 * d)))
    have h1 : Module.finrank ℝ (E_d × E_r) =
        Module.finrank ℝ (degreeLESubmodule d) + Module.finrank ℝ (degreeLESubmodule (k - 2 * d)) := by
      rw [Module.finrank_prod]
      <;> simp [E_d, E_r, finrank_euclideanSpace_fin]
      <;> rfl
    have h2 : Module.finrank ℝ (CoefficientSpace P.dim) =
        Module.finrank ℝ (degreeLESubmodule k) := by
      exact P.equiv.finrank_eq
    have h4 := finrank_product_ineq k d hk hd h2d
    have h5 : Module.finrank ℝ (degreeLESubmodule d × degreeLESubmodule (k - 2 * d)) =
        Module.finrank ℝ (degreeLESubmodule d) + Module.finrank ℝ (degreeLESubmodule (k - 2 * d)) :=
      Module.finrank_prod
    rw [h5] at h4
    rw [h1, h2]
    exact h4

  rw [← h_range]
  exact measure_zero_range_of_finrank_lt hf h_dim

/-! ### Main proof -/

theorem generic_polynomial_regularity :
    GenericPolynomialRegularityStatement := by
  dsimp only [GenericPolynomialRegularityStatement]
  intro k P x ε hε

  let bad : Set (CoefficientSpace P.dim) :=
    {y | ¬(parameterPolynomial P y ≠ 0 ∧ Squarefree (parameterPolynomial P y))}

  have h_dim_pos : 0 < P.dim := by
    rw [param_dim_eq_finrank P, finrank_degreeLESubmodule k]
    apply Nat.choose_pos <;> omega

  -- Provide Nontrivial instance for NoAtoms volume
  haveI : Nonempty (Fin P.dim) := Fin.pos_iff_nonempty.mp h_dim_pos
  haveI : Nontrivial (CoefficientSpace P.dim) := by
    exact WithLp.instNontrivial 2 ((i : Fin P.dim) → (fun x => ℝ) i)

  -- Step 1: bad set has measure zero
  have h_bad_null : volume bad = 0 := by
    by_cases hk : k ≤ 1
    · -- Case k ≤ 1
      have h1 : ∀ (p : MvPolynomial (Fin 3) ℝ),
          p ≠ 0 → p.totalDegree ≤ k → Squarefree p := by
        intro p hp hdeg
        by_contra hnsq
        have h := exists_nonconstant_square_factor hp hdeg hnsq
        rcases h with ⟨q, r, _, hq_pos, hq_le⟩
        have h_k2 : k / 2 = 0 := by omega
        rw [h_k2] at hq_le
        linarith
      have h2 : bad ⊆ {0} := by
        intro y hy
        have h3 : ¬(parameterPolynomial P y ≠ 0 ∧ Squarefree (parameterPolynomial P y)) := hy
        by_cases h4 : parameterPolynomial P y = 0
        · have h5 : P.equiv y = P.equiv 0 := by
            simpa [parameterPolynomial] using h4
          have h6 : y = 0 := P.equiv.injective h5
          exact h6
        · have h5 : parameterPolynomial P y ≠ 0 := h4
          have h6 : (parameterPolynomial P y).totalDegree ≤ k := (P.equiv y).prop
          have h7 : Squarefree (parameterPolynomial P y) := h1 _ h5 h6
          exfalso; exact h3 ⟨h5, h7⟩
      have h3 : volume ({0} : Set (CoefficientSpace P.dim)) = 0 :=
        MeasureTheory.measure_singleton 0
      exact measure_mono_null h2 h3

    · -- Case k ≥ 2
      have hk2 : 2 ≤ k := by omega
      let zero_locus : Set (CoefficientSpace P.dim) :=
        {y | parameterPolynomial P y = 0}
      let nonsq_locus : Set (CoefficientSpace P.dim) :=
        {y | ¬Squarefree (parameterPolynomial P y)}

      have h_bad_decomp : bad ⊆ zero_locus ∪ nonsq_locus := by
        intro y hy
        simp only [bad, Set.mem_setOf_eq] at hy
        by_cases h : parameterPolynomial P y = 0
        · exact Or.inl h
        · have h' : ¬Squarefree (parameterPolynomial P y) := by tauto
          exact Or.inr h'

      -- Zero locus = {0}
      have h_zero_locus_eq : zero_locus = {0} := by
        ext y
        simp only [zero_locus, Set.mem_setOf_eq, Set.mem_singleton_iff]
        constructor
        · intro h
          have h5 : P.equiv y = P.equiv 0 := by
            simpa [parameterPolynomial] using h
          exact P.equiv.injective h5
        · intro h
          rw [h]
          simp [parameterPolynomial]
      have h_zero_null : volume zero_locus = 0 := by
        rw [h_zero_locus_eq]
        exact MeasureTheory.measure_singleton 0

      -- Non-squarefree locus ⊆ union of factorization map images
      let D := Finset.Icc 1 (k / 2)
      let S : ℕ → Set (CoefficientSpace P.dim) := fun d =>
        if h2d : 2 * d ≤ k then
          Set.range (fun (z : (degreeLESubmodule d) × (degreeLESubmodule (k - 2 * d))) =>
            let q : MvPolynomial (Fin 3) ℝ := z.1.val
            let r : MvPolynomial (Fin 3) ℝ := z.2.val
            P.equiv.symm ⟨q ^ 2 * r, square_mul_degree_bound h2d z.1.prop z.2.prop⟩)
        else
          ∅

      have h_nonsq_subset : nonsq_locus ⊆ ⋃ d ∈ D, S d := by
        intro y hy
        have h_p : ¬Squarefree (parameterPolynomial P y) := hy
        by_cases h_p0 : parameterPolynomial P y = 0
        · -- p = 0, so y = 0; 0 is in S d for any d ∈ D
          have h_y0 : y = 0 := by
            have h5 : P.equiv y = P.equiv 0 := by
              simpa [parameterPolynomial] using h_p0
            exact P.equiv.injective h5
          have hD_nonempty : D.Nonempty := by
            refine ⟨1, ?_⟩
            simp only [D, Finset.mem_Icc] <;> omega
          rcases hD_nonempty with ⟨d, hdD⟩
          have h2d : 2 * d ≤ k := by
            have h := (Finset.mem_Icc.mp hdD).2; omega
          have h0_in_S : (0 : CoefficientSpace P.dim) ∈ S d := by
            rw [show S d = _ from dif_pos h2d]
            let q0 : degreeLESubmodule d := ⟨0, by simp⟩
            let r0 : degreeLESubmodule (k - 2 * d) := ⟨0, by simp⟩
            have h_map : (P.equiv.symm ⟨(0 : MvPolynomial (Fin 3) ℝ) ^ 2 * (0 : MvPolynomial (Fin 3) ℝ),
                square_mul_degree_bound h2d q0.prop r0.prop⟩) = 0 := by
              simp <;> exact P.equiv.map_zero.symm
            exact ⟨(q0, r0), h_map⟩
          rw [h_y0]
          exact Set.mem_iUnion₂.mpr ⟨d, hdD, h0_in_S⟩
        · -- p ≠ 0
          have hdeg : (parameterPolynomial P y).totalDegree ≤ k := (P.equiv y).prop
          have hfac := exists_nonconstant_square_factor h_p0 hdeg h_p
          rcases hfac with ⟨q, r, hr_eq, hq_pos, hq_le⟩
          let d := q.totalDegree
          have hd1 : 1 ≤ d := hq_pos
          have hd2 : d ≤ k / 2 := hq_le
          have hdD : d ∈ D := by
            simp only [D, Finset.mem_Icc] <;> omega
          have h2d : 2 * d ≤ k := by omega
          have hr_deg : r.totalDegree ≤ k - 2 * d :=
            cofactor_degree_le h_p0 hr_eq hdeg hq_pos
          let q' : degreeLESubmodule d := ⟨q, le_refl d⟩
          let r' : degreeLESubmodule (k - 2 * d) := ⟨r, hr_deg⟩
          have hS_eq : S d = _ := dif_pos h2d
          have h_y_in_S : y ∈ S d := by
            rw [hS_eq]
            have h_main : (P.equiv.symm ⟨q ^ 2 * r,
                square_mul_degree_bound h2d q'.prop r'.prop⟩) = y := by
              apply P.equiv.injective
              apply Subtype.ext
              have h_eq2 : (q ^ 2 * r : MvPolynomial (Fin 3) ℝ) = (P.equiv y).val := by
                exact hr_eq.symm
              simpa using h_eq2
            exact ⟨(q', r'), h_main⟩
          exact Set.mem_iUnion₂.mpr ⟨d, hdD, h_y_in_S⟩

      -- Each S d has measure zero
      have h_S_null : ∀ d ∈ D, volume (S d) = 0 := by
        intro d hdD
        have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hdD).1
        have h2d : 2 * d ≤ k := by
          have h : d ≤ k / 2 := (Finset.mem_Icc.mp hdD).2; omega
        have hS_eq : S d = _ := dif_pos h2d
        rw [hS_eq]
        exact factorization_image_null hk2 hd1 h2d

      have hD_count : Set.Countable (D : Set ℕ) := by
        exact Finset.countable_toSet D
      have h_union_null : volume (⋃ d ∈ (D : Set ℕ), S d) = 0 :=
        (MeasureTheory.measure_biUnion_null_iff hD_count).mpr h_S_null

      have h_nonsq_null : volume nonsq_locus = 0 :=
        measure_mono_null h_nonsq_subset h_union_null

      have h_union2 : volume (zero_locus ∪ nonsq_locus) = 0 :=
        measure_union_null h_zero_null h_nonsq_null

      exact measure_mono_null h_bad_decomp h_union2

  -- Step 2: intersection with ball is null
  have h_inter_subset : bad ∩ Metric.ball x ε ⊆ bad := by
    intro z hz
    exact hz.1
  have h_ball_null : volume (bad ∩ Metric.ball x ε) = 0 :=
    measure_mono_null h_inter_subset h_bad_null

  -- Step 3: conclude AE using restrict measure
  let μ := volume.restrict (Metric.ball x ε)
  have h_ball_meas : MeasurableSet (Metric.ball x ε) := Metric.isOpen_ball.measurableSet
  have h_restrict_apply : μ bad = volume (bad ∩ Metric.ball x ε) :=
    MeasureTheory.Measure.restrict_apply' h_ball_meas
  have h_restrict_null : μ bad = 0 := by
    rw [h_restrict_apply]
    exact h_ball_null

  let good : Set (CoefficientSpace P.dim) :=
    {y | parameterPolynomial P y ≠ 0 ∧ Squarefree (parameterPolynomial P y)}
  have h_compl : goodᶜ = bad := by
    ext y; simp [good, bad]
  have h_final : ∀ᵐ (y : CoefficientSpace P.dim) ∂μ,
      parameterPolynomial P y ≠ 0 ∧ Squarefree (parameterPolynomial P y) := by
    have h : good ∈ MeasureTheory.ae μ := by
      rw [MeasureTheory.mem_ae_iff]
      rw [h_compl]
      exact h_restrict_null
    exact h

  exact h_final

end Kakeya.CV
