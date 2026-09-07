/-
# Perimeter Measure Density Equals One at Reduced Boundary Points

At μHE-a.e. point where `d(perimeterMeasure U)/dμHE[n-1] > 0`, the density
ratio equals 1. Consequently `perimeter U ≤ μHE[n-1](frontier U)`.

## Proof route

1. **Gauss-Green scaling**: At a TRB point x with normal ν, for smooth compactly
   supported ψ:
   `∫ ψ((y-x)/r) inner(ν, ν_U(y)) dμ(y) = r^{n-1} ∫_{U_{x,r}} fderiv ψ(z) ν dz`

2. **RHS limit** (COBALT): Blow-up convergence `U_{x,r} → Hν` in L¹_loc gives
   `∫_{U_{x,r}} fderiv ψ ν → ∫_{Hν} fderiv ψ ν = -∫_{Pν} ψ dH^{n-1}`

3. **LHS approximation**: Upper density + Lebesgue differentiation of normal gives
   `∫ ψ((y-x)/r) (inner(ν,ν_U)-1) dμ = o(r^{n-1})`

4. **Test functions to balls** (PELICAN): Approximate indicator of B(0,1) by smooth
   functions, use upper density to control annulus, get
   `μ(B(x,r)) / r^{n-1} → ω_{n-1}`

5. **μHE-a.e. upgrade**: Good points have full μ-measure in TRB. Since μ ≪ μHE,
   `dμ/dμHE = 0` off good set, and on good set density ratio = 1.

6. **Assembly**: `perimeter U = μ(frontier) = ∫ dμ/dμHE dμHE ≤ μHE(frontier)`.

## References

- Maggi, Sets of Finite Perimeter, Theorem 16.3
- Ambrosio-Fusco-Pallara, Functions of BV, Theorem 3.59
-/

import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.PerimeterDefinition
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.ReducedBoundaryData
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.BlowUpLemma
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.PerimeterMeasureSupport
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.PerimeterDensityLowerBound
import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.PerimeterAbsoluteContinuity
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.ReducedBoundaryOrientation
import MyLeanRepo.Kakeya.CV.Isoperimetric.Measure.Eilenberg
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.GeometricLowerBound
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.TrueReducedBoundaryHasData
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.LowerPerimeterDensityAE
import Mathlib.Tactic


open MeasureTheory Metric Set ENNReal Filter
open scoped MeasureTheory ContDiff

namespace Geometry.StructureTheorem

open Perimeter

variable {n : ℕ}

/-- **Step 1: Gauss-Green scaling identity**.

For a smooth compactly supported scalar test function `ψ`, a fixed unit vector `ν`,
and `r > 0`, let `η(y) := ψ((1/r)•(y - x))`. Then:

`∫ η(y) * inner(ν, ν_U(y)) dμ(y) = r^{n-1} ∫_{U_{x,r}} fderiv ψ(z) ν dz`

where `U_{x,r} = blowUp U x r`. -/
lemma gauss_green_scaling
    {U : Set (E n)} (hU : MeasurableSet U) (hfin : perimeter U < ⊤)
    (x : E n) (r : ℝ) (hr : 0 < r)
    (ν : E n) (hν_unit : ‖ν‖ = 1)
    (hn : 2 ≤ n)
    (ψ : E n → ℝ) (hψ_smooth : ContDiff ℝ ∞ ψ) (hψ_supp : HasCompactSupport ψ) :
    ∫ y, ψ ((1 / r) • (y - x)) * inner ℝ ν (measureTheoreticNormal U y) ∂(perimeterMeasure U) =
    (r : ℝ) ^ (n - 1) * ∫ z in blowUp U x r, fderiv ℝ ψ z ν := by
  let c : ℝ := 1 / r
  let η : E n → ℝ := fun y => ψ (c • (y - x))
  have hc_pos : 0 < c := by positivity
  have hc_ne : c ≠ 0 := hc_pos.ne'

  have h_sub : ContDiff ℝ ∞ (fun y : E n => y - x) :=
    contDiff_id.sub (show ContDiff ℝ ∞ (fun (_ : E n) => x) from contDiff_const)
  have hmap_smooth : ContDiff ℝ ∞ (fun y : E n => c • (y - x)) :=
    h_sub.const_smul c
  have hη_smooth : ContDiff ℝ ∞ η := hψ_smooth.comp hmap_smooth

  have hη_supp : HasCompactSupport η := by
    have h1 : Function.support η ⊆ (fun z : E n => x + r • z) '' tsupport ψ := by
      intro y hy
      have h2 : ψ (c • (y - x)) ≠ 0 := by simpa [η, Function.mem_support] using hy
      have h3 : c • (y - x) ∈ tsupport ψ := by
        exact subset_closure h2
      refine ⟨c • (y - x), h3, ?_⟩
      have h4 : x + r • (c • (y - x)) = y := by
        simp [c, smul_smul, hr.ne'] <;> abel
      exact h4
    have h_cont : Continuous (fun z : E n => x + r • z) := by fun_prop
    have h3 : IsCompact ((fun z : E n => x + r • z) '' tsupport ψ) :=
      hψ_supp.isCompact.image h_cont
    have h4 : closure (Function.support η) ⊆
        (fun z : E n => x + r • z) '' tsupport ψ :=
      closure_minimal h1 h3.isClosed
    exact h3.of_isClosed_subset isClosed_closure h4

  have h_main1 : ∫ y in U, fderiv ℝ η y ν =
      ∫ y, η y * inner ℝ ν (measureTheoreticNormal U y) ∂(perimeterMeasure U) :=
    gauss_green_scalar_identity hU hfin hν_unit hη_smooth hη_supp

  have h_fderiv : ∀ y : E n, fderiv ℝ η y ν = c * fderiv ℝ ψ (c • (y - x)) ν := by
    intro y
    have h_fd1 : HasFDerivAt (fun z : E n => c • (z - x)) (c • ContinuousLinearMap.id ℝ (E n)) y := by
      exact ((hasFDerivAt_id y).sub_const x).const_smul c
    have h_diff : Differentiable ℝ ψ := hψ_smooth.differentiable (by simp)
    have h_fd2 : HasFDerivAt ψ (fderiv ℝ ψ (c • (y - x))) (c • (y - x)) :=
      h_diff.differentiableAt.hasFDerivAt
    have h1 : HasFDerivAt η ((fderiv ℝ ψ (c • (y - x))).comp (c • ContinuousLinearMap.id ℝ (E n))) y :=
      h_fd2.comp y h_fd1
    have h2 : (fderiv ℝ ψ (c • (y - x))).comp (c • ContinuousLinearMap.id ℝ (E n)) =
        c • (fderiv ℝ ψ (c • (y - x))) := by
      ext v
      simp [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply]
      <;> ring
    have h3 : fderiv ℝ η y = (fderiv ℝ ψ (c • (y - x))).comp (c • ContinuousLinearMap.id ℝ (E n)) :=
      h1.fderiv
    rw [h3, h2]
    simp [ContinuousLinearMap.smul_apply] <;> ring

  let g : E n → ℝ := fun z => fderiv ℝ ψ z ν
  have h1_fd : Continuous (fderiv ℝ ψ) := hψ_smooth.continuous_fderiv (by simp)
  have hg_cont : Continuous g := by
    have h_eval : Continuous (fun (L : E n →L[ℝ] ℝ) => L ν) := by fun_prop
    exact h_eval.comp h1_fd
  have hg_supp : HasCompactSupport g := by
    have h1 : Function.support g ⊆ tsupport ψ := by
      intro z hz
      by_cases h : z ∈ tsupport ψ
      · exact h
      · have h2 : ψ =ᶠ[nhds z] 0 := by
          have h3 : (tsupport ψ)ᶜ ∈ nhds z := IsOpen.mem_nhds (isOpen_compl_iff.mpr hψ_supp.isCompact.isClosed) h
          filter_upwards [h3] with w hw
          have h4 : w ∉ tsupport ψ := hw
          have h5 : w ∉ closure (Function.support ψ) := h4
          have h6 : w ∉ Function.support ψ := fun h7 => h5 (subset_closure h7)
          simpa [Function.mem_support] using h6
        have h4 : fderiv ℝ ψ z = 0 := fderiv_zero_outside_tsupport hψ_smooth h
        have h5 : g z = 0 := by simp [g, h4]
        exact False.elim (Function.mem_support.mp hz h5)
    have h4 : closure (Function.support g) ⊆ tsupport ψ := closure_minimal h1 hψ_supp.isCompact.isClosed
    exact hψ_supp.isCompact.of_isClosed_subset isClosed_closure h4
  have hg_int : Integrable g volume := hg_cont.integrable_of_hasCompactSupport hg_supp

  have h_change_vars : ∫ z in blowUp U x r, g z =
      c ^ n * ∫ y in U, g (c • (y - x)) :=
    blowUp_integral_change_of_vars hr hU g hg_int

  have h_eq1 : ∫ y in U, fderiv ℝ η y ν =
      c * ∫ y in U, fderiv ℝ ψ (c • (y - x)) ν := by
    have h : ∫ y in U, fderiv ℝ η y ν = ∫ y in U, (c * fderiv ℝ ψ (c • (y - x)) ν) := by
      apply integral_congr_ae
      filter_upwards with y
      exact h_fderiv y
    rw [h]
    rw [integral_const_mul]

  have h_final : ∫ y in U, fderiv ℝ η y ν =
      (r : ℝ) ^ (n - 1) * ∫ z in blowUp U x r, fderiv ℝ ψ z ν := by
    rw [h_eq1]
    have h2 : ∫ y in U, fderiv ℝ ψ (c • (y - x)) ν =
        (1 / c ^ n) * ∫ z in blowUp U x r, fderiv ℝ ψ z ν := by
      rw [h_change_vars]
      have hcn_pos : 0 < c ^ n := by positivity
      field_simp [hcn_pos.ne'] <;> ring
    rw [h2]
    have h3 : c * ((1 / c ^ n) * ∫ z in blowUp U x r, fderiv ℝ ψ z ν) =
        (c * (1 / c ^ n)) * ∫ z in blowUp U x r, fderiv ℝ ψ z ν := by ring
    rw [h3]
    have h4 : c * (1 / c ^ n) = (r : ℝ) ^ (n - 1) := by
      simp only [c]
      have hn1 : 1 ≤ n := by linarith
      have h5 : (1 / r : ℝ) ^ n = 1 / r ^ n := by
        have h6 : ∀ k : ℕ, (1 / r : ℝ) ^ k = 1 / r ^ k := by
          intro k; induction k with
          | zero => norm_num
          | succ k ih => rw [pow_succ, pow_succ, ih] <;> field_simp [hr.ne'] <;> ring
        exact h6 n
      rw [h5]
      have h7 : (1 / r : ℝ) * (1 / (1 / r ^ n)) = (r : ℝ) ^ (n - 1) := by
        have h8 : 1 / (1 / r ^ n : ℝ) = r ^ n := by
          field_simp [hr.ne'] <;> ring
        rw [h8]
        have h9 : (1 / r : ℝ) * r ^ n = (r : ℝ) ^ (n - 1) := by
          cases n with
          | zero => linarith
          | succ n' =>
            simp [pow_succ, hr.ne'] <;> field_simp <;> ring
        exact h9
      exact h7
    rw [h4]

  rw [←h_main1]
  exact h_final

/-- **Step 2 (COBALT): Blow-up integral convergence**.

Given L¹_loc convergence of blow-ups to the half-space `Hν`, for any smooth
compactly supported `ψ`:
`∫_{U_{x,r}} fderiv ψ ν → ∫_{Hν} fderiv ψ ν = -∫_{Pν} ψ dH^{n-1}` -/
lemma blowup_integral_convergence
    {U : Set (E n)} (hU : MeasurableSet U) {x : E n} {ν : E n} (hν_unit : ‖ν‖ = 1)
    (h_conv : ∀ (R : ℝ), 0 < R →
      Tendsto (fun r : ℝ => volume (symmDiff (blowUp U x r) (halfSpace ν) ∩ ball (0 : E n) R))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (ψ : E n → ℝ) (hψ_smooth : ContDiff ℝ ∞ ψ) (hψ_supp : HasCompactSupport ψ) :
    Tendsto (fun r : ℝ => ∫ z in blowUp U x r, fderiv ℝ ψ z ν)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (∫ z in halfSpace ν, fderiv ℝ ψ z ν)) := by
  let f : E n → ℝ := fun z => fderiv ℝ ψ z ν
  have h1_fd : Continuous (fderiv ℝ ψ) := hψ_smooth.continuous_fderiv (by simp)
  have hf_cont : Continuous f := by
    have h_eval : Continuous (fun (L : E n →L[ℝ] ℝ) => L ν) := by fun_prop
    exact h_eval.comp h1_fd
  have h_supp1 : Function.support f ⊆ tsupport ψ := by
    intro z hz
    by_cases h : z ∈ tsupport ψ
    · exact h
    · have h2 : fderiv ℝ ψ z = 0 := fderiv_zero_outside_tsupport hψ_smooth h
      have h3 : f z = 0 := by simp [f, h2]
      exact False.elim (Function.mem_support.mp hz h3)
  have hf_supp : HasCompactSupport f := by
    have h4 : closure (Function.support f) ⊆ tsupport ψ :=
      closure_minimal h_supp1 hψ_supp.isCompact.isClosed
    exact hψ_supp.isCompact.of_isClosed_subset isClosed_closure h4
  have hf_int : Integrable f volume := hf_cont.integrable_of_hasCompactSupport hf_supp
  let K := tsupport ψ
  have hK_compact : IsCompact K := hψ_supp.isCompact
  have hK_bdd : Bornology.IsBounded K := hK_compact.isBounded
  rcases hK_bdd.subset_ball (0 : E n) with ⟨r0, hr0⟩
  let R : ℝ := max r0 1
  have hR_pos : 0 < R := by positivity
  have hK_ball : K ⊆ ball (0 : E n) R := by
    intro z hz
    have h2 : dist z 0 < r0 := hr0 hz
    have h3 : r0 ≤ R := le_max_left r0 1
    have h4 : dist z 0 < R := by linarith
    exact h4
  have h_bdd1 : BddAbove (Set.image (fun z : E n => |f z|) K) :=
    hK_compact.bddAbove_image (hf_cont.norm.continuousOn)
  rcases h_bdd1 with ⟨C0, hC0⟩
  let C : ℝ := max C0 1
  have hC_pos : 0 < C := by positivity
  have hC : ∀ z, |f z| ≤ C := by
    intro z
    by_cases hz : z ∈ K
    · have h5 : |f z| ∈ Set.image (fun z => |f z|) K := ⟨z, hz, rfl⟩
      have h6 : |f z| ≤ C0 := hC0 h5
      have h7 : C0 ≤ C := le_max_left C0 1
      linarith
    · have h7 : z ∉ Function.support f := fun h8 => hz (h_supp1 h8)
      have h8 : f z = 0 := by simpa [Function.mem_support] using h7
      rw [h8]
      have h9 : |(0 : ℝ)| ≤ C := by
        have h10 : |(0 : ℝ)| = 0 := by simp
        rw [h10]
        <;> linarith
      exact h9
  have hU_meas : ∀ (r : ℝ), 0 < r → MeasurableSet (blowUp U x r) := by
    intro r hr
    have h_me : MeasurableEmbedding (blowUpMap x r) := blowUpMap_measurableEmbedding x hr.ne'
    exact h_me.measurableSet_image.mpr hU
  have hH_meas : MeasurableSet (halfSpace ν) := by
    have h1 : Continuous (fun z : E n => inner ℝ z ν) := by fun_prop
    exact (isOpen_Iio.preimage h1).measurableSet
  have h_main_estimate : ∀ (r : ℝ), 0 < r →
      |((∫ z in blowUp U x r, f z) - (∫ z in halfSpace ν, f z))| ≤
        C * (volume (symmDiff (blowUp U x r) (halfSpace ν) ∩ ball (0 : E n) R)).toReal := by
    intro r hr
    set A := blowUp U x r with hA_def
    set B := halfSpace ν with hB_def
    have hA_meas : MeasurableSet A := hU_meas r hr
    have hB_meas : MeasurableSet B := hH_meas
    have hsd : symmDiff A B = (A \ B) ∪ (B \ A) := by
      exact Subset.antisymm (fun ⦃a⦄ a_1 => a_1) fun ⦃a⦄ a_1 => a_1
    have h11 : ∫ z in A, f z = ∫ z, indicator A f z := by
      rw [integral_indicator hA_meas]
    have h12 : ∫ z in B, f z = ∫ z, indicator B f z := by
      rw [integral_indicator hB_meas]
    have h_int1 : Integrable (indicator A f) volume := hf_int.indicator hA_meas
    have h_int2 : Integrable (indicator B f) volume := hf_int.indicator hB_meas
    let hdiff : E n → ℝ := indicator A f - indicator B f
    have h1 : (∫ z in A, f z) - (∫ z in B, f z) = ∫ z, hdiff z := by
      calc (∫ z in A, f z) - (∫ z in B, f z)
        = (∫ z, indicator A f z) - (∫ z, indicator B f z) := by rw [h11, h12]
      _ = ∫ z, (indicator A f z - indicator B f z) := by rw [integral_sub h_int1 h_int2]
      _ = ∫ z, hdiff z := by rfl
    have h2 : |∫ z, hdiff z| ≤ ∫ z, |hdiff z| := abs_integral_le_integral_abs
    let bound : E n → ℝ := fun z => C * Set.indicator (symmDiff A B ∩ ball (0 : E n) R) 1 z
    have h3 : ∀ z, |hdiff z| ≤ bound z := by
      intro z
      by_cases hz : z ∈ symmDiff A B ∩ ball (0 : E n) R
      · have hb : bound z = C := by
          simp [bound, Set.indicator, hz]
        rw [hb]
        have h4 : |f z| ≤ C := hC z
        by_cases h5 : z ∈ A
        · have h6 : z ∉ B := by
            by_contra h7
            have h8 : z ∉ symmDiff A B := by
              intro h9
              rw [hsd] at h9
              rcases h9 with (⟨hA, hnB⟩ | ⟨hB, hnA⟩)
              · exact hnB h7
              · exact hnA h5
            exact h8 hz.1
          have h9 : hdiff z = f z := by
            simp [hdiff, h5, h6]
          rw [h9] <;> exact h4
        · have h6 : z ∈ B := by
            by_contra h7
            have h8 : z ∉ symmDiff A B := by
              intro h9
              rw [hsd] at h9
              rcases h9 with (⟨hA, hnB⟩ | ⟨hB, hnA⟩)
              · exact h5 hA
              · exact h7 hB
            exact h8 hz.1
          have h9 : hdiff z = -f z := by
            simp [hdiff, h5, h6] <;> ring
          rw [h9] <;> rw [abs_neg] <;> exact h4
      · have hb : bound z = 0 := by
          simp [bound, Set.indicator, hz]
        rw [hb]
        by_cases h6 : z ∈ ball (0 : E n) R
        · have h7 : z ∉ symmDiff A B := by tauto
          have h8 : z ∈ A ↔ z ∈ B := by
            constructor
            · intro hA
              by_contra hB
              have h9 : z ∈ symmDiff A B := by
                rw [hsd]
                exact Or.inl ⟨hA, hB⟩
              exact h7 h9
            · intro hB
              by_contra hA
              have h9 : z ∈ symmDiff A B := by
                rw [hsd]
                exact Or.inr ⟨hB, hA⟩
              exact h7 h9
          have h9 : indicator A f z = indicator B f z := by
            by_cases h10 : z ∈ A
            · have h11 : z ∈ B := h8.mp h10
              simp [Set.indicator, h10, h11]
            · have h11 : z ∉ B := by
                intro h12
                exact h10 (h8.mpr h12)
              simp [Set.indicator, h10, h11]
          have h10 : hdiff z = 0 := by
            simp [hdiff, h9]
          rw [h10] <;> simp
        · have h7 : z ∉ K := by
            intro h8
            exact h6 (hK_ball h8)
          have h8 : z ∉ Function.support f := fun h9 => h7 (h_supp1 h9)
          have h9 : f z = 0 := by simpa [Function.mem_support] using h8
          have h10 : indicator A f z = 0 := by simp [Set.indicator, h9]
          have h11 : indicator B f z = 0 := by simp [Set.indicator, h9]
          have h12 : hdiff z = 0 := by
            simp [hdiff, h10, h11]
          rw [h12] <;> simp
    have h4_meas : MeasurableSet (symmDiff A B ∩ ball (0 : E n) R) := by
      have hsd : MeasurableSet (symmDiff A B) := by
        have h1 : MeasurableSet (A \ B) := hA_meas.diff hB_meas
        have h2 : MeasurableSet (B \ A) := hB_meas.diff hA_meas
        have h3 : (A \ B) ∪ (B \ A) = symmDiff A B := by
          exact hsd.symm
        rw [←h3]
        exact h1.union h2
      exact hsd.inter isOpen_ball.measurableSet
    have h4_fin : volume (symmDiff A B ∩ ball (0 : E n) R) < ⊤ :=
      (measure_mono inter_subset_right).trans_lt measure_ball_lt_top
    have h_int_bound : Integrable bound volume := by
      have h1 : IntegrableOn (1 : E n → ℝ) (symmDiff A B ∩ ball (0 : E n) R) volume :=
        MeasureTheory.integrableOn_const (hs := h4_fin.ne) (hC := by simp [ENorm.enorm])
      have h2 : Integrable (Set.indicator (symmDiff A B ∩ ball (0 : E n) R) (1 : E n → ℝ)) volume :=
        (integrable_indicator_iff h4_meas).mpr h1
      exact h2.const_mul C
    calc |(∫ z in A, f z) - (∫ z in B, f z)|
      = |∫ z, hdiff z| := by rw [h1]
    _ ≤ ∫ z, |hdiff z| := h2
    _ ≤ ∫ z, bound z := integral_mono (h_int1.sub h_int2).abs h_int_bound h3
    _ = C * (volume (symmDiff A B ∩ ball (0 : E n) R)).toReal := by
        have h51 : ∫ z, bound z = C * ∫ z, Set.indicator (symmDiff A B ∩ ball (0 : E n) R) (1 : E n → ℝ) z := by
          rw [integral_const_mul]
          <;> rfl
        rw [h51]
        have h52 : ∫ z, Set.indicator (symmDiff A B ∩ ball (0 : E n) R) (1 : E n → ℝ) z = (volume (symmDiff A B ∩ ball (0 : E n) R)).toReal := by
          have h_eq1 : ∫ z, Set.indicator (symmDiff A B ∩ ball (0 : E n) R) (1 : E n → ℝ) z = ∫ z in (symmDiff A B ∩ ball (0 : E n) R), (1 : ℝ) := by
            rw [integral_indicator h4_meas] <;> rfl
          rw [h_eq1]
          have h_eq2 : ∫ z in (symmDiff A B ∩ ball (0 : E n) R), (1 : ℝ) = (volume (symmDiff A B ∩ ball (0 : E n) R)).toReal := by
            simp [integral_const]
            <;> rfl
          exact h_eq2
        rw [h52] <;> ring
  have h4 := h_conv R hR_pos
  have h_ne_top : ∀ (r : ℝ), volume (symmDiff (blowUp U x r) (halfSpace ν) ∩ ball (0 : E n) R) ≠ ⊤ := by
    intro r
    have h_sub : (symmDiff (blowUp U x r) (halfSpace ν) ∩ ball (0 : E n) R) ⊆ ball (0 : E n) R := inter_subset_right
    have h_le : volume (symmDiff (blowUp U x r) (halfSpace ν) ∩ ball (0 : E n) R) ≤ volume (ball (0 : E n) R) := measure_mono h_sub
    have h_lt : volume (ball (0 : E n) R) < ⊤ := measure_ball_lt_top
    exact (h_le.trans_lt h_lt).ne
  have h5 : Tendsto (fun r : ℝ => (volume (symmDiff (blowUp U x r) (halfSpace ν) ∩ ball (0 : E n) R)).toReal)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    (ENNReal.tendsto_toReal_zero_iff (hf := h_ne_top)).mpr h4
  have h_tendsto : Tendsto (fun r : ℝ => C * (volume (symmDiff (blowUp U x r) (halfSpace ν) ∩ ball (0 : E n) R)).toReal)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa [mul_zero] using h5.const_mul C
  let F : ℝ → ℝ := fun r => (∫ z in blowUp U x r, f z) - (∫ z in halfSpace ν, f z)
  let G : ℝ → ℝ := fun r => C * (volume (symmDiff (blowUp U x r) (halfSpace ν) ∩ ball (0 : E n) R)).toReal
  have h_nonneg : ∀ᶠ (r : ℝ) in nhdsWithin 0 (Set.Ioi 0), 0 ≤ |F r| := by
    filter_upwards with r <;> exact abs_nonneg _
  have h_ev : ∀ᶠ (r : ℝ) in nhdsWithin 0 (Set.Ioi 0), |F r| ≤ G r := by
    have h_pos : ∀ᶠ (r : ℝ) in nhdsWithin 0 (Set.Ioi 0), 0 < r := self_mem_nhdsWithin
    filter_upwards [h_pos] with r hr
    exact h_main_estimate r hr
  have h_abs_tendsto : Tendsto (fun r => |F r|) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    squeeze_zero' h_nonneg h_ev h_tendsto
  have h_final : Tendsto F (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa [Metric.tendsto_nhds, dist_eq_norm] using h_abs_tendsto
  have h_add : Tendsto (fun r : ℝ => ∫ z in blowUp U x r, f z) (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ z in halfSpace ν, f z)) := by
    have h_eq : (fun r : ℝ => ∫ z in blowUp U x r, f z) = fun r => F r + (∫ z in halfSpace ν, f z) := by
      funext r; simp [F] <;> abel
    rw [h_eq]
    have h_const : Tendsto (fun r : ℝ => ∫ z in halfSpace ν, f z) (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ z in halfSpace ν, f z)) :=
      tendsto_const_nhds
    have h_result := h_final.add h_const
    simpa [zero_add] using h_result
  exact h_add

/-- **Half-space divergence theorem** (COBALT):
`∫_{Hν} fderiv ψ ν = ∫_{Pν} ψ dH^{n-1}` where `Pν = {inner(z,ν) = 0}`. -/
lemma halfspace_divergence_theorem
    {ν : E n} (hν_unit : ‖ν‖ = 1)
    (ψ : E n → ℝ) (hψ_smooth : ContDiff ℝ ∞ ψ) (hψ_supp : HasCompactSupport ψ) :
    ∫ z in halfSpace ν, fderiv ℝ ψ z ν =
    ∫ z in {z : E n | inner ℝ z ν = 0}, ψ z ∂μHE[n - 1] := by
  let s : Submodule ℝ (E n) := ℝ ∙ ν
  let Pν : Submodule ℝ (E n) := sᗮ
  have hν_ne_zero : ν ≠ 0 := by
    intro h
    rw [h] at hν_unit
    simp at hν_unit <;> linarith

  -- Step 1: Measure-preserving equivalence E n ≃ᵐ ℝ × Pν
  let e0 : E n ≃ᵐ s × Pν := s.measurableEquivProd (0 : E n)
  have h_eq_vol : (μHE[Module.finrank ℝ (E n)] : Measure (E n)) = volume :=
    InnerProductSpace.euclideanHausdorffMeasure_eq_volume
  have h_mp0_he : MeasurePreserving e0 (μHE[Module.finrank ℝ (E n)]) :=
    Submodule.measurePreserving_measurableEquivProd s (0 : E n)
  have h_mp0 : MeasurePreserving e0 volume := by
    rw [← h_eq_vol]
    exact h_mp0_he

  let e_sₗ : ℝ ≃ₗᵢ[ℝ] s := LinearIsometryEquiv.toSpanUnitSingleton ν hν_unit
  let e_s : s ≃ᵐ ℝ := e_sₗ.symm.toHomeomorph.toMeasurableEquiv
  have h_mps : MeasurePreserving e_s volume := e_sₗ.symm.measurePreserving

  let e_prod : s × Pν ≃ᵐ ℝ × Pν :=
    { toFun := fun p : s × Pν => (e_s p.1, p.2),
      invFun := fun p : ℝ × Pν => (e_s.symm p.1, p.2),
      left_inv := by intro ⟨x, y⟩; simp,
      right_inv := by intro ⟨x, y⟩; simp,
      measurable_toFun := (e_s.measurable.comp measurable_fst).prod measurable_snd,
      measurable_invFun := (e_s.symm.measurable.comp measurable_fst).prod measurable_snd }
  have h_e_prod_apply : ∀ (p : s × Pν), e_prod p = (e_s p.1, p.2) := by
    intro p; rfl
  have h_mp_prod : MeasurePreserving e_prod volume volume := by
    have hvol1 : (volume : Measure (s × Pν)) = volume.prod volume :=
      MeasureTheory.Measure.volume_eq_prod s Pν
    have hvol2 : (volume : Measure (ℝ × Pν)) = volume.prod volume :=
      MeasureTheory.Measure.volume_eq_prod ℝ Pν
    rw [hvol1, hvol2]
    have h : MeasurePreserving (Prod.map (e_s : s → ℝ) (id : Pν → Pν)) (volume.prod volume) (volume.prod volume) :=
      h_mps.prod (MeasurePreserving.id volume)
    have h_eq : (e_prod : (s × Pν) → (ℝ × Pν)) = Prod.map e_s id := by
      funext p; exact h_e_prod_apply p
    rw [h_eq]
    exact h

  let e' : E n ≃ᵐ ℝ × Pν := e0.trans e_prod
  have h_mp' : MeasurePreserving e' volume volume :=
    h_mp_prod.comp h_mp0

  -- Step 2: Formula for e' and e'.symm
  have h_proj_s : ∀ (z : E n), s.orthogonalProjectionOnto z = (inner ℝ ν z) • ν := by
    intro z
    have h : s.starProjection z = inner ℝ ν z • ν :=
      Submodule.starProjection_unit_singleton ℝ hν_unit z
    have h2 : s.starProjection z = s.orthogonalProjectionOnto z := by rfl
    rw [h2] at h
    exact h

  have h_e_s_symm : ∀ (t : ℝ), e_s.symm t = (⟨t • ν, Submodule.mem_span_singleton.mpr ⟨t, by simp⟩⟩ : s) := by
    intro t
    exact LinearIsometryEquiv.toSpanUnitSingleton_apply ν hν_unit t

  have h_e'_apply : ∀ (z : E n), e' z = (inner ℝ z ν, sᗮ.orthogonalProjectionOnto z) := by
    intro z
    have h1a := Submodule.measurableEquivProd_apply s (0 : E n) z
    have h_sub : z -ᵥ (0 : E n) = z := by simp
    rw [h_sub] at h1a
    have h1 : e0 z = (s.orthogonalProjectionOnto z, sᗮ.orthogonalProjectionOnto z) := h1a
    have h2 : e' z = e_prod (e0 z) := by rfl
    rw [h2, h1]
    have h3 : e_prod (s.orthogonalProjectionOnto z, sᗮ.orthogonalProjectionOnto z) =
        (e_s (s.orthogonalProjectionOnto z), sᗮ.orthogonalProjectionOnto z) :=
      h_e_prod_apply _
    rw [h3]
    have h5 : (s.orthogonalProjectionOnto z : E n) = inner ℝ ν z • ν := h_proj_s z
    have h6 : e_s (s.orthogonalProjectionOnto z) = inner ℝ ν z := by
      have h7 : e_s.symm (inner ℝ ν z) = s.orthogonalProjectionOnto z := by
        rw [h_e_s_symm]
        apply Subtype.ext
        exact Eq.symm h5
      have h8 : e_s (e_s.symm (inner ℝ ν z)) = inner ℝ ν z := e_s.apply_symm_apply (inner ℝ ν z)
      rw [h7] at h8
      exact h8
    have h9 : inner ℝ ν z = inner ℝ z ν := by exact real_inner_comm z ν
    rw [h6, h9]
    <;> rfl

  have h_e'_symm : ∀ (t : ℝ) (w : Pν), e'.symm (t, w) = t • ν + w.val := by
    intro t w
    have h1 : e'.symm (t, w) = e0.symm (e_prod.symm (t, w)) := by rfl
    rw [h1]
    have h2 : e_prod.symm (t, w) = (e_s.symm t, w) := by rfl
    rw [h2]
    have h3 : e0.symm (e_s.symm t, w) = ((e_s.symm t).val + w.val) +ᵥ (0 : E n) := by
      rw [Submodule.measurableEquivProd_symm_apply s (0 : E n)]
    rw [h3]
    have h4 : ((e_s.symm t).val + w.val) +ᵥ (0 : E n) = (e_s.symm t).val + w.val := by
      simp
    rw [h4]
    rw [h_e_s_symm t]
    <;> rfl

  -- Step 3: Image of halfspace
  have h_image : e' '' halfSpace ν = Set.Iio 0 ×ˢ (Set.univ : Set Pν) := by
    ext p
    simp only [Set.mem_image, Set.mem_prod, Set.mem_univ, true_and]
    constructor
    · rintro ⟨z, hz, h_eq⟩
      have h4 : e' z = p := h_eq
      have h5 : inner ℝ z ν < 0 := by simpa [halfSpace] using hz
      have h6 : (e' z).1 = p.1 := by rw [h4]
      have h7 : (e' z).1 = inner ℝ z ν := by
        rw [h_e'_apply z] <;> rfl
      have h8 : p.1 = inner ℝ z ν := by
        rw [←h6, h7]
      have h9 : p.1 < 0 := by
        have h10 : p.1 = inner ℝ z ν := h8
        rw [h10]
        exact h5
      exact ⟨h9, trivial⟩
    · rintro ⟨ht, _⟩
      refine ⟨e'.symm (p.1, p.2), ?_, ?_⟩
      · have h_inner : inner ℝ (e'.symm (p.1, p.2)) ν = p.1 := by
          rw [h_e'_symm]
          have hOrth : inner ℝ (↑p.2) ν = 0 := by
            have hOrth' : inner ℝ ν (↑p.2) = 0 := p.2.property ν (Submodule.mem_span_singleton.mpr ⟨1, by simp⟩)
            have hComm : inner ℝ (↑p.2) ν = inner ℝ ν (↑p.2) := by exact real_inner_comm ν ↑p.2
            rw [hComm, hOrth']
          simp [inner_add_left, inner_smul_left, hν_unit, hOrth] <;> ring
        have h_goal : inner ℝ (e'.symm (p.1, p.2)) ν < 0 := by
          rw [h_inner]
          exact ht
        simpa [halfSpace] using h_goal
      · exact e'.apply_symm_apply (p.1, p.2)

  -- Step 4: Change variables
  let G : E n → ℝ := fun z => fderiv ℝ ψ z ν
  have h_fd_cont : Continuous (fderiv ℝ ψ) := hψ_smooth.continuous_fderiv (by norm_num)
  have h_eval : Continuous (fun f : (E n →L[ℝ] ℝ) => f ν) := by exact continuous_eval_const ν
  have hG_cont : Continuous G := h_eval.comp h_fd_cont
  have hG_supp : HasCompactSupport G := by
    have h1 : Function.support G ⊆ tsupport ψ := by
      intro x hx
      by_contra h2
      let s : Set (E n) := (tsupport ψ)ᶜ
      have hs_closed : IsClosed (tsupport ψ) := hψ_supp.isCompact.isClosed
      have hs_open : IsOpen s := hs_closed.isOpen_compl
      have hx_s : x ∈ s := h2
      have h_zero : ∀ y ∈ s, ψ y = 0 := by
        intro y hy
        have h7 : y ∉ Function.support ψ := fun h8 => hy (subset_closure h8)
        simpa [Function.mem_support] using h7
      have h4 : ∀ y ∈ s, G y = 0 := by
        intro y hy
        have h5 : ψ =ᶠ[nhds y] 0 := by
          filter_upwards [hs_open.mem_nhds hy] with z hz
          exact h_zero z hz
        have h6 : fderiv ℝ ψ y = 0 := by
          have h7 : fderiv ℝ ψ y = fderiv ℝ (fun _ : E n => (0 : ℝ)) y := h5.fderiv_eq
          rw [h7]
          have h8 : fderiv ℝ (fun _ : E n => (0 : ℝ)) y = 0 := by simp
          exact h8
        simpa [G] using congr_arg (fun f : (E n →L[ℝ] ℝ) => f ν) h6
      have h7 : G x = 0 := h4 x hx_s
      exact hx h7
    exact hψ_supp.mono' h1
  have hG_int : Integrable G volume := hG_cont.integrable_of_hasCompactSupport hG_supp

  let F : ℝ × Pν → ℝ := fun p => G (e'.symm p)

  have h1 : ∫ z in halfSpace ν, G z =
      ∫ p in Set.Iio 0 ×ˢ (Set.univ : Set Pν), F p := by
    have h_eq1 : ∫ p in e' '' halfSpace ν, F p =
        ∫ z in halfSpace ν, F (e' z) :=
      h_mp'.setIntegral_image_emb e'.measurableEmbedding F (halfSpace ν)
    have h_eq2 : ∀ z, F (e' z) = G z := by
      intro z
      simp [F, e'.left_inv z]
    have h_eq3 : ∫ z in halfSpace ν, F (e' z) = ∫ z in halfSpace ν, G z := by
      apply integral_congr_ae
      filter_upwards with z
      exact h_eq2 z
    rw [←h_eq3, ←h_eq1, h_image]

  rw [h1]

  -- Step 5: Fubini
  have h_meas1 : MeasurableSet (Set.Iio (0 : ℝ) ×ˢ (Set.univ : Set Pν)) :=
    isOpen_Iio.measurableSet.prod MeasurableSet.univ

  let F : ℝ × Pν → ℝ := fun p => G (e'.symm p)

  have hF_int : Integrable F volume := by
    have h_mp_symm : MeasurePreserving e'.symm volume volume := h_mp'.symm
    have h : Integrable (G ∘ e'.symm) volume ↔ Integrable G volume :=
      h_mp_symm.integrable_comp_emb e'.symm.measurableEmbedding
    exact h.mpr hG_int

  have h2 : ∫ p in Set.Iio 0 ×ˢ (Set.univ : Set Pν), F p =
      ∫ w : Pν, ∫ t in Set.Iio 0, F (t, w) := by
    have hvol : (volume : Measure (ℝ × Pν)) = volume.prod volume :=
      MeasureTheory.Measure.volume_eq_prod ℝ Pν
    have hF_on : IntegrableOn F (Set.Iio 0 ×ˢ (Set.univ : Set Pν)) (volume.prod volume) := by
      rw [←hvol]
      exact hF_int.integrableOn
    let G' : ℝ × Pν → ℝ := Set.indicator (Set.Iio 0 ×ˢ (Set.univ : Set Pν)) F
    have hG'_int : Integrable G' (volume.prod volume) := by
      have h_iff : Integrable G' (volume.prod volume) ↔ IntegrableOn F (Set.Iio 0 ×ˢ (Set.univ : Set Pν)) (volume.prod volume) :=
        integrable_indicator_iff h_meas1
      exact h_iff.mpr hF_on
    have h_eq1 : ∫ p in Set.Iio (0 : ℝ) ×ˢ (Set.univ : Set Pν), F p = ∫ z, G' z ∂volume.prod volume := by
      rw [hvol]
      have h : ∫ p in Set.Iio (0 : ℝ) ×ˢ (Set.univ : Set Pν), F p ∂volume.prod volume =
          ∫ z, Set.indicator (Set.Iio (0 : ℝ) ×ˢ (Set.univ : Set Pν)) F z ∂volume.prod volume := by
        have h_nm1 : NullMeasurableSet (Set.Iio (0 : ℝ) ×ˢ (Set.univ : Set Pν)) (volume.prod volume) := by exact MeasurableSet.nullMeasurableSet h_meas1
        exact (MeasureTheory.integral_indicator₀ h_nm1).symm
      exact h
    rw [h_eq1]
    have h_eq2 : ∫ z, G' z ∂volume.prod volume = ∫ w : Pν, ∫ t : ℝ, G' (t, w) :=
      MeasureTheory.integral_prod_symm G' hG'_int
    rw [h_eq2]
    have h_eq3 : ∀ (w : Pν), ∫ t : ℝ, G' (t, w) = ∫ t in Set.Iio (0 : ℝ), F (t, w) := by
      intro w
      have h51 : ∀ (t : ℝ), G' (t, w) = Set.indicator (Set.Iio (0 : ℝ)) (fun t => F (t, w)) t := by
        intro t
        simp [G', Set.indicator, Set.mem_prod]
        <;> tauto
      have h52 : ∫ t : ℝ, G' (t, w) = ∫ t : ℝ, Set.indicator (Set.Iio (0 : ℝ)) (fun t => F (t, w)) t := by
        apply integral_congr_ae
        filter_upwards with t
        exact h51 t
      rw [h52]
      have h53 : ∫ t : ℝ, Set.indicator (Set.Iio (0 : ℝ)) (fun t => F (t, w)) t =
          ∫ t in Set.Iio (0 : ℝ), F (t, w) := by
        have h_nm2 : NullMeasurableSet (Set.Iio (0 : ℝ)) volume := by exact nullMeasurableSet_Iio
        exact MeasureTheory.integral_indicator₀ h_nm2
      exact h53
    apply integral_congr_ae
    filter_upwards with w
    exact h_eq3 w

  rw [h2]

  -- Step 6: FTC for each w
  have h3 : ∀ (w : Pν), ∫ t in Set.Iio 0, F (t, w) = ψ (w.val) := by
    intro w
    let f_w : ℝ → ℝ := fun t => ψ (e'.symm (t, w))
    have h_fd : ∀ (t : ℝ), HasDerivAt f_w (fderiv ℝ ψ (e'.symm (t, w)) ν) t := by
      intro t
      have h_diff : DifferentiableAt ℝ ψ (e'.symm (t, w)) :=
        (hψ_smooth.differentiable (by norm_num)).differentiableAt
      have h_line : HasDerivAt (fun t : ℝ => e'.symm (t, w)) ν t := by
        have h_eq : (fun t : ℝ => e'.symm (t, w)) = fun t : ℝ => t • ν + w.val := by
          funext t; exact h_e'_symm t w
        rw [h_eq]
        have h : HasDerivAt (fun t : ℝ => t • ν + w.val) ν t := by
          simpa using hasDerivAt_id t |>.smul_const ν |>.add_const w.val
        exact h
      have hG_fd : HasFDerivAt ψ (fderiv ℝ ψ (e'.symm (t, w))) (e'.symm (t, w)) :=
        h_diff.hasFDerivAt
      exact hG_fd.comp_hasDerivAt t h_line
    have h_deriv : ∀ t, deriv f_w t = fderiv ℝ ψ (e'.symm (t, w)) ν := by
      intro t
      exact (h_fd t).deriv
    have h_supp : HasCompactSupport f_w := by
      let g : ℝ → E n := fun t => t • ν + w.val
      have hg_isom : Isometry g := by
        apply Isometry.of_dist_eq
        intro x y
        have h1 : g x - g y = (x - y) • ν := by
          dsimp only [g]
          have h : x • ν + w.val - (y • ν + w.val) = (x - y) • ν := by
            rw [sub_smul] <;> abel
          exact h
        have h_main : dist (g x) (g y) = dist x y := by
          rw [dist_eq_norm, h1, norm_smul, dist_eq_norm]
          have h2 : ‖(x - y : ℝ)‖ = |x - y| := by exact Real.norm_eq_abs (x - y)
          rw [h2, hν_unit] <;> ring
        exact h_main
      have h1 : Function.support f_w ⊆ g ⁻¹' (tsupport ψ) := by
        intro t ht
        have h2 : f_w t ≠ 0 := by simpa [Function.mem_support] using ht
        have h3 : g t ∈ Function.support ψ := by
          have h_eq : g t = e'.symm (t, w) := by
            simp [g, h_e'_symm] <;> rfl
          rw [h_eq]
          simpa [f_w, Function.mem_support] using h2
        exact subset_closure h3
      have h5 : Bornology.IsBounded (tsupport ψ) := hψ_supp.isCompact.isBounded
      have h6 : Bornology.IsBounded (g ⁻¹' (tsupport ψ)) := by
        by_cases h_empty : (g ⁻¹' (tsupport ψ)).Nonempty
        · rcases h_empty with ⟨x0, hx0⟩
          have h_bdd : ∃ C, ∀ y ∈ tsupport ψ, dist y (g x0) ≤ C := by exact (isBounded_iff_subset_closedBall (g x0)).mp h5
          rcases h_bdd with ⟨C, hC⟩
          have h_main : ∀ x ∈ g ⁻¹' (tsupport ψ), dist x x0 ≤ C := by
            intro x hx
            have h63 : g x ∈ tsupport ψ := hx
            have h64 : dist (g x) (g x0) ≤ C := hC (g x) h63
            have h65 : dist x x0 = dist (g x) (g x0) := (hg_isom.dist_eq x x0).symm
            rw [h65]; exact h64
          have h_sub : g ⁻¹' (tsupport ψ) ⊆ Metric.closedBall x0 C := by
            intro x hx
            exact h_main x hx
          have h_bdd_ball : Bornology.IsBounded (Metric.closedBall x0 C) := by exact isBounded_closedBall
          exact h_bdd_ball.subset h_sub
        · have h_empty' : g ⁻¹' (tsupport ψ) = ∅ := by
            simpa [Set.not_nonempty_iff_eq_empty] using h_empty
          rw [h_empty']
          exact Bornology.isBounded_empty
      have h7 : Bornology.IsBounded (Function.support f_w) :=
        Bornology.IsBounded.subset h6 h1
      have h8 : Bornology.IsBounded (tsupport f_w) := h7.closure
      have h9 : IsClosed (tsupport f_w) := isClosed_closure
      have h10 : IsCompact (tsupport f_w) :=
        Metric.isCompact_of_isClosed_isBounded h9 h8
      exact h10
    have h_cd : ContDiff ℝ 1 f_w := by
      let g : ℝ → E n := fun t => t • ν + w.val
      have h1 : ContDiff ℝ 1 ψ := hψ_smooth.of_le (by norm_num)
      have hg : ContDiff ℝ 1 g := by
        have h2 : ContDiff ℝ 1 (fun t : ℝ => t • ν) := by
          have h : ContDiff ℝ ⊤ (fun t : ℝ => t • ν) := contDiff_id.smul_const ν
          exact h.of_le le_top
        have h3 : ContDiff ℝ 1 (fun (_ : ℝ) => w.val) := by
          have h : ContDiff ℝ ⊤ (fun (_ : ℝ) => w.val) := contDiff_const
          exact h.of_le le_top
        exact h2.add h3
      have h_eq : g = fun t : ℝ => e'.symm (t, w) := by
        funext t
        have h : g t = e'.symm (t, w) := by
          simp [g]
          exact (h_e'_symm t w).symm
        exact h
      have h_fw : f_w = ψ ∘ g := by
        funext t; simp [f_w, g, h_e'_symm] <;> rfl
      rw [h_fw]
      exact h1.comp hg
    have h4 : ∫ t in Set.Iic (0 : ℝ), deriv f_w t = f_w 0 :=
      h_supp.integral_Iic_deriv_eq h_cd 0
    have h5 : ∫ t in Set.Iio (0 : ℝ), deriv f_w t = ∫ t in Set.Iic (0 : ℝ), deriv f_w t := by
      have h_sub : Set.Iio (0 : ℝ) ⊆ Set.Iic (0 : ℝ) := by
        intro x hx
        have h_x_lt : x < 0 := by simpa [Set.mem_Iio] using hx
        exact le_of_lt h_x_lt
      have h_null : volume ((Set.Iic (0 : ℝ)) \ Set.Iio (0 : ℝ)) = 0 := by
        have h : (Set.Iic (0 : ℝ)) \ Set.Iio (0 : ℝ) = {0} := by
          ext x; simp [Set.mem_Iic, Set.mem_Iio] <;> constructor <;> intro h <;> tauto
        rw [h] <;> simp
      exact Eq.symm integral_Iic_eq_integral_Iio
    have h7 : ∫ t in Set.Iio (0 : ℝ), F (t, w) = ∫ t in Set.Iio (0 : ℝ), deriv f_w t := by
      apply integral_congr_ae
      filter_upwards with t
      exact (h_deriv t).symm
    rw [h7, h5, h4]
    <;> simp [f_w, h_e'_symm]
    <;> abel

  have h4 : ∫ w : Pν, (∫ t in Set.Iio (0 : ℝ), F (t, w)) = ∫ w : Pν, ψ (w.val) := by
    apply integral_congr_ae
    filter_upwards with w
    exact h3 w

  rw [h4]

  -- Step 7: Map back to hyperplane
  let i : Pν → E n := Subtype.val
  have hi_inj : Function.Injective i := Subtype.coe_injective
  have hi_cont : Continuous i := continuous_subtype_val
  have hi_emb : MeasurableEmbedding i :=
    hi_cont.measurableEmbedding hi_inj

  have h_finrank : Module.finrank ℝ Pν = n - 1 := by
    have h1 : Module.finrank ℝ (E n) = n := by simp
    have hν_ne_zero : ν ≠ 0 := by
      intro h; rw [h] at hν_unit; simp at hν_unit <;> linarith
    have h2 : Module.finrank ℝ s = 1 := finrank_span_singleton hν_ne_zero
    have h3 : Module.finrank ℝ s + Module.finrank ℝ Pν = Module.finrank ℝ (E n) :=
      Submodule.finrank_add_finrank_orthogonal s
    omega
  have h_vol_eq : (μHE[Module.finrank ℝ Pν] : Measure Pν) = volume :=
    InnerProductSpace.euclideanHausdorffMeasure_eq_volume
  have h_μhe_eq : (μHE[n - 1] : Measure Pν) = volume := by
    have h4 : n - 1 = Module.finrank ℝ Pν := by omega
    rw [h4]
    exact h_vol_eq
  have h_goal1 : ∫ w : Pν, ψ (w.val) = ∫ w : Pν, ψ (w.val) ∂μHE[n - 1] := by
    rw [←h_μhe_eq] <;> rfl
  rw [h_goal1]

  have hPν_set : (Pν : Set (E n)) = {z : E n | inner ℝ z ν = 0} := by
    ext z
    simp only [Pν, Submodule.mem_orthogonal, Set.mem_setOf_eq]
    constructor
    · intro h
      have h10 : inner ℝ ν z = 0 := h ν (Submodule.mem_span_singleton.mpr ⟨1, by simp⟩)
      have h11 : inner ℝ z ν = inner ℝ ν z := by exact real_inner_comm ν z
      rw [h11]
      exact h10
    · intro h
      intro y hy
      rcases Submodule.mem_span_singleton.mp hy with ⟨c, rfl⟩
      have h10 : inner ℝ z ν = 0 := h
      have h11 : inner ℝ ν z = 0 := by
        have h12 : inner ℝ ν z = inner ℝ z ν := by exact real_inner_comm z ν
        rw [h12]; exact h10
      have h13 : inner ℝ (c • ν) z = c * inner ℝ ν z := by
        rw [inner_smul_left] <;> rfl
      rw [h13, h11] <;> ring

  have hi_isom : Isometry i := by
    intro x y
    simp [i, dist_eq_norm] <;> rfl
  have h_map : Measure.map i (μHE[n - 1]) = (μHE[n - 1]).restrict (Pν : Set (E n)) := by
    have h1 : Measure.map i (μHE[n - 1]) = (μHE[n - 1]).restrict (Set.range i) :=
      hi_isom.map_euclideanHausdorffMeasure
    rw [h1]
    have h2 : Set.range i = (Pν : Set (E n)) := by
      ext x
      simp [i, Subtype.range_val]
      <;> rfl
    rw [h2]

  have h_int : ∫ w : Pν, ψ (w.val) ∂μHE[n - 1] =
      ∫ z : E n, ψ z ∂(Measure.map i (μHE[n - 1])) := by
    exact (hi_emb.integral_map (g := ψ)).symm

  rw [h_int, h_map]
  have h_restrict : ∫ z : E n, ψ z ∂(μHE[n - 1].restrict (Pν : Set (E n))) =
      ∫ z in (Pν : Set (E n)), ψ z ∂μHE[n - 1] := by
    rfl
  rw [h_restrict, hPν_set] <;> rfl

/-- **Step 3: LHS approximation by μ-integral**.

Given upper density bound and Lebesgue differentiation of the normal at x,
`∫ ψ((y-x)/r) (inner(ν,ν_U(y)) - 1) dμ(y) = o(r^{n-1})`. -/
lemma lhs_normal_average
    {U : Set (E n)} (hfin : perimeter U < ⊤)
    (x : E n) (ν : E n) (hν_unit : ‖ν‖ = 1)
    (hνx : measureTheoreticNormal U x = ν)
    (ψ : E n → ℝ) (hψ_smooth : ContDiff ℝ ∞ ψ) (hψ_supp : HasCompactSupport ψ)
    (h_upper : ∃ (C : ℝ) (r0 : ℝ), 0 < C ∧ 0 < r0 ∧
      ∀ r, 0 < r → r < r0 →
        perimeterMeasure U (closedBall x r) ≤ ENNReal.ofReal (C * r ^ (n - 1)))
    (h_leb : ∀ (R : ℝ), 0 < R →
      Tendsto (fun r : ℝ =>
        (∫ y in closedBall x (R * r), |inner ℝ ν (measureTheoreticNormal U y) - 1| ∂(perimeterMeasure U)) /
          (perimeterMeasure U (closedBall x (R * r))).toReal)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) :
    Tendsto (fun r : ℝ =>
      (∫ y, ψ ((1 / r) • (y - x)) * (inner ℝ ν (measureTheoreticNormal U y) - 1) ∂(perimeterMeasure U)) / r ^ (n - 1))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  let μ := perimeterMeasure U
  let f : E n → E n := measureTheoreticNormal U
  let g : E n → ℝ := fun y => inner ℝ ν (f y) - 1
  let η : ℝ → E n → ℝ := fun r y => ψ ((1 / r) • (y - x))
  have hμ_fin : μ Set.univ < ⊤ := by
    rw [← perimeter_eq_variation U hfin] <;> exact hfin
  letI : IsFiniteMeasure μ := ⟨hμ_fin⟩
  have hf_norm_one : ∀ᵐ y ∂μ, ‖f y‖ = 1 := norm_measureTheoreticNormal_eq_one hfin
  have hf_meas : Measurable f := measureTheoreticNormal_measurable hfin
  have hg_meas : Measurable g := by fun_prop
  have hg_bound : ∀ᵐ y ∂μ, |g y| ≤ 2 := by
    filter_upwards [hf_norm_one] with y hy
    have h1 : |inner ℝ ν (f y)| ≤ ‖ν‖ * ‖f y‖ := by exact abs_real_inner_le_norm ν (f y)
    have h2 : |inner ℝ ν (f y)| ≤ 1 := by
      calc |inner ℝ ν (f y)|
        ≤ ‖ν‖ * ‖f y‖ := by exact abs_real_inner_le_norm ν (f y)
      _ = 1 * 1 := by rw [hν_unit, hy]
      _ = 1 := by norm_num
    have h3 : |g y| ≤ |inner ℝ ν (f y)| + 1 := by
      simpa [g] using abs_sub (inner ℝ ν (f y)) 1
    linarith
  have hg_int : Integrable g μ := by
    have h1 : ∀ᵐ y ∂μ, ‖g y‖ ≤ 2 := by
      filter_upwards [hg_bound] with y hy
      simpa [Real.norm_eq_abs] using hy
    exact Integrable.of_bound hg_meas.aestronglyMeasurable 2 h1
  rcases h_upper with ⟨C, r0, hC_pos, hr0_pos, h_upper_bound⟩
  have hK_bdd : Bornology.IsBounded (tsupport ψ) := hψ_supp.isCompact.isBounded
  rcases hK_bdd.subset_ball (0 : E n) with ⟨R0, hR0⟩
  let R : ℝ := max R0 1
  have hR_pos : 0 < R := by positivity
  have hK_ball : tsupport ψ ⊆ ball (0 : E n) R := by
    intro z hz
    have h2 : dist z 0 < R0 := hR0 hz
    have h3 : R0 ≤ R := le_max_left R0 1
    have h4 : dist z 0 < R := by linarith
    exact h4
  have h_supp : ∀ (r : ℝ), 0 < r → ∀ y, y ∉ ball x (R * r) → η r y = 0 := by
    intro r hr y hy
    have h_pos : 0 < 1 / r := by positivity
    have h1 : dist ((1 / r) • (y - x)) 0 ≥ R := by
      have h2 : dist ((1 / r) • (y - x)) 0 = (1 / r) * dist y x := by
        calc dist ((1 / r) • (y - x)) 0
          = ‖(1 / r) • (y - x)‖ := by simp
        _ = (1 / r) * ‖y - x‖ := by
          rw [norm_smul]
          have h_abs : ‖(1 / r)‖ = 1 / r := by
            have h : ‖(1 / r)‖ = |1 / r| := by exact Real.norm_eq_abs (1 / r)
            rw [h, abs_of_pos h_pos]
          rw [h_abs] <;> ring
        _ = (1 / r) * dist y x := by rw [dist_eq_norm]
      rw [h2]
      have h3 : dist y x ≥ R * r := by simpa [ball] using hy
      have h4 : (1 / r) * dist y x ≥ (1 / r) * (R * r) := by gcongr
      have h5 : (1 / r) * (R * r) = R := by field_simp [hr.ne'] <;> ring
      linarith
    have h5 : (1 / r) • (y - x) ∉ tsupport ψ := by
      intro h6
      have h7 : (1 / r) • (y - x) ∈ ball (0 : E n) R := hK_ball h6
      have h8 : ‖(1 / r) • (y - x)‖ < R := by simpa [ball] using h7
      have h9 : dist ((1 / r) • (y - x)) 0 < R := by simpa [dist_zero_right] using h8
      linarith
    have h6 : ψ ((1 / r) • (y - x)) = 0 := by
      have h7 : (1 / r) • (y - x) ∉ Function.support ψ := fun h8 => h5 (subset_closure h8)
      simpa [Function.mem_support] using h7
    exact h6
  have hψ_bdd : ∃ (Cψ : ℝ), 0 < Cψ ∧ ∀ z, |ψ z| ≤ Cψ := by
    have h1 : BddAbove (Set.image (fun z => |ψ z|) (tsupport ψ)) :=
      hψ_supp.isCompact.bddAbove_image (hψ_smooth.continuous.norm.continuousOn)
    rcases h1 with ⟨Cψ, hCψ⟩
    have h2 : ∀ z ∈ tsupport ψ, |ψ z| ≤ Cψ := by
      intro z hz
      have h3 : |ψ z| ∈ Set.image (fun z => |ψ z|) (tsupport ψ) := ⟨z, hz, rfl⟩
      exact hCψ h3
    refine ⟨max Cψ 1, by positivity, fun z => ?_⟩
    by_cases hz : z ∈ tsupport ψ
    · have h4 : |ψ z| ≤ Cψ := h2 z hz
      have h5 : Cψ ≤ max Cψ 1 := le_max_left Cψ 1
      linarith
    · have h6 : ψ z = 0 := by
        have h7 : z ∉ Function.support ψ := fun h8 => hz (subset_closure h8)
        simpa [Function.mem_support] using h7
      rw [h6]; simpa using by positivity
  rcases hψ_bdd with ⟨Cψ, hCψ_pos, hCψ⟩
  let A : ℝ → ℝ := fun r => ∫ y in closedBall x (R * r), |g y| ∂μ
  let B : ℝ → ℝ := fun r => (μ (closedBall x (R * r))).toReal
  let D : ℝ → ℝ := fun r => A r / B r
  let F : ℝ → ℝ := fun r => (∫ y, η r y * g y ∂μ) / r ^ (n - 1)
  have hD_tendsto : Tendsto D (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := h_leb R hR_pos
  have h_upper_R : ∀ r, 0 < r → r < r0 / R →
      B r ≤ C * R ^ (n - 1) * r ^ (n - 1) := by
    intro r hr hrl
    have h_Rr_pos : 0 < R * r := mul_pos hR_pos hr
    have h_Rr_lt : R * r < r0 := by
      calc R * r < R * (r0 / R) := by gcongr
        _ = r0 := by field_simp [hR_pos.ne'] <;> ring
    have h9 : μ (closedBall x (R * r)) ≤ ENNReal.ofReal (C * (R * r) ^ (n - 1)) :=
      h_upper_bound (R * r) h_Rr_pos h_Rr_lt
    have h_ne : μ (closedBall x (R * r)) ≠ ⊤ := by
      have h : μ (closedBall x (R * r)) ≤ μ Set.univ := measure_mono (subset_univ _)
      exact (h.trans_lt hμ_fin).ne
    have h_b_ne : ENNReal.ofReal (C * (R * r) ^ (n - 1)) ≠ ⊤ := ENNReal.ofReal_lt_top.ne
    have h10 : (μ (closedBall x (R * r))).toReal ≤ (ENNReal.ofReal (C * (R * r) ^ (n - 1))).toReal :=
      (ENNReal.toReal_le_toReal h_ne h_b_ne).mpr h9
    have h11 : (ENNReal.ofReal (C * (R * r) ^ (n - 1))).toReal = C * (R * r) ^ (n - 1) := by
      rw [ENNReal.toReal_ofReal (by positivity)]
    rw [h11] at h10
    have h12 : C * (R * r) ^ (n - 1) = C * R ^ (n - 1) * r ^ (n - 1) := by ring
    rw [h12] at h10; exact h10
  have h_small : ∀ᶠ (r : ℝ) in nhdsWithin 0 (Set.Ioi 0), r < r0 / R := by
    have h1 : 0 < r0 / R := by positivity
    have h2 : Set.Iio (r0 / R) ∈ nhds (0 : ℝ) := Iio_mem_nhds h1
    exact mem_nhdsWithin_of_mem_nhds h2
  have hA_eq : ∀ r, A r = D r * B r := by
    intro r
    by_cases hB : B r = 0
    · have h_null : μ (closedBall x (R * r)) = 0 := by
        have h14 : (μ (closedBall x (R * r))).toReal = 0 := hB
        have h15 : μ (closedBall x (R * r)) = 0 ∨ μ (closedBall x (R * r)) = ⊤ := by
          simpa [ENNReal.toReal_eq_zero_iff] using h14
        have h_ne : μ (closedBall x (R * r)) ≠ ⊤ := by
          have h : μ (closedBall x (R * r)) ≤ μ Set.univ := measure_mono (subset_univ _)
          exact (h.trans_lt hμ_fin).ne
        exact h15.resolve_right h_ne
      have hA : A r = 0 := by
        have h_int : ∫ y in closedBall x (R * r), |g y| ∂μ = 0 := by
          rw [setIntegral_measure_zero (fun y => |g y|) h_null]
        simpa [A] using h_int
      rw [hA, hB] <;> ring
    · have hD : D r = A r / B r := by rfl
      rw [hD]
      field_simp [hB] <;> ring
  have h_main : ∀ (r : ℝ), 0 < r → r < r0 / R →
      |F r| ≤ Cψ * |D r| * (B r / r ^ (n - 1)) := by
    intro r hr hrl
    have hη_cont : Continuous (η r) := by fun_prop
    have hη_meas : AEStronglyMeasurable (η r) μ := hη_cont.aestronglyMeasurable
    have hη_bound : ∀ᵐ y ∂μ, ‖η r y‖ ≤ Cψ := by
      filter_upwards with y
      have h : |η r y| ≤ Cψ := hCψ ((1 / r) • (y - x))
      simpa [Real.norm_eq_abs] using h
    have h_prod_int : Integrable (fun y => η r y * g y) μ :=
      hg_int.bdd_mul hη_meas hη_bound
    have h1 : (∫ y, η r y * g y ∂μ) = ∫ y in ball x (R * r), η r y * g y ∂μ := by
      rw [← integral_indicator isOpen_ball.measurableSet]
      apply integral_congr_ae
      filter_upwards with y
      by_cases hy : y ∈ ball x (R * r)
      · simp [hy, Set.indicator]
      · have h2 : η r y = 0 := h_supp r hr y hy
        have h4 : η r y * g y = 0 := by rw [h2]; ring
        have h3 : Set.indicator (ball x (R * r)) (fun y => η r y * g y) y = 0 := by
          simp [Set.indicator, hy]
        rw [h4, h3]
    have hF : F r = (∫ y in ball x (R * r), η r y * g y ∂μ) / r ^ (n - 1) := by
      simp [F, h1]
    rw [hF]
    let hball := ball x (R * r)
    have h_ball_meas : MeasurableSet hball := isOpen_ball.measurableSet
    have h2 : |∫ y in hball, η r y * g y ∂μ| ≤
        ∫ y in hball, |η r y * g y| ∂μ := by
      let ind : E n → ℝ := Set.indicator hball (fun y => η r y * g y)
      have h_eq1 : ∫ y in hball, η r y * g y ∂μ = ∫ y, ind y ∂μ := by
        rw [integral_indicator h_ball_meas] <;> rfl
      have h_abs : ∀ y, |ind y| = Set.indicator hball (fun y => |η r y * g y|) y := by
        intro y
        by_cases hy : y ∈ hball
        · simp [ind, Set.indicator, hy]
        · simp [ind, Set.indicator, hy]
      have h_eq21 : ∫ y in hball, |η r y * g y| ∂μ = ∫ y, Set.indicator hball (fun y => |η r y * g y|) y ∂μ := by
        rw [integral_indicator h_ball_meas]
      have h_eq2 : ∫ y in hball, |η r y * g y| ∂μ = ∫ y, |ind y| ∂μ := by
        rw [h_eq21]
        apply integral_congr_ae
        filter_upwards with y
        exact (h_abs y).symm
      rw [h_eq1, h_eq2]
      exact abs_integral_le_integral_abs
    have h31 : ∀ y ∈ hball, |η r y * g y| ≤ Cψ * |g y| := by
      intro y _
      have h4 : |η r y| ≤ Cψ := hCψ ((1 / r) • (y - x))
      have h5 : |η r y * g y| = |η r y| * |g y| := by rw [abs_mul]
      rw [h5]
      exact mul_le_mul_of_nonneg_right h4 (abs_nonneg _)
    let f_abs : E n → ℝ := Set.indicator hball (fun y => |η r y * g y|)
    let g_C : E n → ℝ := Set.indicator hball (fun y => Cψ * |g y|)
    have h_f_abs_int : Integrable f_abs μ :=
      (integrable_indicator_iff h_ball_meas).mpr h_prod_int.abs.integrableOn
    have h_g_abs_int : Integrable (fun y => |g y|) μ := by exact Integrable.abs hg_int
    have h_Cg : Integrable (fun y => Cψ * |g y|) μ := by
      exact Integrable.const_mul h_g_abs_int Cψ
    have h_g_C_int : Integrable g_C μ :=
      (integrable_indicator_iff h_ball_meas).mpr h_Cg.integrableOn
    have h_ineq : ∀ z, f_abs z ≤ g_C z := by
      intro z
      by_cases hz : z ∈ hball
      · have h7 : f_abs z = |η r z * g z| := by simp [f_abs, hz]
        have h8 : g_C z = Cψ * |g z| := by simp [g_C, hz]
        rw [h7, h8]
        exact h31 z hz
      · have h7 : f_abs z = 0 := by simp [f_abs, hz]
        have h8 : g_C z = 0 := by simp [g_C, hz]
        rw [h7, h8] <;> norm_num
    have h_integral_ineq : ∫ z, f_abs z ∂μ ≤ ∫ z, g_C z ∂μ :=
      integral_mono h_f_abs_int h_g_C_int h_ineq
    have h_eq1 : ∫ z, f_abs z ∂μ = ∫ y in hball, |η r y * g y| ∂μ := by
      rw [integral_indicator h_ball_meas] <;> rfl
    have h_eq2 : ∫ z, g_C z ∂μ = ∫ y in hball, Cψ * |g y| ∂μ := by
      rw [integral_indicator h_ball_meas] <;> rfl
    have h5 : g_C = fun z => Cψ * Set.indicator hball (fun y => |g y|) z := by
      funext z
      by_cases hz : z ∈ hball <;> simp [g_C, Set.indicator, hz] <;> ring
    have h_const_mul : ∫ z, g_C z ∂μ = Cψ * ∫ z, Set.indicator hball (fun y => |g y|) z ∂μ := by
      rw [h5, integral_const_mul]
    have h6 : ∫ z, Set.indicator hball (fun y => |g y|) z ∂μ = ∫ y in hball, |g y| ∂μ := by
      rw [integral_indicator h_ball_meas] <;> rfl
    have h_eq3 : ∫ y in hball, Cψ * |g y| ∂μ = Cψ * ∫ y in hball, |g y| ∂μ := by
      have h7 : ∫ z, g_C z ∂μ = Cψ * ∫ y in hball, |g y| ∂μ := by
        rw [h_const_mul, h6]
      rw [←h_eq2]
      exact h7
    have h3 : ∫ y in hball, |η r y * g y| ∂μ ≤ Cψ * ∫ y in hball, |g y| ∂μ := by
      rw [h_eq1, h_eq2, h_eq3] at h_integral_ineq
      exact h_integral_ineq
    have h4 : ∫ y in ball x (R * r), |g y| ∂μ ≤ A r := by
      have hfi : IntegrableOn (fun y => |g y|) (closedBall x (R * r)) μ :=
        hg_int.abs.integrableOn
      have hnonneg : 0 ≤ᵐ[μ.restrict (closedBall x (R * r))] (fun y => |g y|) := by
        filter_upwards with y; exact abs_nonneg _
      have hsub : ball x (R * r) ≤ᵐ[μ] closedBall x (R * r) := by
        filter_upwards with y hy; exact ball_subset_closedBall hy
      exact setIntegral_mono_set hfi hnonneg hsub
    have h5 : |∫ y in ball x (R * r), η r y * g y ∂μ| ≤ Cψ * A r := by
      calc _ ≤ ∫ y in ball x (R * r), |η r y * g y| ∂μ := h2
        _ ≤ Cψ * ∫ y in ball x (R * r), |g y| ∂μ := h3
        _ ≤ Cψ * A r := by gcongr
    have h13 : 0 < r ^ (n - 1) := pow_pos hr (n - 1)
    have h14 : |F r| ≤ Cψ * A r / r ^ (n - 1) := by
      have h141 : |F r| = |∫ y in ball x (R * r), η r y * g y ∂μ| / r ^ (n - 1) := by
        have hF : F r = (∫ y, η r y * g y ∂μ) / r ^ (n - 1) := by rfl
        rw [hF, abs_div, abs_of_pos h13, h1]
        <;> ring
      rw [h141]
      gcongr
    rw [hA_eq r] at h14
    have h15 : 0 ≤ Cψ := by linarith
    have h16 : 0 ≤ B r := by positivity
    have h17 : 0 ≤ r ^ (n - 1) := by positivity
    have hD_nonneg : 0 ≤ D r := by
      have hA_nonneg : 0 ≤ A r := by positivity
      have hB_nonneg : 0 ≤ B r := by positivity
      exact div_nonneg hA_nonneg hB_nonneg
    have h18 : Cψ * (D r * B r) / r ^ (n - 1) = Cψ * |D r| * (B r / r ^ (n - 1)) := by
      have h19 : |D r| = D r := abs_of_nonneg hD_nonneg
      rw [h19]
      <;> field_simp [h13.ne'] <;> ring
    rw [h18] at h14
    rw [hF] at h14
    exact h14
  have h_eventually : ∀ᶠ (r : ℝ) in nhdsWithin 0 (Set.Ioi 0),
      |F r| ≤ Cψ * (C * R ^ (n - 1)) * |D r| := by
    filter_upwards [h_small, self_mem_nhdsWithin] with r hrl hr
    have h16 := h_main r hr hrl
    have h17 : B r / r ^ (n - 1) ≤ C * R ^ (n - 1) := by
      have h_pos' : 0 < r ^ (n - 1) := pow_pos hr (n - 1)
      have h : B r ≤ C * R ^ (n - 1) * r ^ (n - 1) := h_upper_R r hr hrl
      calc B r / r ^ (n - 1)
        ≤ (C * R ^ (n - 1) * r ^ (n - 1)) / r ^ (n - 1) := by gcongr
      _ = C * R ^ (n - 1) := by field_simp [h_pos'.ne'] <;> ring
    have h18 : 0 ≤ Cψ * |D r| := by positivity
    calc |F r|
      ≤ Cψ * |D r| * (B r / r ^ (n - 1)) := h16
    _ ≤ Cψ * |D r| * (C * R ^ (n - 1)) := by gcongr
    _ = Cψ * (C * R ^ (n - 1)) * |D r| := by ring
  have h19 : Tendsto (fun r => |D r|) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa [abs_zero] using hD_tendsto.abs
  have h20 : Tendsto (fun r : ℝ => Cψ * (C * R ^ (n - 1)) * |D r|)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa [mul_zero] using h19.const_mul (Cψ * (C * R ^ (n - 1)))
  have h21 : ∀ᶠ (r : ℝ) in nhdsWithin 0 (Set.Ioi 0), 0 ≤ |F r| := by
    filter_upwards with r; exact abs_nonneg _
  have h22 : Tendsto (fun r => |F r|) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    squeeze_zero' h21 h_eventually h20
  have h23 : Tendsto F (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h24 : ∀ ε > 0, ∀ᶠ (r : ℝ) in nhdsWithin 0 (Set.Ioi 0), |F r| < ε := by
      intro ε hε
      have h25 := h22 (Metric.ball_mem_nhds 0 hε)
      filter_upwards [h25] with r hr
      simpa [Metric.mem_ball] using hr
    simpa [Metric.tendsto_nhds] using h24
  exact h23

/-- **Hyperplane-ball Hausdorff measure finiteness**.
The intersection of a hyperplane through the origin with a ball has finite
`(n-1)`-dimensional Hausdorff measure. -/
lemma hyperplane_ball_finite {n : ℕ} (ν : E n) (hν_unit : ‖ν‖ = 1)
    (R : ℝ) (hR : 0 < R) :
    μHE[n - 1] ({z : E n | inner ℝ z ν = 0} ∩ ball (0 : E n) R) < ⊤ := by
  let Pν : Submodule ℝ (E n) := (ℝ ∙ ν)ᗮ
  let s : Set Pν := {w | w.val ∈ ball (0 : E n) R}
  have h1 : (Subtype.val '' s) = {z : E n | inner ℝ z ν = 0} ∩ ball (0 : E n) R := by
    ext z
    simp only [s, Set.mem_image, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨w, hw, rfl⟩
      have h_prop : w.val ∈ (ℝ ∙ ν)ᗮ := w.property
      have h_inner : inner ℝ w.val ν = 0 := by
        rw [Submodule.mem_orthogonal_singleton_iff_inner_left] at h_prop
        exact h_prop
      exact ⟨h_inner, hw⟩
    · rintro ⟨hz, hball⟩
      have hP : z ∈ (ℝ ∙ ν)ᗮ := by
        rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
        exact hz
      refine ⟨⟨z, hP⟩, hball, rfl⟩
  have h2 : μHE[n - 1] (Subtype.val '' s) = μHE[n - 1] s :=
    AffineSubspace.euclideanHausdorffMeasure_coe_image (n - 1) (Pν : AffineSubspace ℝ (E n)) s
  rw [←h1, h2]
  have h_finrank : Module.finrank ℝ Pν = n - 1 := by
    have h1 : Module.finrank ℝ (E n) = n := by simp
    have hν_ne_zero : ν ≠ 0 := by
      intro h; rw [h] at hν_unit; simp at hν_unit <;> linarith
    have h2 : Module.finrank ℝ (ℝ ∙ ν) = 1 :=
      finrank_span_singleton hν_ne_zero
    have h3 : Module.finrank ℝ (ℝ ∙ ν) + Module.finrank ℝ Pν = Module.finrank ℝ (E n) :=
      Submodule.finrank_add_finrank_orthogonal (ℝ ∙ ν)
    omega
  have h_vol_eq : (μHE[n - 1] : Measure Pν) = volume := by
    have h4 : n - 1 = Module.finrank ℝ Pν := by omega
    rw [h4]
    exact InnerProductSpace.euclideanHausdorffMeasure_eq_volume
  have h5 : s ⊆ closedBall (0 : Pν) R := by
    intro w hw
    have h6 : w.val ∈ ball (0 : E n) R := hw
    have h7 : ‖w.val‖ < R := by simpa [Metric.mem_ball] using h6
    have h8 : ‖w‖ < R := by simpa using h7
    have h9 : w ∈ closedBall (0 : Pν) R := by
      simpa [Metric.mem_closedBall] using h8.le
    exact h9
  have h_compact : IsCompact (closedBall (0 : Pν) R) := isCompact_closedBall _ _
  have h_fin : volume (closedBall (0 : Pν) R) < ⊤ := h_compact.measure_lt_top
  have h_fin' : μHE[n - 1] (closedBall (0 : Pν) R) < ⊤ := by
    rw [h_vol_eq]; exact h_fin
  exact (measure_mono h5).trans_lt h_fin'

/-- **Hyperplane-sphere Hausdorff measure nullity**.
The intersection of a hyperplane through the origin with the unit sphere has zero
`(n-1)`-dimensional Hausdorff measure. -/
lemma hyperplane_sphere_null {n : ℕ} (ν : E n) (hν_unit : ‖ν‖ = 1) :
    μHE[n - 1] ({z : E n | inner ℝ z ν = 0} ∩ sphere (0 : E n) 1) = 0 := by
  let Pν : Submodule ℝ (E n) := (ℝ ∙ ν)ᗮ
  let s : Set Pν := sphere (0 : Pν) 1
  have h1 : (Subtype.val '' s) = {z : E n | inner ℝ z ν = 0} ∩ sphere (0 : E n) 1 := by
    ext z
    simp only [s, Set.mem_image, Set.mem_inter_iff, Set.mem_setOf_eq, Metric.mem_sphere]
    constructor
    · rintro ⟨w, hw, rfl⟩
      have h_prop : w.val ∈ (ℝ ∙ ν)ᗮ := w.property
      have h_inner : inner ℝ w.val ν = 0 := by
        rw [Submodule.mem_orthogonal_singleton_iff_inner_left] at h_prop
        exact h_prop
      exact ⟨h_inner, by simpa using hw⟩
    · rintro ⟨hz, hsph⟩
      have hP : z ∈ (ℝ ∙ ν)ᗮ := by
        rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
        exact hz
      refine ⟨⟨z, hP⟩, by simpa using hsph, rfl⟩
  have h2 : μHE[n - 1] (Subtype.val '' s) = μHE[n - 1] s :=
    AffineSubspace.euclideanHausdorffMeasure_coe_image (n - 1) (Pν : AffineSubspace ℝ (E n)) s
  rw [←h1, h2]
  have h_finrank : Module.finrank ℝ Pν = n - 1 := by
    have h1 : Module.finrank ℝ (E n) = n := by simp
    have hν_ne_zero2 : ν ≠ 0 := by
      intro h; rw [h] at hν_unit; simp at hν_unit <;> linarith
    have h2 : Module.finrank ℝ (ℝ ∙ ν) = 1 :=
      finrank_span_singleton hν_ne_zero2
    have h3 : Module.finrank ℝ (ℝ ∙ ν) + Module.finrank ℝ Pν = Module.finrank ℝ (E n) :=
      Submodule.finrank_add_finrank_orthogonal (ℝ ∙ ν)
    omega
  have h_vol_eq : (μHE[n - 1] : Measure Pν) = volume := by
    have h4 : n - 1 = Module.finrank ℝ Pν := by omega
    rw [h4]
    exact InnerProductSpace.euclideanHausdorffMeasure_eq_volume
  have h3 : μHE[n - 1] (closedBall (0 : Pν) 1) = μHE[n - 1] (ball (0 : Pν) 1) := by
    rw [h_vol_eq]
    exact MeasureTheory.Measure.addHaar_unitClosedBall_eq_addHaar_unitBall volume
  have h4 : closedBall (0 : Pν) 1 = ball (0 : Pν) 1 ∪ sphere (0 : Pν) 1 := by
    ext y
    simp [Metric.mem_closedBall, Metric.mem_ball, Metric.mem_sphere]
    <;> constructor <;> intro h <;> linarith
  have h5 : Disjoint (ball (0 : Pν) 1) (sphere (0 : Pν) 1) := by
    rw [Set.disjoint_left]
    intro y h1 h2
    have h1' : ‖y‖ < 1 := by simpa [Metric.mem_ball] using h1
    have h2' : ‖y‖ = 1 := by simpa [Metric.mem_sphere] using h2
    linarith
  rw [h4] at h3
  have h_ball_meas : MeasurableSet (ball (0 : Pν) 1) := isOpen_ball.measurableSet
  have h_sphere_meas : MeasurableSet (sphere (0 : Pν) 1) := isClosed_sphere.measurableSet
  have h_union : μHE[n - 1] (ball (0 : Pν) 1 ∪ sphere (0 : Pν) 1) =
      μHE[n - 1] (ball (0 : Pν) 1) + μHE[n - 1] (sphere (0 : Pν) 1) :=
    measure_union h5 h_sphere_meas
  rw [h_union] at h3
  have h_ball_ne_top : μHE[n - 1] (ball (0 : Pν) 1) ≠ ⊤ := by
    have h_sub : ball (0 : Pν) 1 ⊆ closedBall (0 : Pν) 1 := ball_subset_closedBall
    have h_compact : IsCompact (closedBall (0 : Pν) 1) := isCompact_closedBall _ _
    have h' : volume (closedBall (0 : Pν) 1) < ⊤ := h_compact.measure_lt_top
    have h'' : μHE[n - 1] (closedBall (0 : Pν) 1) < ⊤ := by
      rw [h_vol_eq]; exact h'
    exact (measure_mono h_sub).trans_lt h'' |>.ne
  have h6 : μHE[n - 1] (sphere (0 : Pν) 1) = 0 := by
    have h_eq : μHE[n - 1] (ball (0 : Pν) 1) + μHE[n - 1] (sphere (0 : Pν) 1) = μHE[n - 1] (ball (0 : Pν) 1) := h3
    have h_eq3 : μHE[n - 1] (sphere (0 : Pν) 1) + μHE[n - 1] (ball (0 : Pν) 1) = 0 + μHE[n - 1] (ball (0 : Pν) 1) := by
      have h_comm : μHE[n - 1] (sphere (0 : Pν) 1) + μHE[n - 1] (ball (0 : Pν) 1) = μHE[n - 1] (ball (0 : Pν) 1) + μHE[n - 1] (sphere (0 : Pν) 1) := by
        apply add_comm
      rw [h_comm, h_eq, zero_add]
    have h7 : μHE[n - 1] (sphere (0 : Pν) 1) = 0 := (ENNReal.add_left_inj h_ball_ne_top).mp h_eq3
    exact h7
  exact h6

/-- **Helper**: A continuous, bounded function supported on a finite-measure set is integrable. -/
lemma integrable_bounded_finite_support {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α] {μ : Measure α} {f : α → ℝ} {s : Set α}
    (hs : MeasurableSet s) (hfin : μ s < ⊤) (hf_cont : Continuous f)
    (h_supp : ∀ x, x ∉ s → f x = 0) (C : ℝ) (h_bound : ∀ x, |f x| ≤ C) :
    Integrable f μ := by
  have h_f_meas : AEStronglyMeasurable f μ := hf_cont.aestronglyMeasurable
  have h_f_bound_s : ∀ᵐ x ∂μ.restrict s, ‖f x‖ ≤ C := by
    filter_upwards with x
    simpa [Real.norm_eq_abs] using h_bound x
  have h_int_on : IntegrableOn f s μ :=
    Measure.integrableOn_of_bounded hfin.ne h_f_meas h_f_bound_s
  have h_ind_int : Integrable (Set.indicator s f) μ :=
    (integrable_indicator_iff hs).mpr h_int_on
  have h_eq : Set.indicator s f = f := by
    funext x
    by_cases hx : x ∈ s
    · simp [hx, Set.indicator]
    · have hfx : f x = 0 := h_supp x hx
      simp [hx, hfx, Set.indicator]
  rw [←h_eq]
  exact h_ind_int

/-- **Step 4 (PELICAN): From test function convergence to ball density**.

If for every smooth compactly supported `ψ` with `0 ≤ ψ ≤ 1`:
`lim_{r→0} r^{1-n} ∫ ψ((y-x)/r) dμ(y) = ∫_{Pν} ψ dH^{n-1}`
and upper density `μ(B(x,r)) ≤ C r^{n-1}`,
then `lim_{r→0} μ(B(x,r)) / r^{n-1} = H^{n-1}(Pν ∩ B(0,1)) = ω_{n-1}`. -/
lemma test_functions_to_ball_density
    {U : Set (E n)} (x : E n) (ν : E n) (hν_unit : ‖ν‖ = 1)
    (μ : Measure (E n))
    (h_upper : ∃ (C : ℝ) (r0 : ℝ), 0 < C ∧ 0 < r0 ∧
      ∀ r, 0 < r → r < r0 → μ (closedBall x r) ≤ ENNReal.ofReal (C * r ^ (n - 1)))
    (h_test : ∀ (ψ : E n → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∀ z, 0 ≤ ψ z) →
      Tendsto (fun r : ℝ =>
        (∫ y, ψ ((1 / r) • (y - x)) ∂μ) / r ^ (n - 1))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (∫ z in {z : E n | inner ℝ z ν = 0}, ψ z ∂μHE[n - 1]))) :
    Tendsto (fun r : ℝ => (μ (ball x r)).toReal / r ^ (n - 1))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((μHE[n - 1] ({z : E n | inner ℝ z ν = 0} ∩ ball (0 : E n) 1)).toReal)) := by
  let l : Filter ℝ := nhdsWithin 0 (Set.Ioi 0)
  let f : ℝ → ℝ := fun r => (μ (ball x r)).toReal / r ^ (n - 1)
  let Pν : Set (E n) := {z | inner ℝ z ν = 0}
  let H : Measure (E n) := μHE[n - 1].restrict Pν
  let L : ℝ := (H (ball (0 : E n) 1)).toReal

  -- ε_k = 1/(k+2) ∈ (0,1), tends to 0
  let ε : ℕ → ℝ := fun k => (k + 2 : ℝ)⁻¹
  have hε_pos : ∀ k, 0 < ε k := by intro k; positivity
  have hε_lt_one : ∀ k, ε k < 1 := by
    intro k
    have h : (k + 2 : ℝ) > 1 := by linarith
    have h4 : (k + 2 : ℝ)⁻¹ < 1 := by
      calc (k + 2 : ℝ)⁻¹ < (1 : ℝ)⁻¹ := by gcongr
        _ = 1 := by norm_num
    exact h4
  have hε_tendsto : Tendsto ε atTop (nhds 0) := by
    have h1 : ∀ (M : ℝ), 0 < M → ∃ N : ℕ, ∀ k ≥ N, (k + 2 : ℝ)⁻¹ < M := by
      intro M hM
      refine ⟨Nat.ceil (M⁻¹) + 1, fun k hk => ?_⟩
      have h2 : (k : ℝ) ≥ Nat.ceil (M⁻¹) + 1 := by exact_mod_cast hk
      have h3 : (k + 2 : ℝ) > M⁻¹ := by linarith [Nat.le_ceil (M⁻¹)]
      have h4 : (k + 2 : ℝ)⁻¹ < M := by
        have h_pos1 : 0 < M⁻¹ := by positivity
        have h_pos2 : 0 < (k + 2 : ℝ) := by positivity
        have h5 : (k + 2 : ℝ)⁻¹ < (M⁻¹)⁻¹ := by gcongr
        have h6 : (M⁻¹)⁻¹ = M := by field_simp [hM.ne'] <;> ring
        rw [h6] at h5
        exact h5
      exact h4
    have h_main : ∀ δ > 0, ∃ N : ℕ, ∀ k ≥ N, |ε k - 0| < δ := by
      intro δ hδ
      rcases h1 δ hδ with ⟨N, hN⟩
      refine ⟨N, fun k hk => ?_⟩
      have h5 : ε k < δ := hN k hk
      have h6 : 0 < ε k := hε_pos k
      have h7 : |ε k - 0| = ε k := by
        have h8 : |ε k| = ε k := abs_of_pos h6
        simpa using h8
      rw [h7] <;> exact h5
    simpa [Metric.tendsto_atTop] using h_main
  have h1_pos : ∀ k, 0 < 1 - ε k := by intro k; linarith [hε_lt_one k]

  -- Lower and upper smooth approximations
  let ψ : ℕ → (E n → ℝ) := fun k => radialCutoff 0 (1 - ε k) (ε k)
  let φ : ℕ → (E n → ℝ) := fun k => radialCutoff 0 1 (ε k)

  have hψ_smooth : ∀ k, ContDiff ℝ ∞ (ψ k) := by
    intro k; have h := radialCutoff_contDiff (x₀ := (0 : E n)) (h1_pos k) (hε_pos k); simpa [ψ] using h
  have hφ_smooth : ∀ k, ContDiff ℝ ∞ (φ k) := by
    intro k; have h := radialCutoff_contDiff (x₀ := (0 : E n)) (show (0 : ℝ) < 1 by norm_num) (hε_pos k); simpa [φ] using h

  have hψ_zero_outside : ∀ k (y : E n), y ∉ ball (0 : E n) 1 → ψ k y = 0 := by
    intro k y hy
    have h_eq : (1 - ε k) + ε k = (1 : ℝ) := by ring
    have h : y ∉ ball (0 : E n) ((1 - ε k) + ε k) := by rw [h_eq]; exact hy
    exact radialCutoff_zero_of_not_mem_ball (h1_pos k) (hε_pos k) h

  have hφ_zero_outside : ∀ k (y : E n), y ∉ ball (0 : E n) 2 → φ k y = 0 := by
    intro k y hy
    have h2 : y ∉ ball (0 : E n) (1 + ε k) := by
      intro h3
      have h4 : dist y (0 : E n) < 1 + ε k := h3
      have h5 : dist y (0 : E n) < 2 := by linarith [hε_lt_one k]
      exact hy h5
    exact radialCutoff_zero_of_not_mem_ball (by norm_num) (hε_pos k) h2

  have hψ_support : ∀ k, HasCompactSupport (ψ k) := by
    intro k
    exact HasCompactSupport.intro (isCompact_closedBall 0 1)
      (fun y hy => hψ_zero_outside k y (fun h => hy (ball_subset_closedBall h)))
  have hφ_support : ∀ k, HasCompactSupport (φ k) := by
    intro k
    exact HasCompactSupport.intro (isCompact_closedBall 0 2)
      (fun y hy => hφ_zero_outside k y (fun h => hy (ball_subset_closedBall h)))

  have hψ_nonneg : ∀ k z, 0 ≤ ψ k z := by intro k z; exact (Perimeter.smoothStep_range).1
  have hφ_nonneg : ∀ k z, 0 ≤ φ k z := by intro k z; exact (Perimeter.smoothStep_range).1
  have hψ_le_one : ∀ k z, ψ k z ≤ 1 := by intro k z; exact (Perimeter.smoothStep_range).2
  have hφ_le_one : ∀ k z, φ k z ≤ 1 := by intro k z; exact (Perimeter.smoothStep_range).2

  have hψ_one : ∀ k y, y ∈ closedBall (0 : E n) (1 - ε k) → ψ k y = 1 := by
    intro k y hy; exact radialCutoff_one_of_mem_closedBall (h1_pos k) (hε_pos k) hy
  have hφ_one : ∀ k y, y ∈ closedBall (0 : E n) 1 → φ k y = 1 := by
    intro k y hy; exact radialCutoff_one_of_mem_closedBall (by norm_num) (hε_pos k) hy

  -- ψ_k ≤ 1_{ball 0 1} ≤ φ_k
  have hψ_le : ∀ k (z : E n), ψ k z ≤ Set.indicator (ball (0 : E n) 1) 1 z := by
    intro k z; by_cases h : z ∈ ball (0 : E n) 1
    · simp [h, hψ_le_one k z]
    · have h2 : ψ k z = 0 := hψ_zero_outside k z h; simp [h, h2]
  have h_le_φ : ∀ k (z : E n), Set.indicator (ball (0 : E n) 1) 1 z ≤ φ k z := by
    intro k z; by_cases h : z ∈ ball (0 : E n) 1
    · have h2 : z ∈ closedBall (0 : E n) 1 := ball_subset_closedBall h
      have h3 : φ k z = 1 := hφ_one k z h2; simp [h, h3]
    · have h4 : 0 ≤ φ k z := hφ_nonneg k z; simp [h, h4]

  -- Scaling map
  let scale : ℝ → (E n → E n) := fun r y => (1 / r) • (y - x)
  have h_scale_ball : ∀ (r : ℝ), 0 < r → ∀ (y : E n),
      scale r y ∈ ball (0 : E n) 1 ↔ y ∈ ball x r := by
    intro r hr y
    have h_pos : 0 < 1 / r := by positivity
    have h1 : ‖scale r y‖ = (1 / r) * ‖y - x‖ := by
      have h2 : ‖scale r y‖ = ‖(1 / r) • (y - x)‖ := by rfl
      rw [h2, norm_smul, Real.norm_eq_abs, abs_of_pos h_pos] <;> ring
    have h4 : scale r y ∈ ball (0 : E n) 1 ↔ ‖scale r y‖ < 1 := by
      simp [ball, dist_zero_right]
    have h5 : y ∈ ball x r ↔ ‖y - x‖ < r := by
      simp [ball, dist_eq_norm]
    rw [h4, h5, h1]
    constructor
    · intro h6
      have h7 : (1 / r) * ‖y - x‖ < 1 := h6
      have h8 : ‖y - x‖ < r := by
        calc ‖y - x‖
          = r * ((1 / r) * ‖y - x‖) := by field_simp [hr.ne'] <;> ring
        _ < r * 1 := by gcongr
        _ = r := by ring
      exact h8
    · intro h6
      calc (1 / r) * ‖y - x‖
        < (1 / r) * r := by gcongr
      _ = 1 := by field_simp [hr.ne'] <;> ring

  -- Local finiteness of μ from upper density
  rcases h_upper with ⟨C, r0, hC_pos, hr0_pos, h_upper_bound⟩
  have hfin_small : ∀ r, 0 < r → r < r0 → μ (ball x r) < ⊤ := by
    intro r hr_pos hr_lt
    have h : ball x r ⊆ closedBall x r := ball_subset_closedBall
    have h2 : μ (closedBall x r) ≤ ENNReal.ofReal (C * r ^ (n - 1)) := h_upper_bound r hr_pos hr_lt
    have h3 : μ (ball x r) ≤ μ (closedBall x r) := measure_mono h
    have h4 : μ (ball x r) < ⊤ := by
      calc μ (ball x r) ≤ μ (closedBall x r) := h3
        _ ≤ ENNReal.ofReal (C * r ^ (n - 1)) := h2
        _ < ⊤ := ENNReal.ofReal_lt_top
    exact h4

  have h_nhds : Set.Ioc (0 : ℝ) (r0 / 3) ∈ l := by
    have h1 : Set.Ioc (0 : ℝ) (r0 / 3) = Set.Ioi (0 : ℝ) ∩ Set.Iic (r0 / 3) := by
      ext r; simp [Set.mem_Ioc, Set.mem_Ioi, Set.mem_Iic] <;> tauto
    rw [h1]
    have h2 : 0 < r0 / 3 := by linarith
    exact inter_mem_nhdsWithin _ (Iic_mem_nhds h2)

  -- Continuity of scaled functions
  have hcont_scale : ∀ (r : ℝ), 0 < r → Continuous (scale r) := by
    intro r _
    change Continuous (fun y : E n => (1 / r) • (y - x))
    fun_prop

  -- Integral inequalities: ψ_k ≤ f(r) ≤ φ_k (scaled)
  have h_lower : ∀ k, ∀ᶠ r in l,
      (∫ y, (ψ k) (scale r y) ∂μ) / r ^ (n - 1) ≤ f r := by
    intro k
    filter_upwards [h_nhds] with r hr
    have hr_pos : 0 < r := hr.1
    have hr_le : r ≤ r0 / 3 := hr.2
    have hr_lt : r < r0 := by
      calc r ≤ r0 / 3 := hr_le
        _ < r0 := by have h3 : 0 < r0 := hr0_pos; linarith
    have hfin : μ (ball x r) < ⊤ := hfin_small r hr_pos hr_lt
    have h1 : ∀ y, (ψ k) (scale r y) ≤ Set.indicator (ball x r) 1 y := by
      intro y
      have h2 := h_scale_ball r hr_pos y
      have h3 := hψ_le k (scale r y)
      by_cases h4 : y ∈ ball x r
      · have h5 : scale r y ∈ ball (0 : E n) 1 := h2.mpr h4
        simpa [h4, h5] using h3
      · have h5 : scale r y ∉ ball (0 : E n) 1 := fun h6 => h4 (h2.mp h6)
        simpa [h4, h5] using h3
    have h_int1 : Integrable (fun y : E n => (ψ k) (scale r y)) μ :=
      integrable_bounded_finite_support isOpen_ball.measurableSet hfin
        ((hψ_smooth k).continuous.comp (hcont_scale r hr_pos))
        (fun y hy => hψ_zero_outside k (scale r y) ((h_scale_ball r hr_pos y).not.mpr hy))
        1 (fun y => by
          have h : 0 ≤ ψ k (scale r y) ∧ ψ k (scale r y) ≤ 1 := ⟨hψ_nonneg k _, hψ_le_one k _⟩
          exact abs_le.mpr ⟨by linarith, by linarith⟩)
    let ind : E n → ℝ := Set.indicator (ball x r) (fun _ => 1)
    have h_int2 : Integrable ind μ := by
      rw [integrable_indicator_iff isOpen_ball.measurableSet]
      have hC : ‖(1 : ℝ)‖ₑ ≠ ⊤ := by simp [ENorm.enorm] <;> norm_num
      exact MeasureTheory.integrableOn_const (hs := hfin.ne) (hC := hC)
    have h5 : ∫ y, ind y ∂μ = (μ (ball x r)).toReal := by
      have h_eq1 : ∫ y, ind y ∂μ = ∫ y in ball x r, (1 : ℝ) ∂μ := by
        rw [integral_indicator isOpen_ball.measurableSet] <;> rfl
      rw [h_eq1]
      have h_eq2 : ∫ y in ball x r, (1 : ℝ) ∂μ = (μ (ball x r)).toReal := by
        rw [MeasureTheory.setIntegral_const (1 : ℝ)]
        <;> simp [Measure.real, hfin.ne]
      exact h_eq2
    have h6 : ∫ y, (ψ k) (scale r y) ∂μ ≤ ∫ y, ind y ∂μ :=
      integral_mono h_int1 h_int2 h1
    have h7 : 0 < r ^ (n - 1) := by positivity
    rw [h5] at h6
    exact div_le_div_of_nonneg_right h6 (by positivity)

  have h_upper : ∀ k, ∀ᶠ r in l,
      f r ≤ (∫ y, (φ k) (scale r y) ∂μ) / r ^ (n - 1) := by
    intro k
    filter_upwards [h_nhds] with r hr
    have hr_pos : 0 < r := hr.1
    have hr_le : r ≤ r0 / 3 := hr.2
    have hr_lt : r < r0 := by
      calc r ≤ r0 / 3 := hr_le
        _ < r0 := by have h3 : 0 < r0 := hr0_pos; linarith
    have hfin : μ (ball x r) < ⊤ := hfin_small r hr_pos hr_lt
    have h1 : ∀ y, Set.indicator (ball x r) 1 y ≤ (φ k) (scale r y) := by
      intro y
      have h2 := h_scale_ball r hr_pos y
      have h3 := h_le_φ k (scale r y)
      by_cases h4 : y ∈ ball x r
      · have h5 : scale r y ∈ ball (0 : E n) 1 := h2.mpr h4
        simpa [h4, h5] using h3
      · have h6 : 0 ≤ φ k (scale r y) := hφ_nonneg k (scale r y)
        simpa [h4] using h6
    let ind2 : E n → ℝ := Set.indicator (ball x r) (fun _ => 1)
    have h_int1 : Integrable ind2 μ := by
      rw [integrable_indicator_iff isOpen_ball.measurableSet]
      have hC : ‖(1 : ℝ)‖ₑ ≠ ⊤ := by simp [ENorm.enorm] <;> norm_num
      exact MeasureTheory.integrableOn_const (hs := hfin.ne) (hC := hC)
    have h2r_pos : 0 < 2 * r := by positivity
    have h2r_lt : 2 * r < r0 := by linarith [hr.2]
    have hfin2 : μ (ball x (2 * r)) < ⊤ := hfin_small (2 * r) h2r_pos h2r_lt
    have h_scale_ball2 : ∀ (y : E n), scale r y ∈ ball (0 : E n) 2 ↔ y ∈ ball x (2 * r) := by
      intro y
      have h_pos : 0 < 1 / r := by positivity
      have h_eq : dist (scale r y) 0 = (1 / r) * dist y x := by
        have h1 : dist (scale r y) 0 = ‖scale r y‖ := by simp
        rw [h1]
        have h2 : ‖scale r y‖ = (1 / r) * ‖y - x‖ := by
          have h_scale_def : scale r y = (1 / r) • (y - x) := by rfl
          rw [h_scale_def, norm_smul]
          have h3 : ‖(1 / r : ℝ)‖ = 1 / r := by
            rw [Real.norm_eq_abs, abs_of_pos h_pos]
          rw [h3] <;> ring
        rw [h2, dist_eq_norm]
      have h4 : dist (scale r y) 0 < 2 ↔ dist y x < 2 * r := by
        rw [h_eq]
        constructor
        · intro h5
          calc dist y x
            = r * ((1 / r) * dist y x) := by field_simp [hr_pos.ne'] <;> ring
          _ < r * 2 := by gcongr
          _ = 2 * r := by ring
        · intro h5
          calc (1 / r) * dist y x
            < (1 / r) * (2 * r) := by gcongr
          _ = 2 := by field_simp [hr_pos.ne'] <;> ring
      simpa [ball, Metric.mem_ball] using h4
    have h_int2 : Integrable (fun y : E n => (φ k) (scale r y)) μ :=
      integrable_bounded_finite_support (isOpen_ball.measurableSet : MeasurableSet (ball x (2 * r))) hfin2
        ((hφ_smooth k).continuous.comp (hcont_scale r hr_pos))
        (fun y hy => hφ_zero_outside k (scale r y) ((h_scale_ball2 y).not.mpr hy))
        1 (fun y => by
          have h : 0 ≤ φ k (scale r y) ∧ φ k (scale r y) ≤ 1 := ⟨hφ_nonneg k _, hφ_le_one k _⟩
          exact abs_le.mpr ⟨by linarith, by linarith⟩)
    have h5 : ∫ y, ind2 y ∂μ = (μ (ball x r)).toReal := by
      have h_eq1 : ∫ y, ind2 y ∂μ = ∫ y in ball x r, (1 : ℝ) ∂μ := by
        rw [integral_indicator isOpen_ball.measurableSet] <;> rfl
      rw [h_eq1]
      rw [MeasureTheory.setIntegral_const (1 : ℝ)]
      <;> simp [Measure.real, hfin.ne]
    have h6 : ∫ y, ind2 y ∂μ ≤ ∫ y, (φ k) (scale r y) ∂μ :=
      integral_mono h_int1 h_int2 h1
    rw [h5] at h6
    exact div_le_div_of_nonneg_right h6 (by positivity)

  -- Test function convergence
  have hψ_conv : ∀ k, Tendsto (fun r : ℝ => (∫ y, (ψ k) (scale r y) ∂μ) / r ^ (n - 1)) l
        (nhds (∫ z in Pν, (ψ k) z ∂μHE[n - 1])) :=
    fun k => h_test (ψ k) (hψ_smooth k) (hψ_support k) (hψ_nonneg k)
  have hφ_conv : ∀ k, Tendsto (fun r : ℝ => (∫ y, (φ k) (scale r y) ∂μ) / r ^ (n - 1)) l
        (nhds (∫ z in Pν, (φ k) z ∂μHE[n - 1])) :=
    fun k => h_test (φ k) (hφ_smooth k) (hφ_support k) (hφ_nonneg k)

  let a : ℕ → ℝ := fun k => ∫ z in Pν, (ψ k) z ∂μHE[n - 1]
  let b : ℕ → ℝ := fun k => ∫ z in Pν, (φ k) z ∂μHE[n - 1]

  -- H(Pν ∩ ball 0 2) < ⊤ needed for DCT
  have hH_ball2_finite : H (ball (0 : E n) 2) < ⊤ := by
    have hR : (0 : ℝ) < 2 := by norm_num
    have h_eq : H (ball (0 : E n) 2) = μHE[n - 1] (Pν ∩ ball (0 : E n) 2) := by
      dsimp only [H]
      have h : (μHE[n - 1].restrict Pν) (ball (0 : E n) 2) = μHE[n - 1] (ball (0 : E n) 2 ∩ Pν) :=
        Measure.restrict_apply isOpen_ball.measurableSet
      rw [h, Set.inter_comm]
    rw [h_eq]
    have hPν_eq : Pν = {z : E n | inner ℝ z ν = 0} := by rfl
    rw [hPν_eq]
    exact hyperplane_ball_finite ν hν_unit (2 : ℝ) hR

  -- Dominating function for DCT
  let dom : E n → ℝ := Set.indicator (ball (0 : E n) 2) 1
  have hdom_int : Integrable dom H := by
    have h' : IntegrableOn (1 : E n → ℝ) (ball (0 : E n) 2) H := by
      have hC : ‖(1 : ℝ)‖ₑ ≠ ⊤ := by simp [ENorm.enorm] <;> norm_num
      exact MeasureTheory.integrableOn_const (hs := hH_ball2_finite.ne) (hC := hC)
    simpa [dom, integrable_indicator_iff, isOpen_ball.measurableSet] using h'

  -- a_k → L by DCT
  have ha_tendsto : Tendsto a atTop (nhds L) := by
    have h_pointwise : ∀ᵐ z ∂H, Tendsto (fun k => ψ k z) atTop (nhds (Set.indicator (ball (0 : E n) 1) 1 z)) := by
      filter_upwards with z
      by_cases hz : z ∈ ball (0 : E n) 1
      · have h_dist : dist z (0 : E n) < 1 := by simpa [ball] using hz
        have h_pos : 0 < 1 - dist z (0 : E n) := by linarith
        have h_ev : ∀ᶠ k in atTop, ε k < 1 - dist z (0 : E n) :=
          hε_tendsto (Iio_mem_nhds h_pos)
        have h_eventually : ∀ᶠ k in atTop, ψ k z = 1 := by
          filter_upwards [h_ev] with k hk
          have h_le : dist z (0 : E n) ≤ 1 - ε k := by linarith
          exact hψ_one k z h_le
        have h_eq : (fun k => ψ k z) =ᶠ[atTop] (fun _ => 1) := h_eventually
        have h_tendsto : Tendsto (fun k => ψ k z) atTop (nhds 1) :=
          Tendsto.congr' h_eq.symm tendsto_const_nhds
        simpa [hz] using h_tendsto
      · have h_all : ∀ k, ψ k z = 0 := by intro k; exact hψ_zero_outside k z hz
        have h_eq : (fun k => ψ k z) = fun _ => 0 := by funext k; exact h_all k
        have h_tendsto : Tendsto (fun k => ψ k z) atTop (nhds 0) := by
          rw [h_eq]; exact tendsto_const_nhds
        simpa [hz] using h_tendsto
    have h_bound : ∀ k, ∀ᵐ z ∂H, ‖ψ k z‖ ≤ dom z := by
      intro k; filter_upwards with z
      by_cases hz : z ∈ ball (0 : E n) 2
      · have hdom : dom z = 1 := by simp [dom, hz]
        rw [hdom]; have h : ‖ψ k z‖ ≤ 1 := by
          have h2 : 0 ≤ ψ k z ∧ ψ k z ≤ 1 := ⟨hψ_nonneg k z, hψ_le_one k z⟩
          rw [Real.norm_eq_abs]; exact abs_le.mpr ⟨by linarith, by linarith⟩
        exact h
      · have h2 : ψ k z = 0 := hψ_zero_outside k z (fun h3 => hz (ball_subset_ball (by norm_num) h3))
        have hdom : dom z = 0 := by simp [dom, hz]
        rw [hdom, h2] <;> norm_num
    have h_main := tendsto_integral_of_dominated_convergence dom
      (fun k => (hψ_smooth k).continuous.aestronglyMeasurable) hdom_int h_bound h_pointwise
    have h_eq : ∫ z, Set.indicator (ball (0 : E n) 1) 1 z ∂H = L := by
      simp [L, H, Measure.restrict_apply, isOpen_ball.measurableSet] <;> rfl
    rw [h_eq] at h_main; exact h_main

  -- b_k → L by DCT
  have hb_tendsto : Tendsto b atTop (nhds L) := by
    have h_pointwise : ∀ᵐ z ∂H, Tendsto (fun k => φ k z) atTop (nhds (Set.indicator (closedBall (0 : E n) 1) 1 z)) := by
      filter_upwards with z
      by_cases hz : z ∈ closedBall (0 : E n) 1
      · have h_all : ∀ k, φ k z = 1 := by intro k; exact hφ_one k z hz
        have h_eq : (fun k => φ k z) = fun _ => 1 := by funext k; exact h_all k
        have h_tendsto : Tendsto (fun k => φ k z) atTop (nhds 1) := by
          rw [h_eq]; exact tendsto_const_nhds
        simpa [hz] using h_tendsto
      · have h_dist : 1 < dist z (0 : E n) := by simpa [closedBall] using hz
        have h_pos : 0 < dist z (0 : E n) - 1 := by linarith
        have h_ev : ∀ᶠ k in atTop, ε k < dist z (0 : E n) - 1 :=
          hε_tendsto (Iio_mem_nhds h_pos)
        have h_eventually : ∀ᶠ k in atTop, φ k z = 0 := by
          filter_upwards [h_ev] with k hk
          have h_gt : 1 + ε k < dist z (0 : E n) := by linarith
          have h_le : 1 + ε k ≤ dist z (0 : E n) := le_of_lt h_gt
          exact radialCutoff_zero_of_not_mem_ball (by norm_num) (hε_pos k)
            (by simpa [ball] using h_le)
        have h_eq2 : (fun k => φ k z) =ᶠ[atTop] (fun _ => 0) := h_eventually
        have h_tendsto : Tendsto (fun k => φ k z) atTop (nhds 0) :=
          Tendsto.congr' h_eq2.symm tendsto_const_nhds
        simpa [hz] using h_tendsto
    have h_bound : ∀ k, ∀ᵐ z ∂H, ‖φ k z‖ ≤ dom z := by
      intro k; filter_upwards with z
      by_cases hz : z ∈ ball (0 : E n) 2
      · have hdom : dom z = 1 := by simp [dom, hz]
        rw [hdom]; have h : ‖φ k z‖ ≤ 1 := by
          have h2 : 0 ≤ φ k z ∧ φ k z ≤ 1 := ⟨hφ_nonneg k z, hφ_le_one k z⟩
          rw [Real.norm_eq_abs]; exact abs_le.mpr ⟨by linarith, by linarith⟩
        exact h
      · have h2 : φ k z = 0 := hφ_zero_outside k z (fun h3 => hz (ball_subset_ball (by norm_num) h3))
        have hdom : dom z = 0 := by simp [dom, hz]
        rw [hdom, h2] <;> norm_num
    have h_main := tendsto_integral_of_dominated_convergence dom
      (fun k => (hφ_smooth k).continuous.aestronglyMeasurable) hdom_int h_bound h_pointwise
    have h_eq1 : ∫ z, Set.indicator (closedBall (0 : E n) 1) 1 z ∂H = (H (closedBall (0 : E n) 1)).toReal := by
      simp [H, Measure.restrict_apply, isClosed_closedBall.measurableSet, integral_indicator]
      <;> rfl
    have hPν_set : (Pν : Set (E n)) = {z : E n | inner ℝ z ν = 0} := by
      ext z
      simp [Pν, Submodule.mem_orthogonal_singleton_iff_inner_left,
        real_inner_comm]
    have h_sphere_null : H (sphere (0 : E n) 1) = 0 := by
      have h : H (sphere (0 : E n) 1) = μHE[n - 1] ((Pν : Set (E n)) ∩ sphere (0 : E n) 1) := by
        simp [H, Measure.restrict_apply, isClosed_sphere.measurableSet]
        <;> rw [Set.inter_comm]
        <;> rfl
      rw [h, hPν_set]
      exact hyperplane_sphere_null ν hν_unit
    have h_sphere : H (closedBall (0 : E n) 1) = H (ball (0 : E n) 1) := by
      have h1 : closedBall (0 : E n) 1 = ball (0 : E n) 1 ∪ sphere (0 : E n) 1 := by
        ext y; simp [closedBall, ball, sphere, le_iff_lt_or_eq] <;> tauto
      rw [h1]
      have h_disj : Disjoint (ball (0 : E n) 1) (sphere (0 : E n) 1) := by
        rw [Set.disjoint_left] <;> intro y h1 h2 <;> simp [ball, sphere] at h1 h2 <;> linarith
      rw [measure_union h_disj isClosed_sphere.measurableSet, h_sphere_null, add_zero]
    rw [h_eq1, h_sphere] at h_main; exact h_main

  -- Double-limit squeeze: for any ε > 0, pick k with a_k, b_k close to L, then use convergence
  have h_main : Tendsto f l (nhds L) := by
    rw [Metric.tendsto_atTop] at ha_tendsto hb_tendsto
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hε2 : 0 < ε / 3 := by positivity
    rcases ha_tendsto (ε / 3) hε2 with ⟨N1, hN1⟩
    rcases hb_tendsto (ε / 3) hε2 with ⟨N2, hN2⟩
    let N := max N1 N2
    have ha_N : |a N - L| < ε / 3 := hN1 N (le_max_left _ _)
    have hb_N : |b N - L| < ε / 3 := hN2 N (le_max_right _ _)
    have h_lower_N : ∀ᶠ r in l, (∫ y, (ψ N) (scale r y) ∂μ) / r ^ (n - 1) ≤ f r := h_lower N
    have h_upper_N : ∀ᶠ r in l, f r ≤ (∫ y, (φ N) (scale r y) ∂μ) / r ^ (n - 1) := h_upper N
    have hψ_N_conv : Tendsto (fun r : ℝ => (∫ y, (ψ N) (scale r y) ∂μ) / r ^ (n - 1)) l (nhds (a N)) := hψ_conv N
    have hφ_N_conv : Tendsto (fun r : ℝ => (∫ y, (φ N) (scale r y) ∂μ) / r ^ (n - 1)) l (nhds (b N)) := hφ_conv N
    have h1 : ∀ᶠ r in l, a N - ε / 3 < (∫ y, (ψ N) (scale r y) ∂μ) / r ^ (n - 1) :=
      hψ_N_conv (Ioi_mem_nhds (by linarith))
    have h2 : ∀ᶠ r in l, (∫ y, (φ N) (scale r y) ∂μ) / r ^ (n - 1) < b N + ε / 3 :=
      hφ_N_conv (Iio_mem_nhds (by linarith))
    filter_upwards [h_lower_N, h_upper_N, h1, h2] with r hlow hhigh h1r h2r
    have h3 : L - ε < f r := by
      calc L - ε
        < a N - ε / 3 := by linarith [abs_lt.mp ha_N]
      _ < (∫ y, (ψ N) (scale r y) ∂μ) / r ^ (n - 1) := h1r
      _ ≤ f r := hlow
    have h4 : f r < L + ε := by
      calc f r
        ≤ (∫ y, (φ N) (scale r y) ∂μ) / r ^ (n - 1) := hhigh
      _ < b N + ε / 3 := h2r
      _ < L + ε := by linarith [abs_lt.mp hb_N]
    have h5 : dist (f r) L < ε := by
      simpa [dist_eq_norm, Real.norm_eq_abs, abs_lt] using ⟨by linarith, by linarith⟩
    exact h5
  have hL_eq : L = (μHE[n - 1] ({z : E n | inner ℝ z ν = 0} ∩ ball (0 : E n) 1)).toReal := by
    have h_eq1 : H (ball (0 : E n) 1) = μHE[n - 1] (Pν ∩ ball (0 : E n) 1) := by
      dsimp only [H]
      have h : (μHE[n - 1].restrict Pν) (ball (0 : E n) 1) = μHE[n - 1] (ball (0 : E n) 1 ∩ Pν) :=
        Measure.restrict_apply isOpen_ball.measurableSet
      rw [h, Set.inter_comm]
    have hPν_eq : Pν = {z : E n | inner ℝ z ν = 0} := by rfl
    have h : (H (ball (0 : E n) 1)).toReal = (μHE[n - 1] ({z : E n | inner ℝ z ν = 0} ∩ ball (0 : E n) 1)).toReal := by
      rw [h_eq1, hPν_eq]
    exact h
  rw [hL_eq] at h_main
  exact h_main

/-- **Pointwise perimeter density = ω_{n-1}** at a good reduced boundary point.

Combines Steps 1-4. -/
theorem perimeter_density_one_at_point
    {U : Set (E n)} (hU : IsOpen U) (hBdd : Bornology.IsBounded U)
    (h_perim_finite : perimeter U < ⊤) (hn : 2 ≤ n)
    (x : E n) (ν : E n) (hν_unit : ‖ν‖ = 1)
    (hνx : measureTheoreticNormal U x = ν)
    (hdata : ReducedBoundaryData U x ν)
    (h_upper : ∃ (C : ℝ) (r0 : ℝ), 0 < C ∧ 0 < r0 ∧
      ∀ r, 0 < r → r < r0 →
        perimeterMeasure U (closedBall x r) ≤ ENNReal.ofReal (C * r ^ (n - 1)))
    (h_leb : ∀ (R : ℝ), 0 < R →
      Tendsto (fun r : ℝ =>
        (∫ y in closedBall x (R * r), |inner ℝ ν (measureTheoreticNormal U y) - 1| ∂(perimeterMeasure U)) /
          (perimeterMeasure U (closedBall x (R * r))).toReal)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) :
    Tendsto (fun r : ℝ => (perimeterMeasure U (ball x r)).toReal / r ^ (n - 1))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((μHE[n - 1] ({z : E n | inner ℝ z ν = 0} ∩ ball (0 : E n) 1)).toReal)) := by
  let μ := perimeterMeasure U
  let Pν := {z : E n | inner ℝ z ν = 0}
  have h_conv := blow_up_lemma hU.measurableSet x ν hν_unit hdata hn
  have h_test : ∀ (ψ : E n → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∀ z, 0 ≤ ψ z) →
      Tendsto (fun r : ℝ => (∫ y, ψ ((1 / r) • (y - x)) ∂μ) / r ^ (n - 1))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (∫ z in Pν, ψ z ∂μHE[n - 1])) := by
    intro ψ hψ_smooth hψ_supp hψ_nonneg
    let I1 : ℝ → ℝ := fun r =>
      (∫ y, ψ ((1 / r) • (y - x)) * inner ℝ ν (measureTheoreticNormal U y) ∂μ) / r ^ (n - 1)
    let I2 : ℝ → ℝ := fun r =>
      (∫ y, ψ ((1 / r) • (y - x)) ∂μ) / r ^ (n - 1)
    let I3 : ℝ → ℝ := fun r =>
      (∫ y, ψ ((1 / r) • (y - x)) * (inner ℝ ν (measureTheoreticNormal U y) - 1) ∂μ) / r ^ (n - 1)
    have h_gg : ∀ (r : ℝ), 0 < r →
        ∫ y, ψ ((1 / r) • (y - x)) * inner ℝ ν (measureTheoreticNormal U y) ∂μ =
        (r : ℝ) ^ (n - 1) * ∫ z in blowUp U x r, fderiv ℝ ψ z ν :=
      fun r hr => gauss_green_scaling hU.measurableSet h_perim_finite x r hr ν hν_unit hn ψ hψ_smooth hψ_supp
    have h_blowup := blowup_integral_convergence hU.measurableSet hν_unit h_conv ψ hψ_smooth hψ_supp
    have h_div := halfspace_divergence_theorem hν_unit ψ hψ_smooth hψ_supp
    have h_lhs := lhs_normal_average h_perim_finite x ν hν_unit hνx ψ hψ_smooth hψ_supp h_upper h_leb
    have h1_eq : ∀ (r : ℝ), 0 < r → I1 r = ∫ z in blowUp U x r, fderiv ℝ ψ z ν := by
      intro r hr
      have h2 : I1 r = ((r : ℝ) ^ (n - 1) * ∫ z in blowUp U x r, fderiv ℝ ψ z ν) / r ^ (n - 1) := by
        simpa [I1] using congr_arg (fun x : ℝ => x / r ^ (n - 1)) (h_gg r hr)
      rw [h2]
      have h3 : 0 < r ^ (n - 1) := pow_pos hr (n - 1)
      field_simp [h3.ne'] <;> ring
    have hI1_tendsto : Tendsto I1 (nhdsWithin 0 (Set.Ioi 0))
        (nhds (∫ z in Pν, ψ z ∂μHE[n - 1])) := by
      have h_eq : ∀ᶠ r in nhdsWithin 0 (Set.Ioi 0), I1 r = ∫ z in blowUp U x r, fderiv ℝ ψ z ν := by
        filter_upwards [self_mem_nhdsWithin] with r hr
        exact h1_eq r hr
      have h4 : Tendsto (fun r => ∫ z in blowUp U x r, fderiv ℝ ψ z ν) (nhdsWithin 0 (Set.Ioi 0))
          (nhds (∫ z in halfSpace ν, fderiv ℝ ψ z ν)) := h_blowup
      rw [h_div] at h4
      have h_eq_symm : ∀ᶠ r in nhdsWithin 0 (Set.Ioi 0), (∫ z in blowUp U x r, fderiv ℝ ψ z ν) = I1 r := by
        filter_upwards [h_eq] with r hr
        exact hr.symm
      exact Tendsto.congr' h_eq_symm h4
    have hI3_tendsto : Tendsto I3 (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := h_lhs
    have h_rel : ∀ (r : ℝ), 0 < r → I1 r = I2 r + I3 r := by
      intro r hr
      let η_r : E n → ℝ := fun y => ψ ((1 / r) • (y - x))
      let g : E n → ℝ := fun y => inner ℝ ν (measureTheoreticNormal U y)
      have hμ_fin : μ Set.univ < ⊤ := by
        rw [← perimeter_eq_variation U h_perim_finite] <;> exact h_perim_finite
      letI : IsFiniteMeasure μ := ⟨hμ_fin⟩
      have h_int_η : Integrable η_r μ := by
        have h_cont : Continuous η_r := by fun_prop
        have h_supp : HasCompactSupport η_r := by
          let h_map : E n → E n := fun y => (1 / r) • (y - x)
          have h1 : Function.support η_r ⊆ h_map ⁻¹' (tsupport ψ) := by
            intro y hy
            have h2 : η_r y ≠ 0 := by simpa [Function.mem_support] using hy
            have h3 : h_map y ∈ Function.support ψ := by
              have h_eq : h_map y = (1 / r) • (y - x) := by rfl
              rw [h_eq]; simpa [η_r, Function.mem_support] using h2
            exact subset_closure h3
          let h_inv : E n → E n := fun z => r • z + x
          have h_right_inv : ∀ z, h_map (h_inv z) = z := by
            intro z
            have h1 : h_inv z - x = r • z := by simp [h_inv] <;> abel
            have h2 : h_map (h_inv z) = (1 / r) • (h_inv z - x) := by rfl
            rw [h2, h1]
            have h3 : (1 / r) • (r • z) = ((1 / r) * r) • z := by rw [smul_smul] <;> ring
            rw [h3]
            have h4 : (1 / r) * r = 1 := by field_simp [hr.ne'] <;> ring
            rw [h4] <;> simp
          have h_left_inv : ∀ y, h_inv (h_map y) = y := by
            intro y
            have h1 : h_map y = (1 / r) • (y - x) := by rfl
            rw [h1]
            have h2 : h_inv ((1 / r) • (y - x)) = r • ((1 / r) • (y - x)) + x := by rfl
            rw [h2]
            have h3 : r • ((1 / r) • (y - x)) = (r * (1 / r)) • (y - x) := by rw [smul_smul] <;> ring
            rw [h3]
            have h4 : r * (1 / r) = 1 := by field_simp [hr.ne'] <;> ring
            rw [h4] <;> simp <;> abel
          have h_preimage_eq : h_map ⁻¹' (tsupport ψ) = h_inv '' (tsupport ψ) := by
            ext y; simp only [Set.mem_preimage, Set.mem_image]
            constructor
            · intro hy; refine ⟨h_map y, hy, ?_⟩; exact h_left_inv y
            · rintro ⟨z, hz, rfl⟩
              have h6 : h_map (h_inv z) = z := h_right_inv z
              rw [h6]; exact hz
          have h1' : Function.support η_r ⊆ h_inv '' (tsupport ψ) := by
            rw [h_preimage_eq] at h1; exact h1
          rcases hψ_supp.isCompact.isBounded.subset_ball 0 with ⟨C, hC⟩
          have h6 : h_inv '' (tsupport ψ) ⊆ Metric.closedBall x (r * C) := by
            intro y hy; rcases hy with ⟨z, hz, rfl⟩
            have h7 : z ∈ Metric.closedBall (0 : E n) C := ball_subset_closedBall (hC hz)
            have h8 : dist z (0 : E n) ≤ C := h7
            have h9 : ‖z‖ ≤ C := by
              have h10 : dist z (0 : E n) = ‖z‖ := by simp [dist_eq_norm]
              rw [h10] at h8; exact h8
            have h10 : r * ‖z‖ ≤ r * C := mul_le_mul_of_nonneg_left h9 hr.le
            simpa [Metric.mem_closedBall, h_inv, dist_eq_norm, norm_smul, abs_of_pos hr] using h10
          have h9 : Bornology.IsBounded (Metric.closedBall x (r * C)) := by exact isBounded_closedBall
          have h10 : Bornology.IsBounded (Function.support η_r) := Bornology.IsBounded.subset (h9.subset h6) h1'
          have h11 : Bornology.IsBounded (tsupport η_r) := h10.closure
          have h12 : IsClosed (tsupport η_r) := isClosed_closure
          have h13 : IsCompact (tsupport η_r) := Metric.isCompact_of_isClosed_isBounded h12 h11
          exact h13
        exact h_cont.integrable_of_hasCompactSupport h_supp
      have hf_meas : Measurable (measureTheoreticNormal U) := measureTheoreticNormal_measurable h_perim_finite
      have hg_meas : AEStronglyMeasurable g μ := by
        have h : Measurable g := by fun_prop
        exact h.aestronglyMeasurable
      have hg_bdd : ∀ᵐ y ∂μ, ‖g y‖ ≤ 1 := by
        filter_upwards [norm_measureTheoreticNormal_eq_one h_perim_finite] with y hy
        have h1 : ‖g y‖ ≤ ‖ν‖ * ‖measureTheoreticNormal U y‖ := by
          have h2 : g y = inner ℝ ν (measureTheoreticNormal U y) := by rfl
          rw [h2]
          exact norm_inner_le_norm ν (measureTheoreticNormal U y)
        rw [hν_unit, hy] at h1
        have h1' : ‖g y‖ ≤ 1 := by simpa using h1
        exact h1'
      have h_prod_meas : AEStronglyMeasurable (η_r * g) μ := h_int_η.1.mul hg_meas
      have h_prod_bound : ∀ᵐ y ∂μ, ‖(η_r * g) y‖ ≤ ‖η_r y‖ := by
        filter_upwards [hg_bdd] with y hy
        have h_eq1 : (η_r * g) y = η_r y * g y := by rfl
        rw [h_eq1, norm_mul]
        calc ‖η_r y‖ * ‖g y‖
          _ ≤ ‖η_r y‖ * 1 := by gcongr
          _ = ‖η_r y‖ := by ring
      have h_int_ηg : Integrable (η_r * g) μ := Integrable.mono h_int_η h_prod_meas h_prod_bound
      have hg1_meas : AEStronglyMeasurable (g - 1) μ := by
        have h : Measurable (g - 1) := by fun_prop
        exact h.aestronglyMeasurable
      have hg1_bdd : ∀ᵐ y ∂μ, ‖g y - 1‖ ≤ 2 := by
        filter_upwards [hg_bdd] with y hy
        have h1 : |g y| ≤ 1 := by
          have h2 : ‖g y‖ = |g y| := by simp [Real.norm_eq_abs]
          rw [h2] at hy; exact hy
        have h3 : -1 ≤ g y := (abs_le.mp h1).1
        have h4 : g y ≤ 1 := (abs_le.mp h1).2
        have h5 : |g y - 1| ≤ 2 := by
          rw [abs_le] <;> constructor <;> linarith
        have h6 : ‖g y - 1‖ = |g y - 1| := by simp [Real.norm_eq_abs]
        rw [h6]; exact h5
      have h_prod1_meas : AEStronglyMeasurable (η_r * (g - 1)) μ := h_int_η.1.mul hg1_meas
      have h_int_2η : Integrable (2 • η_r) μ := by
        have h_eq : (2 • η_r) = fun y => (2 : ℝ) * η_r y := by funext y; simp
        rw [h_eq]
        exact h_int_η.const_mul (2 : ℝ)
      have h_prod1_bound : ∀ᵐ y ∂μ, ‖(η_r * (g - 1)) y‖ ≤ ‖(2 • η_r) y‖ := by
        filter_upwards [hg1_bdd] with y hy
        have h_eq1 : (η_r * (g - 1)) y = η_r y * (g y - 1) := by rfl
        rw [h_eq1, norm_mul]
        calc ‖η_r y‖ * ‖g y - 1‖
          _ ≤ ‖η_r y‖ * 2 := by gcongr
          _ = 2 * ‖η_r y‖ := by ring
          _ = ‖(2 • η_r) y‖ := by simp [norm_smul] <;> ring
      have h_int_ηg1 : Integrable (η_r * (g - 1)) μ := Integrable.mono h_int_2η h_prod1_meas h_prod1_bound
      have h_eq : η_r * g = η_r + (η_r * (g - 1)) := by
        funext y
        have h : η_r y * g y = η_r y + (η_r y * (g y - 1)) := by ring
        exact h
      have h5 : ∫ y, (η_r * g) y ∂μ = ∫ y, η_r y ∂μ + ∫ y, (η_r * (g - 1)) y ∂μ := by
        have h_eq2 : (η_r * g) = (η_r + (η_r * (g - 1))) := h_eq
        rw [h_eq2]
        exact integral_add h_int_η h_int_ηg1
      have h5' : (∫ y, (η_r * g) y ∂μ) / r ^ (n - 1) =
          (∫ y, η_r y ∂μ) / r ^ (n - 1) + (∫ y, (η_r * (g - 1)) y ∂μ) / r ^ (n - 1) := by
        rw [h5] <;> ring
      dsimp only [I1, I2, I3]
      simpa [η_r, g] using h5'
    have hI2_tendsto : Tendsto I2 (nhdsWithin 0 (Set.Ioi 0))
        (nhds (∫ z in Pν, ψ z ∂μHE[n - 1])) := by
      have h6 : ∀ᶠ (r : ℝ) in nhdsWithin 0 (Set.Ioi 0), I2 r = I1 r - I3 r := by
        filter_upwards [self_mem_nhdsWithin] with r hr
        have h7 := h_rel r hr
        linarith
      have h8 : Tendsto (fun r => I1 r - I3 r) (nhdsWithin 0 (Set.Ioi 0))
          (nhds ((∫ z in Pν, ψ z ∂μHE[n - 1]) - 0)) := hI1_tendsto.sub hI3_tendsto
      have h6_symm : ∀ᶠ (r : ℝ) in nhdsWithin 0 (Set.Ioi 0), (I1 r - I3 r) = I2 r := by
        filter_upwards [h6] with r hr
        exact hr.symm
      simpa [sub_zero] using Tendsto.congr' h6_symm h8
    exact hI2_tendsto
  exact test_functions_to_ball_density (U := U) x ν hν_unit μ h_upper h_test

/-- The (n-1)-dimensional Hausdorff measure of a unit hyperplane disk is positive. -/
lemma hyperplane_disk_positive {n : ℕ} (hn : 2 ≤ n) (ν_vec : E n) (hν_unit : ‖ν_vec‖ = 1) :
    0 < (μHE[n - 1] ({z : E n | inner ℝ z ν_vec = 0} ∩ ball (0 : E n) 1)).toReal := by
  let f : Module.Dual ℝ (E n) :=
    { toFun := fun z => inner ℝ z ν_vec
      map_add' := by simp [inner_add_left]
      map_smul' := by simp [inner_smul_left] }
  let H : Submodule ℝ (E n) := LinearMap.ker f
  have hH_def : (H : Set (E n)) = {z | inner ℝ z ν_vec = 0} := by
    ext z
    simp [H, f] <;> rfl
  have hf_ne_zero : f ≠ 0 := by
    intro h
    have h1 : f ν_vec = 0 := by rw [h] <;> simp
    have h2 : f ν_vec = inner ℝ ν_vec ν_vec := by rfl
    rw [h2] at h1
    have h3 : inner ℝ ν_vec ν_vec = ‖ν_vec‖ ^ 2 := by exact real_inner_self_eq_norm_sq ν_vec
    rw [h3, hν_unit] at h1 <;> norm_num at h1
  have h_dim : Module.finrank ℝ H + 1 = Module.finrank ℝ (E n) :=
    Module.Dual.finrank_ker_add_one_of_ne_zero hf_ne_zero
  have h_finrank_E : Module.finrank ℝ (E n) = n := by
    simpa [E, Fintype.card_fin] using finrank_fintype_fun
  have h_dim' : Module.finrank ℝ H = n - 1 := by omega
  let i : H → E n := Subtype.val
  have hi : Isometry i := by
    intro x y
    have h : edist (i x) (i y) = edist (x : E n) (y : E n) := by rfl
    have h2 : edist (x : H) y = edist (x : E n) (y : E n) := by exact Subtype.edist_eq x y
    exact Eq.trans h h2.symm
  let s : Set H := ball (0 : H) 1
  have h_image : i '' s = (H : Set (E n)) ∩ ball (0 : E n) 1 := by
    ext y
    simp only [Set.mem_image, s, Set.mem_inter_iff]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.prop, by simpa [mem_ball] using hx⟩
    · rintro ⟨hy, hball⟩
      refine ⟨⟨y, hy⟩, by simpa [mem_ball] using hball, rfl⟩
  have h_meas : μHE[n - 1] (i '' s) = μHE[n - 1] s :=
    Isometry.euclideanHausdorffMeasure_image hi s
  have h_eq : (μHE[n - 1] : Measure H) = volume := by
    have h_tmp : (μHE[Module.finrank ℝ H] : Measure H) = volume :=
      InnerProductSpace.euclideanHausdorffMeasure_eq_volume
    rw [h_dim'] at h_tmp
    exact h_tmp
  have h_pos : 0 < volume (ball (0 : H) 1) := by
    have h_open : IsOpen (ball (0 : H) 1) := isOpen_ball
    have h_int : interior (ball (0 : H) 1) = ball (0 : H) 1 := h_open.interior_eq
    have h_nonempty : (interior (ball (0 : H) 1)).Nonempty := by
      rw [h_int]
      exact ⟨0, by simp [mem_ball]⟩
    exact MeasureTheory.Measure.measure_pos_of_nonempty_interior volume h_nonempty
  have h_main : μHE[n - 1] ((H : Set (E n)) ∩ ball (0 : E n) 1) = volume (ball (0 : H) 1) := by
    calc μHE[n - 1] ((H : Set (E n)) ∩ ball (0 : E n) 1)
      = μHE[n - 1] (i '' s) := by rw [h_image]
    _ = μHE[n - 1] s := h_meas
    _ = volume s := by rw [h_eq]
    _ = volume (ball (0 : H) 1) := by rfl
  have h_set_eq : {z : E n | inner ℝ z ν_vec = 0} ∩ ball (0 : E n) 1 = (H : Set (E n)) ∩ ball (0 : E n) 1 := by
    rw [hH_def]
  rw [h_set_eq]
  have h_final : 0 < (μHE[n - 1] ((H : Set (E n)) ∩ ball (0 : E n) 1)).toReal := by
    rw [h_main]
    have h_lt_top : volume (ball (0 : H) 1) < ⊤ := by exact measure_ball_lt_top
    exact ENNReal.toReal_pos h_pos.ne' h_lt_top.ne
  exact h_final

/-- If a/r^k < L+δ eventually and b/r^k > L-δ eventually, then a/b < 1+ε eventually. -/
lemma ratio_bound_helper {n : ℕ} {a b : ℝ → ℝ} {L : ℝ} (hL_pos : 0 < L)
    (ha : ∀ δ, 0 < δ → ∀ᶠ r in nhdsWithin 0 (Set.Ioi 0), a r / r ^ (n - 1) < L + δ)
    (hb : ∀ δ, 0 < δ → ∀ᶠ r in nhdsWithin 0 (Set.Ioi 0), b r / r ^ (n - 1) > L - δ)
    (hb_pos : ∀ᶠ r in nhdsWithin 0 (Set.Ioi 0), 0 < b r) :
    ∀ ε, 0 < ε → ∀ᶠ r in nhdsWithin 0 (Set.Ioi 0), a r / b r < 1 + ε := by
  intro ε hε
  set δ : ℝ := ε * L / (2 + ε) with hδ_def
  have h2pos : 0 < 2 + ε := by linarith
  have hδ_pos : 0 < δ := by rw [hδ_def] <;> positivity
  have hδ_lt_L : δ < L := by
    rw [hδ_def]
    have h2pos : 0 < 2 + ε := by linarith
    have hLpos : 0 < L := hL_pos
    have h3 : ε * L < L * (2 + ε) := by nlinarith
    calc ε * L / (2 + ε)
      < L * (2 + ε) / (2 + ε) := by gcongr
    _ = L := by field_simp [h2pos.ne'] <;> ring
  have h1 := ha δ hδ_pos
  have h2 : ∀ᶠ r in nhdsWithin 0 (Set.Ioi 0), b r / r ^ (n - 1) > L - δ := hb δ hδ_pos
  filter_upwards [h1, h2, hb_pos, self_mem_nhdsWithin] with r h1 h2 h3 hr
  have hpos : 0 < r ^ (n - 1) := pow_pos hr (n - 1)
  have h4 : a r < (L + δ) * r ^ (n - 1) := by
    calc a r = (a r / r ^ (n - 1)) * r ^ (n - 1) := by field_simp [hpos.ne'] <;> ring
      _ < (L + δ) * r ^ (n - 1) := by gcongr
  have h5 : (L - δ) * r ^ (n - 1) < b r := by
    calc (L - δ) * r ^ (n - 1) < (b r / r ^ (n - 1)) * r ^ (n - 1) := by gcongr
      _ = b r := by field_simp [hpos.ne'] <;> ring
  have h6 : 0 < (L - δ) * r ^ (n - 1) := by positivity
  have h7 : a r / b r < (L + δ) / (L - δ) := by
    calc a r / b r
      < ((L + δ) * r ^ (n - 1)) / ((L - δ) * r ^ (n - 1)) := by gcongr
    _ = (L + δ) / (L - δ) := by field_simp [h6.ne'] <;> ring
  have h8 : (L + δ) / (L - δ) = 1 + ε := by
    rw [hδ_def]
    have h9 : 0 < L := hL_pos
    field_simp [h2pos.ne', h9.ne'] <;> ring
  rw [h8] at h7
  exact h7

/-- **Pointwise f ≤ 1 at a good TRB point**. -/
lemma f_le_one_at_good_trb_point
    {U : Set (E n)} (hU : IsOpen U) (hBdd : Bornology.IsBounded U)
    (h_perim_finite : perimeter U < ⊤) (hn : 2 ≤ n)
    (μ ν : Measure (E n)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (f : E n → ℝ≥0∞)
    (hμ_def : μ = perimeterMeasure U)
    (hν_def : ν = μHE[n - 1].restrict (frontier U))
    (x : E n) (ν_vec : E n)
    (hν_unit : ‖ν_vec‖ = 1)
    (hνx : measureTheoreticNormal U x = ν_vec)
    (hdata : ReducedBoundaryData U x ν_vec)
    (omega : ℝ) (homega_pos : 0 < omega)
    (h_perim_ball : Tendsto (fun r : ℝ => (μ (ball x r)).toReal / r ^ (n - 1))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds omega))
    (h_haus_lower : ∀ (δ : ℝ), 0 < δ →
      ∀ᶠ r in nhdsWithin 0 (Set.Ioi 0),
        (ν (ball x r)).toReal / r ^ (n - 1) > omega - δ)
    (h_upper : ∃ (C : ℝ) (r0 : ℝ), 0 < C ∧ 0 < r0 ∧
      ∀ r, 0 < r → r < r0 →
        μ (closedBall x r) ≤ ENNReal.ofReal (C * r ^ (n - 1)))
    (h_leb : ∀ (R : ℝ), 0 < R →
      Tendsto (fun r : ℝ =>
        (∫ y in closedBall x (R * r), |inner ℝ ν_vec (measureTheoreticNormal U y) - 1| ∂μ) /
          (μ (closedBall x (R * r))).toReal)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (h_besicovitch : Tendsto (fun r : ℝ => μ (closedBall x r) / ν (closedBall x r))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (f x))) :
    f x ≤ 1 := by
  let A : ℝ → ℝ := fun r => (μ (closedBall x r)).toReal
  let B : ℝ → ℝ := fun r => (ν (closedBall x r)).toReal

  -- closedBall perimeter density: for any δ, eventually A/r^(n-1) < omega + δ
  have h_A_upper : ∀ (δ : ℝ), 0 < δ →
      ∀ᶠ r in nhdsWithin 0 (Set.Ioi 0), A r / r ^ (n - 1) < omega + δ := by
    intro δ hδ
    have h_cont : Continuous (fun ε : ℝ => (1 + ε) ^ (n - 1) * omega) := by fun_prop
    have h_f0 : (1 + (0 : ℝ)) ^ (n - 1) * omega < omega + δ := by
      have h1 : (1 + (0 : ℝ)) ^ (n - 1) = 1 := by simp
      rw [h1, one_mul]
      exact lt_add_of_pos_right omega hδ
    have h_ev : ∀ᶠ ε in nhds (0 : ℝ), (1 + ε) ^ (n - 1) * omega < omega + δ :=
      h_cont.continuousAt.tendsto (Iio_mem_nhds h_f0)
    rcases Metric.mem_nhds_iff.mp h_ev with ⟨ε0, hε0_pos, hball⟩
    let ε : ℝ := ε0 / 2
    have hε_pos : 0 < ε := by positivity
    have hε_mem : ε ∈ Metric.ball (0 : ℝ) ε0 := by
      have h : dist (0 : ℝ) ε < ε0 := by
        dsimp only [ε]
        have h2 : dist (0 : ℝ) (ε0 / 2) = ε0 / 2 := by
          rw [Real.dist_eq]
          have h3 : |(0 : ℝ) - ε0 / 2| = ε0 / 2 := by
            have h4 : (0 : ℝ) - ε0 / 2 = -(ε0 / 2) := by ring
            rw [h4, abs_neg, abs_of_pos] <;> positivity
          exact h3
        rw [h2] <;> linarith
      simpa [Metric.mem_ball] using h
    have hε_lt : (1 + ε) ^ (n - 1) * omega < omega + δ := hball hε_mem
    set c : ℝ := (1 + ε) ^ (n - 1) with hc_def
    set c' : ℝ := 1 + ε with hc'_def
    have hc'_pos : 0 < c' := by linarith
    have h_sub : ∀ r ∈ Set.Ioi (0 : ℝ), closedBall x r ⊆ ball x (c' * r) := by
      intro r hr y hy
      have hdist : dist y x ≤ r := mem_closedBall.mp hy
      have h1 : 1 < c' := by linarith
      have hlt : r < c' * r := by
        have h2 : 0 < r := hr
        calc r = 1 * r := by ring
          _ < c' * r := by gcongr
      exact mem_ball.mpr (lt_of_le_of_lt hdist hlt)
    have h_map : ∀ r ∈ Set.Ioi (0 : ℝ), c' * r ∈ Set.Ioi (0 : ℝ) := by
      intro r hr; exact mul_pos hc'_pos hr
    have h_id : Tendsto (fun r : ℝ => r) (nhds 0) (nhds 0) := tendsto_id
    have h_base : Tendsto (fun r : ℝ => c' * r) (nhds 0) (nhds 0) := by
      have h : Tendsto (fun r : ℝ => c' * r) (nhds 0) (nhds (c' * (0 : ℝ))) := h_id.const_mul c'
      have h2 : c' * (0 : ℝ) = 0 := by ring
      rw [h2] at h
      exact h
    have h1a : Tendsto (fun r : ℝ => c' * r) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
      h_base.mono_left nhdsWithin_le_nhds
    have h1b : ∀ᶠ r in nhdsWithin 0 (Set.Ioi 0), (c' * r) ∈ Set.Ioi (0 : ℝ) := by
      filter_upwards [self_mem_nhdsWithin] with r hr; exact h_map r hr
    have h1 : Tendsto (fun r : ℝ => c' * r) (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin 0 (Set.Ioi 0)) :=
      tendsto_nhdsWithin_iff.mpr ⟨h1a, h1b⟩
    have h_scale : Tendsto (fun r : ℝ => (μ (ball x (c' * r))).toReal / (c' * r) ^ (n - 1))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds omega) := h_perim_ball.comp h1
    have h_bound : ∀ᶠ r in nhdsWithin 0 (Set.Ioi 0),
        A r / r ^ (n - 1) ≤ c * ((μ (ball x (c' * r))).toReal / (c' * r) ^ (n - 1)) := by
      filter_upwards [self_mem_nhdsWithin] with r hr
      have hpos2 : 0 < c' * r := mul_pos hc'_pos hr
      have hfin : μ (ball x (c' * r)) ≠ ⊤ := (measure_lt_top _ _).ne
      have hle : A r ≤ (μ (ball x (c' * r))).toReal :=
        ENNReal.toReal_mono hfin (measure_mono (h_sub r hr))
      have hpos3 : 0 < (c' * r) ^ (n - 1) := by positivity
      have h_eq : (c' * r) ^ (n - 1) = r ^ (n - 1) * c := by
        calc (c' * r) ^ (n - 1)
          = (c') ^ (n - 1) * r ^ (n - 1) := by rw [mul_pow]
        _ = r ^ (n - 1) * (c') ^ (n - 1) := by ring
        _ = r ^ (n - 1) * c := by rw [hc_def, hc'_def]
      have hpos4 : 0 < r ^ (n - 1) := pow_pos hr (n - 1)
      have hpos4' : 0 ≤ r ^ (n - 1) := by linarith
      have h_eq2 : (μ (ball x (c' * r))).toReal / r ^ (n - 1) =
          c * ((μ (ball x (c' * r))).toReal / (c' * r) ^ (n - 1)) := by
        have h_eq3 : (c' * r) ^ (n - 1) = r ^ (n - 1) * c := by
          calc (c' * r) ^ (n - 1)
            = (c') ^ (n - 1) * r ^ (n - 1) := by rw [mul_pow]
          _ = r ^ (n - 1) * (c') ^ (n - 1) := by ring
          _ = r ^ (n - 1) * c := by rw [hc_def, hc'_def]
        field_simp [hpos3.ne'] <;> rw [h_eq3] <;> ring
      calc A r / r ^ (n - 1)
        ≤ (μ (ball x (c' * r))).toReal / r ^ (n - 1) :=
          div_le_div_of_nonneg_right hle hpos4'
      _ = c * ((μ (ball x (c' * r))).toReal / (c' * r) ^ (n - 1)) := h_eq2
    have h_c_mul : Tendsto (fun r : ℝ => c * ((μ (ball x (c' * r))).toReal / (c' * r) ^ (n - 1)))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (c * omega)) := h_scale.const_mul c
    have h_eventually : ∀ᶠ r in nhdsWithin 0 (Set.Ioi 0),
        c * ((μ (ball x (c' * r))).toReal / (c' * r) ^ (n - 1)) < omega + δ := by
      have h : c * omega < omega + δ := by simpa [hc_def] using hε_lt
      exact h_c_mul (Iio_mem_nhds h)
    filter_upwards [h_bound, h_eventually] with r h1 h2
    exact lt_of_le_of_lt h1 h2

  -- B lower bound from ball lower bound
  have h_B_lower : ∀ (δ : ℝ), 0 < δ →
      ∀ᶠ r in nhdsWithin 0 (Set.Ioi 0), B r / r ^ (n - 1) > omega - δ := by
    intro δ hδ
    have h1 := h_haus_lower δ hδ
    filter_upwards [h1, self_mem_nhdsWithin] with r h1 hr
    have hpos : 0 < r ^ (n - 1) := pow_pos hr (n - 1)
    have hle : (ν (ball x r)).toReal ≤ B r :=
      ENNReal.toReal_mono (measure_lt_top _ _).ne (measure_mono ball_subset_closedBall)
    have h : (ν (ball x r)).toReal / r ^ (n - 1) ≤ B r / r ^ (n - 1) :=
      div_le_div_of_nonneg_right hle (by positivity)
    exact lt_of_lt_of_le h1 h

  -- B positive eventually
  have hB_pos : ∀ᶠ r in nhdsWithin 0 (Set.Ioi 0), 0 < B r := by
    have h1 := h_B_lower (omega / 2) (by linarith [homega_pos])
    filter_upwards [h1, self_mem_nhdsWithin] with r h1 hr
    have hpos : 0 < r ^ (n - 1) := pow_pos hr (n - 1)
    have h_half_pos : 0 < omega - omega / 2 := by linarith [homega_pos]
    have h2 : B r > (omega - omega / 2) * r ^ (n - 1) := by
      have h3 : B r / r ^ (n - 1) > omega - omega / 2 := h1
      have h4 : B r = (B r / r ^ (n - 1)) * r ^ (n - 1) := by
        field_simp [hpos.ne'] <;> ring
      rw [h4]
      gcongr
    have h5 : 0 < (omega - omega / 2) * r ^ (n - 1) := mul_pos h_half_pos hpos
    exact lt_of_lt_of_le h5 h2.le

  -- Real ratio bound
  have h_ratio : ∀ ε, 0 < ε → ∀ᶠ r in nhdsWithin 0 (Set.Ioi 0), A r / B r < 1 + ε :=
    ratio_bound_helper homega_pos h_A_upper h_B_lower hB_pos

  -- ENNReal ratio bound
  have h_main : ∀ (ε : ℝ), 0 < ε →
      ∀ᶠ r in nhdsWithin 0 (Set.Ioi 0),
        μ (closedBall x r) / ν (closedBall x r) ≤ ENNReal.ofReal (1 + ε) := by
    intro ε hε
    have h4 := h_ratio ε hε
    filter_upwards [h4, hB_pos, self_mem_nhdsWithin] with r h4 hBpos hr
    have hfin1 : μ (closedBall x r) ≠ ⊤ := (measure_lt_top _ _).ne
    have hfin2 : ν (closedBall x r) ≠ ⊤ := (measure_lt_top _ _).ne
    have hne : ν (closedBall x r) ≠ 0 := by
      have hBpos' : (ν (closedBall x r)).toReal > 0 := by simpa [B] using hBpos
      by_contra h0
      have h5 : (ν (closedBall x r)).toReal = 0 := by rw [h0] <;> simp
      rw [h5] at hBpos'
      exact False.elim (lt_irrefl (0 : ℝ) hBpos')
    set x' : ENNReal := μ (closedBall x r) / ν (closedBall x r) with hx'_def
    have h_x'_fin : x' ≠ ⊤ := by
      simp [hx'_def, ENNReal.div_eq_top] <;> tauto
    have h10 : x'.toReal = A r / B r := by
      simp only [hx'_def, A, B]
      rw [ENNReal.toReal_div] <;> rfl
    have h11 : x'.toReal < 1 + ε := by rw [h10] <;> exact h4
    have h12 : x' ≤ ENNReal.ofReal (1 + ε) := by
      have h13 : x'.toReal ≤ 1 + ε := by linarith
      have h14 : x' = ENNReal.ofReal x'.toReal := (ENNReal.ofReal_toReal h_x'_fin).symm
      rw [h14]
      have h15 : ENNReal.ofReal x'.toReal ≤ ENNReal.ofReal (1 + ε) :=
        ENNReal.ofReal_le_ofReal h13
      exact h15
    exact h12

  -- Conclude f x ≤ 1
  have h9 : ∀ (ε : ℝ), 0 < ε → f x ≤ ENNReal.ofReal (1 + ε) :=
    fun ε hε => by
      have h : ∀ᶠ r in nhdsWithin 0 (Set.Ioi 0), μ (closedBall x r) / ν (closedBall x r) ≤ ENNReal.ofReal (1 + ε) := h_main ε hε
      exact le_of_tendsto h_besicovitch h
  by_cases h_top : f x = ⊤
  · have h10 : f x ≤ ENNReal.ofReal 2 := by
      have h10' := h9 1 (by norm_num)
      have h10'' : ENNReal.ofReal (1 + 1) = ENNReal.ofReal 2 := by norm_cast
      rw [h10''] at h10'
      exact h10'
    rw [h_top] at h10
    simpa using h10
  · have h_finite : f x ≠ ⊤ := h_top
    by_contra h
    have h_gt : 1 < f x := by exact lt_of_not_ge h
    have h_eq : f x = ENNReal.ofReal (f x).toReal := (ENNReal.ofReal_toReal h_finite).symm
    have h10 : 1 < (f x).toReal := by
      have h11 : (ENNReal.ofReal 1 : ENNReal) < f x := by
        have h11' : (1 : ENNReal) < f x := h_gt
        simpa using h11'
      have h12 : f x = ENNReal.ofReal (f x).toReal := h_eq
      rw [h12] at h11
      have h13 : 0 ≤ (1 : ℝ) := by norm_num
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg h13).mp h11
    set ε : ℝ := ((f x).toReal - 1) / 2 with hε_def
    have hε_pos : 0 < ε := by linarith
    have h11 : (f x).toReal > 1 + ε := by
      rw [hε_def] <;> linarith
    have h12 : f x > ENNReal.ofReal (1 + ε) := by
      have h13 : 0 < (f x).toReal := by linarith
      have h14 : ENNReal.ofReal (1 + ε) < ENNReal.ofReal (f x).toReal :=
        (ENNReal.ofReal_lt_ofReal_iff h13).mpr h11
      rw [h_eq]
      exact h14
    have h13 : f x ≤ ENNReal.ofReal (1 + ε) := h9 ε hε_pos
    exact not_le.mpr h12 h13

lemma f_le_one_ae_on_trb
    {U : Set (E n)} (hU : IsOpen U) (hU_reg : U = interior (closure U))
    (hBdd : Bornology.IsBounded U) (h_perim_finite : perimeter U < ⊤)
    (hfin : μHE[n - 1] (frontier U) < ⊤) (hn : 2 ≤ n)
    (μ ν : Measure (E n)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (f : E n → ℝ≥0∞)
    (hμ_def : μ = perimeterMeasure U)
    (hν_def : ν = μHE[n - 1].restrict (frontier U))
    (h_f_def : f = μ.rnDeriv ν)
    (h_abs : μ ≪ ν)
    (h_withDensity : μ = ν.withDensity f) :
    ∀ᵐ x ∂ν, x ∈ trueReducedBoundary U → f x ≤ 1 := by
  subst h_f_def
  subst hμ_def
  let TRB := trueReducedBoundary U
  let ν_U := measureTheoreticNormal U
  let μ : Measure (E n) := perimeterMeasure U

  -- Step 1: Lower perimeter density AE (from Maggi 15.5)
  have h_lower_ae_raw := lower_perimeter_density_ae_at_trb hU hU_reg hBdd h_perim_finite hn
  have h_lower_ae : ∃ (N_lower : Set (E n)), MeasurableSet N_lower ∧
      perimeterMeasure U N_lower = 0 ∧
      ∀ x ∈ TRB \ N_lower,
        ∃ (c : ℝ) (R : ℝ), 0 < c ∧ 0 < R ∧
          ∀ r, 0 < r → r < R →
            perimeterMeasure U (ball x r) ≥ ENNReal.ofReal (c * r ^ (n - 1)) := by
    rcases h_lower_ae_raw with ⟨N, hN_meas, hN_null, h_lower⟩
    refine ⟨N, hN_meas, hN_null, fun x hx => ?_⟩
    rcases h_lower x hx with ⟨c, R, hc_pos, hR_pos, h_bound⟩
    refine ⟨c, R, hc_pos, hR_pos, fun r hr hrR => ?_⟩
    have h1 : ENNReal.ofReal (c * r ^ (n - 1)) ≤ perimeterIn U (ball x r) := h_bound r hr hrR
    have h2 : perimeterIn U (ball x r) ≤ perimeterMeasure U (ball x r) :=
      perimeterIn_le_perimeterMeasure' h_perim_finite
    exact le_trans h1 h2

  -- Step 2: Reduced boundary data + norm 1 outside a μ-null set
  rcases trueReducedBoundary_has_data hU hU_reg hBdd h_perim_finite hn h_lower_ae with
    ⟨N_data, hN_data_meas, hN_data_null, h_data⟩

  -- Step 3: AE properties
  have h_upper_ae : ∀ᵐ (x : E n) ∂μ,
      ∃ (C : ℝ) (r0 : ℝ), 0 < C ∧ 0 < r0 ∧
        ∀ r, 0 < r → r < r0 →
          perimeterIn U (ball x r) ≤ ENNReal.ofReal (C * r ^ (n - 1)) :=
    perimeter_density_upper_bound hU hBdd h_perim_finite hn

  have h_leb_ae : ∀ᵐ (x : E n) ∂μ,
      ∀ (v : E n), ‖v‖ = 1 → ν_U x = v →
        Filter.Tendsto (fun r : ℝ =>
          (∫ y in closedBall x r, |inner ℝ v (ν_U y) - 1| ∂μ) /
            (μ (closedBall x r)).toReal)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    leb_abs_ae h_perim_finite

  have h_besicovitch_ν : ∀ᵐ (x : E n) ∂ν,
      Filter.Tendsto (fun r : ℝ => μ (closedBall x r) / ν (closedBall x r))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds ((μ.rnDeriv ν) x)) :=
    Besicovitch.ae_tendsto_rnDeriv μ ν

  -- Convert ν-a.e. to μ-a.e. using absolute continuity
  let Bad_bes := {x : E n | ¬Filter.Tendsto (fun r : ℝ => μ (closedBall x r) / ν (closedBall x r))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ((μ.rnDeriv ν) x))}
  have hBad_bes_null : ν Bad_bes = 0 := (ae_iff).mp h_besicovitch_ν
  rcases MeasureTheory.exists_measurable_superset ν Bad_bes with ⟨N_bes, hN_bes_sub, hN_bes_meas, hN_bes_eq⟩
  have hN_bes_null : ν N_bes = 0 := by rw [hN_bes_eq, hBad_bes_null]
  have hμ_bes_null : μ N_bes = 0 := h_abs hN_bes_null
  have h_bad_bes_μ_null : μ Bad_bes = 0 := measure_mono_null hN_bes_sub hμ_bes_null
  have h_besicovitch_μ : ∀ᵐ (x : E n) ∂μ,
      Filter.Tendsto (fun r : ℝ => μ (closedBall x r) / ν (closedBall x r))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds ((μ.rnDeriv ν) x)) :=
    (ae_iff).mpr h_bad_bes_μ_null

  have h_not_N_data : ∀ᵐ (x : E n) ∂μ, x ∉ N_data := by
    simpa [ae_iff] using hN_data_null

  -- Combined good property P
  let P : E n → Prop := fun x =>
    (x ∉ N_data) ∧
    (∃ (C : ℝ) (r0 : ℝ), 0 < C ∧ 0 < r0 ∧
      ∀ r, 0 < r → r < r0 →
        perimeterIn U (ball x r) ≤ ENNReal.ofReal (C * r ^ (n - 1))) ∧
    (∀ (v : E n), ‖v‖ = 1 → ν_U x = v →
      Filter.Tendsto (fun r : ℝ =>
        (∫ y in closedBall x r, |inner ℝ v (ν_U y) - 1| ∂μ) /
          (μ (closedBall x r)).toReal)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) ∧
    (Filter.Tendsto (fun r : ℝ => μ (closedBall x r) / ν (closedBall x r))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ((μ.rnDeriv ν) x)))

  have hP_ae : ∀ᵐ (x : E n) ∂μ, P x :=
    h_not_N_data.and (h_upper_ae.and (h_leb_ae.and h_besicovitch_μ))

  let Bad := {x | ¬P x}
  have hBad_null : μ Bad = 0 := (ae_iff).mp hP_ae
  rcases MeasureTheory.exists_measurable_superset μ Bad with ⟨N_meas, hN_sub, hN_meas, hN_eq⟩
  have hN_null : μ N_meas = 0 := by rw [hN_eq, hBad_null]

  let G := {x | P x}

  -- Step 4: Pointwise bound on G ∩ TRB
  have h_good_pointwise : ∀ x ∈ G ∩ TRB, (μ.rnDeriv ν) x ≤ 1 := by
    intro x hx
    have hx_P : P x := hx.1
    have hx_trb : x ∈ TRB := hx.2
    rcases hx_P with ⟨hx_not_N_data, h_upper_raw, h_leb_raw, h_besicovitch_x⟩

    have h_data_x : ‖ν_U x‖ = 1 ∧ ReducedBoundaryData U x (ν_U x) :=
      h_data x ⟨hx_trb, hx_not_N_data⟩
    have hν_unit : ‖ν_U x‖ = 1 := h_data_x.1
    have hdata : ReducedBoundaryData U x (ν_U x) := h_data_x.2

    rcases h_upper_raw with ⟨C, r0, hC_pos, hr0_pos, h_ud_bound⟩
    have h_upper_closed : ∃ (C' : ℝ) (r0' : ℝ), 0 < C' ∧ 0 < r0' ∧
        ∀ r, 0 < r → r < r0' →
          μ (closedBall x r) ≤ ENNReal.ofReal (C' * r ^ (n - 1)) :=
      upper_bound_perimeterMeasure_from_perimeterIn h_perim_finite hC_pos hr0_pos h_ud_bound hn

    have h_leb1 := h_leb_raw (ν_U x) hν_unit rfl

    have h_leb_all : ∀ (R : ℝ), 0 < R →
        Filter.Tendsto (fun r : ℝ =>
          (∫ y in closedBall x (R * r), |inner ℝ (ν_U x) (ν_U y) - 1| ∂μ) /
            (μ (closedBall x (R * r))).toReal)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      intro R hR
      have h_id : Filter.Tendsto (fun r : ℝ => r) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      have h_mul0 : Filter.Tendsto (fun r : ℝ => R * r) (nhds 0) (nhds (R * (0 : ℝ))) :=
        tendsto_id.const_mul R
      have h_mul : Filter.Tendsto (fun r : ℝ => R * r) (nhds 0) (nhds 0) := by
        have hR0 : R * (0 : ℝ) = 0 := by ring
        rw [hR0] at h_mul0
        exact h_mul0
      have h_mul_within : Filter.Tendsto (fun r : ℝ => R * r) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
        h_mul.mono_left nhdsWithin_le_nhds
      have h_pos : ∀ᶠ r in nhdsWithin 0 (Set.Ioi 0), R * r ∈ Set.Ioi 0 := by
        filter_upwards [self_mem_nhdsWithin] with r hr
        exact mul_pos hR hr
      have h_map : Filter.Tendsto (fun r : ℝ => R * r) (nhdsWithin 0 (Set.Ioi 0))
          (nhdsWithin 0 (Set.Ioi 0)) :=
        tendsto_nhdsWithin_iff.mpr ⟨h_mul_within, h_pos⟩
      exact h_leb1.comp h_map

    let omega : ℝ := (μHE[n - 1] ({z : E n | inner ℝ z (ν_U x) = 0} ∩ ball (0 : E n) 1)).toReal
    have homega_pos : 0 < omega := hyperplane_disk_positive hn (ν_U x) hν_unit

    have h_perim_ball : Filter.Tendsto (fun r : ℝ => (μ (ball x r)).toReal / r ^ (n - 1))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds omega) :=
      perimeter_density_one_at_point hU hBdd h_perim_finite hn x (ν_U x) hν_unit rfl hdata
        h_upper_closed h_leb_all

    have h_haus_frontier_lt_top : μHE[n - 1] (frontier U) < ⊤ := by
      have h1 : ν Set.univ < ⊤ := by (expose_names; exact (isFiniteMeasure_iff ν).mp inst)
      rw [hν_def] at h1
      simpa using h1

    have h_haus_raw : ∀ (ε : ℝ), 0 < ε →
        ∀ᶠ r in nhdsWithin 0 (Set.Ioi 0),
          (μHE[n - 1] (frontier U ∩ ball x r)).toReal / r ^ (n - 1) ≥ omega - ε :=
      hausdorff_lower_density_at_trb hU hBdd h_perim_finite hn hfin x (ν_U x) hν_unit hdata

    have hν_ball : ∀ (r : ℝ), ν (ball x r) = μHE[n - 1] (frontier U ∩ ball x r) := by
      intro r
      have h_ball_meas : MeasurableSet (ball x r) := isOpen_ball.measurableSet
      rw [hν_def, Measure.restrict_apply h_ball_meas]
      have h_eq : ball x r ∩ frontier U = frontier U ∩ ball x r := Set.inter_comm _ _
      rw [h_eq]

    have h_haus_lower : ∀ (δ : ℝ), 0 < δ →
        ∀ᶠ r in nhdsWithin 0 (Set.Ioi 0),
          (ν (ball x r)).toReal / r ^ (n - 1) > omega - δ := by
      intro δ hδ
      have h1 := h_haus_raw (δ / 2) (by linarith)
      filter_upwards [h1, self_mem_nhdsWithin] with r h1 hr
      have h_eq : (ν (ball x r)).toReal = (μHE[n - 1] (frontier U ∩ ball x r)).toReal := by
        rw [hν_ball r]
      rw [h_eq]
      have h2 : omega - δ / 2 > omega - δ := by linarith
      exact lt_of_lt_of_le h2 h1

    exact f_le_one_at_good_trb_point hU hBdd h_perim_finite hn μ ν (μ.rnDeriv ν) rfl hν_def
      x (ν_U x) hν_unit rfl hdata omega homega_pos h_perim_ball h_haus_lower h_upper_closed
      h_leb_all h_besicovitch_x

  -- Step 5: μ(TRB \ G) = 0 since TRB \ G ⊆ Bad
  have h_sub : TRB \ G ⊆ Bad := by
    intro x hx
    exact hx.2
  have hμ_null : μ (TRB \ G) = 0 := measure_mono_null h_sub hBad_null

  -- Step 6: f = 0 ν-a.e. on TRB \ G (via measurable superset N_meas)
  have h8 : TRB \ G ⊆ N_meas ∩ TRB := by
    intro x hx
    have h9 : x ∈ TRB := hx.1
    have h10 : x ∈ Bad := h_sub hx
    have h11 : x ∈ N_meas := hN_sub h10
    exact ⟨h11, h9⟩
  have hTRB_meas : MeasurableSet TRB := trb_measurable h_perim_finite
  have hN_TRB_meas : MeasurableSet (N_meas ∩ TRB) := hN_meas.inter hTRB_meas
  have h3 : μ (N_meas ∩ TRB) = 0 := by
    have h4 : N_meas ∩ TRB ⊆ N_meas := by simp
    exact measure_mono_null h4 hN_null
  have h4 : (ν.withDensity (μ.rnDeriv ν)) (N_meas ∩ TRB) = ∫⁻ x, Set.indicator (N_meas ∩ TRB) (μ.rnDeriv ν) x ∂ν := by
    rw [MeasureTheory.withDensity_apply (μ.rnDeriv ν) hN_TRB_meas]
    exact (MeasureTheory.lintegral_indicator hN_TRB_meas (μ.rnDeriv ν)).symm
  have h_eq_μ : μ = ν.withDensity (μ.rnDeriv ν) := by
    simpa [μ] using h_withDensity
  have h5 : μ (N_meas ∩ TRB) = (ν.withDensity (μ.rnDeriv ν)) (N_meas ∩ TRB) :=
    congr_arg (fun m : Measure (E n) => m (N_meas ∩ TRB)) h_eq_μ
  have h6 : ∫⁻ x, Set.indicator (N_meas ∩ TRB) (μ.rnDeriv ν) x ∂ν = 0 := by
    rw [←h4, ←h5, h3]
  have hf_meas : Measurable (μ.rnDeriv ν) := Measure.measurable_rnDeriv μ ν
  have h_indic_meas : Measurable (Set.indicator (N_meas ∩ TRB) (μ.rnDeriv ν)) := hf_meas.indicator hN_TRB_meas
  have h7 : ∀ᵐ x ∂ν, Set.indicator (N_meas ∩ TRB) (μ.rnDeriv ν) x = 0 := by
    rwa [lintegral_eq_zero_iff h_indic_meas] at h6
  have h_f_zero_bad : ∀ᵐ x ∂ν, x ∈ TRB \ G → (μ.rnDeriv ν) x = 0 := by
    filter_upwards [h7] with x hx
    intro hx_in
    have h13 : x ∈ N_meas ∩ TRB := h8 hx_in
    have h14 : Set.indicator (N_meas ∩ TRB) (μ.rnDeriv ν) x = (μ.rnDeriv ν) x := by
      simp [Set.indicator, h13]
    rw [h14] at hx
    exact hx

  -- Step 7: Combine
  filter_upwards [h_f_zero_bad] with x hx
  intro hx_trb
  by_cases h : x ∈ G
  · exact h_good_pointwise x ⟨h, hx_trb⟩
  · have h' : x ∈ TRB \ G := ⟨hx_trb, h⟩
    have h_f0 : (μ.rnDeriv ν) x = 0 := hx h'
    rw [h_f0]
    <;> simp

/-- **Final theorem: perimeter ≤ μHE(frontier)**.

For a regular open bounded set with finite H^{n-1}(frontier),
`perimeter U ≤ μHE[n-1](frontier U)`. -/
theorem perimeter_le_hausdorff_frontier
    {U : Set (E n)} (hU : IsOpen U) (hU_reg : U = interior (closure U))
    (hBdd : Bornology.IsBounded U) (hfin : μHE[n - 1] (frontier U) < ⊤)
    (hn : 2 ≤ n) :
    perimeter U ≤ μHE[n - 1] (frontier U) := by
  set μ : Measure (E n) := perimeterMeasure U with hμ_def
  set ν : Measure (E n) := μHE[n - 1].restrict (frontier U) with hν_def
  have h_perim_finite : perimeter U < ⊤ :=
    perimeter_finite_of_euclideanHausdorff_finite (by linarith) hU.measurableSet hfin
  have hμ_univ : μ Set.univ = perimeter U :=
    (perimeter_eq_variation U h_perim_finite).symm
  have h_abs : μ ≪ ν :=
    perimeterMeasure_absolutelyContinuous_hausdorff hU hBdd h_perim_finite hn
  let f : E n → ℝ≥0∞ := μ.rnDeriv ν
  have hμ_fin : μ Set.univ < ⊤ := by
    rw [hμ_univ] <;> exact h_perim_finite
  have hν_fin : ν Set.univ < ⊤ := by
    simpa [hν_def, Measure.restrict_apply'] using hfin
  letI : IsFiniteMeasure μ := ⟨hμ_fin⟩
  letI : IsFiniteMeasure ν := ⟨hν_fin⟩
  have h_withDensity : μ = ν.withDensity f := by
    haveI : Measure.HaveLebesgueDecomposition μ ν :=
      MeasureTheory.Measure.haveLebesgueDecomposition_of_finiteMeasure
    exact (Measure.withDensity_rnDeriv_eq μ ν h_abs).symm
  have h_lintegral : μ Set.univ = ∫⁻ x, f x ∂ν := by
    rw [h_withDensity]
    have h_eq : (ν.withDensity f) Set.univ = ∫⁻ x, f x ∂ν := by
      rw [MeasureTheory.withDensity_apply f MeasurableSet.univ]
      <;> simp
    exact h_eq
  have h_support_frontier : μ ((frontier U)ᶜ) = 0 :=
    perimeterMeasure_support_frontier hU
  let TRB := trueReducedBoundary U
  have hTRB_meas : MeasurableSet TRB := trb_measurable h_perim_finite
  have hTRB_sub_frontier : TRB ⊆ frontier U := by
    intro x hx
    by_contra h
    have h3 : (frontier U)ᶜ ∈ nhds x := IsOpen.mem_nhds isClosed_frontier.isOpen_compl h
    rcases Metric.mem_nhds_iff.mp h3 with ⟨r, hr_pos, h4⟩
    have h5 : μ (ball x r) = 0 := measure_mono_null h4 h_support_frontier
    have h6 : ∀ (r : ℝ), 0 < r → 0 < μ (ball x r) := hx.1
    exact (h6 r hr_pos).ne' h5
  have h_trb_null : μ (frontier U \ TRB) = 0 :=
    perimeterMeasure_compl_trueReducedBoundary U
  have h_trb_concentrated : μ (TRBᶜ) = 0 := by
    have h1 : (frontier U)ᶜ ∪ (frontier U \ TRB) = TRBᶜ := by
      ext x
      simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_diff]
      constructor
      · rintro (h | h)
        · exact fun h2 => h (hTRB_sub_frontier h2)
        · exact h.2
      · intro h
        by_cases h2 : x ∈ frontier U
        · exact Or.inr ⟨h2, h⟩
        · exact Or.inl h2
    have h2 : μ ((frontier U)ᶜ ∪ (frontier U \ TRB)) = 0 := by
      rw [measure_union_null h_support_frontier h_trb_null]
    rw [←h1]
    exact h2
  have h_f_zero_off_trb : ∀ᵐ x ∂ν, x ∉ TRB → f x = 0 := by
    have h3 : μ (TRBᶜ) = 0 := h_trb_concentrated
    have hTRBc_meas : MeasurableSet (TRBᶜ) := hTRB_meas.compl
    have h_eq1 : (ν.withDensity f) (TRBᶜ) = ∫⁻ x, Set.indicator (TRBᶜ) f x ∂ν := by
      rw [MeasureTheory.withDensity_apply f hTRBc_meas]
      exact (MeasureTheory.lintegral_indicator hTRBc_meas f).symm
    have h_eq2 : μ (TRBᶜ) = (ν.withDensity f) (TRBᶜ) := by
      rw [h_withDensity]
    have h4 : ∫⁻ x, Set.indicator (TRBᶜ) f x ∂ν = 0 := by
      rw [←h_eq1, ←h_eq2, h3]
    have hf_meas : Measurable f := Measure.measurable_rnDeriv μ ν
    have h_meas : Measurable (Set.indicator (TRBᶜ) f) := hf_meas.indicator hTRBc_meas
    have h6 : ∀ᵐ x ∂ν, Set.indicator (TRBᶜ) f x = 0 := by
      rwa [lintegral_eq_zero_iff h_meas] at h4
    filter_upwards [h6] with x hx
    intro hx_not
    have h7 : Set.indicator (TRBᶜ) f x = f x := by
      simp [Set.indicator, hx_not]
    rw [h7] at hx
    exact hx
  have h_f_le_one_on_trb : ∀ᵐ x ∂ν, x ∈ TRB → f x ≤ 1 :=
    f_le_one_ae_on_trb hU hU_reg hBdd h_perim_finite hfin hn μ ν f
      hμ_def hν_def rfl h_abs h_withDensity
  have h_f_le_one : ∀ᵐ x ∂ν, f x ≤ 1 := by
    filter_upwards [h_f_zero_off_trb, h_f_le_one_on_trb] with x h0 h1
    by_cases h : x ∈ TRB
    · exact h1 h
    · have h2 : f x = 0 := h0 h
      rw [h2] <;> simp
  have h_main : ∫⁻ x, f x ∂ν ≤ ∫⁻ x, (1 : ℝ≥0∞) ∂ν :=
    lintegral_mono_ae h_f_le_one
  have h_rhs : ∫⁻ x, (1 : ℝ≥0∞) ∂ν = ν Set.univ := by simp
  calc perimeter U
    = μ Set.univ := hμ_univ.symm
    _ = ∫⁻ x, f x ∂ν := h_lintegral
    _ ≤ ∫⁻ x, (1 : ℝ≥0∞) ∂ν := h_main
    _ = ν Set.univ := h_rhs
    _ = μHE[n - 1] (frontier U) := by
      simp [hν_def, Measure.restrict_apply'] <;> rfl

end Geometry.StructureTheorem
