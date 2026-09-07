import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.BlowUpScaling
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.DistributionalDerivative
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.VectorMeasureInner
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.TrueReducedBoundary
import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import Mathlib.Tactic


open MeasureTheory Metric Set ENNReal Filter
open scoped MeasureTheory ContDiff

namespace Geometry.StructureTheorem

open Perimeter

variable {n : ℕ}

/-- Gauss-Green scaling identity:
`∫_{U_{x,r}} fderiv φ · ν = r^{-(n-1)} ∫ φ((y-x)/r) * inner(ν, ν_U(y)) dμ_y`. -/
lemma gauss_green_blowup_identity
    (hn : 2 ≤ n)
    {U : Set (E n)} (hU : IsOpen U) (h_perim_finite : perimeter U < ⊤)
    (x ν : E n) (r : ℝ) (hr_pos : 0 < r)
    (φ : E n → ℝ) (hφ : ContDiff ℝ ∞ φ) (hsupp : HasCompactSupport φ)
    (g : E n → ℝ) (hg_int : Integrable g volume)
    (h_g_def : ∀ z, g z = fderiv ℝ φ z ν) :
    ∫ z in blowUp U x r, g z =
      ((1 / r) ^ (n - 1) : ℝ) *
        ∫ y, (φ ((1 / r) • (y - x))) * inner ℝ ν (measureTheoreticNormal U y)
          ∂(perimeterMeasure U) := by
  let μ := perimeterMeasure U
  let f := measureTheoreticNormal U
  let h : E n → ℝ := fun y => inner ℝ ν (f y)
  let ψ : E n → ℝ := fun y => φ ((1 / r) • (y - x))
  have hr_ne : r ≠ 0 := hr_pos.ne'

  have hψ_smooth : ContDiff ℝ ∞ ψ := by
    have hconst : ContDiff ℝ ∞ (fun (_ : E n) => x) := contDiff_const
    have h2 : ContDiff ℝ ∞ (fun y : E n => y - x) := contDiff_id.sub hconst
    have h3 : ContDiff ℝ ∞ (fun y : E n => (1 / r) • (y - x)) := by
      have h5 : ContDiff ℝ ∞ (fun (_ : E n) => (1 / r : ℝ)) := contDiff_const
      exact h5.smul h2
    exact hφ.comp h3

  have hR_exists : ∃ (R : ℝ), 0 < R ∧ tsupport φ ⊆ closedBall (0 : E n) R :=
    Bornology.IsBounded.subset_closedBall_lt hsupp.isCompact.isBounded 0 0
  rcases hR_exists with ⟨R, hR_pos, hR_tsupp⟩
  have hR_supp : Function.support φ ⊆ closedBall (0 : E n) R := subset_closure.trans hR_tsupp

  have hψ_supp : HasCompactSupport ψ := by
    let H : E n → E n := fun z => x + r • z
    have hH_cont : Continuous H := by fun_prop
    have h_preimage_eq : (fun y : E n => (1 / r) • (y - x)) ⁻¹' (closedBall (0 : E n) R)
        = H '' (closedBall (0 : E n) R) := by
      ext y
      simp only [Set.mem_preimage, Set.mem_image, H]
      constructor
      · intro h4
        refine ⟨(1 / r) • (y - x), h4, ?_⟩
        simp [H, smul_smul, hr_ne] <;> abel
      · rintro ⟨z, hz, rfl⟩
        have h10 : (1 / r) • (x + r • z - x) = z := by
          simp [smul_smul, hr_ne] <;> abel
        rw [h10]; exact hz
    have h1 : Function.support ψ ⊆ (fun y : E n => (1 / r) • (y - x)) ⁻¹' (closedBall (0 : E n) R) := by
      intro y hy
      have h2 : φ ((1 / r) • (y - x)) ≠ 0 := by simpa [ψ, Function.mem_support] using hy
      have h3 : (1 / r) • (y - x) ∈ Function.support φ := by
        simpa [Function.mem_support] using h2
      exact hR_supp h3
    rw [h_preimage_eq] at h1
    have h4 : IsCompact (H '' (closedBall (0 : E n) R)) :=
      (isCompact_closedBall _ _).image hH_cont
    have h5 : IsClosed (H '' (closedBall (0 : E n) R)) := h4.isClosed
    exact h4.of_isClosed_subset isClosed_closure (closure_minimal h1 h5)

  let vec : E n → E n := fun y => ψ y • ν
  have hvec_smooth : ContDiff ℝ ∞ vec := hψ_smooth.smul contDiff_const
  have hvec_supp : HasCompactSupport vec := by
    have h1 : Function.support vec ⊆ Function.support ψ := by
      intro y hy
      have h_ne : ψ y • ν ≠ 0 := by simpa [vec, Function.mem_support] using hy
      have hψ_ne : ψ y ≠ 0 := by
        intro h; rw [h] at h_ne; simpa using h_ne
      exact Function.mem_support.mpr hψ_ne
    have h1' : Function.support vec ⊆ tsupport ψ := h1.trans subset_closure
    have h2 : IsCompact (closure (Function.support vec)) :=
      hψ_supp.of_isClosed_subset isClosed_closure (closure_minimal h1' isClosed_closure)
    exact h2

  have hμ_fin : μ Set.univ < ⊤ := by
    have h_eq : perimeter U = μ Set.univ := perimeter_eq_variation U h_perim_finite
    rw [h_eq] at h_perim_finite; exact h_perim_finite
  haveI : IsFiniteMeasure μ := ⟨hμ_fin⟩

  have hvec_int : Integrable vec μ := by
    have h_cont : Continuous vec := hvec_smooth.continuous
    have hK : IsCompact (tsupport vec) := hvec_supp
    have h_bdd_img : BddAbove (Set.image (fun x => ‖vec x‖) (tsupport vec)) :=
      hK.bddAbove_image h_cont.norm.continuousOn
    rcases h_bdd_img with ⟨C0, hC0⟩
    let C := max C0 0
    have hC_nonneg : 0 ≤ C := by positivity
    have h_on : ∀ x ∈ tsupport vec, ‖vec x‖ ≤ C := by
      intro x hx
      have h5 : ‖vec x‖ ∈ Set.image (fun x => ‖vec x‖) (tsupport vec) := ⟨x, hx, rfl⟩
      have h6 : ‖vec x‖ ≤ C0 := hC0 h5
      exact le_trans h6 (le_max_left _ _)
    have h_bdd_all : ∀ x, ‖vec x‖ ≤ C := by
      intro x
      by_cases hx : x ∈ tsupport vec
      · exact h_on x hx
      · have h7 : vec x = 0 := by
          have h8 : x ∉ Function.support vec := fun h9 => hx (subset_closure h9)
          simpa [Function.mem_support] using h8
        rw [h7] <;> simp [hC_nonneg]
    have h_int : IntegrableOn vec Set.univ μ :=
      IntegrableOn.of_bound hμ_fin h_cont.measurable.aestronglyMeasurable C
        (by filter_upwards with x using h_bdd_all x)
    simpa using h_int

  have h1 : ∫ᵛ y, vec y ∂[innerBilinear; distributionalDerivative U] =
      ∫ y in U, divergence vec y :=
    Perimeter.distributionalDerivative_integral_formula U h_perim_finite vec hvec_smooth hvec_supp
  have h2 : ∫ᵛ y, vec y ∂[innerBilinear; distributionalDerivative U] =
      ∫ y, inner ℝ (vec y) (f y) ∂μ :=
    distributionalDerivative_integral_eq_inner U h_perim_finite hvec_int
  have hdiv : divergence vec = fun y => fderiv ℝ ψ y ν :=
    divergence_smul_const hψ_smooth
  have h4 : ∀ y, inner ℝ (vec y) (f y) = ψ y * h y := by
    intro y
    simp [vec, h, inner_smul_left] <;> ring
  have h_green : ∫ y in U, fderiv ℝ ψ y ν = ∫ y, ψ y * h y ∂μ := by
    have h5 : ∫ y in U, divergence vec y = ∫ y in U, fderiv ℝ ψ y ν := by
      rw [hdiv]
    have h6 : ∫ y, inner ℝ (vec y) (f y) ∂μ = ∫ y, ψ y * h y ∂μ := by
      congr 1 with y; exact h4 y
    exact h5.symm.trans (h1.symm.trans (h2.trans h6))

  have h_cov : ∫ z in blowUp U x r, g z =
      (1 / r) ^ n * ∫ y in U, g ((1 / r) • (y - x)) := by
    let c : ℝ := 1 / r
    let G : E n → E n := fun y => c • (y - x)
    let G' : E n → (E n →L[ℝ] E n) := fun _ => c • ContinuousLinearMap.id ℝ (E n)
    have hc_pos : 0 < c := by positivity
    have hc_ne : c ≠ 0 := hc_pos.ne'
    have hG_fd : ∀ y ∈ U, HasFDerivWithinAt G (G' y) U y := by
      intro y _
      have h1 : HasFDerivAt (fun z : E n => z - x) (ContinuousLinearMap.id ℝ (E n)) y :=
        (hasFDerivAt_id y).sub_const x
      have h2 : HasFDerivAt G (G' y) y := h1.const_smul c
      exact h2.hasFDerivWithinAt
    have hG_inj : Set.InjOn G U := by
      intro y1 _ y2 _ h
      have h4 : c • (y1 - x) = c • (y2 - x) := h
      have h5 : y1 - x = y2 - x := by
        apply_fun (fun z : E n => (1 / c) • z) at h4
        simpa [smul_smul, hc_ne] using h4
      simpa using h5
    have hG_image : G '' U = blowUp U x r := by
      have hG_eq : G = blowUpMap x r := by
        funext y
        dsimp only [G, blowUpMap] <;> rfl
      rw [hG_eq] <;> rfl
    have h_det : ∀ y, |(G' y).det| = c ^ n := by
      intro y
      have h1 : (G' y).toLinearMap = c • (1 : E n →ₗ[ℝ] E n) := by
        ext v; simp [G', ContinuousLinearMap.id_apply]
      have h2 : (G' y).det = (G' y).toLinearMap.det := by rfl
      rw [h2, h1, LinearMap.det_smul]
      have h3 : Module.finrank ℝ (E n) = n := by simp [E]
      simpa [h3, abs_of_pos (pow_pos hc_pos n)] using rfl
    have h_cov1 : ∫ z in G '' U, g z =
        ∫ y in U, |(G' y).det| * g (G y) :=
      integral_image_eq_integral_abs_det_fderiv_smul volume hU.measurableSet hG_fd hG_inj g
    rw [hG_image] at h_cov1
    have h3 : ∀ y, |(G' y).det| * g (G y) = (c ^ n : ℝ) * g (G y) := by
      intro y; rw [h_det y]
    have h4 : ∫ y in U, |(G' y).det| * g (G y) = ∫ y in U, (c ^ n : ℝ) * g (G y) := by
      congr with y; exact h3 y
    rw [h_cov1, h4, integral_const_mul] <;> rfl

  have h_g_eq : ∀ y, g ((1 / r) • (y - x)) = r * fderiv ℝ ψ y ν := by
    intro y
    let z := (1 / r) • (y - x)
    have h_fd : HasFDerivAt φ (fderiv ℝ φ z) z :=
      (hφ.differentiable (by norm_num)).differentiableAt.hasFDerivAt
    have hG_fd : HasFDerivAt (fun y : E n => (1 / r) • (y - x))
        ((1 / r : ℝ) • ContinuousLinearMap.id ℝ (E n)) y := by
      exact (hasFDerivAt_id y).sub_const x |>.const_smul (1 / r)
    have h_comp : HasFDerivAt ψ ((fderiv ℝ φ z).comp ((1 / r : ℝ) • ContinuousLinearMap.id ℝ (E n))) y :=
      h_fd.comp y hG_fd
    have h_eq : (fderiv ℝ φ z).comp ((1 / r : ℝ) • ContinuousLinearMap.id ℝ (E n))
        = (1 / r : ℝ) • fderiv ℝ φ z := by
      ext v
      simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply] <;> ring
    have h4 : HasFDerivAt ψ ((1 / r : ℝ) • fderiv ℝ φ z) y := by
      simpa [h_eq] using h_comp
    have h5 : fderiv ℝ ψ y = (1 / r : ℝ) • fderiv ℝ φ z := h4.fderiv
    have h6 : fderiv ℝ ψ y ν = (1 / r) * fderiv ℝ φ z ν := by
      rw [h5] <;> simp
    have h7 : g z = fderiv ℝ φ z ν := h_g_def z
    rw [h7, h6] <;> field_simp [hr_ne] <;> ring

  have h_step2 : ∫ y in U, g ((1 / r) • (y - x)) = r * ∫ y in U, fderiv ℝ ψ y ν := by
    have h : ∫ y in U, g ((1 / r) • (y - x)) = ∫ y in U, r * fderiv ℝ ψ y ν := by
      congr 1 with y; exact h_g_eq y
    rw [h, integral_const_mul]

  have h_main : ∫ z in blowUp U x r, g z =
      ((1 / r) ^ (n - 1) : ℝ) * ∫ y, ψ y * h y ∂μ := by
    rw [h_cov, h_step2, h_green]
    have hpow : (1 / r) ^ n * r = (1 / r) ^ (n - 1) := by
      have hn_pos : 0 < n := by omega
      have h : n = Nat.succ (n - 1) := by omega
      rw [h]
      simp [pow_succ] <;> field_simp [hr_ne] <;> ring
    have h : (1 / r) ^ n * (r * ∫ y, ψ y * h y ∂μ) =
        ((1 / r) ^ (n - 1) : ℝ) * ∫ y, ψ y * h y ∂μ := by
      rw [← mul_assoc, hpow]
    exact h
  simpa [ψ, h] using h_main

/-- Sequential version of `integral_convergence_of_symmDiff`: if symmetric differences
converge to zero in volume on compact sets, then integrals of compactly supported continuous
functions converge. -/
lemma integral_convergence_of_symmDiff_seq
    {f : E n → ℝ} (hf_cont : Continuous f) (hf_support : HasCompactSupport f)
    {A : ℕ → Set (E n)} {B : Set (E n)}
    (hA_meas : ∀ k, MeasurableSet (A k)) (hB_meas : MeasurableSet B)
    {K : Set (E n)} (hK : IsCompact K) (h_support : Function.support f ⊆ K)
    (h_conv : Tendsto (fun k => volume (symmDiff (A k) B ∩ K)) atTop (nhds 0)) :
    Tendsto (fun k => ∫ x in A k, f x) atTop (nhds (∫ x in B, f x)) := by
  have h_full : Integrable f volume := hf_cont.integrable_of_hasCompactSupport hf_support
  have h_bdd : ∃ C, 0 < C ∧ ∀ x, |f x| ≤ C := by
    have h1 : BddAbove (Set.image (fun x => |f x|) (tsupport f)) :=
      hf_support.isCompact.bddAbove_image ((continuous_abs.comp hf_cont).continuousOn)
    rcases h1 with ⟨C0, hC0⟩
    let C := max C0 1
    have hC_pos : 0 < C := by positivity
    have h2 : ∀ x ∈ tsupport f, |f x| ≤ C := by
      intro x hx
      have h3 : |f x| ∈ Set.image (fun x => |f x|) (tsupport f) := ⟨x, hx, rfl⟩
      have h4 : |f x| ≤ C0 := hC0 h3
      exact le_trans h4 (le_max_left _ _)
    have h3 : ∀ x, |f x| ≤ C := by
      intro x
      by_cases h4 : x ∈ tsupport f
      · exact h2 x h4
      · have h5 : f x = 0 := by
          have h6 : x ∉ Function.support f := fun h7 => h4 (subset_closure h7)
          simpa [Function.mem_support] using h6
        rw [h5, abs_zero] <;> exact hC_pos.le
    exact ⟨C, hC_pos, h3⟩
  rcases h_bdd with ⟨C, hC_pos, hC_bound⟩
  have h_main : ∀ k, |(∫ x in A k, f x) - (∫ x in B, f x)| ≤
      C * (volume (symmDiff (A k) B ∩ K)).toReal := by
    intro k
    let gA := Set.indicator (A k) f
    let gB := Set.indicator B f
    let indA := Set.indicator (A k) (fun _ : E n => (1 : ℝ))
    let indB := Set.indicator B (fun _ : E n => (1 : ℝ))
    let indS := Set.indicator (symmDiff (A k) B ∩ K) (fun _ : E n => (1 : ℝ))
    let S := symmDiff (A k) B ∩ K
    have hS_meas : MeasurableSet S := (hA_meas k).symmDiff hB_meas |>.inter hK.measurableSet
    have h_gA_int : Integrable gA volume := h_full.indicator (hA_meas k)
    have h_gB_int : Integrable gB volume := h_full.indicator hB_meas
    have h1 : ∫ x in A k, f x = ∫ x, gA x := by
      have h_eq1 : (∫ x in A k, f x) = ∫ x, Set.indicator (A k) f x := by exact Eq.symm (integral_indicator (hA_meas k))
      have h_eq2 : gA = Set.indicator (A k) f := by rfl
      rw [h_eq1, h_eq2]
    have h2 : ∫ x in B, f x = ∫ x, gB x := by
      have h_eq1 : (∫ x in B, f x) = ∫ x, Set.indicator B f x := by exact Eq.symm (integral_indicator hB_meas)
      have h_eq2 : gB = Set.indicator B f := by rfl
      rw [h_eq1, h_eq2]
    have h_eq : (∫ x in A k, f x) - (∫ x in B, f x) = ∫ x, (gA x - gB x) := by
      rw [h1, h2, ← integral_sub h_gA_int h_gB_int] <;> rfl
    rw [h_eq]
    have h_gA_eq : ∀ x, gA x = indA x * f x := by
      intro x; by_cases h : x ∈ A k <;> simp [gA, indA, Set.indicator_apply, h] <;> ring
    have h_gB_eq : ∀ x, gB x = indB x * f x := by
      intro x; by_cases h : x ∈ B <;> simp [gB, indB, Set.indicator_apply, h] <;> ring
    have h_pointwise : ∀ x, |gA x - gB x| ≤ C * indS x := by
      intro x
      by_cases h6 : x ∈ S
      · have h6' : x ∈ symmDiff (A k) B ∧ x ∈ K := h6
        have h_indS1 : indS x = 1 := by
          simp [indS, Set.indicator_apply, h6']
        have h_diff : |indA x - indB x| ≤ 1 := by
          have h1 : indA x = 0 ∨ indA x = 1 := by simp [indA, Set.indicator] <;> tauto
          have h2 : indB x = 0 ∨ indB x = 1 := by simp [indB, Set.indicator] <;> tauto
          rcases h1 with (h1 | h1) <;> rcases h2 with (h2 | h2) <;> simp [h1, h2] <;> linarith
        have h_eq : gA x - gB x = (indA x - indB x) * f x := by
          rw [h_gA_eq x, h_gB_eq x] <;> ring
        rw [h_indS1]
        rw [h_eq, abs_mul]
        have h7 : |indA x - indB x| * |f x| ≤ 1 * |f x| := by gcongr
        have h8 : 1 * |f x| ≤ C := by simpa using hC_bound x
        linarith
      · have h7 : x ∉ symmDiff (A k) B ∨ x ∉ K := by tauto
        have h_prod : gA x - gB x = 0 := by
          rcases h7 with (h7 | h7)
          · have h8 : indA x = indB x := by
              have h9 : x ∉ symmDiff (A k) B := h7
              simp only [indA, indB, symmDiff, Set.mem_union, Set.mem_diff, Set.indicator] at h9 ⊢
              by_cases h10 : x ∈ A k <;> by_cases h11 : x ∈ B <;> simp [h10, h11] at h9 ⊢ <;> tauto
            have h9 : gA x = gB x := by
              rw [h_gA_eq x, h_gB_eq x, h8] <;> ring
            rw [h9] <;> ring
          · have h8 : x ∉ Function.support f := fun h9 => h7 (h_support h9)
            have h9 : f x = 0 := by simpa [Function.mem_support] using h8
            have h10 : gA x = 0 := by rw [h_gA_eq x, h9] <;> ring
            have h11 : gB x = 0 := by rw [h_gB_eq x, h9] <;> ring
            rw [h10, h11] <;> ring
        have h_indS0 : indS x = 0 := by
          have h_notinS : x ∉ S := h6
          have h : indS x = Set.indicator S (fun _ => (1 : ℝ)) x := by rfl
          rw [h]
          simp [Set.indicator_apply, h_notinS]
        rw [h_prod, h_indS0] <;> simp [hC_pos.le]
    have h_int_abs : Integrable (fun x => |gA x - gB x|) volume := (h_gA_int.sub h_gB_int).abs
    have h_fin : volume S < ⊤ := by
      have h_sub : S ⊆ K := inter_subset_right
      exact lt_of_le_of_lt (measure_mono h_sub) hK.measure_lt_top
    letI : IsFiniteMeasure (volume.restrict S) := ⟨by simpa [Measure.restrict_apply'] using h_fin⟩
    have h_indS_on : IntegrableOn (fun _ => (1 : ℝ)) S volume := integrableOn_const
    have h_indS_int : Integrable indS volume :=
      (MeasureTheory.integrable_indicator_iff hS_meas).mpr h_indS_on
    have h_int_C : Integrable (fun x => C * indS x) volume := h_indS_int.const_mul C
    have h3 : ∫ x, |gA x - gB x| ≤ ∫ x, C * indS x :=
      integral_mono h_int_abs h_int_C (by intro x; exact h_pointwise x)
    have h4 : ∫ x, C * indS x = C * (volume S).toReal := by
      rw [MeasureTheory.integral_const_mul]
      have h9 : ∫ x, indS x = (volume S).toReal := by
        rw [integral_indicator hS_meas]
        simp [indS, integral_const] <;> rfl
      rw [h9] <;> ring
    calc
      |∫ x, (gA x - gB x)|
        ≤ ∫ x, |gA x - gB x| := abs_integral_le_integral_abs
      _ ≤ ∫ x, C * indS x := h3
      _ = C * (volume S).toReal := h4
  have h1 : ContinuousAt ENNReal.toReal 0 := ENNReal.continuousAt_toReal (by simp)
  have h_conv' : Tendsto (fun k => (volume (symmDiff (A k) B ∩ K)).toReal) atTop (nhds 0) :=
    h1.tendsto.comp h_conv
  have h_tendsto : Tendsto (fun k => C * (volume (symmDiff (A k) B ∩ K)).toReal) atTop (nhds 0) := by
    simpa [mul_zero] using h_conv'.const_mul C
  have h_zero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0) := tendsto_const_nhds
  have h_ev1 : ∀ᶠ k in atTop, (0 : ℝ) ≤ |(∫ x in A k, f x) - (∫ x in B, f x)| := by
    filter_upwards with _ <;> exact abs_nonneg _
  have h_ev2 : ∀ᶠ k in atTop, |(∫ x in A k, f x) - (∫ x in B, f x)| ≤ C * (volume (symmDiff (A k) B ∩ K)).toReal := by
    filter_upwards with k; exact h_main k
  have h_abs_tendsto : Tendsto (fun k => |(∫ x in A k, f x) - (∫ x in B, f x)|) atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' h_zero h_tendsto h_ev1 h_ev2
  have h_main_tendsto : Tendsto (fun k => (∫ x in A k, f x) - (∫ x in B, f x)) atTop (nhds 0) :=
    (tendsto_zero_iff_abs_tendsto_zero (fun k => (∫ x in A k, f x) - (∫ x in B, f x))).mpr h_abs_tendsto
  have h_final : Tendsto (fun k => ∫ x in A k, f x) atTop (nhds (∫ x in B, f x)) := by
    have h_add : Tendsto (fun k => (∫ x in A k, f x) - (∫ x in B, f x) + (∫ x in B, f x))
        atTop (nhds (0 + (∫ x in B, f x))) :=
      h_main_tendsto.add tendsto_const_nhds
    have h_simp : (0 + (∫ x in B, f x)) = (∫ x in B, f x) := by ring
    rw [h_simp] at h_add
    have h_eq : (fun k : ℕ => (∫ x in A k, f x) - (∫ x in B, f x) + (∫ x in B, f x)) =
        (fun k : ℕ => ∫ x in A k, f x) := by
      funext k; ring
    rw [h_eq] at h_add
    exact h_add
  exact h_final

/-- **Orientation for blow-up limit from scalar comparability**. -/
theorem orientation_from_scalar_comparability
    (hn : 2 ≤ n)
    {U : Set (E n)} (hU : IsOpen U) (h_perim_finite : perimeter U < ⊤)
    (x : E n) (ν : E n) (hx_trb : x ∈ trueReducedBoundary U)
    (hν : measureTheoreticNormal U x = ν)
    (h_upper : ∃ (C : ℝ) (r0 : ℝ), 0 < C ∧ 0 < r0 ∧
        ∀ r, 0 < r → r < r0 →
          perimeterMeasure U (closedBall x r) ≤ ENNReal.ofReal (C * r ^ (n - 1)))
    (h_inner_lebesgue : Tendsto (fun r : ℝ =>
        (∫ y in closedBall x r, inner ℝ ν (measureTheoreticNormal U y) ∂(perimeterMeasure U)) /
          (perimeterMeasure U (closedBall x r)).toReal)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 1))
    {F : Set (E n)} (hF : MeasurableSet F)
    {r_seq : ℕ → ℝ} (hr_pos : ∀ k, 0 < r_seq k)
    (hr_tendsto : Tendsto r_seq atTop (nhds 0))
    (h_conv : ∀ K, IsCompact K →
      Tendsto (fun k => volume (symmDiff (blowUp U x (r_seq k)) F ∩ K)) atTop (nhds 0)) :
    ∀ (φ : E n → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∀ x, 0 ≤ φ x) → 0 ≤ ∫ x in F, fderiv ℝ φ x ν := by
  let μ := perimeterMeasure U
  let f := measureTheoreticNormal U
  let h : E n → ℝ := fun y => inner ℝ ν (f y)

  have hν_norm_one : ‖ν‖ = 1 := by
    have h1 : ‖f x‖ = 1 := hx_trb.2
    have h2 : f x = ν := hν
    rw [h2] at h1; exact h1

  have hf_norm_one : ∀ᵐ y ∂μ, ‖f y‖ = 1 := norm_measureTheoreticNormal_eq_one h_perim_finite
  have h_one_minus_h_nonneg : ∀ᵐ y ∂μ, 0 ≤ 1 - h y := by
    filter_upwards [hf_norm_one] with y hy
    have h5 : h y ≤ ‖ν‖ * ‖f y‖ := real_inner_le_norm ν (f y)
    rw [hν_norm_one, hy] at h5
    have h6 : h y ≤ 1 := by simpa using h5
    linarith

  have hμ_fin : μ Set.univ < ⊤ := by
    have h_eq : perimeter U = μ Set.univ := perimeter_eq_variation U h_perim_finite
    rw [h_eq] at h_perim_finite; exact h_perim_finite
  haveI : IsFiniteMeasure μ := ⟨hμ_fin⟩

  have h_meas : Measurable h := by
    have hf_meas : Measurable f := measureTheoreticNormal_measurable h_perim_finite
    have h_cont1 : Continuous (fun z : E n => inner ℝ ν z) := by fun_prop
    exact h_cont1.measurable.comp hf_meas

  have h_int_h : Integrable h μ := by
    have h_norm_bound1 : ∀ᵐ y ∂μ, |h y| ≤ 1 := by
      filter_upwards [hf_norm_one] with y hy
      have h5 : |h y| ≤ ‖ν‖ * ‖f y‖ := abs_real_inner_le_norm ν (f y)
      rw [hν_norm_one, hy] at h5
      simpa using h5
    have h_norm_bound : ∀ᵐ y ∂(μ.restrict Set.univ), |h y| ≤ 1 := by
      simpa [ae_restrict_mem] using h_norm_bound1
    have h_on : IntegrableOn h Set.univ μ := IntegrableOn.of_bound hμ_fin h_meas.aestronglyMeasurable 1 h_norm_bound
    simpa using h_on

  rcases h_upper with ⟨C, r0, hC_pos, hr0_pos, h_upper_bound⟩

  intro φ hφ hsupp φ_nonneg

  -- Support radius R and bound Mφ
  have hR_exists : ∃ (R : ℝ), 0 < R ∧ tsupport φ ⊆ closedBall (0 : E n) R :=
    Bornology.IsBounded.subset_closedBall_lt hsupp.isCompact.isBounded 0 0
  rcases hR_exists with ⟨R, hR_pos, hR_tsupp⟩
  have hR_supp : Function.support φ ⊆ closedBall (0 : E n) R := subset_closure.trans hR_tsupp

  have hMφ_exists : ∃ (Mφ : ℝ), 0 ≤ Mφ ∧ ∀ z, |φ z| ≤ Mφ := by
    let K := tsupport φ
    have hK : IsCompact K := hsupp
    have h_cont : Continuous φ := hφ.continuous
    have h_bdd : BddAbove (Set.image (fun x => |φ x|) K) :=
      hK.bddAbove_image ((continuous_abs.comp h_cont).continuousOn)
    rcases h_bdd with ⟨M0, hM0⟩
    let M := max M0 0
    have hM_nonneg : 0 ≤ M := by positivity
    have h_on_K : ∀ x ∈ K, |φ x| ≤ M := by
      intro x hx
      have h5 : |φ x| ∈ Set.image (fun x => |φ x|) K := ⟨x, hx, rfl⟩
      have h6 : |φ x| ≤ M0 := hM0 h5
      exact le_trans h6 (le_max_left _ _)
    refine ⟨M, hM_nonneg, fun x => ?_⟩
    by_cases hx : x ∈ K
    · exact h_on_K x hx
    · have h7 : φ x = 0 := by
        have h8 : x ∉ Function.support φ := fun h9 => hx (subset_closure h9)
        simpa [Function.mem_support] using h8
      rw [h7] <;> simp [hM_nonneg]
  rcases hMφ_exists with ⟨Mφ, hMφ_nonneg, hφ_bound⟩

  let g : E n → ℝ := fun y => fderiv ℝ φ y ν

  have hg_int : Integrable g volume := by
    have h_cont : Continuous g := by
      have h1 : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by norm_num)
      fun_prop
    have h_supp_g : Function.support g ⊆ tsupport φ := by
      intro y hy
      by_contra h2
      have h3 : y ∉ tsupport φ := h2
      have h4 : IsOpen (tsupport φ)ᶜ := isClosed_closure.isOpen_compl
      have h5 : y ∈ (tsupport φ)ᶜ := h3
      have h6 : ∀ᶠ z in nhds y, φ z = 0 := by
        filter_upwards [h4.mem_nhds h5] with z hz
        have h7 : z ∉ Function.support φ := fun h8 => hz (subset_closure h8)
        simpa [Function.mem_support] using h7
      have h7 : fderiv ℝ φ y = 0 := by
        have h9 : HasFDerivAt (fun (_ : E n) => (0 : ℝ)) (0 : E n →L[ℝ] ℝ) y := by
          exact hasFDerivAt_const (c := (0 : ℝ)) (x := y)
        have h10 : φ =ᶠ[nhds y] (fun (_ : E n) => (0 : ℝ)) := h6
        have h8 : HasFDerivAt φ (0 : E n →L[ℝ] ℝ) y :=
          h9.congr_of_eventuallyEq h10
        exact h8.fderiv
      have h9 : g y = 0 := by simp [g, h7]
      exact hy h9
    have hg_supp : HasCompactSupport g := by
      have h2 : IsCompact (tsupport φ) := hsupp
      have h3 : IsClosed (tsupport φ) := isClosed_closure
      have h4 : IsCompact (closure (Function.support g)) :=
        h2.of_isClosed_subset isClosed_closure (closure_minimal h_supp_g h3)
      exact h4
    exact h_cont.integrable_of_hasCompactSupport hg_supp

  -- Scalar comparability at scale R*r
  have h_tendsto_mul : Tendsto (fun r : ℝ => r * R) (nhds 0) (nhds 0) := by
    have h_cont : ContinuousAt (fun r : ℝ => r * R) 0 := by fun_prop
    have h : Tendsto (fun r : ℝ => r * R) (nhds 0) (nhds (0 * R)) := h_cont.tendsto
    have h2 : (0 * R : ℝ) = 0 := by ring
    rw [h2] at h
    exact h
  have h_scale_map : Tendsto (fun r : ℝ => r * R) (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin 0 (Set.Ioi 0)) := by
    have h1 : Tendsto (fun r : ℝ => r * R) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds h_tendsto_mul
    have h2 : ∀ᶠ r in nhdsWithin 0 (Set.Ioi 0), (r * R) ∈ Set.Ioi (0 : ℝ) := by
      filter_upwards [self_mem_nhdsWithin] with r hr
      exact mul_pos hr hR_pos
    rw [tendsto_nhdsWithin_iff]
    exact ⟨h1, h2⟩

  have h_avg_h_R : Tendsto (fun r : ℝ =>
      (∫ y in closedBall x (r * R), h y ∂μ) / (μ (closedBall x (r * R))).toReal)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) :=
    h_inner_lebesgue.comp h_scale_map

  -- Average of (1-h) tends to 0
  have h_avg_one_minus_h_R : Tendsto (fun r : ℝ =>
      (∫ y in closedBall x (r * R), (1 - h y) ∂μ) / (μ (closedBall x (r * R))).toReal)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h_eventually_eq : ∀ᶠ r in nhdsWithin 0 (Set.Ioi 0),
        (1 - (∫ y in closedBall x (r * R), h y ∂μ) / (μ (closedBall x (r * R))).toReal) =
        (∫ y in closedBall x (r * R), (1 - h y) ∂μ) / (μ (closedBall x (r * R))).toReal := by
      filter_upwards [self_mem_nhdsWithin] with r hr
      have hμ_pos : 0 < μ (closedBall x (r * R)) := by
        have h1 : 0 < μ (ball x (r * R)) := hx_trb.1 (r * R) (mul_pos hr hR_pos)
        exact h1.trans_le (measure_mono ball_subset_closedBall)
      have hμ_ne_top : μ (closedBall x (r * R)) ≠ ⊤ :=
        ne_top_of_le_ne_top hμ_fin.ne (measure_mono (Set.subset_univ _))
      have hdenom_pos : 0 < (μ (closedBall x (r * R))).toReal :=
        ENNReal.toReal_pos hμ_pos.ne' hμ_ne_top
      have h_int_h_on : IntegrableOn h (closedBall x (r * R)) μ := h_int_h.integrableOn
      have h_int1 : IntegrableOn (fun y => (1 : ℝ)) (closedBall x (r * R)) μ :=
        (integrable_const (1 : ℝ)).integrableOn
      have h_sub : ∫ y in closedBall x (r * R), (1 - h y) ∂μ =
          (μ (closedBall x (r * R))).toReal - ∫ y in closedBall x (r * R), h y ∂μ := by
        have h5 : ∫ y in closedBall x (r * R), (1 - h y) ∂μ =
            ∫ y in closedBall x (r * R), (1 : ℝ) ∂μ - ∫ y in closedBall x (r * R), h y ∂μ :=
          integral_sub h_int1 h_int_h_on
        rw [h5]
        have h6 : ∫ y in closedBall x (r * R), (1 : ℝ) ∂μ = (μ (closedBall x (r * R))).toReal := by
          simp [integral_const] <;> rfl
        rw [h6]
      rw [h_sub]
      field_simp [hdenom_pos.ne'] <;> ring
    have h_one : Tendsto (fun _ : ℝ => (1 : ℝ)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := tendsto_const_nhds
    have h_tendsto_sub : Tendsto (fun r : ℝ =>
        1 - (∫ y in closedBall x (r * R), h y ∂μ) / (μ (closedBall x (r * R))).toReal)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 - 1)) := h_one.sub h_avg_h_R
    have h_zero : (1 - 1 : ℝ) = 0 := by norm_num
    rw [h_zero] at h_tendsto_sub
    exact h_tendsto_sub.congr' h_eventually_eq

  -- For each k, Gauss-Green identity + decomposition
  have h_main_eq : ∀ k, ∫ z in blowUp U x (r_seq k), g z =
      ((1 / r_seq k) ^ (n - 1) : ℝ) *
        ((∫ y, (φ ((1 / r_seq k) • (y - x))) ∂μ) -
         ∫ y, (φ ((1 / r_seq k) • (y - x))) * (1 - h y) ∂μ) := by
    intro k
    let r := r_seq k
    have hr_pos' : 0 < r := hr_pos k
    let ψ : E n → ℝ := fun y => φ ((1 / r) • (y - x))

    have h_identity : ∫ z in blowUp U x r, g z =
        ((1 / r) ^ (n - 1) : ℝ) * ∫ y, ψ y * h y ∂μ :=
      gauss_green_blowup_identity hn hU h_perim_finite x ν r hr_pos' φ hφ hsupp g hg_int (fun z => rfl)

    have hψ_cont : Continuous ψ := by
      have hconst : ContDiff ℝ ∞ (fun (_ : E n) => x) := contDiff_const
      have h2 : ContDiff ℝ ∞ (fun y : E n => y - x) := contDiff_id.sub hconst
      have h3 : ContDiff ℝ ∞ (fun y : E n => (1 / r) • (y - x)) := by
        have h5 : ContDiff ℝ ∞ (fun (_ : E n) => (1 / r : ℝ)) := contDiff_const
        exact h5.smul h2
      exact (hφ.comp h3).continuous
    have hψ_supp : HasCompactSupport ψ := by
      let H : E n → E n := fun z => x + r • z
      have hH_cont : Continuous H := by fun_prop
      have h_preimage_eq : (fun y : E n => (1 / r) • (y - x)) ⁻¹' (closedBall (0 : E n) R)
          = H '' (closedBall (0 : E n) R) := by
        ext y
        simp only [Set.mem_preimage, Set.mem_image, H]
        constructor
        · intro h4
          refine ⟨(1 / r) • (y - x), h4, ?_⟩
          simp [H, smul_smul, hr_pos'.ne'] <;> abel
        · rintro ⟨z, hz, rfl⟩
          have h10 : (1 / r) • (x + r • z - x) = z := by
            simp [smul_smul, hr_pos'.ne'] <;> abel
          rw [h10]; exact hz
      have h1 : Function.support ψ ⊆ (fun y : E n => (1 / r) • (y - x)) ⁻¹' (closedBall (0 : E n) R) := by
        intro y hy
        have h2 : φ ((1 / r) • (y - x)) ≠ 0 := by simpa [ψ, Function.mem_support] using hy
        have h3 : (1 / r) • (y - x) ∈ Function.support φ := by
          simpa [Function.mem_support] using h2
        exact hR_supp h3
      rw [h_preimage_eq] at h1
      have h4 : IsCompact (H '' (closedBall (0 : E n) R)) :=
        (isCompact_closedBall _ _).image hH_cont
      have h5 : IsClosed (H '' (closedBall (0 : E n) R)) := h4.isClosed
      exact h4.of_isClosed_subset isClosed_closure (closure_minimal h1 h5)
    have h_int_ψ : Integrable ψ μ := hψ_cont.integrable_of_hasCompactSupport hψ_supp
    have h_int_1mh : Integrable (fun y : E n => 1 - h y) μ := by
      exact (integrable_const (1 : ℝ)).sub h_int_h
    have h_int_ψh : Integrable (fun y : E n => ψ y * h y) μ := by
      have h_bound : ∀ᵐ y ∂μ, |ψ y * h y| ≤ (Mφ + 1) * |h y| := by
        filter_upwards with y
        have h9 : |ψ y| ≤ Mφ := hφ_bound ((1 / r) • (y - x))
        calc |ψ y * h y|
          = |ψ y| * |h y| := by rw [abs_mul]
        _ ≤ Mφ * |h y| := by gcongr
        _ ≤ (Mφ + 1) * |h y| := by gcongr <;> linarith
      have h_abs : Integrable (fun y : E n => |h y|) μ := h_int_h.abs
      have h_scaled : Integrable (fun y : E n => (Mφ + 1) * |h y|) μ := h_abs.const_mul (Mφ + 1)
      have h_meas : Measurable (fun y : E n => ψ y * h y) := by fun_prop
      exact Integrable.mono' h_scaled h_meas.aestronglyMeasurable h_bound
    have h_int_ψ1mh : Integrable (fun y : E n => ψ y * (1 - h y)) μ := by
      have h_bound : ∀ᵐ y ∂μ, |ψ y * (1 - h y)| ≤ (Mφ + 1) * |1 - h y| := by
        filter_upwards with y
        have h9 : |ψ y| ≤ Mφ := hφ_bound ((1 / r) • (y - x))
        calc |ψ y * (1 - h y)|
          = |ψ y| * |1 - h y| := by rw [abs_mul]
        _ ≤ Mφ * |1 - h y| := by gcongr
        _ ≤ (Mφ + 1) * |1 - h y| := by gcongr <;> linarith
      have h_abs : Integrable (fun y : E n => |1 - h y|) μ := h_int_1mh.abs
      have h_scaled : Integrable (fun y : E n => (Mφ + 1) * |1 - h y|) μ := h_abs.const_mul (Mφ + 1)
      have h_meas : Measurable (fun y : E n => ψ y * (1 - h y)) := by fun_prop
      exact Integrable.mono' h_scaled h_meas.aestronglyMeasurable h_bound
    have h_decomp : ∫ y, ψ y * h y ∂μ = (∫ y, ψ y ∂μ) - ∫ y, ψ y * (1 - h y) ∂μ := by
      have h3 : ∀ y, ψ y * h y = ψ y - ψ y * (1 - h y) := by intro y; ring
      have h4 : ∫ y, ψ y * h y ∂μ = ∫ y, (ψ y - ψ y * (1 - h y)) ∂μ := by
        congr with y; exact h3 y
      rw [h4]
      have h5 : Integrable (fun y : E n => ψ y - ψ y * (1 - h y)) μ :=
        h_int_ψ.sub h_int_ψ1mh
      exact integral_sub h_int_ψ h_int_ψ1mh
    rw [h_identity, h_decomp] <;> ring

  -- Main term non-negative
  have h_main_nonneg : ∀ k, 0 ≤ ((1 / r_seq k) ^ (n - 1) : ℝ) *
      ∫ y, (φ ((1 / r_seq k) • (y - x))) ∂μ := by
    intro k
    let r := r_seq k
    have hr_pos' : 0 < r := hr_pos k
    let ψ : E n → ℝ := fun y => φ ((1 / r) • (y - x))
    have hψ_nonneg : ∀ᵐ y ∂μ, 0 ≤ ψ y := by
      filter_upwards with y
      exact φ_nonneg ((1 / r) • (y - x))
    have hψ_cont : Continuous ψ := by
      have hconst : ContDiff ℝ ∞ (fun (_ : E n) => x) := contDiff_const
      have h2 : ContDiff ℝ ∞ (fun y : E n => y - x) := contDiff_id.sub hconst
      have h3 : ContDiff ℝ ∞ (fun y : E n => (1 / r) • (y - x)) := by
        have h5 : ContDiff ℝ ∞ (fun (_ : E n) => (1 / r : ℝ)) := contDiff_const
        exact h5.smul h2
      exact (hφ.comp h3).continuous
    have hψ_supp : HasCompactSupport ψ := by
      let H : E n → E n := fun z => x + r • z
      have hH_cont : Continuous H := by fun_prop
      have h_preimage_eq : (fun y : E n => (1 / r) • (y - x)) ⁻¹' (closedBall (0 : E n) R)
          = H '' (closedBall (0 : E n) R) := by
        ext y
        simp only [Set.mem_preimage, Set.mem_image, H]
        constructor
        · intro h4
          refine ⟨(1 / r) • (y - x), h4, ?_⟩
          simp [H, smul_smul, hr_pos'.ne'] <;> abel
        · rintro ⟨z, hz, rfl⟩
          have h10 : (1 / r) • (x + r • z - x) = z := by
            simp [smul_smul, hr_pos'.ne'] <;> abel
          rw [h10]; exact hz
      have h1 : Function.support ψ ⊆ (fun y : E n => (1 / r) • (y - x)) ⁻¹' (closedBall (0 : E n) R) := by
        intro y hy
        have h2 : φ ((1 / r) • (y - x)) ≠ 0 := by simpa [ψ, Function.mem_support] using hy
        have h3 : (1 / r) • (y - x) ∈ Function.support φ := by
          simpa [Function.mem_support] using h2
        exact hR_supp h3
      rw [h_preimage_eq] at h1
      have h4 : IsCompact (H '' (closedBall (0 : E n) R)) :=
        (isCompact_closedBall _ _).image hH_cont
      have h5 : IsClosed (H '' (closedBall (0 : E n) R)) := h4.isClosed
      exact h4.of_isClosed_subset isClosed_closure (closure_minimal h1 h5)
    have h_int_ψ : Integrable ψ μ := hψ_cont.integrable_of_hasCompactSupport hψ_supp
    have h_int_nonneg : 0 ≤ ∫ y, ψ y ∂μ := integral_nonneg_of_ae hψ_nonneg
    have h_scale_pos : 0 < ((1 / r) ^ (n - 1) : ℝ) := by positivity
    exact mul_nonneg h_scale_pos.le h_int_nonneg

  -- Error term tends to 0
  have h_error_tendsto : Tendsto (fun k : ℕ =>
      ((1 / r_seq k) ^ (n - 1) : ℝ) *
        ∫ y, (φ ((1 / r_seq k) • (y - x))) * (1 - h y) ∂μ)
      atTop (nhds 0) := by
    have h_eventually_small : ∀ᶠ k in atTop, r_seq k * R < r0 := by
      have h : ∀ᶠ k in atTop, r_seq k < r0 / R := hr_tendsto (Iio_mem_nhds (by positivity))
      filter_upwards [h] with k hk
      have h5 : r_seq k * R < (r0 / R) * R := by gcongr
      have h6 : (r0 / R) * R = r0 := by field_simp [hR_pos.ne'] <;> ring
      rw [h6] at h5; exact h5

    have h_tendsto_avg : Tendsto (fun k : ℕ =>
        (∫ y in closedBall x (r_seq k * R), (1 - h y) ∂μ) / (μ (closedBall x (r_seq k * R))).toReal)
        atTop (nhds 0) := by
      have h1 : ∀ᶠ k in atTop, r_seq k ∈ Set.Ioi (0 : ℝ) := by
        filter_upwards with k; exact hr_pos k
      exact h_avg_one_minus_h_R.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within r_seq hr_tendsto h1)

    have h_bound : ∀ᶠ k in atTop,
        |((1 / r_seq k) ^ (n - 1) : ℝ) * ∫ y, (φ ((1 / r_seq k) • (y - x))) * (1 - h y) ∂μ| ≤
        Mφ * (C * R ^ (n - 1)) *
          ((∫ y in closedBall x (r_seq k * R), (1 - h y) ∂μ) / (μ (closedBall x (r_seq k * R))).toReal) := by
      filter_upwards [h_eventually_small] with k hk_small
      let r := r_seq k
      have hr_pos' : 0 < r := hr_pos k
      have hr_ne : r ≠ 0 := hr_pos'.ne'
      let ψ : E n → ℝ := fun y => φ ((1 / r) • (y - x))

      have h_supp_ψ : ∀ᵐ y ∂μ, ψ y ≠ 0 → y ∈ closedBall x (r * R) := by
        filter_upwards with y hy
        have h1 : (1 / r) • (y - x) ∈ Function.support φ := by
          simpa [ψ, Function.mem_support] using hy
        have h2 : (1 / r) • (y - x) ∈ closedBall (0 : E n) R := hR_supp h1
        have h3 : ‖(1 / r) • (y - x)‖ ≤ R := by
          have h4 : dist ((1 / r) • (y - x)) (0 : E n) ≤ R := mem_closedBall.mp h2
          have h5 : dist ((1 / r) • (y - x)) (0 : E n) = ‖(1 / r) • (y - x)‖ := by rw [dist_zero_right]
          rw [h5] at h4; exact h4
        have h4 : dist y x ≤ r * R := by
          have h5 : ‖(1 / r) • (y - x)‖ = (1 / r) * dist y x := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
            <;> simp [dist_eq_norm] <;> ring
          rw [h5] at h3
          have h6 : (1 / r) * dist y x ≤ R := h3
          have h7 : dist y x ≤ r * R := by
            calc dist y x
              = r * ((1 / r) * dist y x) := by field_simp [hr_ne] <;> ring
            _ ≤ r * R := by gcongr
          exact h7
        simpa [mem_closedBall] using h4

      have h_main : ∫ y, ψ y * (1 - h y) ∂μ = ∫ y in closedBall x (r * R), ψ y * (1 - h y) ∂μ := by
        let F : E n → ℝ := fun y => ψ y * (1 - h y)
        have h9 : ∀ᵐ y ∂μ, F y = Set.indicator (closedBall x (r * R)) F y := by
          filter_upwards [h_supp_ψ] with y hy
          by_cases h6 : y ∈ closedBall x (r * R)
          · simp [h6, Set.indicator_apply, F]
          · have h7 : ψ y = 0 := by
              by_contra h8; exact h6 (hy h8)
            have hF : F y = 0 := by simp [F, h7]
            simp [hF, Set.indicator_apply, h6]
        have h10 : ∫ y, F y ∂μ = ∫ y, Set.indicator (closedBall x (r * R)) F y ∂μ :=
          integral_congr_ae h9
        rw [h10, integral_indicator measurableSet_closedBall]

      have hμRR_pos : 0 < μ (closedBall x (r * R)) := by
        have h1 : 0 < μ (ball x (r * R)) := hx_trb.1 (r * R) (mul_pos hr_pos' hR_pos)
        exact h1.trans_le (measure_mono ball_subset_closedBall)
      have hμRR_ne_top : μ (closedBall x (r * R)) ≠ ⊤ :=
        ne_top_of_le_ne_top hμ_fin.ne (measure_mono (Set.subset_univ _))
      have hdenom_pos : 0 < (μ (closedBall x (r * R))).toReal :=
        ENNReal.toReal_pos hμRR_pos.ne' hμRR_ne_top

      have h_upper_R : μ (closedBall x (r * R)) ≤ ENNReal.ofReal (C * (r * R) ^ (n - 1)) :=
        h_upper_bound (r * R) (mul_pos hr_pos' hR_pos) hk_small

      have h_scale_bound : ((1 / r) ^ (n - 1) : ℝ) * (μ (closedBall x (r * R))).toReal ≤ C * R ^ (n - 1) := by
        have h1 : (μ (closedBall x (r * R))).toReal ≤ (ENNReal.ofReal (C * (r * R) ^ (n - 1))).toReal :=
          ENNReal.toReal_le_toReal hμRR_ne_top ENNReal.ofReal_ne_top |>.mpr h_upper_R
        have h2 : (ENNReal.ofReal (C * (r * R) ^ (n - 1))).toReal = C * (r * R) ^ (n - 1) := by
          rw [ENNReal.toReal_ofReal (by positivity)]
        have h3 : (μ (closedBall x (r * R))).toReal ≤ C * (r * R) ^ (n - 1) := by
          rw [h2] at h1; exact h1
        have h4 : ((1 / r) ^ (n - 1) : ℝ) * (μ (closedBall x (r * R))).toReal ≤
            ((1 / r) ^ (n - 1) : ℝ) * (C * (r * R) ^ (n - 1)) := by gcongr
        have h5 : ((1 / r) ^ (n - 1) : ℝ) * (C * (r * R) ^ (n - 1)) = C * R ^ (n - 1) := by
          have h6 : (1 / r) ^ (n - 1) * (r * R) ^ (n - 1) = R ^ (n - 1) := by
            have h7 : (1 / r) * (r * R) = R := by field_simp [hr_ne] <;> ring
            rw [← mul_pow, h7]
          calc
            ((1 / r) ^ (n - 1) : ℝ) * (C * (r * R) ^ (n - 1))
              = C * (((1 / r) ^ (n - 1) : ℝ) * (r * R) ^ (n - 1)) := by ring
            _ = C * R ^ (n - 1) := by rw [h6]
        rw [h5] at h4
        exact h4

      have h_abs_bound : |∫ y, ψ y * (1 - h y) ∂μ| ≤
          Mφ * ∫ y in closedBall x (r * R), (1 - h y) ∂μ := by
        rw [h_main]
        have h5 : |∫ y in closedBall x (r * R), ψ y * (1 - h y) ∂μ| ≤
            ∫ y in closedBall x (r * R), |ψ y * (1 - h y)| ∂μ := abs_integral_le_integral_abs
        have h7 : ∀ y, |ψ y| ≤ Mφ := by intro y; exact hφ_bound ((1 / r) • (y - x))
        have h_bound_all : ∀ᵐ y ∂μ, |ψ y * (1 - h y)| ≤ Mφ * (1 - h y) := by
          filter_upwards [h_one_minus_h_nonneg] with y hy
          have h9 : |ψ y * (1 - h y)| = |ψ y| * |1 - h y| := by rw [abs_mul]
          rw [h9, abs_of_nonneg hy]
          exact mul_le_mul_of_nonneg_right (h7 y) hy
        have h_int_1mh_local : Integrable (fun y : E n => 1 - h y) μ := (integrable_const 1).sub h_int_h
        have h_int_bound : Integrable (fun y : E n => Mφ * (1 - h y)) μ := h_int_1mh_local.const_mul Mφ
        have hψ_cont_local : Continuous ψ := by
          have hconst : ContDiff ℝ ∞ (fun (_ : E n) => x) := contDiff_const
          have h2 : ContDiff ℝ ∞ (fun y : E n => y - x) := contDiff_id.sub hconst
          have h3 : ContDiff ℝ ∞ (fun y : E n => (1 / r) • (y - x)) := by
            have h5 : ContDiff ℝ ∞ (fun (_ : E n) => (1 / r : ℝ)) := contDiff_const
            exact h5.smul h2
          exact (hφ.comp h3).continuous
        have h_meas1mh : Measurable (fun y : E n => 1 - h y) := h_meas.const_sub 1
        have h_meas2 : Measurable (fun y : E n => |ψ y * (1 - h y)|) := by
          simpa [Real.norm_eq_abs] using
            (hψ_cont_local.measurable.mul h_meas1mh |>.norm)
        have h_bound_all' : ∀ᵐ y ∂μ, ‖(|ψ y * (1 - h y)|)‖ ≤ Mφ * (1 - h y) := by
          filter_upwards [h_bound_all] with y hy
          simpa [Real.norm_eq_abs] using hy
        have h_int_abs2 : Integrable (fun y : E n => |ψ y * (1 - h y)|) μ :=
          Integrable.mono' h_int_bound h_meas2.aestronglyMeasurable h_bound_all'
        have h_int_abs_on : IntegrableOn (fun y : E n => |ψ y * (1 - h y)|) (closedBall x (r * R)) μ :=
          h_int_abs2.integrableOn
        have h_int_M_on : IntegrableOn (fun y : E n => Mφ * (1 - h y)) (closedBall x (r * R)) μ :=
          h_int_bound.integrableOn
        have h9 : ∫ y in closedBall x (r * R), |ψ y * (1 - h y)| ∂μ ≤
            ∫ y in closedBall x (r * R), Mφ * (1 - h y) ∂μ :=
          MeasureTheory.setIntegral_mono_ae h_int_abs_on h_int_M_on h_bound_all
        have h10 : ∫ y in closedBall x (r * R), Mφ * (1 - h y) ∂μ =
            Mφ * ∫ y in closedBall x (r * R), (1 - h y) ∂μ := by
          rw [integral_const_mul]
        rw [h10] at h9
        exact h5.trans h9

      have h_avg_nonneg : 0 ≤
          ((∫ y in closedBall x (r * R), (1 - h y) ∂μ) / (μ (closedBall x (r * R))).toReal) := by
        have h11_on : ∀ᵐ y ∂(μ.restrict (closedBall x (r * R))), 0 ≤ 1 - h y := by
          have h : ∀ᵐ y ∂μ, y ∈ closedBall x (r * R) → 0 ≤ 1 - h y := by
            filter_upwards [h_one_minus_h_nonneg] with y hy _; exact hy
          exact (ae_restrict_iff' measurableSet_closedBall).mpr h
        have h_int_nonneg : 0 ≤ ∫ y in closedBall x (r * R), (1 - h y) ∂μ :=
          integral_nonneg_of_ae h11_on
        exact div_nonneg h_int_nonneg hdenom_pos.le

      have h_scale_pos : 0 < ((1 / r) ^ (n - 1) : ℝ) := by positivity
      have h_abs_mul : ∀ (a b : ℝ), 0 ≤ a → |a * b| = a * |b| := by
        intro a b ha
        rw [abs_mul, abs_of_nonneg ha]
      have h_mul_bound : ((1 / r) ^ (n - 1) : ℝ) * (μ (closedBall x (r * R))).toReal *
            ((∫ y in closedBall x (r * R), (1 - h y) ∂μ) / (μ (closedBall x (r * R))).toReal) ≤
          (C * R ^ (n - 1)) *
            ((∫ y in closedBall x (r * R), (1 - h y) ∂μ) / (μ (closedBall x (r * R))).toReal) :=
        mul_le_mul_of_nonneg_right h_scale_bound h_avg_nonneg
      have h_eq2 : (μ (closedBall x (r * R))).toReal *
            ((∫ y in closedBall x (r * R), (1 - h y) ∂μ) / (μ (closedBall x (r * R))).toReal) =
          ∫ y in closedBall x (r * R), (1 - h y) ∂μ := by
        field_simp [hdenom_pos.ne'] <;> ring
      let avg := (∫ y in closedBall x (r * R), (1 - h y) ∂μ) / (μ (closedBall x (r * R))).toReal
      have h_step1 : ((1 / r) ^ (n - 1) : ℝ) * (Mφ * ∫ y in closedBall x (r * R), (1 - h y) ∂μ) =
          Mφ * (((1 / r) ^ (n - 1) : ℝ) * (μ (closedBall x (r * R))).toReal * avg) := by
        have h9 : ((1 / r) ^ (n - 1) : ℝ) * (Mφ * ∫ y in closedBall x (r * R), (1 - h y) ∂μ) =
            Mφ * ((1 / r) ^ (n - 1) : ℝ) * (∫ y in closedBall x (r * R), (1 - h y) ∂μ) := by ring
        rw [h9]
        have h10 : (∫ y in closedBall x (r * R), (1 - h y) ∂μ) =
            (μ (closedBall x (r * R))).toReal * avg := h_eq2.symm
        rw [h_eq2.symm] <;> ring
      have h_step2 : Mφ * (((1 / r) ^ (n - 1) : ℝ) * (μ (closedBall x (r * R))).toReal * avg) ≤
          Mφ * (C * R ^ (n - 1)) * avg := by
        have h11 : Mφ * (((1 / r) ^ (n - 1) : ℝ) * (μ (closedBall x (r * R))).toReal * avg) ≤
            Mφ * ((C * R ^ (n - 1)) * avg) :=
          mul_le_mul_of_nonneg_left h_mul_bound (by positivity)
        have h12 : Mφ * ((C * R ^ (n - 1)) * avg) = Mφ * (C * R ^ (n - 1)) * avg := by ring
        rw [h12] at h11
        exact h11
      calc |((1 / r) ^ (n - 1) : ℝ) * ∫ y, ψ y * (1 - h y) ∂μ|
        = ((1 / r) ^ (n - 1) : ℝ) * |∫ y, ψ y * (1 - h y) ∂μ| :=
          h_abs_mul ((1 / r) ^ (n - 1) : ℝ) (∫ y, ψ y * (1 - h y) ∂μ) h_scale_pos.le
      _ ≤ ((1 / r) ^ (n - 1) : ℝ) * (Mφ * ∫ y in closedBall x (r * R), (1 - h y) ∂μ) := by
          gcongr <;> exact h_abs_bound
      _ = Mφ * (((1 / r) ^ (n - 1) : ℝ) * (μ (closedBall x (r * R))).toReal * avg) := h_step1
      _ ≤ Mφ * (C * R ^ (n - 1)) * avg := h_step2

    have h_zero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0) := tendsto_const_nhds
    have h_ev1 : ∀ᶠ k in atTop, (0 : ℝ) ≤
        |((1 / r_seq k) ^ (n - 1) : ℝ) * ∫ y, (φ ((1 / r_seq k) • (y - x))) * (1 - h y) ∂μ| := by
      filter_upwards with _; exact abs_nonneg _
    have h_tendsto_scaled : Tendsto (fun k : ℕ => Mφ * (C * R ^ (n - 1)) *
          ((∫ y in closedBall x (r_seq k * R), (1 - h y) ∂μ) / (μ (closedBall x (r_seq k * R))).toReal))
        atTop (nhds 0) := by
      simpa [mul_zero] using h_tendsto_avg.const_mul (Mφ * (C * R ^ (n - 1)))
    have h_abs_tendsto : Tendsto (fun k : ℕ =>
        |((1 / r_seq k) ^ (n - 1) : ℝ) * ∫ y, (φ ((1 / r_seq k) • (y - x))) * (1 - h y) ∂μ|)
        atTop (nhds 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le' h_zero h_tendsto_scaled h_ev1 h_bound
    exact (tendsto_zero_iff_abs_tendsto_zero _).mpr h_abs_tendsto

  -- L¹ convergence of integrals
  have h_blowup_tendsto : Tendsto (fun k => ∫ z in blowUp U x (r_seq k), g z)
      atTop (nhds (∫ z in F, g z)) := by
    have hg_cont : Continuous g := by
      have h1 : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by norm_num)
      fun_prop
    have h_supp_g : Function.support g ⊆ tsupport φ := by
      intro y hy
      by_contra h2
      have h3 : y ∉ tsupport φ := h2
      have h4 : IsOpen (tsupport φ)ᶜ := isClosed_closure.isOpen_compl
      have h5 : y ∈ (tsupport φ)ᶜ := h3
      have h6 : ∀ᶠ z in nhds y, φ z = 0 := by
        filter_upwards [h4.mem_nhds h5] with z hz
        have h7 : z ∉ Function.support φ := fun h8 => hz (subset_closure h8)
        simpa [Function.mem_support] using h7
      have h7 : fderiv ℝ φ y = 0 := by
        have h9 : HasFDerivAt (fun (_ : E n) => (0 : ℝ)) (0 : E n →L[ℝ] ℝ) y := by
          exact hasFDerivAt_const (c := (0 : ℝ)) (x := y)
        have h10 : φ =ᶠ[nhds y] (fun (_ : E n) => (0 : ℝ)) := h6
        have h8 : HasFDerivAt φ (0 : E n →L[ℝ] ℝ) y :=
          h9.congr_of_eventuallyEq h10
        exact h8.fderiv
      have h9 : g y = 0 := by simp [g, h7]
      exact hy h9
    have hg_support : HasCompactSupport g := by
      have h2 : IsCompact (tsupport φ) := hsupp
      have h3 : IsClosed (tsupport φ) := isClosed_closure
      have h4 : IsCompact (closure (Function.support g)) :=
        h2.of_isClosed_subset isClosed_closure (closure_minimal h_supp_g h3)
      exact h4
    have hA_meas : ∀ k, MeasurableSet (blowUp U x (r_seq k)) := by
      intro k
      have hr_ne : r_seq k ≠ 0 := (hr_pos k).ne'
      let H := blowUpMapHomeomorph x hr_ne
      have h_open : IsOpen (H '' U) := H.isOpenMap _ hU
      exact h_open.measurableSet
    let K := tsupport φ
    have hK : IsCompact K := hsupp
    exact integral_convergence_of_symmDiff_seq hg_cont hg_support hA_meas hF hK h_supp_g
      (h_conv K hK)

  -- Final conclusion
  have h_neg_error_tendsto : Tendsto (fun k : ℕ =>
      -(((1 / r_seq k) ^ (n - 1) : ℝ) *
        ∫ y, (φ ((1 / r_seq k) • (y - x))) * (1 - h y) ∂μ))
      atTop (nhds 0) := by
    have h_neg : Tendsto (fun k : ℕ =>
        -(((1 / r_seq k) ^ (n - 1) : ℝ) *
          ∫ y, (φ ((1 / r_seq k) • (y - x))) * (1 - h y) ∂μ))
        atTop (nhds (-0 : ℝ)) := h_error_tendsto.neg
    have h2 : (-0 : ℝ) = 0 := by norm_num
    rw [h2] at h_neg
    exact h_neg
  have h_final : 0 ≤ ∫ z in F, g z := by
    have h_seq : ∀ k, ∫ z in blowUp U x (r_seq k), g z =
        ((1 / r_seq k) ^ (n - 1) : ℝ) * ∫ y, (φ ((1 / r_seq k) • (y - x))) ∂μ -
        ((1 / r_seq k) ^ (n - 1) : ℝ) * ∫ y, (φ ((1 / r_seq k) • (y - x))) * (1 - h y) ∂μ := by
      intro k
      rw [h_main_eq k] <;> ring
    have h_main_seq : ∀ k, 0 ≤ ((1 / r_seq k) ^ (n - 1) : ℝ) * ∫ y, (φ ((1 / r_seq k) • (y - x))) ∂μ :=
      h_main_nonneg
    have h_ge : ∀ k, -(((1 / r_seq k) ^ (n - 1) : ℝ) * ∫ y, (φ ((1 / r_seq k) • (y - x))) * (1 - h y) ∂μ) ≤
        ∫ z in blowUp U x (r_seq k), g z := by
      intro k
      rw [h_seq k]
      linarith [h_main_seq k]
    exact le_of_tendsto_of_tendsto' h_neg_error_tendsto h_blowup_tendsto h_ge

  simpa [g] using h_final

end Geometry.StructureTheorem
