import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.TrueReducedBoundary
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.VectorMeasureInner
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.BlowUpScaling
import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import Mathlib.Tactic


/-!
# M3: Orientation condition at reduced boundary (Lebesgue point version)

At a true reduced boundary point x with normal ν, for every non-negative smooth
compactly supported test function φ with φ(0) > 0, the integral
`∫_{blowUp U x r} fderiv φ ν` is non-negative for all sufficiently small r > 0.

Requires Lebesgue differentiation at x and perimeter measure density bounds.
-/

open MeasureTheory Metric Set ENNReal Filter
open scoped MeasureTheory ContDiff
open Geometry.StructureTheorem (blowUp)

namespace Geometry.Perimeter

variable {n : ℕ}

/-- Helper: change of variables for integrals over blow-ups.
`∫ z in blowUp U x r, g z = (1/r)^n * ∫ y in U, g((1/r)•(y-x))`. -/
lemma blowUp_integral_change_of_vars
    {U : Set (E n)} {x : E n} {r : ℝ} (hr : 0 < r)
    (hU_meas : MeasurableSet U) (g : E n → ℝ) (hg_int : Integrable g volume) :
    ∫ z in blowUp U x r, g z =
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
    ext z
    simp only [Set.mem_image, G, blowUp, StructureTheorem.blowUpMap]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, by simp [G, show c = 1 / r from rfl]⟩
    · rintro ⟨y, hy, h_eq⟩
      exact ⟨y, hy, h_eq⟩

  have h_det : ∀ y, |(G' y).det| = c ^ n := by
    intro y
    have h1 : (G' y).toLinearMap = c • (1 : E n →ₗ[ℝ] E n) := by
      ext v
      simp [G', ContinuousLinearMap.id_apply]
      <;> ring
    have h2 : (G' y).det = (G' y).toLinearMap.det := by rfl
    rw [h2, h1, LinearMap.det_smul]
    have h3 : Module.finrank ℝ (E n) = n := by simp [E]
    simpa [h3, abs_of_pos (pow_pos hc_pos n)] using rfl

  have h_cov : ∫ z in G '' U, g z =
      ∫ y in U, |(G' y).det| * g (G y) :=
    integral_image_eq_integral_abs_det_fderiv_smul volume hU_meas hG_fd hG_inj g

  rw [hG_image] at h_cov
  have h3 : ∀ y, |(G' y).det| * g (G y) = (c ^ n : ℝ) * g (G y) := by
    intro y; rw [h_det y]
  have h4 : ∫ y in U, |(G' y).det| * g (G y) = ∫ y in U, (c ^ n : ℝ) * g (G y) := by
    congr with y; exact h3 y
  rw [h_cov, h4, integral_const_mul]
  <;> rfl


/-- Hypothesis: Lebesgue differentiation of perimeter measure at x. -/
@[irreducible] def LebesgueDiffHyp (U : Set (E n)) (x : E n) : Prop :=
  ∀ (g : E n → ℝ), Integrable g (perimeterMeasure U) →
    Tendsto (fun r : ℝ =>
      (∫ y in closedBall x r, g y ∂(perimeterMeasure U)) /
        (perimeterMeasure U (closedBall x r)).toReal)
    (nhdsWithin 0 (Set.Ioi 0)) (nhds (g x))

/-- Hypothesis: lower density bound for perimeter measure at x. -/
@[irreducible] def DensityLowerBound (U : Set (E n)) (x : E n) (n : ℕ) : Prop :=
  ∃ (c : ℝ) (R : ℝ), 0 < c ∧ 0 < R ∧
    ∀ r, 0 < r → r < R →
      perimeterMeasure U (ball x r) ≥ ENNReal.ofReal (c * r ^ (n - 1))

/-- Hypothesis: upper density bound for perimeter measure at x. -/
@[irreducible] def DensityUpperBound (U : Set (E n)) (x : E n) (n : ℕ) : Prop :=
  ∃ (C : ℝ) (R : ℝ), 0 < C ∧ 0 < R ∧
    ∀ r, 0 < r → r < R →
      perimeterMeasure U (ball x r) ≤ ENNReal.ofReal (C * r ^ (n - 1))

/-- Structure bundling all hypotheses for the reduced boundary orientation theorem,
    to prevent kernel whnf normalization timeout on the complex dependent types. -/
structure OrientationHypotheses (n : ℕ) (U : Set (E n)) (x : E n) (ν : E n) : Prop where
  hU : IsOpen U
  hn : 2 ≤ n
  h_perim_finite : perimeter U < ⊤
  hx : x ∈ trueReducedBoundary U
  hν : measureTheoreticNormal U x = ν
  h_lebesgue : LebesgueDiffHyp U x
  h_density_lower : DensityLowerBound U x n
  h_density_upper : DensityUpperBound U x n

/-- Conclusion type for reduced boundary orientation, isolated to avoid whnf timeout. -/
def OrientationConclusion (n : ℕ) (U : Set (E n)) (x : E n) (φ : E n → ℝ) (ν : E n) : Prop :=
  ∃ (r₀ : ℝ), 0 < r₀ ∧ ∀ (r : ℝ), 0 < r → r < r₀ →
    0 ≤ ∫ z in blowUp U x r, fderiv ℝ φ z ν

private lemma orientation_error_bound
    (M c C : ℝ) (hM : 0 < M) (hc : 0 < c) (hC : 0 < C)
    (μbig μsmall : ENNReal)
    (hbig_fin : μbig ≠ ⊤) (hsmall_fin : μsmall ≠ ⊤)
    (hsmall_pos : 0 < μsmall)
    (h_doub : μbig ≤ ENNReal.ofReal C * μsmall)
    (err avg : ℝ)
    (h_err : err ≤ M * avg)
    (h_avg : avg < (c / (4 * M * C + 1)) * μbig.toReal) :
    err < c * μsmall.toReal := by
  have hμ :
      μbig.toReal ≤ C * μsmall.toReal := by
    have hproduct_fin :
        ENNReal.ofReal C * μsmall ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hsmall_fin
    have hreal :
        μbig.toReal ≤
          (ENNReal.ofReal C * μsmall).toReal :=
      (ENNReal.toReal_le_toReal hbig_fin hproduct_fin).mpr h_doub
    have hproduct :
        (ENNReal.ofReal C * μsmall).toReal =
          C * μsmall.toReal := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC.le]
    rwa [hproduct] at hreal
  have hdenom : 0 < 4 * M * C + 1 := by positivity
  have hcoefficient :
      M * (c / (4 * M * C + 1)) * C < c := by
    have heq :
        M * (c / (4 * M * C + 1)) * C =
          c * (M * C) / (4 * M * C + 1) := by
      field_simp [hdenom.ne']
    rw [heq]
    have hlt :
        c * (M * C) <
          c * (4 * M * C + 1) := by
      gcongr
      linarith
    calc
      c * (M * C) / (4 * M * C + 1)
          < c * (4 * M * C + 1) /
              (4 * M * C + 1) := by gcongr
      _ = c := mul_div_cancel_right₀ c hdenom.ne'
  have hsmall_real_pos : 0 < μsmall.toReal :=
    ENNReal.toReal_pos hsmall_pos.ne' hsmall_fin
  calc
    err ≤ M * avg := h_err
    _ < M * ((c / (4 * M * C + 1)) * μbig.toReal) := by
      gcongr
    _ = (M * (c / (4 * M * C + 1))) * μbig.toReal := by ring
    _ ≤ (M * (c / (4 * M * C + 1))) *
        (C * μsmall.toReal) := by gcongr
    _ = (M * (c / (4 * M * C + 1)) * C) *
        μsmall.toReal := by ring
    _ < c * μsmall.toReal :=
      mul_lt_mul_of_pos_right hcoefficient hsmall_real_pos

theorem reduced_boundary_orientation
    {n : ℕ} {U : Set (E n)} {x ν : E n}
    (h : OrientationHypotheses n U x ν)
    (φ : E n → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hsupp : HasCompactSupport φ)
    (φ_nonneg : ∀ x, 0 ≤ φ x)
    (hφ0 : 0 < φ 0) :
    OrientationConclusion n U x φ ν := by
  simp only [OrientationConclusion]
  rcases h with ⟨hU, hn, h_perim_finite, hx, hν, h_lebesgue, h_density_lower, h_density_upper⟩
  let μ := perimeterMeasure U
  let f := measureTheoreticNormal U
  let h : E n → ℝ := fun y => inner ℝ ν (f y)

  have hν_norm_one : ‖ν‖ = 1 := by
    have h1 : ‖f x‖ = 1 := hx.2
    have h2 : f x = ν := hν
    rw [h2] at h1; exact h1

  have hx_h : h x = 1 := by
    have h1 : h x = inner ℝ ν (f x) := by rfl
    have h_fx : f x = measureTheoreticNormal U x := by rfl
    rw [h1, h_fx, hν]
    have h2 : inner ℝ ν ν = ‖ν‖ ^ 2 := by simp [real_inner_self_eq_norm_sq]
    rw [h2, hν_norm_one] <;> norm_num

  have hf_norm_one : ∀ᵐ y ∂μ, ‖f y‖ = 1 := norm_measureTheoreticNormal_eq_one h_perim_finite
  have h_bound : ∀ᵐ y ∂μ, |h y| ≤ 1 := by
    filter_upwards [hf_norm_one] with y hy
    have h5 : |inner ℝ ν (f y)| ≤ ‖ν‖ * ‖f y‖ := abs_real_inner_le_norm ν (f y)
    rw [hν_norm_one, hy] at h5 <;> simpa [h] using h5

  have h_meas : Measurable h := by
    have hf_meas : Measurable f := measureTheoreticNormal_measurable h_perim_finite
    have h_cont1 : Continuous (fun z : E n => inner ℝ ν z) := by fun_prop
    exact h_cont1.measurable.comp hf_meas

  have hμ_fin : μ Set.univ < ⊤ := by
    have h_eq : perimeter U = μ Set.univ := perimeter_eq_variation U h_perim_finite
    rw [h_eq] at h_perim_finite; exact h_perim_finite
  haveI : IsFiniteMeasure μ := ⟨hμ_fin⟩

  have h_int : Integrable h μ := by
    have h_norm_bound : ∀ᵐ y ∂(μ.restrict Set.univ), ‖h y‖ ≤ 1 := by
      simpa [ae_restrict_mem] using h_bound
    have h_on : IntegrableOn h Set.univ μ :=
      IntegrableOn.of_bound hμ_fin h_meas.aestronglyMeasurable 1 h_norm_bound
    simpa using h_on

  have h_abs_int : Integrable (fun y => |h y - 1|) μ := by
    have h2 : Integrable (fun _ : E n => (1 : ℝ)) μ := integrable_const (1 : ℝ)
    exact h_int.sub h2 |>.abs

  -- R: support radius
  have h1_compact : IsCompact (tsupport φ) := hsupp
  have h2_bdd : Bornology.IsBounded (tsupport φ) := h1_compact.isBounded
  have hR_exists : ∃ (R : ℝ), 0 < R ∧ tsupport φ ⊆ closedBall (0 : E n) R :=
    Bornology.IsBounded.subset_closedBall_lt h2_bdd 0 0
  rcases hR_exists with ⟨R, hR_pos, hR_tsupp⟩
  have hR_supp : Function.support φ ⊆ closedBall (0 : E n) R :=
    subset_closure.trans hR_tsupp

  -- δ, cφ: φ ≥ cφ on closedBall 0 δ, with δ ≤ R
  have hδ_orig_exists : ∃ (δ_orig : ℝ), 0 < δ_orig ∧ ∃ (cφ : ℝ), 0 < cφ ∧
      ∀ z ∈ closedBall (0 : E n) δ_orig, cφ ≤ φ z := by
    have h_cont : Continuous φ := hφ.continuous
    have h1 : ∃ (δ' : ℝ), 0 < δ' ∧ ∀ z ∈ ball (0 : E n) δ', φ 0 / 2 ≤ φ z := by
      have h_nhds : ∀ᶠ z in nhds (0 : E n), φ 0 / 2 ≤ φ z :=
        h_cont.continuousAt.eventually (Ici_mem_nhds (by linarith))
      rcases Metric.mem_nhds_iff.mp h_nhds with ⟨δ', hδ'_pos, hδ'⟩
      exact ⟨δ', hδ'_pos, fun z hz => hδ' (by simpa [mem_ball] using hz)⟩
    rcases h1 with ⟨δ', hδ'_pos, hδ'⟩
    let δ_orig := δ' / 2
    have hδ_orig_pos : 0 < δ_orig := by positivity
    have h2 : ∀ z ∈ closedBall (0 : E n) δ_orig, φ 0 / 2 ≤ φ z := by
      intro z hz
      have h3 : ‖z‖ ≤ δ_orig := by simpa [mem_closedBall, dist_zero_right] using hz
      have hδ_orig_eq : δ_orig = δ' / 2 := by rfl
      have h4 : ‖z‖ < δ' := by
        calc ‖z‖ ≤ δ_orig := h3
             _ = δ' / 2 := hδ_orig_eq
             _ < δ' := by linarith [hδ'_pos]
      have h5 : z ∈ ball (0 : E n) δ' := by
        simpa [mem_ball, dist_zero_right] using h4
      exact hδ' z h5
    exact ⟨δ_orig, hδ_orig_pos, φ 0 / 2, by linarith, h2⟩
  rcases hδ_orig_exists with ⟨δ_orig, hδ_orig_pos, cφ, hcφ_pos, hφ_lower_orig⟩
  let δ := min δ_orig R
  have hδ_pos : 0 < δ := by positivity
  have hδ_le_R : δ ≤ R := min_le_right _ _
  have hφ_lower : ∀ z ∈ closedBall (0 : E n) δ, cφ ≤ φ z := by
    intro z hz
    have h5 : z ∈ closedBall (0 : E n) δ_orig := by
      have h6 : δ ≤ δ_orig := min_le_left _ _
      exact closedBall_subset_closedBall h6 hz
    exact hφ_lower_orig z h5

  -- Mφ: bound on |φ|
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
  have h_mul_int : Integrable (fun y => Mφ * |h y - 1|) μ := h_abs_int.const_mul Mφ

  -- Density bounds
  simp only [DensityLowerBound] at h_density_lower
  simp only [DensityUpperBound] at h_density_upper
  rcases h_density_lower with ⟨c, Rl, hc_pos, hRl_pos, h_lower⟩
  rcases h_density_upper with ⟨C, Ru, hC_pos, hRu_pos, h_upper⟩
  have hn_pos : 0 < n - 1 := by omega

  -- Doubling constant
  let C_doub : ℝ := (C / c) * (2 * R / δ) ^ (n - 1)
  have hC_doub_pos : 0 < C_doub := by positivity

  -- Lebesgue differentiation for |h - 1|
  simp only [LebesgueDiffHyp] at h_lebesgue
  have h_leb_abs : Tendsto (fun r : ℝ =>
      (∫ y in closedBall x r, |h y - 1| ∂μ) / (μ (closedBall x r)).toReal)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (|h x - 1|)) :=
    h_lebesgue (fun y => |h y - 1|) h_abs_int
  have h_abs_x : |h x - 1| = 0 := by
    rw [hx_h] <;> norm_num
  rw [h_abs_x] at h_leb_abs

  let ε_target : ℝ := cφ / (4 * Mφ * C_doub + 1)
  have hε_pos : 0 < ε_target := by positivity

  have h_eventually : ∀ᶠ (r : ℝ) in nhdsWithin 0 (Set.Ioi 0),
      (∫ y in closedBall x (r * R), |h y - 1| ∂μ) / (μ (closedBall x (r * R))).toReal < ε_target := by
    have h_tendsto' : Tendsto (fun s : ℝ =>
        (∫ y in closedBall x s, |h y - 1| ∂μ) / (μ (closedBall x s)).toReal)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := h_leb_abs
    have h_scale : Tendsto (fun r : ℝ => r * R) (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin 0 (Set.Ioi 0)) := by
      have h_cont : Continuous (fun r : ℝ => r * R) := by fun_prop
      have h_tendsto_nhds : Tendsto (fun r : ℝ => r * R) (nhds 0) (nhds 0) := by
        have h : ContinuousAt (fun r : ℝ => r * R) 0 := h_cont.continuousAt
        simpa using h.tendsto
      have h_map : ∀ r ∈ Set.Ioi (0 : ℝ), (r * R) ∈ Set.Ioi (0 : ℝ) :=
        fun r hr => mul_pos hr hR_pos
      have h1 : Tendsto (fun r : ℝ => r * R) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
        h_tendsto_nhds.mono_left nhdsWithin_le_nhds
      have h2 : ∀ᶠ r in nhdsWithin 0 (Set.Ioi 0), (r * R) ∈ Set.Ioi (0 : ℝ) := by
        filter_upwards [self_mem_nhdsWithin] with r hr
        exact h_map r hr
      have h2' : Tendsto (fun r : ℝ => r * R) (nhdsWithin 0 (Set.Ioi 0)) (principal (Set.Ioi 0)) :=
        tendsto_principal.mpr h2
      have h_scale' : Tendsto (fun r : ℝ => r * R) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0 ⊓ principal (Set.Ioi 0)) := by
        have h : Tendsto (fun r : ℝ => r * R) (nhdsWithin 0 (Set.Ioi 0) ⊓ nhdsWithin 0 (Set.Ioi 0)) (nhds 0 ⊓ principal (Set.Ioi 0)) :=
          h1.inf h2'
        simpa [inf_idem] using h
      simpa [nhdsWithin] using h_scale'
    exact h_tendsto'.comp h_scale (Iio_mem_nhds hε_pos)

  rcases mem_nhdsWithin.mp h_eventually with ⟨o, ho_open, hxo, ho_sub⟩
  have h_ball : ∃ (r₁ : ℝ), 0 < r₁ ∧ ball (0 : ℝ) r₁ ⊆ o :=
    Metric.isOpen_iff.mp ho_open 0 hxo
  rcases h_ball with ⟨r₁, hr₁_pos, hr₁_sub⟩

  let R_min := min Rl Ru
  have hR_min_pos : 0 < R_min := by positivity
  let r₀ := min r₁ (R_min / (2 * max R 1))
  have hr₀_pos : 0 < r₀ := by positivity

  refine ⟨r₀, hr₀_pos, fun r hr_pos hr_lt => ?_⟩

  have hr_lt_r1 : r < r₁ := by
    have h : r₀ ≤ r₁ := min_le_left _ _
    linarith
  have h_max_pos : 0 < max R 1 := by positivity
  have h_two_max_pos : 0 < 2 * max R 1 := by positivity
  have h_r_lt_div : r < R_min / (2 * max R 1) := by
    have h1 : r₀ ≤ R_min / (2 * max R 1) := min_le_right _ _
    linarith
  have h_r_max_lt : r * max R 1 < R_min / 2 := by
    have h6 : r * max R 1 < (R_min / (2 * max R 1)) * max R 1 := by gcongr
    have h7 : (R_min / (2 * max R 1)) * max R 1 = R_min / 2 := by
      field_simp [h_max_pos.ne'] <;> ring
    rw [h7] at h6; exact h6
  have h_2rR_lt_min : 2 * r * R < R_min := by
    have h8 : 2 * r * R ≤ 2 * r * max R 1 := by gcongr <;> exact le_max_left _ _
    have h9 : 2 * r * max R 1 < R_min := by linarith
    exact h8.trans_lt h9
  have h_rR_le : r * R ≤ r * max R 1 := by
    gcongr <;> exact le_max_left _ _
  have h_rR_lt_min : r * R < R_min := h_rR_le.trans_lt (by linarith)
  have hrR_lt_Rl : r * R < Rl := by
    have h6 : R_min ≤ Rl := min_le_left _ _; linarith
  have hrR_lt_Ru : r * R < Ru := by
    have h6 : R_min ≤ Ru := min_le_right _ _; linarith
  have hrδ_lt_Rl : r * δ < Rl := by
    have h1 : r * δ ≤ r * R := by gcongr <;> exact hδ_le_R
    exact h1.trans_lt hrR_lt_Rl
  have hrδ_lt_Ru : r * δ < Ru := by
    have h1 : r * δ ≤ r * R := by gcongr <;> exact hδ_le_R
    exact h1.trans_lt hrR_lt_Ru

  have hr_in : r ∈ ball (0 : ℝ) r₁ := by
    simpa [mem_ball, abs_of_pos hr_pos] using hr_lt_r1
  have hr_o : r ∈ o := hr₁_sub hr_in
  have hr_Ioi : r ∈ Set.Ioi (0 : ℝ) := hr_pos
  have h_abs_avg : (∫ y in closedBall x (r * R), |h y - 1| ∂μ) / (μ (closedBall x (r * R))).toReal < ε_target :=
    ho_sub ⟨hr_o, hr_Ioi⟩

  -- Gauss-Green formula
  have h_gauss_green : ∀ (ψ : E n → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      ∫ y in U, fderiv ℝ ψ y ν = ∫ y, ψ y * h y ∂μ := by
    intro ψ hψ hsuppψ
    let vec : E n → E n := fun y => ψ y • ν
    have hvec_smooth : ContDiff ℝ ∞ vec := hψ.smul contDiff_const
    have hvec_supp : HasCompactSupport vec := by
      have h1 : Function.support vec ⊆ Function.support ψ := by
        intro y hy
        have h_ne : ψ y • ν ≠ 0 := by simpa [vec, Function.mem_support] using hy
        have hψ_ne : ψ y ≠ 0 := by
          intro h
          rw [h] at h_ne
          simpa using h_ne
        exact Function.mem_support.mpr hψ_ne
      have h1' : Function.support vec ⊆ tsupport ψ := h1.trans subset_closure
      have h2 : IsCompact (closure (Function.support vec)) :=
        hsuppψ.of_isClosed_subset isClosed_closure (closure_minimal h1' isClosed_closure)
      exact h2
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
      distributionalDerivative_integral_formula U h_perim_finite vec hvec_smooth hvec_supp
    have h2 : ∫ᵛ y, vec y ∂[innerBilinear; distributionalDerivative U] =
        ∫ y, inner ℝ (vec y) (f y) ∂μ :=
      Geometry.StructureTheorem.distributionalDerivative_integral_eq_inner U h_perim_finite hvec_int
    have hdiv : divergence vec = fun y => fderiv ℝ ψ y ν :=
      divergence_smul_const hψ
    have h3 : ∀ y, divergence vec y = fderiv ℝ ψ y ν := by
      exact congr_fun hdiv
    have h4 : ∀ y, inner ℝ (vec y) (f y) = ψ y * h y := by
      intro y
      simp [vec, h, inner_smul_left] <;> ring
    have h5 : ∫ y in U, divergence vec y = ∫ y in U, fderiv ℝ ψ y ν := by
      congr 1 with y
    have h6 : ∫ y, inner ℝ (vec y) (f y) ∂μ = ∫ y, ψ y * h y ∂μ := by
      congr 1 with y; exact h4 y
    have h7 : ∫ y in U, fderiv ℝ ψ y ν = ∫ y, ψ y * h y ∂μ :=
      h5.symm.trans (h1.symm.trans (h2.trans h6))
    exact h7

  -- Change of variables setup
  let ψ : E n → ℝ := fun y => φ ((1 / r) • (y - x))
  have hψ_smooth : ContDiff ℝ ∞ ψ := by
    have hconst : ContDiff ℝ ∞ (fun (_ : E n) => x) := contDiff_const
    have h2 : ContDiff ℝ ∞ (fun y : E n => y - x) := contDiff_id.sub hconst
    have h3 : ContDiff ℝ ∞ (fun y : E n => (1 / r) • (y - x)) := by
      have h5 : ContDiff ℝ ∞ (fun (_ : E n) => (1 / r : ℝ)) := contDiff_const
      exact h5.smul h2
    exact hφ.comp h3

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
        simp [H, smul_smul, hr_pos.ne'] <;> abel
      · rintro ⟨z, hz, rfl⟩
        have h10 : (1 / r) • (x + r • z - x) = z := by
          simp [smul_smul, hr_pos.ne'] <;> abel
        rw [h10]
        exact hz
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

  have hU_meas : MeasurableSet U := hU.measurableSet
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

  have h_cov : ∫ z in blowUp U x r, g z =
      (1 / r) ^ n * ∫ y in U, g ((1 / r) • (y - x)) :=
    blowUp_integral_change_of_vars hr_pos hU_meas g hg_int

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
      simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply]
      <;> ring
    have h4 : HasFDerivAt ψ ((1 / r : ℝ) • fderiv ℝ φ z) y := by
      simpa [h_eq] using h_comp
    have h5 : fderiv ℝ ψ y = (1 / r : ℝ) • fderiv ℝ φ z := h4.fderiv
    have h6 : fderiv ℝ ψ y ν = (1 / r) * fderiv ℝ φ z ν := by
      rw [h5] <;> simp
    have h7 : g z = fderiv ℝ φ z ν := by rfl
    rw [h7, h6]
    <;> field_simp [hr_pos.ne'] <;> ring

  have h_step2 : ∫ y in U, g ((1 / r) • (y - x)) = r * ∫ y in U, fderiv ℝ ψ y ν := by
    have h : ∫ y in U, g ((1 / r) • (y - x)) = ∫ y in U, r * fderiv ℝ ψ y ν := by
      congr 1 with y; exact h_g_eq y
    rw [h, integral_const_mul]

  have h_green : ∫ y in U, fderiv ℝ ψ y ν = ∫ y, ψ y * h y ∂μ :=
    h_gauss_green ψ hψ_smooth hψ_supp

  have h_main_eq : ∫ z in blowUp U x r, fderiv ℝ φ z ν =
      ((1 / r) ^ (n - 1) : ℝ) * ∫ y, ψ y * h y ∂μ := by
    rw [h_cov, h_step2, h_green]
    have hpow : (1 / r) ^ n * r = (1 / r) ^ (n - 1) := by
      cases n with
      | zero => contradiction
      | succ n' =>
        simp [pow_succ]
        <;> field_simp [hr_pos.ne'] <;> ring
    have h : (1 / r) ^ n * (r * ∫ y, ψ y * h y ∂μ) =
        ((1 / r) ^ (n - 1) : ℝ) * ∫ y, ψ y * h y ∂μ := by
      rw [← mul_assoc, hpow]
    exact h

  -- Lower bound on ∫ ψ (not ∫ ψ*h, since h can be negative)
  have h_nonneg_ψ : ∀ᵐ y ∂μ, 0 ≤ ψ y := by
    filter_upwards with y
    exact φ_nonneg ((1 / r) • (y - x))
  have h_int_ψ : Integrable ψ μ := by
    have h_cont : Continuous ψ := hψ_smooth.continuous
    have hK : IsCompact (tsupport ψ) := hψ_supp
    have h_bdd_img : BddAbove (Set.image (fun x => ‖ψ x‖) (tsupport ψ)) :=
      hK.bddAbove_image h_cont.norm.continuousOn
    rcases h_bdd_img with ⟨C0, hC0⟩
    let C := max C0 0
    have hC_nonneg : 0 ≤ C := by positivity
    have h_on : ∀ x ∈ tsupport ψ, ‖ψ x‖ ≤ C := by
      intro x hx
      have h5 : ‖ψ x‖ ∈ Set.image (fun x => ‖ψ x‖) (tsupport ψ) := ⟨x, hx, rfl⟩
      have h6 : ‖ψ x‖ ≤ C0 := hC0 h5
      exact le_trans h6 (le_max_left _ _)
    have h_bdd_all : ∀ x, ‖ψ x‖ ≤ C := by
      intro x
      by_cases hx : x ∈ tsupport ψ
      · exact h_on x hx
      · have h7 : ψ x = 0 := by
          have h8 : x ∉ Function.support ψ := fun h9 => hx (subset_closure h9)
          simpa [Function.mem_support] using h8
        rw [h7] <;> simp [hC_nonneg]
    have h_norm_bound2 : ∀ᵐ y ∂(μ.restrict Set.univ), ‖ψ y‖ ≤ C := by
      simpa [ae_restrict_mem] using (by filter_upwards with x using h_bdd_all x)
    have h_on2 : IntegrableOn ψ Set.univ μ :=
      IntegrableOn.of_bound hμ_fin h_cont.measurable.aestronglyMeasurable C h_norm_bound2
    simpa using h_on2
  have h_pos_ψ1 : ∫ y in closedBall x (r * δ), ψ y ∂μ ≤ ∫ y, ψ y ∂μ :=
    setIntegral_le_integral h_int_ψ h_nonneg_ψ

  have h_pos_ψ2 : ∫ y in closedBall x (r * δ), ψ y ∂μ ≥
      cφ * (μ (closedBall x (r * δ))).toReal := by
    have h1 : ∀ y ∈ closedBall x (r * δ), cφ ≤ ψ y := by
      intro y hy
      have h2 : ‖(1 / r) • (y - x)‖ ≤ δ := by
        have h3 : dist y x ≤ r * δ := by simpa [mem_closedBall] using hy
        have h4 : ‖(1 / r) • (y - x)‖ = (1 / r) * dist y x := by
          have h5 : ‖(1 / r) • (y - x)‖ = |1 / r| * ‖y - x‖ := by
            rw [norm_smul]
            rw [Real.norm_eq_abs]
          rw [h5, abs_of_pos (by positivity)]
          have h6 : ‖y - x‖ = dist y x := by simp [dist_eq_norm]
          rw [h6] <;> ring
        rw [h4]
        have h5 : (1 / r) * dist y x ≤ (1 / r) * (r * δ) := by gcongr
        have h6 : (1 / r) * (r * δ) = δ := by
          field_simp [hr_pos.ne'] <;> ring
        rw [h6] at h5
        exact h5
      have h5 : (1 / r) • (y - x) ∈ closedBall (0 : E n) δ := by
        simpa [mem_closedBall, dist_zero_right] using h2
      exact hφ_lower ((1 / r) • (y - x)) h5
    have h2 : ∀ᵐ y ∂(μ.restrict (closedBall x (r * δ))), cφ ≤ ψ y := by
      filter_upwards [ae_restrict_mem measurableSet_closedBall] with y hy
      exact h1 y hy
    have h4 : μ (closedBall x (r * δ)) < ⊤ := by
      have h5 : μ (closedBall x (r * δ)) ≤ μ Set.univ := measure_mono (Set.subset_univ _)
      exact h5.trans_lt hμ_fin
    have h_int3 : IntegrableOn ψ (closedBall x (r * δ)) μ :=
      h_int_ψ.integrableOn
    have h_const_int : IntegrableOn (fun _ : E n => cφ) (closedBall x (r * δ)) μ :=
      (integrable_const cφ).integrableOn
    have h_mono : ∫ y in closedBall x (r * δ), cφ ∂μ ≤ ∫ y in closedBall x (r * δ), ψ y ∂μ :=
      setIntegral_mono_on h_const_int h_int3 measurableSet_closedBall h1
    have h_eq : ∫ y in closedBall x (r * δ), cφ ∂μ = cφ * (μ (closedBall x (r * δ))).toReal := by
      have h' : ∫ y in closedBall x (r * δ), cφ ∂μ = ∫ y, cφ ∂(μ.restrict (closedBall x (r * δ))) := by rfl
      rw [h']
      have h2 : ∫ (y : E n), cφ ∂(μ.restrict (closedBall x (r * δ))) =
          (μ.restrict (closedBall x (r * δ))).real Set.univ • cφ := integral_const (c := cφ)
      rw [h2]
      have h5 : (μ.restrict (closedBall x (r * δ))) Set.univ = μ (closedBall x (r * δ)) := by simp
      have h7 : (μ.restrict (closedBall x (r * δ))).real Set.univ =
          ((μ.restrict (closedBall x (r * δ))) Set.univ).toReal := by
        rfl
      rw [h7, h5]
      <;> simp [smul_eq_mul, mul_comm]
    rw [h_eq] at h_mono
    exact h_mono

  have h_pos3 : cφ * (μ (closedBall x (r * δ))).toReal ≤ ∫ y, ψ y ∂μ :=
    h_pos_ψ2.trans h_pos_ψ1

  -- Error bound for ∫ ψ*(h-1)
  have h_err : |∫ y, ψ y * (h y - 1) ∂μ| ≤
      Mφ * ∫ y in closedBall x (r * R), |h y - 1| ∂μ := by
    have h_supp : ∀ᵐ y ∂μ, ψ y ≠ 0 → y ∈ closedBall x (r * R) := by
      filter_upwards with y hy
      have h1 : (1 / r) • (y - x) ∈ Function.support φ := by
        simpa [ψ, Function.mem_support] using hy
      have h2 : (1 / r) • (y - x) ∈ closedBall (0 : E n) R := hR_supp h1
      have h3 : ‖(1 / r) • (y - x)‖ ≤ R := by
        have h4 : dist ((1 / r) • (y - x)) (0 : E n) ≤ R := mem_closedBall.mp h2
        have h5 : dist ((1 / r) • (y - x)) (0 : E n) = ‖(1 / r) • (y - x)‖ := by
          rw [dist_zero_right]
        rw [h5] at h4
        exact h4
      have h4 : dist y x ≤ r * R := by
        have h5 : ‖(1 / r) • (y - x)‖ = (1 / r) * dist y x := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
          <;> simp [dist_eq_norm] <;> ring
        rw [h5] at h3
        have h6 : (1 / r) * dist y x ≤ R := h3
        have h7 : dist y x ≤ r * R := by
          calc dist y x
            = r * ((1 / r) * dist y x) := by field_simp [hr_pos.ne'] <;> ring
          _ ≤ r * R := by gcongr
        exact h7
      simpa [mem_closedBall] using h4
    have h_main : ∫ y, ψ y * (h y - 1) ∂μ = ∫ y in closedBall x (r * R), ψ y * (h y - 1) ∂μ := by
      let F : E n → ℝ := fun y => ψ y * (h y - 1)
      have h9 : ∀ᵐ y ∂μ, F y = Set.indicator (closedBall x (r * R)) F y := by
        filter_upwards [h_supp] with y hy
        by_cases h6 : y ∈ closedBall x (r * R)
        · simp [h6, Set.indicator_apply, F]
        · have h7 : ψ y = 0 := by
            by_contra h8
            exact h6 (hy h8)
          have hF : F y = 0 := by
            simp [F, h7]
          simp [hF, Set.indicator_apply, h6]
      have h10 : ∫ y, F y ∂μ = ∫ y, Set.indicator (closedBall x (r * R)) F y ∂μ :=
        integral_congr_ae h9
      rw [h10, integral_indicator measurableSet_closedBall]
    rw [h_main]
    calc |∫ y in closedBall x (r * R), ψ y * (h y - 1) ∂μ|
      ≤ ∫ y in closedBall x (r * R), |ψ y * (h y - 1)| ∂μ := abs_integral_le_integral_abs
    _ = ∫ y in closedBall x (r * R), |ψ y| * |h y - 1| ∂μ := by
        congr 1 with y <;> simp [abs_mul]
    _ ≤ Mφ * ∫ y in closedBall x (r * R), |h y - 1| ∂μ := by
        have h5 : ∀ y, |ψ y| ≤ Mφ := by
          intro y
          exact hφ_bound ((1 / r) • (y - x))
        have h6 : ∀ᵐ y ∂(μ.restrict (closedBall x (r * R))), |ψ y| * |h y - 1| ≤ Mφ * |h y - 1| := by
          filter_upwards with y
          exact mul_le_mul_of_nonneg_right (h5 y) (abs_nonneg _)
        have h_int4 : IntegrableOn (fun y => |ψ y| * |h y - 1|) (closedBall x (r * R)) μ := by
          have h_cont2 : Continuous (fun y => |ψ y|) := continuous_abs.comp hψ_smooth.continuous
          have hK2 : IsCompact (tsupport ψ) := hψ_supp
          have h_bdd_img2 : BddAbove (Set.image (fun x => ‖(|ψ x|)‖) (tsupport ψ)) :=
            hK2.bddAbove_image h_cont2.norm.continuousOn
          rcases h_bdd_img2 with ⟨C0, hC0⟩
          let C2 := max C0 0
          have hC2_nonneg : 0 ≤ C2 := by positivity
          have h_on2 : ∀ x ∈ tsupport ψ, ‖(|ψ x|)‖ ≤ C2 := by
            intro x hx
            have h5 : ‖(|ψ x|)‖ ∈ Set.image (fun x => ‖(|ψ x|)‖) (tsupport ψ) := ⟨x, hx, rfl⟩
            have h6 : ‖(|ψ x|)‖ ≤ C0 := hC0 h5
            exact le_trans h6 (le_max_left _ _)
          have h_bdd_all2 : ∀ x, ‖(|ψ x|)‖ ≤ C2 := by
            intro x
            by_cases hx : x ∈ tsupport ψ
            · exact h_on2 x hx
            · have h7 : ψ x = 0 := by
                have h8 : x ∉ Function.support ψ := fun h9 => hx (subset_closure h9)
                simpa [Function.mem_support] using h8
              simp [h7, hC2_nonneg]
          have h_abs_and : AEStronglyMeasurable (fun y => |ψ y|) (μ.restrict Set.univ) ∧ HasFiniteIntegral (fun y => |ψ y|) (μ.restrict Set.univ) :=
            IntegrableOn.of_bound hμ_fin h_cont2.measurable.aestronglyMeasurable C2
              (by filter_upwards with x using h_bdd_all2 x)
          have h_eq : μ.restrict Set.univ = μ := by simp
          have h_abs_ae : AEStronglyMeasurable (fun y => |ψ y|) μ := by
            rw [← h_eq]; exact h_abs_and.1
          have h_abs_fi : HasFiniteIntegral (fun y => |ψ y|) μ := by
            rw [← h_eq]; exact h_abs_and.2
          have h_absψ_int : Integrable (fun y => |ψ y|) μ := by
            refine' ⟨h_abs_ae, h_abs_fi⟩
          have h_absψ_memLp_top : MemLp (fun y => |ψ y|) ⊤ μ :=
            MemLp.of_bound h_abs_ae C2 (by filter_upwards with y using h_bdd_all2 y)
          have h_prod_int : Integrable (fun y => |ψ y| * |h y - 1|) μ :=
            h_abs_int.mul_of_top_right h_absψ_memLp_top
          exact h_prod_int.integrableOn
        have h_Mφ_int : IntegrableOn (fun y => Mφ * |h y - 1|) (closedBall x (r * R)) μ :=
          (h_abs_int.const_mul Mφ).integrableOn
        have h7 : ∫ y in closedBall x (r * R), |ψ y| * |h y - 1| ∂μ ≤ ∫ y in closedBall x (r * R), Mφ * |h y - 1| ∂μ :=
          setIntegral_mono_on h_int4 h_Mφ_int measurableSet_closedBall
            (fun y _ => mul_le_mul_of_nonneg_right (h5 y) (abs_nonneg _))
        have h8 : ∫ y in closedBall x (r * R), Mφ * |h y - 1| ∂μ = Mφ * ∫ y in closedBall x (r * R), |h y - 1| ∂μ := by
          rw [integral_const_mul]
        rw [h8] at h7
        exact h7

  -- Density doubling
  have h_doub : μ (closedBall x (r * R)) ≤
      ENNReal.ofReal C_doub * μ (closedBall x (r * δ)) := by
    have h1 : μ (closedBall x (r * R)) ≤ μ (ball x (2 * r * R)) := by
      apply measure_mono
      intro y hy
      have h2 : dist y x ≤ r * R := by simpa [mem_closedBall] using hy
      have h_pos : 0 < r * R := mul_pos hr_pos hR_pos
      have h3 : dist y x < 2 * r * R := by linarith
      exact mem_ball.mpr h3
    have h2 : 2 * r * R < Ru := by
      have h3 : R_min ≤ Ru := min_le_right _ _
      exact h_2rR_lt_min.trans_le h3
    have h3 : μ (ball x (2 * r * R)) ≤ ENNReal.ofReal (C * (2 * r * R) ^ (n - 1)) :=
      h_upper (2 * r * R) (by positivity) h2
    have h4 : μ (ball x (r * δ)) ≥ ENNReal.ofReal (c * (r * δ) ^ (n - 1)) :=
      h_lower (r * δ) (by positivity) hrδ_lt_Rl
    have h5 : μ (closedBall x (r * δ)) ≥ μ (ball x (r * δ)) := measure_mono ball_subset_closedBall
    calc μ (closedBall x (r * R))
      ≤ μ (ball x (2 * r * R)) := h1
    _ ≤ ENNReal.ofReal (C * (2 * r * R) ^ (n - 1)) := h3
    _ = ENNReal.ofReal C_doub * ENNReal.ofReal (c * (r * δ) ^ (n - 1)) := by
        have h_pos1 : 0 ≤ C_doub := by positivity
        have h_pos2 : 0 ≤ c * (r * δ) ^ (n - 1) := by positivity
        have h_eq_real : C * (2 * r * R) ^ (n - 1) = C_doub * (c * (r * δ) ^ (n - 1)) := by
          have hc_pos' : 0 < c := hc_pos
          have hδ_pos' : 0 < δ := hδ_pos
          simp only [C_doub]
          have h1 : (2 * R / δ) ^ (n - 1) * (r * δ) ^ (n - 1) = (2 * r * R) ^ (n - 1) := by
            have h2 : (2 * R / δ) * (r * δ) = 2 * r * R := by
              field_simp [hδ_pos'.ne'] <;> ring
            rw [← mul_pow, h2]
          calc
            C * (2 * r * R) ^ (n - 1)
              = (C / c) * c * (2 * r * R) ^ (n - 1) := by
                field_simp [hc_pos'.ne'] <;> ring
          _ = (C / c) * ((2 * R / δ) ^ (n - 1) * (r * δ) ^ (n - 1)) * c := by
              rw [h1] <;> ring
          _ = (C / c) * (2 * R / δ) ^ (n - 1) * (c * (r * δ) ^ (n - 1)) := by ring
        have h_eq_mul : ENNReal.ofReal (C_doub * (c * (r * δ) ^ (n - 1))) =
            ENNReal.ofReal C_doub * ENNReal.ofReal (c * (r * δ) ^ (n - 1)) :=
          ENNReal.ofReal_mul h_pos1
        rw [h_eq_real, h_eq_mul]
    _ ≤ ENNReal.ofReal C_doub * μ (closedBall x (r * δ)) := by
        gcongr <;> exact h4.trans h5

  have hμRR_fin : μ (closedBall x (r * R)) ≠ ⊤ := by
    exact ne_top_of_le_ne_top hμ_fin.ne (measure_mono (Set.subset_univ _))
  have hμRR_pos : 0 < μ (closedBall x (r * R)) := by
    have h1 : 0 < μ (ball x (r * R)) := hx.1 (r * R) (by positivity)
    exact h1.trans_le (measure_mono ball_subset_closedBall)
  have hμδ_fin : μ (closedBall x (r * δ)) ≠ ⊤ := by
    exact ne_top_of_le_ne_top hμ_fin.ne (measure_mono (Set.subset_univ _))
  have hμδ_pos : 0 < μ (closedBall x (r * δ)) := by
    have h1 : 0 < μ (ball x (r * δ)) := hx.1 (r * δ) (by positivity)
    exact h1.trans_le (measure_mono ball_subset_closedBall)

  have hdenom_pos : 0 < (μ (closedBall x (r * R))).toReal :=
    ENNReal.toReal_pos hμRR_pos.ne' hμRR_fin

  have h_avg : (∫ y in closedBall x (r * R), |h y - 1| ∂μ) <
      ε_target * (μ (closedBall x (r * R))).toReal := by
    have h_ineq : (∫ y in closedBall x (r * R), |h y - 1| ∂μ) / (μ (closedBall x (r * R))).toReal < ε_target :=
      h_abs_avg
    have h_eq_div : (∫ y in closedBall x (r * R), |h y - 1| ∂μ) =
        ((∫ y in closedBall x (r * R), |h y - 1| ∂μ) / (μ (closedBall x (r * R))).toReal) * (μ (closedBall x (r * R))).toReal := by
      field_simp [hdenom_pos.ne'] <;> ring
    rw [h_eq_div]
    exact mul_lt_mul_of_pos_right h_ineq hdenom_pos

  have h_decomp : ∫ y, ψ y * h y ∂μ =
      (∫ y, ψ y ∂μ) + ∫ y, ψ y * (h y - 1) ∂μ := by
    have h3 : ∀ y, ψ y * h y = ψ y + ψ y * (h y - 1) := by
      intro y; ring
    have h4 : (fun y => ψ y * h y) = (fun y => ψ y) + (fun y => ψ y * (h y - 1)) := by
      funext y; exact h3 y
    have h_int_hsub : Integrable (fun y => h y - 1) μ := h_int.sub (integrable_const 1)
    have hψ_memLp_top : MemLp ψ ⊤ μ := by
      have h_cont : Continuous ψ := hψ_smooth.continuous
      have hK : IsCompact (tsupport ψ) := hψ_supp
      have h_bdd_img : BddAbove (Set.image (fun x => ‖ψ x‖) (tsupport ψ)) :=
        hK.bddAbove_image h_cont.norm.continuousOn
      rcases h_bdd_img with ⟨C0, hC0⟩
      let C' := max C0 0
      have hC'_nonneg : 0 ≤ C' := by positivity
      have h_on : ∀ x ∈ tsupport ψ, ‖ψ x‖ ≤ C' := by
        intro x hx
        have h5 : ‖ψ x‖ ∈ Set.image (fun x => ‖ψ x‖) (tsupport ψ) := ⟨x, hx, rfl⟩
        have h6 : ‖ψ x‖ ≤ C0 := hC0 h5
        exact le_trans h6 (le_max_left _ _)
      have h_bdd_all' : ∀ x, ‖ψ x‖ ≤ C' := by
        intro x
        by_cases hx : x ∈ tsupport ψ
        · exact h_on x hx
        · have h7 : ψ x = 0 := by
            have h8 : x ∉ Function.support ψ := fun h9 => hx (subset_closure h9)
            simpa [Function.mem_support] using h8
          rw [h7] <;> simp [hC'_nonneg]
      exact MemLp.of_bound h_int_ψ.aestronglyMeasurable C' (by filter_upwards with y using h_bdd_all' y)
    have h_int_err : Integrable (fun y => ψ y * (h y - 1)) μ :=
      h_int_hsub.mul_of_top_right hψ_memLp_top
    have h5 : ∫ y, (ψ y + ψ y * (h y - 1)) ∂μ =
        (∫ y, ψ y ∂μ) + ∫ y, ψ y * (h y - 1) ∂μ :=
      integral_add h_int_ψ h_int_err
    rw [h4]
    exact h5

  have h_err2 : |∫ y, ψ y * (h y - 1) ∂μ| < cφ * (μ (closedBall x (r * δ))).toReal := by
    have hMφ_pos : 0 < Mφ := by
      have h9 : |φ 0| ≤ Mφ := hφ_bound 0
      have h10 : 0 < |φ 0| := by
        rw [abs_pos] <;> exact hφ0.ne'
      linarith
    apply orientation_error_bound
      Mφ cφ C_doub hMφ_pos hcφ_pos hC_doub_pos
      (μ (closedBall x (r * R)))
      (μ (closedBall x (r * δ)))
      hμRR_fin hμδ_fin hμδ_pos h_doub
      |∫ y, ψ y * (h y - 1) ∂μ|
      (∫ y in closedBall x (r * R), |h y - 1| ∂μ)
      h_err
    simpa [ε_target] using h_avg

  have h_final_pos : 0 < ∫ y, ψ y * h y ∂μ := by
    rw [h_decomp]
    set A := cφ * (μ (closedBall x (r * δ))).toReal with hA
    set B := ∫ y, ψ y ∂μ with hB
    set C := ∫ y, ψ y * (h y - 1) ∂μ with hC
    have h10 : A ≤ B := h_pos3
    have h11 : |C| < A := h_err2
    have h12 : -A < C := by
      have h13 : -|C| ≤ C := neg_abs_le C
      have h14 : -A < -|C| := by gcongr <;> exact abs_nonneg C
      linarith
    have h15 : 0 < B + C := by linarith
    exact h15

  have h_scale_pos : 0 < ((1 / r) ^ (n - 1) : ℝ) := by positivity
  rw [h_main_eq]
  exact mul_nonneg h_scale_pos.le h_final_pos.le

end Geometry.Perimeter
