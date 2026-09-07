import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import MyLeanRepo.Kakeya.CV.Isoperimetric.Measure.AEMVT
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.Tactic


/-!
# Local Coarea Inequality for Lipschitz Functions

Assembles the local coarea inequality using:
1. Bi-Lipschitz correction map Φ
2. Fubini for linear level sets
3. Lipschitz Hausdorff image bound
4. Almost-everywhere mean value theorem (imported from AEMVT)
-/

open MeasureTheory Metric Set ENNReal Filter
open scoped MeasureTheory

namespace Geometry

variable {n : ℕ} [Nonempty (Fin n)]

-- ============================================================================
-- Section 1: Bi-Lipschitz correction
-- ============================================================================

lemma correction_upper_lipschitz
    {g : E n → ℝ} {v : E n} {ε : ℝ} (hε : 0 ≤ ε)
    {s : Set (E n)}
    (hg_lip : ∀ (x y : E n), x ∈ s → y ∈ s → |g y - g x| ≤ ε * ‖y - x‖)
    (hv : ‖v‖ = 1) :
    ∀ (x y : E n), x ∈ s → y ∈ s →
      ‖(y + g y • v) - (x + g x • v)‖ ≤ (1 + ε) * ‖y - x‖ := by
  intro x y hx hy
  have h1 : ‖(y + g y • v) - (x + g x • v)‖ ≤ ‖y - x‖ + ‖(g y - g x) • v‖ := by
    have h_eq : (y + g y • v) - (x + g x • v) = (y - x) + (g y - g x) • v := by
      simp [sub_smul] <;> abel
    rw [h_eq]; exact norm_add_le _ _
  have h2 : ‖(g y - g x) • v‖ = |g y - g x| * ‖v‖ := by rw [norm_smul] <;> rfl
  rw [h2, hv] at h1
  have h3 : |g y - g x| ≤ ε * ‖y - x‖ := hg_lip x y hx hy
  linarith

lemma correction_lower_lipschitz
    {g : E n → ℝ} {v : E n} {ε : ℝ} (hε : 0 ≤ ε) (hε2 : ε < 1)
    {s : Set (E n)}
    (hg_lip : ∀ (x y : E n), x ∈ s → y ∈ s → |g y - g x| ≤ ε * ‖y - x‖)
    (hv : ‖v‖ = 1) :
    ∀ (x y : E n), x ∈ s → y ∈ s →
      (1 - ε) * ‖y - x‖ ≤ ‖(y + g y • v) - (x + g x • v)‖ := by
  intro x y hx hy
  set a := (y - x) + (g y - g x) • v with ha
  set b := (g y - g x) • v with hb
  have h4 : a - b = y - x := by simp [ha, hb] <;> abel
  have h5 : ‖y - x‖ ≤ ‖a‖ + ‖b‖ := by
    have h6 : ‖a - b‖ ≤ ‖a‖ + ‖b‖ := norm_sub_le a b
    rw [h4] at h6; exact h6
  have h7 : ‖b‖ ≤ ε * ‖y - x‖ := by
    have h8 : ‖b‖ = |g y - g x| * ‖v‖ := by rw [hb, norm_smul] <;> rfl
    rw [h8, hv]
    have h9 : |g y - g x| ≤ ε * ‖y - x‖ := hg_lip x y hx hy
    simpa [mul_one] using h9
  have h10 : (1 - ε) * ‖y - x‖ ≤ ‖a‖ := by
    calc (1 - ε) * ‖y - x‖ = ‖y - x‖ - ε * ‖y - x‖ := by ring
      _ ≤ ‖y - x‖ - ‖b‖ := by gcongr
      _ ≤ ‖a‖ := by linarith
  have h_goal : a = (y + g y • v) - (x + g x • v) := by
    have h11 : (y + g y • v) - (x + g x • v) = (y - x) + (g y • v - g x • v) := by abel
    have h12 : g y • v - g x • v = (g y - g x) • v := by rw [sub_smul]
    rw [h11, h12] <;> rfl
  exact h_goal ▸ h10

-- ============================================================================
-- Section 2: Lipschitz image bound for Euclidean Hausdorff measure
-- ============================================================================

/-- Transfer Hausdorff Lipschitz image bound to Euclidean Hausdorff measure. -/
lemma euclideanHausdorff_image_le
    {K : NNReal} {f : E n → E n} {s : Set (E n)}
    (h : LipschitzOnWith K f s) {d : ℕ} :
    μHE[d] (f '' s) ≤ (K : ENNReal) ^ d * μHE[d] s := by
  have h1 : μH[(d : ℝ)] (f '' s) ≤ (K : ENNReal) ^ (d : ℝ) * μH[(d : ℝ)] s :=
    h.hausdorffMeasure_image_le (by positivity)
  have h2 : ∀ (c : ENNReal), c * μH[(d : ℝ)] (f '' s) ≤ (K : ENNReal) ^ (d : ℝ) * (c * μH[(d : ℝ)] s) := by
    intro c
    have h3 : c * μH[(d : ℝ)] (f '' s) ≤ c * ((K : ENNReal) ^ (d : ℝ) * μH[(d : ℝ)] s) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h4 : c * ((K : ENNReal) ^ (d : ℝ) * μH[(d : ℝ)] s) = (K : ENNReal) ^ (d : ℝ) * (c * μH[(d : ℝ)] s) := by ring
    exact le_trans h3 (le_of_eq h4)
  have h_pow : (K : ENNReal) ^ (d : ℝ) = (K : ENNReal) ^ d := by simp
  simpa [MeasureTheory.Measure.euclideanHausdorffMeasure_def, Measure.smul_apply, h_pow] using h2 _

-- ============================================================================
-- Section 3: Fubini for linear functions
-- ============================================================================

/-- Coarea formula for linear function `y ↦ inner(y,v)` with `‖v‖=1`. -/
lemma linear_coarea_formula
    (v : E n) (hv : ‖v‖ = 1) (D : Set (E n)) (hD : MeasurableSet D)
    (a b : ℝ) (hab : a < b) :
    volume {y ∈ D | a < inner ℝ y v ∧ inner ℝ y v ≤ b} =
      ∫⁻ s in Set.Ioc a b, μHE[n - 1] {y ∈ D | inner ℝ y v = s} := by
  let T : Set (E n) := {y ∈ D | a < inner ℝ y v ∧ inner ℝ y v ≤ b}
  have h_meas : Measurable (fun y : E n => inner ℝ y v) := by fun_prop
  have hT_meas : MeasurableSet T := by
    have h_lt : MeasurableSet {y | a < inner ℝ y v} := h_meas isOpen_Ioi.measurableSet
    have h_le : MeasurableSet {y | inner ℝ y v ≤ b} := h_meas isClosed_Iic.measurableSet
    exact hD.inter (h_lt.inter h_le)
  have hv_ne : v ≠ 0 := by
    intro h; rw [h] at hv; simp at hv
  have h_finrank : Module.finrank ℝ (E n) = n := by simp [E]
  have h_orth : ∀ (z : E n), z ∈ (ℝ ∙ v)ᗮ ↔ inner ℝ z v = 0 := by
    intro z
    constructor
    · intro h
      have h3 : v ∈ (ℝ ∙ v) := by
        simp [Submodule.mem_span_singleton] <;> exact ⟨1, by ring⟩
      have h4 : inner ℝ v z = 0 := h v h3
      have h5 : inner ℝ z v = inner ℝ v z := (real_inner_comm z v).symm
      rw [h5]; exact h4
    · intro h; intro w hw
      rcases Submodule.mem_span_singleton.mp hw with ⟨c, rfl⟩
      have h4 : inner ℝ (c • v) z = c * inner ℝ v z := by
        rw [inner_smul_left]; simp
      have h5 : inner ℝ v z = inner ℝ z v := (real_inner_comm v z).symm
      rw [h4, h5, h] <;> ring
  have h_affine : ∀ (x : ℝ) (y : E n),
      y ∈ AffineSubspace.mk' (x • v) (ℝ ∙ v)ᗮ ↔ inner ℝ y v = x := by
    intro x y
    have h1 : y ∈ AffineSubspace.mk' (x • v) (ℝ ∙ v)ᗮ ↔
        y - x • v ∈ (ℝ ∙ v)ᗮ := AffineSubspace.mem_mk'
    rw [h1]
    rw [h_orth (y - x • v)]
    have h2 : inner ℝ (y - x • v) v = inner ℝ y v - x := by
      have h3 : inner ℝ (y - x • v) v = inner ℝ y v - inner ℝ (x • v) v := by
        rw [inner_sub_left]
      rw [h3]
      have h4 : inner ℝ (x • v) v = x * inner ℝ v v := by
        rw [inner_smul_left] <;> simp
      rw [h4]
      have h5 : inner ℝ v v = ‖v‖ ^ 2 := real_inner_self_eq_norm_sq v
      rw [h5, hv] <;> ring
    rw [h2] <;> exact sub_eq_zero
  have h_enorm : ‖v‖ₑ = 1 := by
    have h : ‖v‖ₑ = ↑‖v‖₊ := enorm_eq_nnnorm v
    rw [h]
    have h2 : ‖v‖₊ = 1 := by
      apply NNReal.coe_injective
      simp [hv]
    rw [h2] <;> simp
  have h_main_raw := EuclideanGeometry.euclideanHausdorffMeasure_eq_lintegral (0 : E n) hv_ne hT_meas
  have h_main : μHE[n] T = ∫⁻ (x : ℝ), μHE[n - 1] (T ∩ AffineSubspace.mk' (x • v) (ℝ ∙ v)ᗮ) := by
    simpa [h_finrank, h_enorm, one_mul] using h_main_raw
  have h_volume : volume T = μHE[n] T := by
    have h_eq : (μHE[n] : Measure (E n)) = volume :=
      EuclideanSpace.euclideanHausdorffMeasure_eq_volume n
    exact congr_arg (fun m : Measure (E n) => m T) h_eq |>.symm
  rw [h_volume, h_main]
  have h_slice : ∀ (x : ℝ), T ∩ AffineSubspace.mk' (x • v) (ℝ ∙ v)ᗮ =
      if a < x ∧ x ≤ b then {y ∈ D | inner ℝ y v = x} else (∅ : Set (E n)) := by
    intro x
    ext y
    simp only [T, Set.mem_inter_iff, Set.mem_setOf_eq]
    have h4 := h_affine x y
    constructor
    · rintro ⟨⟨hyD, h1, h2⟩, h3⟩
      have h5 : inner ℝ y v = x := h4.mp h3
      have h6 : a < x := by rw [←h5]; exact h1
      have h7 : x ≤ b := by rw [←h5]; exact h2
      rw [if_pos ⟨h6, h7⟩]
      exact ⟨hyD, h5⟩
    · intro h
      by_cases h_case : a < x ∧ x ≤ b
      · rw [if_pos h_case] at h
        have h5 : inner ℝ y v = x := h.2
        have h6 : a < inner ℝ y v := by rw [h5] <;> exact h_case.1
        have h7 : inner ℝ y v ≤ b := by rw [h5] <;> exact h_case.2
        exact ⟨⟨h.1, h6, h7⟩, h4.mpr h5⟩
      · rw [if_neg h_case] at h
        simp at h
  have h_eq_fun : ∀ (x : ℝ), μHE[n - 1] (T ∩ AffineSubspace.mk' (x • v) (ℝ ∙ v)ᗮ) =
      Set.indicator (Set.Ioc a b) (fun s : ℝ => μHE[n - 1] {y ∈ D | inner ℝ y v = s}) x := by
    intro x
    rw [h_slice x]
    by_cases h : a < x ∧ x ≤ b
    · rw [if_pos h]
      simp [Set.indicator, h, Set.mem_Ioc] <;> tauto
    · rw [if_neg h]
      simp [Set.indicator, h, Set.mem_Ioc] <;> tauto
  have h5 : ∫⁻ (x : ℝ), μHE[n - 1] (T ∩ AffineSubspace.mk' (x • v) (ℝ ∙ v)ᗮ) =
      ∫⁻ (x : ℝ), Set.indicator (Set.Ioc a b) (fun s : ℝ => μHE[n - 1] {y ∈ D | inner ℝ y v = s}) x := by
    rw [lintegral_congr h_eq_fun]
  rw [h5]
  have h6 : ∫⁻ (x : ℝ), Set.indicator (Set.Ioc a b) (fun s : ℝ => μHE[n - 1] {y ∈ D | inner ℝ y v = s}) x =
      ∫⁻ s in Set.Ioc a b, μHE[n - 1] {y ∈ D | inner ℝ y v = s} := by
    simpa using rfl
  exact h6

/-- Shifted version: for `L(y) = inner(y, v) + c`. -/
lemma linear_coarea_formula_shifted
    (v : E n) (hv : ‖v‖ = 1) (c : ℝ) (D : Set (E n)) (hD : MeasurableSet D)
    (a b : ℝ) (hab : a < b) :
    volume {y ∈ D | a < inner ℝ y v + c ∧ inner ℝ y v + c ≤ b} =
      ∫⁻ s in Set.Ioc a b, μHE[n - 1] {y ∈ D | inner ℝ y v + c = s} := by
  let a' := a - c
  let b' := b - c
  have h_ab' : a' < b' := by simp [a', b']; linarith
  have h_set_eq : {y ∈ D | a < inner ℝ y v + c ∧ inner ℝ y v + c ≤ b} =
      {y ∈ D | a' < inner ℝ y v ∧ inner ℝ y v ≤ b'} := by
    ext y
    simp only [Set.mem_setOf_eq, a', b']
    constructor
    · rintro ⟨hyD, h1, h2⟩
      have h3 : a - c < inner ℝ y v := by linarith
      have h4 : inner ℝ y v ≤ b - c := by linarith
      exact ⟨hyD, h3, h4⟩
    · rintro ⟨hyD, h1, h2⟩
      have h3 : a < inner ℝ y v + c := by linarith
      have h4 : inner ℝ y v + c ≤ b := by linarith
      exact ⟨hyD, h3, h4⟩
  rw [h_set_eq]
  have h_main := linear_coarea_formula v hv D hD a' b' h_ab'
  rw [h_main]
  let g : ℝ → ENNReal := fun x => μHE[n - 1] {y ∈ D | inner ℝ y v = x}
  have h_trans : ∀ (f : ℝ → ENNReal), ∫⁻ (x : ℝ), f (x - c) = ∫⁻ (x : ℝ), f x := by
    intro f
    have hmp : MeasurePreserving (fun x : ℝ => x - c) := measurePreserving_add_right volume (-c)
    have h_meas_g : Measurable (fun x : ℝ => x - c) := by fun_prop
    let g : ℝ → ℝ := fun x => x - c
    have hg : Measurable g := by fun_prop
    let e_meas : ℝ ≃ᵐ ℝ :=
      { toFun := g
        invFun := fun x => x + c
        left_inv := by intro x; ring
        right_inv := by intro x; ring
        measurable_toFun := hg
        measurable_invFun := measurable_id.add measurable_const }
    have h : ∫⁻ (y : ℝ), f y ∂Measure.map g volume = ∫⁻ (x : ℝ), f (g x) :=
      MeasureTheory.lintegral_map_equiv f e_meas
    have h2 : Measure.map g volume = volume := hmp.map_eq
    rw [h2] at h
    exact h.symm
  have h_goal : ∫⁻ x in Set.Ioc a' b', g x = ∫⁻ s in Set.Ioc a b, g (s - c) := by
    have h1 : ∫⁻ x in Set.Ioc a' b', g x =
        ∫⁻ (x : ℝ), Set.indicator (Set.Ioc a' b') g x := by simpa using rfl
    rw [h1]
    have h2 : ∫⁻ (x : ℝ), Set.indicator (Set.Ioc a' b') g x =
        ∫⁻ (s : ℝ), Set.indicator (Set.Ioc a' b') g (s - c) := (h_trans _).symm
    rw [h2]
    have h3 : ∀ (s : ℝ), Set.indicator (Set.Ioc a' b') g (s - c) =
        Set.indicator (Set.Ioc a b) (fun s : ℝ => g (s - c)) s := by
      intro s
      simp [Set.indicator, Set.mem_Ioc, a', b']
      <;> constructor <;> intro h <;> simp_all <;> linarith
    have h4 : ∫⁻ (s : ℝ), Set.indicator (Set.Ioc a' b') g (s - c) =
        ∫⁻ (s : ℝ), Set.indicator (Set.Ioc a b) (fun s : ℝ => g (s - c)) s :=
      lintegral_congr (μ := volume) h3
    rw [h4]
    simpa using rfl
  rw [h_goal]
  apply lintegral_congr
  intro s
  have h5 : g (s - c) = μHE[n - 1] {y ∈ D | inner ℝ y v = s - c} := by rfl
  rw [h5]
  have h6 : {y ∈ D | inner ℝ y v = s - c} = {y ∈ D | inner ℝ y v + c = s} := by
    ext y
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨hyD, h⟩
      exact ⟨hyD, by linarith⟩
    · rintro ⟨hyD, h⟩
      exact ⟨hyD, by linarith⟩
  rw [h6]

-- ============================================================================
-- Section 4: Local Lipschitz coarea inequality
-- ============================================================================

/-- Local coarea inequality for Lipschitz functions.

At `x₀` with `‖∇f(x₀)‖ = 1` and gradient `ε`-close a.e. on `ball x₀ r`,
for any compact `C ⊆ closedBall x₀ (r/2)`:
`volume {x ∈ C | a < f(x) ≤ b} ≤ ((1+ε)^{n-1}/(1-ε)^n) * ∫ₐᵇ μHE[n-1]({x ∈ C | f(x)=s}) ds`
-/
theorem local_coarea_lipschitz
    (f : E n → ℝ) (hf : LipschitzWith 1 f)
    (x₀ : E n) (h₁ : ‖fderiv ℝ f x₀‖ = 1)
    (r ε : ℝ) (hr : 0 < r) (hε : 0 < ε) (hε2 : ε < 1)
    (h_grad_close : ∀ᵐ (x : E n) ∂volume.restrict (ball x₀ r),
      ‖fderiv ℝ f x - fderiv ℝ f x₀‖ ≤ ε)
    :
    ∀ (C : Set (E n)), IsCompact C → C ⊆ closedBall x₀ (r / 2) →
      ∀ (a b : ℝ), a < b →
        volume {x ∈ C | a < f x ∧ f x ≤ b} ≤
          ENNReal.ofReal (((1 + ε) ^ (n - 1 : ℕ)) / ((1 - ε) ^ n)) *
          ∫⁻ s in Set.Ioc a b, μHE[n - 1] {x ∈ C | f x = s} := by
  let v : E n := (InnerProductSpace.toDual ℝ (E n)).symm (fderiv ℝ f x₀)
  have hv_norm : ‖v‖ = 1 := by
    have h : ‖v‖ = ‖fderiv ℝ f x₀‖ := (InnerProductSpace.toDual ℝ (E n)).symm.norm_map _
    rw [h, h₁]

  let L : E n → ℝ := fun y => f x₀ + inner ℝ (y - x₀) v
  let h : E n → ℝ := fun y => f y - L y

  have hL_lip : LipschitzWith 1 L := by
    refine' LipschitzWith.of_dist_le_mul fun y z => _
    have h_eq : dist (L y) (L z) = |inner ℝ (y - z) v| := by
      simp [L, dist_eq_norm, inner_sub_left] <;> ring_nf
    have h2 : |inner ℝ (y - z) v| ≤ ‖y - z‖ * ‖v‖ := abs_real_inner_le_norm (y - z) v
    rw [hv_norm] at h2
    have h3 : dist (L y) (L z) ≤ ‖y - z‖ := by
      rw [h_eq]; simpa using h2
    have h4 : dist (L y) (L z) ≤ (1 : NNReal) * dist y z := by
      simpa [dist_eq_norm] using h3
    exact h4

  have h_fderiv_L : ∀ (x : E n), fderiv ℝ L x = fderiv ℝ f x₀ := by
    intro x
    set clm : E n → ℝ := fun y => inner ℝ y v with hclm_def
    set cnst : E n → ℝ := Function.const (E n) (f x₀ - inner ℝ x₀ v) with hcnst_def
    have hL_eq2 : L = fun y : E n => clm y + cnst y := by
      funext y
      simp only [L, hclm_def, hcnst_def, Function.const_apply, inner_sub_left]
      <;> ring
    have h1 : fderiv ℝ L x = innerSL ℝ v := by
      rw [hL_eq2]
      have h_clm_eq : clm = (innerSL ℝ v) := by
        funext z; simp [hclm_def, innerSL]; exact (real_inner_comm z v).symm
      have h_diff1 : DifferentiableAt ℝ clm x := by
        rw [h_clm_eq]
        exact (innerSL ℝ v).differentiableAt
      have h_diff2 : DifferentiableAt ℝ cnst x := by
        rw [hcnst_def]
        exact differentiableAt_const (c := f x₀ - inner ℝ x₀ v) (x := x)
      have h_sum : fderiv ℝ (fun y : E n => clm y + cnst y) x =
          fderiv ℝ clm x + fderiv ℝ cnst x := fderiv_add h_diff1 h_diff2
      rw [h_sum]
      have h_fderiv_clm : fderiv ℝ clm x = innerSL ℝ v := by
        rw [h_clm_eq]
        exact ContinuousLinearMap.fderiv (innerSL ℝ v)
      have h_fderiv_cnst : fderiv ℝ cnst x = 0 := by
        rw [hcnst_def]
        have h_fc : fderiv ℝ (Function.const (E n) (f x₀ - inner ℝ x₀ v)) = 0 :=
          fderiv_const (c := f x₀ - inner ℝ x₀ v)
        exact congr_fun h_fc x
      rw [h_fderiv_clm, h_fderiv_cnst] <;> simp
    rw [h1]
    have h4 : (InnerProductSpace.toDual ℝ (E n)) v = fderiv ℝ f x₀ :=
      (InnerProductSpace.toDual ℝ (E n)).apply_symm_apply (fderiv ℝ f x₀)
    have h5 : innerSL ℝ v = (InnerProductSpace.toDual ℝ (E n)) v := by rfl
    rw [h5, h4]

  have h_diff_ae : ∀ᵐ (x : E n) ∂volume.restrict (ball x₀ r), DifferentiableAt ℝ f x :=
    hf.ae_differentiableAt.filter_mono (ae_mono Measure.restrict_le_self)

  have h_fderiv_h : ∀ᵐ (x : E n) ∂volume.restrict (ball x₀ r),
      fderiv ℝ h x = fderiv ℝ f x - fderiv ℝ f x₀ := by
    filter_upwards [h_diff_ae] with x hx
    have hL_diff_at : DifferentiableAt ℝ L x := by
      have hL_diff : Differentiable ℝ L := by
        have h2 : Differentiable ℝ (fun y : E n => y - x₀) :=
          differentiable_id.sub (differentiable_const (c := x₀))
        have h3 : Differentiable ℝ (fun z : E n => inner ℝ z v) := by
          have h_eq : (fun z : E n => inner ℝ z v) = (innerSL ℝ v) := by
            funext z; simp [innerSL]; exact (real_inner_comm z v).symm
          rw [h_eq]
          exact (innerSL ℝ v).differentiable
        have h4 : Differentiable ℝ (fun y : E n => inner ℝ (y - x₀) v) :=
          h3.comp h2
        exact h4.const_add (f x₀)
      exact hL_diff.differentiableAt
    have h2 : fderiv ℝ h x = fderiv ℝ f x - fderiv ℝ L x := by
      rw [show h = f - L from rfl]
      exact fderiv_sub hx hL_diff_at
    rw [h2, h_fderiv_L x]

  have h_grad_h : ∀ᵐ (x : E n) ∂volume.restrict (ball x₀ r),
      ‖fderiv ℝ h x‖ ≤ ε := by
    filter_upwards [h_fderiv_h, h_grad_close] with x h2 h3
    rw [h2] at *; exact h3

  have h_h_lip : ∀ (x y : E n), x ∈ ball x₀ r → y ∈ ball x₀ r →
      |h y - h x| ≤ ε * ‖y - x‖ := by
    have h2 := lipschitzOn_of_ae_norm_fderiv_le (hg := hf.sub hL_lip)
      (hs := convex_ball x₀ r) (hs_open := isOpen_ball) (C := ε) (hC := by linarith) h_grad_h
    intro x y hx hy
    have h3 : ‖h y - h x‖ ≤ ε * ‖y - x‖ := h2 x y hx hy
    simpa using h3

  let Φ : E n → E n := fun y => y + h y • v
  have hΦ_cont : Continuous Φ := by
    have h_h_cont : Continuous h := hf.continuous.sub hL_lip.continuous
    have h_smul : Continuous (fun y => h y • v) := h_h_cont.smul continuous_const
    exact continuous_id.add h_smul

  have hΦ_upper : ∀ (x y : E n), x ∈ ball x₀ r → y ∈ ball x₀ r →
      ‖Φ y - Φ x‖ ≤ (1 + ε) * ‖y - x‖ :=
    correction_upper_lipschitz (le_of_lt hε) h_h_lip hv_norm

  have hΦ_lower : ∀ (x y : E n), x ∈ ball x₀ r → y ∈ ball x₀ r →
      (1 - ε) * ‖y - x‖ ≤ ‖Φ y - Φ x‖ :=
    correction_lower_lipschitz (le_of_lt hε) hε2 h_h_lip hv_norm

  have hΦ_inj : Set.InjOn Φ (ball x₀ r) := by
    intro x hx y hy hxy
    have h : ‖Φ y - Φ x‖ = 0 := by rw [hxy] <;> simp
    have h2 : (1 - ε) * ‖y - x‖ ≤ ‖Φ y - Φ x‖ := hΦ_lower x y hx hy
    rw [h] at h2
    have h4 : ‖y - x‖ ≤ 0 := by nlinarith
    have h5 : y - x = 0 := by simpa [norm_eq_zero] using h4
    have h6 : y = x := sub_eq_zero.mp h5
    exact h6.symm

  have h_comp : ∀ y, L (Φ y) = f y := by
    intro y
    have h1 : inner ℝ (Φ y - x₀) v = inner ℝ (y - x₀) v + h y := by
      have h2 : Φ y - x₀ = (y - x₀) + h y • v := by simp [Φ, h, L] <;> abel
      rw [h2]
      have h3 : inner ℝ ((y - x₀) + h y • v) v = inner ℝ (y - x₀) v + inner ℝ (h y • v) v := by
        rw [inner_add_left]
      rw [h3]
      have h4 : inner ℝ (h y • v) v = h y * inner ℝ v v := by
        rw [inner_smul_left] <;> simp
      rw [h4]
      have h5 : inner ℝ v v = ‖v‖ ^ 2 := real_inner_self_eq_norm_sq v
      rw [h5, hv_norm] <;> ring
    have h6 : L (Φ y) = f x₀ + inner ℝ (Φ y - x₀) v := by simp [L]
    rw [h6, h1]
    have h7 : f x₀ + (inner ℝ (y - x₀) v + h y) = f y := by
      have h8 : h y = f y - L y := by rfl
      rw [h8]
      simp [L] <;> abel
    exact h7

  intro C hC_compact hC_sub a b hab

  have hC_meas : MeasurableSet C := hC_compact.measurableSet
  have hC_in_ball : C ⊆ ball x₀ r := by
    intro x hx
    have h1 : x ∈ closedBall x₀ (r / 2) := hC_sub hx
    have h2 : dist x x₀ ≤ r / 2 := by simpa [mem_closedBall] using h1
    have h3 : dist x x₀ < r := by linarith [hr]
    simpa [mem_ball] using h3

  let S : Set (E n) := {x ∈ C | a < f x ∧ f x ≤ b}
  have hS_meas : MeasurableSet S := by
    have h2 : Measurable f := hf.continuous.measurable
    have h_lt : MeasurableSet {x | a < f x} := h2 isOpen_Ioi.measurableSet
    have h_le : MeasurableSet {x | f x ≤ b} := h2 isClosed_Iic.measurableSet
    exact hC_meas.inter (h_lt.inter h_le)

  have h_image_meas : MeasurableSet (Φ '' C) :=
    (hC_compact.image hΦ_cont).measurableSet

  have h_image_eq : Φ '' S = {y ∈ Φ '' C | a < L y ∧ L y ≤ b} := by
    ext z
    simp only [Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have h_xC : x ∈ C := hx.1
      have h_f : a < f x ∧ f x ≤ b := hx.2
      exact ⟨⟨x, h_xC, rfl⟩, by have h5 : L (Φ x) = f x := h_comp x; rw [h5] <;> exact h_f⟩
    · rintro ⟨⟨x, hxC, rfl⟩, hL⟩
      have h5 : L (Φ x) = f x := h_comp x
      rw [h5] at hL
      exact ⟨x, ⟨hxC, hL⟩, rfl⟩

  let K_inv : NNReal := ⟨1 / (1 - ε), by positivity⟩
  have hK_inv_coe : (K_inv : ℝ) = 1 / (1 - ε) := by
    exact NNReal.coe_mk (1 / (1 - ε)) (by positivity)
  let Φ_inv : E n → E n := Function.invFunOn Φ (ball x₀ r)

  have h_inv_eq : ∀ (x : E n), x ∈ ball x₀ r → Φ_inv (Φ x) = x := by
    intro x hx
    have h1 : Φ (Φ_inv (Φ x)) = Φ x := Function.invFunOn_apply_eq hx
    have h2 : Φ_inv (Φ x) ∈ ball x₀ r := Function.invFunOn_mem ⟨x, hx, rfl⟩
    exact hΦ_inj h2 hx h1

  have h_inv_lip : LipschitzOnWith K_inv Φ_inv (Φ '' S) :=
    LipschitzOnWith.of_dist_le_mul fun z1 hz1 z2 hz2 => by
      rcases hz1 with ⟨x1, hx1S, h_eq1⟩
      rcases hz2 with ⟨x2, hx2S, h_eq2⟩
      have hx1 : x1 ∈ ball x₀ r := hC_in_ball hx1S.1
      have hx2 : x2 ∈ ball x₀ r := hC_in_ball hx2S.1
      have h1 : Φ_inv z1 = x1 := by
        rw [h_eq1.symm]; exact h_inv_eq x1 hx1
      have h2 : Φ_inv z2 = x2 := by
        rw [h_eq2.symm]; exact h_inv_eq x2 hx2
      have h3 : (1 - ε) * ‖x2 - x1‖ ≤ ‖Φ x2 - Φ x1‖ := hΦ_lower x1 x2 hx1 hx2
      have h4 : (1 - ε) * ‖x2 - x1‖ ≤ ‖z2 - z1‖ := by
        rw [h_eq1, h_eq2] at h3; exact h3
      have h5 : 0 < 1 - ε := by linarith
      have h6 : ‖x2 - x1‖ ≤ (1 / (1 - ε)) * ‖z2 - z1‖ := by
        calc
          ‖x2 - x1‖
            = (1 / (1 - ε)) * ((1 - ε) * ‖x2 - x1‖) := by field_simp [h5.ne'] <;> ring
          _ ≤ (1 / (1 - ε)) * ‖z2 - z1‖ := by gcongr
      have h7 : ‖x1 - x2‖ = ‖x2 - x1‖ := norm_sub_rev x1 x2
      have h8 : ‖z1 - z2‖ = ‖z2 - z1‖ := norm_sub_rev z1 z2
      have h6' : ‖x1 - x2‖ ≤ (1 / (1 - ε)) * ‖z1 - z2‖ := by
        rw [h7, h8]; exact h6
      simpa [h1, h2, dist_eq_norm, hK_inv_coe] using h6'

  have h_image_inv : Φ_inv '' (Φ '' S) = S := by
    ext x
    simp only [Set.mem_image]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rcases hz with ⟨y, hyS, h_eq⟩
      have h6 : Φ_inv z = y := by
        have h_eq' : z = Φ y := h_eq.symm
        rw [h_eq']
        exact h_inv_eq y (hC_in_ball hyS.1)
      rw [h6]; exact hyS
    · intro hx
      have h_z_in : Φ x ∈ Φ '' S := ⟨x, hx, rfl⟩
      have h6 : Φ_inv (Φ x) = x := h_inv_eq x (hC_in_ball hx.1)
      exact ⟨Φ x, h_z_in, h6⟩

  have h_vol_le : volume S ≤ (K_inv : ENNReal) ^ n * volume (Φ '' S) := by
    have h : μHE[n] (Φ_inv '' (Φ '' S)) ≤ (K_inv : ENNReal) ^ n * μHE[n] (Φ '' S) :=
      euclideanHausdorff_image_le h_inv_lip (d := n)
    rw [h_image_inv] at h
    have h_vol : (μHE[n] : Measure (E n)) = volume :=
      EuclideanSpace.euclideanHausdorffMeasure_eq_volume n
    simpa [h_vol] using h

  let c : ℝ := f x₀ - inner ℝ x₀ v
  have hL_eq : ∀ y, L y = inner ℝ y v + c := by
    intro y; simp [L, c, inner_sub_left] <;> ring

  have h_fubini : volume (Φ '' S) =
      ∫⁻ s in Set.Ioc a b, μHE[n - 1] {y ∈ Φ '' C | L y = s} := by
    have h_set_eq : Φ '' S = {y ∈ Φ '' C | a < L y ∧ L y ≤ b} := h_image_eq
    rw [h_set_eq]
    have h2 : {y ∈ Φ '' C | a < L y ∧ L y ≤ b} =
        {y ∈ Φ '' C | a < inner ℝ y v + c ∧ inner ℝ y v + c ≤ b} := by
      ext y; simp [hL_eq]
    rw [h2]
    have h3 := linear_coarea_formula_shifted v hv_norm c (Φ '' C) h_image_meas a b hab
    have h4 : ∀ s, {y ∈ Φ '' C | inner ℝ y v + c = s} = {y ∈ Φ '' C | L y = s} := by
      intro s; ext y; simp [hL_eq]
    have h5 : ∫⁻ s in Set.Ioc a b, μHE[n - 1] {y ∈ Φ '' C | inner ℝ y v + c = s} =
        ∫⁻ s in Set.Ioc a b, μHE[n - 1] {y ∈ Φ '' C | L y = s} := by
      apply lintegral_congr; intro s; rw [h4 s]
    rw [h3, h5]

  let c_eps : ENNReal := ENNReal.ofReal (1 + ε)
  let K_upper : NNReal := ⟨1 + ε, by linarith⟩
  have hK_upper_coe : (K_upper : ℝ) = 1 + ε := by
    exact NNReal.coe_mk (1 + ε) (by linarith)
  have hK_upper_eq : (K_upper : ENNReal) = c_eps := by
    have h1 : (K_upper : ENNReal) = ENNReal.ofReal (K_upper : ℝ) := by simp
    rw [h1, hK_upper_coe] <;> rfl

  have h_hausdorff : ∀ (T : Set (E n)), T ⊆ C →
      μHE[n - 1] (Φ '' T) ≤ c_eps ^ (n - 1) * μHE[n - 1] T := by
    intro T hT_sub
    have hT_in_ball : T ⊆ ball x₀ r := hT_sub.trans hC_in_ball
    have h_lip_on : LipschitzOnWith K_upper Φ T :=
      LipschitzOnWith.of_dist_le_mul fun x hx y hy =>
        have h : ‖Φ y - Φ x‖ ≤ (1 + ε) * ‖y - x‖ :=
          hΦ_upper x y (hT_in_ball hx) (hT_in_ball hy)
        have h_sym1 : ‖Φ x - Φ y‖ = ‖Φ y - Φ x‖ := norm_sub_rev (Φ x) (Φ y)
        have h_sym2 : ‖x - y‖ = ‖y - x‖ := norm_sub_rev x y
        have h' : ‖Φ x - Φ y‖ ≤ (1 + ε) * ‖x - y‖ := by
          rw [h_sym1, h_sym2]; exact h
        have h'' : dist (Φ x) (Φ y) ≤ (K_upper : ℝ) * dist x y := by
          simpa [dist_eq_norm, hK_upper_coe] using h'
        h''
    have h := euclideanHausdorff_image_le h_lip_on (d := n - 1)
    rw [hK_upper_eq] at h
    exact h

  have h_level_eq : ∀ s, Φ '' ({x ∈ C | f x = s}) = {y ∈ Φ '' C | L y = s} := by
    intro s
    ext z
    simp only [Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have h_xC : x ∈ C := hx.1
      have h_f : f x = s := hx.2
      exact ⟨⟨x, h_xC, rfl⟩, by have h5 : L (Φ x) = f x := h_comp x; rw [h5, h_f]⟩
    · rintro ⟨⟨x, hxC, rfl⟩, hL⟩
      have h5 : L (Φ x) = f x := h_comp x
      rw [h5] at hL
      exact ⟨x, ⟨hxC, hL⟩, rfl⟩

  have h_integral_bound : ∫⁻ s in Set.Ioc a b, μHE[n - 1] {y ∈ Φ '' C | L y = s} ≤
      c_eps ^ (n - 1) * ∫⁻ s in Set.Ioc a b, μHE[n - 1] {x ∈ C | f x = s} := by
    have h_mono : ∀ᵐ (s : ℝ) ∂volume.restrict (Set.Ioc a b),
        μHE[n - 1] {y ∈ Φ '' C | L y = s} ≤
        c_eps ^ (n - 1) * μHE[n - 1] {x ∈ C | f x = s} := by
      filter_upwards with s
      have h6 : μHE[n - 1] {y ∈ Φ '' C | L y = s} = μHE[n - 1] (Φ '' ({x ∈ C | f x = s})) := by
        rw [h_level_eq s]
      rw [h6]
      exact h_hausdorff ({x ∈ C | f x = s}) (by simp)
    have h_bound1 := lintegral_mono_ae h_mono
    have h_c_finite : c_eps ^ (n - 1) ≠ ⊤ := by
      apply ENNReal.pow_ne_top
      exact ENNReal.ofReal_ne_top
    have h_bound2 : ∫⁻ s in Set.Ioc a b, c_eps ^ (n - 1) * μHE[n - 1] {x ∈ C | f x = s} =
        c_eps ^ (n - 1) * ∫⁻ s in Set.Ioc a b, μHE[n - 1] {x ∈ C | f x = s} :=
      lintegral_const_mul' (c_eps ^ (n - 1)) _ h_c_finite
    rw [h_bound2] at h_bound1
    exact h_bound1

  have hK_eq : (K_inv : ENNReal) = ENNReal.ofReal (1 / (1 - ε)) := by
    have h1 : (K_inv : ENNReal) = ENNReal.ofReal (K_inv : ℝ) := by simp
    rw [h1, hK_inv_coe] <;> rfl

  have h_final_eq : c_eps ^ (n - 1) * (K_inv : ENNReal) ^ n =
      ENNReal.ofReal (((1 + ε) ^ (n - 1)) / ((1 - ε) ^ n)) := by
    have h_pos1 : 0 < 1 + ε := by linarith
    have h_pos2 : 0 < 1 - ε := by linarith
    have h1 : c_eps = ENNReal.ofReal (1 + ε) := by rfl
    rw [h1, hK_eq]
    have h3 : ENNReal.ofReal (1 + ε) ^ (n - 1) = ENNReal.ofReal ((1 + ε) ^ (n - 1)) := by
      rw [ENNReal.ofReal_pow] <;> positivity
    have h4 : ENNReal.ofReal (1 / (1 - ε)) ^ n = ENNReal.ofReal ((1 / (1 - ε)) ^ n) := by
      rw [ENNReal.ofReal_pow] <;> positivity
    rw [h3, h4]
    have h_pos3 : 0 ≤ (1 + ε) ^ (n - 1) := by positivity
    have h_pos4 : 0 ≤ (1 / (1 - ε)) ^ n := by positivity
    have h_mul : ENNReal.ofReal (((1 + ε) ^ (n - 1)) * ((1 / (1 - ε)) ^ n)) =
        ENNReal.ofReal ((1 + ε) ^ (n - 1)) * ENNReal.ofReal ((1 / (1 - ε)) ^ n) := by
      exact ENNReal.ofReal_mul h_pos3
    rw [←h_mul]
    congr 1
    have h_div : (1 / (1 - ε)) ^ n = 1 / (1 - ε) ^ n := by
      rw [div_pow]
      <;> simp
    rw [h_div]
    <;> field_simp [h_pos2.ne'] <;> ring

  calc
    volume S
      ≤ (K_inv : ENNReal) ^ n * volume (Φ '' S) := h_vol_le
    _ = (K_inv : ENNReal) ^ n * (∫⁻ s in Set.Ioc a b, μHE[n - 1] {y ∈ Φ '' C | L y = s}) := by
      rw [h_fubini]
    _ ≤ (K_inv : ENNReal) ^ n * (c_eps ^ (n - 1) * ∫⁻ s in Set.Ioc a b, μHE[n - 1] {x ∈ C | f x = s}) := by
      gcongr
    _ = (c_eps ^ (n - 1) * (K_inv : ENNReal) ^ n) * ∫⁻ s in Set.Ioc a b, μHE[n - 1] {x ∈ C | f x = s} := by
      rw [mul_assoc, mul_left_comm]
    _ = ENNReal.ofReal (((1 + ε) ^ (n - 1)) / ((1 - ε) ^ n)) * ∫⁻ s in Set.Ioc a b, μHE[n - 1] {x ∈ C | f x = s} := by
      rw [h_final_eq]

/-- **Reverse local coarea inequality for Lipschitz functions.**

At `x₀` with `‖∇f(x₀)‖ = 1` and gradient `ε`-close a.e. on `ball x₀ r`,
for any compact `C ⊆ closedBall x₀ (r/2)`:
`volume {x ∈ C | a < f(x) ≤ b} ≥ ((1-ε)^{n-1}/(1+ε)^n) * ∫ₐᵇ μHE[n-1]({x ∈ C | f(x)=s}) ds`
-/
theorem local_coarea_lipschitz_reverse
    (f : E n → ℝ) (hf : LipschitzWith 1 f)
    (x₀ : E n) (h₁ : ‖fderiv ℝ f x₀‖ = 1)
    (r ε : ℝ) (hr : 0 < r) (hε : 0 < ε) (hε2 : ε < 1)
    (h_grad_close : ∀ᵐ (x : E n) ∂volume.restrict (ball x₀ r),
      ‖fderiv ℝ f x - fderiv ℝ f x₀‖ ≤ ε) :
    ∀ (C : Set (E n)), IsCompact C → C ⊆ closedBall x₀ (r / 2) →
      ∀ (a b : ℝ), a < b →
        volume {x ∈ C | a < f x ∧ f x ≤ b} ≥
          ENNReal.ofReal (((1 - ε) ^ (n - 1 : ℕ)) / ((1 + ε) ^ n)) *
          ∫⁻ s in Set.Ioc a b, μHE[n - 1] {x ∈ C | f x = s} := by
  let v : E n := (InnerProductSpace.toDual ℝ (E n)).symm (fderiv ℝ f x₀)
  have hv_norm : ‖v‖ = 1 := by
    have h : ‖v‖ = ‖fderiv ℝ f x₀‖ := (InnerProductSpace.toDual ℝ (E n)).symm.norm_map _
    rw [h, h₁]
  let L : E n → ℝ := fun y => f x₀ + inner ℝ (y - x₀) v
  let h : E n → ℝ := fun y => f y - L y
  have hL_lip : LipschitzWith 1 L := by
    refine' LipschitzWith.of_dist_le_mul fun y z => _
    have h_eq : dist (L y) (L z) = |inner ℝ (y - z) v| := by
      simp [L, dist_eq_norm, inner_sub_left] <;> ring_nf
    have h2 : |inner ℝ (y - z) v| ≤ ‖y - z‖ * ‖v‖ := abs_real_inner_le_norm (y - z) v
    rw [hv_norm] at h2
    have h3 : dist (L y) (L z) ≤ ‖y - z‖ := by rw [h_eq]; simpa using h2
    simpa [dist_eq_norm] using h3
  have h_fderiv_L : ∀ (x : E n), fderiv ℝ L x = fderiv ℝ f x₀ := by
    intro x
    have h_clm_eq : (fun y : E n => inner ℝ y v) = (innerSL ℝ v) := by
      funext z; simp [innerSL]; exact (real_inner_comm z v).symm
    have hL_eq2 : L = fun y : E n => (innerSL ℝ v) y + (f x₀ - inner ℝ x₀ v) := by
      funext y
      have h_eq : (innerSL ℝ v) y = inner ℝ y v := by rw [← h_clm_eq] <;> rfl
      simp [L, h_eq, inner_sub_left] <;> ring
    have h1 : fderiv ℝ L x = innerSL ℝ v := by
      rw [hL_eq2]
      have h_has : HasFDerivAt (fun y : E n => (innerSL ℝ v) y + (f x₀ - inner ℝ x₀ v)) (innerSL ℝ v) x :=
        (innerSL ℝ v).hasFDerivAt.add_const (f x₀ - inner ℝ x₀ v)
      exact h_has.fderiv
    rw [h1]
    have h4 : (InnerProductSpace.toDual ℝ (E n)) v = fderiv ℝ f x₀ :=
      (InnerProductSpace.toDual ℝ (E n)).apply_symm_apply (fderiv ℝ f x₀)
    have h5 : innerSL ℝ v = (InnerProductSpace.toDual ℝ (E n)) v := by rfl
    rw [h5, h4]
  have h_diff_ae : ∀ᵐ (x : E n) ∂volume.restrict (ball x₀ r), DifferentiableAt ℝ f x :=
    hf.ae_differentiableAt.filter_mono (ae_mono Measure.restrict_le_self)
  have h_fderiv_h : ∀ᵐ (x : E n) ∂volume.restrict (ball x₀ r),
      fderiv ℝ h x = fderiv ℝ f x - fderiv ℝ f x₀ := by
    filter_upwards [h_diff_ae] with x hx
    have hL_diff_at : DifferentiableAt ℝ L x := by
      have hL_diff : Differentiable ℝ L := by
        have h1 : Differentiable ℝ (fun y : E n => y - x₀) :=
          differentiable_id.sub (differentiable_const (c := x₀))
        have h_clm_eq : (fun z : E n => inner ℝ z v) = (innerSL ℝ v) := by
          funext z; simp [innerSL]; exact (real_inner_comm z v).symm
        have h2 : Differentiable ℝ (fun z : E n => inner ℝ z v) := by
          rw [h_clm_eq]; exact (innerSL ℝ v).differentiable
        have h3 : Differentiable ℝ (fun y : E n => inner ℝ (y - x₀) v) :=
          h2.comp h1
        exact h3.const_add (f x₀)
      exact hL_diff.differentiableAt
    have h2 : fderiv ℝ h x = fderiv ℝ f x - fderiv ℝ L x := by
      rw [show h = f - L from rfl]
      exact fderiv_sub hx hL_diff_at
    rw [h2, h_fderiv_L x]
  have h_grad_h : ∀ᵐ (x : E n) ∂volume.restrict (ball x₀ r), ‖fderiv ℝ h x‖ ≤ ε := by
    filter_upwards [h_fderiv_h, h_grad_close] with x h2 h3
    rw [h2] at *; exact h3
  have h_h_lip : ∀ (x y : E n), x ∈ ball x₀ r → y ∈ ball x₀ r →
      |h y - h x| ≤ ε * ‖y - x‖ := by
    have h2 := lipschitzOn_of_ae_norm_fderiv_le (hg := hf.sub hL_lip)
      (hs := convex_ball x₀ r) (hs_open := isOpen_ball) (C := ε) (hC := by linarith) h_grad_h
    intro x y hx hy
    have h3 : ‖h y - h x‖ ≤ ε * ‖y - x‖ := h2 x y hx hy
    simpa using h3
  let Φ : E n → E n := fun y => y + h y • v
  have hΦ_cont : Continuous Φ := by
    have h_h_cont : Continuous h := hf.continuous.sub hL_lip.continuous
    have h_smul : Continuous (fun y => h y • v) := h_h_cont.smul continuous_const
    exact continuous_id.add h_smul
  have hΦ_upper : ∀ (x y : E n), x ∈ ball x₀ r → y ∈ ball x₀ r →
      ‖Φ y - Φ x‖ ≤ (1 + ε) * ‖y - x‖ :=
    correction_upper_lipschitz (le_of_lt hε) h_h_lip hv_norm
  have hΦ_lower : ∀ (x y : E n), x ∈ ball x₀ r → y ∈ ball x₀ r →
      (1 - ε) * ‖y - x‖ ≤ ‖Φ y - Φ x‖ :=
    correction_lower_lipschitz (le_of_lt hε) hε2 h_h_lip hv_norm
  have hΦ_inj : Set.InjOn Φ (ball x₀ r) := by
    intro x hx y hy hxy
    have h : ‖Φ y - Φ x‖ = 0 := by rw [hxy] <;> simp
    have h2 : (1 - ε) * ‖y - x‖ ≤ ‖Φ y - Φ x‖ := hΦ_lower x y hx hy
    rw [h] at h2
    have h4 : ‖y - x‖ ≤ 0 := by nlinarith
    have h5 : y - x = 0 := by simpa [norm_eq_zero] using h4
    have h6 : y = x := sub_eq_zero.mp h5
    exact h6.symm
  have h_comp : ∀ y, L (Φ y) = f y := by
    intro y
    have h1 : inner ℝ (Φ y - x₀) v = inner ℝ (y - x₀) v + h y := by
      have h2 : Φ y - x₀ = (y - x₀) + h y • v := by simp [Φ, h, L] <;> abel
      rw [h2]
      have h3 : inner ℝ ((y - x₀) + h y • v) v = inner ℝ (y - x₀) v + inner ℝ (h y • v) v := by
        rw [inner_add_left]
      rw [h3]
      have h4 : inner ℝ (h y • v) v = h y * inner ℝ v v := by
        rw [inner_smul_left] <;> simp
      rw [h4]
      have h5 : inner ℝ v v = ‖v‖ ^ 2 := real_inner_self_eq_norm_sq v
      rw [h5, hv_norm] <;> ring
    have h6 : L (Φ y) = f x₀ + inner ℝ (Φ y - x₀) v := by simp [L]
    rw [h6, h1]
    have h7 : f x₀ + (inner ℝ (y - x₀) v + h y) = f y := by
      have h8 : h y = f y - L y := by rfl
      rw [h8]
      simp [L] <;> abel
    exact h7
  intro C hC_compact hC_sub a b hab
  have hC_meas : MeasurableSet C := hC_compact.measurableSet
  have hC_in_ball : C ⊆ ball x₀ r := by
    intro x hx
    have h1 : x ∈ closedBall x₀ (r / 2) := hC_sub hx
    have h2 : dist x x₀ ≤ r / 2 := by simpa [mem_closedBall] using h1
    have h3 : dist x x₀ < r := by linarith [hr]
    simpa [mem_ball] using h3
  let S : Set (E n) := {x ∈ C | a < f x ∧ f x ≤ b}
  have hS_meas : MeasurableSet S := by
    have h2 : Continuous f := hf.continuous
    have h_lt : MeasurableSet {x | a < f x} := isOpen_Ioi.preimage h2 |>.measurableSet
    have h_le : MeasurableSet {x | f x ≤ b} := isClosed_Iic.preimage h2 |>.measurableSet
    exact hC_meas.inter (h_lt.inter h_le)
  have h_image_meas : MeasurableSet (Φ '' C) :=
    (hC_compact.image hΦ_cont).measurableSet
  have h_image_eq : Φ '' S = {y ∈ Φ '' C | a < L y ∧ L y ≤ b} := by
    ext z
    simp only [Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have h_xC : x ∈ C := hx.1
      have h_f : a < f x ∧ f x ≤ b := hx.2
      exact ⟨⟨x, h_xC, rfl⟩, by have h5 : L (Φ x) = f x := h_comp x; rw [h5] <;> exact h_f⟩
    · rintro ⟨⟨x, hxC, rfl⟩, hL⟩
      have h5 : L (Φ x) = f x := h_comp x
      rw [h5] at hL
      exact ⟨x, ⟨hxC, hL⟩, rfl⟩
  let K_upper : NNReal := ⟨1 + ε, by linarith⟩
  have hK_upper_coe : (K_upper : ℝ) = 1 + ε := by
    exact NNReal.coe_mk (1 + ε) (by linarith)
  have hK_upper_eq : (K_upper : ENNReal) = ENNReal.ofReal (1 + ε) := by
    have h1 : (K_upper : ENNReal) = ENNReal.ofReal (K_upper : ℝ) := by simp
    rw [h1, hK_upper_coe] <;> rfl
  let K_inv : NNReal := ⟨1 / (1 - ε), by positivity⟩
  have hK_inv_coe : (K_inv : ℝ) = 1 / (1 - ε) := by
    exact NNReal.coe_mk (1 / (1 - ε)) (by positivity)
  let Φ_inv : E n → E n := Function.invFunOn Φ (ball x₀ r)
  have h_inv_eq : ∀ (x : E n), x ∈ ball x₀ r → Φ_inv (Φ x) = x := by
    intro x hx
    have h1 : Φ (Φ_inv (Φ x)) = Φ x := Function.invFunOn_apply_eq hx
    have h2 : Φ_inv (Φ x) ∈ ball x₀ r := Function.invFunOn_mem ⟨x, hx, rfl⟩
    exact hΦ_inj h2 hx h1
  have h_image_inv : Φ_inv '' (Φ '' S) = S := by
    ext x
    simp only [Set.mem_image]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rcases hz with ⟨y, hyS, h_eq⟩
      have h6 : Φ_inv z = y := by
        have h_eq' : z = Φ y := h_eq.symm
        rw [h_eq']
        exact h_inv_eq y (hC_in_ball hyS.1)
      rw [h6]; exact hyS
    · intro hx
      have h_z_in : Φ x ∈ Φ '' S := ⟨x, hx, rfl⟩
      have h6 : Φ_inv (Φ x) = x := h_inv_eq x (hC_in_ball hx.1)
      exact ⟨Φ x, h_z_in, h6⟩
  have h_vol_upper : volume (Φ '' S) ≤ (K_upper : ENNReal) ^ n * volume S := by
    have h_lip_on : LipschitzOnWith K_upper Φ S :=
      LipschitzOnWith.of_dist_le_mul fun x hx y hy =>
        have h : ‖Φ y - Φ x‖ ≤ (1 + ε) * ‖y - x‖ :=
          hΦ_upper x y (hC_in_ball hx.1) (hC_in_ball hy.1)
        have h_sym1 : ‖Φ x - Φ y‖ = ‖Φ y - Φ x‖ := norm_sub_rev (Φ x) (Φ y)
        have h_sym2 : ‖x - y‖ = ‖y - x‖ := norm_sub_rev x y
        have h' : ‖Φ x - Φ y‖ ≤ (1 + ε) * ‖x - y‖ := by
          rw [h_sym1, h_sym2]; exact h
        have h'' : dist (Φ x) (Φ y) ≤ (K_upper : ℝ) * dist x y := by
          simpa [dist_eq_norm, hK_upper_coe] using h'
        h''
    have h : μHE[n] (Φ '' S) ≤ (K_upper : ENNReal) ^ n * μHE[n] S :=
      euclideanHausdorff_image_le h_lip_on (d := n)
    have h_vol : (μHE[n] : Measure (E n)) = volume :=
      EuclideanSpace.euclideanHausdorffMeasure_eq_volume n
    simpa [h_vol] using h
  have h_vol_lower : volume S ≥ (ENNReal.ofReal (1 / (1 + ε)) ^ n) * volume (Φ '' S) := by
    have h_pos : 0 < 1 + ε := by linarith
    set a : ENNReal := ENNReal.ofReal (1 / (1 + ε)) ^ n with ha_def
    set c : ENNReal := (K_upper : ENNReal) ^ n with hc_def
    have h_ac : a * c = 1 := by
      have hK : (K_upper : ENNReal) = ENNReal.ofReal (1 + ε) := hK_upper_eq
      have h1 : a = ENNReal.ofReal ((1 / (1 + ε)) ^ n) := by
        rw [ha_def, ENNReal.ofReal_pow (by positivity)]
      have h2 : c = ENNReal.ofReal ((1 + ε) ^ n) := by
        rw [hc_def, hK, ENNReal.ofReal_pow (by linarith)]
      rw [h1, h2]
      have h3 : (1 / (1 + ε)) ^ n * (1 + ε) ^ n = 1 := by
        have h4 : (1 / (1 + ε)) * (1 + ε) = 1 := by field_simp [h_pos.ne']
        have h5 : (1 / (1 + ε)) ^ n * (1 + ε) ^ n = ((1 / (1 + ε)) * (1 + ε)) ^ n := by
          rw [← mul_pow]
        rw [h5, h4] <;> simp
      rw [← ENNReal.ofReal_mul (by positivity), h3] <;> simp
    have h1 : c * volume S ≥ volume (Φ '' S) := h_vol_upper
    have h3 : a * volume (Φ '' S) ≤ a * (c * volume S) := by
      exact mul_le_mul_left' h1 a
    have h4 : a * (c * volume S) = (a * c) * volume S := by rw [mul_assoc]
    rw [h4] at h3
    rw [h_ac] at h3
    simpa using h3
  let c : ℝ := f x₀ - inner ℝ x₀ v
  have hL_eq : ∀ y, L y = inner ℝ y v + c := by
    intro y; simp [L, c, inner_sub_left] <;> ring
  have h_fubini : volume (Φ '' S) =
      ∫⁻ s in Set.Ioc a b, μHE[n - 1] {y ∈ Φ '' C | L y = s} := by
    have h_set_eq : Φ '' S = {y ∈ Φ '' C | a < L y ∧ L y ≤ b} := h_image_eq
    rw [h_set_eq]
    have h2 : {y ∈ Φ '' C | a < L y ∧ L y ≤ b} =
        {y ∈ Φ '' C | a < inner ℝ y v + c ∧ inner ℝ y v + c ≤ b} := by
      ext y; simp [hL_eq]
    rw [h2]
    have h3 := linear_coarea_formula_shifted v hv_norm c (Φ '' C) h_image_meas a b hab
    have h4 : ∀ s, {y ∈ Φ '' C | inner ℝ y v + c = s} = {y ∈ Φ '' C | L y = s} := by
      intro s; ext y; simp [hL_eq]
    have h5 : ∫⁻ s in Set.Ioc a b, μHE[n - 1] {y ∈ Φ '' C | inner ℝ y v + c = s} =
        ∫⁻ s in Set.Ioc a b, μHE[n - 1] {y ∈ Φ '' C | L y = s} := by
      apply lintegral_congr; intro s; rw [h4 s]
    rw [h3, h5]
  have h_level_eq : ∀ s, Φ '' ({x ∈ C | f x = s}) = {y ∈ Φ '' C | L y = s} := by
    intro s
    ext z
    simp only [Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have h_xC : x ∈ C := hx.1
      have h_f : f x = s := hx.2
      exact ⟨⟨x, h_xC, rfl⟩, by have h5 : L (Φ x) = f x := h_comp x; rw [h5, h_f]⟩
    · rintro ⟨⟨x, hxC, rfl⟩, hL⟩
      have h5 : L (Φ x) = f x := h_comp x
      rw [h5] at hL
      exact ⟨x, ⟨hxC, hL⟩, rfl⟩
  have h_inv_lip_on : LipschitzOnWith K_inv Φ_inv (Φ '' C) :=
    LipschitzOnWith.of_dist_le_mul fun z1 hz1 z2 hz2 => by
      rcases hz1 with ⟨x1, hx1C, h_eq1⟩
      rcases hz2 with ⟨x2, hx2C, h_eq2⟩
      have hx1 : x1 ∈ ball x₀ r := hC_in_ball hx1C
      have hx2 : x2 ∈ ball x₀ r := hC_in_ball hx2C
      have h1 : Φ_inv z1 = x1 := by
        rw [h_eq1.symm]; exact h_inv_eq x1 hx1
      have h2 : Φ_inv z2 = x2 := by
        rw [h_eq2.symm]; exact h_inv_eq x2 hx2
      have h3 : (1 - ε) * ‖x2 - x1‖ ≤ ‖Φ x2 - Φ x1‖ := hΦ_lower x1 x2 hx1 hx2
      have h4 : (1 - ε) * ‖x2 - x1‖ ≤ ‖z2 - z1‖ := by
        rw [h_eq1, h_eq2] at h3; exact h3
      have h5 : 0 < 1 - ε := by linarith
      have h6 : ‖x2 - x1‖ ≤ (1 / (1 - ε)) * ‖z2 - z1‖ := by
        calc
          ‖x2 - x1‖
            = (1 / (1 - ε)) * ((1 - ε) * ‖x2 - x1‖) := by field_simp [h5.ne'] <;> ring
          _ ≤ (1 / (1 - ε)) * ‖z2 - z1‖ := by gcongr
      have h7 : ‖x1 - x2‖ = ‖x2 - x1‖ := norm_sub_rev x1 x2
      have h8 : ‖z1 - z2‖ = ‖z2 - z1‖ := norm_sub_rev z1 z2
      have h6' : ‖x1 - x2‖ ≤ (1 / (1 - ε)) * ‖z1 - z2‖ := by
        rw [h7, h8]; exact h6
      simpa [h1, h2, dist_eq_norm, hK_inv_coe] using h6'
  have h_hausdorff_lower : ∀ (T : Set (E n)), T ⊆ C →
      μHE[n - 1] (Φ '' T) ≥ (ENNReal.ofReal (1 - ε) ^ (n - 1)) * μHE[n - 1] T := by
    intro T hT_sub
    have hT_in_ball : T ⊆ ball x₀ r := hT_sub.trans hC_in_ball
    have h_image_inv_T : Φ_inv '' (Φ '' T) = T := by
      ext x
      simp only [Set.mem_image]
      constructor
      · rintro ⟨z, hz, rfl⟩
        rcases hz with ⟨y, hyT, h_eq⟩
        have h6 : Φ_inv z = y := by
          have h_eq' : z = Φ y := h_eq.symm
          rw [h_eq']
          exact h_inv_eq y (hT_in_ball hyT)
        rw [h6]; exact hyT
      · intro hx
        have h_z_in : Φ x ∈ Φ '' T := ⟨x, hx, rfl⟩
        have h6 : Φ_inv (Φ x) = x := h_inv_eq x (hT_in_ball hx)
        exact ⟨Φ x, h_z_in, h6⟩
    have h_upper_bound : μHE[n - 1] T ≤ (K_inv : ENNReal) ^ (n - 1) * μHE[n - 1] (Φ '' T) := by
      have hT_image_sub : Φ '' T ⊆ Φ '' C := by
        intro z hz; rcases hz with ⟨x, hx, rfl⟩; exact ⟨x, hT_sub hx, rfl⟩
      have h_lip_on' : LipschitzOnWith K_inv Φ_inv (Φ '' T) := h_inv_lip_on.mono hT_image_sub
      have h : μHE[n - 1] (Φ_inv '' (Φ '' T)) ≤ (K_inv : ENNReal) ^ (n - 1) * μHE[n - 1] (Φ '' T) :=
        euclideanHausdorff_image_le h_lip_on' (d := n - 1)
      rw [h_image_inv_T] at h
      exact h
    have hK_inv_eq : (K_inv : ENNReal) = ENNReal.ofReal (1 / (1 - ε)) := by
      have h1 : (K_inv : ENNReal) = ENNReal.ofReal (K_inv : ℝ) := by simp
      rw [h1, hK_inv_coe] <;> rfl
    have h_pos : 0 < 1 - ε := by linarith
    set a2 : ENNReal := ENNReal.ofReal (1 - ε) ^ (n - 1) with ha2_def
    set c2 : ENNReal := (K_inv : ENNReal) ^ (n - 1) with hc2_def
    have h_a2c2 : a2 * c2 = 1 := by
      rw [ha2_def, hc2_def, hK_inv_eq]
      have h4 : ENNReal.ofReal (1 - ε) ^ (n - 1) = ENNReal.ofReal ((1 - ε) ^ (n - 1)) := by
        rw [ENNReal.ofReal_pow (by positivity)]
      have h5 : ENNReal.ofReal (1 / (1 - ε)) ^ (n - 1) = ENNReal.ofReal ((1 / (1 - ε)) ^ (n - 1)) := by
        rw [ENNReal.ofReal_pow (by positivity)]
      rw [h4, h5]
      have h6 : (1 - ε) ^ (n - 1) * (1 / (1 - ε)) ^ (n - 1) = 1 := by
        have h7 : (1 - ε) * (1 / (1 - ε)) = 1 := by field_simp [h_pos.ne']
        have h8 : (1 - ε) ^ (n - 1) * (1 / (1 - ε)) ^ (n - 1) = ((1 - ε) * (1 / (1 - ε))) ^ (n - 1) := by
          rw [← mul_pow]
        rw [h8, h7] <;> simp
      rw [← ENNReal.ofReal_mul (by positivity), h6] <;> simp
    have h7 : a2 * μHE[n - 1] T ≤ a2 * (c2 * μHE[n - 1] (Φ '' T)) := by
      exact mul_le_mul_left' h_upper_bound a2
    have h8 : a2 * (c2 * μHE[n - 1] (Φ '' T)) = (a2 * c2) * μHE[n - 1] (Φ '' T) := by rw [mul_assoc]
    rw [h8] at h7
    rw [h_a2c2] at h7
    simpa using h7
  have h_integral_lower : ∫⁻ s in Set.Ioc a b, μHE[n - 1] {y ∈ Φ '' C | L y = s} ≥
      (ENNReal.ofReal (1 - ε) ^ (n - 1)) * ∫⁻ s in Set.Ioc a b, μHE[n - 1] {x ∈ C | f x = s} := by
    have h_mono : ∀ᵐ (s : ℝ) ∂volume.restrict (Set.Ioc a b),
        μHE[n - 1] {y ∈ Φ '' C | L y = s} ≥
        (ENNReal.ofReal (1 - ε) ^ (n - 1)) * μHE[n - 1] {x ∈ C | f x = s} := by
      filter_upwards with s
      have h6 : μHE[n - 1] {y ∈ Φ '' C | L y = s} = μHE[n - 1] (Φ '' ({x ∈ C | f x = s})) := by
        rw [h_level_eq s]
      rw [h6]
      exact h_hausdorff_lower ({x ∈ C | f x = s}) (by simp)
    have h_bound1 := lintegral_mono_ae h_mono
    have h_c_finite : (ENNReal.ofReal (1 - ε) ^ (n - 1)) ≠ ⊤ := by
      apply ENNReal.pow_ne_top
      exact ENNReal.ofReal_ne_top
    have h_bound2 : ∫⁻ s in Set.Ioc a b, (ENNReal.ofReal (1 - ε) ^ (n - 1)) * μHE[n - 1] {x ∈ C | f x = s} =
        (ENNReal.ofReal (1 - ε) ^ (n - 1)) * ∫⁻ s in Set.Ioc a b, μHE[n - 1] {x ∈ C | f x = s} :=
      lintegral_const_mul' (ENNReal.ofReal (1 - ε) ^ (n - 1)) _ h_c_finite
    rw [h_bound2] at h_bound1
    exact h_bound1
  have h_final_eq : (ENNReal.ofReal (1 / (1 + ε)) ^ n) * (ENNReal.ofReal (1 - ε) ^ (n - 1)) =
      ENNReal.ofReal (((1 - ε) ^ (n - 1)) / ((1 + ε) ^ n)) := by
    have h_pos1 : 0 < 1 + ε := by linarith
    have h_pos2 : 0 < 1 - ε := by linarith
    have h1 : ENNReal.ofReal (1 / (1 + ε)) ^ n = ENNReal.ofReal ((1 / (1 + ε)) ^ n) := by
      rw [ENNReal.ofReal_pow] <;> positivity
    have h2 : ENNReal.ofReal (1 - ε) ^ (n - 1) = ENNReal.ofReal ((1 - ε) ^ (n - 1)) := by
      rw [ENNReal.ofReal_pow] <;> positivity
    rw [h1, h2]
    have h3 : 0 ≤ (1 / (1 + ε)) ^ n := by positivity
    have h4 : 0 ≤ (1 - ε) ^ (n - 1) := by positivity
    have h_mul : ENNReal.ofReal (((1 / (1 + ε)) ^ n) * ((1 - ε) ^ (n - 1))) =
        ENNReal.ofReal ((1 / (1 + ε)) ^ n) * ENNReal.ofReal ((1 - ε) ^ (n - 1)) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
    rw [←h_mul]
    congr 1
    have h_div : (1 / (1 + ε)) ^ n = 1 / (1 + ε) ^ n := by
      rw [div_pow] <;> simp
    rw [h_div]
    <;> field_simp [h_pos1.ne', h_pos2.ne'] <;> ring
  calc
    volume S
      ≥ (ENNReal.ofReal (1 / (1 + ε)) ^ n) * volume (Φ '' S) := h_vol_lower
    _ = (ENNReal.ofReal (1 / (1 + ε)) ^ n) * (∫⁻ s in Set.Ioc a b, μHE[n - 1] {y ∈ Φ '' C | L y = s}) := by
      rw [h_fubini]
    _ ≥ (ENNReal.ofReal (1 / (1 + ε)) ^ n) * ((ENNReal.ofReal (1 - ε) ^ (n - 1)) * ∫⁻ s in Set.Ioc a b, μHE[n - 1] {x ∈ C | f x = s}) := by
      gcongr
    _ = ((ENNReal.ofReal (1 / (1 + ε)) ^ n) * (ENNReal.ofReal (1 - ε) ^ (n - 1))) * ∫⁻ s in Set.Ioc a b, μHE[n - 1] {x ∈ C | f x = s} := by
      rw [mul_assoc]
    _ = ENNReal.ofReal (((1 - ε) ^ (n - 1)) / ((1 + ε) ^ n)) * ∫⁻ s in Set.Ioc a b, μHE[n - 1] {x ∈ C | f x = s} := by
      rw [h_final_eq]

end Geometry
