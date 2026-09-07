/-
# Reduced Boundary Data and Blow-Up Lemma Assembly

Defines `ReducedBoundaryData` — the explicit GMT assumptions needed at a
reduced boundary point — and proves `reduced_boundary_blowup_data`
conditional on these assumptions plus the half-space characterization lemma.

## Main definitions

- `ReducedBoundaryData S x ν`: bundles the key properties at a reduced
  boundary point: blow-up bounds, directional variation vanishing,
  half-ball density, and orientation.

## Main results

- `halfspace_identification`: zero directional variation + orientation +
  half-ball density → F is a.e. the half-space `{inner y ν < 0}`
- `reduced_boundary_blowup_data`: all blow-up data needed for the
  blow-up lemma, proved from `ReducedBoundaryData`

## References

- Maggi, Sets of Finite Perimeter, Theorem 15.5
- Ambrosio-Fusco-Pallara, Functions of BV, Theorem 3.59
-/

import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.Basic
import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.DirectionalVariationLemmas
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.BlowUpScaling
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.HalfSpaceCharacterization
import Mathlib.Tactic


open MeasureTheory Metric Set ENNReal Filter
open scoped MeasureTheory ContDiff

namespace Geometry.StructureTheorem

variable {n : ℕ}

/-- Symmetric difference of two sets. -/
def symmDiff {α : Type*} (A B : Set α) : Set α := (A \ B) ∪ (B \ A)

/-- The two `symmDiff` definitions are equal. -/
lemma symmDiff_eq (A B : Set (E n)) :
    symmDiff A B = symmDiff A B := by
  rfl

/-- **Reduced boundary data** — the explicit GMT assumptions at a reduced
boundary point x with normal ν.

These properties are the standard consequences of x being a reduced boundary
point (Maggi §15). The `density` field (half-ball density of blow-ups) is
the strengthened form that enables the half-space identification. -/
structure ReducedBoundaryData (S : Set (E n)) (x : E n) (ν : E n) : Prop where
  h_vol_bound : ∀ (K : Set (E n)), IsCompact K →
    ∃ (C : ENNReal), ∀ (r : ℝ), 0 < r → r < 1 →
      volume (blowUp S x r ∩ K) ≤ C
  h_trans_bound : ∀ (K : Set (E n)), IsCompact K →
    ∃ (C : ℝ), ∀ (r : ℝ), 0 < r → r < 1 → ∀ (h : E n),
      volume (symmDiff (blowUp S x r) ((fun y => y + h) '' (blowUp S x r)) ∩ K) ≤
      ENNReal.ofReal (C * ‖h‖)
  h_directional_vanishing : ∀ (K : Set (E n)), IsCompact K → ∀ (w : E n), inner ℝ w ν = 0 →
    Filter.Tendsto (fun r : ℝ => Perimeter.directionalVariationIn (blowUp S x r) w K)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)
  density : Tendsto (fun r : ℝ => volume (blowUp S x r ∩ ball (0 : E n) 1))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (volume (ball (0 : E n) 1) / 2))
  /-- Eventual orientation: for every non-negative smooth compactly supported
  `φ` with `φ 0 > 0`, there exists `r₀ > 0` such that the ν-directional
  derivative integral over the blow-up is non-negative for all `0 < r < r₀`.
  The `φ 0 > 0` condition is sufficient: see `orientation_weak_to_strong`
  for the bridge to all test functions at the blow-up limit level. -/
  h_orientation : ∀ (φ : E n → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
    (∀ x, 0 ≤ φ x) → 0 < φ 0 →
      ∃ (r₀ : ℝ), 0 < r₀ ∧ ∀ (r : ℝ), 0 < r → r < r₀ →
        0 ≤ ∫ x in blowUp S x r, fderiv ℝ φ x ν

/-- **Half-space volume at zero**: `volume({y | inner y ν < 0} ∩ ball 0 1) =
volume(ball 0 1) / 2`, by reflection through the origin. -/
lemma halfspace_volume_at_zero {ν : E n} (hν_unit : ‖ν‖ = 1) :
    volume ({y : E n | inner ℝ y ν < 0} ∩ ball (0 : E n) 1) =
    volume (ball (0 : E n) 1) / 2 := by
  let B := ball (0 : E n) 1
  let Hneg := {y : E n | inner ℝ y ν < 0} ∩ B
  let Hpos := {y : E n | inner ℝ y ν > 0} ∩ B
  let Hzero := {y : E n | inner ℝ y ν = 0} ∩ B
  have hν_ne : ν ≠ 0 := by intro h; rw [h] at hν_unit; simp at hν_unit
  let f : E n →ₗ[ℝ] ℝ :=
    { toFun := fun x => inner ℝ x ν
      map_add' := fun x y => inner_add_left x y ν
      map_smul' := fun c x => by simp [inner_smul_left] }
  let K : Submodule ℝ (E n) := LinearMap.ker f
  have hK_proper : K ≠ ⊤ := by
    intro h; have h1 : ν ∈ K := by rw [h]; trivial
    have h2 : f ν = 0 := by simpa [K] using h1
    have h3 : f ν = inner ℝ ν ν := by rfl
    have h4 : inner ℝ ν ν = 0 := by rw [← h3, h2]
    have h5 : inner ℝ ν ν = ‖ν‖ ^ 2 := by exact inner_self_eq_norm_sq_to_K ν
    rw [h5] at h4; rw [hν_unit] at h4; norm_num at h4
  let A : AffineSubspace ℝ (E n) := AffineSubspace.mk' 0 K
  have hA_proper : A ≠ ⊤ := by
    intro h; have h6 : A.direction = ⊤ := by rw [h] <;> simp
    have h8 : A.direction = K := by simp [A]
    have h7 : K = ⊤ := by
      rw [←h8]
      exact h6
    exact hK_proper h7
  have hK_null : volume (K : Set (E n)) = 0 := by
    have h : volume (A : Set (E n)) = 0 := Measure.addHaar_affineSubspace volume A hA_proper
    have hA_eq : (A : Set (E n)) = (K : Set (E n)) := by
      ext x; simp [A, AffineSubspace.mk', Submodule.zero_mem K] <;> tauto
    rw [hA_eq] at h; exact h
  have h_zero_null : volume Hzero = 0 := by
    have h5 : Hzero ⊆ (K : Set (E n)) := by
      intro x hx
      have h_inner : inner ℝ x ν = 0 := hx.1
      have hfx : f x = 0 := by simpa [f] using h_inner
      exact hfx
    exact measure_mono_null h5 (by simpa using hK_null)
  let neg_lie : E n ≃ₗᵢ[ℝ] E n := LinearIsometryEquiv.neg ℝ
  let neg : E n ≃ E n := neg_lie.toEquiv
  have hmp : MeasurePreserving neg volume := LinearIsometryEquiv.measurePreserving neg_lie
  have h_img : neg '' Hneg = Hpos := by
    ext z
    simp only [Set.mem_image, Hneg, Hpos, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
      have hny : -y ∈ B := by simpa [B, dist_zero_right, norm_neg] using hy2
      have h_inner : inner ℝ (-y) ν = -inner ℝ y ν := by rw [inner_neg_left]
      have h_gt : 0 < inner ℝ (-y) ν := by rw [h_inner]; exact neg_pos_of_neg hy1
      exact ⟨h_gt, hny⟩
    · rintro ⟨hz1, hz2⟩
      have hnz : -z ∈ B := by simpa [B, dist_zero_right, norm_neg] using hz2
      have h_inner : inner ℝ (-z) ν = -inner ℝ z ν := by rw [inner_neg_left]
      have h_lt : inner ℝ (-z) ν < 0 := by rw [h_inner] <;> linarith
      refine ⟨-z, ⟨h_lt, hnz⟩, ?_⟩
      have h_eq : neg (-z) = z := by
        have h2 : neg z = -z := by rfl
        have h3 : neg (neg z) = z := neg_lie.left_inv z
        rw [h2] at h3; exact h3
      exact h_eq
  have hHneg_meas : MeasurableSet Hneg := by
    exact (isOpen_lt (by fun_prop) continuous_const |>.measurableSet).inter isOpen_ball.measurableSet
  have h_neg_eq_pos : volume Hneg = volume Hpos := by
    have hmp_symm : MeasurePreserving neg.symm volume := LinearIsometryEquiv.measurePreserving neg_lie.symm
    have h1 : neg '' Hneg = neg.symm ⁻¹' Hneg := by
      ext y; simp [Set.mem_image, Set.mem_preimage] <;> constructor <;> rintro ⟨x, hx, rfl⟩ <;> exact ⟨x, hx, rfl⟩
    have h : volume (neg '' Hneg) = volume Hneg := by
      rw [h1]; exact hmp_symm.measure_preimage hHneg_meas.nullMeasurableSet
    rw [h_img] at h; exact h.symm
  have hHzero_meas : MeasurableSet Hzero := by
    exact (isClosed_eq (by fun_prop) continuous_const |>.measurableSet).inter isOpen_ball.measurableSet
  have hHpos_meas : MeasurableSet Hpos := by
    exact (isOpen_lt continuous_const (by fun_prop) |>.measurableSet).inter isOpen_ball.measurableSet
  have h_disj1 : Disjoint Hneg Hzero := by
    rw [Set.disjoint_left]; intro x h1 h2
    have h1' : inner ℝ x ν < 0 := h1.1; have h2' : inner ℝ x ν = 0 := h2.1
    exact h1'.ne h2'
  have h_disj2 : Disjoint (Hneg ∪ Hzero) Hpos := by
    rw [Set.disjoint_left]; intro x h1 h2
    have h2' : 0 < inner ℝ x ν := h2.1
    rcases h1 with (h1 | h1)
    · have h1' : inner ℝ x ν < 0 := h1.1; linarith
    · have h1' : inner ℝ x ν = 0 := h1.1; linarith
  have h_union : Hneg ∪ Hzero ∪ Hpos = B := by
    ext y
    simp only [Hneg, Hzero, Hpos, B, Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · intro h; have h10 : Hneg ∪ Hzero ∪ Hpos ⊆ B := Set.union_subset (Set.union_subset (fun _ hz => hz.2) (fun _ hz => hz.2)) (fun _ hz => hz.2); exact h10 h
    · intro hyB
      by_cases h : inner ℝ y ν < 0
      · exact Or.inl (Or.inl ⟨h, hyB⟩)
      · by_cases h2 : inner ℝ y ν = 0
        · exact Or.inl (Or.inr ⟨h2, hyB⟩)
        · have h3 : 0 < inner ℝ y ν := by
            have h4 : ¬inner ℝ y ν < 0 := h; have h5 : ¬inner ℝ y ν = 0 := h2
            exact lt_of_not_ge (fun h6 => h5 (le_antisymm h6 (le_of_not_gt h4)))
          exact Or.inr ⟨h3, hyB⟩
  have h_vol1 : volume (Hneg ∪ Hzero) = volume Hneg + volume Hzero := by
    rw [measure_union h_disj1 hHzero_meas]
  have h_vol2 : volume B = volume (Hneg ∪ Hzero) + volume Hpos := by
    rw [← h_union, measure_union h_disj2 hHpos_meas]
  have h_volB : volume B = volume Hneg + volume Hzero + volume Hpos := by
    rw [h_vol2, h_vol1] <;> simp
  have h_eq : volume B = volume Hneg + volume Hneg := by
    rw [h_volB, h_zero_null, h_neg_eq_pos] <;> simp
  have h_eq2 : volume B = 2 * volume Hneg := by rw [h_eq] <;> simp [two_mul]
  have h_final : volume Hneg = volume B / 2 := by
    rw [h_eq2]
    have h_ne_zero : (2 : ENNReal) ≠ 0 := by norm_num
    have h_ne_top : (2 : ENNReal) ≠ ⊤ := by norm_num
    have h : (volume Hneg * (2 : ENNReal)) / (2 : ENNReal) = volume Hneg :=
      ENNReal.mul_div_cancel_right h_ne_zero h_ne_top
    have h_comm : (2 * volume Hneg) / 2 = (volume Hneg * (2 : ENNReal)) / (2 : ENNReal) := by
      congr 1; exact mul_comm (2 : ENNReal) (volume Hneg)
    rw [h_comm]; exact h.symm
  exact h_final

/-- **Density forces α = 0**: if `F =ᵐ {inner < α}` and `F` has half-ball
density at the origin, then `α = 0`. -/
lemma halfspace_density_alpha_zero {ν : E n} (hν_unit : ‖ν‖ = 1)
    (α : ℝ) (F : Set (E n))
    (hα : ∀ᵐ (z : E n) ∂volume, (z ∈ F ↔ inner ℝ z ν < α))
    (h_density : volume (Set.inter F (ball (0 : E n) 1)) = volume (ball (0 : E n) 1) / 2) :
    α = 0 := by
  let B : Set (E n) := ball (0 : E n) 1
  let H : ℝ → Set (E n) := fun t => {y | inner ℝ y ν < t}
  let HtB : ℝ → Set (E n) := fun t => Set.inter (H t) B
  have hF_Hα : Set.inter F B =ᵐ[volume] HtB α := by
    filter_upwards [hα] with z hz
    have h : (z ∈ Set.inter F B) ↔ (z ∈ HtB α) := by
      constructor
      · intro ⟨h1, h2⟩; simp only [HtB, H, Set.mem_inter_iff, Set.mem_setOf_eq]; exact ⟨hz.mp h1, h2⟩
      · intro h; simp only [HtB, H, Set.mem_inter_iff, Set.mem_setOf_eq] at h; exact ⟨hz.mpr h.1, h.2⟩
    exact propext h
  have hvol : volume (HtB α) = volume B / 2 := by
    rw [← measure_congr hF_Hα, h_density]
  have h_f0 : volume (HtB 0) = volume B / 2 := halfspace_volume_at_zero hν_unit
  have hB_lt_top : volume B < ⊤ := measure_ball_lt_top
  have hB_meas : MeasurableSet B := isOpen_ball.measurableSet
  have hH_meas : ∀ t, MeasurableSet (H t) := by
    intro t; exact isOpen_lt (by fun_prop) continuous_const |>.measurableSet
  have hHtB_meas : ∀ t, MeasurableSet (HtB t) := by
    intro t; exact (hH_meas t).inter hB_meas
  have h_strict_mono : ∀ (s t : ℝ), s < t → (s < 1 ∧ -1 < t) → volume (HtB s) < volume (HtB t) := by
    intro s t hst h_range
    have h_exists : ∃ (c : ℝ), s < c ∧ c < t ∧ |c| < 1 := by
      let lower := max s (-1 : ℝ); let upper := min t (1 : ℝ)
      have h_s_lt_t : s < t := hst
      have h_s_lt_1 : s < 1 := h_range.1
      have h_neg1_lt_t : -1 < t := h_range.2
      have h_lower_lt_upper : lower < upper := by
        have h1 : s < upper := by exact lt_min h_s_lt_t h_s_lt_1
        have h2 : (-1 : ℝ) < upper := by exact lt_min h_neg1_lt_t (by norm_num)
        exact max_lt h1 h2
      set c : ℝ := (lower + upper) / 2 with hc_def
      have hc1 : lower < c := by rw [hc_def]; linarith [h_lower_lt_upper]
      have hc2 : c < upper := by rw [hc_def]; linarith [h_lower_lt_upper]
      have h1 : s < c := by have h_s_le_lower : s ≤ lower := le_max_left s (-1 : ℝ); linarith
      have h2 : c < t := by have h_upper_le_t : upper ≤ t := min_le_left t (1 : ℝ); linarith
      have h3 : -1 < c := by have h_neg1_le_lower : -1 ≤ lower := le_max_right s (-1 : ℝ); linarith
      have h4 : c < 1 := by have h_upper_le_1 : upper ≤ 1 := min_le_right t (1 : ℝ); linarith
      have h5 : |c| < 1 := by rw [abs_lt] <;> constructor <;> linarith
      exact ⟨c, h1, h2, h5⟩
    rcases h_exists with ⟨c, hc1, hc2, hc3⟩
    set y : E n := c • ν with hy_def
    have hy_inner : inner ℝ y ν = c := by simp [hy_def, inner_smul_left, hν_unit] <;> ring
    have hy_ball : y ∈ B := by
      have h_norm : dist y 0 = |c| := by simp [dist_zero_right, hy_def, norm_smul, hν_unit] <;> ring
      rw [mem_ball, h_norm]; exact hc3
    let U : Set (E n) := {z | s < inner ℝ z ν ∧ inner ℝ z ν < t} ∩ B
    have hU_open : IsOpen U := by
      apply IsOpen.inter
      · exact IsOpen.and (isOpen_lt continuous_const (by fun_prop)) (isOpen_lt (by fun_prop) continuous_const)
      · exact isOpen_ball
    have hyU : y ∈ U := by
      have h1 : s < inner ℝ y ν := by rw [hy_inner]; exact hc1
      have h2 : inner ℝ y ν < t := by rw [hy_inner]; exact hc2
      exact ⟨⟨h1, h2⟩, hy_ball⟩
    have hU_pos : 0 < volume U := hU_open.measure_pos volume ⟨y, hyU⟩
    have h_sub : U ⊆ (HtB t) \ (HtB s) := by
      intro z hz
      have hz1 : s < inner ℝ z ν := hz.1.1; have hz2 : inner ℝ z ν < t := hz.1.2
      have hz3 : z ∈ B := hz.2
      have hz4 : z ∉ HtB s := by intro h; have h5 : inner ℝ z ν < s := h.1; linarith
      exact ⟨⟨hz2, hz3⟩, hz4⟩
    have h_diff_pos : 0 < volume ((HtB t) \ (HtB s)) := lt_of_lt_of_le hU_pos (measure_mono h_sub)
    have h_subset : HtB s ⊆ HtB t := by
      intro z hz; have hz1 : inner ℝ z ν < s := hz.1; have hz2 : z ∈ B := hz.2
      have hz3 : inner ℝ z ν < t := by linarith
      exact ⟨hz3, hz2⟩
    have h_diff_sub_B : (HtB t) \ (HtB s) ⊆ B := by intro x hx; exact hx.1.2
    have h_ne_top : volume ((HtB t) \ (HtB s)) ≠ ⊤ :=
      ne_top_of_le_ne_top hB_lt_top.ne (measure_mono h_diff_sub_B)
    have h_fin_s : volume (HtB s) ≠ ⊤ :=
      ne_top_of_le_ne_top hB_lt_top.ne (measure_mono (show HtB s ⊆ B from fun x hx => hx.2))
    have h_meas_diff : MeasurableSet ((HtB t) \ (HtB s)) := (hHtB_meas t).diff (hHtB_meas s)
    have h_eq : volume (HtB t) = volume (HtB s) + volume ((HtB t) \ (HtB s)) := by
      have h_union : HtB s ∪ ((HtB t) \ (HtB s)) = HtB t := by
        ext x
        simp only [HtB, Set.mem_union, Set.mem_sdiff, Set.mem_inter_iff, Set.mem_setOf_eq]
        <;> constructor
        · rintro (h | h); exact ⟨lt_trans h.1 hst, h.2⟩; exact ⟨h.1.1, h.1.2⟩
        · intro h; by_cases h2 : inner ℝ x ν < s
          · exact Or.inl ⟨h2, h.2⟩
          · have h2' : x ∉ HtB s := by intro h3; exact h2 h3.1
            exact Or.inr ⟨h, h2'⟩
      have h_disj : Disjoint (HtB s) ((HtB t) \ (HtB s)) := by
        rw [Set.disjoint_left]; intro x hx1 hx2; exact hx2.2 hx1
      have h_vol : volume (HtB s ∪ ((HtB t) \ (HtB s))) =
          volume (HtB s) + volume ((HtB t) \ (HtB s)) := measure_union h_disj h_meas_diff
      rw [h_union] at h_vol; exact h_vol
    rw [h_eq]; exact ENNReal.lt_add_right h_fin_s h_diff_pos.ne'
  by_cases hpos : 0 < α
  · have h_range : (0 : ℝ) < 1 ∧ -1 < α := by constructor <;> linarith
    have h_contra : volume (HtB 0) < volume (HtB α) := h_strict_mono 0 α hpos h_range
    rw [h_f0, hvol] at h_contra; exact False.elim (lt_irrefl _ h_contra)
  · by_cases hneg : α < 0
    · have h_range : α < 1 ∧ -1 < (0 : ℝ) := by constructor <;> linarith
      have h_contra : volume (HtB α) < volume (HtB 0) := h_strict_mono α 0 hneg h_range
      rw [h_f0, hvol] at h_contra; exact False.elim (lt_irrefl _ h_contra)
    · have h_eq : α = 0 := by linarith
      exact h_eq

/-- **Half-space identification**.

If `F` has a monotone boolean factorization through `inner(·, ν)` and
half-ball density at the origin, then `F =ᵐ {y | inner y ν < 0}`. -/
theorem halfspace_identification {F : Set (E n)} (hF : MeasurableSet F)
    (ν : E n) (hν_unit : ‖ν‖ = 1)
    (h_mono_factor : ∃ (g : ℝ → ℝ),
      Measurable g ∧ (∀ t, g t = 0 ∨ g t = 1) ∧
      (∀ s t, s ≤ t → g t ≤ g s) ∧
      (∀ᵐ (x : E n) ∂volume, x ∈ F ↔ g (inner ℝ x ν) = 1))
    (h_density : volume (F ∩ ball (0 : E n) 1) = volume (ball (0 : E n) 1) / 2) :
    F =ᵐ[volume] {y | inner ℝ y ν < 0} := by
  rcases h_mono_factor with ⟨g, hg_meas, hg_values, hg_decr, h_factor⟩
  have h_main := Geometry.Perimeter.halfSpace_characterization hF (v := ν) hν_unit g hg_meas hg_values hg_decr h_factor
  rcases h_main with (h_case | h_empty | h_full)
  · rcases h_case with ⟨α, hα⟩
    have hα0 : α = 0 := halfspace_density_alpha_zero hν_unit α F hα h_density
    filter_upwards [hα] with z hz
    have hz' : z ∈ F ↔ inner ℝ z ν < 0 := by rw [hα0] at hz; exact hz
    exact propext hz'
  · have hF_null : volume F = 0 := by simpa [ae_iff] using h_empty
    have h_vol : volume (F ∩ ball (0 : E n) 1) = 0 := measure_inter_null_of_null_left (ball (0 : E n) 1) hF_null
    have hV_pos : 0 < volume (ball (0 : E n) 1) := isOpen_ball.measure_pos volume ⟨0, mem_ball_self zero_lt_one⟩
    have h_contra : volume (ball (0 : E n) 1) / 2 = 0 := by rw [← h_density, h_vol]
    have h_pos2 : 0 < volume (ball (0 : E n) 1) / 2 := ENNReal.div_pos hV_pos.ne' (by norm_num)
    rw [h_contra] at h_pos2; exact False.elim (lt_irrefl 0 h_pos2)
  · let B : Set (E n) := ball (0 : E n) 1
    have h_inter_ae : Set.inter F B =ᵐ[volume] B := by
      filter_upwards [h_full] with z hz
      have h1 : (z ∈ F ∧ z ∈ B) ↔ z ∈ B := by exact ⟨fun h => h.2, fun hB => ⟨hz, hB⟩⟩
      have h2 : z ∈ Set.inter F B ↔ (z ∈ F ∧ z ∈ B) := by rfl
      exact (h2.trans h1).eq
    have h_vol : volume (Set.inter F B) = volume B := measure_congr h_inter_ae
    have hV_pos : 0 < volume B := isOpen_ball.measure_pos volume ⟨0, mem_ball_self zero_lt_one⟩
    have hV_lt_top : volume B < ⊤ := measure_ball_lt_top
    have h_density' : volume (Set.inter F B) = volume B / 2 := by
      have h_eq1 : Set.inter F B = F ∩ ball (0 : E n) 1 := by rfl
      rw [h_eq1]; exact h_density
    have h_eq : volume B = volume B / 2 := by rw [h_vol] at h_density'; exact h_density'
    have hB_ne_top : volume B ≠ ⊤ := hV_lt_top.ne
    have hmul : (2 : ENNReal) * volume B = volume B := by
      have h1 : (2 : ENNReal) * volume B = (2 : ENNReal) * (volume B / 2) := congr_arg (fun x : ENNReal => (2 : ENNReal) * x) h_eq
      have h2 : (2 : ENNReal) * (volume B / 2) = volume B := ENNReal.mul_div_cancel (by norm_num) (by norm_num)
      rw [h1, h2]
    have h3 : volume B + volume B = volume B := by
      have h4 : (2 : ENNReal) * volume B = volume B + volume B := by rw [two_mul]
      rw [h4] at hmul; exact hmul
    have h5 : (volume B + volume B).toReal = (volume B).toReal := by rw [h3]
    have h6 : (volume B + volume B).toReal = (volume B).toReal + (volume B).toReal := by rw [ENNReal.toReal_add hB_ne_top hB_ne_top]
    have h7 : (volume B).toReal + (volume B).toReal = (volume B).toReal := by rw [← h6, h5]
    have h8 : (volume B).toReal = 0 := by linarith
    have h_zero : volume B = 0 := by rw [← ENNReal.ofReal_toReal hB_ne_top, h8] <;> simp
    exact False.elim (hV_pos.ne' h_zero)

/-- **Half-space characterization**.

If F has zero directional variation in directions ⟂ν, half-ball density,
and positive orientation, then F =ᵐ {y | inner y ν < 0}. -/
lemma halfspace_characterization (F : Set (E n)) (hF : MeasurableSet F)
    (ν : E n) (hν_unit : ‖ν‖ = 1)
    (h_zero : ∀ (w : E n), inner ℝ w ν = 0 → Perimeter.directionalVariation F w = 0)
    (h_density : volume (F ∩ ball (0 : E n) 1) = volume (ball (0 : E n) 1) / 2)
    (h_orientation : ∀ (φ : E n → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∀ x, 0 ≤ φ x) → 0 ≤ ∫ x in F, fderiv ℝ φ x ν) :
    F =ᵐ[volume] {y | inner ℝ y ν < 0} := by
  have h_transl : ∀ (w : E n), inner ℝ w ν = 0 →
      ∀ (t : ℝ), Geometry.Perimeter.translateSet F (t • w) =ᵐ[volume] F := by
    intro w hw t
    exact Geometry.Perimeter.zero_directionalVariation_translation_invariant hF (h_zero w hw) t
  have h_mono_factor : ∃ (g : ℝ → ℝ),
      Measurable g ∧ (∀ t, g t = 0 ∨ g t = 1) ∧
      (∀ s t, s ≤ t → g t ≤ g s) ∧
      (∀ᵐ (x : E n) ∂volume, x ∈ F ↔ g (inner ℝ x ν) = 1) :=
    Geometry.Perimeter.orientation_to_monotone_factorization hF hν_unit h_transl h_orientation
  exact halfspace_identification hF ν hν_unit h_mono_factor h_density

-- ============================================================================
-- Weak-to-strong orientation bridge
-- ============================================================================

/-- Helper: the directional derivative of a smooth compactly supported
function has compact support. -/
lemma hasCompactSupport_fderiv {φ : E n → ℝ} {v : E n}
    (hφ : ContDiff ℝ ∞ φ) (hsupp : HasCompactSupport φ) :
    HasCompactSupport (fun x : E n => fderiv ℝ φ x v) := by
  let ψ := fun x : E n => fderiv ℝ φ x v
  have h1 : Function.support ψ ⊆ closure (Function.support φ) := by
    intro x hx
    by_contra h2
    have h3 : φ =ᶠ[nhds x] 0 := by
      have h4 : IsOpen (closure (Function.support φ))ᶜ := isClosed_closure.isOpen_compl
      exact Filter.eventually_of_mem (IsOpen.mem_nhds h4 h2) (fun y hy => by
        have hφy : φ y = 0 := by simpa [Function.mem_support] using fun h => hy (subset_closure h)
        exact hφy)
    have h41 : HasFDerivAt (fun (_ : E n) => (0 : ℝ)) (0 : E n →L[ℝ] ℝ) x := hasFDerivAt_const (c := (0 : ℝ)) (x := x)
    have h42 : HasFDerivAt φ (0 : E n →L[ℝ] ℝ) x := h41.congr_of_eventuallyEq h3
    have h4 : fderiv ℝ φ x = 0 := h42.fderiv
    have h5 : ψ x = 0 := by simpa [ψ] using congr_arg (fun (f : E n →L[ℝ] ℝ) => f v) h4
    exact hx h5
  have h2 : closure (Function.support ψ) ⊆ closure (Function.support φ) := closure_minimal h1 isClosed_closure
  have h3 : IsCompact (closure (Function.support φ)) := hsupp
  exact h3.of_isClosed_subset isClosed_closure h2

/-- **Bridge: weak orientation implies strong orientation**.

If a measurable set `F` satisfies the orientation inequality for all
nonnegative smooth compactly supported test functions `φ` with `φ 0 > 0`,
then it satisfies the inequality for ALL nonnegative smooth compactly
supported test functions.

Proof: for `φ` with `φ 0 = 0`, approximate by `φ_ε = φ + ε·η` where `η`
is a fixed smooth bump with `η 0 = 1`. The inequality is linear in `φ`,
so taking `ε → 0+` recovers the result for `φ`. -/
lemma orientation_weak_to_strong {F : Set (E n)} {v : E n}
    (hF : MeasurableSet F)
    (h_weak : ∀ (φ : E n → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∀ x, 0 ≤ φ x) → 0 < φ 0 → 0 ≤ ∫ x in F, fderiv ℝ φ x v) :
    ∀ (φ : E n → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∀ x, 0 ≤ φ x) → 0 ≤ ∫ x in F, fderiv ℝ φ x v := by
  intro φ hφ hsupp hnonneg
  -- Bump function η with η 0 = 1, η ≥ 0, smooth, compact support
  have h_bump : ∃ (η : E n → ℝ), HasCompactSupport η ∧ ContDiff ℝ ∞ η ∧ (∀ x, 0 ≤ η x) ∧ η 0 = 1 := by
    rcases exists_contDiff_tsupport_subset (n := ⊤) (s := Set.univ) (x := (0 : E n)) (by simp)
      with ⟨η, _hη_tsupp, hη_supp, hη_smooth, hη_range, hη0⟩
    have hη_nonneg : ∀ x, 0 ≤ η x := by
      intro x
      have h : η x ∈ Set.range η := ⟨x, rfl⟩
      have h' : η x ∈ Set.Icc (0 : ℝ) 1 := hη_range h
      exact h'.1
    exact ⟨η, hη_supp, hη_smooth, hη_nonneg, hη0⟩
  rcases h_bump with ⟨η, hη_supp, hη_smooth, hη_nonneg, hη0⟩
  have hη0_pos : 0 < η 0 := by rw [hη0]; norm_num
  let dφ : E n → ℝ := fun x => fderiv ℝ φ x v
  let dη : E n → ℝ := fun x => fderiv ℝ η x v
  have h_dφ_supp : HasCompactSupport dφ := hasCompactSupport_fderiv hφ hsupp
  have h_dη_supp : HasCompactSupport dη := hasCompactSupport_fderiv hη_smooth hη_supp
  have h_dφ_cont : Continuous dφ := by have h1 : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by norm_num); fun_prop
  have h_dη_cont : Continuous dη := by have h1 : Continuous (fderiv ℝ η) := hη_smooth.continuous_fderiv (by norm_num); fun_prop
  have h_dφ_int : Integrable dφ volume := h_dφ_cont.integrable_of_hasCompactSupport h_dφ_supp
  have h_dη_int : Integrable dη volume := h_dη_cont.integrable_of_hasCompactSupport h_dη_supp
  have h_dφ_int_F : IntegrableOn dφ F volume := h_dφ_int.integrableOn
  have h_dη_int_F : IntegrableOn dη F volume := h_dη_int.integrableOn
  let I := ∫ x in F, dφ x
  let C := ∫ x in F, dη x
  have h_main : ∀ (ε : ℝ), 0 < ε → 0 ≤ I + ε * C := by
    intro ε hε
    let φ_ε : E n → ℝ := fun x => φ x + ε * η x
    have h_scaled_smooth : ContDiff ℝ ∞ (fun x : E n => ε * η x) :=
      contDiff_const.mul hη_smooth
    have hφ_ε_smooth : ContDiff ℝ ∞ φ_ε := hφ.add h_scaled_smooth
    have h_scaled_supp : HasCompactSupport (fun x : E n => ε * η x) := by
      have hε_ne : ε ≠ 0 := hε.ne'
      have h1 : Function.support (fun x : E n => ε * η x) = Function.support η := by
        ext x; simp [hε_ne]
      have h2 : tsupport (fun x : E n => ε * η x) = tsupport η := by
        rw [tsupport, tsupport, h1]
      have h_main : IsCompact (tsupport (fun x : E n => ε * η x)) := by
        rw [h2]
        exact hη_supp
      exact h_main
    have hφ_ε_supp : HasCompactSupport φ_ε := by
      have h1 : Function.support φ_ε ⊆ Function.support φ ∪ Function.support (fun x : E n => ε * η x) := by
        intro x hx
        simp only [φ_ε, Function.mem_support, mem_union] at hx ⊢
        by_cases h2 : φ x = 0
        · by_cases h3 : ε * η x = 0
          · have h4 : φ_ε x = 0 := by simp [φ_ε, h2, h3] <;> ring
            contradiction
          · exact Or.inr h3
        · exact Or.inl h2
      let U := Function.support φ ∪ Function.support (fun x : E n => ε * η x)
      have h1' : Function.support φ_ε ⊆ closure U := h1.trans subset_closure
      have h_clos : closure (Function.support φ_ε) ⊆ closure U := closure_minimal h1' isClosed_closure
      have h4 : IsCompact (closure U) := by
        have h5 : closure U = closure (Function.support φ) ∪ closure (Function.support (fun x : E n => ε * η x)) := closure_union
        rw [h5]
        have h6 : IsCompact (closure (Function.support φ)) := hsupp
        have h7 : IsCompact (closure (Function.support (fun x : E n => ε * η x))) := by
          have h8 : tsupport (fun x : E n => ε * η x) = closure (Function.support (fun x : E n => ε * η x)) := by rfl
          rw [←h8]
          exact h_scaled_supp
        exact h6.union h7
      have h9 : tsupport φ_ε = closure (Function.support φ_ε) := by rfl
      have h10 : IsCompact (tsupport φ_ε) := by
        rw [h9]
        exact h4.of_isClosed_subset isClosed_closure h_clos
      exact h10
    have hφ_ε_nonneg : ∀ x, 0 ≤ φ_ε x := by
      intro x
      have h1 : 0 ≤ φ x := hnonneg x
      have h2 : 0 ≤ ε := by linarith
      have h3 : 0 ≤ η x := hη_nonneg x
      have h4 : 0 ≤ ε * η x := mul_nonneg h2 h3
      linarith
    have hφ_ε_0_pos : 0 < φ_ε 0 := by
      have h1 : 0 ≤ φ 0 := hnonneg 0
      have h2 : 0 < ε * η 0 := mul_pos hε hη0_pos
      simpa [φ_ε] using add_pos_of_nonneg_of_pos h1 h2
    have h_fderiv_eq : ∀ x, fderiv ℝ φ_ε x v = dφ x + ε * dη x := by
      intro x
      have h_diff1 : DifferentiableAt ℝ φ x := (hφ.differentiable (by norm_num)).differentiableAt
      have h_diff2 : DifferentiableAt ℝ η x := (hη_smooth.differentiable (by norm_num)).differentiableAt
      have h5 : fderiv ℝ φ_ε x = fderiv ℝ φ x + ε • fderiv ℝ η x := by
        have h6 : fderiv ℝ φ_ε x = fderiv ℝ φ x + fderiv ℝ (fun x : E n => ε * η x) x :=
          fderiv_add h_diff1 (h_diff2.const_smul ε)
        rw [h6]
        have h7 : fderiv ℝ (fun x : E n => ε * η x) x = ε • fderiv ℝ η x :=
          fderiv_const_smul h_diff2 ε
        rw [h7]
      rw [h5]
      <;> simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, dφ, dη] <;> ring
    have h6 : 0 ≤ ∫ x in F, fderiv ℝ φ_ε x v :=
      h_weak φ_ε hφ_ε_smooth hφ_ε_supp hφ_ε_nonneg hφ_ε_0_pos
    have h7 : (fun x => fderiv ℝ φ_ε x v) = fun x => dφ x + ε * dη x := by
      funext x; exact h_fderiv_eq x
    rw [h7] at h6
    have h8 : ∫ x in F, (dφ x + ε * dη x) = I + ε * C := by
      rw [integral_add h_dφ_int_F (h_dη_int_F.const_mul ε), integral_const_mul] <;> rfl
    rw [h8] at h6
    exact h6
  by_contra h
  have hI_neg : I < 0 := by linarith
  by_cases hC : 0 < C
  · -- C > 0: choose ε = -I / (2 * C)
    set ε : ℝ := -I / (2 * C) with hε_def
    have hε_pos : 0 < ε := by
      rw [hε_def]
      apply div_pos
      · linarith
      · positivity
    have h9 := h_main ε hε_pos
    have h10 : I + ε * C = I / 2 := by
      rw [hε_def]
      have h11 : C ≠ 0 := hC.ne'
      field_simp [h11] <;> ring
    rw [h10] at h9
    linarith
  · -- C ≤ 0: I + C < 0 since I < 0 and C ≤ 0
    have hC_le : C ≤ 0 := by linarith
    have h9 := h_main 1 (by norm_num)
    have h10 : I + (1 : ℝ) * C < 0 := by linarith
    linarith

/-- **All reduced-boundary blow-up data needed for the blow-up lemma**.

At a reduced boundary point x with normal ν, provides:
1. Uniform volume and translation bounds for blow-ups
2. Any L¹_loc limit of blow-ups is a.e. the half-space Hν -/
theorem reduced_boundary_blowup_data {S : Set (E n)} (hS : MeasurableSet S)
    (x : E n) (ν : E n) (hν_unit : ‖ν‖ = 1)
    (h_reduced : ReducedBoundaryData S x ν) :
    (∀ (K : Set (E n)), IsCompact K →
      ∃ (C : ENNReal), ∀ (r : ℝ), 0 < r → r < 1 → volume (blowUp S x r ∩ K) ≤ C) ∧
    (∀ (K : Set (E n)), IsCompact K →
      ∃ (C : ℝ), ∀ (r : ℝ), 0 < r → r < 1 → ∀ (h : E n),
        volume (symmDiff (blowUp S x r) ((fun y => y + h) '' (blowUp S x r)) ∩ K) ≤
        ENNReal.ofReal (C * ‖h‖)) ∧
    ∀ (F : Set (E n)) (hF : MeasurableSet F) (r_seq : ℕ → ℝ),
      (∀ k, 0 < r_seq k) → Filter.Tendsto r_seq atTop (nhds 0) →
      (∀ K, IsCompact K →
        Filter.Tendsto (fun k => volume (symmDiff (blowUp S x (r_seq k)) F ∩ K))
          atTop (nhds 0)) →
      F =ᵐ[volume] {y | inner ℝ y ν < 0} := by
  have h_vol_bound := h_reduced.h_vol_bound
  have h_trans_bound := h_reduced.h_trans_bound
  have h_dir_vanish := h_reduced.h_directional_vanishing
  refine ⟨h_vol_bound, h_trans_bound, ?_⟩
  intro F hF r_seq hr_pos hr_tendsto h_conv

  have hE_meas : ∀ k, MeasurableSet (blowUp S x (r_seq k)) := by
    intro k
    have hr_ne : r_seq k ≠ 0 := (hr_pos k).ne'
    let Φ : E n ≃ₜ E n :=
      { toFun := fun y => (r_seq k)⁻¹ • (y - x)
        invFun := fun z => x + (r_seq k) • z
        left_inv := fun y => by simp [smul_smul, hr_ne] <;> abel
        right_inv := fun z => by simp [smul_smul, hr_ne] <;> abel
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
    have h_eq : Φ '' S = blowUp S x (r_seq k) := by ext z; simp [blowUp, blowUpMap, Φ]
    have h_meas : MeasurableSet (Φ '' S) := by
      have h_iff : MeasurableSet (Φ '' S) ↔ MeasurableSet S := Φ.measurableEmbedding.measurableSet_image
      exact h_iff.mpr hS
    rw [← h_eq]; exact h_meas

  have h_zero_dv : ∀ (w : E n), inner ℝ w ν = 0 → Perimeter.directionalVariation F w = 0 := by
    intro w hw
    have h_local_zero : ∀ (K : Set (E n)), IsCompact K → Perimeter.directionalVariationIn F w K = 0 := by
      intro K hK
      let a : ℕ → ENNReal := fun k => Perimeter.directionalVariationIn (blowUp S x (r_seq k)) w K
      have h_lsc : Perimeter.directionalVariationIn F w K ≤ Filter.liminf a Filter.atTop :=
        Perimeter.directionalVariationIn_lowerSemicontinuity hF hE_meas (fun K' hK' => h_conv K' hK') w K
      have h_eventually : ∀ᶠ k in Filter.atTop, r_seq k ∈ Set.Ioi 0 := by filter_upwards with k; exact hr_pos k
      have h2 : Filter.Tendsto r_seq Filter.atTop (Filter.principal (Set.Ioi 0)) := by simpa [Filter.tendsto_principal] using h_eventually
      have h : Filter.Tendsto r_seq Filter.atTop (nhds 0 ⊓ Filter.principal (Set.Ioi 0)) := Filter.tendsto_inf.mpr ⟨hr_tendsto, h2⟩
      have h_tendsto_within : Filter.Tendsto r_seq Filter.atTop (nhdsWithin 0 (Set.Ioi 0)) := by simpa [nhdsWithin] using h
      have h_tendsto : Filter.Tendsto a Filter.atTop (nhds 0) := (h_dir_vanish K hK w hw).comp h_tendsto_within
      have h_liminf_zero : Filter.liminf a Filter.atTop = 0 := h_tendsto.liminf_eq
      rw [h_liminf_zero] at h_lsc
      exact bot_unique h_lsc
    exact Perimeter.directionalVariationIn_all_compact_zero hF w h_local_zero

  have h_density_F : volume (F ∩ ball (0 : E n) 1) = volume (ball (0 : E n) 1) / 2 := by
    let B := ball (0 : E n) 1
    have hB_meas : MeasurableSet B := isOpen_ball.measurableSet
    have hB_lt_top : volume B ≠ ⊤ := by
      have h : volume B ≤ volume (closedBall (0 : E n) 1) := measure_mono ball_subset_closedBall
      have h2 : volume (closedBall (0 : E n) 1) ≠ ⊤ := (isCompact_closedBall _ _).measure_lt_top.ne
      exact ne_top_of_le_ne_top h2 h
    let A := fun k => blowUp S x (r_seq k)
    have h_symm_B : Tendsto (fun k => volume (symmDiff (A k) F ∩ B)) atTop (nhds 0) := by
      have h_closed := h_conv (closedBall (0 : E n) 1) (isCompact_closedBall _ _)
      have h_sub : ∀ k, volume (symmDiff (A k) F ∩ B) ≤ volume (symmDiff (A k) F ∩ closedBall (0 : E n) 1) := by
        intro k; exact measure_mono (inter_subset_inter_right _ ball_subset_closedBall)
      have h_zero : ∀ k, (0 : ENNReal) ≤ volume (symmDiff (A k) F ∩ B) := fun k => by positivity
      have h_const : Tendsto (fun _ : ℕ => (0 : ENNReal)) atTop (nhds 0) := tendsto_const_nhds
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' h_const h_closed (Filter.univ_mem' h_zero) (Filter.univ_mem' h_sub)
    have h_conv_vol : Tendsto (fun k => volume (A k ∩ B)) atTop (nhds (volume (F ∩ B))) := by
      let c := volume (F ∩ B)
      have hc_lt_top : c ≠ ⊤ := ne_top_of_le_ne_top hB_lt_top (measure_mono (fun x hx => hx.2))
      have h1 : ∀ k, volume (A k ∩ B) ≤ c + volume (symmDiff (A k) F ∩ B) := by
        intro k
        have h_sub : A k ∩ B ⊆ (F ∩ B) ∪ (symmDiff (A k) F ∩ B) := by
          intro x hx; by_cases h : x ∈ F
          · exact Or.inl ⟨h, hx.2⟩
          · exact Or.inr ⟨Or.inl ⟨hx.1, h⟩, hx.2⟩
        calc volume (A k ∩ B) ≤ volume ((F ∩ B) ∪ (symmDiff (A k) F ∩ B)) := measure_mono h_sub
          _ ≤ c + volume (symmDiff (A k) F ∩ B) := measure_union_le _ _
      have h2 : ∀ k, c ≤ volume (A k ∩ B) + volume (symmDiff (A k) F ∩ B) := by
        intro k
        have h_sub : F ∩ B ⊆ (A k ∩ B) ∪ (symmDiff (A k) F ∩ B) := by
          intro x hx; by_cases h : x ∈ A k
          · exact Or.inl ⟨h, hx.2⟩
          · exact Or.inr ⟨Or.inr ⟨hx.1, h⟩, hx.2⟩
        calc c = volume (F ∩ B) := rfl
          _ ≤ volume ((A k ∩ B) ∪ (symmDiff (A k) F ∩ B)) := measure_mono h_sub
          _ ≤ volume (A k ∩ B) + volume (symmDiff (A k) F ∩ B) := measure_union_le _ _
      let a k := (volume (A k ∩ B)).toReal
      let b := c.toReal
      let e k := (volume (symmDiff (A k) F ∩ B)).toReal
      have h_fin1 : ∀ k, volume (A k ∩ B) ≠ ⊤ := fun k => ne_top_of_le_ne_top hB_lt_top (measure_mono (fun x hx => hx.2))
      have h_fin2 : ∀ k, volume (symmDiff (A k) F ∩ B) ≠ ⊤ := fun k => ne_top_of_le_ne_top hB_lt_top (measure_mono (fun x hx => hx.2))
      have h_fin_sum : ∀ k, volume (A k ∩ B) + volume (symmDiff (A k) F ∩ B) ≠ ⊤ := fun k => ENNReal.add_ne_top.mpr ⟨h_fin1 k, h_fin2 k⟩
      have h_cont_toReal : ContinuousAt ENNReal.toReal (0 : ENNReal) := ENNReal.continuousAt_toReal (by simp)
      have he_tendsto : Tendsto e atTop (nhds 0) := h_cont_toReal.tendsto.comp h_symm_B
      have h1' : ∀ k, a k ≤ b + e k := by
        intro k
        have h_add : (c + volume (symmDiff (A k) F ∩ B)).toReal = b + e k := by rw [ENNReal.toReal_add hc_lt_top (h_fin2 k)] <;> rfl
        have h := (ENNReal.toReal_le_toReal (h_fin1 k) (ENNReal.add_ne_top.mpr ⟨hc_lt_top, h_fin2 k⟩)).mpr (h1 k)
        rw [h_add] at h; exact h
      have h2' : ∀ k, b ≤ a k + e k := by
        intro k
        have h_add : (volume (A k ∩ B) + volume (symmDiff (A k) F ∩ B)).toReal = a k + e k := by rw [ENNReal.toReal_add (h_fin1 k) (h_fin2 k)] <;> rfl
        have h := (ENNReal.toReal_le_toReal hc_lt_top (h_fin_sum k)).mpr (h2 k)
        rw [h_add] at h; exact h
      have h3' : ∀ k, |a k - b| ≤ e k := by
        intro k
        have h4 : a k - b ≤ e k := by
          have h41 : a k ≤ b + e k := h1' k
          linarith
        have h5 : -e k ≤ a k - b := by
          have h51 : b ≤ a k + e k := h2' k
          linarith
        exact abs_le.mpr ⟨h5, h4⟩
      have h_diff_tendsto : Tendsto (fun k => a k - b) atTop (nhds 0) := squeeze_zero_norm h3' he_tendsto
      have h_b_tendsto_real : Tendsto a atTop (nhds b) := by
        have h : Tendsto (fun k : ℕ => (a k - b) + b) atTop (nhds (0 + b)) := h_diff_tendsto.add tendsto_const_nhds
        have h2 : (fun k : ℕ => (a k - b) + b) = a := by funext k; ring
        have h3 : (0 + b : ℝ) = b := by ring
        rw [h2, h3] at h; exact h
      have h_b_tendsto : Tendsto (fun k => volume (A k ∩ B)) atTop (nhds c) := by
        have h4 : ∀ k, ENNReal.ofReal (a k) = volume (A k ∩ B) := by
          intro k; rw [ENNReal.ofReal_toReal]; exact ne_top_of_le_ne_top hB_lt_top (measure_mono (show A k ∩ B ⊆ B from fun x hx => hx.2))
        have h5 : ENNReal.ofReal b = c := by rw [ENNReal.ofReal_toReal]; exact hc_lt_top
        have h_cont : Continuous ENNReal.ofReal := ENNReal.continuous_ofReal
        have h6 : Tendsto (fun k => ENNReal.ofReal (a k)) atTop (nhds (ENNReal.ofReal b)) := (h_cont.tendsto b).comp h_b_tendsto_real
        rw [funext h4, h5] at h6; exact h6
      exact h_b_tendsto
    have h_density_seq : Tendsto (fun k => volume (A k ∩ B)) atTop (nhds (volume B / 2)) :=
      h_reduced.density.comp (by
        have h1 : ∀ᶠ k in atTop, r_seq k ∈ Set.Ioi (0 : ℝ) := by filter_upwards with k; exact hr_pos k
        exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within r_seq hr_tendsto h1)
    exact tendsto_nhds_unique h_conv_vol h_density_seq

  have h_orientation_F_weak : ∀ (φ : E n → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∀ x, 0 ≤ φ x) → 0 < φ 0 → 0 ≤ ∫ x in F, fderiv ℝ φ x ν := by
    intro φ hφ hsupp φ_nonneg hφ0
    let ψ : E n → ℝ := fun x => fderiv ℝ φ x ν
    have hψ_cont : Continuous ψ := by have h1 : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by norm_num); fun_prop
    have hψ_supp : HasCompactSupport ψ := by
      have h1 : Function.support ψ ⊆ closure (Function.support φ) := by
        intro x hx; by_contra h2
        have h3 : φ =ᶠ[nhds x] 0 := by
          have h4 : IsOpen (closure (Function.support φ))ᶜ := isClosed_closure.isOpen_compl
          exact Filter.eventually_of_mem (IsOpen.mem_nhds h4 h2) (fun y hy => by
            have hφy : φ y = 0 := by simpa [Function.mem_support] using fun h => hy (subset_closure h)
            exact hφy)
        have h41 : HasFDerivAt (fun (_ : E n) => (0 : ℝ)) (0 : E n →L[ℝ] ℝ) x := hasFDerivAt_const (c := (0 : ℝ)) (x := x)
        have h42 : HasFDerivAt φ (0 : E n →L[ℝ] ℝ) x := h41.congr_of_eventuallyEq h3
        have h4 : fderiv ℝ φ x = 0 := h42.fderiv
        have h5 : ψ x = 0 := by simpa [ψ] using congr_arg (fun (f : E n →L[ℝ] ℝ) => f ν) h4
        exact hx h5
      have h2 : closure (Function.support ψ) ⊆ closure (Function.support φ) := closure_minimal h1 isClosed_closure
      have h3 : IsCompact (closure (Function.support φ)) := hsupp
      exact h3.of_isClosed_subset isClosed_closure h2
    let K : Set (E n) := closure (Function.support ψ)
    have hK : IsCompact K := hψ_supp
    have hK_meas : MeasurableSet K := hK.measurableSet
    have h_bdd : ∃ (C : ℝ), 0 ≤ C ∧ ∀ x, |ψ x| ≤ C := by
      have h4 : BddAbove (Set.image (fun x => |ψ x|) K) := hK.bddAbove_image (continuous_abs.comp hψ_cont).continuousOn
      rcases h4 with ⟨C0, hC0⟩
      let C := max C0 0
      have hC_nonneg : 0 ≤ C := by positivity
      have hC_on_K : ∀ x ∈ K, |ψ x| ≤ C := by
        intro x hx
        have h5 : |ψ x| ∈ Set.image (fun x => |ψ x|) K := ⟨x, hx, rfl⟩
        have h6 : |ψ x| ≤ C0 := hC0 h5
        exact le_trans h6 (le_max_left _ _)
      refine ⟨C, hC_nonneg, fun x => ?_⟩
      by_cases hx : x ∈ K
      · exact hC_on_K x hx
      · have h7 : ψ x = 0 := by have h8 : x ∉ Function.support ψ := fun h9 => hx (subset_closure h9); simpa [Function.mem_support] using h8
        rw [h7] <;> simp [hC_nonneg]
    rcases h_bdd with ⟨C, C_nonneg, hC⟩
    have hψ_int : Integrable ψ volume := hψ_cont.integrable_of_hasCompactSupport hψ_supp
    have h_diff_bound : ∀ k, |(∫ x in blowUp S x (r_seq k), ψ x) - (∫ x in F, ψ x)| ≤
        C * (volume (symmDiff (blowUp S x (r_seq k)) F ∩ Function.support ψ)).toReal := by
      intro k
      set A : Set (E n) := blowUp S x (r_seq k) with hA_def
      set D : Set (E n) := symmDiff A F ∩ Function.support ψ with hD_def
      have hA_meas : MeasurableSet A := hE_meas k
      have hD_meas : MeasurableSet D := by
        rw [hD_def]
        have h_support_meas : MeasurableSet (Function.support ψ) := by
          have h1 : IsOpen (ψ ⁻¹' ({0}ᶜ : Set ℝ)) := hψ_cont.isOpen_preimage ({0}ᶜ : Set ℝ) isOpen_compl_singleton
          have h_eq : ψ ⁻¹' ({0}ᶜ : Set ℝ) = Function.support ψ := by ext x; simp [Function.mem_support]
          rw [h_eq] at h1; exact h1.measurableSet
        exact (hA_meas.symmDiff hF).inter h_support_meas
      have h_fin : volume D ≠ ⊤ := by
        rw [hD_def]; have h_sub : D ⊆ K := by intro x hx; exact subset_closure hx.2
        exact ne_top_of_le_ne_top hK.measure_lt_top.ne (measure_mono h_sub)
      let f_k : E n → ℝ := fun x => (Set.indicator A (1 : E n → ℝ) x - Set.indicator F (1 : E n → ℝ) x) * ψ x
      let g_k : E n → ℝ := fun x => C * Set.indicator D (1 : E n → ℝ) x
      have h_f_eq : f_k = fun x => Set.indicator A ψ x - Set.indicator F ψ x := by
        funext x
        have h1 : (Set.indicator A (1 : E n → ℝ) x) * ψ x = Set.indicator A ψ x := by by_cases h : x ∈ A <;> simp [Set.indicator_apply, h] <;> ring
        have h2 : (Set.indicator F (1 : E n → ℝ) x) * ψ x = Set.indicator F ψ x := by by_cases h : x ∈ F <;> simp [Set.indicator_apply, h] <;> ring
        simp only [f_k]
        have h3 : (Set.indicator A (1 : E n → ℝ) x - Set.indicator F (1 : E n → ℝ) x) * ψ x = Set.indicator A (1 : E n → ℝ) x * ψ x - Set.indicator F (1 : E n → ℝ) x * ψ x := by ring
        rw [h3, h1, h2]
      have hf_int : Integrable f_k volume := by rw [h_f_eq]; exact (hψ_int.indicator hA_meas).sub (hψ_int.indicator hF)
      have hg_int : Integrable g_k volume := by
        have h_int_on : IntegrableOn (1 : E n → ℝ) D volume := MeasureTheory.integrableOn_const (hs := h_fin)
        have h_int_D : Integrable (Set.indicator D (1 : E n → ℝ)) volume := (MeasureTheory.integrable_indicator_iff hD_meas).mpr h_int_on
        exact h_int_D.const_mul C
      have h3 : ∀ x, |f_k x| ≤ g_k x := by
        intro x
        by_cases h4 : x ∈ D
        · have h5 : |ψ x| ≤ C := hC x
          have h61 : x ∈ symmDiff A F := (hD_def ▸ h4).1
          have h6 : |Set.indicator A (1 : E n → ℝ) x - Set.indicator F (1 : E n → ℝ) x| = 1 := by
            rcases h61 with (h61 | h61)
            · simp [Set.indicator_apply, h61.1, h61.2] <;> norm_num
            · simp [Set.indicator_apply, h61.1, h61.2] <;> norm_num
          have h7 : |f_k x| = |ψ x| := by
            have h71 : f_k x = (Set.indicator A (1 : E n → ℝ) x - Set.indicator F (1 : E n → ℝ) x) * ψ x := by rfl
            rw [h71, abs_mul, h6] <;> ring
          have h8 : g_k x = C := by simp [g_k, Set.indicator_apply, h4] <;> ring
          rw [h7, h8]; exact h5
        · by_cases h8 : x ∈ Function.support ψ
          · have h9 : x ∉ symmDiff A F := by intro h9; exact h4 ⟨h9, h8⟩
            have h10 : Set.indicator A (1 : E n → ℝ) x = Set.indicator F (1 : E n → ℝ) x := by
              have h9' : (x ∈ A → x ∈ F) ∧ (x ∈ F → x ∈ A) := by simpa [symmDiff, Set.mem_union, Set.mem_diff] using h9
              have h_iff : x ∈ A ↔ x ∈ F := ⟨h9'.1, h9'.2⟩
              by_cases h : x ∈ A
              · have h' : x ∈ F := h_iff.mp h; simp [Set.indicator_apply, h, h']
              · have h' : x ∉ F := by intro h''; exact h (h_iff.mpr h'')
                simp [Set.indicator_apply, h, h']
            have h11 : f_k x = 0 := by simp [f_k, h10] <;> ring
            have h12 : g_k x = 0 := by simp [g_k, Set.indicator_apply, h4]
            rw [h11, h12] <;> norm_num
          · have h11 : ψ x = 0 := by simpa [Function.mem_support] using h8
            have h12 : f_k x = 0 := by simp [f_k, h11] <;> ring
            have h13 : g_k x = 0 := by simp [g_k, Set.indicator_apply, h4]
            rw [h12, h13] <;> norm_num
      have h1 : (∫ x in A, ψ x) - (∫ x in F, ψ x) = ∫ x, f_k x := by
        have h_int1 : Integrable (Set.indicator A ψ) volume := hψ_int.indicator hA_meas
        have h_int2 : Integrable (Set.indicator F ψ) volume := hψ_int.indicator hF
        have h_eq : (∫ x in A, ψ x) - (∫ x in F, ψ x) = ∫ x, (Set.indicator A ψ x - Set.indicator F ψ x) := by
          calc (∫ x in A, ψ x) - (∫ x in F, ψ x)
              = (∫ x, Set.indicator A ψ x) - (∫ x, Set.indicator F ψ x) := by rw [← integral_indicator hA_meas, ← integral_indicator hF]
            _ = ∫ x, (Set.indicator A ψ x - Set.indicator F ψ x) := by rw [← integral_sub h_int1 h_int2]
        rw [h_eq]; rw [← h_f_eq]
      rw [h1]
      calc |∫ x, f_k x| ≤ ∫ x, |f_k x| := abs_integral_le_integral_abs
        _ ≤ ∫ x, g_k x := by
          have h4 : (fun x => |f_k x|) ≤ g_k := by intro x; exact h3 x
          exact MeasureTheory.integral_mono_ae hf_int.abs hg_int (Filter.Eventually.of_forall h4)
        _ = C * (volume D).toReal := by
          have h2 : ∫ x, g_k x = C * ∫ x, D.indicator (1 : E n → ℝ) x := by rw [integral_const_mul]
          rw [h2]
          have h3 : ∫ x, D.indicator (1 : E n → ℝ) x = (volume D).toReal := by
            have h4 : ∫ x, D.indicator (1 : E n → ℝ) x = ∫ x in D, (1 : E n → ℝ) x := by rw [← integral_indicator hD_meas]
            rw [h4]; have h5 : ∫ x in D, (1 : E n → ℝ) x = volume.real D := by simp
            rw [h5] <;> rfl
          rw [h3] <;> ring
    have h_tendsto_real : Tendsto (fun k => C * (volume (symmDiff (blowUp S x (r_seq k)) F ∩ Function.support ψ)).toReal) atTop (nhds 0) := by
      have h_cont : ContinuousAt ENNReal.toReal (0 : ENNReal) := ENNReal.continuousAt_toReal (by simp)
      have h_le : ∀ k, volume (symmDiff (blowUp S x (r_seq k)) F ∩ Function.support ψ) ≤ volume (symmDiff (blowUp S x (r_seq k)) F ∩ K) := by
        intro k; exact measure_mono (inter_subset_inter_right _ (subset_closure))
      have h1 : Tendsto (fun k => (volume (symmDiff (blowUp S x (r_seq k)) F ∩ K)).toReal) atTop (nhds 0) := h_cont.tendsto.comp (h_conv K hK)
      have h2 : ∀ k, 0 ≤ (volume (symmDiff (blowUp S x (r_seq k)) F ∩ Function.support ψ)).toReal := by intro k; positivity
      have h3 : ∀ k, (volume (symmDiff (blowUp S x (r_seq k)) F ∩ Function.support ψ)).toReal ≤ (volume (symmDiff (blowUp S x (r_seq k)) F ∩ K)).toReal := by
        intro k
        have hb : volume (symmDiff (blowUp S x (r_seq k)) F ∩ K) ≠ ⊤ := ne_top_of_le_ne_top hK.measure_lt_top.ne (measure_mono (fun _ h => h.2))
        have ha : volume (symmDiff (blowUp S x (r_seq k)) F ∩ Function.support ψ) ≠ ⊤ := ne_top_of_le_ne_top hb (h_le k)
        exact (ENNReal.toReal_le_toReal ha hb).mpr (h_le k)
      have h3' : ∀ k, ‖(volume (symmDiff (blowUp S x (r_seq k)) F ∩ Function.support ψ)).toReal‖ ≤ (volume (symmDiff (blowUp S x (r_seq k)) F ∩ K)).toReal := by
        intro k
        have h_nonneg : 0 ≤ (volume (symmDiff (blowUp S x (r_seq k)) F ∩ Function.support ψ)).toReal := by positivity
        rw [Real.norm_eq_abs, abs_of_nonneg h_nonneg]; exact h3 k
      have h4 : Tendsto (fun k => (volume (symmDiff (blowUp S x (r_seq k)) F ∩ Function.support ψ)).toReal) atTop (nhds 0) := squeeze_zero_norm h3' h1
      have h5 : Tendsto (fun k => C * (volume (symmDiff (blowUp S x (r_seq k)) F ∩ Function.support ψ)).toReal) atTop (nhds (C * (0 : ℝ))) := tendsto_const_nhds.mul h4
      have h6 : C * (0 : ℝ) = 0 := by ring
      rw [h6] at h5; exact h5
    have h_tendsto_integral : Filter.Tendsto (fun k => ∫ x in blowUp S x (r_seq k), ψ x) atTop (nhds (∫ x in F, ψ x)) := by
      have h_diff_bound' : ∀ k, ‖(∫ x in blowUp S x (r_seq k), ψ x) - (∫ x in F, ψ x)‖ ≤ C * (volume (symmDiff (blowUp S x (r_seq k)) F ∩ Function.support ψ)).toReal := by
        intro k; simpa [Real.norm_eq_abs] using h_diff_bound k
      have h_tendsto_diff : Tendsto (fun k => (∫ x in blowUp S x (r_seq k), ψ x) - (∫ x in F, ψ x)) atTop (nhds 0) := squeeze_zero_norm h_diff_bound' h_tendsto_real
      have h_add : Tendsto (fun k => (∫ x in blowUp S x (r_seq k), ψ x) - (∫ x in F, ψ x) + (∫ x in F, ψ x)) atTop (nhds ((0 : ℝ) + (∫ x in F, ψ x))) := h_tendsto_diff.add tendsto_const_nhds
      have h_eq1 : (fun k : ℕ => (∫ x in blowUp S x (r_seq k), ψ x) - (∫ x in F, ψ x) + (∫ x in F, ψ x)) = (fun k : ℕ => ∫ x in blowUp S x (r_seq k), ψ x) := by funext k; ring
      rw [h_eq1] at h_add
      have h_zero : (0 : ℝ) + (∫ x in F, ψ x) = (∫ x in F, ψ x) := by ring
      rw [h_zero] at h_add; exact h_add
    rcases h_reduced.h_orientation φ hφ hsupp φ_nonneg hφ0 with ⟨r₀, hr₀_pos, h_orient⟩
    have h_eventually_r₀ : ∀ᶠ k in atTop, r_seq k < r₀ := hr_tendsto (Iio_mem_nhds hr₀_pos)
    have h_nonneg_seq : ∀ᶠ k in atTop, 0 ≤ ∫ x in blowUp S x (r_seq k), ψ x := by
      filter_upwards [h_eventually_r₀] with k hk
      exact h_orient (r_seq k) (hr_pos k) hk
    exact ge_of_tendsto h_tendsto_integral h_nonneg_seq

  have h_orientation_F : ∀ (φ : E n → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∀ x, 0 ≤ φ x) → 0 ≤ ∫ x in F, fderiv ℝ φ x ν :=
    orientation_weak_to_strong hF h_orientation_F_weak

  exact halfspace_characterization F hF ν hν_unit h_zero_dv h_density_F h_orientation_F

-- ============================================================================
-- Transport of ReducedBoundaryData under linear isometries
-- ============================================================================

/-- Blow-up transforms under a linear isometry. -/
lemma blowUp_transport {S : Set (E n)} {x : E n} {r : ℝ} (hr : r ≠ 0)
    (φ : E n ≃ₗᵢ[ℝ] E n) :
    blowUp (φ '' S) (φ x) r = φ '' (blowUp S x r) := by
  ext y
  simp only [blowUp, blowUpMap, Set.mem_image]
  constructor
  · rintro ⟨z, ⟨s, hs, rfl⟩, rfl⟩
    refine ⟨(1 / r) • (s - x), ?_, ?_⟩
    · exact ⟨s, hs, rfl⟩
    · simp [φ.map_sub, φ.map_smul] <;> abel
  · rintro ⟨w, ⟨s, hs, rfl⟩, rfl⟩
    refine ⟨φ s, ⟨s, hs, rfl⟩, ?_⟩
    simp [φ.map_sub, φ.map_smul] <;> abel

/-- **Transport of ReducedBoundaryData under linear isometry**.

If `ReducedBoundaryData S x ν` holds and `φ` is a linear isometry, then
`ReducedBoundaryData (φ '' S) (φ x) (φ ν)` holds. -/
theorem ReducedBoundaryData.transport {S : Set (E n)} {x : E n} {ν : E n}
    (hS_meas : MeasurableSet S)
    (hdata : ReducedBoundaryData S x ν)
    (φ : E n ≃ₗᵢ[ℝ] E n) :
    ReducedBoundaryData (φ '' S) (φ x) (φ ν) := by
  have hme : MeasurableEmbedding φ :=
    φ.toContinuousLinearEquiv.toHomeomorph.measurableEmbedding
  have h_vol_pres : MeasurePreserving φ volume := φ.measurePreserving
  have h_vol_image : ∀ (A : Set (E n)), MeasurableSet A → volume (φ '' A) = volume A := by
    intro A hA
    have h1 : φ '' A = φ.symm ⁻¹' A := by
      ext z
      simp only [Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨x, hx, rfl⟩
        simpa using hx
      · intro hz
        refine ⟨φ.symm z, hz, ?_⟩
        exact φ.apply_symm_apply z
    rw [h1]
    have h2 : MeasurePreserving φ.symm volume volume := φ.symm.measurePreserving
    exact h2.measure_preimage hA.nullMeasurableSet
  have h_blowUp_meas : ∀ (r : ℝ), 0 < r → MeasurableSet (blowUp S x r) := by
    intro r hr
    have h_ne : r ≠ 0 := hr.ne'
    have h_mul1 : r * (1 / r) = 1 := by field_simp [h_ne]
    have h_mul2 : (1 / r) * r = 1 := by field_simp [h_ne]
    let Φ : E n ≃ₜ E n :=
      { toFun := fun y => (1 / r) • (y - x)
        invFun := fun z => r • z + x
        left_inv := by
          intro y
          calc r • ((1 / r) • (y - x)) + x
            = (r * (1 / r)) • (y - x) + x := by rw [smul_smul]
          _ = (1 : ℝ) • (y - x) + x := by rw [h_mul1]
          _ = (y - x) + x := by rw [one_smul]
          _ = y := by simp [sub_add_cancel]
        right_inv := by
          intro z
          have h_sub : (r • z + x) - x = r • z := by abel
          calc (1 / r) • ((r • z + x) - x)
            = (1 / r) • (r • z) := by rw [h_sub]
          _ = ((1 / r) * r) • z := by rw [smul_smul]
          _ = (1 : ℝ) • z := by rw [h_mul2]
          _ = z := by rw [one_smul]
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
    have h_eq : Φ '' S = blowUp S x r := by
      unfold blowUp; rfl
    have h_iff : MeasurableSet (Φ '' S) ↔ MeasurableSet S :=
      Φ.measurableEmbedding.measurableSet_image
    have h_meas : MeasurableSet (Φ '' S) := h_iff.mpr hS_meas
    rw [← h_eq]
    exact h_meas
  refine ⟨?_, ?_, ?_, ?_, ?_⟩

  -- Volume bound
  · intro K hK
    rcases hdata.h_vol_bound (φ.symm '' K) (hK.image φ.symm.continuous) with ⟨C, hC⟩
    refine ⟨C, fun r hr_pos hr_lt => ?_⟩
    have h_img_eq : (φ '' blowUp S x r) ∩ K = φ '' (blowUp S x r ∩ φ.symm '' K) := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_image]
      constructor
      · rintro ⟨⟨z, hz, rfl⟩, hyK⟩
        have hzK : z ∈ φ.symm '' K := ⟨φ z, hyK, by simp⟩
        exact ⟨z, ⟨hz, hzK⟩, rfl⟩
      · rintro ⟨z, ⟨hz, hzK⟩, rfl⟩
        rcases hzK with ⟨w, hwK, h_eq⟩
        have hφz : φ z = w := by
          have h : φ (φ.symm w) = w := φ.apply_symm_apply w
          rw [h_eq] at *; exact h
        exact ⟨⟨z, hz, rfl⟩, by rw [hφz]; exact hwK⟩
    have h1 : blowUp (φ '' S) (φ x) r ∩ K = φ '' (blowUp S x r ∩ (φ.symm '' K)) := by
      rw [blowUp_transport hr_pos.ne' φ]
      exact h_img_eq
    have h_meas : MeasurableSet (blowUp S x r ∩ φ.symm '' K) :=
      (h_blowUp_meas r hr_pos).inter ((hK.image φ.symm.continuous).measurableSet)
    rw [h1, h_vol_image (blowUp S x r ∩ φ.symm '' K) h_meas]
    <;> exact hC r hr_pos hr_lt

  -- Translation bound
  · intro K hK
    rcases hdata.h_trans_bound (φ.symm '' K) (hK.image φ.symm.continuous) with ⟨C, hC⟩
    refine ⟨C, fun r hr_pos hr_lt h => ?_⟩
    let h' := φ.symm h
    have h_h'_eq : φ h' = h := by simp [h']
    have h_norm : ‖h'‖ = ‖h‖ := by simp [h']
    let A := blowUp S x r
    let B := (fun y : E n => y + h') '' A
    have h_trans_img : φ '' B = (fun z : E n => z + h) '' (φ '' A) := by
      ext z
      simp only [Set.mem_image, B]
      constructor
      · rintro ⟨y, ⟨a, ha, rfl⟩, rfl⟩
        refine ⟨φ a, ⟨a, ha, rfl⟩, ?_⟩
        rw [φ.map_add, h_h'_eq]
      · rintro ⟨w, hw, rfl⟩
        have h1 : φ.symm w ∈ A := by
          rcases hw with ⟨a, ha, h_eq⟩
          have h2 : φ.symm w = a := by
            rw [←h_eq]; simp
          rw [h2]; exact ha
        refine ⟨φ.symm w + h', ⟨φ.symm w, h1, rfl⟩, ?_⟩
        rw [φ.map_add, φ.apply_symm_apply w, h_h'_eq]
    have h_symm_img : symmDiff (φ '' A) (φ '' B) = φ '' symmDiff A B := by
      ext z
      simp only [symmDiff, Set.mem_union, Set.mem_diff, Set.mem_image]
      <;> aesop
    have h1 : symmDiff (blowUp (φ '' S) (φ x) r) ((fun y => y + h) '' (blowUp (φ '' S) (φ x) r)) ∩ K =
        φ '' (symmDiff A B ∩ φ.symm '' K) := by
      have h_blow : blowUp (φ '' S) (φ x) r = φ '' A := blowUp_transport hr_pos.ne' φ
      rw [h_blow]
      rw [←h_trans_img]
      rw [h_symm_img]
      ext y
      simp only [Set.mem_inter_iff, Set.mem_image]
      constructor
      · rintro ⟨⟨z, hz, rfl⟩, hyK⟩
        have hzK : z ∈ φ.symm '' K := ⟨φ z, hyK, by simp⟩
        exact ⟨z, ⟨hz, hzK⟩, rfl⟩
      · rintro ⟨z, ⟨hz, hzK⟩, rfl⟩
        rcases hzK with ⟨w, hwK, h_eq⟩
        have hφz : φ z = w := by
          have h : φ (φ.symm w) = w := φ.apply_symm_apply w
          rw [h_eq] at *; exact h
        exact ⟨⟨z, hz, rfl⟩, by rw [hφz]; exact hwK⟩
    rw [h1]
    let h_homeo : Homeomorph (E n) (E n) :=
      { toFun := fun y => y + h'
        invFun := fun z => z - h'
        left_inv := by intro z; simp [sub_add_cancel]
        right_inv := by intro z; simp [add_sub_cancel]
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
    have h_img_meas : MeasurableSet B :=
      h_homeo.measurableEmbedding.measurableSet_image.mpr (h_blowUp_meas r hr_pos)
    have h_phi_meas : MeasurableSet (φ.symm '' K) :=
      (hK.image φ.symm.continuous).measurableSet
    have h_set_meas : MeasurableSet (symmDiff A B ∩ φ.symm '' K) :=
      (h_blowUp_meas r hr_pos).symmDiff h_img_meas |>.inter h_phi_meas
    rw [h_vol_image _ h_set_meas]
    have h_goal : volume (symmDiff A B ∩ φ.symm '' K) ≤ ENNReal.ofReal (C * ‖h'‖) :=
      hC r hr_pos hr_lt h'
    simpa [h_norm] using h_goal

  -- Directional variation vanishing
  · intro K hK w hw
    have h_w' : inner ℝ (φ.symm w) ν = 0 := by
      have h1 : inner ℝ (φ.symm w) ν = inner ℝ w (φ ν) := by
        rw [← φ.inner_map_map] <;> simp
      rw [h1, hw]
    have h_main : ∀ (K' : Set (E n)), IsCompact K' →
        Filter.Tendsto (fun r : ℝ => Perimeter.directionalVariationIn (blowUp (φ '' S) (φ x) r) w K')
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      intro K' hK'
      have h_ineq : ∀ (S_r : Set (E n)),
          Perimeter.directionalVariationIn (φ '' S_r) w K' ≤
          Perimeter.directionalVariationIn S_r (φ.symm w) (φ.symm '' K') := by
        intro S_r
        apply iSup_le
        intro ψ
        let ψ' : Perimeter.TestScalar :=
          { toFun := ψ.val.toFun ∘ φ
            smooth := ψ.val.smooth.comp φ.contDiff
            compact := by
              have h1 : Function.support (ψ.val.toFun ∘ φ) = φ.symm '' Function.support ψ.val.toFun := by
                ext y
                simp only [Function.mem_support, Set.mem_image]
                constructor
                · intro h
                  refine ⟨φ y, h, ?_⟩
                  simp
                · rintro ⟨x, hx, rfl⟩
                  simpa using hx
              have h2 : closure (φ.symm '' Function.support ψ.val.toFun) = φ.symm '' closure (Function.support ψ.val.toFun) := by
                have h_cont : Continuous φ.symm := φ.symm.continuous
                have h_closed : IsClosed (φ.symm '' closure (Function.support ψ.val.toFun)) :=
                  (φ.symm.toHomeomorph.isClosed_image).mpr isClosed_closure
                have h3 : closure (φ.symm '' Function.support ψ.val.toFun) ⊆ φ.symm '' closure (Function.support ψ.val.toFun) :=
                  closure_minimal (by intro z hz; rcases hz with ⟨x, hx, rfl⟩; exact ⟨x, subset_closure hx, rfl⟩) h_closed
                have h4 : φ.symm '' closure (Function.support ψ.val.toFun) ⊆ closure (φ.symm '' Function.support ψ.val.toFun) :=
                  image_closure_subset_closure_image h_cont
                exact le_antisymm h3 h4
              have h_tsupp : tsupport (ψ.val.toFun ∘ φ) = φ.symm '' tsupport ψ.val.toFun := by
                simpa [tsupport, h1] using h2
              have h_main : IsCompact (tsupport (ψ.val.toFun ∘ φ)) := by
                rw [h_tsupp]
                exact ψ.val.compact.image φ.symm.continuous
              exact h_main
            bound := fun x => ψ.val.bound (φ x) }
        have h_supp : Function.support ψ'.toFun ⊆ φ.symm '' K' := by
          intro y hy
          have h1 : φ y ∈ Function.support ψ.val.toFun := by
            simpa [ψ', Function.support] using hy
          have h2 : φ y ∈ K' := ψ.property h1
          exact ⟨φ y, h2, by simp⟩
        let ψ'' : {ψ'' : Perimeter.TestScalar // Function.support ψ''.toFun ⊆ φ.symm '' K'} :=
          ⟨ψ', h_supp⟩
        have h_eq : ∫ q in (φ '' S_r), fderiv ℝ ψ.val.toFun q w =
            ∫ y in S_r, fderiv ℝ ψ'.toFun y (φ.symm w) := by
          have h1 : ∫ q in (φ '' S_r), fderiv ℝ ψ.val.toFun q w =
              ∫ y in S_r, fderiv ℝ ψ.val.toFun (φ y) w :=
            h_vol_pres.setIntegral_image_emb hme (fun q => fderiv ℝ ψ.val.toFun q w) S_r
          rw [h1]
          have h_eq2 : (fun y : E n => fderiv ℝ ψ.val.toFun (φ y) w) = (fun y : E n => fderiv ℝ ψ'.toFun y (φ.symm w)) := by
            funext y
            have h_fd : HasFDerivAt ψ.val.toFun (fderiv ℝ ψ.val.toFun (φ y)) (φ y) :=
              (ψ.val.smooth.differentiable (by norm_num)).differentiableAt.hasFDerivAt
            have h_fd2 : HasFDerivAt ψ'.toFun ((fderiv ℝ ψ.val.toFun (φ y)).comp φ) y :=
              h_fd.comp y φ.hasFDerivAt
            have h_eq3 := h_fd2.fderiv
            rw [h_eq3] <;> simp
          rw [h_eq2]
        rw [h_eq]
        exact le_iSup (fun (θ : {θ : Perimeter.TestScalar // Function.support θ.toFun ⊆ φ.symm '' K'}) =>
          ENNReal.ofReal |∫ y in S_r, fderiv ℝ θ.val.toFun y (φ.symm w)|) ψ''
      have h_tendsto := hdata.h_directional_vanishing (φ.symm '' K') (hK'.image φ.symm.continuous) (φ.symm w) h_w'
      have h_zero : Tendsto (fun (_ : ℝ) => (0 : ENNReal)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := tendsto_const_nhds
      have h_nonneg : ∀ᶠ (r : ℝ) in nhdsWithin 0 (Set.Ioi 0), (0 : ENNReal) ≤ Perimeter.directionalVariationIn (blowUp (φ '' S) (φ x) r) w K' := by
        filter_upwards with r
        positivity
      have h_le : ∀ᶠ (r : ℝ) in nhdsWithin 0 (Set.Ioi 0),
          Perimeter.directionalVariationIn (blowUp (φ '' S) (φ x) r) w K' ≤
          Perimeter.directionalVariationIn (blowUp S x r) (φ.symm w) (φ.symm '' K') := by
        filter_upwards [self_mem_nhdsWithin] with r hr
        have hr_ne : r ≠ 0 := hr.ne'
        rw [blowUp_transport hr_ne φ]
        exact h_ineq (blowUp S x r)
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' h_zero h_tendsto h_nonneg h_le
    exact h_main K hK

  -- Density
  · have h_main : Tendsto (fun r : ℝ => volume (blowUp (φ '' S) (φ x) r ∩ ball (0 : E n) 1))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (volume (ball (0 : E n) 1) / 2)) := by
      have h1 : ∀ (r : ℝ), 0 < r → blowUp (φ '' S) (φ x) r ∩ ball (0 : E n) 1 =
          φ '' (blowUp S x r ∩ ball (0 : E n) 1) := by
        intro r hr
        rw [blowUp_transport hr.ne' φ]
        ext y
        simp only [Set.mem_inter_iff, Set.mem_image]
        constructor
        · rintro ⟨⟨z, hz, rfl⟩, hyball⟩
          have hzball : z ∈ ball (0 : E n) 1 := by
            simpa [ball, dist_zero_right, φ.norm_map] using hyball
          exact ⟨z, ⟨hz, hzball⟩, rfl⟩
        · rintro ⟨z, ⟨hz, hyball⟩, rfl⟩
          have hφzball : φ z ∈ ball (0 : E n) 1 := by
            simpa [ball, dist_zero_right, φ.norm_map] using hyball
          exact ⟨⟨z, hz, rfl⟩, hφzball⟩
      have h2 : ∀ᶠ (r : ℝ) in nhdsWithin 0 (Set.Ioi 0),
          volume (blowUp (φ '' S) (φ x) r ∩ ball (0 : E n) 1) =
          volume (blowUp S x r ∩ ball (0 : E n) 1) := by
        filter_upwards [self_mem_nhdsWithin] with r hr
        have hr' : 0 < r := mem_Ioi.mp hr
        have h_meas : MeasurableSet (blowUp S x r ∩ ball (0 : E n) 1) :=
          (h_blowUp_meas r hr').inter isOpen_ball.measurableSet
        rw [h1 r hr', h_vol_image (blowUp S x r ∩ ball (0 : E n) 1) h_meas]
      have h_main2 : Tendsto (fun r : ℝ => volume (blowUp S x r ∩ ball (0 : E n) 1))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (volume (ball (0 : E n) 1) / 2)) := hdata.density
      have h2' : (fun r : ℝ => volume (blowUp (φ '' S) (φ x) r ∩ ball (0 : E n) 1)) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
          (fun r : ℝ => volume (blowUp S x r ∩ ball (0 : E n) 1)) := h2
      exact h_main2.congr' h2'.symm
    exact h_main

  -- Orientation
  · intro ψ hψ_smooth hψ_supp hψ_nonneg hψ_0_pos
    let ψ' := ψ ∘ φ
    have hψ'_smooth : ContDiff ℝ ∞ ψ' := hψ_smooth.comp φ.contDiff
    have hψ'_supp : HasCompactSupport ψ' := by
      have h1 : Function.support ψ' = φ.symm '' Function.support ψ := by
        ext y
        simp only [ψ', Function.mem_support, Set.mem_image]
        constructor
        · intro h
          refine ⟨φ y, h, ?_⟩
          simp
        · rintro ⟨x, hx, rfl⟩
          simpa using hx
      have h2 : closure (φ.symm '' Function.support ψ) = φ.symm '' closure (Function.support ψ) := by
        have h_cont : Continuous φ.symm := φ.symm.continuous
        have h_closed : IsClosed (φ.symm '' closure (Function.support ψ)) :=
          (φ.symm.toHomeomorph.isClosed_image).mpr isClosed_closure
        have h3 : closure (φ.symm '' Function.support ψ) ⊆ φ.symm '' closure (Function.support ψ) :=
          closure_minimal (Set.image_mono subset_closure) h_closed
        have h4 : φ.symm '' closure (Function.support ψ) ⊆ closure (φ.symm '' Function.support ψ) :=
          image_closure_subset_closure_image h_cont
        exact le_antisymm h3 h4
      have h_tsupp : tsupport ψ' = φ.symm '' tsupport ψ := by
        simpa [tsupport, h1] using h2
      have h_main : IsCompact (tsupport ψ') := by
        rw [h_tsupp]
        exact hψ_supp.image φ.symm.continuous
      exact h_main
    have hψ'_nonneg : ∀ x, 0 ≤ ψ' x := by intro x; exact hψ_nonneg (φ x)
    have hψ'_0_pos : 0 < ψ' 0 := by
      have h1 : ψ' 0 = ψ (φ 0) := by rfl
      have h2 : φ 0 = (0 : E n) := by simp
      rw [h1, h2]
      exact hψ_0_pos
    rcases hdata.h_orientation ψ' hψ'_smooth hψ'_supp hψ'_nonneg hψ'_0_pos with ⟨r₀, hr₀_pos, h_orient⟩
    refine ⟨r₀, hr₀_pos, fun r hr_pos hr_lt => ?_⟩
    have h_eq : ∫ q in blowUp (φ '' S) (φ x) r, fderiv ℝ ψ q (φ ν) =
        ∫ y in blowUp S x r, fderiv ℝ ψ' y ν := by
      have h_blowup : blowUp (φ '' S) (φ x) r = φ '' (blowUp S x r) :=
        blowUp_transport hr_pos.ne' φ
      rw [h_blowup]
      have h_chain : ∀ y : E n, fderiv ℝ ψ (φ y) (φ ν) = fderiv ℝ ψ' y ν := by
        intro y
        have h_diff : DifferentiableAt ℝ ψ (φ y) :=
          (hψ_smooth.differentiable (by norm_num)).differentiableAt
        have h_diffφ : DifferentiableAt ℝ φ y := φ.differentiableAt
        have h_eq3 : fderiv ℝ ψ' y = (fderiv ℝ ψ (φ y)).comp (fderiv ℝ φ y) :=
          fderiv_comp y h_diff h_diffφ
        have h_fderiv_φ : fderiv ℝ φ y = (φ : E n →L[ℝ] E n) :=
          LinearIsometryEquiv.fderiv φ
        rw [h_eq3, h_fderiv_φ] <;> simp
      have h1 : ∫ q in φ '' (blowUp S x r), fderiv ℝ ψ q (φ ν) =
          ∫ y in blowUp S x r, fderiv ℝ ψ (φ y) (φ ν) :=
        h_vol_pres.setIntegral_image_emb hme (fun q => fderiv ℝ ψ q (φ ν)) (blowUp S x r)
      rw [h1]
      have h_eq2 : (fun y : E n => fderiv ℝ ψ (φ y) (φ ν)) = (fun y : E n => fderiv ℝ ψ' y ν) := by
        funext y; exact h_chain y
      rw [h_eq2]
    rw [h_eq]
    exact h_orient r hr_pos hr_lt

end Geometry.StructureTheorem
