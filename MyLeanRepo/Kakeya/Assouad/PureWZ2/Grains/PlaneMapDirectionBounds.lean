import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.GlobalProjectionHelpers
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition3_2PaperStatements
import Mathlib.Tactic

/-!
# Plane map direction bounds for Pure WZ2 grains

## Key results

1. `plane_map_horizontal_component_bound`: a unit normal exactly perpendicular
   to a line-class tube direction (`d 2 ≥ 1/2`) has at least one horizontal
   component with absolute value `≥ 1/(2*√2) > 1/3`.

2. `PureWZ2PaperADSet1.transfer_to_global_direction_of_horizontal`: relaxed
   version of `transfer_to_global_direction` that drops the unused vertical
   component bound `hv2`. Only `hv0 : 1/3 ≤ |v 0|` is needed.

## Why the vertical bound is unnecessary

The original `transfer_to_global_direction` requires `|v 2| ≤ 1/10`, but this
hypothesis is not used in its proof. The projection onto the horizontal part
`h = v - v2 • e3` is an exact translation by `-v2 * z`, which preserves the AD
constant regardless of `|v2|`. The only geometric requirement is a lower bound
on `|v 0|` to control the scaling factor `c = 1/|v 0|`.

## Horizontal bound from line-class perpendicularity

For a unit normal `n` with `inner n d = 0` and `d 2 ≥ 1/2`:
- `n 2 * d 2 = -(n 0 * d 0 + n 1 * d 1)`
- By Cauchy-Schwarz: `|n 2| * d 2 ≤ √(1 - n 2^2) * √(1 - d 2^2)`
- This gives `n 2^2 ≤ 1 - d 2^2 ≤ 3/4`
- Hence `n 0^2 + n 1^2 ≥ 1/4`, so `max(|n 0|, |n 1|) ≥ 1/(2*√2) > 1/3`.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

/-- Horizontal component lower bound for a normal perpendicular to a line-class direction.

If `n` is a unit vector exactly perpendicular to a unit vector `d` with
`d 2 ≥ 1/2`, then `max (|n 0|) (|n 1|) ≥ 1 / (2 * Real.sqrt 2) > 1 / 3`.

This means at least one horizontal component is strictly greater than `1/3`,
which is the threshold needed by `transfer_to_global_direction`. -/
lemma plane_map_horizontal_component_bound
    (n d : Point3)
    (hn_unit : ‖n‖ = 1)
    (hd_unit : ‖d‖ = 1)
    (hd_vertical : 1 / 2 ≤ d 2)
    (h_perp : inner ℝ n d = 0) :
    1 / 3 ≤ |n 0| ∨ 1 / 3 ≤ |n 1| := by
  have h_inner_expand : ∀ (x y : Point3), inner ℝ x y = x 0 * y 0 + x 1 * y 1 + x 2 * y 2 := by
    intro x y
    have h_pol : inner ℝ x y = (‖x + y‖^2 - ‖x‖^2 - ‖y‖^2) / 2 := by
      rw [norm_add_sq_real] <;> ring
    rw [h_pol]
    have h1 : ‖x + y‖^2 = ∑ i : Fin 3, (x i + y i)^2 := EuclideanSpace.real_norm_sq_eq (x + y)
    have h2 : ‖x‖^2 = ∑ i : Fin 3, (x i)^2 := EuclideanSpace.real_norm_sq_eq x
    have h3 : ‖y‖^2 = ∑ i : Fin 3, (y i)^2 := EuclideanSpace.real_norm_sq_eq y
    rw [h1, h2, h3]
    simp [Fin.sum_univ_succ] <;> ring
  have h_coord : ∀ (x : Point3), (x 0)^2 + (x 1)^2 + (x 2)^2 = ‖x‖^2 := by
    intro x
    have h1 : ‖x‖^2 = ∑ i : Fin 3, (x i)^2 := EuclideanSpace.real_norm_sq_eq x
    have h4 : (x 0)^2 + (x 1)^2 + (x 2)^2 = ∑ i : Fin 3, (x i)^2 := by
      simp [Fin.sum_univ_succ] <;> ring
    rw [h4, h1]
  have h_inner_coord : inner ℝ n d = n 0 * d 0 + n 1 * d 1 + n 2 * d 2 := h_inner_expand n d
  have h1 : n 2 * d 2 = -(n 0 * d 0 + n 1 * d 1) := by
    rw [h_inner_coord] at h_perp
    linarith
  have h_cs : (n 0 * d 0 + n 1 * d 1)^2 ≤ ((n 0)^2 + (n 1)^2) * ((d 0)^2 + (d 1)^2) := by
    nlinarith [sq_nonneg (n 0 * d 1 - n 1 * d 0)]
  have h3 : (n 2)^2 * (d 2)^2 ≤ ((n 0)^2 + (n 1)^2) * ((d 0)^2 + (d 1)^2) := by
    have h4 : (n 2 * d 2)^2 = (n 0 * d 0 + n 1 * d 1)^2 := by
      rw [h1] <;> ring
    have h5 : (n 2)^2 * (d 2)^2 = (n 2 * d 2)^2 := by ring
    rw [h5, h4]
    exact h_cs
  have h_nsq : (n 0)^2 + (n 1)^2 + (n 2)^2 = 1 := by
    have h := h_coord n
    rw [hn_unit] at h
    norm_num at h
    exact h
  have h_dsq : (d 0)^2 + (d 1)^2 + (d 2)^2 = 1 := by
    have h := h_coord d
    rw [hd_unit] at h
    norm_num at h
    exact h
  have h6 : (n 2)^2 ≤ (d 0)^2 + (d 1)^2 := by
    nlinarith
  have h7 : (d 0)^2 + (d 1)^2 ≤ 3 / 4 := by
    nlinarith
  have h9 : (n 0)^2 + (n 1)^2 ≥ 1 / 4 := by
    nlinarith
  by_cases h10 : (n 0)^2 ≥ 1 / 8
  · have h11 : 1 / 3 ≤ |n 0| := by
      have h12 : (1 / 3 : ℝ)^2 ≤ (n 0)^2 := by nlinarith
      have h13 : (n 0)^2 = |n 0|^2 := by rw [sq_abs]
      nlinarith [abs_nonneg (n 0)]
    exact Or.inl h11
  · have h14 : (n 1)^2 ≥ 1 / 8 := by nlinarith
    have h15 : 1 / 3 ≤ |n 1| := by
      have h16 : (1 / 3 : ℝ)^2 ≤ (n 1)^2 := by nlinarith
      have h17 : (n 1)^2 = |n 1|^2 := by rw [sq_abs]
      nlinarith [abs_nonneg (n 1)]
    exact Or.inr h15

/-- Relaxed direction transfer: only requires a horizontal component bound.

Drops the unused `hv2 : |v 2| ≤ 1/10` hypothesis from
`PureWZ2PaperADSet1.transfer_to_global_direction`. The translation by
`v2 * z` is exact and preserves the AD constant for any `v2`. -/
lemma PureWZ2PaperADSet1.transfer_to_global_direction_of_horizontal
    {E : Set Point3} {delta alpha : ℝ} {C : ENNReal}
    {v : Point3} (z : ℝ)
    (hE_height : ∀ p ∈ E, inner ℝ p e3 = z)
    (hv_unit : ‖v‖ = 1)
    (hv0 : 1 / 3 ≤ |v (0 : Fin 3)|)
    (hAD : PureWZ2PaperADSet1 (scalarProjection v E) delta alpha C)
    (hdelta_le_one : delta ≤ 1) :
    PureWZ2PaperADSet1
      (scalarProjection (globalGrainDirection (v 1 / v 0)) E)
      delta alpha (100 * C) := by
  let v0 : ℝ := v 0
  let v1 : ℝ := v 1
  let v2 : ℝ := v 2
  let h : Point3 := v - v2 • e3
  have h_e30 : e3 0 = 0 := by simp [e3, EuclideanSpace.single]
  have h_e31 : e3 1 = 0 := by simp [e3, EuclideanSpace.single]
  have h_e32 : e3 2 = 1 := by simp [e3, EuclideanSpace.single]
  have h_h0 : h 0 = v0 := by
    dsimp only [h, v0]; simp [Pi.smul_apply, h_e30] <;> ring
  have h_h1 : h 1 = v1 := by
    dsimp only [h, v1]; simp [Pi.smul_apply, h_e31] <;> ring
  have h_h2 : h 2 = 0 := by
    dsimp only [h, v2]; simp [Pi.smul_apply, h_e32] <;> ring
  have h_proj_h : scalarProjection h E =
      (fun x : ℝ => x - v2 * z) '' scalarProjection v E := by
    ext y
    simp only [scalarProjection, Set.mem_image]
    constructor
    · rintro ⟨p, hp, rfl⟩
      have hz : inner ℝ p e3 = z := hE_height p hp
      have h_eq : inner ℝ p h = inner ℝ p v - v2 * z := by
        have h1 : inner ℝ p h = inner ℝ p v - inner ℝ p (v2 • e3) := by
          simpa [h, inner_sub_right] using rfl
        rw [h1]
        have h2 : inner ℝ p (v2 • e3) = v2 * inner ℝ p e3 := by
          simp [inner_smul_right] <;> ring
        rw [h2, hz] <;> ring
      exact ⟨inner ℝ p v, ⟨p, hp, rfl⟩, h_eq.symm⟩
    · rintro ⟨x, ⟨p, hp, rfl⟩, rfl⟩
      have hz : inner ℝ p e3 = z := hE_height p hp
      have h_eq : inner ℝ p h = inner ℝ p v - v2 * z := by
        have h1 : inner ℝ p h = inner ℝ p v - inner ℝ p (v2 • e3) := by
          simpa [h, inner_sub_right] using rfl
        rw [h1]
        have h2 : inner ℝ p (v2 • e3) = v2 * inner ℝ p e3 := by
          simp [inner_smul_right] <;> ring
        rw [h2, hz] <;> ring
      exact ⟨p, hp, h_eq⟩
  have hAD_h : PureWZ2PaperADSet1 (scalarProjection h E) delta alpha C := by
    rw [h_proj_h]
    have h_trans := hAD.translate (-v2 * z)
    have h_eq : (fun x : ℝ => x + -v2 * z) = (fun x : ℝ => x - v2 * z) := by
      funext x; ring
    rw [h_eq] at h_trans
    exact h_trans
  have h_v0_nonzero : v0 ≠ 0 := by
    have h : 1 / 3 ≤ |v0| := hv0
    have h' : |v0| ≠ 0 := by linarith
    simpa [abs_eq_zero] using h'
  have h_abs_lower : 1 / 3 ≤ |v0| := hv0
  have h_abs_upper : |v0| ≤ 1 := by
    have h6 : |v0| ≤ ‖v‖ := PiLp.norm_apply_le v (0 : Fin 3)
    linarith [hv_unit]
  have h_abs_pos : 0 < |v0| := by linarith
  have h_inv_lower : 1 / 4 ≤ 1 / |v0| := by
    have h_pos : 0 < |v0| := h_abs_pos
    have h_le : |v0| ≤ 4 := by linarith
    have h5 : 1 / (4 : ℝ) ≤ 1 / |v0| := one_div_le_one_div_of_le h_pos h_le
    exact h5
  have h_inv_upper : 1 / |v0| ≤ 3 := by
    have h_pos : 0 < |v0| := h_abs_pos
    have h_ge : 1 ≤ 3 * |v0| := by linarith
    have h_diff : 3 - 1 / |v0| = (3 * |v0| - 1) / |v0| := by
      field_simp [h_pos.ne'] <;> ring
    have h_nonneg : 0 ≤ (3 * |v0| - 1) / |v0| := by
      apply div_nonneg
      · linarith
      · exact abs_nonneg v0
    linarith [h_diff, h_nonneg]
  have h_cases : 0 < v0 ∨ v0 < 0 := by
    by_cases h : 0 ≤ v0
    · have h' : 0 < v0 := by exact lt_of_le_of_ne h h_v0_nonzero.symm
      exact Or.inl h'
    · have h' : v0 < 0 := by linarith
      exact Or.inr h'
  rcases h_cases with (h_v0_pos | h_v0_neg)
  · let c : ℝ := 1 / v0
    have hc_pos : 0 < c := by positivity
    have hc_range : 1 / 4 ≤ c := by
      dsimp only [c]
      have h_eq : 1 / v0 = 1 / |v0| := by
        have h_abs : |v0| = v0 := abs_of_pos h_v0_pos
        rw [h_abs]
      rw [h_eq]
      exact h_inv_lower
    have hc_upper : c ≤ 4 := by
      dsimp only [c]
      have h_eq : 1 / v0 = 1 / |v0| := by
        have h_abs : |v0| = v0 := abs_of_pos h_v0_pos
        rw [h_abs]
      rw [h_eq]
      have h : 1 / |v0| ≤ 3 := h_inv_upper
      linarith
    have h_dir : globalGrainDirection (v1 / v0) = c • h := by
      ext i
      fin_cases i
      · simp [globalGrainDirection, h_h0, c] <;> field_simp [h_v0_nonzero] <;> ring
      · simp [globalGrainDirection, h_h1, c] <;> field_simp [h_v0_nonzero] <;> ring
      · simp [globalGrainDirection, h_h2]
    rw [h_dir]
    have h_scale : scalarProjection (c • h) E =
        (fun x : ℝ => c * x) '' scalarProjection h E :=
      scalarProjection_scale c hc_pos h E
    rw [h_scale]
    exact hAD_h.scale c hc_pos hc_range hc_upper hdelta_le_one
  · let c : ℝ := 1 / |v0|
    have hc_pos : 0 < c := by
      dsimp only [c]
      exact one_div_pos.mpr h_abs_pos
    have hc_range : 1 / 4 ≤ c := by
      dsimp only [c]
      exact h_inv_lower
    have hc_upper : c ≤ 4 := by
      dsimp only [c]
      have h : 1 / |v0| ≤ 3 := h_inv_upper
      linarith
    have h_dir : globalGrainDirection (v1 / v0) = -c • h := by
      ext i
      fin_cases i
      · simp [globalGrainDirection, h_h0, c, abs_of_neg h_v0_neg]
        <;> field_simp [h_v0_nonzero] <;> ring
      · simp [globalGrainDirection, h_h1, c, abs_of_neg h_v0_neg]
        <;> field_simp [h_v0_nonzero] <;> ring
      · simp [globalGrainDirection, h_h2]
    have hAD_scale : PureWZ2PaperADSet1 ((fun x : ℝ => c * x) '' scalarProjection h E)
        delta alpha (100 * C) :=
      hAD_h.scale c hc_pos hc_range hc_upper hdelta_le_one
    have h_neg_proj : scalarProjection (-c • h) E =
        (fun x : ℝ => -x) '' ((fun x : ℝ => c * x) '' scalarProjection h E) := by
      have h1 : -c • h = c • (-h) := by ext j; simp
      rw [h1]
      have h3 := scalarProjection_scale c hc_pos (-h) E
      rw [h3]
      have h4 : scalarProjection (-h) E = (fun x : ℝ => -x) '' scalarProjection h E := by
        ext y
        simp only [scalarProjection, Set.mem_image]
        constructor
        · rintro ⟨p, hp, rfl⟩
          exact ⟨inner ℝ p h, ⟨p, hp, rfl⟩, by simp [inner_neg_right]⟩
        · rintro ⟨x, ⟨p, hp, rfl⟩, rfl⟩
          exact ⟨p, hp, by simp [inner_neg_right]⟩
      rw [h4]
      ext y
      simp only [Set.mem_image]
      constructor
      · rintro ⟨x, ⟨w, hw, hx : -w = x⟩, hy : c * x = y⟩
        refine ⟨c * w, ⟨w, hw, rfl⟩, ?_⟩
        have h : -(c * w) = y := by
          calc -(c * w) = c * (-w) := by ring
            _ = c * x := by rw [hx]
            _ = y := hy
        exact h
      · rintro ⟨z2, ⟨w, hw, hz : c * w = z2⟩, hy : -z2 = y⟩
        refine ⟨-w, ⟨w, hw, rfl⟩, ?_⟩
        have h : c * (-w) = y := by
          calc c * (-w) = -(c * w) := by ring
            _ = -z2 := by rw [hz]
            _ = y := hy
        exact h
    rw [h_dir, h_neg_proj]
    exact hAD_scale.negate

end Kakeya.Assouad

end
