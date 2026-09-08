/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Mathlib.Analysis.EuclideanFrame
public import Kakeya.Tube.Basic
public import Kakeya.Tube.Param
public import Kakeya.Tube.BushSeparation

/-!
# Two `δ`-tubes through a common point

Two `δ`-tubes that share a point `x` and whose directions differ by at most `r` have
midpoints whose difference is close to the line spanned by the reference direction
(`Kakeya.norm_perp_midpoint_sub_le`) and small in norm
(`Kakeya.norm_midpoint_sub_le_of_common_mem`). These are packaged as `Kakeya.bushFeatures`,
the *feature bundle* that the packing bound `Kakeya.packing_card_le_of_features` consumes
inside a single direction class.

Nothing here is specific to the ambient dimension; the dimension-three count assembled from
these features is `Kakeya.bushCount` in `Kakeya/DimensionThree/BushCount.lean`.

The two constants `Kakeya.bushSeparation.c` and `Kakeya.bushSeparation.δ` used here are in
`Kakeya/Tube/BushSeparation.lean`.
-/

@[expose] public section

namespace Kakeya

/-! ### Features of two `δ`-tubes through a common point

The bush bound is proved by grouping the tubes through `x` into direction classes of width
`δ` and applying the packing bound `Kakeya.packing_card_le_of_features` inside each class.
The lemmas of this section supply the *features* that packing bound consumes: for two
`δ`-tubes through a common point whose directions differ by at most `r`, the difference of
the midpoints is within `r + 4 * δ` of the reference direction line, and has norm at most
`1 + 2 * δ`. -/

section CommonPoint

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [ProperSpace E]

/-- Perpendicular feature of two `δ`-tubes through a common point: if the directions of `T`
and `T₀` differ by at most `r`, the difference of the midpoints is within `r + 4 * δ` of the
line spanned by `T₀.direction`. -/
lemma norm_perp_midpoint_sub_le {δ : NNReal} {T T₀ : Tube δ E} {x : E}
    (hT : x ∈ T.carrier) (hT₀ : x ∈ T₀.carrier) {r : ℝ}
    (hdir : ‖T.direction - T₀.direction‖ ≤ r) :
    ‖(T.midpoint - T₀.midpoint) -
        (inner ℝ (T.midpoint - T₀.midpoint) T₀.direction) • T₀.direction‖
      ≤ r + 4 * (δ : ℝ) := by
  rcases T.exists_param_of_mem_carrier hT with ⟨t, ht, hxT⟩
  rcases T₀.exists_param_of_mem_carrier hT₀ with ⟨t₀, ht₀, hxT₀⟩
  set z := x - T.midpoint - t • T.direction with hz_def
  set z₀ := x - T₀.midpoint - t₀ • T₀.direction with hz₀_def
  have hz_norm : ‖z‖ ≤ (δ : ℝ) := hxT
  have hz₀_norm : ‖z₀‖ ≤ (δ : ℝ) := hxT₀
  have hmid_eq : T.midpoint - T₀.midpoint = (-t) • T.direction + t₀ • T₀.direction + (z₀ - z) := by
    apply sub_eq_zero.mp
    dsimp [z, z₀]
    abel
    simp [add_comm]
  have hz_sub_norm : ‖z₀ - z‖ ≤ 2 * (δ : ℝ) := by
    calc
      ‖z₀ - z‖ ≤ ‖z₀‖ + ‖z‖ := norm_sub_le _ _
      _ ≤ (δ : ℝ) + (δ : ℝ) := add_le_add hz₀_norm hz_norm
      _ = 2 * (δ : ℝ) := by ring
  have h_abs_t : |-t| ≤ 1 / 2 := by
    rw [abs_neg]
    exact ht
  have h_norm_dir : ‖T₀.direction‖ = 1 := T₀.norm_direction
  have h := norm_perp_le_of_decomp h_norm_dir hmid_eq h_abs_t hdir hz_sub_norm
  -- simplify r + 2 * (2 * (δ : ℝ)) = r + 4 * (δ : ℝ)
  have : r + 2 * (2 * (δ : ℝ)) = r + 4 * (δ : ℝ) := by ring
  rw [this] at h
  exact h

/-- Longitudinal feature of two `δ`-tubes through a common point: both midpoints are within
`1 / 2 + δ` of the common point, so their difference has norm at most `1 + 2 * δ`. -/
lemma norm_midpoint_sub_le_of_common_mem {δ : NNReal} {T T₀ : Tube δ E} {x : E}
    (hT : x ∈ T.carrier) (hT₀ : x ∈ T₀.carrier) :
    ‖T.midpoint - T₀.midpoint‖ ≤ 1 + 2 * (δ : ℝ) := by
  rcases T.exists_param_of_mem_carrier hT with ⟨t, ht, hxT⟩
  rcases T₀.exists_param_of_mem_carrier hT₀ with ⟨s, hs, hxT₀⟩
  have hdirT : ‖T.direction‖ = 1 := T.norm_direction
  have hdirT₀ : ‖T₀.direction‖ = 1 := T₀.norm_direction
  have h_smulT : ‖t • T.direction‖ = |t| := by
    calc
      ‖t • T.direction‖ = |t| * ‖T.direction‖ := norm_smul _ _
      _ = |t| * 1 := by rw [hdirT]
      _ = |t| := by simp
  have h_smulT₀ : ‖s • T₀.direction‖ = |s| := by
    calc
      ‖s • T₀.direction‖ = |s| * ‖T₀.direction‖ := norm_smul _ _
      _ = |s| * 1 := by rw [hdirT₀]
      _ = |s| := by simp
  have hxT_midpoint : ‖x - T.midpoint‖ ≤ 1/2 + (δ : ℝ) := by
    calc
      ‖x - T.midpoint‖ = ‖(x - T.midpoint - t • T.direction) + t • T.direction‖ := by
        abel
      _ ≤ ‖x - T.midpoint - t • T.direction‖ + ‖t • T.direction‖ := norm_add_le _ _
      _ ≤ (δ : ℝ) + |t| := by
        rw [h_smulT]
        nlinarith
      _ ≤ (δ : ℝ) + 1/2 := by
        nlinarith
      _ = 1/2 + (δ : ℝ) := by ring
  have hxT₀_midpoint : ‖x - T₀.midpoint‖ ≤ 1/2 + (δ : ℝ) := by
    calc
      ‖x - T₀.midpoint‖ = ‖(x - T₀.midpoint - s • T₀.direction) + s • T₀.direction‖ := by
        abel
      _ ≤ ‖x - T₀.midpoint - s • T₀.direction‖ + ‖s • T₀.direction‖ := norm_add_le _ _
      _ ≤ (δ : ℝ) + |s| := by
        rw [h_smulT₀]
        nlinarith
      _ ≤ (δ : ℝ) + 1/2 := by
        nlinarith
      _ = 1/2 + (δ : ℝ) := by ring
  calc
    ‖T.midpoint - T₀.midpoint‖ = ‖(x - T₀.midpoint) - (x - T.midpoint)‖ := by
      congr 1; abel
    _ ≤ ‖x - T₀.midpoint‖ + ‖x - T.midpoint‖ := norm_sub_le _ _
    _ ≤ (1/2 + (δ : ℝ)) + (1/2 + (δ : ℝ)) := by nlinarith
    _ = 1 + 2 * (δ : ℝ) := by ring

/-- The feature bundle consumed by `Kakeya.packing_card_le_of_features`, for a family of
`δ`-tubes all passing through `x` whose directions all lie within `δ` of a common unit
vector `u`, measured against the member `T i₀` of the family. The constants are
`C_dir = 2`, `C_perp = 6` and `C_long = 3`. -/
lemma bushFeatures {δ : NNReal} (hδ1 : (δ : ℝ) ≤ 1) {ι : Type*} (s : Finset ι)
    (T : ι → Tube δ E) (x u : E) {i₀ : ι} (hi₀ : i₀ ∈ s)
    (hx : ∀ i ∈ s, x ∈ (T i).carrier)
    (hu : ∀ i ∈ s, ‖(T i).direction - u‖ ≤ (δ : ℝ)) :
    ∀ i ∈ s, ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      ‖ε • (T i).direction - (T i₀).direction‖ ≤ 2 * (δ : ℝ) ∧
      ‖((T i).midpoint - (T i₀).midpoint) -
          (inner ℝ ((T i).midpoint - (T i₀).midpoint) (T i₀).direction) • (T i₀).direction‖
        ≤ 6 * (δ : ℝ) ∧
      |inner ℝ ((T i).midpoint - (T i₀).midpoint) (T i₀).direction| ≤ 3 := by
  intro i hi
  refine ⟨1, Or.inl rfl, ?_, ?_, ?_⟩
  · -- Direction bound: ‖1 • (T i).direction - (T i₀).direction‖ ≤ 2 * δ
    rw [one_smul]
    have h_dir : ‖(T i).direction - (T i₀).direction‖ ≤ 2 * (δ : ℝ) := by
      calc
        ‖(T i).direction - (T i₀).direction‖
            = ‖((T i).direction - u) - ((T i₀).direction - u)‖ := by
              congr 1; abel
        _ ≤ ‖(T i).direction - u‖ + ‖(T i₀).direction - u‖ := norm_sub_le _ _
        _ ≤ (δ : ℝ) + (δ : ℝ) := by
          gcongr
          · exact hu i hi
          · exact hu i₀ hi₀
        _ = 2 * (δ : ℝ) := by ring
    exact h_dir
  · -- Perpendicular feature: apply norm_perp_midpoint_sub_le with r := 2 * (δ : ℝ)
    have h_dir_bound : ‖(T i).direction - (T i₀).direction‖ ≤ 2 * (δ : ℝ) := by
      calc
        ‖(T i).direction - (T i₀).direction‖
            = ‖((T i).direction - u) - ((T i₀).direction - u)‖ := by
              congr 1; abel
        _ ≤ ‖(T i).direction - u‖ + ‖(T i₀).direction - u‖ := norm_sub_le _ _
        _ ≤ (δ : ℝ) + (δ : ℝ) := by
          gcongr
          · exact hu i hi
          · exact hu i₀ hi₀
        _ = 2 * (δ : ℝ) := by ring
    have h_perp := norm_perp_midpoint_sub_le (hx i hi) (hx i₀ hi₀) h_dir_bound
    have : 2 * (δ : ℝ) + 4 * (δ : ℝ) = 6 * (δ : ℝ) := by ring
    rw [this] at h_perp
    exact h_perp
  · -- Longitudinal feature: bound via norm and Cauchy-Schwarz
    have h_mid_norm : ‖(T i).midpoint - (T i₀).midpoint‖ ≤ 1 + 2 * (δ : ℝ) :=
      norm_midpoint_sub_le_of_common_mem (hx i hi) (hx i₀ hi₀)
    have h_dir_norm : ‖(T i₀).direction‖ = 1 := (T i₀).norm_direction
    have h_inner_bound : |inner ℝ ((T i).midpoint - (T i₀).midpoint) (T i₀).direction|
        ≤ ‖(T i).midpoint - (T i₀).midpoint‖ * ‖(T i₀).direction‖ :=
      abs_real_inner_le_norm _ _
    rw [h_dir_norm, mul_one] at h_inner_bound
    have h_ineq : 1 + 2 * (δ : ℝ) ≤ 3 := by
      nlinarith
    nlinarith

end CommonPoint

end Kakeya
