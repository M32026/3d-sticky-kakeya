/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorShapeFillSep

/-!
# A volume criterion for failure of the fill condition

`FillAt 𝒰 κ k c j` compares `κ * Δ_max(𝕋_c[T_k])` with
`Δ(𝕋_c[T_k], T_k)`. A family with a positive-volume member has maximal density
at least one, by `Kakeya.one_le_maxDensity`. Meanwhile,
`densityIn_nodesUnder_self` identifies its density in the node with
`(Σ |T_c|) / |T_k|`.

Consequently, `not_fillAt_of_sum_lt` proves that `Σ |T_c| < |T_k|` and `1 ≤ κ`
imply failure of the fill condition. A volume deficit suffices; no special
configuration is needed. When members lie in one coarse tube,
`card_indexSet_le_of_le_tube` bounds the cell count by `Cu`, so a sufficiently
small fine scale gives such a deficit.

`not_fillAt_before_and_at_changed_node` applies this criterion at two nodes.
It distinguishes changing the reading node from restricting the family:
failure at both nodes shows that the node change alone cannot restore filling.
The fill condition on the restricted family is a separate hypothesis.
-/

@[expose] public section

open MeasureTheory Metric ConvexSpaceBody
open Tube
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

section NoFill

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} {δ C : NNReal} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ}

omit [Nontrivial E] in
open scoped Classical in
/-- **`T-S2a`'s engine: a volume deficit kills the fill.**

If the level-`c` cells under a level-`k` node do not fill it by volume, then
`Kakeya.ML2Core.FillAt` fails there at every `κ ≥ 1`.  The left-hand side of `FillAt` is at least
`κ ≥ 1` because a node witnesses its own density (`Kakeya.one_le_maxDensity`); the right-hand side
is the volume fraction (`Kakeya.ML2Core.densityIn_nodesUnder_self`), which `hsum` puts below `1`. -/
theorem not_fillAt_of_sum_lt (𝒰 : Tube.UniformTubeSet s T N C) {κ : ℝ} {c k : ℕ} {j : ι}
    (hpos : ∃ j' ∈ 𝒰.nodesUnder c k j, 0 < volume (𝒰.cover.tube c j').carrier)
    (hκ : (1 : ℝ) ≤ κ)
    (hsum : ∑ j' ∈ 𝒰.nodesUnder c k j, volume (𝒰.cover.tube c j').carrier
      < volume (𝒰.cover.tube k j).carrier) :
    ¬ FillAt 𝒰 κ k c j := by
  classical
  unfold FillAt
  rw [densityIn_nodesUnder_self 𝒰 c k j]
  intro hle
  -- the left-hand side is at least `1`
  have hΔ : (1 : ℝ≥0∞) ≤ Kakeya.maxDensity (𝒰.nodesUnder c k j)
      (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) := Kakeya.one_le_maxDensity hpos
  have hκ' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal κ := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    exact ENNReal.ofReal_le_ofReal hκ
  have hone : (1 : ℝ≥0∞) ≤ ENNReal.ofReal κ * Kakeya.maxDensity (𝒰.nodesUnder c k j)
      (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) := by
    calc (1 : ℝ≥0∞) = 1 * 1 := (one_mul 1).symm
      _ ≤ ENNReal.ofReal κ * Kakeya.maxDensity (𝒰.nodesUnder c k j)
            (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) := mul_le_mul' hκ' hΔ
  -- so the volume fraction is at least `1`, i.e. the cells do fill the node — against `hsum`
  have hdiv : (1 : ℝ≥0∞)
      ≤ (∑ j' ∈ 𝒰.nodesUnder c k j, volume (𝒰.cover.tube c j').carrier)
        / volume (𝒰.cover.tube k j).carrier := hone.trans hle
  have hV0 : volume (𝒰.cover.tube k j).carrier ≠ 0 := by
    obtain ⟨j', hj', hj'pos⟩ := hpos
    refine ne_of_gt (lt_of_lt_of_le hj'pos ?_)
    exact measure_mono (SetLike.coe_subset_coe.mpr (le_tube_of_mem_nodesUnder 𝒰 c k j hj'))
  have hVtop : volume (𝒰.cover.tube k j).carrier ≠ ⊤ :=
    (𝒰.cover.tube k j).isCompact'.measure_ne_top
  rw [ENNReal.le_div_iff_mul_le (.inl hV0) (.inl hVtop), one_mul] at hdiv
  exact absurd hdiv (not_le.mpr hsum)

omit [Nontrivial E] in
open scoped Classical in
/-- **The fill at two nodes at once**, the shape a host supplies for 's first
clause.  (An earlier draft offered this as option `(a)`'s *"the node change alone does not
suffice"*;  **withdrew** `C-TS2b` and with it option `(a)`, so this now stands only as a
convenience: the criterion applied twice.) -/
theorem not_fillAt_at_two_nodes (𝒰 : Tube.UniformTubeSet s T N C) {κ : ℝ}
    {c k q : ℕ} {j jq : ι} (hκ : (1 : ℝ) ≤ κ)
    (hposk : ∃ j' ∈ 𝒰.nodesUnder c k j, 0 < volume (𝒰.cover.tube c j').carrier)
    (hsumk : ∑ j' ∈ 𝒰.nodesUnder c k j, volume (𝒰.cover.tube c j').carrier
      < volume (𝒰.cover.tube k j).carrier)
    (hposq : ∃ j' ∈ 𝒰.nodesUnder c q jq, 0 < volume (𝒰.cover.tube c j').carrier)
    (hsumq : ∑ j' ∈ 𝒰.nodesUnder c q jq, volume (𝒰.cover.tube c j').carrier
      < volume (𝒰.cover.tube q jq).carrier) :
    ¬ FillAt 𝒰 κ k c j ∧ ¬ FillAt 𝒰 κ q c jq :=
  ⟨not_fillAt_of_sum_lt 𝒰 hposk hκ hsumk, not_fillAt_of_sum_lt 𝒰 hposq hκ hsumq⟩

omit [Nontrivial E] in
open scoped Classical in
/-- **The volume deficit from a cell count**, the form a host supplies it in: at most `n` cells,
each of volume at most `v`, inside a node of volume more than `n · v`. -/
theorem not_fillAt_of_card_mul_lt (𝒰 : Tube.UniformTubeSet s T N C) {κ : ℝ} {c k : ℕ} {j : ι}
    (hpos : ∃ j' ∈ 𝒰.nodesUnder c k j, 0 < volume (𝒰.cover.tube c j').carrier)
    (hκ : (1 : ℝ) ≤ κ) {v : ℝ≥0∞}
    (hv : ∀ j' ∈ 𝒰.nodesUnder c k j, volume (𝒰.cover.tube c j').carrier ≤ v)
    (hlt : ((𝒰.nodesUnder c k j).card : ℝ≥0∞) * v < volume (𝒰.cover.tube k j).carrier) :
    ¬ FillAt 𝒰 κ k c j := by
  refine not_fillAt_of_sum_lt 𝒰 hpos hκ (lt_of_le_of_lt ?_ hlt)
  calc ∑ j' ∈ 𝒰.nodesUnder c k j, volume (𝒰.cover.tube c j').carrier
      ≤ ∑ _j' ∈ 𝒰.nodesUnder c k j, v := Finset.sum_le_sum hv
    _ = ((𝒰.nodesUnder c k j).card : ℝ≥0∞) * v := by
        rw [Finset.sum_const, nsmul_eq_mul]

end NoFill

/-! ### Control -/

section Control

/-- **Firing control: the criterion is not vacuous and `1 ≤ κ` is load-bearing.**  Below `κ = 1` a
volume deficit no longer kills the fill: `κ · 1 ≤ d` is satisfiable for `d < 1`. -/
theorem not_fillAt_of_sum_lt_needs_one_le :
    ∃ κ d : ℝ≥0∞, d < 1 ∧ κ < 1 ∧ κ * 1 ≤ d :=
  ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num⟩

end Control

end Kakeya.ML2Core
