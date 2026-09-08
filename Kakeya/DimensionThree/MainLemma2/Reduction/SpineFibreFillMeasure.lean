/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFibreTowerData
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorShapeParentFill

/-!
# The count bridge, measured: the replacement cannot deliver it

**Finding: the density-to-count bridge that  asks to keep is `FillAt` in disguise, so replacing
`FillAt` by a biased-factoring body cannot produce it.  No existing statement is changed in this
batch, and the condition is returned unused.**

## What  asks, and what the tree actually uses

`hfill` enters the whole floor chain through **exactly one** lemma — the existing
`Kakeya.ML2Core.maxDensity_mul_le_card_of_fillAt`, whose own docstring says so
(`SpineFloorShapeParentFill.lean:135-138`: *"This is the only place the fill hypothesis is
used"*).  Its conclusion is the density-to-count bridge

  `κ · Δ_max(𝕋_c[T_k]) · (c₃ ρ_k²) ≤ #𝕋_c[T_k] · (C₃ ρ_c²)`.   (†)

 asks to keep (†) and to obtain it from a factoring body `W ⊆ T_k` supplied by
`ConvexSpaceBody.nonempty_biasedFactorization` (GWZ 9.2) instead of from `FillAt`.

## What a factoring body gives — `maxDensity_mul_volume_le_of_body`: if some body `W` captures the maximal density up to `Cf`,
i.e. `Δ_max(A) ≤ Cf · Δ(A, W)`, and each cell has volume at most `v_max`, then

  `Δ_max(A) · |W| ≤ Cf · (#A · v_max)`.   (‡)

That is the honest content of the factoring: the **factoring body's own volume** appears on the
left, not the node's.  (‡) is `Δ(A,W) = (Σ_{A ∩ W} |V|)/|W|` and nothing more, and it holds for
*any* `W`.

## Why (‡) does not give (†) — in the sharpest form

(†) has `c₃ρ_k²`, the **node's** volume, where (‡) has `|W|`.  To pass from (‡) to (†) one needs

  `c₃ ρ_k² ≤ |W|`,

i.e. *the maximiser is comparable to the node* — which is the fill.  And this is not a lossy
reading of the situation: `fillAt_of_count_bridge` compiles the converse implication outright —

> **(†) ⟹ `FillAt`**, at the price of the two dimensional tube-volume constants
> (`fillAt_of_count_bridge_grid` is the same statement with `C₃ρ_k²` and `c₃ρ_c²` substituted).

So (†) and `FillAt` are equivalent up to `(c₃/C₃)`-type factors.  A hypothesis strictly weaker than
`FillAt` therefore **cannot** yield (†); in particular the biased factoring cannot, because (‡) is
all it gives and (‡) is weaker precisely by the missing `c₃ρ_k² ≤ |W|`.

`maxDensity_mul_volume_le_of_body_vacuous_at_zero` is the firing control: at `|W| = 0` the
factoring bound is vacuous, which is the same missing volume comparison read at its extreme.

## Consequently

Changing `FloorHypothesisAt`, its consumers and `hclose` on this route would replace a hypothesis
the tree cannot discharge by one it also cannot discharge, while breaking ~120 call sites across
20 files.  The condition is therefore returned unused and ****; what 
correctly identifies — that `Δ_max` maximises over every convex body and nothing privileges the
node's tube — is exactly why (†) is as strong as it is, and the row that has to move is (†)
itself, not the hypothesis in front of it.

## A conflict in the directive, names the twin *"at `SpineFloorTerminal.lean:610-637`"*, but those lines lie **inside the
`hfac` hypothesis block** (`hfac` begins at `:612`), and the same message excludes `hfac` from the
condition.  Also, `hfill` is not a field of `Kakeya.ML2Core.FloorHypothesisAt` at all — it is a
hypothesis of the producers `floor_of_windowLevels_of_fill` /
`floorHypothesisAt_of_windowLevels`; `FloorHypothesisAt`'s three conjuncts are the parent-level
row, the parent-density row and the count floor.  So "replace `hfill` in `FloorHypothesisAt`" has
no referent, and the `Iff.rfl` compatibility between `FloorHypothesisAt` and `hfac`'s tail cannot be
kept while either side moves.

## Family / shading / level pair

| declaration | family / shading | level pair |
|---|---|---|
| `maxDensity_mul_volume_le_of_body` | the tower; no shading | `(k,c)` at node `j` |
| `fillAt_of_count_bridge`, `…_grid` | the tower; no shading | `(k,c)` at node `j` |

## A1-a

No `GridUniformCore`; no `(F)`-branch interface statement is defined or altered; no existing line is
modified anywhere in this batch.
-/

@[expose] public section

open scoped NNReal ENNReal
open MeasureTheory Tube

namespace Kakeya.ML2Core

section CountBridge

universe u

variable {ι : Type u} {δ Cu : NNReal} {s : Finset ι}
  {T : ι → Tube δ (EuclideanSpace ℝ (Fin 3))}

open scoped Classical in
/-- **What a maximising body gives.** -/
theorem maxDensity_mul_volume_le_of_body
    (𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu) {c k : ℕ} {j : ι}
    (W : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) {Cf vmax : ENNReal}
    (hcap : Kakeya.maxDensity (𝒰.nodesUnder c k j)
        (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)
      ≤ Cf * Kakeya.densityIn (𝒰.nodesUnder c k j)
          (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) W)
    (hvmax : ∀ j' ∈ 𝒰.nodesUnder c k j, volume (𝒰.cover.tube c j').carrier ≤ vmax) :
    Kakeya.maxDensity (𝒰.nodesUnder c k j)
        (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) * volume W.carrier
      ≤ Cf * (((𝒰.nodesUnder c k j).card : ENNReal) * vmax) := by
  classical
  set A := 𝒰.nodesUnder c k j with hA
  set V : ι → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) :=
    fun j' => (𝒰.cover.tube c j').toConvexSpaceBody with hV
  have hsum : Kakeya.densityIn A V W * volume W.carrier
      ≤ ∑ j' ∈ A, volume (V j').carrier := by
    unfold Kakeya.densityIn
    refine le_trans (ENNReal.mul_le_of_le_div le_rfl) ?_
    exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  calc Kakeya.maxDensity A V * volume W.carrier
      ≤ (Cf * Kakeya.densityIn A V W) * volume W.carrier := mul_le_mul' hcap le_rfl
    _ = Cf * (Kakeya.densityIn A V W * volume W.carrier) := by ring
    _ ≤ Cf * ∑ j' ∈ A, volume (V j').carrier := mul_le_mul' le_rfl hsum
    _ ≤ Cf * ∑ _j' ∈ A, vmax := mul_le_mul' le_rfl (Finset.sum_le_sum hvmax)
    _ = Cf * ((A.card : ENNReal) * vmax) := by rw [Finset.sum_const, nsmul_eq_mul]

open scoped Classical in
/-- **The count bridge implies the fill.** -/
theorem fillAt_of_count_bridge
    (𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu) {κ κ₀ : ℝ} {c k : ℕ} {j : ι}
    {Ck cc P Q : ENNReal}
    (hCk : volume (𝒰.cover.tube k j).carrier ≤ Ck)
    (hcc : ∀ j' ∈ 𝒰.nodesUnder c k j, cc ≤ volume (𝒰.cover.tube c j').carrier)
    (hP0 : P ≠ 0) (hPtop : P ≠ ⊤)
    (hk0 : volume (𝒰.cover.tube k j).carrier ≠ 0)
    (hktop : volume (𝒰.cover.tube k j).carrier ≠ ⊤)
    (hbridge : ENNReal.ofReal κ₀
        * Kakeya.maxDensity (𝒰.nodesUnder c k j)
            (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) * Q
      ≤ ((𝒰.nodesUnder c k j).card : ENNReal) * P)
    (hnum : ENNReal.ofReal κ * Ck * P ≤ ENNReal.ofReal κ₀ * Q * cc) :
    FillAt 𝒰 κ k c j := by
  classical
  set A := 𝒰.nodesUnder c k j with hA
  set X := Kakeya.maxDensity A (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) with hX
  unfold FillAt
  rw [densityIn_nodesUnder_self 𝒰 c k j, ENNReal.le_div_iff_mul_le (Or.inl hk0) (Or.inl hktop)]
  have hkey : (ENNReal.ofReal κ * X * volume (𝒰.cover.tube k j).carrier) * P
      ≤ (∑ j' ∈ A, volume (𝒰.cover.tube c j').carrier) * P := by
    calc (ENNReal.ofReal κ * X * volume (𝒰.cover.tube k j).carrier) * P
        ≤ (ENNReal.ofReal κ * X * Ck) * P := mul_le_mul' (mul_le_mul' le_rfl hCk) le_rfl
      _ = X * (ENNReal.ofReal κ * Ck * P) := by ring
      _ ≤ X * (ENNReal.ofReal κ₀ * Q * cc) := mul_le_mul' le_rfl hnum
      _ = (ENNReal.ofReal κ₀ * X * Q) * cc := by ring
      _ ≤ (((A.card : ENNReal)) * P) * cc := mul_le_mul' hbridge le_rfl
      _ = ((A.card : ENNReal) * cc) * P := by ring
      _ = (∑ _j' ∈ A, cc) * P := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (∑ j' ∈ A, volume (𝒰.cover.tube c j').carrier) * P :=
          mul_le_mul' (Finset.sum_le_sum hcc) le_rfl
  refine (ENNReal.mul_le_mul_iff_right hP0 hPtop).mp ?_
  calc P * (ENNReal.ofReal κ * X * volume (𝒰.cover.tube k j).carrier)
      = (ENNReal.ofReal κ * X * volume (𝒰.cover.tube k j).carrier) * P := by ring
    _ ≤ (∑ j' ∈ A, volume (𝒰.cover.tube c j').carrier) * P := hkey
    _ = P * (∑ j' ∈ A, volume (𝒰.cover.tube c j').carrier) := by ring

open scoped Classical in
/-- **The two dimensional constants, at the grid.** -/
theorem fillAt_of_count_bridge_grid (hδ1 : δ ≤ 1)
    (𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu) {κ κ₀ : ℝ} {c k : ℕ} {j : ι}
    (hk0 : volume (𝒰.cover.tube k j).carrier ≠ 0)
    (hbridge : ENNReal.ofReal κ₀
        * Kakeya.maxDensity (𝒰.nodesUnder c k j)
            (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody)
        * (((Tube.le_volume.c 3 : NNReal) : ENNReal)
            * ((Tube.gridScale δ (Tube.ssfGridLen δ) k : NNReal) : ENNReal) ^ (2 : ℕ))
      ≤ ((𝒰.nodesUnder c k j).card : ENNReal)
        * (((Tube.volume_le.C 3 : NNReal) : ENNReal)
            * ((Tube.gridScale δ (Tube.ssfGridLen δ) c : NNReal) : ENNReal) ^ (2 : ℕ)))
    (hc0 : ((Tube.gridScale δ (Tube.ssfGridLen δ) c : NNReal) : ENNReal) ^ (2 : ℕ) ≠ 0)
    (hnum : ENNReal.ofReal κ
        * (((Tube.volume_le.C 3 : NNReal) : ENNReal)
            * ((Tube.gridScale δ (Tube.ssfGridLen δ) k : NNReal) : ENNReal) ^ (2 : ℕ))
        * (((Tube.volume_le.C 3 : NNReal) : ENNReal)
            * ((Tube.gridScale δ (Tube.ssfGridLen δ) c : NNReal) : ENNReal) ^ (2 : ℕ))
      ≤ ENNReal.ofReal κ₀
        * (((Tube.le_volume.c 3 : NNReal) : ENNReal)
            * ((Tube.gridScale δ (Tube.ssfGridLen δ) k : NNReal) : ENNReal) ^ (2 : ℕ))
        * (((Tube.le_volume.c 3 : NNReal) : ENNReal)
            * ((Tube.gridScale δ (Tube.ssfGridLen δ) c : NNReal) : ENNReal) ^ (2 : ℕ))) :
    FillAt 𝒰 κ k c j := by
  classical
  have hrank : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have hCk : volume (𝒰.cover.tube k j).carrier
      ≤ ((Tube.volume_le.C 3 : NNReal) : ENNReal)
        * ((Tube.gridScale δ (Tube.ssfGridLen δ) k : NNReal) : ENNReal) ^ (2 : ℕ) := by
    have hvol := Tube.volume_le (E := EuclideanSpace ℝ (Fin 3))
      (Tube.gridScale_le_one hδ1 (Tube.ssfGridLen δ) k) (𝒰.cover.tube k j)
    rw [hrank] at hvol
    simpa using hvol
  have hcc : ∀ j' ∈ 𝒰.nodesUnder c k j,
      ((Tube.le_volume.c 3 : NNReal) : ENNReal)
        * ((Tube.gridScale δ (Tube.ssfGridLen δ) c : NNReal) : ENNReal) ^ (2 : ℕ)
      ≤ volume (𝒰.cover.tube c j').carrier := by
    intro j' _
    have := Tube.le_volume (E := EuclideanSpace ℝ (Fin 3)) (𝒰.cover.tube c j')
    rw [hrank] at this
    simpa using this
  refine fillAt_of_count_bridge 𝒰 hCk hcc ?_ ?_ hk0 ?_ hbridge hnum
  · exact mul_ne_zero (ENNReal.coe_ne_zero.mpr (Tube.volume_le.C_pos 3).ne') hc0
  · exact ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)
  · exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top
      (ENNReal.pow_ne_top ENNReal.coe_ne_top)) hCk

open scoped Classical in
/-- **Firing control: the factoring body's volume is the whole content.**  At `|W| = 0` the
factorization bound says nothing about the count. -/
theorem maxDensity_mul_volume_le_of_body_vacuous_at_zero
    (𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu) {c k : ℕ} {j : ι}
    (W : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) (hW : volume W.carrier = 0)
    {Cf vmax : ENNReal} :
    Kakeya.maxDensity (𝒰.nodesUnder c k j)
        (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) * volume W.carrier
      ≤ Cf * (((𝒰.nodesUnder c k j).card : ENNReal) * vmax) := by
  rw [hW, mul_zero]
  simp

end CountBridge

end Kakeya.ML2Core

end
