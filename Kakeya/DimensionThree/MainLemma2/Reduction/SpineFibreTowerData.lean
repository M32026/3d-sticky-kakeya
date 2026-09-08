/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFibreSupplyClosure

/-!
# The tower rows, produced from the block's data

`NEXT`'s items 1, 2, 4 closed; item 3 measured.  Every row that this run can reach from the
tower's own fields is now reached; `hfill` is the single named hypothesis left, with the
measurement below.

## 2. `hGood` (l.2683-2684) — from the block's node-level density row, not from a count

My previous reduction to `#s ≤ δ^{-η₀}` was the wrong one, as flagged: a cardinality row is
neither needed nor available at `η₀`.  The right one is one line:

> `assignFibre L 0 j ⊆ indexSet L` (`assignFibre_subset_indexSet`, existing) and
> `Kakeya.maxDensity_mono` give `Z_fib(0,L) ≤ Δ_max(indexSet L)`.

So `hGood_of_maxDensity_indexSet` reduces the top-cell estimate to the **maximal density of the
tower's finest node family**, and `hGood_of_everyScale` reads that off
`Tube.UniformTubeSet.IsKatzTaoAtEveryScale A` at `k = L` — i.e. off the block's standing
`Δ_max(𝕋) ≤ δ^{-η₀}` row (l.5814, l.4348) transported to nodes.  What the caller supplies is the
exponent relation `A ≤ (ρ₀/ρ_L)^{η₁} = δ^{-η₁}`, i.e. `η_in ≤ η₁` in the tree's ladder; that is a
scalar comparison of two exponents and nothing else.

## 1. Per-cell cardinality (l.2679-2681) — it is the tower's branching row

`assignFibre c p j` is the image under `assign c` of the level-`p` **class** of `j`, so
`card_assignFibre_le_mul_branchingN` bounds it by `Cu · branchingN p` using
`UniformTubeSet.card_class_le` — Definition 2.1(iii), a *field of the tower*.  Hence
`hcrude_of_branchingN`: the source's `#𝕋_l⟨S⟩ ≤ D(ρ_k/ρ_l)^4` is exactly the statement that the
tower's branching numbers obey the crude Katz-Tao count.

**Which field it consumes, on the record.**  This route consumes `card_class_le` (2.1(iii)) and
**not** essential distinctness: a bare `UniformTubeSet` carries no ED hypothesis, and the existing
ED-based count `Kakeya.ML2Assembly.card_le_rpow_neg_four` is the `k = 0`, whole-family instance —
it runs through `Tube.card_le_of_densityIn_le` in the **unit ball** and needs a *density* input
(`maxDensity ≤ δ^{-η}` with `η ≤ 1`), so it does not localise to a level-`p` cell without a
per-cell density bound, which is what the run is trying to prove.  The per-cell count is therefore
supplied either by the block's branching data on `refinedHierarchy`'s `UniformTubeSet`, or by an
ED row that the tower would have to carry; `card_assignFibre_le_mul_branchingN` is the bridge to the first.

## 4. `le_window_maxDensity` — body and volume floor both produced

`rescale_le_rescale_of_mem_nodesUnder` produces the containing body: a level-`b` node under the
level-`a` node `j`, rescaled to `ρ`, lies in `T_a(j)` **rescaled to `1 + ρ_a + ρ`**.  The proof is
the two-midpoint estimate — `Tube.carrier_subset_closedBall_midpoint` at both scales, the fine
node's midpoint inside `T_a(j)` because the core lies in the tube (`segment_subset_carrier`), and
`closedBall_midpoint_subset_rescale` to land back in a tube body.  Its volume is positive and
finite by `Tube.le_volume`/`Tube.volume_le_of_le`, and the per-tube floor `c₃ρ²` is `Tube.le_volume`
at the window radius.

So `window_field_of_numeric` produces `le_window_maxDensity` from **one explicit numerical
inequality** with every term concrete:
`(ρ_a/ρ)^{η_{m+1}} · |T_a(j)^{(1+ρ_a+ρ)}| ≤ C* · #(nodesUnder b a j) · c₃ρ²`.
No body row, no volume row, and the count is still not fed circularly.

## 3. `hfill` — measured, and the shapes do not match

* **`FillAt 𝒰 κ k c j`** is `κ · Δ_max(𝕋_c[T_k]) ≤ Δ(𝕋_c[T_k], T_k)`: inside **one** cell, the
  node's own tube must be a `κ`-almost-maximiser of the level-`c` node family's density.  It
  mentions **no shading**.
* **The source's l.4030-4031 clause** is `λ(𝕊',Z) ≥ δ^{3η_f}` — the **family's shading fullness**,
  a statement about `|Z(T)|/|T|` for the retained tubes.

These constrain different objects, so family fullness cannot imply `FillAt`, at any loss: fullness
says the shading fills the tubes, `FillAt` says the node tube is where the *node-family* density is
attained.  Adding the two-level band does not close the gap either: `level_density_band` and
`le_level_maxDensity` compare densities **across cells** (they band `Δ_max(𝕋_c⟨S⟩)` as `S` varies),
and give no information about **which test body** attains the supremum inside a fixed cell —
`Kakeya.maxDensity` is a supremum over all convex bodies, and the existing file
`SpineFloorShapeNoFill.lean` exhibits configurations where the supremum is attained on a clump
far smaller than the node.

So it is a genuine
statement about the **location of the maximiser**, and either the existing `FloorHypothesisAt` is
stronger than the source's floor at this clause, or the source's floor is being read through a
different quantity. That is a shape question about the existing floor hypothesis, not a gap in the
dividing-scales run.

## Family / shading / level pair

| declaration | family / shading | level pair |
|---|---|---|
| `hGood_of_maxDensity_indexSet`, `hGood_of_everyScale` | the tower; no shading | `(0,L)` |
| `card_assignFibre_le_mul_branchingN`, `hcrude_of_branchingN` | the tower; no shading | `(p,c)` |
| `closedBall_midpoint_subset_rescale`, `segment_subset_carrier` | none — tube geometry | none |
| `rescale_le_rescale_of_mem_nodesUnder`, `window_field_of_numeric` | the tower | `(a,b)` at `ρ` |

## A1-a

No `GridUniformCore`; no `(F)`-branch interface statement is defined or altered.
-/

@[expose] public section

open scoped NNReal ENNReal
open MeasureTheory Tube

namespace Kakeya.ML2Core

section TowerRows

universe u

variable {ι : Type u} {δ Cu : NNReal} {s : Finset ι}
  {T : ι → Tube δ (EuclideanSpace ℝ (Fin 3))}

open scoped Classical in
/-- **`hGood` from the tower's node-level density row.** -/
theorem hGood_of_maxDensity_indexSet
    (𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu) {A : ENNReal}
    (hmax : Kakeya.maxDensity (𝒰.cover.indexSet (Tube.ssfGridLen δ))
      (fun j => (𝒰.cover.tube (Tube.ssfGridLen δ) j).toConvexSpaceBody) ≤ A) :
    towerDensityArrayFibre 𝒰 0 (Tube.ssfGridLen δ) ≤ A := by
  classical
  refine Finset.sup_le fun j _ => le_trans (Kakeya.maxDensity_mono _ ?_) hmax
  exact assignFibre_subset_indexSet 𝒰 le_rfl j

open scoped Classical in
/-- **`hGood` from `IsKatzTaoAtEveryScale`.** -/
theorem hGood_of_everyScale (𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu) {A : ENNReal}
    (hKT : 𝒰.IsKatzTaoAtEveryScale A) :
    towerDensityArrayFibre 𝒰 0 (Tube.ssfGridLen δ) ≤ A :=
  hGood_of_maxDensity_indexSet 𝒰 (hKT (Tube.ssfGridLen δ) le_rfl)

open scoped Classical in
/-- **The per-cell count is the tower's own branching row.** -/
theorem card_assignFibre_le_mul_branchingN
    (𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu) {p c : ℕ}
    (hp : p ≤ Tube.ssfGridLen δ) {j : ι} (hj : j ∈ 𝒰.cover.indexSet p) :
    ((𝒰.assignFibre c p j).card : NNReal) ≤ Cu * 𝒰.branchingN p := by
  classical
  refine le_trans ?_ (𝒰.card_class_le p hp j hj)
  exact_mod_cast Finset.card_image_le

open scoped Classical in
/-- **`hcrude` from the tower's branching numbers.** -/
theorem hcrude_of_branchingN (𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu)
    {D : ENNReal}
    (hbr : ∀ p c : ℕ, p ≤ c → c ≤ Tube.ssfGridLen δ →
      ((Cu * 𝒰.branchingN p : NNReal) : ENNReal) ≤ D * ENNReal.ofReal
        (((Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ)
          / (Tube.gridScale δ (Tube.ssfGridLen δ) c : ℝ)) ^ (4 : ℕ))) :
    ∀ p c : ℕ, p ≤ c → c ≤ Tube.ssfGridLen δ →
      towerDensityArrayFibre 𝒰 p c ≤ D * ENNReal.ofReal
        (((Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ)
          / (Tube.gridScale δ (Tube.ssfGridLen δ) c : ℝ)) ^ (4 : ℕ)) := by
  classical
  intro p c hpc hc
  refine hcrude_of_cardEstimate 𝒰 (fun p' c' hp'c' hc' j hj => ?_) p c hpc hc
  refine le_trans ?_ (hbr p' c' hp'c' hc')
  exact_mod_cast card_assignFibre_le_mul_branchingN 𝒰 (hp'c'.trans hc') hj

end TowerRows

section WindowBall

universe u

variable {ι : Type u} {δ Cu : NNReal} {s : Finset ι}
  {T : ι → Tube δ (EuclideanSpace ℝ (Fin 3))}

open Metric in
/-- The closed ball about a tube's core midpoint, at any radius, sits inside the tube rescaled to
that radius. -/
theorem closedBall_midpoint_subset_rescale {ρ : NNReal}
    (V : Tube δ (EuclideanSpace ℝ (Fin 3))) :
    Metric.closedBall (midpoint ℝ V.x V.y) (ρ : ℝ) ⊆ (V.rescale ρ).carrier := by
  rw [Tube.rescale, Tube.mk', Tube.carrier_eq]
  exact Set.subset_iUnion₂_of_subset (midpoint ℝ V.x V.y) (midpoint_mem_segment _ _) subset_rfl

open Metric in
/-- A tube's core segment lies in the tube. -/
theorem segment_subset_carrier (V : Tube δ (EuclideanSpace ℝ (Fin 3))) :
    segment ℝ V.x V.y ⊆ V.carrier := by
  rw [V.carrier_eq]
  exact fun z hz => Set.mem_iUnion₂_of_mem hz (Metric.mem_closedBall_self (by positivity))

open scoped Classical in
open Metric in
/-- **The window's containing body, produced**: every level-`b` node under a level-`a` node,
rescaled to `ρ`, sits inside the level-`a` node's own tube rescaled to `1 + ρ_a + ρ`. -/
theorem rescale_le_rescale_of_mem_nodesUnder
    (𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu) {a b : ℕ} {j : ι} {ρ : NNReal}
    {j' : ι} (hj' : j' ∈ 𝒰.nodesUnder b a j) :
    ((𝒰.cover.tube b j').rescale ρ).toConvexSpaceBody
      ≤ ((𝒰.cover.tube a j).rescale
          (1 + Tube.gridScale δ (Tube.ssfGridLen δ) a + ρ)).toConvexSpaceBody := by
  classical
  rw [Tube.UniformTubeSet.nodesUnder_eq_nodesIn, Tube.UniformTubeSet.mem_nodesIn_iff] at hj'
  set Va := 𝒰.cover.tube a j with hVa
  set Vb := 𝒰.cover.tube b j' with hVb
  have hsub : Vb.carrier ⊆ Va.carrier := by
    have h2 := hj'.2
    rw [← SetLike.coe_subset_coe] at h2
    exact h2
  have hmidb : midpoint ℝ Vb.x Vb.y ∈ Va.carrier :=
    hsub (segment_subset_carrier Vb (midpoint_mem_segment _ _))
  have hballa : Va.carrier
      ⊆ Metric.closedBall (midpoint ℝ Va.x Va.y)
          (1 / 2 + (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) :=
    Tube.carrier_subset_closedBall_midpoint (E := EuclideanSpace ℝ (Fin 3)) Va
  have hd : dist (midpoint ℝ Vb.x Vb.y) (midpoint ℝ Va.x Va.y)
      ≤ 1 / 2 + (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ) :=
    Metric.mem_closedBall.mp (hballa hmidb)
  rw [← SetLike.coe_subset_coe]
  intro p hp
  have hp' : p ∈ Metric.closedBall (midpoint ℝ Vb.x Vb.y) (1 / 2 + (ρ : ℝ)) := by
    have := Tube.carrier_subset_closedBall_midpoint (E := EuclideanSpace ℝ (Fin 3))
      (Vb.rescale ρ) hp
    simpa [Tube.rescale, Tube.mk'] using this
  have hdist : dist p (midpoint ℝ Va.x Va.y)
      ≤ ((1 : ℝ) + (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ) + (ρ : ℝ)) := by
    have h1 : dist p (midpoint ℝ Vb.x Vb.y) ≤ 1 / 2 + (ρ : ℝ) := Metric.mem_closedBall.mp hp'
    have := dist_triangle p (midpoint ℝ Vb.x Vb.y) (midpoint ℝ Va.x Va.y)
    linarith
  refine closedBall_midpoint_subset_rescale (ρ := 1 + Tube.gridScale δ (Tube.ssfGridLen δ) a + ρ)
    Va ?_
  refine Metric.mem_closedBall.mpr ?_
  push_cast
  exact hdist

open scoped Classical in
/-- **`le_window_maxDensity` with the body AND the volume floor produced.** -/
theorem window_field_of_numeric (𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu)
    {Cstar : ENNReal} {η : ℕ → ℝ} {εd : ℝ} {a b m : ℕ}
    (hnum : ∀ ρ : NNReal,
      (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
          * ((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
            / (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)) ^ εd ≤ (ρ : ℝ) →
      (ρ : ℝ) ≤ (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
          * ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
            / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ εd →
      ∀ j ∈ 𝒰.cover.indexSet a,
        ENNReal.ofReal
            (((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ) / (ρ : ℝ)) ^ η (m + 1))
            * volume ((𝒰.cover.tube a j).rescale
                (1 + Tube.gridScale δ (Tube.ssfGridLen δ) a + ρ)).carrier
          ≤ Cstar * (((𝒰.nodesUnder b a j).card : ENNReal)
              * (((Tube.le_volume.c 3 : NNReal) : ENNReal)
                  * ((ρ : NNReal) : ENNReal) ^ (2 : ℕ)))) :
    ∀ ρ : NNReal,
      (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
          * ((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
            / (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)) ^ εd ≤ (ρ : ℝ) →
      (ρ : ℝ) ≤ (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
          * ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
            / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ εd →
      ∀ j ∈ 𝒰.cover.indexSet a,
        ENNReal.ofReal (((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ) / (ρ : ℝ)) ^ η (m + 1))
          ≤ Cstar * Kakeya.maxDensity (𝒰.nodesUnder b a j)
              (fun j' => ((𝒰.cover.tube b j').rescale ρ).toConvexSpaceBody) := by
  classical
  have hrank : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  refine window_field_of_body 𝒰 (fun ρ h1 h2 j hj => ?_)
  set r : NNReal := 1 + Tube.gridScale δ (Tube.ssfGridLen δ) a + ρ with hr
  have hr1 : (1 : NNReal) ≤ r := by
    rw [hr]; exact le_add_right (le_add_right le_rfl)
  have hvpos : (0 : ENNReal) < volume ((𝒰.cover.tube a j).rescale r).carrier := by
    refine lt_of_lt_of_le ?_ (Tube.le_volume (E := EuclideanSpace ℝ (Fin 3))
      ((𝒰.cover.tube a j).rescale r))
    rw [hrank]
    have : (0 : ENNReal) < ((Tube.le_volume.c 3 : NNReal) : ENNReal) :=
      ENNReal.coe_pos.mpr (Tube.le_volume.c_pos 3)
    have hrpos : (0 : ENNReal) < ((r : NNReal) : ENNReal) ^ (3 - 1) := by
      refine ENNReal.pow_pos ?_ _
      exact_mod_cast lt_of_lt_of_le zero_lt_one hr1
    exact ENNReal.mul_pos this.ne' hrpos.ne'
  have hvtop : volume ((𝒰.cover.tube a j).rescale r).carrier ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (Tube.volume_le_of_le (le_refl r)
      ((𝒰.cover.tube a j).rescale r))
    exact ENNReal.coe_ne_top
  exact ⟨((𝒰.cover.tube a j).rescale r).toConvexSpaceBody, hvpos.ne', hvtop,
    fun j' hj' => rescale_le_rescale_of_mem_nodesUnder 𝒰 hj', hnum ρ h1 h2 j hj⟩

end WindowBall

section Controls

universe u

variable {ι : Type u} {δ Cu : NNReal} {s : Finset ι}
  {T : ι → Tube δ (EuclideanSpace ℝ (Fin 3))}

open scoped Classical in
/-- **Firing control: the every-scale route to `hGood` is not vacuous.**  Read at `A = 0` it forces
the array to vanish, so the exponent in the block's density row is load-bearing. -/
theorem hGood_of_everyScale_vacuous_at_zero
    (𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu)
    (hKT : 𝒰.IsKatzTaoAtEveryScale 0) :
    towerDensityArrayFibre 𝒰 0 (Tube.ssfGridLen δ) = 0 :=
  nonpos_iff_eq_zero.mp (hGood_of_everyScale 𝒰 hKT)

open scoped Classical in
/-- **Firing control: the branching row is load-bearing in `hcrude_of_branchingN`.**  At
`branchingN p = 0` the tower's own `card_class_le` forces every level-`p` class empty, hence every
thread cell empty. -/
theorem card_assignFibre_eq_zero_of_branchingN_zero
    (𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu) {p c : ℕ}
    (hp : p ≤ Tube.ssfGridLen δ) {j : ι} (hj : j ∈ 𝒰.cover.indexSet p)
    (hbr : 𝒰.branchingN p = 0) : (𝒰.assignFibre c p j).card = 0 := by
  have h := card_assignFibre_le_mul_branchingN (c := c) 𝒰 hp hj
  rw [hbr, mul_zero, nonpos_iff_eq_zero] at h
  exact_mod_cast h

end Controls

end Kakeya.ML2Core

end
