/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineTowerArrayFibre
public import Kakeya.MultiScaleFac.UniformBridgeKT

/-!
# The window's two upper-bound fields, each from the array that is correct for it

's **Condition R**, applied field by field.  The dividing window has two
upper-bound density clauses and one lower-bound one, and they do **not** all read the same array:

| window field | source clause | array it must use | why |
|---|---|---|---|
| `coarse_maxDensity_le` | `eqdividingKfirst` l.2695 | **fibre** | source clause is a thread cell |
| `middle_maxDensity_le` | `eqdividingKsecond` l.2697 | **containment** | an *upper* bound |
| `le_window_maxDensity` | `eqdividingKwitness` l.2700 | **fibre** | a *lower* bound |

This file supplies the first two.  The third is
`Kakeya.ML2Core.le_mul_maxDensity_nodesUnder_of_lt_towerDensityArrayFibre`.

## `coarse_maxDensity_le`: the field is about the *level family*, the source's clause about a *cell*

The Lean field bounds `Δ_max(𝒰.cover.indexSet a)` — the whole level-`a` node family — while
`eqdividingKfirst` bounds `max_{S₀ ∈ 𝕋₀} Δ_max(𝕋_a⟨S₀⟩) = Z_fib(0,a)`.  The bridge is Definition
2.1(ii) again: the thread cells *partition*, so the level family is the union of the level-`0`
cells' fibres,

  `indexSet a ⊆ (indexSet 0).biUnion (fun S₀ => assignFibre a 0 S₀)`,

`Kakeya.maxDensity_le_sum_of_subset_biUnion` turns that into a sum, and
`Kakeya.MultiScaleFac.card_parent_zero_le` caps the number of summands by the hierarchy's own `Cu`.
So the field costs **one factor `Cu`** above the source's clause and nothing else; `Cu` is `δ`-free
, so the factor is absorbed by a scale threshold and enters no exponent
account.

The inclusion needs `s.Nonempty` — an empty family has no leaves to thread — and `a ≤ ssfGridLen δ`.
It does **not** need the level-`a` nodes to be active *a priori*: activity is supplied by
`Kakeya.MultiScaleFac.coverClass_nonempty_of_mem_parent`.

## `middle_maxDensity_le`: literally `TowerGood`, unfolded

`TowerGood 𝒰 bound j a b ` is `towerDensityArray 𝒰 a b ≤ bound j a b`, i.e. a bound on
`sup_{p ∈ indexSet a} Δ_max(nodesUnder b a p)`, which is the field verbatim once the `sup` is read
at each `p`.  No constant is paid and no reading changes.  **This is the field that must NOT be
moved to the fibre**: it is an upper bound, so the containment reading is the stronger statement,
and using the fibre array here would deliver strictly less.

## Family / shading / level pair

| declaration | family / shading | level pair |
|---|---|---|
| `indexSet_subset_biUnion_assignFibre` | the tower's `s`, `T`; no shading | `(0,a)` |
| `maxDensity_indexSet_le_mul_towerDensityArrayFibre` | as above | `(0,a)` |
| `maxDensity_nodesUnder_le_of_towerGood` | as above | `(a,b)` |

## A1-a

No `GridUniformCore`; no (F)-branch interface statement is defined or altered.  The window fields
are *supplied by shape*, not restated.
-/

@[expose] public section

open scoped NNReal ENNReal
open MeasureTheory Tube

namespace Kakeya.ML2Core

section WindowFieldsFromArrays

universe u

variable {ι : Type u} {δ Cu : NNReal} {s : Finset ι}
  {T : ι → Tube δ (EuclideanSpace ℝ (Fin 3))}

open scoped Classical in
/-- **Definition 2.1(ii), the partition clause, at the top level**: every level-`a` node is a member
of the thread cell of some level-`0` cell.  The witness is any class member of the node, which
exists by `Kakeya.MultiScaleFac.coverClass_nonempty_of_mem_parent`. -/
theorem indexSet_subset_biUnion_assignFibre
    (𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu) (hs : s.Nonempty)
    {a : ℕ} (ha : a ≤ Tube.ssfGridLen δ) :
    𝒰.cover.indexSet a
      ⊆ (𝒰.cover.indexSet 0).biUnion (fun S0 => 𝒰.assignFibre a 0 S0) := by
  classical
  intro j hj
  obtain ⟨i, hi⟩ := Kakeya.MultiScaleFac.coverClass_nonempty_of_mem_parent 𝒰 ha hs hj
  simp only [coverClass, Finset.mem_filter] at hi
  obtain ⟨his, hij⟩ := hi
  refine Finset.mem_biUnion.mpr ⟨𝒰.cover.assign 0 i, 𝒰.cover.assign_mem 0 (Nat.zero_le _) i his, ?_⟩
  simp only [Tube.UniformTubeSet.assignFibre, Finset.mem_image]
  exact ⟨i, by simp [coverClass, his], hij⟩

open scoped Classical in
/-- **`coarse_maxDensity_le`'s supply** (`eqdividingKfirst`, l.2695-2696): the level-`a` family's
maximal density is at most `Cu` times the **fibre** array at `(0,a)`.

`Cu` is the hierarchy's own uniformity constant, capping the number of level-`0` cells by
`Kakeya.MultiScaleFac.card_parent_zero_le`; it is `δ`-free, so it enters no exponent account.

**Family/shading:** the tower's `s`, `T`; no shading.  **Level pair:** `(0,a)`. -/
theorem maxDensity_indexSet_le_mul_towerDensityArrayFibre
    (𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu) (hs : s.Nonempty)
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)
    {a : ℕ} (ha : a ≤ Tube.ssfGridLen δ) :
    Kakeya.maxDensity (𝒰.cover.indexSet a)
        (fun j => (𝒰.cover.tube a j).toConvexSpaceBody)
      ≤ (Cu : ENNReal) * towerDensityArrayFibre 𝒰 0 a := by
  classical
  set W : ι → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)) :=
    fun j => (𝒰.cover.tube a j).toConvexSpaceBody with hW
  calc Kakeya.maxDensity (𝒰.cover.indexSet a) W
      ≤ ∑ S0 ∈ 𝒰.cover.indexSet 0, Kakeya.maxDensity (𝒰.assignFibre a 0 S0) W :=
        Kakeya.maxDensity_le_sum_of_subset_biUnion W
          (indexSet_subset_biUnion_assignFibre 𝒰 hs ha)
    _ ≤ ∑ _S0 ∈ 𝒰.cover.indexSet 0, towerDensityArrayFibre 𝒰 0 a :=
        Finset.sum_le_sum (fun S0 hS0 =>
          Finset.le_sup (f := fun j => Kakeya.maxDensity (𝒰.assignFibre a 0 j) W) hS0)
    _ = ((𝒰.cover.indexSet 0).card : ENNReal) * towerDensityArrayFibre 𝒰 0 a := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Cu : ENNReal) * towerDensityArrayFibre 𝒰 0 a := by
        gcongr
        exact_mod_cast Kakeya.MultiScaleFac.card_parent_zero_le 𝒰 hs hball

open scoped Classical in
/-- **`middle_maxDensity_le`'s supply** (`eqdividingKsecond`, l.2697-2698): `TowerGood` on the
**containment** array is the field, once the supremum is read at each level-`a` node.

Condition R's permissive half: this clause is an **upper** bound, so `nodesUnder`
is the *stronger* reading and must be kept — supplying it from the fibre array would deliver
strictly less.

**Family/shading:** the tower's `s`, `T`; no shading.  **Level pair:** `(a,b)`. -/
theorem maxDensity_nodesUnder_le_of_towerGood
    {𝒰 : Tube.UniformTubeSet s T (Tube.ssfGridLen δ) Cu} {bound : ℕ → ℕ → ℕ → ENNReal}
    {j a b : ℕ} (h : TowerGood 𝒰 bound j a b ()) :
    ∀ p ∈ 𝒰.cover.indexSet a,
      Kakeya.maxDensity (𝒰.nodesUnder b a p)
        (fun p' => (𝒰.cover.tube b p').toConvexSpaceBody) ≤ bound j a b := by
  intro p hp
  refine le_trans ?_ h
  exact Finset.le_sup (f := fun p' => Kakeya.maxDensity (𝒰.nodesUnder b a p')
    (fun p'' => (𝒰.cover.tube b p'').toConvexSpaceBody)) hp

end WindowFieldsFromArrays

end Kakeya.ML2Core

end
