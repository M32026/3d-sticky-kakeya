/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineDensityBandFromBin
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineDefectConstantLedger
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCountFloor

/-!
# A1's data: the statistics of l.4032-4035 as **leaf-local**, family-indexed statistics

`SpineDensityBandFromBin.lean` is A1 in the abstract: it takes statistics of the shape
`D : Finset ι → ι → ENNReal`, a leaf-locality hypothesis `LeafLocalStat cell D`, brackets, and a
label.  This file supplies that data for the source's own statistics, and compiles the two facts
that a caller cannot supply by hand: **leaf-locality**, and the **node-side reading** of the band.

## Why the statistics must be family-indexed, and why `coverClass` makes it free

`Tube.coverClass v assign k = {j ∈ v | assign j = k}` already takes the family `v` as an argument.
So the thread-cell statistics are *born* in the shape `LeafLocalStat` needs — the level-`(p,c)`
density at a leaf `i`, read in the family `v`, is

  `levelDensityStat 𝒰 p c v i = Δ_max((𝕋_c⟨S_p(i)⟩ computed in v))`,

and leaf-locality is then l.4917-4918 *"depends only on the leaves of the relevant thread cell"*
**by definition of `coverClass`**, not by an argument: `leafLocal_levelDensityStat` is three lines.
That is the payoff of having stated `LeafLocalStat` over families rather than over a fixed one.

## The node-side reading — the step that connects A1's leaves to `level_density_band`'s nodes

A1 bands the statistic over **leaves**; `level_density_band` quantifies over **nodes**
`j ∈ 𝒰.cover.indexSet p`.  The bridge is that the restricted hierarchy's index set is exactly the
image of the surviving leaves — `Tube.UniformTubeSet.restrictOccupied` sets
`indexSet k := S.image (assign k)` (`SpineDefectConstantLedger.lean:387`) — and that the statistic
is constant on each `assign p`-fibre, which is leaf-locality again.  `band_over_nodes` is that
transfer, stated over any hierarchy whose index set has that shape, and
`restrictOccupied_mem_indexSet_iff` records that `restrictOccupied` has it.

## The brackets, * **lower, densities:** `one_le_levelDensityStat` — `1 ≤ Δ_max`, from `Kakeya.one_le_maxDensity`,
  needing only that the cell contains one tube of positive volume.  `C₁ = 0`: **no `δ`-power is
  spent below**, so `Λ_f`'s logarithm comes entirely from the upper bracket.  Only the shaded-mass
  statistic spends a `δ`-power below, and it spends the source's own `3η_f` (l.4030-4031).
* **upper, densities:** `levelDensityStat_le_levelCountStat` — `Δ_max ≤ #`, from
  `Kakeya.maxDensity_le_card`; the count is then bracketed by the source's `(32/ρ_k)^6` (l.4028).
* **counts:** lower `1` on a nonempty cell (`one_le_levelCountStat`), upper the same l.4028.

## Family / shading / level pair

| declaration | family / shading | level pair |
|---|---|---|
| `levelDensityStat`, `levelCountStat` | the family `v` is an **argument** | `(p,c)` |
| `leafLocal_levelDensityStat`, `leafLocal_levelCountStat` | as above | `(p,c)` |
| `one_le_levelDensityStat`, `levelDensityStat_le_levelCountStat` | as above | `(p,c)` |
| `band_over_nodes` | the restricted family `S`; no shading | `(p,c)` |
| `restrictOccupied_mem_indexSet_iff` | `S ⊆ u`; no shading | one level `k` |

**The shading changes at the refinement and nowhere else.**  Nothing in this file carries a
shading: the density and count statistics are functions of tubes and cells only.  The passage
`Z → W` happens where the source puts it — in `lem:ml2-window-refinement`'s simultaneous refinement
(l.4056-4058), i.e. in the caller that *applies* A1, not in A1's data.

## A1-a

No `GridUniformCore`; no (F)-branch interface statement is defined or altered here.
-/

@[expose] public section

open scoped NNReal ENNReal
open MeasureTheory Tube

namespace Kakeya.ML2Core

section FourStatistics

variable {ι : Type*} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {δ Cu : NNReal} {u : Finset ι} {T : ι → Tube δ E} {N : ℕ}

open scoped Classical in
/-- `Tube.coverClass` **is** the fibre filter, spelled with whatever `DecidableEq` is in scope. -/
theorem coverClass_eq_filter [DecidableEq ι] (v : Finset ι) (f : ι → ι) (k : ι) :
    coverClass v f k = {j ∈ v | f j = k} := by
  ext j
  simp [coverClass]

open scoped Classical in
/-- **The two-level maximal density at the pair `(p,c)`**, read in the family `v`: the source's
`Δ_max(𝕋_c⟨S⟩)` at the thread cell of the leaf `i`.  Family-indexed, so that leaf-locality and its
stability are expressible. -/
noncomputable def levelDensityStat (𝒰 : Tube.UniformTubeSet u T N Cu) (p c : ℕ)
    (v : Finset ι) (i : ι) : ENNReal :=
  Kakeya.maxDensity
    ((coverClass v (𝒰.cover.assign p) (𝒰.cover.assign p i)).image (𝒰.cover.assign c))
    (fun j => (𝒰.cover.tube c j).toConvexSpaceBody)

open scoped Classical in
/-- **The two-level count at the pair `(p,c)`**, read in the family `v`: the source's
`#𝕋_c⟨S⟩`. -/
noncomputable def levelCountStat (𝒰 : Tube.UniformTubeSet u T N Cu) (p c : ℕ)
    (v : Finset ι) (i : ι) : ENNReal :=
  (((coverClass v (𝒰.cover.assign p) (𝒰.cover.assign p i)).image
    (𝒰.cover.assign c)).card : ENNReal)

open scoped Classical in
/-- **Leaf-locality of the density statistic** (l.4917-4918), by definition of `coverClass`. -/
theorem leafLocal_levelDensityStat [DecidableEq ι] (𝒰 : Tube.UniformTubeSet u T N Cu) (p c : ℕ) :
    LeafLocalStat (𝒰.cover.assign p) (levelDensityStat 𝒰 p c) := by
  intro v w i h
  simp only [levelDensityStat]
  rw [coverClass_eq_filter, coverClass_eq_filter, h]

open scoped Classical in
/-- **Leaf-locality of the count statistic**, likewise. -/
theorem leafLocal_levelCountStat [DecidableEq ι] (𝒰 : Tube.UniformTubeSet u T N Cu) (p c : ℕ) :
    LeafLocalStat (𝒰.cover.assign p) (levelCountStat 𝒰 p c) := by
  intro v w i h
  simp only [levelCountStat]
  rw [coverClass_eq_filter, coverClass_eq_filter, h]

open scoped Classical in
/-- **The lower bracket for the density statistic is `1`** — `C₁ = 0`, no `δ`-power spent below.
The cell of `i` contains `i`'s own level-`c` node, and one tube of positive volume already forces
`Δ_max ≥ 1` (`Kakeya.one_le_maxDensity`). -/
theorem one_le_levelDensityStat (𝒰 : Tube.UniformTubeSet u T N Cu) (p c : ℕ)
    {v : Finset ι} {i : ι} (hi : i ∈ v)
    (hvol : 0 < volume (𝒰.cover.tube c (𝒰.cover.assign c i)).carrier) :
    1 ≤ levelDensityStat 𝒰 p c v i := by
  classical
  refine Kakeya.one_le_maxDensity ⟨𝒰.cover.assign c i, ?_, hvol⟩
  refine Finset.mem_image_of_mem _ ?_
  simp only [coverClass, Finset.mem_filter]
  exact ⟨hi, trivial⟩

open scoped Classical in
/-- **The lower bracket for the count statistic is `1`**, on a cell containing its own leaf. -/
theorem one_le_levelCountStat (𝒰 : Tube.UniformTubeSet u T N Cu) (p c : ℕ)
    {v : Finset ι} {i : ι} (hi : i ∈ v) :
    1 ≤ levelCountStat 𝒰 p c v i := by
  classical
  have hne : (𝒰.cover.assign c i) ∈
      (coverClass v (𝒰.cover.assign p) (𝒰.cover.assign p i)).image (𝒰.cover.assign c) := by
    refine Finset.mem_image_of_mem _ ?_
    simp only [coverClass, Finset.mem_filter]
    exact ⟨hi, trivial⟩
  have := Finset.card_pos.mpr ⟨_, hne⟩
  simp only [levelCountStat]
  exact_mod_cast this

open scoped Classical in
/-- **The upper bracket for the density statistic is the count** (`Kakeya.maxDensity_le_card`);
the count is then bracketed by the source's `(32/ρ_k)^6`, l.4028. -/
theorem levelDensityStat_le_levelCountStat (𝒰 : Tube.UniformTubeSet u T N Cu) (p c : ℕ)
    (v : Finset ι) (i : ι) :
    levelDensityStat 𝒰 p c v i ≤ levelCountStat 𝒰 p c v i :=
  Kakeya.maxDensity_le_card _ _

open scoped Classical in
/-- **The node-side reading**: a band over the surviving *leaves* is a band over the *nodes* of the
restricted hierarchy, because the index set is the image of the leaves and the statistic is
constant on `assign p`-fibres.  This is the shape
`Kakeya.ML2Reduction.IsKatzTaoDividingWindowLevels.level_density_band` states.

**Family/shading:** the restricted family `S`; no shading.  **Level pair:** `(p,c)`. -/
theorem band_over_nodes {S : Finset ι} (𝒱 : Tube.UniformTubeSet S T N Cu) (p c : ℕ)
    (hidx : ∀ j ∈ 𝒱.cover.indexSet p, ∃ k ∈ S, 𝒱.cover.assign p k = j)
    {Φ : ENNReal}
    (hband : ∀ k ∈ S, Φ ≤ levelDensityStat 𝒱 p c S k ∧
      levelDensityStat 𝒱 p c S k ≤ 2 * Φ) :
    ∀ j ∈ 𝒱.cover.indexSet p,
      Φ ≤ Kakeya.maxDensity (𝒱.assignFibre c p j)
          (fun j' => (𝒱.cover.tube c j').toConvexSpaceBody) ∧
        Kakeya.maxDensity (𝒱.assignFibre c p j)
          (fun j' => (𝒱.cover.tube c j').toConvexSpaceBody) ≤ 2 * Φ := by
  classical
  intro j hj
  obtain ⟨k, hk, rfl⟩ := hidx j hj
  exact hband k hk

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **`restrictOccupied` has the index-set shape `band_over_nodes` asks for**: its level-`k` nodes
are exactly the level-`k` nodes of the surviving leaves. -/
theorem restrictOccupied_mem_indexSet_iff
    (𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu) {S : Finset ι} (hS : S ⊆ u)
    (hhom : IsClassHomogeneousOn 𝒰 S) (k : ℕ) (j : ι) :
    j ∈ (𝒰.restrictOccupied hS hhom).cover.indexSet k
      ↔ ∃ i ∈ S, (𝒰.restrictOccupied hS hhom).cover.assign k i = j := by
  classical
  simp [Tube.UniformTubeSet.restrictOccupied]

end FourStatistics

end Kakeya.ML2Core

end
