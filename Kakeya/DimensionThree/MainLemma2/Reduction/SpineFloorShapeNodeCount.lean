/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.FibreCommon

/-!
# `R6b` — how many nodes of a fine level fit inside one node of a coarse level

  `R6` (*"the genuine parent precedes the whole middle window"*) is a
competition between a **polynomial** lower bound on the level-`m₀` maximal density, supplied by the
window twin's `le_level_maxDensity`, and a **subpolynomial** upper bound on the branching across a
few grid steps.  This file supplies the upper bound.

> `#(𝒰.nodesUnder c k j) ≤ 2 · 25^{2n} · (4ρ_k/ρ_c)^{2n} · Cu`.

**The exponent is `2n`, and it is not negotiable.**  A `ρ`-tube of unit length contains `≍(ρ/σ)²`
*translates* **times** `≍(ρ/σ)²` *directions* of `σ`-tubes, so the volumetric `(ρ/σ)²` is **false**
for nodes.  Recorded here so that nobody "simplifies" the exponent later: the whole argument of `R6`
survives any fixed exponent — one grid step is `δ^{-1/N}` with `N = Tube.ssfGridLen δ → ∞`, so
`2n/N → 0` — but a `(ρ/σ)²` node count would be a false lemma.

## The bridge, in five steps

1. `Kakeya.MultiScaleFac.coverClass_nonempty_of_mem_parent` picks a member `i₀` of the coarse node
   (both halves of the branching bracket are used there, which is why the family must be nonempty).
2. `Tube.rescale_le_of_le` puts the coarse **node** inside the `4ρ_k`-thickening of `i₀` — the
   tree's own factor-`4` hop, the one `Kakeya.MultiScaleFac.coverClass_subset_fibreIndex` performs.
3. `Kakeya.MultiScaleFac.exists_gapFibre_cover_of_ratio` covers that thickening by at most
   `2 · 25^{2n} · (4ρ_k/ρ_c)^{2n}` tight `ρ_c`-fibres.
4. `Tube.UniformTubeSet.boundedOverlap`, **read at level `c`** with the test body
   `(T i₂).rescale ρ_c` (a genuine `Tube.gridScale δ N c`-tube), caps at `Cu` the level-`c` nodes
   that each fibre accounts for.
5. `Finset.card_biUnion_le` multiplies the two.

**Rejected supplier, recorded.**  `Tube.essDistinctTubesInSelfDilate` and
`Tube.essDistinctTubesInDilate` both require the counted family to be *pairwise essentially
distinct*, which the nodes of a `Tube.UniformTubeSet` are **not**: `boundedOverlap` is Definition
2.1(ii)'s deliberate replacement for pairwise-ED, *"which is unsatisfiable while preserving
cardinality"*.  Citing either for nodes would be a hypothesis the tree cannot supply.

## Two side conditions that are real

* **`2δ ≤ ρ_c`** — `exists_gapFibre_cover_of_ratio`'s `2σ ≤ ρ` at `σ := δ`.  It **fails** at the
  finest level `c = N`, where `ρ_N = δ`.  `R6` only ever needs `c = m₀ < N`, so it is discharged at
  the call site, but it cannot be dropped.
* **`ρ_c ≤ 4ρ_k`** — free whenever `k ≤ c`, since the grid scales decrease.

## A correction to, recorded

That section gives `C_ess := 2 · 25^{2n} · Cu`.  **The factor `4^{2n}` from step 2 is missing**: the
container that step 3 must cover is the `4ρ_k`-thickening, not the node, so the honest constant is
`2 · 25^{2n} · 4^{2n} · Cu = 2 · 100^{2n} · Cu` in the `(ρ_k/ρ_c)^{2n}` normalisation
(`Kakeya.ML2Core.card_nodesUnder_le_coverCount'` below).  `R6` is unaffected — a polynomial beats a
subpolynomial at any fixed constant — but a bound stated at `25^{2n}` against `(ρ_k/ρ_c)^{2n}` would
not be provable.
-/

@[expose] public section

open MeasureTheory Metric ConvexSpaceBody
open Tube
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

section NodeCount

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {Cu : NNReal}

open scoped Classical in
/-- **`R6b`.**  The level-`c` nodes inside one level-`k` node number at most
`2 · 25^{2n} · (4ρ_k/ρ_c)^{2n} · Cu`.  See the module docstring for the five steps and for why the
exponent is `2n` and not `2`. -/
theorem card_nodesUnder_le_coverCount (𝒰 : Tube.UniformTubeSet s T N Cu) (hs : s.Nonempty)
    {k c : ℕ} (hk : k ≤ N) (hc : c ≤ N)
    (hρc : 0 < Tube.gridScale δ N c)
    (h2δ : 2 * δ ≤ Tube.gridScale δ N c)
    (hle : Tube.gridScale δ N c ≤ 4 * Tube.gridScale δ N k)
    {j : ι} (hj : j ∈ 𝒰.cover.indexSet k) :
    ((𝒰.nodesUnder c k j).card : ℝ)
      ≤ 2 * (25 : ℝ) ^ (2 * Module.finrank ℝ E)
          * (((4 * Tube.gridScale δ N k : NNReal) : ℝ)
              / ((Tube.gridScale δ N c : NNReal) : ℝ)) ^ (2 * Module.finrank ℝ E)
        * (Cu : ℝ) := by
  classical
  -- 1. an anchor member of the coarse node
  obtain ⟨i₀, hi₀⟩ := Kakeya.MultiScaleFac.coverClass_nonempty_of_mem_parent 𝒰 hk hs hj
  simp only [Tube.coverClass, Finset.mem_filter] at hi₀
  obtain ⟨hi₀s, hi₀j⟩ := hi₀
  -- 2. the coarse node sits inside the `4ρ_k`-thickening of the anchor
  have hnode : (𝒰.cover.tube k j).toConvexSpaceBody
      ≤ ((T i₀).rescale (4 * Tube.gridScale δ N k)).toConvexSpaceBody := by
    have h := Tube.rescale_le_of_le (T i₀) (𝒰.cover.tube k (𝒰.cover.assign k i₀))
      (𝒰.cover.le_tube_assign k hk i₀ hi₀s)
    rwa [hi₀j] at h
  -- 3. the fibre cover of that thickening by tight `ρ_c`-fibres
  obtain ⟨A, hAs, hAcard, hAcov⟩ :=
    Kakeya.MultiScaleFac.exists_gapFibre_cover_of_ratio (E := E) (s := s) (T := T)
      hρc le_rfl h2δ hle i₀
  -- 4. each covering fibre accounts for at most `Cu` level-`c` nodes
  set B : ι → Finset ι := fun i₂ => (𝒰.cover.indexSet c).filter (fun j' => ∃ i ∈ s,
      (T i).toConvexSpaceBody ≤ (𝒰.cover.tube c j').toConvexSpaceBody ∧
      (T i).toConvexSpaceBody
        ≤ ((T i₂).rescale (Tube.gridScale δ N c)).toConvexSpaceBody) with hBdef
  have hBcard : ∀ i₂ ∈ A, ((B i₂).card : ℝ) ≤ (Cu : ℝ) := by
    intro i₂ _
    have := 𝒰.boundedOverlap c hc ((T i₂).rescale (Tube.gridScale δ N c))
    exact_mod_cast this
  -- the nodes are distributed among the fibres
  have hsub : 𝒰.nodesUnder c k j ⊆ A.biUnion B := by
    intro j' hj'
    rw [Tube.UniformTubeSet.nodesUnder_eq_nodesIn, Tube.UniformTubeSet.mem_nodesIn_iff] at hj'
    obtain ⟨hj'idx, hj'le⟩ := hj'
    obtain ⟨i₁, hi₁⟩ := Kakeya.MultiScaleFac.coverClass_nonempty_of_mem_parent 𝒰 hc hs hj'idx
    simp only [Tube.coverClass, Finset.mem_filter] at hi₁
    obtain ⟨hi₁s, hi₁j⟩ := hi₁
    have hmem1 : (T i₁).toConvexSpaceBody ≤ (𝒰.cover.tube c j').toConvexSpaceBody := by
      have h := 𝒰.cover.le_tube_assign c hc i₁ hi₁s
      rwa [hi₁j] at h
    have hin : i₁ ∈ Kakeya.StickyKakeya.fibreIndex s T δ (4 * Tube.gridScale δ N k) i₀ := by
      rw [Kakeya.StickyKakeya.fibreIndex_self]
      exact Finset.mem_filter.mpr ⟨hi₁s, hmem1.trans (hj'le.trans hnode)⟩
    obtain ⟨i₂, hi₂A, hi₂⟩ := hAcov i₁ hin
    rw [Kakeya.StickyKakeya.fibreIndex_self, Finset.mem_filter] at hi₂
    refine Finset.mem_biUnion.mpr ⟨i₂, hi₂A, ?_⟩
    exact Finset.mem_filter.mpr ⟨hj'idx, i₁, hi₁s, hmem1, hi₂.2⟩
  -- 5. multiply
  have hstep : ((𝒰.nodesUnder c k j).card : ℝ) ≤ (A.card : ℝ) * (Cu : ℝ) := by
    have h1 : ((𝒰.nodesUnder c k j).card : ℝ) ≤ ((A.biUnion B).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have h2 : ((A.biUnion B).card : ℝ) ≤ ∑ i₂ ∈ A, ((B i₂).card : ℝ) := by
      have := Finset.card_biUnion_le (s := A) (t := B)
      calc ((A.biUnion B).card : ℝ) ≤ ((∑ i₂ ∈ A, (B i₂).card : ℕ) : ℝ) := by exact_mod_cast this
        _ = ∑ i₂ ∈ A, ((B i₂).card : ℝ) := by push_cast; ring
    have h3 : ∑ i₂ ∈ A, ((B i₂).card : ℝ) ≤ (A.card : ℝ) * (Cu : ℝ) := by
      calc ∑ i₂ ∈ A, ((B i₂).card : ℝ) ≤ ∑ _i₂ ∈ A, (Cu : ℝ) := Finset.sum_le_sum hBcard
        _ = (A.card : ℝ) * (Cu : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
    exact h1.trans (h2.trans h3)
  refine hstep.trans ?_
  have hCu : (0 : ℝ) ≤ (Cu : ℝ) := NNReal.coe_nonneg _
  exact mul_le_mul_of_nonneg_right hAcard hCu

open scoped Classical in
/-- **`R6b`, in the normalisation `R6` uses.**  `4^{2n}` is pulled out of the ratio, giving the
honest `C_ess = 2 · 100^{2n} · Cu`. -/
theorem card_nodesUnder_le_coverCount' (𝒰 : Tube.UniformTubeSet s T N Cu) (hs : s.Nonempty)
    {k c : ℕ} (hk : k ≤ N) (hc : c ≤ N)
    (hρc : 0 < Tube.gridScale δ N c)
    (h2δ : 2 * δ ≤ Tube.gridScale δ N c)
    (hle : Tube.gridScale δ N c ≤ 4 * Tube.gridScale δ N k)
    {j : ι} (hj : j ∈ 𝒰.cover.indexSet k) :
    ((𝒰.nodesUnder c k j).card : ℝ)
      ≤ 2 * (100 : ℝ) ^ (2 * Module.finrank ℝ E) * (Cu : ℝ)
        * (((Tube.gridScale δ N k : NNReal) : ℝ)
            / ((Tube.gridScale δ N c : NNReal) : ℝ)) ^ (2 * Module.finrank ℝ E) := by
  refine (card_nodesUnder_le_coverCount 𝒰 hs hk hc hρc h2δ hle hj).trans (le_of_eq ?_)
  have hsplit : (((4 * Tube.gridScale δ N k : NNReal) : ℝ)
        / ((Tube.gridScale δ N c : NNReal) : ℝ)) ^ (2 * Module.finrank ℝ E)
      = (4 : ℝ) ^ (2 * Module.finrank ℝ E)
        * (((Tube.gridScale δ N k : NNReal) : ℝ)
            / ((Tube.gridScale δ N c : NNReal) : ℝ)) ^ (2 * Module.finrank ℝ E) := by
    rw [← mul_pow]
    congr 1
    push_cast
    ring
  rw [hsplit]
  have h100 : (100 : ℝ) ^ (2 * Module.finrank ℝ E)
      = (25 : ℝ) ^ (2 * Module.finrank ℝ E) * (4 : ℝ) ^ (2 * Module.finrank ℝ E) := by
    rw [← mul_pow]; norm_num
  rw [h100]
  ring

end NodeCount

end Kakeya.ML2Core
