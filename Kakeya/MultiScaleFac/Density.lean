/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Density
public import Kakeya.FibreCommon
public import Kakeya.Sticky
public import Kakeya.Tube.Basic
public import Kakeya.Uniform

/-!
# Reading the gap-node index and the branching product

The elementary readings of a uniform hierarchy that GWZ Lemma 7.7(A)
(`Kakeya.StickyKakeya.dividingScalesFrostman`) uses when it moves between a leaf count and the
nodes of the hierarchy.

Fix a family `T : ι → Tube δ E` indexed by `s : Finset ι`.  The *gap-node index* of
`Kakeya/FibreCommon.lean` collects the nodes of one grid level sitting inside a thickening of a
distinguished tube `T i₀`: `gapNodeIndex` for a chain bundle
`𝒰 : ChainUniformTubeSet s T N σ Cu`, `gapNodeIndexAtScale` for a single
`Tube.IsUniformAtScale s T σ Cu`.  This file records four facts about them, in matching chain and
single-scale pairs:

* `gapNodeIndex_eq_filter` / `gapNodeIndex_atScale_eq_filter` — the index is the `Finset.filter`
  its definition unfolds to, which is what lets cardinality lemmas reach it;
* `one_le_mul_branchingN` / `one_le_mul_branchingN_atScale` — a branching number is at least `1`,
  so multiplying by it never loses.

The fifth result, `card_fibre_mul_le_densityIn`, is one half of a volume band: the leaf count
weighted by the minimal `δ`-tube volume is below the density weighted by the maximal container
volume, for container scales up to `5`.

Multiplicativity itself is not here.  The statement that Frostman constants multiply along a chain
of scales is `Kakeya/MultiScaleFac/Product.lean`; the two-sided bracket between a fibre density and
a fibre cardinality is `Kakeya.MultiScaleFac.densityIn_fibre_mul_le_card` together with
`Kakeya.MultiScaleFac.card_mul_le_densityIn_fibre`, both in `Kakeya/FibreCommon.lean`.
-/

@[expose] public section

open MeasureTheory Real Metric
open Tube

namespace Kakeya

open StickyKakeya

namespace MultiScaleFac

universe u

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

variable {ι : Type*} {δ : NNReal} {s : Finset ι} {T : ι → Tube δ E} {Cu : NNReal}

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
theorem gapNodeIndex_eq_filter {N : ℕ} {σ : ℕ → NNReal} (𝒰 : ChainUniformTubeSet s T N σ Cu)
    (k : ℕ) (i₀ : ι) (θ : NNReal) :
    gapNodeIndex 𝒰 k i₀ θ =
      (𝒰.cover.indexSet k).filter (fun j =>
        (𝒰.cover.tube k j).toConvexSpaceBody ≤ ((T i₀).rescale θ).toConvexSpaceBody) := by
  classical
  simp only [gapNodeIndex, Kakeya.familyIn]

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
theorem one_le_mul_branchingN {N : ℕ} {σ : ℕ → NNReal} (𝒰 : ChainUniformTubeSet s T N σ Cu)
    (hCu : 1 ≤ Cu) {k : ℕ} (hk : k ≤ N) {i₀ : ι} (hi₀ : i₀ ∈ s) :
    1 ≤ Cu ^ 2 * 𝒰.branchingN k := by
  obtain ⟨j, hj, hle⟩ := (𝒰.uniformAt hCu hk).exists_le_rescale hi₀
  refine le_trans ?_ ((𝒰.uniformAt hCu hk).card_filter_le hj)
  exact_mod_cast Finset.one_le_card.mpr ⟨i₀, Finset.mem_filter.mpr ⟨hi₀, hle⟩⟩

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- The per-scale form of `gapNodeIndex_eq_filter`, kept because its consumers hold uniformity at
a single real scale and cannot supply a `ChainUniformTubeSet` bundle. -/
theorem gapNodeIndex_atScale_eq_filter {σ : NNReal} (h : Tube.IsUniformAtScale s T σ Cu)
    (i₀ : ι) (θ : NNReal) :
    gapNodeIndexAtScale h i₀ θ =
      h.parent.filter (fun j =>
        (h.parentTube j).toConvexSpaceBody ≤ ((T i₀).rescale θ).toConvexSpaceBody) := by
  classical
  simp only [gapNodeIndexAtScale, Kakeya.familyIn]

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- The per-scale form of `one_le_mul_branchingN`, kept because its consumers hold uniformity at
a single real scale and cannot supply a `ChainUniformTubeSet` bundle. -/
theorem one_le_mul_branchingN_atScale {σ : NNReal} (h : Tube.IsUniformAtScale s T σ Cu)
    {i₀ : ι} (hi₀ : i₀ ∈ s) : 1 ≤ Cu * h.branchingN := by
  obtain ⟨j, hj, hle⟩ := h.exists_le_rescale hi₀
  refine le_trans ?_ (h.card_filter_le hj)
  exact_mod_cast Finset.one_le_card.mpr ⟨i₀, Finset.mem_filter.mpr ⟨hi₀, hle⟩⟩

/-- Band for the full family, lower form: the leaf count weighted by the minimal `δ`-tube volume
is dominated by the density weighted by the maximal container volume, for container scales up
to `5`. -/
theorem card_fibre_mul_le_densityIn {θ : NNReal} (hθ : θ ≤ 5) (i₀ : ι) :
    ((fibreIndex s T δ θ i₀).card : ENNReal)
        * (((Tube.le_volume.c (Module.finrank ℝ E) : NNReal) : ENNReal)
            * ((δ : ENNReal) ^ (Module.finrank ℝ E - 1)))
      ≤ Kakeya.densityIn s (fun i => (T i).toConvexSpaceBody)
            ((T i₀).rescale θ).toConvexSpaceBody
          * ((((6 : NNReal) * Tube.volume_le.C (Module.finrank ℝ E) : NNReal) : ENNReal)
              * ((θ : ENNReal) ^ (Module.finrank ℝ E - 1))) := by
  rw [show fibreIndex s T δ θ i₀ = Kakeya.familyIn s (fun i => (T i).toConvexSpaceBody)
      ((T i₀).rescale θ).toConvexSpaceBody from by simp [fibreIndex, fibreBodies_self]]
  refine le_densityIn_mul_of_volume_band s (fun i => (T i).toConvexSpaceBody)
    ((T i₀).rescale θ).toConvexSpaceBody (fun i _ => ?_) ?_
  · simpa using Tube.le_volume (T i)
  · refine (Tube.volume_le_of_le hθ ((T i₀).rescale θ)).trans ?_
    have hconst : ((2 : NNReal) ^ Module.finrank ℝ E * (1 + 5) : NNReal)
        ≤ 6 * Tube.volume_le.C (Module.finrank ℝ E) := by
      unfold Tube.volume_le.C
      rw [pow_succ]
      calc (2 : NNReal) ^ Module.finrank ℝ E * (1 + 5)
          = 6 * 2 ^ Module.finrank ℝ E := by ring
        _ ≤ 6 * (2 ^ Module.finrank ℝ E * 2) := by
            gcongr
            exact le_mul_of_one_le_right zero_le one_le_two
    refine (ENNReal.coe_le_coe.mpr (mul_le_mul_left hconst
      (θ ^ (Module.finrank ℝ E - 1)))).trans ?_
    push_cast
    ring_nf
    exact le_refl _

end MultiScaleFac

end Kakeya
