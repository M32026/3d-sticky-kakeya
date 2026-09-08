/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFourFactorLedger
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCoarseFibreBracket

/-!
# R0c: the third `exists_spineOneScale` application — the four-way split's product

 measured that the two-scale split is
`Kakeya.ML2Reduction.exists_spineOneScale` applied **twice**
(`Kakeya.ML2Reduction.exists_spineTwoScale`), and that the three-scale split is *the same lemma a
third time*.  This file is that third application, and the map was right: there is no new
estimate, and the proof is `exists_spineTwoScale` composed with one more `exists_spineOneScale`.

The output is the four-factor product the re-cut `hfac`
(`Kakeya.ML2Core.HfacPostDropFour`) carries: **three** `spineScaleLoss` factors — at the leaf
scale `δ`, at the fine node scale `τ = ρ_b` and at the genuine-parent scale `π = ρ_p` — against
the four multiplicities of the source's `n_a n_p n_b n_i` (l.4451), telescoping
`ρ_a · (ρ_p/2ρ_a) · (ρ_b/2ρ_p) · (δ/2ρ_b) = δ/8` (l.4666-4669).

**Family / shading / level pair.**  `(s, V)` at the leaf scale `δ`; `Tτ` the level-`b` nodes,
`Tπ` the level-`p` nodes, `Tθ` the level-`a` nodes; the three parent maps are
`pτ : ιf → ιm` (leaf → `b`), `pπ : ιm → ιp` (`b` → `p`, the **seam**, the source's middle-factor
pair) and `pθ : ιp → ιc` (`p` → `a`, the **new-parent** pair).  Shadings: `Y'` on the leaves,
`Yτ'` on the retained level-`b` set, `Yπ'` on the retained level-`p` set, `Yθ` on the retained
level-`a` set.

**`p ≠ 0`, not `a ≠ 0`** ((ii)): nothing here is guarded on the coarse
level being nonzero.  The scale hypotheses are `δ ≤ τ ≤ π ≤ θ ≤ 1` and nothing else, so the
degenerate case `θ = 1` (the single ambient cell, the source's `a = 0`) is *inside* the statement
rather than excluded from it, and the new-parent link `(a, p)` stays live there exactly when
`π < 1`.  `Kakeya.ML2Reduction.spineThreeScale_live_at_ambient` records that reading.
-/

@[expose] public section

open MeasureTheory Metric ConvexSpaceBody ShadedBody
open scoped NNReal ENNReal

namespace Kakeya.ML2Reduction

universe u

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

open Classical in
/-- **The three-scale split: `exists_spineOneScale` a third time.**

`Kakeya.ML2Reduction.exists_spineTwoScale` at `(δ, τ, π)` followed by one more
`Kakeya.ML2Reduction.exists_spineOneScale` at `(π, θ)`, on the level-`p` shading the two-scale
split hands back.  Its conclusion is the four-factor product of the re-cut `hfac`.

**Family/shading:** as in the module docstring.  **Level pairs:** leaf → `b`, then the seam
`(p, b)`, then the new parent `(a, p)`. -/
theorem exists_spineThreeScale
    {δ τ π θ : ℝ≥0} (hδ : 0 < δ) (hδτ : δ ≤ τ) (hτπ : τ ≤ π) (hπθ : π ≤ θ) (hθ1 : θ ≤ 1)
    {ιf ιm ιp ιc : Type u} {s : Finset ιf} {t : Finset ιm} {tp : Finset ιp} {u : Finset ιc}
    (V : ιf → ShadedTube δ E) (Tτ : ιm → Tube τ E) (Tπ : ιp → Tube π E) (Tθ : ιc → Tube θ E)
    (pτ : ιf → ιm) (pπ : ιm → ιp) (pθ : ιp → ιc)
    (hball : ∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall (0 : E) 1)
    (hballτ : ∀ j ∈ t, (Tτ j).carrier ⊆ Metric.closedBall (0 : E) 1)
    (hballπ : ∀ k ∈ tp, (Tπ k).carrier ⊆ Metric.closedBall (0 : E) 1)
    (hmapsτ : ∀ i ∈ s, pτ i ∈ t)
    (hleτ : ∀ i ∈ s, (V i).toConvexSpaceBody ≤ (Tτ (pτ i)).toConvexSpaceBody)
    (hmapsπ : ∀ j ∈ t, pπ j ∈ tp)
    (hleπ : ∀ j ∈ t, (Tτ j).toConvexSpaceBody ≤ (Tπ (pπ j)).toConvexSpaceBody)
    (hmapsθ : ∀ k ∈ tp, pθ k ∈ u)
    (hleθ : ∀ k ∈ tp, (Tπ k).toConvexSpaceBody ≤ (Tθ (pθ k)).toConvexSpaceBody) :
    ∃ tτ' ⊆ t, ∃ tπ' ⊆ tp, ∃ tθ' ⊆ u,
      ∃ (Yτ' : ιm → ShadedTube τ E) (Yπ Yπ' : ιp → ShadedTube π E) (Yθ : ιc → ShadedTube θ E)
        (Y' : ιf → ShadedTube δ E),
        (∀ j, (Yτ' j).toTube = Tτ j) ∧
        (∀ k, (Yπ k).toTube = Tπ k) ∧
        (∀ k, (Yπ' k).toTube = Tπ k) ∧
        (∀ l, (Yθ l).toTube = Tθ l) ∧
        (∀ i, (Y' i).toTube = (V i).toTube) ∧
        (∀ i, (Y' i).shade ⊆ (V i).shade) ∧
        (∀ k, (Yπ' k).shade ⊆ (Yπ k).shade) ∧
        (0 < ∑ i ∈ s, volume (V i).shade → tτ'.Nonempty ∧ tπ'.Nonempty ∧ tθ'.Nonempty) ∧
        (spineScaleLoss (Module.finrank ℝ E) s.card δ *
              spineScaleLoss (Module.finrank ℝ E) tτ'.card τ)⁻¹ *
            ShadedBody.fullness s (fun i => (V i).toShadedBody)
          ≤ ShadedBody.fullness tπ' (fun k => (Yπ k).toShadedBody) ∧
        (∀ jτ ∈ tτ', ∀ jπ ∈ tπ', ∀ jθ ∈ tθ',
          ShadedBody.multiplicity s (fun i => (V i).toShadedBody)
            ≤ ((spineScaleLoss (Module.finrank ℝ E) s.card δ *
                  spineScaleLoss (Module.finrank ℝ E) tτ'.card τ *
                  spineScaleLoss (Module.finrank ℝ E) tπ'.card π : ℝ≥0) : ENNReal)
              * ShadedBody.multiplicity {i ∈ s | pτ i = jτ} (fun i => (Y' i).toShadedBody)
              * ShadedBody.multiplicity {j ∈ tτ' | pπ j = jπ} (fun j => (Yτ' j).toShadedBody)
              * ShadedBody.multiplicity {k ∈ tπ' | pθ k = jθ} (fun k => (Yπ' k).toShadedBody)
              * ShadedBody.multiplicity tθ' (fun l => (Yθ l).toShadedBody)) := by
  classical
  have hτ0 : 0 < τ := lt_of_lt_of_le hδ hδτ
  have hπ0 : 0 < π := lt_of_lt_of_le hτ0 hτπ
  have hτ1 : τ ≤ 1 := hτπ.trans (hπθ.trans hθ1)
  have hπ1 : π ≤ 1 := hπθ.trans hθ1
  -- step 1: `δ → τ`
  obtain ⟨tτ', htτ', Yτ, Y', hYτtube, hY'tube, hY'shade, hτne, hτmass, _hc1, hf1, _hr1,
      hprod1⟩ :=
    exists_spineOneScale (E := E) hδ hδτ hτ1 V Tτ pτ hball hmapsτ hleτ
  have hYτbody : ∀ j, (Yτ j).toConvexSpaceBody = (Tτ j).toConvexSpaceBody := fun j =>
    congrArg (fun T : Tube τ E => T.toConvexSpaceBody) (hYτtube j)
  have hballYτ : ∀ j ∈ tτ', (Yτ j).carrier ⊆ Metric.closedBall (0 : E) 1 := by
    intro j hj
    have hc : (Yτ j).carrier = (Tτ j).carrier :=
      congrArg (fun B : ConvexSpaceBody E => B.carrier) (hYτbody j)
    rw [hc]
    exact hballτ j (htτ' hj)
  -- step 2: `τ → π`, the seam
  obtain ⟨tπ', htπ', Yπ, Yτ', hYπtube, hYτ'tube, _hYτ'shade, hπne, hπmass, _hc2, hf2, _hr2,
      hprod2⟩ :=
    exists_spineOneScale (E := E) hτ0 hτπ hπ1 Yτ Tπ pπ hballYτ
      (fun j hj => hmapsπ j (htτ' hj))
      (fun j hj => by rw [hYτbody j]; exact hleπ j (htτ' hj))
  have hYπbody : ∀ k, (Yπ k).toConvexSpaceBody = (Tπ k).toConvexSpaceBody := fun k =>
    congrArg (fun T : Tube π E => T.toConvexSpaceBody) (hYπtube k)
  have hballYπ : ∀ k ∈ tπ', (Yπ k).carrier ⊆ Metric.closedBall (0 : E) 1 := by
    intro k hk
    have hc : (Yπ k).carrier = (Tπ k).carrier :=
      congrArg (fun B : ConvexSpaceBody E => B.carrier) (hYπbody k)
    rw [hc]
    exact hballπ k (htπ' hk)
  -- step 3: `π → θ`, the THIRD application
  obtain ⟨tθ', htθ', Yθ, Yπ', hYθtube, hYπ'tube, hYπ'shade, hθne, _hθmass, _hc3, _hf3, _hr3,
      hprod3⟩ :=
    exists_spineOneScale (E := E) hπ0 hπθ hθ1 Yπ Tθ pθ hballYπ
      (fun k hk => hmapsθ k (htπ' hk))
      (fun k hk => by rw [hYπbody k]; exact hleθ k (htπ' hk))
  refine ⟨tτ', htτ', tπ', htπ', tθ', htθ', Yτ', Yπ, Yπ', Yθ, Y',
    fun j => (hYτ'tube j).trans (hYτtube j), hYπtube,
    fun k => (hYπ'tube k).trans (hYπtube k),
    hYθtube, hY'tube, hY'shade, hYπ'shade, ?_, ?_, ?_⟩
  · intro hmass
    exact ⟨hτne hmass, hπne (hτmass hmass), hθne (hπmass (hτmass hmass))⟩
  · -- the fullness chain, at the genuine-parent level
    calc (spineScaleLoss (Module.finrank ℝ E) s.card δ *
            spineScaleLoss (Module.finrank ℝ E) tτ'.card τ)⁻¹ *
            ShadedBody.fullness s (fun i => (V i).toShadedBody)
        = (spineScaleLoss (Module.finrank ℝ E) tτ'.card τ)⁻¹ *
            ((spineScaleLoss (Module.finrank ℝ E) s.card δ)⁻¹ *
              ShadedBody.fullness s (fun i => (V i).toShadedBody)) := by
          rw [mul_inv]; ring
      _ ≤ (spineScaleLoss (Module.finrank ℝ E) tτ'.card τ)⁻¹ *
            ShadedBody.fullness tτ' (fun j => (Yτ j).toShadedBody) := by gcongr
      _ ≤ ShadedBody.fullness tπ' (fun k => (Yπ k).toShadedBody) := hf2
  · intro jτ hjτ jπ hjπ jθ hjθ
    calc ShadedBody.multiplicity s (fun i => (V i).toShadedBody)
        ≤ ((spineScaleLoss (Module.finrank ℝ E) s.card δ : ℝ≥0) : ENNReal)
            * ShadedBody.multiplicity tτ' (fun j => (Yτ j).toShadedBody)
            * ShadedBody.multiplicity {i ∈ s | pτ i = jτ} (fun i => (Y' i).toShadedBody) :=
          hprod1 jτ hjτ
      _ ≤ ((spineScaleLoss (Module.finrank ℝ E) s.card δ : ℝ≥0) : ENNReal)
            * (((spineScaleLoss (Module.finrank ℝ E) tτ'.card τ : ℝ≥0) : ENNReal)
                * ShadedBody.multiplicity tπ' (fun k => (Yπ k).toShadedBody)
                * ShadedBody.multiplicity {j ∈ tτ' | pπ j = jπ} (fun j => (Yτ' j).toShadedBody))
            * ShadedBody.multiplicity {i ∈ s | pτ i = jτ} (fun i => (Y' i).toShadedBody) := by
          gcongr
          exact hprod2 jπ hjπ
      _ ≤ ((spineScaleLoss (Module.finrank ℝ E) s.card δ : ℝ≥0) : ENNReal)
            * (((spineScaleLoss (Module.finrank ℝ E) tτ'.card τ : ℝ≥0) : ENNReal)
                * (((spineScaleLoss (Module.finrank ℝ E) tπ'.card π : ℝ≥0) : ENNReal)
                    * ShadedBody.multiplicity tθ' (fun l => (Yθ l).toShadedBody)
                    * ShadedBody.multiplicity {k ∈ tπ' | pθ k = jθ}
                        (fun k => (Yπ' k).toShadedBody))
                * ShadedBody.multiplicity {j ∈ tτ' | pπ j = jπ} (fun j => (Yτ' j).toShadedBody))
            * ShadedBody.multiplicity {i ∈ s | pτ i = jτ} (fun i => (Y' i).toShadedBody) := by
          gcongr
          exact hprod3 jθ hjθ
      _ = ((spineScaleLoss (Module.finrank ℝ E) s.card δ *
              spineScaleLoss (Module.finrank ℝ E) tτ'.card τ *
              spineScaleLoss (Module.finrank ℝ E) tπ'.card π : ℝ≥0) : ENNReal)
            * ShadedBody.multiplicity {i ∈ s | pτ i = jτ} (fun i => (Y' i).toShadedBody)
            * ShadedBody.multiplicity {j ∈ tτ' | pπ j = jπ} (fun j => (Yτ' j).toShadedBody)
            * ShadedBody.multiplicity {k ∈ tπ' | pθ k = jθ} (fun k => (Yπ' k).toShadedBody)
            * ShadedBody.multiplicity tθ' (fun l => (Yθ l).toShadedBody) := by
          rw [ENNReal.coe_mul, ENNReal.coe_mul]; ring

/-! ## The three-scale split read at three levels of a hierarchy -/

section Hierarchy

variable {δ : ℝ≥0} {ι : Type u} {s : Finset ι} {V : ι → ShadedTube δ E} {N : ℕ} {σ : ℕ → ℝ≥0}

open Classical in
/-- **The four-way split at three levels `a ≤ p ≤ b` of a nested cover hierarchy** — the exact
shape of the re-cut `hfac`'s conclusion.

`Kakeya.ML2Reduction.exists_spineTwoScale_ofChain` with the seam's level inserted: the three
parent maps are `assign b`, `coarseNode 𝒞 p b` (the **seam**, at the source's middle-factor pair)
and `coarseNode 𝒞 a p` (the **new parent**), and their four side conditions are existing —
`assign_mem_activeNodes`, `le_tube_assign`, `Kakeya.ML2Core.coarseNode_mem_activeNodes`,
`tube_le_coarseNode` twice, `coarseNode_mem`.  No new estimate; no `a ≠ 0` guard.

The four multiplicity sets it returns are, verbatim, the four the re-cut `hfac` reads:
`{i ∈ s | assign b i = jτ}`, `{j ∈ tτ' | coarseNode 𝒞 p b j = jp}`,
`{k ∈ tp' | coarseNode 𝒞 a p k = jθ}` and `tθ'`.

**Family/shading:** `(s, V)` under `𝒞`, with the split's four shadings.
**Level pairs:** leaf → `b`; seam `(p, b)`; new parent `(a, p)`; outer level `a`. -/
theorem exists_spineThreeScale_ofChain
    (hδ : 0 < δ) (V : ι → ShadedTube δ E)
    (𝒞 : Tube.ChainCoverSystem s (fun i => (V i).toTube) N σ)
    {a p b : ℕ} (hap : a ≤ p) (hpb : p ≤ b) (haN : a ≤ N) (hpN : p ≤ N) (hbN : b ≤ N)
    (hδτ : δ ≤ σ b) (hτπ : σ b ≤ σ p) (hπθ : σ p ≤ σ a) (hθ1 : σ a ≤ 1)
    (hball : ∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall (0 : E) 1)
    (hballτ : ∀ j ∈ activeNodes 𝒞 b, (𝒞.tube b j).carrier ⊆ Metric.closedBall (0 : E) 1)
    (hballπ : ∀ k ∈ activeNodes 𝒞 p, (𝒞.tube p k).carrier ⊆ Metric.closedBall (0 : E) 1) :
    ∃ tτ' ⊆ activeNodes 𝒞 b, ∃ tp' ⊆ activeNodes 𝒞 p, ∃ tθ' ⊆ 𝒞.indexSet a,
      ∃ (Yτ' : ι → ShadedTube (σ b) E) (Ypo Yp : ι → ShadedTube (σ p) E)
        (Yθ : ι → ShadedTube (σ a) E) (Y' : ι → ShadedTube δ E),
        (∀ j, (Yτ' j).toTube = 𝒞.tube b j) ∧
        (∀ k, (Ypo k).toTube = 𝒞.tube p k) ∧
        (∀ k, (Yp k).toTube = 𝒞.tube p k) ∧
        (∀ l, (Yθ l).toTube = 𝒞.tube a l) ∧
        (∀ i, (Y' i).toTube = (V i).toTube) ∧
        (∀ i, (Y' i).shade ⊆ (V i).shade) ∧
        (∀ k, (Yp k).shade ⊆ (Ypo k).shade) ∧
        (0 < ∑ i ∈ s, volume (V i).shade →
          tτ'.Nonempty ∧ tp'.Nonempty ∧ tθ'.Nonempty) ∧
        (spineScaleLoss (Module.finrank ℝ E) s.card δ *
              spineScaleLoss (Module.finrank ℝ E) tτ'.card (σ b))⁻¹ *
            ShadedBody.fullness s (fun i => (V i).toShadedBody)
          ≤ ShadedBody.fullness tp' (fun k => (Ypo k).toShadedBody) ∧
        (∀ jτ ∈ tτ', ∀ jp ∈ tp', ∀ jθ ∈ tθ',
          ShadedBody.multiplicity s (fun i => (V i).toShadedBody)
            ≤ ((spineScaleLoss (Module.finrank ℝ E) s.card δ *
                  spineScaleLoss (Module.finrank ℝ E) tτ'.card (σ b) *
                  spineScaleLoss (Module.finrank ℝ E) tp'.card (σ p) : ℝ≥0) : ENNReal)
              * ShadedBody.multiplicity {i ∈ s | 𝒞.assign b i = jτ}
                  (fun i => (Y' i).toShadedBody)
              * ShadedBody.multiplicity {j ∈ tτ' | coarseNode 𝒞 p b j = jp}
                  (fun j => (Yτ' j).toShadedBody)
              * ShadedBody.multiplicity {k ∈ tp' | coarseNode 𝒞 a p k = jθ}
                  (fun k => (Yp k).toShadedBody)
              * ShadedBody.multiplicity tθ' (fun l => (Yθ l).toShadedBody)) := by
  classical
  exact exists_spineThreeScale (E := E) hδ hδτ hτπ hπθ hθ1 V (𝒞.tube b) (𝒞.tube p) (𝒞.tube a)
    (𝒞.assign b) (coarseNode 𝒞 p b) (coarseNode 𝒞 a p) hball hballτ hballπ
    (fun i hi => assign_mem_activeNodes 𝒞 hbN hi)
    (fun i hi => 𝒞.le_tube_assign b hbN i hi)
    (fun j hj => Kakeya.ML2Core.coarseNode_mem_activeNodes 𝒞 hpb hbN hj)
    (fun j hj => tube_le_coarseNode 𝒞 hpb hbN hj)
    (fun k hk => coarseNode_mem 𝒞 haN hk)
    (fun k hk => tube_le_coarseNode 𝒞 hap hpN hk)

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
/-- **The ambient case is inside the statement, not excluded from it** ((ii)).

At `a = 0` the outer scale is `σ 0` and the source's outer family is the single ambient cell; the
tree's three `a ≠ 0 →` rows exist because the *coarse seam* is unavailable there.  The three-scale
split asks no such thing: its hypotheses are `δ ≤ σ b ≤ σ p ≤ σ a ≤ 1`, which `σ a = 1` satisfies.
So the new-parent link `(a, p)` is live at `a = 0` exactly when `σ p < σ a`, and the two guards
come apart as the condition requires. -/
theorem spineThreeScale_hyps_at_ambient {σ' : ℕ → ℝ≥0} {p b : ℕ}
    (h1 : σ' 0 = 1) (hbp : σ' b ≤ σ' p) (hp0 : σ' p ≤ σ' 0) :
    σ' b ≤ σ' p ∧ σ' p ≤ σ' 0 ∧ σ' 0 ≤ 1 :=
  ⟨hbp, hp0, le_of_eq h1⟩

end Hierarchy

end Kakeya.ML2Reduction

end
