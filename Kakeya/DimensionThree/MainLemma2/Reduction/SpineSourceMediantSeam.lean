/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFourFactorRowsSite

@[expose] public section

open MeasureTheory Metric ConvexSpaceBody ShadedBody
open scoped NNReal ENNReal Topology

namespace Kakeya.ML2Core

universe u

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

open Classical in
theorem source_exists_spineThreeScale_full_mediant
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
        -- the level-`p` fullness (the existing clause)
        (ML2Reduction.spineScaleLoss (Module.finrank ℝ E) s.card δ *
              ML2Reduction.spineScaleLoss (Module.finrank ℝ E) tτ'.card τ)⁻¹ *
            ShadedBody.fullness s (fun i => (V i).toShadedBody)
          ≤ ShadedBody.fullness tπ' (fun k => (Yπ k).toShadedBody) ∧
        -- KEPT (1): the outer family's fullness
        (ML2Reduction.spineScaleLoss (Module.finrank ℝ E) s.card δ *
              ML2Reduction.spineScaleLoss (Module.finrank ℝ E) tτ'.card τ *
              ML2Reduction.spineScaleLoss (Module.finrank ℝ E) tπ'.card π)⁻¹ *
            ShadedBody.fullness s (fun i => (V i).toShadedBody)
          ≤ ShadedBody.fullness tθ' (fun l => (Yθ l).toShadedBody) ∧
        -- KEPT (2): the leaf refinement, for the fine fibre's mediant
        ShadedBody.IsCRefinement ({i ∈ s | pτ i ∈ tτ'} : Finset ιf)
            (fun i => (Y' i).toShadedBody) s (fun i => (V i).toShadedBody)
            (ML2Reduction.spineScaleLoss (Module.finrank ℝ E) s.card δ)⁻¹ ∧
        -- KEPT (3): the level-`p` refinement, for the `(a,p)` fibre's mediant
        ShadedBody.IsCRefinement ({k ∈ tπ' | pθ k ∈ tθ'} : Finset ιp)
            (fun k => (Yπ' k).toShadedBody) tπ' (fun k => (Yπ k).toShadedBody)
            (ML2Reduction.spineScaleLoss (Module.finrank ℝ E) tπ'.card π)⁻¹ ∧
        -- KEPT (4): the MIDDLE witness may be chosen BY MASS.  The second application's
        -- refinement is internal (its ambient shading is the first application's outer one), so
        -- the mediant is taken here and only its consequence is exported: some retained level-`p`
        -- node `jp` whose `(p,b)` fibre carries the family's fullness at the two-fold loss.  This
        -- is what makes the middle fibre's fullness a THEOREM rather than an assumption -- the
        -- source's own device, l.4482-4483 (`the pigeonholing retained complete tagged fibres and
        -- used their shaded masses as weights`) and l.4675-4677.
        (0 < ∑ i ∈ s, volume (V i).shade →
          ∃ jp ∈ tπ', (ML2Reduction.spineScaleLoss (Module.finrank ℝ E) s.card δ *
              ML2Reduction.spineScaleLoss (Module.finrank ℝ E) tτ'.card τ)⁻¹ *
              ShadedBody.fullness s (fun i => (V i).toShadedBody)
            ≤ ShadedBody.fullness ({j ∈ tτ' | pπ j = jp} : Finset ιm)
                (fun j => (Yτ' j).toShadedBody)) ∧
        (∀ jτ ∈ tτ', ∀ jπ ∈ tπ', ∀ jθ ∈ tθ',
          ShadedBody.multiplicity s (fun i => (V i).toShadedBody)
            ≤ ((ML2Reduction.spineScaleLoss (Module.finrank ℝ E) s.card δ *
                  ML2Reduction.spineScaleLoss (Module.finrank ℝ E) tτ'.card τ *
                  ML2Reduction.spineScaleLoss (Module.finrank ℝ E) tπ'.card π : ℝ≥0) : ENNReal)
              * ShadedBody.multiplicity {i ∈ s | pτ i = jτ} (fun i => (Y' i).toShadedBody)
              * ShadedBody.multiplicity {j ∈ tτ' | pπ j = jπ} (fun j => (Yτ' j).toShadedBody)
              * ShadedBody.multiplicity {k ∈ tπ' | pθ k = jθ} (fun k => (Yπ' k).toShadedBody)
              * ShadedBody.multiplicity tθ' (fun l => (Yθ l).toShadedBody)) := by
  classical
  have hτ0 : 0 < τ := lt_of_lt_of_le hδ hδτ
  have hπ0 : 0 < π := lt_of_lt_of_le hτ0 hτπ
  have hτ1 : τ ≤ 1 := hτπ.trans (hπθ.trans hθ1)
  have hπ1 : π ≤ 1 := hπθ.trans hθ1
  obtain ⟨tτ', htτ', Yτ, Y', hYτtube, hY'tube, hY'shade, hτne, hτmass, _hc1, hf1, hr1,
      hprod1⟩ :=
    ML2Reduction.exists_spineOneScale (E := E) hδ hδτ hτ1 V Tτ pτ hball hmapsτ hleτ
  have hYτbody : ∀ j, (Yτ j).toConvexSpaceBody = (Tτ j).toConvexSpaceBody := fun j =>
    congrArg (fun T : Tube τ E => T.toConvexSpaceBody) (hYτtube j)
  have hballYτ : ∀ j ∈ tτ', (Yτ j).carrier ⊆ Metric.closedBall (0 : E) 1 := by
    intro j hj
    have hc : (Yτ j).carrier = (Tτ j).carrier :=
      congrArg (fun B : ConvexSpaceBody E => B.carrier) (hYτbody j)
    rw [hc]
    exact hballτ j (htτ' hj)
  obtain ⟨tπ', htπ', Yπ, Yτ', hYπtube, hYτ'tube, _hYτ'shade, hπne, hπmass, _hc2, hf2, hr2,
      hprod2⟩ :=
    ML2Reduction.exists_spineOneScale (E := E) hτ0 hτπ hπ1 Yτ Tπ pπ hballYτ
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
  obtain ⟨tθ', htθ', Yθ, Yπ', hYθtube, hYπ'tube, hYπ'shade, hθne, _hθmass, _hc3, hf3, hr3,
      hprod3⟩ :=
    ML2Reduction.exists_spineOneScale (E := E) hπ0 hπθ hθ1 Yπ Tθ pθ hballYπ
      (fun k hk => hmapsθ k (htπ' hk))
      (fun k hk => by rw [hYπbody k]; exact hleθ k (htπ' hk))
  -- the middle witness, by mass, on the second application's own refinement
  have hmed : (0 < ∑ i ∈ s, volume (V i).shade →
      ∃ jp ∈ tπ', (ML2Reduction.spineScaleLoss (Module.finrank ℝ E) s.card δ *
          ML2Reduction.spineScaleLoss (Module.finrank ℝ E) tτ'.card τ)⁻¹ *
          ShadedBody.fullness s (fun i => (V i).toShadedBody)
        ≤ ShadedBody.fullness ({j ∈ tτ' | pπ j = jp} : Finset ιm)
            (fun j => (Yτ' j).toShadedBody)) := by
    intro hmass
    have hτm : 0 < ∑ k ∈ tτ', volume (Yτ k).shade := hτmass hmass
    obtain ⟨hB0, hBtop⟩ :=
      Kakeya.StickyKakeya.sum_volume_carrier_pos_ne_top hτ0 tτ' Yτ (hτne hmass)
    have hfullτ : 0 < ShadedBody.fullness tτ' (fun j => (Yτ j).toShadedBody) :=
      ML2Shaded.fullness_pos_of_sum_shade_ne_zero (E := E) hτm.ne' hBtop
    have hL2 : (1 : NNReal)
        ≤ ML2Reduction.spineScaleLoss (Module.finrank ℝ E) tτ'.card τ :=
      ML2Reduction.one_le_spineScaleLoss _ _ _
    have hinv2 : (0 : NNReal)
        < (ML2Reduction.spineScaleLoss (Module.finrank ℝ E) tτ'.card τ)⁻¹ := by
      simpa using inv_pos.mpr (lt_of_lt_of_le zero_lt_one hL2)
    let s2 : Finset ιm := {j ∈ tτ' | pπ j ∈ tπ'}
    have hs2full : (ML2Reduction.spineScaleLoss (Module.finrank ℝ E) tτ'.card τ)⁻¹ *
        ShadedBody.fullness tτ' (fun j => (Yτ j).toShadedBody) <=
        ShadedBody.fullness s2 (fun j => (Yτ' j).toShadedBody) := by
      exact_mod_cast hr2.coe_mul_fullness_le
    have hs2pos := (mul_pos hinv2 hfullτ).trans_le hs2full
    have hs2ne : s2.Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty.mp h] at hs2pos
      simpa [ShadedBody.fullness, ShadedBody.fullness'] using hs2pos
    obtain ⟨hs20, hs2top⟩ :=
      Kakeya.StickyKakeya.sum_volume_carrier_pos_ne_top hτ0 s2 Yτ' hs2ne
    obtain ⟨jp, hjp, hfib'⟩ :=
      exists_fibre_fullness_le' (E := E) s2 (fun j => (Yτ' j).toShadedBody) tπ' pπ
        (fun j hj => (Finset.mem_filter.mp hj).2) (hπne hτm) hs20.ne' hs2top
    have heq : ({j ∈ s2 | pπ j = jp} : Finset ιm) = {j ∈ tτ' | pπ j = jp} := by
      ext j
      simp only [s2, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hj, _⟩, heq⟩; exact ⟨hj, heq⟩
      · rintro ⟨hj, heq⟩; exact ⟨⟨hj, heq ▸ hjp⟩, heq⟩
    rw [heq] at hfib'
    have hfib := hs2full.trans hfib'
    refine ⟨jp, hjp, le_trans ?_ hfib⟩
    rw [mul_inv]
    calc (ML2Reduction.spineScaleLoss (Module.finrank ℝ E) s.card δ)⁻¹ *
          (ML2Reduction.spineScaleLoss (Module.finrank ℝ E) tτ'.card τ)⁻¹ *
          ShadedBody.fullness s (fun i => (V i).toShadedBody)
        = (ML2Reduction.spineScaleLoss (Module.finrank ℝ E) tτ'.card τ)⁻¹ *
          ((ML2Reduction.spineScaleLoss (Module.finrank ℝ E) s.card δ)⁻¹ *
            ShadedBody.fullness s (fun i => (V i).toShadedBody)) := by ring
      _ ≤ (ML2Reduction.spineScaleLoss (Module.finrank ℝ E) tτ'.card τ)⁻¹ *
          ShadedBody.fullness tτ' (fun j => (Yτ j).toShadedBody) := by gcongr
  refine ⟨tτ', htτ', tπ', htπ', tθ', htθ', Yτ', Yπ, Yπ', Yθ, Y',
    fun j => (hYτ'tube j).trans (hYτtube j), hYπtube,
    fun k => (hYπ'tube k).trans (hYπtube k),
    hYθtube, hY'tube, hY'shade, hYπ'shade, ?_, ?_, ?_, hr1, hr3, hmed, ?_⟩
  · intro hmass
    exact ⟨hτne hmass, hπne (hτmass hmass), hθne (hπmass (hτmass hmass))⟩
  · calc (ML2Reduction.spineScaleLoss (Module.finrank ℝ E) s.card δ *
            ML2Reduction.spineScaleLoss (Module.finrank ℝ E) tτ'.card τ)⁻¹ *
            ShadedBody.fullness s (fun i => (V i).toShadedBody)
        = (ML2Reduction.spineScaleLoss (Module.finrank ℝ E) tτ'.card τ)⁻¹ *
            ((ML2Reduction.spineScaleLoss (Module.finrank ℝ E) s.card δ)⁻¹ *
              ShadedBody.fullness s (fun i => (V i).toShadedBody)) := by
          rw [mul_inv]; ring
      _ ≤ (ML2Reduction.spineScaleLoss (Module.finrank ℝ E) tτ'.card τ)⁻¹ *
            ShadedBody.fullness tτ' (fun j => (Yτ j).toShadedBody) := by gcongr
      _ ≤ ShadedBody.fullness tπ' (fun k => (Yπ k).toShadedBody) := hf2
  · calc (ML2Reduction.spineScaleLoss (Module.finrank ℝ E) s.card δ *
            ML2Reduction.spineScaleLoss (Module.finrank ℝ E) tτ'.card τ *
            ML2Reduction.spineScaleLoss (Module.finrank ℝ E) tπ'.card π)⁻¹ *
            ShadedBody.fullness s (fun i => (V i).toShadedBody)
        = (ML2Reduction.spineScaleLoss (Module.finrank ℝ E) tπ'.card π)⁻¹ *
            ((ML2Reduction.spineScaleLoss (Module.finrank ℝ E) tτ'.card τ)⁻¹ *
              ((ML2Reduction.spineScaleLoss (Module.finrank ℝ E) s.card δ)⁻¹ *
                ShadedBody.fullness s (fun i => (V i).toShadedBody))) := by
          rw [mul_inv, mul_inv]; ring
      _ ≤ (ML2Reduction.spineScaleLoss (Module.finrank ℝ E) tπ'.card π)⁻¹ *
            ((ML2Reduction.spineScaleLoss (Module.finrank ℝ E) tτ'.card τ)⁻¹ *
              ShadedBody.fullness tτ' (fun j => (Yτ j).toShadedBody)) := by gcongr
      _ ≤ (ML2Reduction.spineScaleLoss (Module.finrank ℝ E) tπ'.card π)⁻¹ *
            ShadedBody.fullness tπ' (fun k => (Yπ k).toShadedBody) := by gcongr
      _ ≤ ShadedBody.fullness tθ' (fun l => (Yθ l).toShadedBody) := hf3
  · intro jτ hjτ jπ hjπ jθ hjθ
    calc ShadedBody.multiplicity s (fun i => (V i).toShadedBody)
        ≤ ((ML2Reduction.spineScaleLoss (Module.finrank ℝ E) s.card δ : ℝ≥0) : ENNReal)
            * ShadedBody.multiplicity tτ' (fun j => (Yτ j).toShadedBody)
            * ShadedBody.multiplicity {i ∈ s | pτ i = jτ} (fun i => (Y' i).toShadedBody) :=
          hprod1 jτ hjτ
      _ ≤ ((ML2Reduction.spineScaleLoss (Module.finrank ℝ E) s.card δ : ℝ≥0) : ENNReal)
            * (((ML2Reduction.spineScaleLoss (Module.finrank ℝ E) tτ'.card τ : ℝ≥0) : ENNReal)
                * ShadedBody.multiplicity tπ' (fun k => (Yπ k).toShadedBody)
                * ShadedBody.multiplicity {j ∈ tτ' | pπ j = jπ} (fun j => (Yτ' j).toShadedBody))
            * ShadedBody.multiplicity {i ∈ s | pτ i = jτ} (fun i => (Y' i).toShadedBody) := by
          gcongr
          exact hprod2 jπ hjπ
      _ ≤ ((ML2Reduction.spineScaleLoss (Module.finrank ℝ E) s.card δ : ℝ≥0) : ENNReal)
            * (((ML2Reduction.spineScaleLoss (Module.finrank ℝ E) tτ'.card τ : ℝ≥0) : ENNReal)
                * (((ML2Reduction.spineScaleLoss (Module.finrank ℝ E) tπ'.card π : ℝ≥0) : ENNReal)
                    * ShadedBody.multiplicity tθ' (fun l => (Yθ l).toShadedBody)
                    * ShadedBody.multiplicity {k ∈ tπ' | pθ k = jθ}
                        (fun k => (Yπ' k).toShadedBody))
                * ShadedBody.multiplicity {j ∈ tτ' | pπ j = jπ} (fun j => (Yτ' j).toShadedBody))
            * ShadedBody.multiplicity {i ∈ s | pτ i = jτ} (fun i => (Y' i).toShadedBody) := by
          gcongr
          exact hprod3 jθ hjθ
      _ = ((ML2Reduction.spineScaleLoss (Module.finrank ℝ E) s.card δ *
              ML2Reduction.spineScaleLoss (Module.finrank ℝ E) tτ'.card τ *
              ML2Reduction.spineScaleLoss (Module.finrank ℝ E) tπ'.card π : ℝ≥0) : ENNReal)
            * ShadedBody.multiplicity {i ∈ s | pτ i = jτ} (fun i => (Y' i).toShadedBody)
            * ShadedBody.multiplicity {j ∈ tτ' | pπ j = jπ} (fun j => (Yτ' j).toShadedBody)
            * ShadedBody.multiplicity {k ∈ tπ' | pθ k = jθ} (fun k => (Yπ' k).toShadedBody)
            * ShadedBody.multiplicity tθ' (fun l => (Yθ l).toShadedBody) := by
          rw [ENNReal.coe_mul, ENNReal.coe_mul]; ring

end

open Classical in
theorem source_exists_seamSplit_translated_mediant {ι : Type u} {δ Cu : NNReal} {u : Finset ι}
    {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
    {t₀ t₁ : Finset ι} {a p b : ℕ} {v : EuclideanSpace ℝ (Fin 3)}
    (hδ0 : 0 < δ) (hap : a ≤ p) (hpb : p ≤ b) (hbN : b ≤ Tube.ssfGridLen δ)
    (hδτ : δ ≤ Tube.gridScale δ (Tube.ssfGridLen δ) b)
    (hτπ : Tube.gridScale δ (Tube.ssfGridLen δ) b
      ≤ Tube.gridScale δ (Tube.ssfGridLen δ) p)
    (hπθ : Tube.gridScale δ (Tube.ssfGridLen δ) p
      ≤ Tube.gridScale δ (Tube.ssfGridLen δ) a)
    (hθ1 : Tube.gridScale δ (Tube.ssfGridLen δ) a ≤ 1)
    (hball : ∀ i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι),
      ((T i).translate v).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (hballτ : ∀ j ∈ ML2Reduction.activeNodes (retainedLeafChain 𝒰 t₁ b) b,
      (((retainedLeafChain 𝒰 t₁ b).tube b j).translate v).carrier
        ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (hballπ : ∀ k ∈ ML2Reduction.activeNodes (retainedLeafChain 𝒰 t₁ b) p,
      (((retainedLeafChain 𝒰 t₁ b).tube p k).translate v).carrier
        ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (hmapsθ : ∀ k ∈ ML2Reduction.activeNodes (retainedLeafChain 𝒰 t₁ b) p,
      ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) a p k ∈ t₀) :
    ∃ tτ' ⊆ ML2Reduction.activeNodes (retainedLeafChain 𝒰 t₁ b) b,
      ∃ tp' ⊆ ML2Reduction.activeNodes (retainedLeafChain 𝒰 t₁ b) p, ∃ tθ' ⊆ t₀,
      ∃ (Yτ' : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) b)
          (EuclideanSpace ℝ (Fin 3)))
        (Ypo Yp : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) p)
          (EuclideanSpace ℝ (Fin 3)))
        (Yθ : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) a)
          (EuclideanSpace ℝ (Fin 3)))
        (Y' : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))),
        (∀ j, (Yτ' j).toTube = ((retainedLeafChain 𝒰 t₁ b).tube b j).translate v) ∧
        (∀ k, (Ypo k).toTube = ((retainedLeafChain 𝒰 t₁ b).tube p k).translate v) ∧
        (∀ k, (Yp k).toTube = ((retainedLeafChain 𝒰 t₁ b).tube p k).translate v) ∧
        (∀ l, (Yθ l).toTube = ((retainedLeafChain 𝒰 t₁ b).tube a l).translate v) ∧
        (∀ i, (Y' i).toTube = ((T i).translate v).toTube) ∧
        (0 < ∑ i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι),
            volume ((T i).translate v).shade →
          tτ'.Nonempty ∧ tp'.Nonempty ∧ tθ'.Nonempty) ∧
        (ML2Reduction.spineScaleLoss 3
              ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι).card δ *
            ML2Reduction.spineScaleLoss 3 tτ'.card
              (Tube.gridScale δ (Tube.ssfGridLen δ) b))⁻¹ *
            ShadedBody.fullness ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)
              (fun i => ((T i).translate v).toShadedBody)
          ≤ ShadedBody.fullness tp' (fun k => (Ypo k).toShadedBody) ∧
        (ML2Reduction.spineScaleLoss 3
              ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι).card δ *
            ML2Reduction.spineScaleLoss 3 tτ'.card
              (Tube.gridScale δ (Tube.ssfGridLen δ) b) *
            ML2Reduction.spineScaleLoss 3 tp'.card
              (Tube.gridScale δ (Tube.ssfGridLen δ) p))⁻¹ *
            ShadedBody.fullness ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)
              (fun i => ((T i).translate v).toShadedBody)
          ≤ ShadedBody.fullness tθ' (fun l => (Yθ l).toShadedBody) ∧
        ShadedBody.IsCRefinement
            ({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
              (retainedLeafChain 𝒰 t₁ b).assign b i ∈ tτ'} : Finset ι)
            (fun i => (Y' i).toShadedBody)
            ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)
            (fun i => ((T i).translate v).toShadedBody)
            (ML2Reduction.spineScaleLoss 3
              ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι).card δ)⁻¹ ∧
        ShadedBody.IsCRefinement
            ({k ∈ tp' | ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) a p k ∈ tθ'}
              : Finset ι)
            (fun k => (Yp k).toShadedBody) tp' (fun k => (Ypo k).toShadedBody)
            (ML2Reduction.spineScaleLoss 3 tp'.card
              (Tube.gridScale δ (Tube.ssfGridLen δ) p))⁻¹ ∧
        (0 < ∑ i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι),
              volume ((T i).translate v).shade →
          ∃ jp ∈ tp', (ML2Reduction.spineScaleLoss 3
                ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι).card δ *
              ML2Reduction.spineScaleLoss 3 tτ'.card
                (Tube.gridScale δ (Tube.ssfGridLen δ) b))⁻¹ *
              ShadedBody.fullness ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)
                (fun i => ((T i).translate v).toShadedBody)
            ≤ ShadedBody.fullness
                ({j ∈ tτ' | ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) p b j = jp}
                  : Finset ι) (fun j => (Yτ' j).toShadedBody)) ∧
        (∀ jτ ∈ tτ', ∀ jp ∈ tp', ∀ jθ ∈ tθ',
          ShadedBody.multiplicity ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)
              (fun i => (T i).toShadedBody)
            ≤ ((ML2Reduction.spineScaleLoss 3
                    ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι).card δ *
                  ML2Reduction.spineScaleLoss 3 tτ'.card
                    (Tube.gridScale δ (Tube.ssfGridLen δ) b) *
                  ML2Reduction.spineScaleLoss 3 tp'.card
                    (Tube.gridScale δ (Tube.ssfGridLen δ) p) : ℝ≥0) : ENNReal)
              * ShadedBody.multiplicity
                  ({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) |
                    (retainedLeafChain 𝒰 t₁ b).assign b i = jτ} : Finset ι)
                  (fun i => (Y' i).toShadedBody)
              * ShadedBody.multiplicity
                  ({j ∈ tτ' | ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) p b j = jp}
                    : Finset ι) (fun j => (Yτ' j).toShadedBody)
              * ShadedBody.multiplicity
                  ({k ∈ tp' | ML2Reduction.coarseNode (retainedLeafChain 𝒰 t₁ b) a p k = jθ}
                    : Finset ι) (fun k => (Yp k).toShadedBody)
              * ShadedBody.multiplicity tθ' (fun l => (Yθ l).toShadedBody)) := by
  classical
  let 𝒞 := retainedLeafChain 𝒰 t₁ b
  let fam : Finset ι := ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)
  show ∃ tτ' ⊆ ML2Reduction.activeNodes 𝒞 b, _
  have hn3 : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have hpN : p ≤ Tube.ssfGridLen δ := le_trans hpb hbN
  have haN : a ≤ Tube.ssfGridLen δ := le_trans hap hpN
  have hbody : ∀ i, ((T i).translate v).toConvexSpaceBody
      = (((T i).toTube).translate v).toConvexSpaceBody := fun _ => rfl
  obtain ⟨tτ', htτ', tp', htp', tθ', htθ', Yτ', Ypo, Yp, Yθ, Y', hYτ', hYpo, hYp, hYθ,
      hY'tube, _hY'shade, _hYpshade, hne, hfullπ, hfullθ, hr1, hr3, hmed, hprod⟩ :=
    source_exists_spineThreeScale_full_mediant (E := EuclideanSpace ℝ (Fin 3)) hδ0 hδτ hτπ hπθ hθ1
      (fun i => (T i).translate v)
      (fun j => (𝒞.tube b j).translate v) (fun k => (𝒞.tube p k).translate v)
      (fun l => (𝒞.tube a l).translate v)
      (𝒞.assign b) (ML2Reduction.coarseNode 𝒞 p b) (ML2Reduction.coarseNode 𝒞 a p)
      hball hballτ hballπ
      (fun i hi => ML2Reduction.assign_mem_activeNodes 𝒞 hbN hi)
      (fun i hi => by
        rw [hbody i]
        exact tube_translate_le_translate _ _ v (𝒞.le_tube_assign b hbN i hi))
      (fun j hj => coarseNode_mem_activeNodes 𝒞 hpb hbN hj)
      (fun j hj => tube_translate_le_translate _ _ v
        (ML2Reduction.tube_le_coarseNode 𝒞 hpb hbN hj))
      hmapsθ
      (fun k hk => tube_translate_le_translate _ _ v
        (ML2Reduction.tube_le_coarseNode 𝒞 hap hpN hk))
  rw [hn3] at hfullπ hfullθ hr1 hr3 hmed hprod
  refine ⟨tτ', htτ', tp', htp', tθ', htθ', Yτ', Ypo, Yp, Yθ, Y', hYτ', hYpo, hYp, hYθ, hY'tube,
    hne, hfullπ, hfullθ, hr1, hr3, hmed, ?_⟩
  intro jτ hjτ jp hjp jθ hjθ
  have hbridge : ShadedBody.multiplicity fam (fun i => ((T i).translate v).toShadedBody)
      = ShadedBody.multiplicity fam (fun i => (T i).toShadedBody) :=
    multiplicity_eq_of_shade_translate fam (fun i => (T i).toShadedBody)
      (fun i => ((T i).translate v).toShadedBody) v (fun _ => rfl)
  rw [← hbridge]
  exact hprod jτ hjτ jp hjp jθ hjθ

end Kakeya.ML2Core
