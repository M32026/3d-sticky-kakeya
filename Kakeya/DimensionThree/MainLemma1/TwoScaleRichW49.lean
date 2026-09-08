/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.OneScaleRichW49
public import Kakeya.Factoring.WeightedFullness

/-!
# Product-only two-scale factoring

Two applications of the product-only one-scale theorem are composed here.  The output retains
only the data read by the direct three-factor consumer: positive mass, average fullness,
refinements, fixed tube carriers, and the multiplicity product.
-/

@[expose] public section

open MeasureTheory ConvexSpaceBody
open scoped NNReal ENNReal

namespace Kakeya.ml1Boot

universe u v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-- Map-only form of the current carrier-weighted fibre-fullness selection theorem. -/
private theorem exists_filter_fullness_ge_of_mapsTo_w49
    {ι κ : Type u} [DecidableEq κ] {s : Finset ι} {t : Finset κ}
    (V : ι → ShadedBody E) (p : ι → κ)
    (ht : t.Nonempty) (hmap : ∀ i ∈ s, p i ∈ t)
    (hcarrier : ∑ i ∈ s, volume (V i).carrier ≠ 0) :
    ∃ j ∈ t, ShadedBody.fullness s V ≤
      ShadedBody.fullness (s.filter fun i => p i = j) V := by
  classical
  let F : ShadedBody.FactorFamily E ι κ :=
    { innerSet := s
      innerBody := V
      outerSet := t
      outerBody := fun _ => s.convexHull_biUnion (fun i => (V i).toConvexSpaceBody)
      parent := p
      parent_mem := hmap
      inner_le_parent := fun i hi =>
        Finset.le_convexHull_biUnion (fun i => (V i).toConvexSpaceBody) hi }
  obtain ⟨j, hj, hfull⟩ :=
    ShadedBody.exists_fullness_le_fiber F ht (by simpa [F] using hcarrier)
  refine ⟨j, hj, ?_⟩
  exact ENNReal.coe_le_coe.mp (by
    simpa [F, ShadedBody.FactorFamily.fiber] using hfull)

/-- Pairwise factor-two comparability of both levels of active fibres gives the three-family
cardinality product required by the direct-factor assembly. -/
theorem active_fibre_product_card_le {ι κ l : Type*} [DecidableEq κ] [DecidableEq l]
    {s sf : Finset ι} {tm sm : Finset κ} {tc : Finset l}
    {pτ : ι → κ} {pθ : κ → l}
    (hsf : sf ⊆ s) (hsm : sm ⊆ tm)
    (hmapFine : ∀ i ∈ sf, pτ i ∈ tm)
    (hmapMid : ∀ k ∈ sm, pθ k ∈ tc)
    (hbandFine : ∀ k ∈ tm, ∀ k' ∈ tm,
      ((fibre sf pτ k).card : ENNReal) ≤ 2 * ((fibre sf pτ k').card : ENNReal))
    (hbandMid : ∀ l ∈ tc, ∀ l' ∈ tc,
      ((fibre sm pθ l).card : ENNReal) ≤ 2 * ((fibre sm pθ l').card : ENNReal))
    {k : κ} (hk : k ∈ tm) {l₀ : l} (hl₀ : l₀ ∈ tc) :
    ((fibre sf pτ k).card : ENNReal) * ((fibre sm pθ l₀).card : ENNReal) *
        (tc.card : ENNReal) ≤ 4 * (s.card : ENNReal) := by
  classical
  have hsumFine : (sf.card : ENNReal) =
      ∑ k' ∈ tm, ((fibre sf pτ k').card : ENNReal) := by
    have hnat : sf.card = ∑ k' ∈ tm, (fibre sf pτ k').card := by
      simpa [fibre] using Finset.card_eq_sum_card_fiberwise hmapFine
    exact_mod_cast hnat
  have hsumMid : (sm.card : ENNReal) =
      ∑ l' ∈ tc, ((fibre sm pθ l').card : ENNReal) := by
    have hnat : sm.card = ∑ l' ∈ tc, (fibre sm pθ l').card := by
      simpa [fibre] using Finset.card_eq_sum_card_fiberwise hmapMid
    exact_mod_cast hnat
  have hFine : (tm.card : ENNReal) * ((fibre sf pτ k).card : ENNReal) ≤
      2 * (sf.card : ENNReal) := by
    calc
      (tm.card : ENNReal) * ((fibre sf pτ k).card : ENNReal) =
          ∑ _k' ∈ tm, ((fibre sf pτ k).card : ENNReal) := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ k' ∈ tm, 2 * ((fibre sf pτ k').card : ENNReal) := by
            exact Finset.sum_le_sum fun k' hk' => hbandFine k hk k' hk'
      _ = 2 * (sf.card : ENNReal) := by rw [← Finset.mul_sum, ← hsumFine]
  have hMid : (tc.card : ENNReal) * ((fibre sm pθ l₀).card : ENNReal) ≤
      2 * (tm.card : ENNReal) := by
    calc
      (tc.card : ENNReal) * ((fibre sm pθ l₀).card : ENNReal) =
          ∑ _l' ∈ tc, ((fibre sm pθ l₀).card : ENNReal) := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ l' ∈ tc, 2 * ((fibre sm pθ l').card : ENNReal) := by
            exact Finset.sum_le_sum fun l' hl' => hbandMid l₀ hl₀ l' hl'
      _ = 2 * (sm.card : ENNReal) := by rw [← Finset.mul_sum, ← hsumMid]
      _ ≤ 2 * (tm.card : ENNReal) := by
            exact mul_le_mul_right (by exact_mod_cast Finset.card_le_card hsm) 2
  have hsfCard : (sf.card : ENNReal) ≤ (s.card : ENNReal) := by
    exact_mod_cast Finset.card_le_card hsf
  calc
    ((fibre sf pτ k).card : ENNReal) * ((fibre sm pθ l₀).card : ENNReal) *
          (tc.card : ENNReal)
        = ((fibre sf pτ k).card : ENNReal) *
            ((tc.card : ENNReal) * ((fibre sm pθ l₀).card : ENNReal)) := by ring
    _ ≤ ((fibre sf pτ k).card : ENNReal) * (2 * (tm.card : ENNReal)) := by
          gcongr
    _ = 2 * ((tm.card : ENNReal) * ((fibre sf pτ k).card : ENNReal)) := by ring
    _ ≤ 2 * (2 * (sf.card : ENNReal)) := by gcongr
    _ = 4 * (sf.card : ENNReal) := by ring
    _ ≤ 4 * (s.card : ENNReal) := mul_le_mul_right hsfCard 4

/-- Two axiom-clean one-scale product factorizations, composed without any uniformity bundle. -/
theorem exists_twoScaleProductOnly_rich_w49 (hdim : Module.finrank ℝ E = 3)
    {δ τ θ : NNReal} (hδ : 0 < δ) (hδτ : δ ≤ τ) (hτθ : τ ≤ θ) (hθ1 : θ ≤ 1)
    {ι κ : Type u} [DecidableEq κ] {s : Finset ι} {tτ tθ : Finset κ}
    (T : ι → ShadedTube δ E) (Tτ : κ → Tube τ E) (pτ : ι → κ)
    (Tθ : κ → Tube θ E) (pθ : κ → κ)
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1)
    (hfine : IsParentFamily s (fun i => (T i).toTube) tτ Tτ pτ)
    (hmass : 0 < ∑ i ∈ s, volume (T i).shade)
    (hballτ : ∀ k ∈ tτ, (Tτ k).carrier ⊆ Metric.closedBall 0 1)
    (hcoarse : IsParentFamily tτ Tτ tθ Tθ pθ) :
    ∃ (tm : Finset κ) (sf : Finset ι)
      (Zτ : κ → ShadedTube τ E) (Zf : ι → ShadedTube δ E)
      (tc sm : Finset κ) (Zc : κ → ShadedTube θ E) (Zm : κ → ShadedTube τ E),
      tm.Nonempty ∧ tc.Nonempty ∧ tm ⊆ tτ ∧ sf ⊆ s ∧ sm ⊆ tm ∧ tc ⊆ tθ ∧
      (∀ i ∈ sf, pτ i ∈ tm) ∧
      (∀ k ∈ tm, (fibre sf pτ k).Nonempty) ∧
      (∀ k ∈ tm, ∀ k' ∈ tm,
        ((fibre sf pτ k).card : ENNReal) ≤ 2 * ((fibre sf pτ k').card : ENNReal)) ∧
      (∀ k ∈ sm, pθ k ∈ tc) ∧
      (∀ l ∈ tc, (fibre sm pθ l).Nonempty) ∧
      (∀ l ∈ tc, ∀ l' ∈ tc,
        ((fibre sm pθ l).card : ENNReal) ≤ 2 * ((fibre sm pθ l').card : ENNReal)) ∧
      0 < ∑ i ∈ sf, volume (Zf i).shade ∧
      0 < ∑ k ∈ sm, volume (Zm k).shade ∧
      (∀ k ∈ tm, (Zτ k).toTube = Tτ k) ∧
      (∀ i ∈ sf, (Zf i).toTube = (T i).toTube) ∧
      (factorOneScale.C s.card δ)⁻¹ *
          ShadedBody.fullness s (fun i => (T i).toShadedBody)
        ≤ ShadedBody.fullness tm (fun k => (Zτ k).toShadedBody) ∧
      ShadedBody.IsCRefinement sf
        (fun i => (Zf i).toShadedBody) s (fun i => (T i).toShadedBody)
        (factorOneScale.C s.card δ)⁻¹ ∧
      (factorOneScale.C tm.card τ)⁻¹ *
          ShadedBody.fullness tm (fun k => (Zτ k).toShadedBody)
        ≤ ShadedBody.fullness tc (fun l => (Zc l).toShadedBody) ∧
      ShadedBody.IsCRefinement sm
        (fun k => (Zm k).toShadedBody) tm (fun k => (Zτ k).toShadedBody)
        (factorOneScale.C tm.card τ)⁻¹ ∧
      (∃ k ∈ tm, ShadedBody.fullness sf (fun i => (Zf i).toShadedBody) ≤
        ShadedBody.fullness (fibre sf pτ k) (fun i => (Zf i).toShadedBody)) ∧
      (∃ l ∈ tc, ShadedBody.fullness sm (fun k => (Zm k).toShadedBody) ≤
        ShadedBody.fullness (fibre sm pθ l) (fun k => (Zm k).toShadedBody)) ∧
      (∀ k ∈ tm, ∀ l ∈ tc,
        ((fibre sf pτ k).card : ENNReal) * ((fibre sm pθ l).card : ENNReal) *
          (tc.card : ENNReal) ≤ 4 * (s.card : ENNReal)) ∧
      ∀ k ∈ tm, ∀ l ∈ tc,
        ShadedBody.multiplicity s (fun i => (T i).toShadedBody) ≤
          (factorTwoScales.C s.card δ tm.card τ : ENNReal)
            * ShadedBody.multiplicity tc (fun j => (Zc j).toShadedBody)
            * ShadedBody.multiplicity (fibre sm pθ l)
                (fun j => (Zm j).toShadedBody)
            * ShadedBody.multiplicity (fibre sf pτ k)
                (fun i => (Zf i).toShadedBody) := by
  obtain ⟨tm, htm, sf, hsf, Zτ, Zf, htmne, hsfmaps, htmfibne, hfineCard,
      hmassτ, hmassf, hZτtube, hZftube, hfullτ, hrefFine, hprod1⟩ :=
    exists_oneScaleProductOnly_rich_w49 hdim hδ hδτ (hτθ.trans hθ1)
      T Tτ pτ hball hfine hmass
  have hparent2 : IsParentFamily tm (fun k => (Zτ k).toTube) tθ Tθ pθ := by
    refine ⟨?_, hcoarse.injOn, ?_⟩
    · intro k hk
      exact hcoarse.mapsTo k (htm hk)
    · intro k hk
      rw [hZτtube k]
      exact hcoarse.le_parent k (htm hk)
  have hball2 : ∀ k ∈ tm, (Zτ k).carrier ⊆ Metric.closedBall 0 1 := by
    intro k hk
    rw [hZτtube k]
    exact hballτ k (htm hk)
  obtain ⟨tc, htc, sm, hsm, Zc, Zm, htcne, hsmmaps, htcfibne, hmidCard,
      _hmassc, hmassm, _hZctube, _hZmtube, hfullc, hrefMid, hprod2⟩ :=
    exists_oneScaleProductOnly_rich_w49 hdim (lt_of_lt_of_le hδ hδτ) hτθ hθ1
      Zτ Tθ pθ hball2 hparent2 hmassτ
  have hgoodFine : ∃ k ∈ tm,
      ShadedBody.fullness sf (fun i => (Zf i).toShadedBody) ≤
        ShadedBody.fullness (fibre sf pτ k) (fun i => (Zf i).toShadedBody) := by
    obtain ⟨k, hk, hfull⟩ := exists_filter_fullness_ge_of_mapsTo_w49
      (fun i => (Zf i).toShadedBody) pτ htmne hsfmaps
      (ShadedBody.sum_volume_carrier_ne_zero_of_sum_shade_ne_zero sf
        (fun i => (Zf i).toShadedBody) hmassf.ne')
    exact ⟨k, hk, by simpa only [fibre] using hfull⟩
  have hgoodMid : ∃ l ∈ tc,
      ShadedBody.fullness sm (fun k => (Zm k).toShadedBody) ≤
        ShadedBody.fullness (fibre sm pθ l) (fun k => (Zm k).toShadedBody) := by
    obtain ⟨l, hl, hfull⟩ := exists_filter_fullness_ge_of_mapsTo_w49
      (fun k => (Zm k).toShadedBody) pθ htcne hsmmaps
      (ShadedBody.sum_volume_carrier_ne_zero_of_sum_shade_ne_zero sm
        (fun k => (Zm k).toShadedBody) hmassm.ne')
    exact ⟨l, hl, by simpa only [fibre] using hfull⟩
  refine ⟨tm, sf, Zτ, Zf, tc, sm, Zc, Zm, htmne, htcne, htm, hsf, hsm, htc,
    hsfmaps, htmfibne, hfineCard, hsmmaps, htcfibne, hmidCard, hmassf, hmassm,
    (fun k _ => hZτtube k), (fun i _ => hZftube i), hfullτ, hrefFine, hfullc, hrefMid,
    hgoodFine, hgoodMid, ?_, ?_⟩
  · intro k hk l hl
    exact active_fibre_product_card_le hsf hsm hsfmaps hsmmaps hfineCard hmidCard hk hl
  intro k hk l hl
  calc
    ShadedBody.multiplicity s (fun i => (T i).toShadedBody)
        ≤ (factorOneScale.C s.card δ : ENNReal)
          * ShadedBody.multiplicity tm (fun j => (Zτ j).toShadedBody)
          * ShadedBody.multiplicity (fibre sf pτ k)
              (fun i => (Zf i).toShadedBody) := hprod1 k hk
    _ ≤ (factorOneScale.C s.card δ : ENNReal) *
          ((factorOneScale.C tm.card τ : ENNReal)
            * ShadedBody.multiplicity tc (fun j => (Zc j).toShadedBody)
            * ShadedBody.multiplicity (fibre sm pθ l)
                (fun j => (Zm j).toShadedBody)) *
          ShadedBody.multiplicity (fibre sf pτ k)
              (fun i => (Zf i).toShadedBody) := by
          gcongr
          exact hprod2 l hl
    _ = _ := by
      rw [factorTwoScales.C, ENNReal.coe_mul]
      ring

end Kakeya.ml1Boot

#print axioms Kakeya.ml1Boot.exists_twoScaleProductOnly_rich_w49
