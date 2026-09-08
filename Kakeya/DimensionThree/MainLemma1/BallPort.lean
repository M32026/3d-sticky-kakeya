/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.TwoScaleProductOnly
public import Kakeya.DimensionThree.MainLemma1.Rescaling.BallRadius

/-!
# Product-only factoring in a fixed ambient ball

The second family in the Case (ii) hierarchy lies in `B₄`, whereas the axiom-clean factoring
theorem is normalized to `B₁`.  This file supplies the intervening finite-cell selection.  It
discards low-shading tubes, chooses a cell which controls multiplicity, and translates that cell
to `B₁`.  The loss is the fixed cardinality of the ball cover, with no uniformity bundle or
all-window collision oracle.
-/

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody
open scoped NNReal ENNReal

namespace Kakeya.ml1Boot

universe u v

variable {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-- A positive-mass shaded tube family in a fixed ball has a translated unit-ball subfamily
which retains half the global average fullness and controls the original multiplicity up to the
fixed cell-count loss.

The selected family is chosen only after the shading is known.  This is the product-facing
counterpart of `Kakeya.ml1Boot.multiplicity_le_of_ball_of_unitBall`: here the controlling cell is
returned because it is the input to the second product-only factorization. -/
theorem exists_unitBallCell_productInput (R : ℝ) (hR : 1 ≤ R)
    : ∃ M : ℕ, 0 < M ∧
    ∀ {τ : NNReal}, 0 < τ → (τ : ℝ) ≤ 1 / 4 →
    ∀ {κ : Type u} (t : Finset κ) (T : κ → ShadedTube τ E),
    0 < ∑ k ∈ t, volume (T k).shade →
    (∀ k ∈ t, (T k).carrier ⊆ Metric.closedBall 0 R) →
    ∃ u : Finset κ, u ⊆ t ∧ ∃ v : E,
      u.Nonempty ∧
      0 < ∑ k ∈ u, volume ((T k).translate v).shade ∧
      (∀ k ∈ u, ((T k).translate v).carrier ⊆ Metric.closedBall 0 1) ∧
      ((1 / 2 : NNReal) : ENNReal) *
          (ShadedBody.fullness t (fun k => (T k).toShadedBody) : ENNReal)
        ≤ (ShadedBody.fullness u
            (fun k => ((T k).translate v).toShadedBody) : ENNReal) ∧
      (∑ k ∈ t, volume (T k).shade) ≤
        4 * (M : ENNReal) * ∑ k ∈ u, volume ((T k).translate v).shade ∧
      ShadedBody.multiplicity t (fun k => (T k).toShadedBody)
        ≤ 4 * (M : ENNReal) *
          ShadedBody.multiplicity u (fun k => ((T k).translate v).toShadedBody) := by
  classical
  obtain ⟨xs, hxsne, _hxsNorm, hnet⟩ :=
    StickyKakeya.exists_ball_assignment (E := E) R hR
  refine ⟨xs.card, Finset.card_pos.mpr hxsne, ?_⟩
  intro τ hτ0 hτ4 κ t T hmass hball
  set V : κ → ShadedBody E := fun k => (T k).toShadedBody with hV
  set t₁ : Finset κ := ShadedBody.discardLowShading t V (1 / 2) with ht₁
  have ht₁t : t₁ ⊆ t := ShadedBody.discardLowShading_subset t V (1 / 2)
  have hhalf : ((1 : NNReal) - 1 / 2) = 1 / 2 := by
    refine tsub_eq_of_eq_add ?_
    norm_num
  have hmass₁ : 0 < ∑ k ∈ t₁, volume (V k).shade := by
    have hkeep := ShadedBody.one_sub_mul_sum_volume_shade_le_sum_discardLowShading
      t V (c := (1 / 2 : NNReal)) (by norm_num)
    rw [hhalf] at hkeep
    exact (ENNReal.mul_pos (by norm_num) hmass.ne').trans_le hkeep
  obtain ⟨x₀, hx₀⟩ := hxsne
  set g : κ → E := fun k =>
    if h : ∃ x ∈ xs, (T k).carrier ⊆ Metric.closedBall x 1 then h.choose else x₀
    with hgdef
  have hg : ∀ k ∈ t₁, g k ∈ xs := by
    intro k hk
    have hcond : ∃ x ∈ xs, (T k).carrier ⊆ Metric.closedBall x 1 :=
      hnet hτ4 (T k).toTube (hball k (ht₁t hk))
    simp only [hgdef, dif_pos hcond]
    exact hcond.choose_spec.1
  have hgball : ∀ k ∈ t₁, (T k).carrier ⊆ Metric.closedBall (g k) 1 := by
    intro k hk
    have hcond : ∃ x ∈ xs, (T k).carrier ⊆ Metric.closedBall x 1 :=
      hnet hτ4 (T k).toTube (hball k (ht₁t hk))
    simp only [hgdef, dif_pos hcond]
    exact hcond.choose_spec.2
  let cell : E → Finset κ := fun x => t₁.filter (fun k => g k = x)
  let w : E → ENNReal := fun y => ∑ k ∈ cell y, volume (V k).shade
  let light : Finset E := xs.filter fun y =>
    2 * (xs.card : ENNReal) * w y < ∑ z ∈ xs, w z
  let good : Finset E := xs.filter fun y =>
    ¬2 * (xs.card : ENNReal) * w y < ∑ z ∈ xs, w z
  have hsumCells : (∑ y ∈ xs, w y) = ∑ k ∈ t₁, volume (V k).shade := by
    simpa [w, cell] using
      Finset.sum_fiberwise_of_maps_to hg (fun k => volume (V k).shade)
  have hsumCellsPos : 0 < ∑ y ∈ xs, w y := by
    rw [hsumCells]
    exact hmass₁
  have hsumCellsTop : (∑ y ∈ xs, w y) ≠ ⊤ := by
    rw [hsumCells]
    exact ENNReal.sum_ne_top.mpr fun k hk =>
      ne_top_of_le_ne_top (V k).isCompact'.measure_ne_top (measure_mono (V k).shade_subset)
  have hlight : 2 * ∑ y ∈ light, w y ≤ ∑ y ∈ xs, w y := by
    simpa [light] using ENNReal.two_mul_sum_filter_light_le xs w
  have hsplit : (∑ y ∈ xs, w y) =
      (∑ y ∈ light, w y) + ∑ y ∈ good, w y := by
    simpa [light, good] using
      (Finset.sum_filter_add_sum_filter_not xs
        (fun y => 2 * (xs.card : ENNReal) * w y < ∑ z ∈ xs, w z) w).symm
  have hlightTop : (∑ y ∈ light, w y) ≠ ⊤ := by
    exact ne_top_of_le_ne_top hsumCellsTop (Finset.sum_le_sum_of_subset (by simp [light]))
  have hlightGood : (∑ y ∈ light, w y) ≤ ∑ y ∈ good, w y := by
    apply (ENNReal.add_le_add_iff_left hlightTop).mp
    calc
      (∑ y ∈ light, w y) + ∑ y ∈ light, w y =
          2 * ∑ y ∈ light, w y := by ring
      _ ≤ ∑ y ∈ xs, w y := hlight
      _ = (∑ y ∈ light, w y) + ∑ y ∈ good, w y := hsplit
  have hgoodMass : (∑ y ∈ xs, w y) ≤ 2 * ∑ y ∈ good, w y := by
    calc
      (∑ y ∈ xs, w y) =
          (∑ y ∈ light, w y) + ∑ y ∈ good, w y := hsplit
      _ ≤ (∑ y ∈ good, w y) + ∑ y ∈ good, w y := by gcongr
      _ = 2 * ∑ y ∈ good, w y := by ring
  have hgoodNe : good.Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    have hz : (∑ y ∈ good, w y) = 0 := by rw [hne]; simp
    have hzero : (∑ y ∈ xs, w y) ≤ 0 := by simpa [hz] using hgoodMass
    exact (not_le_of_gt hsumCellsPos) hzero
  let tgood : Finset κ := t₁.filter fun k => g k ∈ good
  have htgoodSub : tgood ⊆ t₁ := Finset.filter_subset _ _
  have hmapGood : ∀ k ∈ tgood, g k ∈ good := by
    intro k hk
    exact (Finset.mem_filter.mp hk).2
  have hfibreGood : ∀ y ∈ good, fibre tgood g y = cell y := by
    intro y hy
    ext k
    simp only [fibre, tgood, cell, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hkt₁, _⟩, hky⟩
      exact ⟨hkt₁, hky⟩
    · rintro ⟨hkt₁, hky⟩
      exact ⟨⟨hkt₁, hky ▸ hy⟩, hky⟩
  have hsumGood : (∑ y ∈ good, w y) = ∑ k ∈ tgood, volume (V k).shade := by
    rw [← Finset.sum_fiberwise_of_maps_to hmapGood (fun k => volume (V k).shade)]
    apply Finset.sum_congr rfl
    intro y hy
    dsimp only [w]
    change (∑ k ∈ cell y, volume (V k).shade) =
      ∑ k ∈ fibre tgood g y, volume (V k).shade
    rw [hfibreGood y hy]
  have ht₁Mass : (∑ k ∈ t₁, volume (V k).shade) ≤
      2 * ∑ k ∈ tgood, volume (V k).shade := by
    rw [← hsumCells, ← hsumGood]
    exact hgoodMass
  obtain ⟨x, hxgood, hxmax⟩ := Finset.exists_max_image good
    (fun y => ShadedBody.multiplicity (cell y) V) hgoodNe
  have hx : x ∈ xs := (Finset.mem_filter.mp hxgood).1
  have hxheavy : (∑ y ∈ xs, w y) ≤ 2 * (xs.card : ENNReal) * w x := by
    exact not_lt.mp (Finset.mem_filter.mp hxgood).2
  have hstep₂ : ShadedBody.multiplicity tgood V
      ≤ ∑ y ∈ good, ShadedBody.multiplicity (cell y) V := by
    have hraw := multiplicity_le_sum_fiberwise tgood V good g hmapGood
    refine hraw.trans_eq ?_
    apply Finset.sum_congr rfl
    intro y hy
    change ShadedBody.multiplicity (fibre tgood g y) V =
      ShadedBody.multiplicity (cell y) V
    rw [hfibreGood y hy]
  have hcellMul : ∑ y ∈ good, ShadedBody.multiplicity (cell y) V
      ≤ (xs.card : ENNReal) * ShadedBody.multiplicity (cell x) V := by
    calc
      ∑ y ∈ good, ShadedBody.multiplicity (cell y) V
          ≤ ∑ _y ∈ good, ShadedBody.multiplicity (cell x) V :=
            Finset.sum_le_sum (fun y hy => hxmax y hy)
      _ = (good.card : ENNReal) * ShadedBody.multiplicity (cell x) V := by
        rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (xs.card : ENNReal) * ShadedBody.multiplicity (cell x) V := by
        gcongr
        exact Finset.filter_subset _ _
  have hstep₁ : ShadedBody.multiplicity t V ≤ 2 * ShadedBody.multiplicity t₁ V := by
    refine ShadedBody.multiplicity_le_mul_of_sum_shade_le_of_biUnion_subset
      t V t₁ V 2 ?_ ?_
    · exact Set.biUnion_subset_biUnion_left (fun k hk => ht₁t hk)
    · have htwo : ((1 / 2 : NNReal) : ENNReal) = (2 : ENNReal)⁻¹ := by norm_num
      calc
        ∑ k ∈ t, volume (V k).shade
            = (2 : ENNReal) * (((1 / 2 : NNReal) : ENNReal) *
                ∑ k ∈ t, volume (V k).shade) := by
              rw [htwo, ← mul_assoc,
                ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
        _ ≤ 2 * ∑ k ∈ t₁, volume (V k).shade := by
              exact mul_le_mul_right
                (by
                  have hkeep :=
                    ShadedBody.one_sub_mul_sum_volume_shade_le_sum_discardLowShading
                      t V (c := (1 / 2 : NNReal)) (by norm_num)
                  rwa [hhalf] at hkeep)
                2
  have hstepGood : ShadedBody.multiplicity t₁ V ≤
      2 * ShadedBody.multiplicity tgood V := by
    refine ShadedBody.multiplicity_le_mul_of_sum_shade_le_of_biUnion_subset
      t₁ V tgood V 2 ?_ ht₁Mass
    exact Set.biUnion_subset_biUnion_left (fun k hk => htgoodSub hk)
  have hmassGood : 0 < ∑ k ∈ tgood, volume (V k).shade := by
    have hpos : 0 < 2 * ∑ k ∈ tgood, volume (V k).shade := hmass₁.trans_le ht₁Mass
    exact (ENNReal.mul_pos_iff.mp hpos).2
  have htgoodMul : 0 < ShadedBody.multiplicity tgood V := by
    rw [ShadedBody.multiplicity_eq_div]
    exact ENNReal.div_pos hmassGood.ne'
      (ShadedBody.volume_iUnion_shade_ne_top tgood V)
  have hcellPos : 0 < ShadedBody.multiplicity (cell x) V := by
    have hsumPos : 0 < ∑ y ∈ good, ShadedBody.multiplicity (cell y) V :=
      htgoodMul.trans_le hstep₂
    obtain ⟨y, hy, hypos⟩ := Finset.sum_pos_iff.mp hsumPos
    exact hypos.trans_le (hxmax y hy)
  have hcellNe : (cell x).Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    simp [hne, ShadedBody.multiplicity_eq_div] at hcellPos
  have hcellMass : 0 < ∑ k ∈ cell x, volume (V k).shade := by
    by_contra hne
    have hz : ∑ k ∈ cell x, volume (V k).shade = 0 := bot_unique (not_lt.mp hne)
    simp [ShadedBody.multiplicity_eq_div, hz] at hcellPos
  have hcellSub : cell x ⊆ t := by
    intro k hk
    exact ht₁t (Finset.mem_filter.mp hk).1
  have hcellBall : ∀ k ∈ cell x, ((T k).translate (-x)).carrier ⊆
      Metric.closedBall 0 1 := by
    intro k hk
    have hkt₁ : k ∈ t₁ := (Finset.mem_filter.mp hk).1
    have hgkx : g k = x := (Finset.mem_filter.mp hk).2
    have hin : (T k).carrier ⊆ Metric.closedBall x 1 := by
      rw [← hgkx]
      exact hgball k hkt₁
    rw [StickyKakeya.shadedTube_translate_carrier]
    intro z hz
    obtain ⟨w, hw, rfl⟩ := hz
    have hwx := hin hw
    rw [Metric.mem_closedBall] at hwx ⊢
    simpa [dist_eq_norm, neg_add_eq_sub, norm_sub_rev] using hwx
  have hcellFull : ((1 / 2 : NNReal) : ENNReal) *
        (ShadedBody.fullness t V : ENNReal)
      ≤ (ShadedBody.fullness (cell x)
          (fun k => ((T k).translate (-x)).toShadedBody) : ENNReal) := by
    let lam : NNReal := (1 / 2) * ShadedBody.fullness t V
    have hdens : ∀ k ∈ cell x,
        (lam : ENNReal) * volume (T k).carrier ≤ volume (T k).shade := by
      intro k hk
      have hkeep := ShadedBody.le_volume_shade_of_mem_discardLowShading
        (V := V) (c := (1 / 2 : NNReal)) (Finset.mem_filter.mp hk).1
      simpa [lam, V, ENNReal.coe_mul] using hkeep
    have hfull := le_fullness_of_dens_lower hτ0 hcellNe T hdens
    have heq : (fun k => ((T k).translate (-x)).toShadedBody) =
        fun k => (V k).translate (-x) := by
      funext k
      exact shadedTube_translate_toShadedBody (T k) (-x)
    rw [heq, ShadedBody.fullness_translate_const (cell x) V (-x)]
    simpa [lam, ENNReal.coe_mul] using hfull
  have htranslatedMass :
      0 < ∑ k ∈ cell x, volume ((T k).translate (-x)).shade := by
    simpa [MeasureTheory.measure_vadd] using hcellMass
  have htranslatedMul : ShadedBody.multiplicity (cell x)
      (fun k => ((T k).translate (-x)).toShadedBody) =
      ShadedBody.multiplicity (cell x) V := by
    simpa [V, shadedTube_translate_toShadedBody] using
      ShadedBody.multiplicity_translate_const (cell x) V (-x)
  have hmassOriginal : (∑ k ∈ t, volume (V k).shade) ≤
      2 * ∑ k ∈ t₁, volume (V k).shade := by
    have hkeep := ShadedBody.one_sub_mul_sum_volume_shade_le_sum_discardLowShading
      t V (c := (1 / 2 : NNReal)) (by norm_num)
    rw [hhalf] at hkeep
    calc
      (∑ k ∈ t, volume (V k).shade) =
          2 * (((1 / 2 : NNReal) : ENNReal) * ∑ k ∈ t, volume (V k).shade) := by
        have htwo : ((1 / 2 : NNReal) : ENNReal) = (2 : ENNReal)⁻¹ := by norm_num
        rw [htwo, ← mul_assoc,
          ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
      _ ≤ 2 * ∑ k ∈ t₁, volume (V k).shade := by gcongr
  have hmassCell : (∑ k ∈ t, volume (T k).shade) ≤
      4 * (xs.card : ENNReal) *
        ∑ k ∈ cell x, volume ((T k).translate (-x)).shade := by
    have htranslate : (∑ k ∈ cell x, volume ((T k).translate (-x)).shade) = w x := by
      simp [w, V]
    calc
      (∑ k ∈ t, volume (T k).shade) = ∑ k ∈ t, volume (V k).shade := by rfl
      _ ≤ 2 * ∑ k ∈ t₁, volume (V k).shade := hmassOriginal
      _ = 2 * ∑ y ∈ xs, w y := by rw [hsumCells]
      _ ≤ 2 * (2 * (xs.card : ENNReal) * w x) := by gcongr
      _ = 4 * (xs.card : ENNReal) *
          ∑ k ∈ cell x, volume ((T k).translate (-x)).shade := by
        rw [htranslate]
        ring
  refine ⟨cell x, hcellSub, -x,
    hcellNe, htranslatedMass, hcellBall, hcellFull, hmassCell, ?_⟩
  calc
    ShadedBody.multiplicity t V ≤ 2 * ShadedBody.multiplicity t₁ V := hstep₁
    _ ≤ 2 * (2 * ShadedBody.multiplicity tgood V) := by gcongr
    _ = 4 * ShadedBody.multiplicity tgood V := by ring
    _ ≤ 4 * (∑ y ∈ good, ShadedBody.multiplicity (cell y) V) := by gcongr
    _ ≤ 4 * ((xs.card : ENNReal) * ShadedBody.multiplicity (cell x) V) := by gcongr
    _ = 4 * (xs.card : ENNReal) *
        ShadedBody.multiplicity (cell x)
          (fun k => ((T k).translate (-x)).toShadedBody) := by
      rw [htranslatedMul]
      ring


/-- Current-API port of the historical fixed-ball two-scale product factorization.

The intermediate family is only assumed to lie in `B_R`. A selected cell is
translated into `B_1` before the second one-scale factorization, and the
coarse factor is translated back afterwards. -/
theorem exists_twoScaleProductOnly_ball (R : ℝ) (hR : 1 ≤ R)
    (hdim : Module.finrank ℝ E = 3) :
    ∃ M : ℕ, 0 < M ∧
    ∀ {δ τ θ : NNReal}, 0 < δ → δ ≤ τ → τ ≤ θ → θ ≤ 1 →
      (τ : ℝ) ≤ 1 / 4 →
    ∀ {ι κ : Type u} [DecidableEq κ] {s : Finset ι} {tτ tθ : Finset κ},
      ∀ (T : ι → ShadedTube δ E) (Tτ : κ → Tube τ E) (pτ : ι → κ)
        (Tθ : κ → Tube θ E) (pθ : κ → κ),
      (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
      IsParentFamily s (fun i => (T i).toTube) tτ Tτ pτ →
      0 < ∑ i ∈ s, volume (T i).shade →
      (∀ k ∈ tτ, (Tτ k).carrier ⊆ Metric.closedBall 0 R) →
      IsParentFamily tτ Tτ tθ Tθ pθ →
      ∃ (tm : Finset κ) (Zτ : κ → ShadedTube τ E) (Zf : ι → ShadedTube δ E)
        (u : Finset κ) (v : E) (tc : Finset κ)
        (Zc : κ → ShadedTube θ E) (Zm : κ → ShadedTube τ E),
        tm.Nonempty ∧ u.Nonempty ∧ tc.Nonempty ∧
        tm ⊆ tτ ∧ u ⊆ tm ∧ tc ⊆ tθ ∧
        (∀ k ∈ tm, (Zτ k).toTube = Tτ k) ∧
        (∀ i ∈ s, pτ i ∈ tm → (Zf i).toTube = (T i).toTube) ∧
        (∀ l ∈ tc, (Zc l).toTube = Tθ l) ∧
        (∀ k ∈ u, pθ k ∈ tc → (Zm k).toTube = (Tτ k).translate v) ∧
        (∀ k ∈ u, pθ k ∈ tc →
          (Zm k).carrier ⊆ Metric.closedBall 0 1) ∧
        ∀ k ∈ tm, ∀ l ∈ tc,
          ShadedBody.multiplicity s (fun i => (T i).toShadedBody) ≤
            (4 * (M : ENNReal)) *
              (factorTwoScales.C s.card δ u.card τ : ENNReal) *
              ShadedBody.multiplicity tc (fun j => (Zc j).toShadedBody) *
              ShadedBody.multiplicity
                (fibre (u.filter fun j => pθ j ∈ tc) pθ l)
                (fun j => (Zm j).toShadedBody) *
              ShadedBody.multiplicity
                (fibre (s.filter fun i => pτ i ∈ tm) pτ k)
                (fun i => (Zf i).toShadedBody) := by
  classical
  obtain ⟨M, hM, hcell⟩ := exists_unitBallCell_productInput (E := E) R hR
  refine ⟨M, hM, ?_⟩
  intro δ τ θ hδ hδτ hτθ hθ1 hτ4 ι κ _ s tτ tθ
    T Tτ pτ Tθ pθ hball hfine hmass hballτ hcoarse
  obtain ⟨tm, htm, Zτ, Zf, htmne, hmassτ, hZτtube, hZftube, hprod1⟩ :=
    exists_oneScaleProductOnly hdim hδ hδτ (hτθ.trans hθ1)
      T Tτ pτ hball hfine hmass
  have hτ0 : 0 < τ := hδ.trans_le hδτ
  have hZτball : ∀ k ∈ tm, (Zτ k).carrier ⊆ Metric.closedBall 0 R := by
    intro k hk
    rw [hZτtube k hk]
    exact hballτ k (htm hk)
  obtain ⟨u, hu, v, hune, hmassu, hballu, _hfullu, _hmassRet, hmultu⟩ :=
    hcell hτ0 hτ4 tm Zτ hmassτ hZτball
  have hparent2 : IsParentFamily u (fun k => ((Zτ k).translate v).toTube)
      tθ (fun l => (Tθ l).translate v) pθ := by
    refine ⟨?_, ?_, ?_⟩
    · intro k hk
      exact hcoarse.mapsTo k (htm (hu hk))
    · intro l hl l' hl' heq
      apply hcoarse.injOn hl hl'
      apply le_antisymm
      · exact le_of_translate_le_translate heq.le
      · exact le_of_translate_le_translate heq.ge
    · intro k hk
      rw [StickyKakeya.shadedTube_translate_toTube, hZτtube k (hu hk)]
      exact translate_le_translate v (hcoarse.le_parent k (htm (hu hk)))
  obtain ⟨tc, htc, ZcTranslated, Zm, htcne, _hmassc,
      hZctube, hZmtube, hprod2⟩ :=
    exists_oneScaleProductOnly hdim hτ0 hτθ hθ1
      (fun k => (Zτ k).translate v) (fun l => (Tθ l).translate v) pθ
      hballu hparent2 hmassu
  let Zc : κ → ShadedTube θ E := fun l => (ZcTranslated l).translate (-v)
  have hZcTube : ∀ l ∈ tc, (Zc l).toTube = Tθ l := by
    intro l hl
    dsimp [Zc]
    rw [StickyKakeya.shadedTube_translate_toTube, hZctube l hl]
    exact StickyKakeya.tube_translate_neg_cancel (Tθ l) v
  have hZmTube : ∀ k ∈ u, pθ k ∈ tc →
      (Zm k).toTube = (Tτ k).translate v := by
    intro k hk hpk
    calc
      (Zm k).toTube = ((Zτ k).translate v).toTube := hZmtube k hk hpk
      _ = ((Zτ k).toTube).translate v :=
        StickyKakeya.shadedTube_translate_toTube (Zτ k) v
      _ = (Tτ k).translate v := congrArg (fun W : Tube τ E => W.translate v)
        (hZτtube k (hu hk))
  have hZmBall : ∀ k ∈ u, pθ k ∈ tc →
      (Zm k).carrier ⊆ Metric.closedBall 0 1 := by
    intro k hk hpk
    rw [hZmtube k hk hpk]
    exact hballu k hk
  have hback : ShadedBody.multiplicity tc (fun l => (Zc l).toShadedBody) =
      ShadedBody.multiplicity tc (fun l => (ZcTranslated l).toShadedBody) := by
    simpa [Zc, shadedTube_translate_toShadedBody] using
      ShadedBody.multiplicity_translate_const tc
        (fun l => (ZcTranslated l).toShadedBody) (-v)
  refine ⟨tm, Zτ, Zf, u, v, tc, Zc, Zm, htmne, hune, htcne,
    htm, hu, htc, hZτtube, hZftube, hZcTube, hZmTube, hZmBall, ?_⟩
  intro k hk l hl
  calc
    ShadedBody.multiplicity s (fun i => (T i).toShadedBody)
        ≤ (factorOneScale.C s.card δ : ENNReal) *
          ShadedBody.multiplicity tm (fun j => (Zτ j).toShadedBody) *
          ShadedBody.multiplicity
            (fibre (s.filter fun i => pτ i ∈ tm) pτ k)
            (fun i => (Zf i).toShadedBody) := hprod1 k hk
    _ ≤ (factorOneScale.C s.card δ : ENNReal) *
          (4 * (M : ENNReal) *
            ShadedBody.multiplicity u
              (fun j => ((Zτ j).translate v).toShadedBody)) *
          ShadedBody.multiplicity
            (fibre (s.filter fun i => pτ i ∈ tm) pτ k)
            (fun i => (Zf i).toShadedBody) := by gcongr
    _ ≤ (factorOneScale.C s.card δ : ENNReal) *
          (4 * (M : ENNReal) *
            ((factorOneScale.C u.card τ : ENNReal) *
              ShadedBody.multiplicity tc
                (fun j => (ZcTranslated j).toShadedBody) *
              ShadedBody.multiplicity
                (fibre (u.filter fun j => pθ j ∈ tc) pθ l)
                (fun j => (Zm j).toShadedBody))) *
          ShadedBody.multiplicity
            (fibre (s.filter fun i => pτ i ∈ tm) pτ k)
            (fun i => (Zf i).toShadedBody) := by
            gcongr
            exact hprod2 l hl
    _ = _ := by
      rw [hback, factorTwoScales.C, ENNReal.coe_mul]
      ring

omit [Nontrivial E] in
/-- Back-translation is lossless on a fixed middle index set.  This is the
translation bridge needed by `IsTwoScaleFactors.mid_tube`; enlarging the index
set by zero-extension is a separate operation. -/
theorem backtranslate_middle_preserves {tau : NNReal} {kappa : Type u}
    [DecidableEq kappa] (t : Finset kappa) (Tmid : kappa → Tube tau E)
    (Ymid : kappa → ShadedTube tau E) (v : E)
    (htube : ∀ k ∈ t, (Ymid k).toTube = (Tmid k).translate v) :
    (∀ k ∈ t, ((Ymid k).translate (-v)).toTube = Tmid k) ∧
      ShadedBody.fullness t
          (fun k => ((Ymid k).translate (-v)).toShadedBody) =
        ShadedBody.fullness t (fun k => (Ymid k).toShadedBody) ∧
      ShadedBody.multiplicity t
          (fun k => ((Ymid k).translate (-v)).toShadedBody) =
        ShadedBody.multiplicity t (fun k => (Ymid k).toShadedBody) := by
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    rw [StickyKakeya.shadedTube_translate_toTube, htube k hk]
    exact StickyKakeya.tube_translate_neg_cancel (Tmid k) v
  · simp [shadedTube_translate_toShadedBody]
  · simpa [shadedTube_translate_toShadedBody] using
      ShadedBody.multiplicity_translate_const t
        (fun k => (Ymid k).toShadedBody) (-v)

end Kakeya.ml1Boot

#print axioms Kakeya.ml1Boot.exists_unitBallCell_productInput
#print axioms Kakeya.ml1Boot.exists_twoScaleProductOnly_ball
#print axioms Kakeya.ml1Boot.backtranslate_middle_preserves
