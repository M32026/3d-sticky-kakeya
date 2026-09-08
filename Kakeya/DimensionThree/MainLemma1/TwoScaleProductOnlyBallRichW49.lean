/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.TwoScaleRichW49
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

/-- Map-only form of the current carrier-weighted fibre-fullness selection theorem. -/
private theorem exists_filter_fullness_ge_of_mapsTo_ball_w49
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

/-- A positive-mass shaded tube family in a fixed ball has a translated unit-ball subfamily
which retains half the global average fullness and controls the original multiplicity up to the
fixed cell-count loss.

The selected family is chosen only after the shading is known.  This is the product-facing
counterpart of `Kakeya.ml1Boot.multiplicity_le_of_ball_of_unitBall`: here the controlling cell is
returned because it is the input to the second product-only factorization. -/
theorem exists_unitBallCell_productInput_rich_w49 (R : ℝ) (hR : 1 ≤ R)
    : ∃ M : ℕ, 0 < M ∧
    ∀ {τ : NNReal}, 0 < τ → (τ : ℝ) ≤ 1 / 4 →
    ∀ {κ : Type u} (t : Finset κ) (T : κ → ShadedTube τ E),
    0 < ∑ k ∈ t, volume (T k).shade →
    (∀ k ∈ t, (T k).carrier ⊆ Metric.closedBall 0 R) →
    ∃ u : Finset κ, u ⊆ t ∧ ∃ v : E,
      u.Nonempty ∧
      0 < ∑ k ∈ u, volume ((T k).translate v).shade ∧
      (∀ k ∈ u, ((T k).translate v).carrier ⊆ Metric.closedBall 0 1) ∧
      (∀ k ∈ u,
        (((1 / 2 : NNReal) : ENNReal) *
            (ShadedBody.fullness t (fun j => (T j).toShadedBody) : ENNReal)) *
          volume ((T k).translate v).carrier ≤
            volume ((T k).translate v).shade) ∧
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
  have hcellDensity : ∀ k ∈ cell x,
      (((1 / 2 : NNReal) : ENNReal) *
          (ShadedBody.fullness t (fun j => (T j).toShadedBody) : ENNReal)) *
        volume ((T k).translate (-x)).carrier ≤
          volume ((T k).translate (-x)).shade := by
    intro k hk
    have hkeep := ShadedBody.le_volume_shade_of_mem_discardLowShading
      (V := V) (c := (1 / 2 : NNReal)) (Finset.mem_filter.mp hk).1
    simpa [V, MeasureTheory.measure_vadd] using hkeep
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
    hcellNe, htranslatedMass, hcellBall, hcellDensity, hcellFull, hmassCell, ?_⟩
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

/-- Two product-only factorizations when the intermediate tubes lie in a fixed ball `B_R`.

After the first factorization, `exists_unitBallCell_productInput` selects and translates the
actual intermediate block.  The second factorization is run on that translated block.  Its
families therefore have tubes `Tτ.translate v` and `Tθ.translate v`; the common translation `v`
is returned explicitly so analytic consumers can transport them back to the fixed hierarchy.

The product loss is the two factoring constants times `4 M`, where `M` is the fixed cell count.
The fine and middle refinements remain independent, and the product holds for every retained
fine parent and every retained coarse parent. -/
theorem exists_twoScaleProductOnly_ball_rich_w49 (R : ℝ) (hR : 1 ≤ R)
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
      ∃ (tm : Finset κ) (sf : Finset ι)
        (Zτ : κ → ShadedTube τ E) (Zf : ι → ShadedTube δ E)
        (u : Finset κ) (v : E) (tc sm : Finset κ)
        (Zc : κ → ShadedTube θ E) (Zm : κ → ShadedTube τ E) (kf lm : κ),
        tm.Nonempty ∧ u.Nonempty ∧ tc.Nonempty ∧
        kf ∈ tm ∧ lm ∈ tc ∧
        tm ⊆ tτ ∧ sf ⊆ s ∧ u ⊆ tm ∧ sm ⊆ u ∧ tc ⊆ tθ ∧
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
        (∀ k, (Zτ k).toTube = Tτ k) ∧
        (∀ i, (Zf i).toTube = (T i).toTube) ∧
        (∀ l, (Zc l).toTube = Tθ l) ∧
        (∀ k, (Zm k).toTube = (Tτ k).translate v) ∧
        (∀ k ∈ u, (Zm k).carrier ⊆ Metric.closedBall 0 1) ∧
        ((1 / 2 : NNReal) : ENNReal) *
            ShadedBody.fullness tm (fun k => (Zτ k).toShadedBody)
          ≤ ShadedBody.fullness u
              (fun k => ((Zτ k).translate v).toShadedBody) ∧
        (∑ k ∈ tm, volume (Zτ k).shade) ≤
          4 * (M : ENNReal) *
            ∑ k ∈ u, volume ((Zτ k).translate v).shade ∧
        (factorOneScale.C s.card δ)⁻¹ *
            ShadedBody.fullness s (fun i => (T i).toShadedBody)
          ≤ ShadedBody.fullness tm (fun k => (Zτ k).toShadedBody) ∧
        ShadedBody.IsCRefinement sf
          (fun i => (Zf i).toShadedBody) s (fun i => (T i).toShadedBody)
          (factorOneScale.C s.card δ)⁻¹ ∧
        (factorOneScale.C u.card τ)⁻¹ * (((1 / 2 : NNReal) : ENNReal) *
            ShadedBody.fullness tm (fun k => (Zτ k).toShadedBody))
          ≤ ShadedBody.fullness tc (fun l => (Zc l).toShadedBody) ∧
        ShadedBody.IsCRefinement sm
          (fun k => (Zm k).toShadedBody) u
          (fun k => ((Zτ k).translate v).toShadedBody)
          (factorOneScale.C u.card τ)⁻¹ ∧
        ShadedBody.fullness sf (fun i => (Zf i).toShadedBody) ≤
          ShadedBody.fullness (fibre sf pτ kf) (fun i => (Zf i).toShadedBody) ∧
        ShadedBody.fullness sm (fun k => (Zm k).toShadedBody) ≤
          ShadedBody.fullness (fibre sm pθ lm) (fun k => (Zm k).toShadedBody) ∧
        (∀ k ∈ tm, ∀ l ∈ tc,
          ((fibre sf pτ k).card : ENNReal) * ((fibre sm pθ l).card : ENNReal) *
            (tc.card : ENNReal) ≤ 4 * (s.card : ENNReal)) ∧
        ∀ k ∈ tm, ∀ l ∈ tc,
          ShadedBody.multiplicity s (fun i => (T i).toShadedBody) ≤
            (4 * (M : ENNReal)) *
              (factorTwoScales.C s.card δ u.card τ : ENNReal)
              * ShadedBody.multiplicity tc (fun j => (Zc j).toShadedBody)
              * ShadedBody.multiplicity (fibre sm pθ l)
                  (fun j => (Zm j).toShadedBody)
              * ShadedBody.multiplicity (fibre sf pτ k)
                  (fun i => (Zf i).toShadedBody) := by
  classical
  obtain ⟨M, hM, hcell⟩ := exists_unitBallCell_productInput_rich_w49 (E := E) R hR
  refine ⟨M, hM, ?_⟩
  intro δ τ θ hδ hδτ hτθ hθ1 hτ4 ι κ _ s tτ tθ T Tτ pτ Tθ pθ hball hfine
    hmass hballτ hcoarse
  obtain ⟨tm, htm, sf, hsf, Zτ, Zf, htmne, hsfmaps, htmfibne, hfineCard,
      hmassτ, hmassf, hZτtube, hZftube, hfullτ, hrefFine, hprod1⟩ :=
    exists_oneScaleProductOnly_rich_w49 hdim hδ hδτ (hτθ.trans hθ1)
      T Tτ pτ hball hfine hmass
  have hτ0 : 0 < τ := hδ.trans_le hδτ
  have hZτball : ∀ k ∈ tm, (Zτ k).carrier ⊆ Metric.closedBall 0 R := by
    intro k hk
    rw [show (Zτ k).carrier = (Tτ k).carrier by
      exact congrArg (fun W : Tube τ E => W.carrier) (hZτtube k)]
    exact hballτ k (htm hk)
  obtain ⟨u, hu, v, hune, hmassu, hballu, _hdensityu, hfullu, hmassuRet, hmultu⟩ :=
    hcell hτ0 hτ4 tm Zτ hmassτ hZτball
  have hparent2 : IsParentFamily u (fun k => ((Zτ k).translate v).toTube)
      tθ (fun l => (Tθ l).translate v) pθ := by
    refine ⟨?_, ?_, ?_⟩
    · intro k hk
      exact hcoarse.mapsTo k (htm (hu hk))
    · intro l hl l' hl' heq
      apply hcoarse.injOn hl hl'
      have hback := congrArg (fun W : ConvexSpaceBody E => W.translate (-v)) heq
      change (ConvexSpaceBody.translate (Tθ l).toConvexSpaceBody v).translate (-v) =
        (ConvexSpaceBody.translate (Tθ l').toConvexSpaceBody v).translate (-v) at hback
      simpa only [ConvexSpaceBody.neg_translate_cancel] using hback
    · intro k hk
      have hle := hcoarse.le_parent k (htm (hu hk))
      have hbody : (Zτ k).toConvexSpaceBody = (Tτ k).toConvexSpaceBody :=
        congrArg (fun W : Tube τ E => W.toConvexSpaceBody) (hZτtube k)
      change ConvexSpaceBody.translate (Zτ k).toConvexSpaceBody v ≤
        ConvexSpaceBody.translate (Tθ (pθ k)).toConvexSpaceBody v
      rw [hbody]
      exact translate_le_translate v hle
  obtain ⟨tc, htc, sm, hsm, Zc, Zm, htcne, hsmmaps, htcfibne, hmidCard,
      _hmassc, hmassm, hZctube, hZmtube, hfullc, hrefMid, hprod2⟩ :=
    exists_oneScaleProductOnly_rich_w49 hdim hτ0 hτθ hθ1
      (fun k => (Zτ k).translate v) (fun l => (Tθ l).translate v) pθ
      hballu hparent2 hmassu
  let ZcBack : κ → ShadedTube θ E := fun l => (Zc l).translate (-v)
  have hfullMiddle : (factorOneScale.C u.card τ)⁻¹ *
        (((1 / 2 : NNReal) : ENNReal) *
          ShadedBody.fullness tm (fun k => (Zτ k).toShadedBody))
      ≤ ShadedBody.fullness tc (fun l => (ZcBack l).toShadedBody) := by
    have hfullcE := ENNReal.coe_le_coe.mpr hfullc
    rw [ENNReal.coe_mul] at hfullcE
    have hback : ShadedBody.fullness tc (fun l => (ZcBack l).toShadedBody) =
        ShadedBody.fullness tc (fun l => (Zc l).toShadedBody) := by
      simp [ZcBack]
    rw [hback]
    calc
      (factorOneScale.C u.card τ)⁻¹ *
          (((1 / 2 : NNReal) : ENNReal) *
            ShadedBody.fullness tm (fun k => (Zτ k).toShadedBody))
          ≤ (factorOneScale.C u.card τ)⁻¹ *
            ShadedBody.fullness u (fun k => ((Zτ k).translate v).toShadedBody) := by
              gcongr
      _ ≤ ShadedBody.fullness tc (fun l => (Zc l).toShadedBody) := hfullcE
  have hgoodFine : ∃ k ∈ tm,
      ShadedBody.fullness sf (fun i => (Zf i).toShadedBody) ≤
        ShadedBody.fullness (fibre sf pτ k) (fun i => (Zf i).toShadedBody) := by
    obtain ⟨k, hk, hfull⟩ := exists_filter_fullness_ge_of_mapsTo_ball_w49
      (fun i => (Zf i).toShadedBody) pτ htmne hsfmaps
      (ShadedBody.sum_volume_carrier_ne_zero_of_sum_shade_ne_zero sf
        (fun i => (Zf i).toShadedBody) hmassf.ne')
    exact ⟨k, hk, by simpa only [fibre] using hfull⟩
  have hgoodMid : ∃ l ∈ tc,
      ShadedBody.fullness sm (fun k => (Zm k).toShadedBody) ≤
        ShadedBody.fullness (fibre sm pθ l) (fun k => (Zm k).toShadedBody) := by
    obtain ⟨l, hl, hfull⟩ := exists_filter_fullness_ge_of_mapsTo_ball_w49
      (fun k => (Zm k).toShadedBody) pθ htcne hsmmaps
      (ShadedBody.sum_volume_carrier_ne_zero_of_sum_shade_ne_zero sm
        (fun k => (Zm k).toShadedBody) hmassm.ne')
    exact ⟨l, hl, by simpa only [fibre] using hfull⟩
  obtain ⟨kf, hkf, hgoodFine⟩ := hgoodFine
  obtain ⟨lm, hlm, hgoodMid⟩ := hgoodMid
  refine ⟨tm, sf, Zτ, Zf, u, v, tc, sm, ZcBack, Zm, kf, lm,
    htmne, hune, htcne, hkf, hlm,
    htm, hsf, hu, hsm, htc, hsfmaps, htmfibne, hfineCard, hsmmaps, htcfibne,
    hmidCard, hmassf, hmassm, hZτtube, hZftube, ?_, ?_, ?_, hfullu, hmassuRet,
    hfullτ, hrefFine,
    hfullMiddle, hrefMid, hgoodFine, hgoodMid, ?_, ?_⟩
  · intro l
    change ((Zc l).toTube.translate (-v)) = Tθ l
    rw [hZctube l]
    exact StickyKakeya.tube_translate_neg_cancel (Tθ l) v
  · intro k
    have h := hZmtube k
    have hbase := hZτtube k
    rw [StickyKakeya.shadedTube_translate_toTube, hbase] at h
    exact h
  · intro k hk
    have h := congrArg (fun W : Tube τ E => W.carrier) (hZmtube k)
    rw [h]
    exact hballu k hk
  · intro k hk l hl
    exact active_fibre_product_card_le hsf (hsm.trans hu) hsfmaps hsmmaps
      hfineCard hmidCard hk hl
  · intro k hk l hl
    calc
      ShadedBody.multiplicity s (fun i => (T i).toShadedBody)
          ≤ (factorOneScale.C s.card δ : ENNReal)
            * ShadedBody.multiplicity tm (fun j => (Zτ j).toShadedBody)
            * ShadedBody.multiplicity (fibre sf pτ k)
                (fun i => (Zf i).toShadedBody) := hprod1 k hk
      _ ≤ (factorOneScale.C s.card δ : ENNReal)
            * (4 * (M : ENNReal) *
              ShadedBody.multiplicity u (fun j => ((Zτ j).translate v).toShadedBody))
            * ShadedBody.multiplicity (fibre sf pτ k)
                (fun i => (Zf i).toShadedBody) := by gcongr
      _ ≤ (factorOneScale.C s.card δ : ENNReal)
            * (4 * (M : ENNReal) *
              ((factorOneScale.C u.card τ : ENNReal)
                * ShadedBody.multiplicity tc (fun j => (ZcBack j).toShadedBody)
                * ShadedBody.multiplicity (fibre sm pθ l)
                    (fun j => (Zm j).toShadedBody)))
            * ShadedBody.multiplicity (fibre sf pτ k)
                (fun i => (Zf i).toShadedBody) := by
              gcongr
              have hback : ShadedBody.multiplicity tc
                    (fun j => (ZcBack j).toShadedBody) =
                  ShadedBody.multiplicity tc (fun j => (Zc j).toShadedBody) := by
                simpa [ZcBack, shadedTube_translate_toShadedBody] using
                  ShadedBody.multiplicity_translate_const tc
                    (fun j => (Zc j).toShadedBody) (-v)
              rw [hback]
              exact hprod2 l hl
      _ = _ := by
        rw [factorTwoScales.C, ENNReal.coe_mul]
        ring

end Kakeya.ml1Boot

#print axioms Kakeya.ml1Boot.exists_unitBallCell_productInput_rich_w49
#print axioms Kakeya.ml1Boot.exists_twoScaleProductOnly_ball_rich_w49
