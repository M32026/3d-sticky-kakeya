/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.PartBOuterFullnessInputs

/-!
# GWZ 6.6(B): the outer fullness clause, over the plank-presented Proposition-5.1 output

steps, **item 1, closed**.

`Kakeya.factoringAndMultPropGlobal_of_remark53` needs, of its outer family,
`δ ^ ηₒ ≤ λ(𝒲, Y_𝒲)`.  Over the family GWZ Proposition 5.1 actually constructs for Part (B),
presented as genuine `Kakeya.ShadedPlank a b hab hb1`s in the fixed radius-`4` window by
`Kakeya.collarPlank`, that is
`Kakeya.PartBLoss.exists_threshold_partB_outer_fullness` below.

## The chain, and where each link comes from

`Kakeya.le_fullness_collarPlank_of_sum_le` reduces the clause to `δ ^ ηₒ ≤ c · M_env⁻¹` with
`c = c_full · C⁻¹ · λ(selected)²`.  The four factors are then bounded separately and multiplied:

| factor | lemma |
|---|---|
| `c_full` | `Kakeya.PartBLoss.exists_threshold_rpow_le_fullnessConstant`, whose `N`-, `M`-, `w`- and `0 < Rc` inputs are `exists_threshold_fineVolumeRatio_exponent_succ_le_rpow_neg`, `exists_threshold_card_le_rpow_neg_seven` with `selectedOuterScaleFamily_innerSet_card_le`, `ShadedBody.le_selectedOuterScale` with `selectedOuterScale_le`, and `ShadedBody.factoringCoreAtScaleUniformRefinementConstant_pos` |
| `C⁻¹` | `exists_threshold_rpow_le_inv_remark53ThickConst`, fed by the datum's own `Cfib, CF ≤ δ ^ (-η)` |
| `λ(selected)²` | `rpow_le_sq_of_selection`, fed by `ShadedBody.…SelectScaleResult.selection_fullness` and `exists_threshold_outerScaleSelectionConstant_le_rpow_neg` |
| `M_env⁻¹` | `exists_threshold_rpow_le_inv` — `M_env` is absolute |
| the product | `rpow_le_mul_four`, then `rpow_le_of_coe_rpow_le` to descend to `ℝ≥0` |

## The two exponent choices

`η := min (ηₒ/24) (ηₒ/32)`.  The binding constraint is `C⁻¹`, which consumes `η = e/6` of budget at
`e = ηₒ/4`, i.e. `ηₒ/24`; the selection bound needs `2 · (η + ηₒ/16) ≤ ηₒ/4`, i.e. `η ≤ ηₒ/32`.
`η` is picked last, as a `min` of upper bounds, so both are free.  **`ε` is untouched and no
structure field is involved.**

`Cw` is quantified *before* the threshold, because `M_env` depends on it and the absorption of an
absolute constant is a threshold on `δ`.  That is the right order for the consumer: at the ML2
eccentric call site `Cw = 128` is absolute
(`Kakeya.ML2Reduction.PlankFactoringData.toGlobalPlankFactorization`), so a `Cw`-dependent threshold
costs nothing.
-/

@[expose] public section

open MeasureTheory Metric Convexity

open scoped ENNReal NNReal

noncomputable section

universe u v

namespace Kakeya

namespace PartBLoss

open _root_.ShadedBody

/-- **GWZ 6.6(B)'s outer fullness clause, on the plank-presented Proposition-5.1 output.**

Every hypothesis is one Proposition 6.6(B) already carries, plus the two that
`Kakeya.Section6PartBData.exists_prop51SelectScale` adds (`δ + 2a ≤ 1` and nonempty coarse fibres)
and the plank-dimension datum `IsPlankOfDimensions Cw a b (D.factor.body x)`, whose producer is
`Kakeya.GlobalPlankFactorization.exists_isPlankFamilyOfDimensions`.  Leaf-scale essential
distinctness of the fine family is used exactly once, for the a-priori count `|𝒯| ≲ δ ^ (-6)` that
makes the fullness constant's `M`-hypothesis available. -/
theorem exists_threshold_partB_outer_fullness {ηₒ : ℝ} (hηₒ : 0 < ηₒ)
    (Cw : ℝ≥0) (hCw : 1 ≤ Cw) :
    ∃ δ₀ : ℝ≥0, 0 < δ₀ ∧ ∃ η > (0 : ℝ),
      ∀ {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {ι : Type u} {q : Finset ι} {δ : ℝ≥0}
        {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
        {κ : Type v} {coarseSet : Finset κ} {ρ : ℝ≥0}
        {R : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))} {m Cfib CF C₀ : ℝ≥0}
        (D : Section6PartBData a b hab hb1 q T coarseSet R m Cfib CF C₀),
        0 < δ → δ ≤ δ₀ → (δ : ℝ) ≤ 1 / 2 → 0 < ρ → ρ ≤ 1 → δ ≤ a → 0 < b →
        (∀ i ∈ q, ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
          ⊆ Metric.closedBall 0 1) →
        0 < ∑ i ∈ q, volume (T i).shade →
        δ + 2 * a ≤ 1 →
        (∀ x ∈ D.factor.cells, (D.factor.coarseFibre x).Nonempty) →
        (∀ x ∈ D.factor.cells, IsPlankOfDimensions Cw a b (D.factor.body x)) →
        (q : Set ι).Pairwise (fun i j =>
          _root_.IsEssentiallyDistinct ((T i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
            ((T j).carrier : Set (EuclideanSpace ℝ (Fin 3)))) →
        Cfib ≤ δ ^ (-η) → CF ≤ δ ^ (-η) →
        (δ : ℝ≥0) ^ η ≤ ShadedBody.fullness q (fun i => (T i).toShadedBody) →
        ∃ (ts : Finset D.factor.Cell) (W : D.factor.Cell → ShadedPlank a b hab hb1),
          ts ⊆ D.factor.cells ∧
          (∀ j ∈ ts, ((W j).carrier : Set (EuclideanSpace ℝ (Fin 3)))
            ⊆ Metric.closedBall 0 ((plankWindowRadius : ℝ≥0) : ℝ)) ∧
          (δ : ℝ≥0) ^ ηₒ ≤ ShadedBody.fullness ts (fun j => (W j).toShadedBody) := by
  classical
  -- the four factor tolerances
  have he4 : (0 : ℝ) < ηₒ / 4 := by positivity
  set Menv : ℝ≥0 :=
    flatPrismEnvelopeVolumeRatio.C (windowPlankEnvelope.windowConst plankWindowRadius Cw)
    with hMenvdef
  have hMenv1 : 1 ≤ Menv := flatPrismEnvelopeVolumeRatio.one_le _
  obtain ⟨d1, hd1, hFC⟩ := exists_threshold_rpow_le_fullnessConstant he4
  obtain ⟨d2, hd2, hNb⟩ :=
    exists_threshold_fineVolumeRatio_exponent_succ_le_rpow_neg.{u, v}
      (show (0 : ℝ) < (ηₒ / 4) / 12 by positivity)
  obtain ⟨d3, hd3, hMb⟩ := exists_threshold_card_le_rpow_neg_seven.{u}
  obtain ⟨d4, hd4, hCb⟩ := exists_threshold_rpow_le_inv_remark53ThickConst he4
  obtain ⟨d5, hd5, hEb⟩ := exists_threshold_rpow_le_inv Menv hMenv1 he4
  obtain ⟨d6, hd6, hSb⟩ :=
    exists_threshold_outerScaleSelectionConstant_le_rpow_neg
      (show (0 : ℝ) < ηₒ / 16 by positivity)
  refine ⟨min (min (min d1 d2) (min d3 d4)) (min (min d5 d6) 1),
    lt_min (lt_min (lt_min hd1 hd2) (lt_min hd3 hd4)) (lt_min (lt_min hd5 hd6) one_pos),
    min (ηₒ / 24) (ηₒ / 32), lt_min (by positivity) (by positivity), ?_⟩
  intro a b hab hb1 ι q δ T κ coarseSet ρ R m Cfib CF C₀ D
    hδ0 hδ hδhalf hρ0 hρ1 hδa hb0 hball hmass hsmall hcfne hdimK hEDq hCfib hCF hfull
  -- unwind the threshold
  have hδ1 : δ ≤ 1 := hδ.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hδd1 : δ ≤ d1 :=
    hδ.trans (((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_left _ _))
  have hδd2 : δ ≤ d2 :=
    hδ.trans (((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_right _ _))
  have hδd3 : δ ≤ d3 :=
    hδ.trans (((min_le_left _ _).trans (min_le_right _ _)).trans (min_le_left _ _))
  have hδd4 : δ ≤ d4 :=
    hδ.trans (((min_le_left _ _).trans (min_le_right _ _)).trans (min_le_right _ _))
  have hδd5 : δ ≤ d5 :=
    hδ.trans (((min_le_right _ _).trans (min_le_left _ _)).trans (min_le_left _ _))
  have hδd6 : δ ≤ d6 :=
    hδ.trans (((min_le_right _ _).trans (min_le_left _ _)).trans (min_le_right _ _))
  have ha0 : 0 < a := lt_of_lt_of_le hδ0 hδa
  have ha1 : a ≤ 1 := hab.trans hb1
  have hδE1 : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1
  -- the Proposition-5.1 input and output
  set input := D.section6SelectScaleInput hδ0 hδhalf hδa le_rfl hball hmass with hinput
  have Q := D.prop51SelectScaleOfDatum input hδ0 hρ0 hρ1 hsmall hcfne
  have hcore := Q.core
  set F' := ShadedBody.selectedOuterScaleFamily D.toFineProp51Family input.hδ input.hdisc
    input.hδB input.hupper input.hmass with hF'
  set Dvr := input.volumeRatio.restrictOuter _
    ((ShadedBody.outerScaleSelection D.toFineProp51Family input.hδ input.hdisc
      input.hδB input.hupper input.hmass).selected_subset.trans
        D.toFineProp51Family.innerSet_image_parent_subset_outerSet) with hDvr
  set w := ShadedBody.selectedOuterScale D.toFineProp51Family input.hδ input.hdisc
    input.hδB input.hupper input.hmass with hwdef
  set O := ShadedBody.outerThickFamilyAtScale F' input.hδ (input.hdisc.restrictOuter _) Dvr w
    Q.scale_pos with hO
  -- the selected outer cells are cells of the datum
  have hsubSelected : F'.outerSet ⊆ D.factor.cells := by
    rw [hF']
    simpa [ShadedBody.selectedOuterScaleFamily,
      ShadedBody.FactorFamily.restrictOuter_outerSet] using
      ((ShadedBody.outerScaleSelection D.toFineProp51Family input.hδ input.hdisc
        input.hδB input.hupper input.hmass).selected_subset.trans
          D.toFineProp51Family.innerSet_image_parent_subset_outerSet)
  have hwin : ∀ j ∈ F'.outerSet,
      ((F'.outerBody j).carrier : Set (EuclideanSpace ℝ (Fin 3)))
        ⊆ Metric.closedBall 0 ((plankWindowRadius : ℝ≥0) : ℝ) := by
    intro j hj
    exact D.body_carrier_subset_window (hsubSelected hj)
  have hdimSel : ∀ j ∈ F'.outerSet, IsPlankOfDimensions Cw a b (F'.outerBody j) := by
    intro j hj
    exact hdimK j (hsubSelected hj)
  have hpres := isCollarPresentable_outerThickFamilyAtScale F' input.hδ
    (input.hdisc.restrictOuter _) Dvr w Q.scale_pos hcore hwin hdimSel
  have houtsub := hcore.outerSet_subset
  -- the selected family carries positive shading mass, hence a nonempty productive output
  have hselmass : 0 < ∑ i ∈ F'.innerSet, volume (F'.innerBody i).shade := by
    have hpos := input.hmass.trans_le Q.selection_mass
    exact pos_of_mul_pos_right hpos bot_le
  have htsne : O.outerSet.Nonempty := hcore.outerSet_nonempty_of_input_mass_pos hselmass
  refine ⟨O.outerSet,
    fun x => collarPlank Kakeya.Section6PartBData.one_le_plankWindowRadius hCw hab hb1 (F'.outerBody x) (O.outerBody x),
    houtsub.trans hsubSelected, ?_, ?_⟩
  · intro j hj
    exact collarPlank_carrier_subset_window Kakeya.Section6PartBData.one_le_plankWindowRadius
      hCw hab hb1 (O.outerBody j) (hwin j (houtsub hj))
  -- the fullness clause
  · set lam' : ℝ≥0 := ShadedBody.fullness F'.innerSet F'.innerBody with hlam'
    set cfull : ℝ≥0 := ShadedBody.factoringCoreAtScaleUniformFullnessConstant 3
      F'.innerSet.card Dvr.exponent w with hcfull
    set Cth : ℝ≥0 := Kakeya.Section6PartBData.remark53ThickConst Cfib CF with hCth
    have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
    have hCthne : Cth ≠ 0 := by
      rw [hCth, Kakeya.Section6PartBData.remark53ThickConst]
      have h1 : (0 : ℝ≥0) < Cfib := lt_of_lt_of_le zero_lt_one D.decomp.one_le_Cfib
      have h2 : (0 : ℝ≥0) < CF := lt_of_lt_of_le zero_lt_one D.factor.one_le_CF
      have h3 : (0 : ℝ≥0) < Kakeya.coarseTubeVolumeRatio :=
        lt_of_lt_of_le zero_lt_one Kakeya.one_le_coarseTubeVolumeRatio
      have h4 : (0 : ℝ≥0) < Metric.volume_comparison.C 3 := Metric.volume_comparison.C_pos 3
      exact ne_of_gt (mul_pos (mul_pos (mul_pos (pow_pos h1 2) (pow_pos h3 2)) h2) (pow_pos h4 2))
    -- Proposition 5.1's summed outer fullness, with an `ℝ≥0` coefficient
    have hthick := hcore.thick_fullness
    rw [hfr] at hthick
    have hsum : (((cfull * Cth⁻¹ * lam' ^ 2 : ℝ≥0)) : ENNReal)
        * (∑ x ∈ O.outerSet, volume (O.outerBody x).carrier)
        ≤ ∑ x ∈ O.outerSet, volume (O.outerBody x).shade := by
      refine le_trans (le_of_eq ?_) hthick
      rw [ENNReal.coe_mul, ENNReal.coe_mul, ENNReal.coe_inv hCthne, ENNReal.coe_pow]
    -- the bridge
    have hbridge := le_fullness_collarPlank_of_sum_le Kakeya.Section6PartBData.one_le_plankWindowRadius hCw hab hb1
      ha0 hb0 htsne F'.outerBody O.outerBody hpres
      (fun x hx => hdimSel x (houtsub hx)) hsum
    refine le_trans ?_ hbridge
    -- the four factor bounds
    have hη24 : min (ηₒ / 24) (ηₒ / 32) ≤ ηₒ / 24 := min_le_left _ _
    have hη32 : min (ηₒ / 24) (ηₒ / 32) ≤ ηₒ / 32 := min_le_right _ _
    have hselpos := input.hmass.trans_le Q.selection_mass
    have hselC0 : ShadedBody.outerScaleSelectionConstant δ a ≠ 0 := by
      have h := pos_of_mul_pos_left hselpos bot_le
      intro hz
      rw [hz] at h
      simp at h
    -- B: the Remark-5.3 thick constant
    have hCfibb : Cfib ≤ δ ^ (-((ηₒ / 4) / 6)) := by
      refine hCfib.trans (NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 ?_)
      have : (ηₒ / 4) / 6 = ηₒ / 24 := by ring
      rw [this]
      linarith [hη24]
    have hCFb : CF ≤ δ ^ (-((ηₒ / 4) / 6)) := by
      refine hCF.trans (NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 ?_)
      have : (ηₒ / 4) / 6 = ηₒ / 24 := by ring
      rw [this]
      linarith [hη24]
    have hB : (δ : ENNReal) ^ (ηₒ / 4) ≤ ((Cth⁻¹ : ℝ≥0) : ENNReal) := by
      rw [hCth]
      exact hCb δ Cfib CF hδ0 hδd4 hδ1 D.decomp.one_le_Cfib D.factor.one_le_CF hCfibb hCFb
    -- D: the absolute envelope ratio
    have hD : (δ : ENNReal) ^ (ηₒ / 4) ≤ ((Menv⁻¹ : ℝ≥0) : ENNReal) := hEb δ hδ0 hδd5
    -- C: the selected family's fullness, squared
    have hqinner : F'.innerSet.card ≤ q.card := by
      have h := selectedOuterScaleFamily_innerSet_card_le D.toFineProp51Family input.hδ
        input.hdisc input.hδB input.hupper input.hmass
      simpa [hF', D.toFineProp51Family_innerSet] using h
    have hC : (δ : ENNReal) ^ (ηₒ / 4) ≤ ((lam' ^ 2 : ℝ≥0) : ENNReal) := by
      refine rpow_le_sq_of_selection (η := min (ηₒ / 24) (ηₒ / 32)) (η' := ηₒ / 16)
        hδ0 hδE1 hselC0 (hSb δ a hδ0 hδa ha1 hδd6) hfull ?_ ?_
      · have hib : D.toFineProp51Family.innerBody = fun i => (T i).toShadedBody := rfl
        have h := Q.selection_fullness D.toFineProp51Family input.hδ input.hdisc
          input.volumeRatio input.hδB input.hupper input.hmass
        simpa [hlam', hF', D.toFineProp51Family_innerSet, hib] using h
      · linarith [hη32]
    -- A: Proposition 5.1's own fullness constant
    have hδw : δ ≤ w := ShadedBody.le_selectedOuterScale D.toFineProp51Family input.hδ
      input.hdisc input.hδB input.hupper input.hmass
    have hw1 : w ≤ 1 := by
      refine le_trans ?_ ha1
      exact selectedOuterScale_le D.toFineProp51Family input.hδ input.hdisc input.hδB
        input.hupper input.hmass
    have hMpos : 0 < F'.innerSet.card := by
      rw [Finset.card_pos]
      by_contra hemp
      rw [Finset.not_nonempty_iff_eq_empty] at hemp
      rw [hemp] at hselmass
      simp at hselmass
    have hMcard : (F'.innerSet.card : ℝ) ≤ (δ : ℝ) ^ (-(7 : ℝ)) :=
      hMb q hδ0 hδd3 T hball hEDq F'.innerSet.card hqinner
    have hNbound : ((Dvr.exponent + 1 : ℕ) : ENNReal) ≤ (δ : ENNReal) ^ (-((ηₒ / 4) / 12)) := by
      have h := hNb D hδ0 hball hδd2
      exact h
    have hRcpos : 0 < ShadedBody.factoringCoreAtScaleUniformRefinementConstant 3
        F'.innerSet.card Dvr.exponent w := by
      have h := ShadedBody.factoringCoreAtScaleUniformRefinementConstant_pos input.hδ
        (input.hdisc.restrictOuter _) Dvr w Q.scale_pos htsne
      rwa [hfr] at h
    have hA : (δ : ENNReal) ^ (ηₒ / 4) ≤ (cfull : ENNReal) := by
      rw [hcfull]
      exact hFC δ w F'.innerSet.card Dvr.exponent hδ0 hδd1 hδw hw1 hMpos hMcard hNbound hRcpos
    -- collect
    have hall := rpow_le_mul_four (e := ηₒ) hδ0 hA hB hC hD
    refine rpow_le_of_coe_rpow_le hδ0 ?_
    rw [ENNReal.coe_mul, ENNReal.coe_mul, ENNReal.coe_mul]
    exact hall


end PartBLoss

end Kakeya

end

end
