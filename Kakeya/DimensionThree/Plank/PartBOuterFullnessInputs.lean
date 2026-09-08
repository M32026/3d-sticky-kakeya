/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.PartBVolumeRatioExponent
public import Kakeya.DimensionThree.Plank.PartBLossAbsorption
public import Kakeya.DimensionThree.Plank.Section6PartBPlankOutput
public import Kakeya.DimensionThree.Plank.CollarPlankFullness

/-!
# The remaining inputs of GWZ 6.6(B)'s outer fullness clause

steps, item 1: `δ ^ ηₒ ≤ λ(𝒲, Y_𝒲)`, the outer fullness clause of
`Kakeya.factoringAndMultPropGlobal_of_remark53`, over the plank-presented Proposition-5.1 output.

`Kakeya.le_fullness_collarPlank_of_sum_le`
(`Kakeya/DimensionThree/Plank/CollarPlankFullness.lean`) turns Proposition 5.1's *summed* outer
fullness into a `ShadedBody.fullness` lower bound on the presented planks, at
`c · M_env⁻¹` with

`c = c_full · C⁻¹ · λ(selected)²`,  `C = Kakeya.Section6PartBData.remark53ThickConst Cfib CF`,
`M_env = Kakeya.flatPrismEnvelopeVolumeRatio.C (Kakeya.windowPlankEnvelope.windowConst R Cw)`.

Reaching `δ ^ ηₒ ≤ c · M_env⁻¹` therefore needs a sub-polynomial lower bound on each of the four
factors, and then one product.  **All four, the product, and the two selection-API facts the
instantiation needs are here or already on the branch:**

| factor | bound |
|---|---|
| `c_full` | `Kakeya.PartBLoss.exists_threshold_rpow_le_fullnessConstant` (phase 6), whose `N`- and `M`-hypotheses are `Kakeya.PartBLoss.exists_threshold_fineVolumeRatio_exponent_succ_le_rpow_neg` and `Kakeya.PartBLoss.exists_threshold_card_le_rpow_neg_seven` (phase 8) |
| `C⁻¹` | `exists_threshold_rpow_le_inv_remark53ThickConst`, below |
| `λ(selected)²` | `rpow_le_sq_of_selection`, below, fed by `ShadedBody.FactoringAndMultPropCoreSelectScaleResult.selection_fullness` and `Kakeya.PartBLoss.exists_threshold_outerScaleSelectionConstant_le_rpow_neg` (phase 6, on `δ ≤ B ≤ 1`) |
| `M_env⁻¹` | `exists_threshold_rpow_le_inv`, below — `M_env` is absolute |
| the product | `rpow_le_mul_four`, below |

## The two selection-API facts

`selectedOuterScale_le` and `selectedOuterScaleFamily_innerSet_card_le` are what the `M`- and
`w`-hypotheses of the fullness-constant absorption need at the actual configuration:
`δ ≤ w` is `ShadedBody.le_selectedOuterScale`, already on the branch, but `w ≤ 1` and
`M ≤ q.card` were not.  Both are three lines and neither needed any new mathematics; they are here
rather than in `Kakeya/Factoring/` because that directory belongs to another component.

## What remains of item 1

One instantiation, inside the setup of
`Kakeya.Section6PartBData.exists_collarPresentable_prop51_output`, where the selected family and its
`M`, `N` and `w` are simultaneously in scope: take `e := ηₒ` in `rpow_le_mul_four`, choose the
consumer's `η` below `min (ηₒ/24) (ηₒ/32)` so that the `Cfib`/`CF` budget and the fullness lower
bound both fit the `e/4` slots, feed the four bounds above, descend with
`rpow_le_of_coe_rpow_le`, and chain with `le_fullness_collarPlank_of_sum_le`.  No further
absorptions, no further exposure gaps, and no bound that fails to collect — the remaining step is
term-level plumbing over the six named lemmas.
-/

@[expose] public section

open MeasureTheory Metric Convexity

open scoped ENNReal NNReal

noncomputable section

namespace Kakeya

namespace PartBLoss

open _root_.ShadedBody

/-! ### Descending an `ℝ≥0∞` power bound to `ℝ≥0` -/

/-- The bridge `Kakeya.le_fullness_collarPlank_of_sum_le` concludes in `ℝ≥0`, while every absorption
here is stated in `ℝ≥0∞`; this is the one-line descent. -/
theorem rpow_le_of_coe_rpow_le {δ X : ℝ≥0} {e : ℝ} (hδ0 : 0 < δ)
    (h : (δ : ENNReal) ^ e ≤ (X : ENNReal)) : (δ : ℝ≥0) ^ e ≤ X := by
  have hcoe : (((δ ^ e : ℝ≥0)) : ENNReal) = (δ : ENNReal) ^ e :=
    ENNReal.coe_rpow_of_ne_zero hδ0.ne' _
  rw [← ENNReal.coe_le_coe, hcoe]
  exact h

/-! ### The collection -/

/-- **Four sub-polynomial lower bounds multiply into one.**  This is the arithmetic step of item 1:
`δ ^ e ≤ A · B · C · D` from `δ ^ (e/4) ≤` each factor. -/
theorem rpow_le_mul_four {δ A B C Dd : ℝ≥0} {e : ℝ} (hδ0 : 0 < δ)
    (hA : (δ : ENNReal) ^ (e / 4) ≤ (A : ENNReal))
    (hB : (δ : ENNReal) ^ (e / 4) ≤ (B : ENNReal))
    (hC : (δ : ENNReal) ^ (e / 4) ≤ (C : ENNReal))
    (hD : (δ : ENNReal) ^ (e / 4) ≤ (Dd : ENNReal)) :
    (δ : ENNReal) ^ e ≤ (A : ENNReal) * (B : ENNReal) * (C : ENNReal) * (Dd : ENNReal) := by
  have hne : (δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hδ0.ne'
  have htop : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hsplit : (δ : ENNReal) ^ e
      = (δ : ENNReal) ^ (e / 4) * (δ : ENNReal) ^ (e / 4)
        * (δ : ENNReal) ^ (e / 4) * (δ : ENNReal) ^ (e / 4) := by
    rw [← ENNReal.rpow_add _ _ hne htop, ← ENNReal.rpow_add _ _ hne htop,
      ← ENNReal.rpow_add _ _ hne htop]
    congr 1
    ring
  rw [hsplit]
  exact mul_le_mul' (mul_le_mul' (mul_le_mul' hA hB) hC) hD

/-! ### The three remaining factor bounds -/

/-- **An absolute constant `≥ 1` has `δ ^ e ≤ C⁻¹` below a threshold.**  Used for the envelope ratio
`M_env`, which sees only the window radius, the comparability constant and the dimension. -/
theorem exists_threshold_rpow_le_inv (C : ℝ≥0) (hC : 1 ≤ C) {e : ℝ} (he : 0 < e) :
    ∃ δ₀ : ℝ≥0, 0 < δ₀ ∧ ∀ δ : ℝ≥0, 0 < δ → δ ≤ δ₀ →
      (δ : ENNReal) ^ e ≤ ((C⁻¹ : ℝ≥0) : ENNReal) := by
  obtain ⟨δ₀, hδ₀, habs⟩ := Kakeya.exists_threshold_le_rpow_neg C hC he
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ hδ0 hδ
  have hCne : C ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hC)
  have hCE : (C : ENNReal) ≤ (δ : ENNReal) ^ (-e) := by
    have h := habs δ hδ0 hδ
    have hcoe : ((δ ^ (-e) : ℝ≥0) : ENNReal) = (δ : ENNReal) ^ (-e) :=
      ENNReal.coe_rpow_of_ne_zero hδ0.ne' _
    calc (C : ENNReal) ≤ ((δ ^ (-e) : ℝ≥0) : ENNReal) := by exact_mod_cast h
      _ = (δ : ENNReal) ^ (-e) := hcoe
  exact rpow_le_inv_of_le_rpow_neg hCne hCE

/-- **The Remark-5.3 thick constant is sub-polynomially small in the inverse.**

`Kakeya.Section6PartBData.remark53ThickConst Cfib CF = Cfib² · r² · CF · v²`, so the datum's own
budget `Cfib, CF ≤ δ ^ (-η)` at `η = e/6` gives `δ ^ (-e/2)`, and the two absolute factors `r², v²`
are absorbed by the other half. -/
theorem exists_threshold_rpow_le_inv_remark53ThickConst {e : ℝ} (he : 0 < e) :
    ∃ δ₀ : ℝ≥0, 0 < δ₀ ∧ ∀ (δ Cfib CF : ℝ≥0), 0 < δ → δ ≤ δ₀ → δ ≤ 1 →
      1 ≤ Cfib → 1 ≤ CF → Cfib ≤ δ ^ (-(e / 6)) → CF ≤ δ ^ (-(e / 6)) →
      (δ : ENNReal) ^ e
        ≤ (((Kakeya.Section6PartBData.remark53ThickConst Cfib CF)⁻¹ : ℝ≥0) : ENNReal) := by
  set A : ℝ≥0 := max 1 (Kakeya.coarseTubeVolumeRatio ^ 2 * Metric.volume_comparison.C 3 ^ 2)
    with hA
  have hA1 : 1 ≤ A := le_max_left _ _
  obtain ⟨δ₀, hδ₀, habs⟩ :=
    Kakeya.exists_threshold_le_rpow_neg A hA1 (show (0 : ℝ) < e / 2 by positivity)
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ Cfib CF hδ0 hδ hδ1 hCfib1 hCF1 hCfib hCF
  have hrpos : (0 : ℝ≥0) < Kakeya.coarseTubeVolumeRatio :=
    lt_of_lt_of_le zero_lt_one Kakeya.one_le_coarseTubeVolumeRatio
  have hvpos : (0 : ℝ≥0) < Metric.volume_comparison.C 3 := Metric.volume_comparison.C_pos 3
  have hCfibpos : (0 : ℝ≥0) < Cfib := lt_of_lt_of_le zero_lt_one hCfib1
  have hCFpos : (0 : ℝ≥0) < CF := lt_of_lt_of_le zero_lt_one hCF1
  have hne : Kakeya.Section6PartBData.remark53ThickConst Cfib CF ≠ 0 := by
    rw [Kakeya.Section6PartBData.remark53ThickConst]
    refine ne_of_gt (mul_pos (mul_pos (mul_pos ?_ ?_) hCFpos) ?_)
    · exact pow_pos hCfibpos 2
    · exact pow_pos hrpos 2
    · exact pow_pos hvpos 2
  have hprod : Kakeya.Section6PartBData.remark53ThickConst Cfib CF
      ≤ (δ ^ (-(e / 2)) : ℝ≥0) * A := by
    have hstep : Kakeya.Section6PartBData.remark53ThickConst Cfib CF
        ≤ (Cfib ^ 2 * CF) * A := by
      rw [Kakeya.Section6PartBData.remark53ThickConst]
      have hAle : Kakeya.coarseTubeVolumeRatio ^ 2 * Metric.volume_comparison.C 3 ^ 2 ≤ A :=
        le_max_right _ _
      calc Cfib ^ 2 * Kakeya.coarseTubeVolumeRatio ^ 2 * CF
              * Metric.volume_comparison.C 3 ^ 2
          = (Cfib ^ 2 * CF)
              * (Kakeya.coarseTubeVolumeRatio ^ 2 * Metric.volume_comparison.C 3 ^ 2) := by ring
        _ ≤ (Cfib ^ 2 * CF) * A := mul_le_mul' le_rfl hAle
    refine hstep.trans (mul_le_mul' ?_ le_rfl)
    have h3 : Cfib ^ 2 * CF ≤ (δ ^ (-(e / 6)) : ℝ≥0) ^ 2 * (δ ^ (-(e / 6)) : ℝ≥0) :=
      mul_le_mul' (pow_le_pow_left' hCfib 2) hCF
    refine h3.trans (le_of_eq ?_)
    rw [← NNReal.rpow_natCast (δ ^ (-(e / 6)) : ℝ≥0) 2, ← NNReal.rpow_mul,
      ← NNReal.rpow_add' (by intro hz; linarith)]
    · congr 1
      push_cast
      ring
  have hAabs := habs δ hδ0 hδ
  have hE : ((Kakeya.Section6PartBData.remark53ThickConst Cfib CF : ℝ≥0) : ENNReal)
      ≤ (δ : ENNReal) ^ (-e) := by
    have hsplit : (δ : ENNReal) ^ (-e)
        = (δ : ENNReal) ^ (-(e / 2)) * (δ : ENNReal) ^ (-(e / 2)) := by
      rw [← ENNReal.rpow_add _ _ (ENNReal.coe_ne_zero.mpr hδ0.ne') ENNReal.coe_ne_top]
      congr 1
      ring
    have hδpow : (((δ ^ (-(e / 2)) : ℝ≥0)) : ENNReal) = (δ : ENNReal) ^ (-(e / 2)) :=
      ENNReal.coe_rpow_of_ne_zero hδ0.ne' _
    have hAE : (A : ENNReal) ≤ (δ : ENNReal) ^ (-(e / 2)) := by
      calc (A : ENNReal) ≤ (((δ ^ (-(e / 2)) : ℝ≥0)) : ENNReal) := by exact_mod_cast hAabs
        _ = (δ : ENNReal) ^ (-(e / 2)) := hδpow
    rw [hsplit]
    calc ((Kakeya.Section6PartBData.remark53ThickConst Cfib CF : ℝ≥0) : ENNReal)
        ≤ (((δ ^ (-(e / 2)) : ℝ≥0) * A : ℝ≥0) : ENNReal) := by exact_mod_cast hprod
      _ = (((δ ^ (-(e / 2)) : ℝ≥0)) : ENNReal) * (A : ENNReal) := by rw [ENNReal.coe_mul]
      _ = (δ : ENNReal) ^ (-(e / 2)) * (A : ENNReal) := by rw [hδpow]
      _ ≤ (δ : ENNReal) ^ (-(e / 2)) * (δ : ENNReal) ^ (-(e / 2)) := by gcongr
  exact rpow_le_inv_of_le_rpow_neg hne hE

/-- **The scale-selected family's fullness, squared, is bounded below by a power of `δ`.**

`hlam'` is exactly `ShadedBody.FactoringAndMultPropCoreSelectScaleResult.selection_fullness`, and
`hselC` is `Kakeya.PartBLoss.exists_threshold_outerScaleSelectionConstant_le_rpow_neg` at `B = a`
(which is why that lemma had to be proved on `δ ≤ B ≤ 1`: the branch's pre-existing version assumes
`1 ≤ B`). -/
theorem rpow_le_sq_of_selection {δ selC lam lam' : ℝ≥0} {e η η' : ℝ}
    (hδ0 : 0 < δ) (hδ1 : (δ : ENNReal) ≤ 1)
    (hselC0 : selC ≠ 0)
    (hselC : (selC : ENNReal) ≤ (δ : ENNReal) ^ (-η'))
    (hlam : (δ : ℝ≥0) ^ η ≤ lam)
    (hlam' : ((selC⁻¹ : ℝ≥0) : ENNReal) * (lam : ENNReal) ≤ (lam' : ENNReal))
    (hsum : 2 * (η + η') ≤ e) :
    (δ : ENNReal) ^ e ≤ ((lam' ^ 2 : ℝ≥0) : ENNReal) := by
  have hne : (δ : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr hδ0.ne'
  have htop : (δ : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hinv : (δ : ENNReal) ^ η' ≤ ((selC⁻¹ : ℝ≥0) : ENNReal) :=
    rpow_le_inv_of_le_rpow_neg hselC0 hselC
  have hlamE : (δ : ENNReal) ^ η ≤ (lam : ENNReal) := by
    have hcoe : (((δ ^ η : ℝ≥0)) : ENNReal) = (δ : ENNReal) ^ η :=
      ENNReal.coe_rpow_of_ne_zero hδ0.ne' _
    calc (δ : ENNReal) ^ η = (((δ ^ η : ℝ≥0)) : ENNReal) := hcoe.symm
      _ ≤ (lam : ENNReal) := by exact_mod_cast hlam
  have hstep : (δ : ENNReal) ^ (η + η') ≤ (lam' : ENNReal) := by
    calc (δ : ENNReal) ^ (η + η') = (δ : ENNReal) ^ η' * (δ : ENNReal) ^ η := by
          rw [← ENNReal.rpow_add _ _ hne htop]
          congr 1
          ring
      _ ≤ ((selC⁻¹ : ℝ≥0) : ENNReal) * (lam : ENNReal) := mul_le_mul' hinv hlamE
      _ ≤ (lam' : ENNReal) := hlam'
  have hsq : (δ : ENNReal) ^ (2 * (η + η')) ≤ ((lam' ^ 2 : ℝ≥0) : ENNReal) :=
    rpow_two_mul_le_sq_of_rpow_le hstep
  exact (ENNReal.rpow_le_rpow_of_exponent_ge hδ1 hsum).trans hsq

/-! ### Two facts the selection API was missing -/

section Sel
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E] {ι κ : Type*} [DecidableEq κ]

/-- **The selected outer scale is at most the upper endpoint.**  `ShadedBody.le_selectedOuterScale`
gives `δ ≤ w`; this gives `w ≤ B`, and at `B = a ≤ 1` it is the `w ≤ 1` hypothesis of the pipeline
envelope. -/
theorem selectedOuterScale_le (F : FactorFamily E ι κ) {δ B : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (hδB : δ ≤ B)
    (hupper : ∀ j ∈ F.innerSet.image F.parent, (F.outerBody j).scale ≤ B)
    (hmass : 0 < ∑ i ∈ F.innerSet, volume (F.innerBody i).shade) :
    selectedOuterScale F hδ hdisc hδB hupper hmass ≤ B := by
  have hj : (outerScaleSelection F hδ hdisc hδB hupper hmass).selected_nonempty.choose
      ∈ F.innerSet.image F.parent :=
    (outerScaleSelection F hδ hdisc hδB hupper hmass).selected_subset
      (outerScaleSelection F hδ hdisc hδB hupper hmass).selected_nonempty.choose_spec
  have hup := hupper _ hj
  show Real.toNNReal _ ≤ B
  rw [← NNReal.coe_le_coe, Real.coe_toNNReal _
    (Metric.thickness_nonneg _ (Module.finrank ℝ E - 1))]
  exact hup

/-- **The scale-selected family has at most as many inner indices.**  This is the `M ≤ q.card`
hypothesis of `Kakeya.PartBLoss.exists_threshold_card_le_rpow_neg_seven` at the actual
configuration. -/
theorem selectedOuterScaleFamily_innerSet_card_le (F : FactorFamily E ι κ) {δ B : NNReal}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) (hδB : δ ≤ B)
    (hupper : ∀ j ∈ F.innerSet.image F.parent, (F.outerBody j).scale ≤ B)
    (hmass : 0 < ∑ i ∈ F.innerSet, volume (F.innerBody i).shade) :
    (selectedOuterScaleFamily F hδ hdisc hδB hupper hmass).innerSet.card
      ≤ F.innerSet.card := by
  refine Finset.card_le_card ?_
  rw [selectedOuterScaleFamily, FactorFamily.restrictOuter_innerSet]
  exact Finset.filter_subset _ _

end Sel

end PartBLoss

end Kakeya

end

end
