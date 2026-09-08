/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.CollarPlankPresentation

/-!
# Outer fullness for the plank-presented Proposition-5.1 output

`Kakeya.Section6PartBData.exists_plank_presented_split_of_blockPigeonhole`
(`Kakeya/DimensionThree/Plank/Section6PartBWiring.lean`) delivers everything
`Kakeya.factoringAndMultPropGlobal_of_remark53` asks of its outer family **except the fullness
clause** `δ ^ ηₒ ≤ λ(𝒲, Y_𝒲)`.  This file supplies the missing composition.

## The shape of the gap

GWZ Proposition 5.1 delivers outer fullness in **summed** form,
`ShadedBody.FactoringAndMultPropCoreAtScale.thick_fullness`:

`c · ∑_j |𝒲_j| ≤ ∑_j |Y_{𝒲_j}|`,   with `c = c_full · C⁻¹ · λ(𝒯, Y)²`,

whereas the consumer wants a `ShadedBody.fullness` **ratio** lower bound, and it wants it on
the *presented* planks `Kakeya.collarPlank`, not on the Proposition-5.1 outer bodies.  Two
transports already exist for the first half of that —
`Kakeya.collarPlank_sum_fullness_transport` (summed, on the presented planks, at the envelope loss)
and `Kakeya.le_fullness_of_mul_sum_carrier_le` (summed ⟹ ratio, given a nonvanishing denominator).
What was missing is their composition together with the denominator fact, which is what
`Kakeya.le_fullness_collarPlank_of_sum_le` below is.

## The denominator is free

A presented plank is an **exact** `a × b × 1` plank, so its volume is `8ab`, positive as soon as
`0 < a` — no geometry is needed, only `ts.Nonempty`.  That is
`Kakeya.sum_volume_carrier_collarPlank_ne_zero`, and it is the only place `ts.Nonempty` is used.

## What this does *not* close, and exactly why

The conclusion is `c · M⁻¹ ≤ λ(𝒲, Y_𝒲)` with `M` the **absolute** envelope ratio
`Kakeya.flatPrismEnvelopeVolumeRatio.C (Kakeya.windowPlankEnvelope.windowConst R Cw)`.  Turning
that into `δ ^ ηₒ ≤ λ(𝒲, Y_𝒲)` needs `δ ^ ηₒ ≤ c · M⁻¹`, i.e. sub-polynomial lower bounds on the
three factors of `c`.  Two of them are available in this development:

* `C⁻¹`, where `C = Kakeya.Section6PartBData.remark53ThickConst Cfib CF`, from the datum's own budget
  `Cfib, CF ≤ δ ^ (-η)`;
* `λ(𝒯, Y) ≥ δ ^ η`, which is a hypothesis of Proposition 6.6(B) — transported to the
  scale-selected subfamily, at the selection loss, by
  `ShadedBody.FactoringAndMultPropCoreSelectScaleResult.selection_fullness`.

The remaining two constants are **now available**, in
`Kakeya/DimensionThree/Plank/PartBLossAbsorption.lean`:

* `Kakeya.PartBLoss.exists_threshold_rpow_le_fullnessConstant` for
  `ShadedBody.factoringCoreAtScaleUniformFullnessConstant`;
* `Kakeya.PartBLoss.exists_threshold_outerScaleSelectionConstant_le_rpow_neg` for
  `ShadedBody.outerScaleSelectionConstant`, on `δ ≤ B ≤ 1` — the regime this consumer needs, and the
  one this branch's pre-existing `ShadedBody.eventually_outerScaleSelectionConstant_le_rpow_neg` does
  *not* cover, since that lemma assumes `1 ≤ B`.

An earlier revision of this docstring said neither existed anywhere on this branch.  That was wrong:
it had searched for the names those lemmas carry on `origin/numina/22`, not for the facts.  See the
module docstring of `PartBLossAbsorption.lean`.

## The two neighbouring outer clauses need nothing new

For the record, since they were on the same list:

* `ts.Nonempty` is `ShadedBody.FactoringAndMultPropCoreAtScale.outerSet_nonempty_of_input_mass_pos`
  applied to the selected mass, which the Part-(B) construction already computes;
* the Katz--Tao clause at `δ ^ (-ηₒ)` is `Kakeya.isKatzTao_collarPlank` followed by
  `ConvexSpaceBody.IsKatzTao.mono`, since the two losses it carries are absolute and the datum's own
  `C₀` is already bounded by `δ ^ (-η)`.

Both are one-liners at the call site, so nothing is added here for them.
-/

@[expose] public section

open MeasureTheory Metric Convexity

open scoped ENNReal NNReal

noncomputable section

namespace Kakeya

open comparablePlankEnvelope windowPlankEnvelope

variable {X : Type*} {R Cw a b : ℝ≥0}

/-- **The presented planks have positive total carrier volume.**

A `Kakeya.collarPlank` is an *exact* `a × b × 1` plank, so `|W x| = 8ab` by
`Prism3D.volume_carrier`; positivity of `a` and `b` and one member of `ts` suffice.  This is
the denominator condition of `Kakeya.le_fullness_of_mul_sum_carrier_le`, and the only place
`ts.Nonempty` enters the fullness transport. -/
theorem sum_volume_carrier_collarPlank_ne_zero (hR : 1 ≤ R) (hCw : 1 ≤ Cw)
    (hab : a ≤ b) (hb1 : b ≤ 1) (ha : 0 < a) (hb : 0 < b)
    {ts : Finset X} (hts : ts.Nonempty)
    (K : X → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
    (Y : X → ShadedBody (EuclideanSpace ℝ (Fin 3))) :
    (∑ x ∈ ts, volume ((collarPlank hR hCw hab hb1 (K x) (Y x)).carrier)) ≠ 0 := by
  obtain ⟨x₀, hx₀⟩ := hts
  have hvol : volume ((collarPlank hR hCw hab hb1 (K x₀) (Y x₀)).carrier)
      = 8 * (a : ENNReal) * (b : ENNReal) * 1 :=
    Prism3D.volume_carrier _
  have hpos : volume ((collarPlank hR hCw hab hb1 (K x₀) (Y x₀)).carrier) ≠ 0 := by
    rw [hvol]
    have ha' : (a : ENNReal) ≠ 0 := by simpa using ha.ne'
    have hb' : (b : ENNReal) ≠ 0 := by simpa using hb.ne'
    simp [ha', hb']
  intro hzero
  refine hpos ?_
  have hle : volume ((collarPlank hR hCw hab hb1 (K x₀) (Y x₀)).carrier)
      ≤ ∑ x ∈ ts, volume ((collarPlank hR hCw hab hb1 (K x) (Y x)).carrier) :=
    Finset.single_le_sum
      (f := fun x => volume ((collarPlank hR hCw hab hb1 (K x) (Y x)).carrier))
      (fun _ _ => bot_le) hx₀
  rw [hzero] at hle
  exact le_antisymm hle bot_le

/-- **Proposition 5.1's summed outer fullness becomes a fullness lower bound on the presented
planks, at the absolute envelope loss.**

The hypothesis `hsum` is *exactly* the shape of
`ShadedBody.FactoringAndMultPropCoreAtScale.thick_fullness`, and `hpres` is exactly what
`Kakeya.isCollarPresentable_outerThickFamilyAtScale` (and, at the Part-(B) datum,
`Kakeya.Section6PartBData.exists_collarPresentable_prop51_output`) produces.  So this lemma has no
hypothesis without a producer: it is the missing composition of
`Kakeya.collarPlank_sum_fullness_transport` with `Kakeya.le_fullness_of_mul_sum_carrier_le`.

The loss is the **absolute** envelope ratio `M`: it sees only the window radius `R`, the
comparability constant `Cw` and the ambient dimension — never `δ`, never the configuration — so it
is absorbed by the same sub-polynomial budget that already carries `Cw`. -/
theorem le_fullness_collarPlank_of_sum_le (hR : 1 ≤ R) (hCw : 1 ≤ Cw)
    (hab : a ≤ b) (hb1 : b ≤ 1) (ha : 0 < a) (hb : 0 < b)
    {ts : Finset X} (hts : ts.Nonempty)
    (K : X → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
    (Y : X → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (hpres : ∀ x ∈ ts, IsCollarPresentable R Cw a b (K x) (Y x))
    (hdim : ∀ x ∈ ts, IsPlankOfDimensions Cw a b (K x))
    {c : ℝ≥0}
    (hsum : (c : ENNReal) * (∑ x ∈ ts, volume (Y x).carrier)
      ≤ ∑ x ∈ ts, volume (Y x).shade) :
    c * (flatPrismEnvelopeVolumeRatio.C (windowConst R Cw))⁻¹
      ≤ ShadedBody.fullness ts
          (fun x => (collarPlank hR hCw hab hb1 (K x) (Y x)).toShadedBody) := by
  set M : ℝ≥0 := flatPrismEnvelopeVolumeRatio.C (windowConst R Cw) with hM
  have hM1 : 1 ≤ M := flatPrismEnvelopeVolumeRatio.one_le _
  have hM0 : M ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hM1)
  have hM0' : (M : ENNReal) ≠ 0 := by simpa using hM0
  have hMtop : (M : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have htr := collarPlank_sum_fullness_transport hR hCw hab hb1 ha hb ts K Y hpres hdim hsum
  have hne := sum_volume_carrier_collarPlank_ne_zero hR hCw hab hb1 ha hb hts K Y
  refine le_fullness_of_mul_sum_carrier_le ts
    (fun x => (collarPlank hR hCw hab hb1 (K x) (Y x)).toShadedBody) ?_ hne
  have hcoe : ((c * M⁻¹ : ℝ≥0) : ENNReal) = (c : ENNReal) * (M : ENNReal)⁻¹ := by
    rw [ENNReal.coe_mul, ENNReal.coe_inv hM0]
  rw [hcoe]
  calc (c : ENNReal) * (M : ENNReal)⁻¹
        * (∑ x ∈ ts, volume ((collarPlank hR hCw hab hb1 (K x) (Y x)).toShadedBody).carrier)
      = (M : ENNReal)⁻¹ * ((c : ENNReal)
          * ∑ x ∈ ts, volume ((collarPlank hR hCw hab hb1 (K x) (Y x)).carrier)) := by
        ring
    _ ≤ (M : ENNReal)⁻¹ * ((M : ENNReal)
          * ∑ x ∈ ts, volume ((collarPlank hR hCw hab hb1 (K x) (Y x)).shade)) := by
        gcongr
    _ = ∑ x ∈ ts, volume ((collarPlank hR hCw hab hb1 (K x) (Y x)).toShadedBody).shade := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hM0' hMtop, one_mul]

end Kakeya

end

end
