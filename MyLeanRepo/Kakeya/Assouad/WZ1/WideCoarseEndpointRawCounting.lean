import MyLeanRepo.Kakeya.Assouad.WZ1.WideCoarseEndpointLineSplitStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.WideCoarseLineTransferBasics

/-!
# Common raw-strip counting chain for wide endpoint synthesis

This module keeps the two quantitative retention losses explicit.  It does
not perform any scale-power comparison or final exponent absorption.
-/

namespace Kakeya.Assouad

open scoped ENNReal

/-- Ambient-to-active retention fraction in one endpoint input. -/
noncomputable def wideCoarseEndpointActiveFraction
    (delta eta : ℝ) : ENNReal :=
  ((1 / 256 : ENNReal) *
    Kakeya.realRpowENN delta eta) / 16

/-- Active-to-selected retention fraction in one endpoint rescaling. -/
noncomputable def wideCoarseEndpointRescaleFraction
    (delta width exponent : ℝ) : ENNReal :=
  Kakeya.realRpowENN (delta / width) exponent

/-- Rewrite one weighted raw-strip factor in the common `realRpowENN` form. -/
lemma wideCoarseEndpoint_weighted_raw_power_identity
    {width radius zeta : ℝ}
    (hwidth : 0 < width) (hradius : 0 < radius) :
    ENNReal.ofReal
        ((Real.rpow width zeta)⁻¹ *
          Real.rpow radius zeta) =
      Kakeya.realRpowENN width (-zeta) *
        Kakeya.realRpowENN radius zeta := by
  have hnegative :
      (Real.rpow width zeta)⁻¹ =
        Real.rpow width (-zeta) :=
    (Real.rpow_neg hwidth.le zeta).symm
  rw [hnegative]
  exact ENNReal.ofReal_mul
    (Real.rpow_nonneg hwidth.le _)

/--
The complete finite-cardinality chain shared by every wide raw-strip leaf.

The two inverse factors are, respectively:

* the ambient-to-active retention in the endpoint input;
* the active-to-selected retention in the anisotropic rescaling.

The final factor `2 * fiberMultiplicity * coarse.enncard` is the balanced
cell upper count.  No power comparison has been used.
-/
lemma wideCoarseEndpoint_selected_strip_card_le_raw_chain
    {epsilon eta delta : ℝ}
    {parameters : WZ1Proposition8_9Parameters epsilon}
    {F G₁ G₂ ambient active : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    {data :
      WZ1Proposition8_9CommonStripData
        delta epsilon eta parameters F G₁ G₂ H}
    (input :
      WZ1WideCoarseEndpointLineInput
        (ambient := ambient) (active := active)
        parameters data)
    (hdelta : 0 < delta)
    (normal : Point2) (hnormal : ‖normal‖ = 1)
    (level rawRadius : ℝ)
    (hdeltaRadius : delta ≤ rawRadius) :
    ((input.rescale.selected.filter fun point =>
      |inner ℝ point normal - level| ≤ rawRadius).card :
        ENNReal) ≤
      ((256 : ENNReal) *
          Kakeya.realRpowENN delta (-eta)) *
        Kakeya.realRpowENN input.rawWidth (-parameters.zeta) *
        Kakeya.realRpowENN rawRadius parameters.zeta *
        (wideCoarseEndpointActiveFraction delta eta)⁻¹ *
        (wideCoarseEndpointRescaleFraction
          delta data.width
          (parameters.stripEpsilon * eta / 10))⁻¹ *
        (2 : ENNReal) *
          (input.rescale.fiberMultiplicity : ENNReal) *
          input.rescale.coarse.enncard := by
  classical
  let sourcePredicate : Point2 → Prop :=
    fun point =>
      |inner ℝ point normal - level| ≤ rawRadius
  let activeFraction : ENNReal :=
    wideCoarseEndpointActiveFraction delta eta
  let rescaleFraction : ENNReal :=
    wideCoarseEndpointRescaleFraction
      delta data.width
      (parameters.stripEpsilon * eta / 10)
  have hselectedAmbient :
      input.rescale.selected ⊆ ambient :=
    input.rescale.selected_subset.trans input.active_subset
  have hcount :
      ((input.rescale.selected.filter sourcePredicate).card :
          ENNReal) ≤
        ((ambient.filter sourcePredicate).card : ENNReal) := by
    exact_mod_cast
      Finset.card_le_card
        (Finset.filter_subset_filter
          sourcePredicate hselectedAmbient)
  have hrawRadius : 0 < rawRadius :=
    hdelta.trans_le hdeltaRadius
  have hambientStrip :
      ((ambient.filter sourcePredicate).card : ENNReal) ≤
        ((256 : ENNReal) *
            Kakeya.realRpowENN delta (-eta)) *
          Kakeya.realRpowENN input.rawWidth (-parameters.zeta) *
          Kakeya.realRpowENN rawRadius parameters.zeta *
          ambient.enncard := by
    have hraw :=
      input.raw_nonconcentration
        normal hnormal level rawRadius hdeltaRadius
    rw [wideCoarseEndpoint_weighted_raw_power_identity
      input.rawWidth_pos hrawRadius] at hraw
    simpa [sourcePredicate, mul_assoc] using hraw
  have hactiveFractionPos : 0 < activeFraction := by
    have hrpowPos :
        0 < Kakeya.realRpowENN delta eta := by
      simp only [Kakeya.realRpowENN, ENNReal.ofReal_pos]
      exact Real.rpow_pos_of_pos hdelta _
    dsimp only [activeFraction, wideCoarseEndpointActiveFraction]
    exact
      ENNReal.div_pos
        (mul_ne_zero (by norm_num) hrpowPos.ne')
        (by norm_num)
  have hactiveFractionTop : activeFraction ≠ ⊤ := by
    dsimp only [activeFraction, wideCoarseEndpointActiveFraction]
    exact
      ENNReal.div_ne_top
        (ENNReal.mul_ne_top
          (by simp)
          (by
            dsimp only [Kakeya.realRpowENN]
            exact ENNReal.ofReal_ne_top))
        (by simp)
  have hambientActive :
      ambient.enncard ≤ activeFraction⁻¹ * active.enncard := by
    have hretention :
        activeFraction * ambient.enncard ≤ active.enncard := by
      simpa [activeFraction,
        wideCoarseEndpointActiveFraction] using
          input.active_retention
    have hscaled :=
      mul_le_mul_left'
        hretention activeFraction⁻¹
    rw [← mul_assoc,
      ENNReal.inv_mul_cancel
        hactiveFractionPos.ne' hactiveFractionTop,
      one_mul] at hscaled
    exact hscaled
  have hrescaleFractionPos : 0 < rescaleFraction := by
    dsimp only [rescaleFraction,
      wideCoarseEndpointRescaleFraction]
    simp only [Kakeya.realRpowENN, ENNReal.ofReal_pos]
    exact Real.rpow_pos_of_pos
      (div_pos hdelta data.width_pos) _
  have hrescaleFractionTop : rescaleFraction ≠ ⊤ := by
    dsimp only [rescaleFraction,
      wideCoarseEndpointRescaleFraction,
      Kakeya.realRpowENN]
    simp
  have hactiveSelected :
      active.enncard ≤
        rescaleFraction⁻¹ * input.rescale.selected.enncard := by
    have hretention :
        rescaleFraction * active.enncard ≤
          input.rescale.selected.enncard := by
      simpa [rescaleFraction,
        wideCoarseEndpointRescaleFraction] using
          input.rescale.retention
    have hscaled :=
      mul_le_mul_left'
        hretention rescaleFraction⁻¹
    rw [← mul_assoc,
      ENNReal.inv_mul_cancel
        hrescaleFractionPos.ne' hrescaleFractionTop,
      one_mul] at hscaled
    exact hscaled
  have hselectedCoarse :=
    anisotropic_selected_card_le_two_fiber_coarse
      input.rescale
  calc
    ((input.rescale.selected.filter fun point =>
        |inner ℝ point normal - level| ≤ rawRadius).card :
          ENNReal) =
        ((input.rescale.selected.filter sourcePredicate).card :
          ENNReal) := by rfl
    _ ≤ ((ambient.filter sourcePredicate).card : ENNReal) :=
      hcount
    _ ≤
        ((256 : ENNReal) *
            Kakeya.realRpowENN delta (-eta)) *
          Kakeya.realRpowENN input.rawWidth (-parameters.zeta) *
          Kakeya.realRpowENN rawRadius parameters.zeta *
          ambient.enncard := hambientStrip
    _ ≤
        ((256 : ENNReal) *
            Kakeya.realRpowENN delta (-eta)) *
          Kakeya.realRpowENN input.rawWidth (-parameters.zeta) *
          Kakeya.realRpowENN rawRadius parameters.zeta *
          (activeFraction⁻¹ * active.enncard) := by
      gcongr
    _ ≤
        ((256 : ENNReal) *
            Kakeya.realRpowENN delta (-eta)) *
          Kakeya.realRpowENN input.rawWidth (-parameters.zeta) *
          Kakeya.realRpowENN rawRadius parameters.zeta *
          (activeFraction⁻¹ *
            (rescaleFraction⁻¹ *
              input.rescale.selected.enncard)) := by
      gcongr
    _ ≤
        ((256 : ENNReal) *
            Kakeya.realRpowENN delta (-eta)) *
          Kakeya.realRpowENN input.rawWidth (-parameters.zeta) *
          Kakeya.realRpowENN rawRadius parameters.zeta *
          (wideCoarseEndpointActiveFraction delta eta)⁻¹ *
          (wideCoarseEndpointRescaleFraction
            delta data.width
            (parameters.stripEpsilon * eta / 10))⁻¹ *
          (2 : ENNReal) *
          (input.rescale.fiberMultiplicity : ENNReal) *
          input.rescale.coarse.enncard := by
      simp only [activeFraction, rescaleFraction]
      calc
        ((256 : ENNReal) *
              Kakeya.realRpowENN delta (-eta)) *
            Kakeya.realRpowENN input.rawWidth (-parameters.zeta) *
            Kakeya.realRpowENN rawRadius parameters.zeta *
            ((wideCoarseEndpointActiveFraction delta eta)⁻¹ *
              ((wideCoarseEndpointRescaleFraction
                delta data.width
                (parameters.stripEpsilon * eta / 10))⁻¹ *
                input.rescale.selected.enncard))
            ≤
          ((256 : ENNReal) *
              Kakeya.realRpowENN delta (-eta)) *
            Kakeya.realRpowENN input.rawWidth (-parameters.zeta) *
            Kakeya.realRpowENN rawRadius parameters.zeta *
            ((wideCoarseEndpointActiveFraction delta eta)⁻¹ *
              ((wideCoarseEndpointRescaleFraction
                delta data.width
                (parameters.stripEpsilon * eta / 10))⁻¹ *
                ((2 : ENNReal) *
                  (input.rescale.fiberMultiplicity : ENNReal) *
                  input.rescale.coarse.enncard))) := by
            gcongr
        _ =
          ((256 : ENNReal) *
              Kakeya.realRpowENN delta (-eta)) *
            Kakeya.realRpowENN input.rawWidth (-parameters.zeta) *
            Kakeya.realRpowENN rawRadius parameters.zeta *
            (wideCoarseEndpointActiveFraction delta eta)⁻¹ *
            (wideCoarseEndpointRescaleFraction
              delta data.width
              (parameters.stripEpsilon * eta / 10))⁻¹ *
            (2 : ENNReal) *
            (input.rescale.fiberMultiplicity : ENNReal) *
            input.rescale.coarse.enncard := by
              ac_rfl

end Kakeya.Assouad
