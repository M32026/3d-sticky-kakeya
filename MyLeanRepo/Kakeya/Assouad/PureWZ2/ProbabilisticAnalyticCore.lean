import MyLeanRepo.Kakeya.Assouad.PureWZ2.BicriteriaAnalyticCore
import MyLeanRepo.Kakeya.Assouad.PureWZ2.BodyCWADeltaMax
import MyLeanRepo.Kakeya.Assouad.TubeVolumeScaling
import MyLeanRepo.Kakeya.Streamlined.GeneralizedKatzTao.ProbabilisticThinning
import MyLeanRepo.Kakeya.Streamlined.MaximalDensityFactoring.SubfamilyHelpers

/-!
# Probabilistic analytic core without UTS

The probabilistic thinning theorem only needs an indexed unit-ball tube family
and a finite `deltaMax` bound.  After thinning, the new `deltaMax` controls the
analytic conflict degree.  A weighted finite-graph cleanup then produces one
pairwise Assertion-D-essentially-distinct core.

This module contains no uniform-tube structure and no assigned-fiber API.
-/

noncomputable section

open Kakeya.Streamlined
open Kakeya.Streamlined.RandomTranslation

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- Delta-max constant delivered by Bernoulli thinning. -/
def pureWZ2ThinnedDeltaMax
    {delta : ℝ}
    (net : TubeDensityTestNet delta)
    (thinningEta : ℝ) : ENNReal :=
  net.lossFactor * 10 *
    Kakeya.realRpowENN delta (-thinningEta)

/-- Analytic conflict-degree constant after Bernoulli thinning. -/
def pureWZ2ThinnedAnalyticConflictBound
    {delta : ℝ}
    (net : TubeDensityTestNet delta)
    (thinningEta : ℝ) : ENNReal :=
  972000000 * pureWZ2ThinnedDeltaMax net thinningEta

/-- View a selected finite set of indices as a genuine tube subfamily. -/
def selectedTubeSubfamily
    {delta : ℝ}
    (family : Kakeya.Streamlined.TubeFamily delta)
    (selected : Finset (Fin family.card)) :
    Kakeya.Streamlined.TubeSubfamily family where
  family := selectedTubeFamily family selected
  embedding :=
    ⟨fun index => (selected.equivFin.symm index).1, by
      intro first second heq
      apply selected.equivFin.symm.injective
      exact Subtype.ext heq⟩
  tube_eq _ := rfl

/--
Bernoulli thinning followed by weighted analytic-essential-distinct cleanup.

The final shading retains the original pointwise density constant.  Its
cardinality lower bound is explicit; the two density factors come from
converting the Bernoulli-retained mass and the weighted cleanup mass into
cardinality.
-/
theorem pure_wz2_probabilistic_analytic_core
    {delta : ℝ}
    (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1)
    (hscaleSmall : 3000 * delta ≤ 1 / 8)
    (family : Kakeya.Streamlined.TubeFamily delta)
    (hfamilyNonempty : family.Nonempty)
    (hfamilyBall : family.IsInUnitBall)
    (shading : Kakeya.Streamlined.TubeShading family)
    (densityConstant D : ENNReal)
    (thinningEta : ℝ)
    (hdensityPositive : 0 < densityConstant)
    (hDtop : D ≠ ⊤)
    (hthinningEta : 0 < thinningEta)
    (hdeltaMax : family.toBodyFamily.deltaMax ≤ D)
    (hthin :
      Kakeya.realRpowENN delta (-thinningEta) ≤ D)
    (hperTube :
      ∀ index,
        densityConstant * (family.tube index).volume ≤
          MeasureTheory.volume (shading.carrier index))
    (net : TubeDensityTestNet delta)
    (hmu :
      Kakeya.deltaTubeVolume delta ≤
        (Kakeya.realRpowENN delta (-thinningEta) / D) *
          shading.mass)
    (hunion :
      let probability :=
        (Kakeya.realRpowENN delta
          (-thinningEta)).toReal / D.toReal
      (net.testSets.card : ℝ) *
            Real.exp (-(11 - Real.exp 1) *
              (Kakeya.realRpowENN delta
                (-thinningEta)).toReal) +
          Real.exp (-(3 - Real.exp 1) *
            probability * (family.card : ℝ)) <
        1 / 8) :
    ∃ final : Kakeya.Streamlined.TubeSubfamily family,
      let thinnedDeltaMax :=
        pureWZ2ThinnedDeltaMax net thinningEta
      let conflictBound :=
        pureWZ2ThinnedAnalyticConflictBound net thinningEta
      let samplingFraction :=
        Kakeya.realRpowENN delta (-thinningEta) / D
      final.family.Nonempty ∧
        final.family.IsInUnitBall ∧
        final.family.IsEssentiallyDistinct ∧
        (final.restrictShading shading).union ⊆ shading.union ∧
        (final.restrictShading shading).IsLambdaDense densityConstant ∧
        final.family.toBodyFamily.IsCKatzTao thinnedDeltaMax ∧
        ((conflictBound + 1)⁻¹ *
            ((1 / 2 : ENNReal) * samplingFraction)) *
            shading.mass ≤
          (final.restrictShading shading).mass ∧
        (((conflictBound + 1)⁻¹ * densityConstant) *
            ((1 / 2 : ENNReal) * samplingFraction *
              densityConstant)) *
            family.enncard ≤
          final.family.enncard := by
  rcases
      Kakeya.Streamlined.ProbabilisticThinning.probabilistic_thinning
        hdelta hdeltaOne hfamilyNonempty hfamilyBall shading
        D hdeltaMax hDtop thinningEta hthinningEta hthin
        net hmu hunion with
    ⟨thinned, hthinnedDeltaMax, _hthinnedCardUpper,
      hthinnedMass⟩
  let target : ENNReal :=
    Kakeya.realRpowENN delta (-thinningEta)
  let samplingFraction : ENNReal := target / D
  let thinnedShading := thinned.restrictShading shading
  have hsourceDense :
      shading.IsLambdaDense densityConstant := by
    show
      densityConstant * family.toBodyFamily.mass ≤ shading.mass
    change
      densityConstant *
          (∑ index : Fin family.card,
            (family.tube index).volume) ≤
        ∑ index : Fin family.card,
          MeasureTheory.volume (shading.carrier index)
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun index _ => hperTube index
  have hthinnedMassLower :
      (1 / 2 : ENNReal) * samplingFraction *
          densityConstant * family.toBodyFamily.mass ≤
        thinnedShading.mass := by
    calc
      (1 / 2 : ENNReal) * samplingFraction *
          densityConstant * family.toBodyFamily.mass =
        (1 / 2 : ENNReal) * samplingFraction *
          (densityConstant * family.toBodyFamily.mass) := by
            ring
      _ ≤
          (1 / 2 : ENNReal) * samplingFraction *
            shading.mass := by
        exact
          mul_le_mul_left'
            hsourceDense
            ((1 / 2 : ENNReal) * samplingFraction)
      _ ≤ thinnedShading.mass := by
        simpa [samplingFraction, target,
          thinnedShading] using hthinnedMass
  have hthinnedShadingMassUpper :
      thinnedShading.mass ≤
        thinned.family.toBodyFamily.mass := by
    change
      (∑ index : Fin thinned.family.card,
          MeasureTheory.volume
            (shading.carrier (thinned.embedding index))) ≤
        ∑ index : Fin thinned.family.card,
          (thinned.family.tube index).volume
    exact Finset.sum_le_sum fun index _ => by
      rw [thinned.tube_eq index]
      exact MeasureTheory.measure_mono
        (shading.subset_body (thinned.embedding index))
  have hfamilyMass :
      family.toBodyFamily.mass =
        family.enncard * Kakeya.deltaTubeVolume delta := by
    rw [tubeFamily_mass_eq_nominal]
    rfl
  have hthinnedFamilyMass :
      thinned.family.toBodyFamily.mass =
        thinned.family.enncard * Kakeya.deltaTubeVolume delta := by
    rw [tubeFamily_mass_eq_nominal]
    rfl
  have htubeVolumePositive :
      Kakeya.deltaTubeVolume delta ≠ 0 :=
    (tube_volume_scaling.2.1 delta hdelta hdeltaOne).1.ne'
  have htubeVolumeTop :
      Kakeya.deltaTubeVolume delta ≠ ⊤ :=
    (tube_volume_scaling.2.1 delta hdelta hdeltaOne).2
  have hthinnedCardinality :
      ((1 / 2 : ENNReal) * samplingFraction *
          densityConstant) * family.enncard ≤
        thinned.family.enncard := by
    have hwithVolume :
        (((1 / 2 : ENNReal) * samplingFraction *
            densityConstant) * family.enncard) *
            Kakeya.deltaTubeVolume delta ≤
          thinned.family.enncard *
            Kakeya.deltaTubeVolume delta := by
      calc
        (((1 / 2 : ENNReal) * samplingFraction *
            densityConstant) * family.enncard) *
            Kakeya.deltaTubeVolume delta =
          (1 / 2 : ENNReal) * samplingFraction *
            densityConstant * family.toBodyFamily.mass := by
          rw [hfamilyMass]
          ring
        _ ≤ thinnedShading.mass := hthinnedMassLower
        _ ≤ thinned.family.toBodyFamily.mass :=
          hthinnedShadingMassUpper
        _ =
            thinned.family.enncard *
              Kakeya.deltaTubeVolume delta := hthinnedFamilyMass
    exact
      (ENNReal.mul_le_mul_iff_right
        htubeVolumePositive htubeVolumeTop).mp (by
          simpa [mul_comm] using hwithVolume)
  have htargetPositive : 0 < target := by
    exact ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos hdelta (-thinningEta))
  have hDPositive : 0 < D := htargetPositive.trans_le hthin
  have hsamplingPositive : 0 < samplingFraction := by
    exact ENNReal.div_pos htargetPositive.ne' hDtop
  have hfamilyCardPositive : 0 < family.enncard := by
    change 0 < (family.card : ENNReal)
    exact_mod_cast hfamilyNonempty
  have hhalfSamplingPositive :
      0 < (1 / 2 : ENNReal) * samplingFraction :=
    ENNReal.mul_pos (by norm_num) hsamplingPositive.ne'
  have hcoefficientPositive :
      0 < (1 / 2 : ENNReal) * samplingFraction *
          densityConstant :=
    ENNReal.mul_pos hhalfSamplingPositive.ne'
      hdensityPositive.ne'
  have hthinnedCardPositive : 0 < thinned.family.enncard :=
    (ENNReal.mul_pos
      hcoefficientPositive.ne'
      hfamilyCardPositive.ne').trans_le hthinnedCardinality
  have hthinnedNonempty : thinned.family.Nonempty := by
    change 0 < thinned.family.card
    change 0 < (thinned.family.card : ENNReal) at hthinnedCardPositive
    exact_mod_cast hthinnedCardPositive
  have hthinnedBall : thinned.family.IsInUnitBall := by
    intro index
    rw [thinned.tube_eq index]
    exact hfamilyBall (thinned.embedding index)
  have hthinnedPerTube :
      ∀ index,
        densityConstant * (thinned.family.tube index).volume ≤
          MeasureTheory.volume (thinnedShading.carrier index) := by
    intro index
    rw [thinned.tube_eq index]
    exact hperTube (thinned.embedding index)
  let thinnedDeltaMax :=
    pureWZ2ThinnedDeltaMax net thinningEta
  let conflictBound :=
    pureWZ2ThinnedAnalyticConflictBound net thinningEta
  have hconflictTop : conflictBound ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by norm_num)
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top net.lossFactor_ne_top (by norm_num))
        ENNReal.ofReal_ne_top)
  have hdegree :
      ∀ index,
        ((Finset.univ.filter fun other =>
          ¬(thinned.family.tube index).EssentiallyDistinct
            (thinned.family.tube other)).card : ENNReal) ≤
          conflictBound := by
    exact
      pure_wz2_analytic_conflict_degree_from_deltaMax
        hdelta hdeltaOne hscaleSmall
        (by simpa [thinnedDeltaMax,
          pureWZ2ThinnedDeltaMax] using
          hthinnedDeltaMax)
  rcases
      pure_wz2_bicriteria_analytic_core_of_degree_and_per_tube
        hdelta hdeltaOne thinned.family hthinnedNonempty
        thinnedShading densityConstant conflictBound
        hdensityPositive hconflictTop hthinnedPerTube hdegree with
    ⟨selected, hselectedNonempty, hselectedDistinct,
      hselectedUnion, hselectedMass, hselectedCardinality,
      hselectedDense⟩
  let inner := selectedTubeSubfamily thinned.family selected
  let final := thinned.comp inner
  have hshading :
      final.restrictShading shading =
        selectedTubeShading thinnedShading selected := by
    rfl
  have hfinalBall : final.family.IsInUnitBall := by
    intro index
    rw [final.tube_eq index]
    exact hfamilyBall (final.embedding index)
  have hfinalUnion :
      (final.restrictShading shading).union ⊆ shading.union := by
    rw [hshading]
    exact hselectedUnion.trans (by
      intro point hpoint
      rcases hpoint with ⟨index, hindex⟩
      exact ⟨thinned.embedding index, hindex⟩)
  have hfinalDeltaMax :
      final.family.toBodyFamily.deltaMax ≤ thinnedDeltaMax := by
    have hsub :=
      Kakeya.Streamlined.subfamily_deltaMax_le inner.toBodySubfamily
    exact hsub.trans (by
      simpa [thinnedDeltaMax, pureWZ2ThinnedDeltaMax,
        ] using hthinnedDeltaMax)
  have hfinalCardinality :
      (((conflictBound + 1)⁻¹ * densityConstant) *
          ((1 / 2 : ENNReal) * samplingFraction *
            densityConstant)) *
          family.enncard ≤
        final.family.enncard := by
    calc
      (((conflictBound + 1)⁻¹ * densityConstant) *
          ((1 / 2 : ENNReal) * samplingFraction *
            densityConstant)) *
          family.enncard =
        ((conflictBound + 1)⁻¹ * densityConstant) *
          (((1 / 2 : ENNReal) * samplingFraction *
            densityConstant) * family.enncard) := by
              ring
      _ ≤
          ((conflictBound + 1)⁻¹ * densityConstant) *
            thinned.family.enncard := by
        gcongr
      _ ≤ (selectedTubeFamily thinned.family selected).enncard :=
        hselectedCardinality
      _ = final.family.enncard := rfl
  have hconflictLossZero : conflictBound + 1 ≠ 0 := by
    have hone : (0 : ENNReal) < 1 := by norm_num
    exact (lt_of_lt_of_le hone (le_add_left le_rfl)).ne'
  have hconflictLossTop : conflictBound + 1 ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hconflictTop, by norm_num⟩
  have hfinalMass :
      ((conflictBound + 1)⁻¹ *
          ((1 / 2 : ENNReal) * samplingFraction)) *
          shading.mass ≤
        (final.restrictShading shading).mass := by
    rw [hshading]
    calc
      ((conflictBound + 1)⁻¹ *
          ((1 / 2 : ENNReal) * samplingFraction)) *
          shading.mass =
        (conflictBound + 1)⁻¹ *
          ((1 / 2 : ENNReal) * samplingFraction *
            shading.mass) := by ring
      _ ≤ (conflictBound + 1)⁻¹ * thinnedShading.mass := by
        gcongr
      _ ≤
          (conflictBound + 1)⁻¹ *
            ((conflictBound + 1) *
              (selectedTubeShading thinnedShading selected).mass) := by
        gcongr
      _ = (selectedTubeShading thinnedShading selected).mass := by
        exact
          ENNReal.inv_mul_cancel_left
            hconflictLossZero hconflictLossTop
  refine
    ⟨final, ?_, hfinalBall, ?_, hfinalUnion, ?_, ?_,
      hfinalMass, ?_⟩
  · change (selectedTubeFamily thinned.family selected).Nonempty
    change 0 < selected.card
    exact Finset.card_pos.mpr hselectedNonempty
  · change (selectedTubeFamily thinned.family selected).IsEssentiallyDistinct
    exact hselectedDistinct
  · rw [hshading]
    exact hselectedDense
  · exact hfinalDeltaMax
  · simpa [thinnedDeltaMax, conflictBound, samplingFraction,
      pureWZ2ThinnedAnalyticConflictBound] using
      hfinalCardinality

end Kakeya.Assouad

end
