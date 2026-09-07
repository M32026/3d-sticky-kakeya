import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62PaperAudit.StatementsV4
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperRefinementComposition
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperNearbyTopLevelConvexWolff
import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers

/-!
# Proposition 6.2 V4 fixed-grid preparation

This module performs only the fixed-grid step preceding the metric-parent and
four-degree stages.  A nearby-source extremal pair and the caller scale window
give an actual fixed-grid cleanup, regarded as a one-log refinement.  Any
subsequent sixty-log refinement of the cleaned shading then composes to a
sixty-one-log refinement of the original shading.

The boundary upper bound is not assumed.  It is obtained below a uniform
threshold from the positive exponent gap
`4 * sourceLoss < outputLoss`.  The factor four records the cubic loss in
the honest nearby-to-top-level CWA theorem together with the source density
power retained after the boundary deletion.
-/

noncomputable section

namespace Kakeya.Assouad.Prop62PaperAudit.V4

open MeasureTheory
open Kakeya.Assouad

attribute [local instance] Classical.propDecidable

private theorem directionLevelCount_le_logEnvelope
    {delta : ℝ}
    (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1) :
    (pureWZ2Prop62DirectionLevelCount delta : ENNReal) ≤
      2 * ENNReal.ofReal (1 + Real.log delta⁻¹) := by
  have hlogNonneg : 0 ≤ Real.log delta⁻¹ := by
    exact Real.log_nonneg ((one_le_inv₀ hdelta).mpr hdeltaOne)
  have hquotientNonneg :
      0 ≤ Real.log delta⁻¹ / Real.log 2 := by
    positivity
  have hfloor :
      (Nat.floor (Real.log delta⁻¹ / Real.log 2) : ℝ) ≤
        Real.log delta⁻¹ / Real.log 2 :=
    Nat.floor_le hquotientNonneg
  have hlogTwoHalf : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have hbound :
        Real.log (1 / 2 : ℝ) ≤ (1 / 2 : ℝ) - 1 :=
      Real.log_le_sub_one_of_pos (by norm_num)
    have hrewrite :
        Real.log (1 / 2 : ℝ) = -Real.log 2 := by
      rw [Real.log_div (by norm_num) (by norm_num)]
      simp
    rw [hrewrite] at hbound
    linarith
  have hquotient :
      Real.log delta⁻¹ / Real.log 2 ≤
        2 * Real.log delta⁻¹ := by
    rw [div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
    nlinarith
  have hreal :
      (pureWZ2Prop62DirectionLevelCount delta : ℝ) ≤
        2 * (1 + Real.log delta⁻¹) := by
    change
      ((Nat.floor (Real.log (1 / delta) / Real.log 2) + 1 : ℕ) : ℝ) ≤
        2 * (1 + Real.log delta⁻¹)
    rw [show 1 / delta = delta⁻¹ by simp]
    norm_num only [Nat.cast_add, Nat.cast_one]
    linarith
  have hconverted := ENNReal.ofReal_mono hreal
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)] at hconverted
  norm_num at hconverted ⊢
  simpa using hconverted

private theorem refinementFraction_one_le_half
    {delta : ℝ}
    (hdelta : 0 < delta)
    (hdeltaSmall : delta ≤ Real.exp (-2)) :
    wz1PaperRefinementFraction delta 1 ≤ (1 / 2 : ENNReal) := by
  have hexpNegPos : 0 < Real.exp (-2) := Real.exp_pos _
  have hinverse : Real.exp 2 ≤ delta⁻¹ := by
    have h := (inv_le_inv₀ hexpNegPos hdelta).mpr hdeltaSmall
    simpa [Real.exp_neg] using h
  have hlog : 2 ≤ Real.log delta⁻¹ := by
    rw [← Real.log_exp 2]
    exact Real.log_le_log (Real.exp_pos 2) hinverse
  unfold wz1PaperRefinementFraction
  simp only [pow_one, one_div]
  rw [ENNReal.inv_le_inv]
  have htwo : (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) := by
    norm_num
  rw [htwo]
  simpa [one_div] using ENNReal.ofReal_mono hlog

/--
The actual fixed-grid cleanup together with the one-log mass receipt needed
to regard it as a paper refinement.
-/
structure FixedGridPreparationData
    {delta rho : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading source)
    (hdelta : 0 < delta) where
  cleanup :
    FixedGridBoundaryRemovalData
      (rho := rho) shading hdelta
  refinement_retained :
    wz1PaperRefinementFraction delta 1 * shading.mass ≤
      cleanup.refined.mass

namespace FixedGridPreparationData

variable
    {delta rho : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {hdelta : 0 < delta}
    (preparation :
      FixedGridPreparationData
        (rho := rho) shading hdelta)

/-- The all-tube one-log refinement supplied by the fixed-grid cleanup. -/
noncomputable def fixedGridRefinement :
    WZ1PaperRefinement shading 1 where
  selected :=
    {
      family := source
      embedding := Function.Embedding.refl (Fin source.card)
      tube_eq := fun _ => rfl
    }
  refined := preparation.cleanup.refined
  subshading := preparation.cleanup.subshading
  retained_mass := preparation.refinement_retained

/--
Prepend the fixed-grid one-log refinement to any later sixty-log refinement
of the cleaned shading.
-/
noncomputable def composeSixtyLogRefinement
    (inner :
      WZ1PaperRefinement preparation.cleanup.refined 60) :
    WZ1PaperRefinement shading 61 := by
  simpa using
    (Classical.choice <|
      wz2_paper_refinement_composition
        shading 1 60 preparation.fixedGridRefinement inner).toRefinement

@[simp] theorem composeSixtyLogRefinement_selected_family
    (inner :
      WZ1PaperRefinement preparation.cleanup.refined 60) :
    (preparation.composeSixtyLogRefinement inner).selected.family =
      inner.selected.family :=
  rfl

@[simp] theorem composeSixtyLogRefinement_refined
    (inner :
      WZ1PaperRefinement preparation.cleanup.refined 60) :
    (preparation.composeSixtyLogRefinement inner).refined =
      inner.refined :=
  rfl

end FixedGridPreparationData

/--
An internal threshold receipt for the fixed-grid preparation.

Its only quantitative hypothesis is the honest positive gap needed to absorb
the nearby CWA loss, the source density loss, and the two boundary scale
factors.  The public Proposition 6.2 API remains unchanged.
-/
structure FixedGridPreparationThresholdReceipt
    (sourceLoss outputLoss : ℝ) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one_hundred : delta₀ ≤ 1 / 100
  prepare :
    ∀ {delta sigma : ℝ},
      ∀ (hdelta : 0 < delta), delta ≤ delta₀ →
        ∀ {source : Kakeya.Streamlined.TubeFamily delta},
          ∀ {shading : WZ1PaperTubeShading source},
            WZ2PaperIsExtremal
                sigma sourceLoss source shading →
              ∀ rho : Kakeya.Streamlined.AdmissibleScale delta,
                Real.rpow delta (1 - outputLoss) ≤ rho.1 →
                rho.1 ≤ Real.rpow delta outputLoss →
                  Nonempty
                    (FixedGridPreparationData
                      (rho := rho.1) shading hdelta)

/--
The nearby source extremality and scale window produce the actual fixed-grid
cleanup and its one-log refinement receipt below a uniform small scale.
-/
theorem fixedGridPreparationThreshold
    {sourceLoss outputLoss : ℝ}
    (hsourceLoss : 0 < sourceLoss)
    (hgap : 4 * sourceLoss < outputLoss)
    (hFixedGrid : FixedGridBoundaryRemovalStatement) :
    Nonempty
      (FixedGridPreparationThresholdReceipt
        sourceLoss outputLoss) := by
  rcases hFixedGrid with
    ⟨gridConstant, outerConstant, gridConstantPos,
      gridConstantTop, outerConstantPos, outerConstantTop,
      fixedGrid⟩
  let dimensionConstant : ENNReal :=
    wz2PaperNearbyTopLevelDimensionConstant
  let absorptionConstant : ENNReal :=
    4 * (gridConstant + outerConstant) * dimensionConstant
  have hdimensionConstantPos : 0 < dimensionConstant := by
    dsimp only [dimensionConstant]
    exact_mod_cast wz2PaperNearbyTopLevelDimensionConstant_pos
  have hdimensionConstantTop : dimensionConstant ≠ ⊤ := by
    exact ENNReal.natCast_ne_top _
  have habsorptionConstantTop : absorptionConstant ≠ ⊤ := by
    dsimp only [absorptionConstant]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by norm_num)
        (ENNReal.add_ne_top.mpr
          ⟨gridConstantTop, outerConstantTop⟩))
      hdimensionConstantTop
  have hgapPos : 0 < outputLoss - 4 * sourceLoss := by
    linarith
  rcases exists_delta_log_absorbed_ennreal
      absorptionConstant habsorptionConstantTop hgapPos
      (show 0 < (1 : ℕ) by norm_num) with
    ⟨absorptionDelta, absorptionDeltaPos,
      absorptionDeltaOne, absorb⟩
  let delta₀ : ℝ :=
    min (1 / 100 : ℝ)
      (min (Real.exp (-2)) absorptionDelta)
  have hdelta₀Pos : 0 < delta₀ := by
    dsimp only [delta₀]
    positivity
  refine
    ⟨{
      delta₀ := delta₀
      delta₀_pos := hdelta₀Pos
      delta₀_le_one_hundred := min_le_left _ _
      prepare := ?_
    }⟩
  intro delta sigma hdelta hdeltaBound source shading
    sourceExtremal rho hrhoLower hrhoUpper
  have hdeltaSmall : delta ≤ 1 / 100 :=
    hdeltaBound.trans (min_le_left _ _)
  have hdeltaOne : delta ≤ 1 :=
    hdeltaSmall.trans (by norm_num)
  have hdeltaAbsorption : delta ≤ absorptionDelta :=
    hdeltaBound.trans <|
      (min_le_right _ _).trans (min_le_right _ _)
  have hdeltaExp : delta ≤ Real.exp (-2) :=
    hdeltaBound.trans <|
      (min_le_right _ _).trans (min_le_left _ _)
  have hrhoPos : 0 < rho.1 :=
    hdelta.trans_le rho.2.1
  have hratioUpper :
      delta / rho.1 ≤ Real.rpow delta outputLoss := by
    rw [div_le_iff₀ hrhoPos]
    calc
      delta = Real.rpow delta 1 := by simp
      _ = Real.rpow delta ((1 - outputLoss) + outputLoss) := by
        congr 1
        ring
      _ = Real.rpow delta (1 - outputLoss) *
            Real.rpow delta outputLoss :=
        Real.rpow_add hdelta (1 - outputLoss) outputLoss
      _ ≤ rho.1 * Real.rpow delta outputLoss := by
        gcongr
        exact Real.rpow_nonneg hdelta.le outputLoss
      _ = Real.rpow delta outputLoss * rho.1 := mul_comm _ _
  let sourceConstant : ENNReal :=
    Kakeya.realRpowENN delta (-3 * sourceLoss)
  let topConstant : ENNReal :=
    dimensionConstant * sourceConstant
  have hsourceConstantOne : 1 ≤ sourceConstant := by
    have sourcePowerLe :
        Kakeya.realRpowENN delta (-sourceLoss) ≤ sourceConstant := by
      dsimp only [sourceConstant]
      exact
        pure_wz2_rpowENN_antitone hdelta hdeltaOne <| by
          linarith
    exact sourceExtremal.cwa_nearby_scales.1.trans sourcePowerLe
  have hdimensionConstantOne : 1 ≤ dimensionConstant := by
    dsimp only [dimensionConstant]
    exact_mod_cast wz2PaperNearbyTopLevelDimensionConstant_pos
  have htopConstantOne : 1 ≤ topConstant := by
    calc
      1 = 1 * 1 := by simp
      _ ≤ dimensionConstant * sourceConstant := by
        gcongr
  have htopConstantTop : topConstant ≠ ⊤ := by
    exact ENNReal.mul_ne_top hdimensionConstantTop <|
      by simp [sourceConstant, Kakeya.realRpowENN]
  have htopCWA :
      WZ2PaperConvexWolffBound source topConstant := by
    simpa only [topConstant, sourceConstant] using
      (wz2_paper_nearby_top_level_convex_wolff_canonical
        hdelta hdeltaSmall hsourceLoss
        sourceExtremal.cwa_nearby_scales)
  have hlevel :
      logarithmicLoss delta ≤
        2 * ENNReal.ofReal (1 + Real.log delta⁻¹) := by
    exact directionLevelCount_le_logEnvelope hdelta hdeltaOne
  have hscaleGrid :
      ENNReal.ofReal (delta / rho.1) ≤
        Kakeya.realRpowENN delta outputLoss :=
    ENNReal.ofReal_mono hratioUpper
  have hscaleOuter :
      ENNReal.ofReal rho.1 ≤
        Kakeya.realRpowENN delta outputLoss :=
    ENNReal.ofReal_mono hrhoUpper
  have habsorb :
      absorptionConstant *
          ENNReal.ofReal (1 + Real.log delta⁻¹) ≤
        Kakeya.realRpowENN delta
          (-(outputLoss - 4 * sourceLoss)) := by
    simpa only [pow_one] using
      absorb delta hdelta hdeltaAbsorption
  have hcoefficient :
      gridConstant * topConstant *
            ENNReal.ofReal (delta / rho.1) *
            logarithmicLoss delta +
          outerConstant * topConstant *
            ENNReal.ofReal rho.1 *
            logarithmicLoss delta ≤
        (1 / 2 : ENNReal) *
          Kakeya.realRpowENN delta sourceLoss := by
    let envelope : ENNReal :=
      ENNReal.ofReal (1 + Real.log delta⁻¹)
    let power : ENNReal :=
      Kakeya.realRpowENN delta outputLoss
    let sourceInverse : ENNReal :=
      Kakeya.realRpowENN delta (-3 * sourceLoss)
    let gapInverse : ENNReal :=
      Kakeya.realRpowENN delta
        (-(outputLoss - 4 * sourceLoss))
    have hpowerIdentity :
        sourceInverse * power =
          Kakeya.realRpowENN delta
            (outputLoss - 3 * sourceLoss) := by
      dsimp only [sourceInverse, power]
      rw [← realRpowENN_add hdelta]
      congr 1
      ring
    have hgapIdentity :
        gapInverse *
            Kakeya.realRpowENN delta
              (outputLoss - 3 * sourceLoss) =
          Kakeya.realRpowENN delta sourceLoss := by
      dsimp only [gapInverse]
      rw [← realRpowENN_add hdelta]
      congr 1
      ring
    calc
      gridConstant * topConstant *
              ENNReal.ofReal (delta / rho.1) *
              logarithmicLoss delta +
            outerConstant * topConstant *
              ENNReal.ofReal rho.1 *
              logarithmicLoss delta ≤
          gridConstant * topConstant * power *
              logarithmicLoss delta +
            outerConstant * topConstant * power *
              logarithmicLoss delta := by
        gcongr
      _ =
          ((gridConstant + outerConstant) *
              dimensionConstant * logarithmicLoss delta) *
            (sourceInverse * power) := by
        dsimp only [topConstant, sourceConstant]
        ring
      _ ≤
          ((gridConstant + outerConstant) *
              dimensionConstant * (2 * envelope)) *
            (sourceInverse * power) := by
        gcongr
      _ =
          ((1 / 2 : ENNReal) *
              (absorptionConstant * envelope)) *
            (sourceInverse * power) := by
        have hhalfFour : (1 / 2 : ENNReal) * 4 = 2 := by
          rw [show (4 : ENNReal) = 2 * 2 by norm_num, one_div,
            ← mul_assoc,
            ENNReal.inv_mul_cancel (by norm_num) (by norm_num),
            one_mul]
        dsimp only [absorptionConstant]
        calc
          ((gridConstant + outerConstant) *
                dimensionConstant * (2 * envelope)) *
              (sourceInverse * power) =
            (2 * ((gridConstant + outerConstant) *
                dimensionConstant * envelope)) *
              (sourceInverse * power) := by ring
          _ =
            (((1 / 2 : ENNReal) * 4) *
                ((gridConstant + outerConstant) *
                  dimensionConstant * envelope)) *
              (sourceInverse * power) := by rw [hhalfFour]
          _ =
            ((1 / 2 : ENNReal) *
                (4 * (gridConstant + outerConstant) *
                  dimensionConstant * envelope)) *
              (sourceInverse * power) := by ring
      _ ≤
          ((1 / 2 : ENNReal) * gapInverse) *
            (sourceInverse * power) := by
        gcongr
      _ =
          (1 / 2 : ENNReal) *
            Kakeya.realRpowENN delta sourceLoss := by
        rw [hpowerIdentity]
        calc
          ((1 / 2 : ENNReal) * gapInverse) *
              Kakeya.realRpowENN delta
                (outputLoss - 3 * sourceLoss) =
            (1 / 2 : ENNReal) *
              (gapInverse *
                Kakeya.realRpowENN delta
                  (outputLoss - 3 * sourceLoss)) := by ring
          _ = (1 / 2 : ENNReal) *
              Kakeya.realRpowENN delta sourceLoss := by
            rw [hgapIdentity]
  have hboundarySmall :
      gridConstant * topConstant *
              ENNReal.ofReal (delta / rho.1) *
              logarithmicLoss delta *
                (wz1PaperBodyFamily source).mass +
            outerConstant * topConstant *
              ENNReal.ofReal rho.1 *
              logarithmicLoss delta *
                (wz1PaperBodyFamily source).mass ≤
        shading.mass / 2 := by
    calc
      gridConstant * topConstant *
              ENNReal.ofReal (delta / rho.1) *
              logarithmicLoss delta *
                (wz1PaperBodyFamily source).mass +
            outerConstant * topConstant *
              ENNReal.ofReal rho.1 *
              logarithmicLoss delta *
                (wz1PaperBodyFamily source).mass =
          (gridConstant * topConstant *
                ENNReal.ofReal (delta / rho.1) *
                logarithmicLoss delta +
              outerConstant * topConstant *
                ENNReal.ofReal rho.1 *
                logarithmicLoss delta) *
            (wz1PaperBodyFamily source).mass := by
        ring
      _ ≤
          ((1 / 2 : ENNReal) *
              Kakeya.realRpowENN delta sourceLoss) *
            (wz1PaperBodyFamily source).mass := by
        gcongr
      _ =
          (1 / 2 : ENNReal) *
            (Kakeya.realRpowENN delta sourceLoss *
              (wz1PaperBodyFamily source).mass) := by
        ring
      _ ≤ (1 / 2 : ENNReal) * shading.mass := by
        gcongr
        exact sourceExtremal.dense
      _ = shading.mass / 2 := by
        simp only [ENNReal.div_eq_inv_mul, mul_one]
  have hboundary :=
    fixedGrid delta rho.1 hdelta hdeltaSmall hrhoPos rho.2.2
      rho.2.1 source sourceExtremal.cwa_nearby_scales.2.1
      shading sourceExtremal.cubical topConstant
      ⟨htopConstantOne, htopConstantTop⟩ htopCWA
  dsimp only at hboundary
  rcases hboundary.2.2 hboundarySmall with ⟨cleanup⟩
  refine ⟨{
    cleanup := cleanup
    refinement_retained := ?_
  }⟩
  calc
    wz1PaperRefinementFraction delta 1 * shading.mass ≤
        (1 / 2 : ENNReal) * shading.mass := by
      gcongr
      exact refinementFraction_one_le_half hdelta hdeltaExp
    _ = shading.mass / 2 := by
      simp only [ENNReal.div_eq_inv_mul, mul_one]
    _ ≤ cleanup.refined.mass := cleanup.mass_retention

end Kakeya.Assouad.Prop62PaperAudit.V4

end
