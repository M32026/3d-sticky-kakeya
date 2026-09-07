import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63PreliminaryLocalGrain
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.RetainedZeroExtensionFinitePlaniness
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63PreliminaryAnalyticSchedule

/-!
# Paper-order producer for the preliminary finite-grid grains

This module keeps the branch selected by finite planiness internal.  The
caller supplies one sticky output, its Property-(P) refinement, and scalar
bounds uniform over either dense or sparse planiness output.  The selected
plane map, shading, and positive-mass proof are then passed directly to the
finite-grid local-AD assembler.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory ENNReal

/-- The exact normalized mass loss of the dense one-coordinate planiness
branch used by the preliminary construction. -/
def proposition63PreliminaryDensePlaninessMassLoss
    {delta sigma planinessLoss coefficient : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (extremal : WZ2PaperCroppedIsExtremal
      sigma planinessLoss family shading)
    (schedule : OneScaleFiniteCoordinationSchedule delta coefficient)
    (kappa eta : ℝ) : ENNReal :=
  1 + (denseBalancedFiniteLeftFactor delta sigma planinessLoss 1)⁻¹ *
    denseBalancedFiniteRightFactor extremal.cwa_nearby_scales kappa eta 1
      schedule.requested schedule.variationScale

/-- The exact normalized mass loss of the sparse one-coordinate planiness
branch.  Its dependence on the selected relative band and CV package remains
explicit until a uniform logarithmic envelope is applied. -/
def proposition63PreliminarySparsePlaninessMassLoss
    {delta sigma planinessLoss coefficient kappa : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (extremal : WZ2PaperCroppedIsExtremal
      sigma planinessLoss family shading)
    (schedule : OneScaleFiniteCoordinationSchedule delta coefficient)
    (prepared : SparseRelativeBandPreparationData
      (kappa := kappa) shading
      (Kakeya.realRpowENN delta (2 - sigma + 3 * planinessLoss)))
    (package : SparseRelativeBandCVPackage shading prepared) : ENNReal :=
  1 + (sparseBalancedFiniteLeftFactor delta sigma planinessLoss 1)⁻¹ *
    sparseBalancedFiniteRightFactor extremal.cwa_nearby_scales 1
      schedule.requested schedule.variationScale prepared package

/-- A family-independent upper bound for the dense branch's right factor.
The quantitative separation `16 * actualRho ≤ kappa` replaces the runtime
nearby scale by the preselected transverse scale. -/
def proposition63PreliminaryDenseRightEnvelope
    {delta coefficient : ℝ}
    (schedule : OneScaleFiniteCoordinationSchedule delta coefficient)
    (kappa eta : ℝ) : ENNReal :=
  2 * (denseLocalDirectionLabelCount kappa eta : ENNReal) *
    ((localPlaneMapCapCount (8 * eta + kappa)
        (schedule.variationScale 0) : ENNReal) *
      27 * (2 * (denseLocalDirectionLabelCount kappa eta : ENNReal))) *
    27

/-- The physical logarithmic envelope for the relative sparse band. -/
def proposition63PreliminaryBandCountEnvelope
    (delta sigma planinessLoss : ℝ) : ENNReal :=
  ENNReal.ofReal
    ((2 + (2 - sigma + 3 * planinessLoss) / Real.log 2) *
      (1 + Real.log delta⁻¹))

/-- A family-independent upper bound for the sparse branch's right factor.
The numerator uses the actual incidence budget; the denominator uses the
half-gap left by `16 * actualRho ≤ kappa`. -/
def proposition63PreliminarySparseRightEnvelope
    {delta coefficient : ℝ}
    (schedule : OneScaleFiniteCoordinationSchedule delta coefficient)
    (sigma planinessLoss incidence kappa : ℝ) : ENNReal :=
  proposition63PreliminaryBandCountEnvelope delta sigma planinessLoss *
    (27 * (2 *
      (wz1OrientationCapCount
        (10 * (incidence + kappa / 4) / (kappa / 2))
        (schedule.variationScale 0) : ENNReal))) *
    27

/-- One explicit envelope dominates either planiness mass loss. -/
def proposition63PreliminaryPlaninessMassEnvelope
    {delta coefficient : ℝ}
    (schedule : OneScaleFiniteCoordinationSchedule delta coefficient)
    (sigma planinessLoss incidence kappa eta : ℝ) : ENNReal :=
  max
    (1 + (denseBalancedFiniteLeftFactor delta sigma planinessLoss 1)⁻¹ *
      proposition63PreliminaryDenseRightEnvelope schedule kappa eta)
    (1 + (sparseBalancedFiniteLeftFactor delta sigma planinessLoss 1)⁻¹ *
      proposition63PreliminarySparseRightEnvelope schedule sigma
        planinessLoss incidence kappa)

private lemma localPlaneMapCapCount_mono_radius
    {first second scale : ℝ}
    (hscale : 0 < scale) (hradius : first ≤ second) :
    localPlaneMapCapCount first scale ≤
      localPlaneMapCapCount second scale := by
  unfold localPlaneMapCapCount
  gcongr

private lemma wz1OrientationCapCount_mono_radius
    {first second scale : ℝ}
    (hscale : 0 < scale) (hradius : first ≤ second) :
    wz1OrientationCapCount first scale ≤
      wz1OrientationCapCount second scale := by
  unfold wz1OrientationCapCount
  gcongr

/-- The dense runtime right factor is controlled by the preselected envelope
once the nearby scale leaves a factor-two transverse gap. -/
lemma proposition63PreliminaryDenseRightFactor_le_envelope
    {delta sigma planinessLoss coefficient kappa eta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (extremal : WZ2PaperCroppedIsExtremal
      sigma planinessLoss family shading)
    (schedule : OneScaleFiniteCoordinationSchedule delta coefficient)
    (hnearby : 16 *
      (extremal.cwa_nearby_scales.chosenNearby
        (schedule.requested 0)).rho ≤ kappa) :
    denseBalancedFiniteRightFactor extremal.cwa_nearby_scales
        kappa eta 1 schedule.requested schedule.variationScale ≤
      proposition63PreliminaryDenseRightEnvelope schedule kappa eta := by
  have hradius :
      8 * eta + 16 *
          (extremal.cwa_nearby_scales.chosenNearby
            (schedule.requested 0)).rho ≤
        8 * eta + kappa := by
    linarith
  have hcap := localPlaneMapCapCount_mono_radius
    (schedule.variation_pos 0 (by norm_num)) hradius
  unfold denseBalancedFiniteRightFactor
    proposition63PreliminaryDenseRightEnvelope
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
  gcongr

/-- The sparse runtime right factor is controlled by the same pre-runtime
data and the physical logarithmic band envelope. -/
lemma proposition63PreliminarySparseRightFactor_le_envelope
    {delta sigma planinessLoss coefficient kappa incidence : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (extremal : WZ2PaperCroppedIsExtremal
      sigma planinessLoss family shading)
    (schedule : OneScaleFiniteCoordinationSchedule delta coefficient)
    (prepared : SparseRelativeBandPreparationData
      (kappa := kappa) shading
      (Kakeya.realRpowENN delta (2 - sigma + 3 * planinessLoss)))
    (package : SparseRelativeBandCVPackage shading prepared)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hdensityExponent : 0 ≤ 2 - sigma + 3 * planinessLoss)
    (hkappa : 0 < kappa)
    (hincidence : package.tau / kappa ≤ incidence)
    (hnearby : 16 *
      (extremal.cwa_nearby_scales.chosenNearby
        (schedule.requested 0)).rho ≤ kappa) :
    sparseBalancedFiniteRightFactor extremal.cwa_nearby_scales 1
        schedule.requested schedule.variationScale prepared package ≤
      proposition63PreliminarySparseRightEnvelope schedule sigma
        planinessLoss incidence kappa := by
  let actualRho :=
    (extremal.cwa_nearby_scales.chosenNearby
      (schedule.requested 0)).rho
  have hdenominator : kappa / 2 ≤ kappa - 8 * actualRho := by
    dsimp only [actualRho]
    linarith
  have hdenominatorPos : 0 < kappa - 8 * actualRho := by
    linarith
  have htargetDenominator : 0 < kappa / 2 := by positivity
  have hnumerator : package.tau / kappa + 4 * actualRho ≤
      incidence + kappa / 4 := by
    dsimp only [actualRho]
    linarith
  have hradius :
      10 * (package.tau / kappa + 4 * actualRho) /
          (kappa - 8 * actualRho) ≤
        10 * (incidence + kappa / 4) / (kappa / 2) := by
    apply div_le_div₀
    · have hincidenceNonnegative : 0 ≤ incidence :=
        (div_nonneg package.tau_pos.le hkappa.le).trans hincidence
      exact mul_nonneg (by norm_num) <| add_nonneg
        hincidenceNonnegative (div_nonneg hkappa.le (by norm_num))
    · exact mul_le_mul_of_nonneg_left hnumerator (by norm_num)
    · exact htargetDenominator
    · exact hdenominator
  have hcap := wz1OrientationCapCount_mono_radius
    (schedule.variation_pos 0 (by norm_num)) hradius
  have hband := prepared.bandCount_le_log_envelope extremal.nonempty
    hdelta hdeltaOne hdensityExponent
  unfold sparseBalancedFiniteRightFactor
    proposition63PreliminarySparseRightEnvelope
    proposition63PreliminaryBandCountEnvelope
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
  have hcapENN :
      (wz1OrientationCapCount
          (10 * (package.tau / kappa + 4 * actualRho) /
            (kappa - 8 * actualRho))
          (schedule.variationScale 0) : ENNReal) ≤
        (wz1OrientationCapCount
          (10 * (incidence + kappa / 4) / (kappa / 2))
          (schedule.variationScale 0) : ENNReal) := by
    exact_mod_cast hcap
  have hcost :
      (27 : ENNReal) * (2 * (wz1OrientationCapCount
          (10 * (package.tau / kappa + 4 * actualRho) /
            (kappa - 8 * actualRho))
          (schedule.variationScale 0) : ENNReal)) * 27 ≤
        27 * (2 * (wz1OrientationCapCount
          (10 * (incidence + kappa / 4) / (kappa / 2))
          (schedule.variationScale 0) : ENNReal)) * 27 := by
    gcongr
  simpa only [mul_assoc] using
    mul_le_mul hband hcost (by positivity) (by positivity)

/-- Both runtime branches are bounded by one explicit preselected envelope. -/
lemma proposition63PreliminaryPlaninessMassLoss_le_envelope
    {delta sigma planinessLoss coefficient kappa eta incidence : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (extremal : WZ2PaperCroppedIsExtremal
      sigma planinessLoss family shading)
    (schedule : OneScaleFiniteCoordinationSchedule delta coefficient)
    (hnearby : 16 *
      (extremal.cwa_nearby_scales.chosenNearby
        (schedule.requested 0)).rho ≤ kappa)
    (hkappa : 0 < kappa)
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (hdensityExponent : 0 ≤ 2 - sigma + 3 * planinessLoss) :
    proposition63PreliminaryDensePlaninessMassLoss extremal schedule
        kappa eta ≤
        proposition63PreliminaryPlaninessMassEnvelope schedule sigma
          planinessLoss incidence kappa eta ∧
      ∀ prepared : SparseRelativeBandPreparationData
          (kappa := kappa) shading
          (Kakeya.realRpowENN delta
            (2 - sigma + 3 * planinessLoss)),
        ∀ package : SparseRelativeBandCVPackage shading prepared,
          package.tau / kappa ≤ incidence →
          proposition63PreliminarySparsePlaninessMassLoss extremal schedule
              prepared package ≤
            proposition63PreliminaryPlaninessMassEnvelope schedule sigma
              planinessLoss incidence kappa eta := by
  constructor
  · apply le_max_of_le_left
    unfold proposition63PreliminaryDensePlaninessMassLoss
    gcongr
    exact proposition63PreliminaryDenseRightFactor_le_envelope
      extremal schedule hnearby
  · intro prepared package hincidence
    apply le_max_of_le_right
    unfold proposition63PreliminarySparsePlaninessMassLoss
    gcongr
    exact proposition63PreliminarySparseRightFactor_le_envelope
      extremal schedule prepared package hdelta hdeltaOne
      hdensityExponent hkappa hincidence hnearby

/-- Run the variable-`Q` finite-planiness dichotomy and immediately attach
the finite-grid LOW/HIGH local-AD estimates to its actual output.  In
particular, no independently chosen planiness refinement can be inserted
between the two steps. -/
theorem proposition63_preliminary_finite_grid_of_planiness
    {delta sigma initialInputLoss normalizationLoss preliminaryStickyLoss
      planinessLoss producerLoss gridLoss gridMidLoss localLoss reentryLoss
      tau epsilon₁ epsilon₃ coefficient incidence densityLoss kappa eta : ℝ}
    {N kMin kMax : ℕ}
    {rho : WZ2PaperRequestedScale delta}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent logExponent : ℕ}
    (initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent)
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := preliminaryStickyLoss)
      initialNormalized.croppedRefined rho logExponent)
    (propP : PureWZ2PropertyPData
      (sigma := sigma) (coarseShading := sticky.croppedCoarseShading)
      (tau := tau) epsilon₁ epsilon₃)
    (commonExtremal : WZ2PaperCroppedIsExtremal sigma planinessLoss
      initialNormalized.croppedFamily
      (ambientPropertyThreeCommonHull sticky propP.propertyThree))
    (hline : WZ1PaperIsLineClass initialNormalized.croppedFamily)
    (planinessSchedule : OneScaleFiniteCoordinationSchedule delta coefficient)
    (hdensityLoss : densityLoss = 2 - sigma + 3 * planinessLoss)
    (hplaninessLoss : 0 < planinessLoss)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hplaninessSmall : Kakeya.realRpowENN delta planinessLoss < 1 / 4)
    (hfixedAbsorb : (288 : ENNReal) * ENNReal.ofReal Real.pi ≤
      Kakeya.realRpowENN delta (-sigma + 4 * planinessLoss))
    (hsparsePackage : ∀ prepared : SparseRelativeBandPreparationData
      (kappa := kappa)
      (ambientPropertyThreeCommonHull sticky propP.propertyThree)
      (Kakeya.realRpowENN delta (2 - sigma + 3 * planinessLoss)),
        Nonempty (SparseRelativeBandCVPackage
          (ambientPropertyThreeCommonHull sticky propP.propertyThree)
          prepared))
    (hdenseIncidence : eta ≤ incidence)
    (hsparseIncidence : ∀ prepared : SparseRelativeBandPreparationData
      (kappa := kappa)
      (ambientPropertyThreeCommonHull sticky propP.propertyThree)
      (Kakeya.realRpowENN delta (2 - sigma + 3 * planinessLoss)),
      ∀ package : SparseRelativeBandCVPackage
        (ambientPropertyThreeCommonHull sticky propP.propertyThree) prepared,
          package.tau / kappa ≤ incidence)
    (hkappaNonnegative : 0 ≤ kappa)
    (hkappaPositive : 0 < kappa)
    (hkappaHalf : kappa ≤ 1 / 2)
    (hetaPositive : 0 < eta)
    (hetaHalf : eta ≤ 1 / 2)
    (hcoefficient : 0 < coefficient)
    (hactualSmall : ∀ coordinate, coordinate < 1 →
      (commonExtremal.cwa_nearby_scales.chosenNearby
        (planinessSchedule.requested coordinate)).rho < 1 / 8)
    (hnearbyGap : ∀ coordinate, coordinate < 1 →
      16 * (commonExtremal.cwa_nearby_scales.chosenNearby
        (planinessSchedule.requested coordinate)).rho ≤ kappa)
    (hnormalizationSticky : normalizationLoss ≤ preliminaryStickyLoss)
    (hstickyProducer : preliminaryStickyLoss ≤ producerLoss)
    (hproducerLocal : producerLoss ≤ localLoss)
    (hproducerReentry : producerLoss ≤ reentryLoss)
    (hmassEnvelopeSlack :
      (propertyThreeCommonHullMassLoss sticky *
          proposition63PreliminaryPlaninessMassEnvelope planinessSchedule
            sigma planinessLoss incidence kappa eta) *
          Kakeya.realRpowENN delta producerLoss ≤
        Kakeya.realRpowENN delta preliminaryStickyLoss)
    (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (hproducerLoss : 0 < producerLoss)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hcoarse : 0 < rho.1)
    (hcoarseSmall : rho.1 ≤ 1 / 10000)
    (hgridLoss : 0 < gridLoss)
    (hgridMidLoss : 0 < gridMidLoss)
    (hN : 0 < (N : ℝ))
    (hkMin : kMin = Nat.ceil ((N : ℝ) * gridMidLoss))
    (hkMinMax : kMin ≤ kMax)
    (hkMaxLower : (N : ℝ) * (1 - gridMidLoss) - 1 ≤ (kMax : ℝ))
    (hgridAdmissible : ∀ k, kMin ≤ k ∧ k ≤ kMax →
      delta ≤ finiteGridScaleVal delta N k ∧
        finiteGridScaleVal delta N k ≤ 1)
    (htauDef : tau = rho.1 * Real.sqrt 3)
    (htauPos : 0 < tau)
    (htauLe : tau ≤ 20 * rho.1)
    (hcoarseTau : rho.1 ≤ tau)
    (htauSq : tau ^ 2 ≤ 4 * rho.1)
    (htauOne : tau ≤ 1)
    (hepsilon₁ : 0 < epsilon₁)
    (hepsilon₃ : 0 < epsilon₃)
    (hepsilonSum : epsilon₁ + epsilon₃ < 1)
    (L₀Log Vtotal : ℝ)
    (hcoarseLog : rho.1 ≤ L₀Log)
    (hlog : 0 < epsilon₁ → ∀ L' : ℝ, 0 < L' → L' ≤ L₀Log →
      ∀ k : ℕ, 0 < k → (k : ℝ) ≤ 100 / L' ^ 3 →
        Real.rpow L' epsilon₁ *
          (288 + 56448 * (1 + Real.log (k : ℝ))) ≤ 125 / 108)
    (hpropertyThree : ∀ parent : Fin sticky.coarse.card, ∀ point : Point3,
      point ∈ propP.propertyThree.carrier parent →
        Kakeya.realRpowENN rho.1 (2 + 2 * epsilon₁) *
            ENNReal.ofReal tau ≤
          volume (propP.propertyThree.carrier parent ∩
            Metric.closedBall point tau))
    (haxis : 4 * (6 * rho.1) ^ 2 ≤
      (3 / 4 : ℝ) * (Real.rpow rho.1 (1 - epsilon₃)) ^ 2)
    (hVtotalPos : 0 < Vtotal)
    (hVtotal : volume sticky.croppedCoarseShading.union ≤
      ENNReal.ofReal Vtotal)
    (highConstant : ENNReal)
    (hhighOne : (1 : ENNReal) ≤ highConstant)
    (hhighTop : highConstant ≠ ⊤)
    (hhighArithmetic : ∀ queryScale : ℝ,
      0 < queryScale → queryScale < 5 * rho.1 ^ 2 →
      ENNReal.ofReal
        ((Vtotal /
            (Real.rpow rho.1 (1 + 7 * epsilon₁ + epsilon₃) *
              tau ^ 2 / 200)) *
          (2 * (2 * (40 * rho.1)) / queryScale + 2)) ≤
        highConstant)
    (hlowAbsorb : Kakeya.realRpowENN rho.1 (-1) ≤
      Kakeya.realRpowENN delta (-gridLoss))
    (hhighAbsorb : 10 * highConstant ≤
      Kakeya.realRpowENN delta (-gridLoss))
    (habsorbInterpolation : (100 : ℝ) * Real.rpow delta
      (-gridLoss - gridMidLoss - 1 / (N : ℝ)) ≤
        Real.rpow delta (-localLoss))
    (habsorbFine : (100 : ℝ) * Real.rpow delta
      (-gridMidLoss - 1 / (N : ℝ)) ≤
        Real.rpow delta (-localLoss)) :
    Nonempty (Proposition63PreliminaryLocalGrainData
      (localLoss := localLoss) (reentryLoss := reentryLoss)
      initialNormalized) := by
  have hparentKappa : ∀ coordinate, coordinate < 1 →
      8 * (commonExtremal.cwa_nearby_scales.chosenNearby
        (planinessSchedule.requested coordinate)).rho < kappa := by
    intro coordinate hcoordinate
    have hrho := (commonExtremal.cwa_nearby_scales.chosenNearby
      (planinessSchedule.requested coordinate)).scaleData.rho_pos
    linarith [hnearbyGap coordinate hcoordinate]
  rcases high_multiplicity_balanced_direction_dichotomy commonExtremal hline
      hdeltaSmall hdensityLoss hplaninessLoss hplaninessSmall hfixedAbsorb with
    ⟨dichotomy⟩
  rcases high_multiplicity_balanced_weak_finite_lipschitz_coefficient
      commonExtremal.cwa_nearby_scales commonExtremal.nonempty hline
      (by simpa [hdensityLoss] using dichotomy) hsparsePackage
      1 planinessSchedule.requested planinessSchedule.spatialScale
      planinessSchedule.variationScale planinessSchedule.K
      hkappaNonnegative hkappaPositive hkappaHalf hdelta hetaPositive
      hetaHalf hcoefficient hactualSmall hparentKappa
      planinessSchedule.spatial_pos planinessSchedule.variation_pos
      planinessSchedule.K_pos planinessSchedule.spatial_aligned
      planinessSchedule.covers with
    ⟨finite⟩
  have hboundedIncidence : finite.incidence ≤ incidence := by
    rcases finite.branch_formula with hdense | hsparse
    · rw [hdense.1]
      exact hdenseIncidence
    · rcases hsparse with
        ⟨prepared, package, hincidence, _hleft, _hright⟩
      rw [hincidence]
      exact hsparseIncidence prepared package
  let bounded : BoundedBalancedFinitePlaninessData
      (coefficient := coefficient)
      (ambientPropertyThreeCommonHull sticky propP.propertyThree) incidence :=
    { data := finite.toPlaniness hdelta
      incidence_le := hboundedIncidence }
  have hboundedMass : 0 < bounded.data.refinement.shading.mass := by
    exact finite.refinement_mass_pos hdelta
      (cropped_extremal_shading_mass_pos commonExtremal hline hdeltaSmall)
  have hincidenceNonnegative : 0 ≤ incidence :=
    hetaPositive.le.trans hdenseIncidence
  have hmassSlack :
      (propertyThreeCommonHullMassLoss sticky * bounded.data.massLoss) *
          Kakeya.realRpowENN delta producerLoss ≤
        Kakeya.realRpowENN delta preliminaryStickyLoss := by
    have hdensityExponent : 0 ≤ 2 - sigma + 3 * planinessLoss := by
      linarith
    have henvelope :=
      proposition63PreliminaryPlaninessMassLoss_le_envelope
        (eta := eta) (incidence := incidence) commonExtremal
        planinessSchedule (hnearbyGap 0 (by norm_num)) hkappaPositive
        hdelta hdeltaOne.le hdensityExponent
    rcases finite.branch_formula with hdense | hsparse
    · have hbranch : bounded.data.massLoss ≤
          proposition63PreliminaryPlaninessMassEnvelope planinessSchedule
            sigma planinessLoss incidence kappa eta := by
        simpa only [bounded,
          HighMultiplicityBalancedFiniteLipschitzOutput.toPlaniness,
          BalancedFinitePlaninessData.massLoss,
          proposition63PreliminaryDensePlaninessMassLoss, hdense.2.1,
          hdense.2.2] using henvelope.1
      exact (mul_le_mul_right'
        (mul_le_mul_left' hbranch (propertyThreeCommonHullMassLoss sticky))
        (Kakeya.realRpowENN delta producerLoss)).trans hmassEnvelopeSlack
    · rcases hsparse with
        ⟨prepared, package, _hincidence, hleft, hright⟩
      have hbranch : bounded.data.massLoss ≤
          proposition63PreliminaryPlaninessMassEnvelope planinessSchedule
            sigma planinessLoss incidence kappa eta := by
        simpa only [bounded,
          HighMultiplicityBalancedFiniteLipschitzOutput.toPlaniness,
          BalancedFinitePlaninessData.massLoss,
          proposition63PreliminarySparsePlaninessMassLoss, hleft, hright] using
          henvelope.2 prepared package (hsparseIncidence prepared package)
      exact (mul_le_mul_right'
        (mul_le_mul_left' hbranch (propertyThreeCommonHullMassLoss sticky))
        (Kakeya.realRpowENN delta producerLoss)).trans hmassEnvelopeSlack
  exact proposition63_preliminary_local_grain_finite_grid_of_bounded
    initialNormalized sticky propP bounded hboundedMass hincidenceNonnegative
    hnormalizationSticky hstickyProducer hproducerLocal hproducerReentry
    hmassSlack hdelta hdeltaOne hproducerLoss hsigma hsigmaOne
    hcoarse hcoarseSmall hgridLoss hgridMidLoss hN hkMin hkMinMax
    hkMaxLower hgridAdmissible htauDef htauPos htauLe hcoarseTau htauSq
    htauOne hepsilon₁ hepsilon₃ hepsilonSum L₀Log Vtotal hcoarseLog hlog
    hpropertyThree haxis hVtotalPos hVtotal highConstant hhighOne hhighTop
    hhighArithmetic hlowAbsorb hhighAbsorb habsorbInterpolation habsorbFine

/-- Instantiate the two pre-runtime analytic producers before running the
preliminary finite-grid construction.  The runtime Property-(P) object, its
common-hull extremality, and the sparse CV package are all generated inside
this theorem from the same sticky output. -/
theorem proposition63_preliminary_finite_grid_of_analytic_schedule
    {delta sigma initialInputLoss normalizationLoss preliminaryStickyLoss
      planinessLoss producerLoss gridLoss gridMidLoss localLoss reentryLoss
      coefficient incidence densityLoss kappa eta : ℝ}
    {N kMin kMax : ℕ}
    {rho : WZ2PaperRequestedScale delta}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent logExponent : ℕ}
    (initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent)
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := preliminaryStickyLoss)
      initialNormalized.croppedRefined rho logExponent)
    (analytic : Proposition63PreliminaryAnalyticSchedule
      sigma preliminaryStickyLoss planinessLoss)
    (hcoarseAnalytic : rho.1 ≤ analytic.propertyPScale)
    (scaleFactor : ℕ) (hscaleFactor : 0 < scaleFactor)
    (hrhoAligned : rho.1 = (scaleFactor : ℝ) * delta)
    (hstickyPlaniness : preliminaryStickyLoss ≤ planinessLoss)
    (hcommonSlack : propertyThreeCommonHullMassLoss sticky *
        Kakeya.realRpowENN delta planinessLoss ≤
      Kakeya.realRpowENN delta preliminaryStickyLoss)
    (hnormalizationSticky : normalizationLoss ≤ preliminaryStickyLoss)
    (hdelta : 0 < delta) (hdeltaOne : delta < 1)
    (planinessSchedule : OneScaleFiniteCoordinationSchedule delta coefficient)
    (hdensityLoss : densityLoss = 2 - sigma + 3 * planinessLoss)
    (hplaninessLoss : 0 < planinessLoss)
    (hdeltaSmall : delta ≤ 1 / 24)
    (hplaninessSmall : Kakeya.realRpowENN delta planinessLoss < 1 / 4)
    (hfixedAbsorb : (288 : ENNReal) * ENNReal.ofReal Real.pi ≤
      Kakeya.realRpowENN delta (-sigma + 4 * planinessLoss))
    (hdenseIncidence : eta ≤ incidence)
    (hsparseIncidence : ∀ prepared : SparseRelativeBandPreparationData
      (kappa := kappa)
      (ambientPropertyThreeCommonHull sticky
        (analytic.parameters sticky hcoarseAnalytic).propP.propertyThree)
      (Kakeya.realRpowENN delta (2 - sigma + 3 * planinessLoss)),
      ∀ package : SparseRelativeBandCVPackage
        (ambientPropertyThreeCommonHull sticky
          (analytic.parameters sticky hcoarseAnalytic).propP.propertyThree)
          prepared,
          package.tau / kappa ≤ incidence)
    (hkappaNonnegative : 0 ≤ kappa)
    (hkappaPositive : 0 < kappa)
    (hkappaHalf : kappa ≤ 1 / 2)
    (hetaPositive : 0 < eta)
    (hetaHalf : eta ≤ 1 / 2)
    (hcoefficient : 0 < coefficient)
    (hactualSmall : ∀ coordinate, coordinate < 1 →
      ((propertyThreeCommonHull_extremal sticky
        (analytic.parameters sticky hcoarseAnalytic).propP
        initialNormalized.cropped_cubical
        scaleFactor hscaleFactor hrhoAligned
        (initialNormalized.final_extremal.mono_loss hnormalizationSticky)
        hdeltaOne hstickyPlaniness hcommonSlack hplaninessLoss
        ).cwa_nearby_scales.chosenNearby
          (planinessSchedule.requested coordinate)).rho < 1 / 8)
    (hnearbyGap : ∀ coordinate, coordinate < 1 →
      16 * ((propertyThreeCommonHull_extremal sticky
        (analytic.parameters sticky hcoarseAnalytic).propP
        initialNormalized.cropped_cubical
        scaleFactor hscaleFactor hrhoAligned
        (initialNormalized.final_extremal.mono_loss hnormalizationSticky)
        hdeltaOne hstickyPlaniness hcommonSlack hplaninessLoss
        ).cwa_nearby_scales.chosenNearby
          (planinessSchedule.requested coordinate)).rho ≤ kappa)
    (hstickyProducer : preliminaryStickyLoss ≤ producerLoss)
    (hproducerLocal : producerLoss ≤ localLoss)
    (hproducerReentry : producerLoss ≤ reentryLoss)
    (hmassEnvelopeSlack :
      (propertyThreeCommonHullMassLoss sticky *
          proposition63PreliminaryPlaninessMassEnvelope planinessSchedule
            sigma planinessLoss incidence kappa eta) *
          Kakeya.realRpowENN delta producerLoss ≤
        Kakeya.realRpowENN delta preliminaryStickyLoss)
    (hproducerLoss : 0 < producerLoss)
    (hsigma : 0 < sigma) (hsigmaOne : sigma < 1)
    (hdeltaSparse : delta ≤ analytic.sparseCVScale)
    (hgridLoss : 0 < gridLoss)
    (hgridMidLoss : 0 < gridMidLoss)
    (hN : 0 < (N : ℝ))
    (hkMin : kMin = Nat.ceil ((N : ℝ) * gridMidLoss))
    (hkMinMax : kMin ≤ kMax)
    (hkMaxLower : (N : ℝ) * (1 - gridMidLoss) - 1 ≤ (kMax : ℝ))
    (hgridAdmissible : ∀ k, kMin ≤ k ∧ k ≤ kMax →
      delta ≤ finiteGridScaleVal delta N k ∧
        finiteGridScaleVal delta N k ≤ 1)
    (Vtotal : ℝ)
    (hVtotalPos : 0 < Vtotal)
    (hVtotal : volume sticky.croppedCoarseShading.union ≤
      ENNReal.ofReal Vtotal)
    (highConstant : ENNReal)
    (hhighOne : (1 : ENNReal) ≤ highConstant)
    (hhighTop : highConstant ≠ ⊤)
    (hhighArithmetic : ∀ queryScale : ℝ,
      0 < queryScale → queryScale < 5 * rho.1 ^ 2 →
      ENNReal.ofReal
        ((Vtotal /
            (Real.rpow rho.1
              (1 + 7 * (analytic.parameters sticky
                hcoarseAnalytic).epsilon₁ +
                (analytic.parameters sticky hcoarseAnalytic).epsilon₃) *
              (analytic.parameters sticky hcoarseAnalytic).tau ^ 2 / 200)) *
          (2 * (2 * (40 * rho.1)) / queryScale + 2)) ≤ highConstant)
    (hlowAbsorb : Kakeya.realRpowENN rho.1 (-1) ≤
      Kakeya.realRpowENN delta (-gridLoss))
    (hhighAbsorb : 10 * highConstant ≤
      Kakeya.realRpowENN delta (-gridLoss))
    (habsorbInterpolation : (100 : ℝ) * Real.rpow delta
      (-gridLoss - gridMidLoss - 1 / (N : ℝ)) ≤
        Real.rpow delta (-localLoss))
    (habsorbFine : (100 : ℝ) * Real.rpow delta
      (-gridMidLoss - 1 / (N : ℝ)) ≤
        Real.rpow delta (-localLoss)) :
    Nonempty (Proposition63PreliminaryLocalGrainData
      (localLoss := localLoss) (reentryLoss := reentryLoss)
      initialNormalized) := by
  let parameters := analytic.parameters sticky hcoarseAnalytic
  have sourceExtremal : WZ2PaperCroppedIsExtremal sigma
      preliminaryStickyLoss initialNormalized.croppedFamily
      initialNormalized.croppedRefined :=
    initialNormalized.final_extremal.mono_loss hnormalizationSticky
  let commonExtremal := propertyThreeCommonHull_extremal sticky
    parameters.propP initialNormalized.cropped_cubical scaleFactor
    hscaleFactor hrhoAligned sourceExtremal hdeltaOne hstickyPlaniness
    hcommonSlack hplaninessLoss
  have sparsePackage : ∀ prepared : SparseRelativeBandPreparationData
      (kappa := kappa)
      (ambientPropertyThreeCommonHull sticky parameters.propP.propertyThree)
      (Kakeya.realRpowENN delta (2 - sigma + 3 * planinessLoss)),
        Nonempty (SparseRelativeBandCVPackage
          (ambientPropertyThreeCommonHull sticky parameters.propP.propertyThree)
          prepared) := by
    intro prepared
    exact analytic.sparseCV prepared commonExtremal.nonempty
      initialNormalized.line_class commonExtremal hdelta hdeltaSparse
  apply proposition63_preliminary_finite_grid_of_planiness initialNormalized
    sticky parameters.propP commonExtremal initialNormalized.line_class
    planinessSchedule hdensityLoss hplaninessLoss hdeltaSmall
    hplaninessSmall hfixedAbsorb sparsePackage hdenseIncidence
    hsparseIncidence hkappaNonnegative hkappaPositive hkappaHalf hetaPositive
    hetaHalf hcoefficient hactualSmall hnearbyGap
    hnormalizationSticky hstickyProducer hproducerLocal hproducerReentry
    hmassEnvelopeSlack hdelta hdeltaOne hproducerLoss
    hsigma hsigmaOne
    sticky.coarse_extremal.delta_pos
    (hcoarseAnalytic.trans analytic.propertyPScale_small) hgridLoss
    hgridMidLoss hN hkMin hkMinMax hkMaxLower hgridAdmissible
    parameters.tau_def parameters.tau_pos parameters.tau_le_twenty
    parameters.scale_le_tau parameters.tau_sq parameters.tau_le_one
    parameters.epsilon₁_pos parameters.epsilon₃_pos parameters.epsilon_sum
    parameters.logScale Vtotal parameters.scale_le_logScale
    parameters.log_absorption parameters.propertyThree_full
    parameters.ax_condition hVtotalPos hVtotal highConstant hhighOne
    hhighTop hhighArithmetic hlowAbsorb hhighAbsorb habsorbInterpolation
    habsorbFine

end Kakeya.Assouad.PureWZ2

end
