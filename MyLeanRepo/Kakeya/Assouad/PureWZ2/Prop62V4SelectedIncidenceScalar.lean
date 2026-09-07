import MyLeanRepo.Kakeya.Assouad.ExponentArithmetic
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Node1AsymptoticHelpers
import MyLeanRepo.Kakeya.Assouad.PureWZ2.PureCriticalFloorSelection
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4PureScalarInputs

/-!
# Scalar absorption for the selected-incidence ordinary coarse shading

Suppose the selected-incidence cropped shading has density
`rho^(s / 2)` and the ordinary overlap retains at least a `1 / 100000`
fraction of its mass.  The fixed overlap loss is absorbed by the remaining
half of the structural power:

`100000 * rho^s ≤ rho^(s / 2)`.

The receipt is selected from the fixed critical-floor data and output loss
before the runtime scales `delta` and `rho`.  This module contains no
geometric assumptions.
-/

noncomputable section

namespace Kakeya.Assouad

/--
A uniform small-scale receipt paying the selected-incidence ordinary overlap
loss with half of the positive structural exponent.
-/
structure Prop62V4SelectedIncidenceScalarReceipt
    {sigma floorLoss structuralBudget : ℝ}
    (outputLoss : ℝ)
    (critical :
      PureWZ2CriticalFloorSelectionData
        sigma floorLoss structuralBudget) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one : delta₀ ≤ 1
  overlap_absorption :
    ∀ {delta rho : ℝ},
      0 < delta → delta ≤ delta₀ →
      0 < rho → rho ≤ Real.rpow delta outputLoss →
        (100000 : ENNReal) *
            Kakeya.realRpowENN rho critical.structuralLoss ≤
          Kakeya.realRpowENN rho
            (critical.structuralLoss / 2)

/--
Choose the selected-incidence scalar receipt before the runtime source and
coarse scales.
-/
theorem prop62V4_selected_incidence_scalar_receipt
    {sigma floorLoss structuralBudget : ℝ}
    (outputLoss : ℝ)
    (outputLossPos : 0 < outputLoss)
    (critical :
      PureWZ2CriticalFloorSelectionData
        sigma floorLoss structuralBudget) :
    Nonempty
      (Prop62V4SelectedIncidenceScalarReceipt
        outputLoss critical) := by
  have halfLt :
      critical.structuralLoss / 2 <
        critical.structuralLoss := by
    linarith [critical.structuralLoss_pos]
  rcases
      exists_delta₀_const_mul_rpow_le
        100000 (by norm_num)
        (critical.structuralLoss / 2)
        critical.structuralLoss halfLt
    with
    ⟨radiusThreshold, radiusThresholdPos, _radiusThresholdLeOne,
      radiusAbsorption⟩
  rcases
      pure_wz2_exists_delta₀_rpow_le
        radiusThresholdPos outputLossPos
    with
    ⟨delta₀, delta₀Pos, delta₀LeOne, scaleSmall⟩
  refine
    ⟨{
      delta₀ := delta₀
      delta₀_pos := delta₀Pos
      delta₀_le_one := delta₀LeOne
      overlap_absorption := ?_
    }⟩
  intro delta rho deltaPos deltaLe rhoPos rhoUpper
  have absorbed :=
    radiusAbsorption rho rhoPos <|
      rhoUpper.trans (scaleSmall delta deltaPos deltaLe)
  norm_num at absorbed ⊢
  exact absorbed

namespace Prop62V4SelectedIncidenceScalarReceipt

/--
Pure mass bookkeeping for the downstream ordinary coarse shading.

The first premise is density of the selected-incidence cropped shading at
half the structural loss.  The second premise says that the ordinary overlap
retains at least `1 / 100000` of that cropped mass.  The conclusion is the
full structural-loss density required by the ordinary critical floor.
-/
theorem dense_of_half_dense_and_overlap
    {sigma floorLoss structuralBudget outputLoss : ℝ}
    {critical :
      PureWZ2CriticalFloorSelectionData
        sigma floorLoss structuralBudget}
    (receipt :
      Prop62V4SelectedIncidenceScalarReceipt
        outputLoss critical)
    {delta rho : ℝ}
    (deltaPos : 0 < delta)
    (deltaLe : delta ≤ receipt.delta₀)
    (rhoPos : 0 < rho)
    (rhoUpper : rho ≤ Real.rpow delta outputLoss)
    {bodyMass croppedMass ordinaryMass : ENNReal}
    (croppedDense :
      Kakeya.realRpowENN rho
          (critical.structuralLoss / 2) *
        bodyMass ≤ croppedMass)
    (ordinaryOverlap :
      (100000 : ENNReal)⁻¹ * croppedMass ≤ ordinaryMass) :
    Kakeya.realRpowENN rho critical.structuralLoss *
        bodyMass ≤ ordinaryMass := by
  have absorbed :=
    receipt.overlap_absorption
      deltaPos deltaLe rhoPos rhoUpper
  have divided :
      Kakeya.realRpowENN rho critical.structuralLoss ≤
        (100000 : ENNReal)⁻¹ *
          Kakeya.realRpowENN rho
            (critical.structuralLoss / 2) :=
    (ENNReal.mul_le_iff_le_inv
      (by norm_num) (by norm_num)).mp absorbed
  calc
    Kakeya.realRpowENN rho critical.structuralLoss *
          bodyMass ≤
        ((100000 : ENNReal)⁻¹ *
            Kakeya.realRpowENN rho
              (critical.structuralLoss / 2)) *
          bodyMass :=
      mul_le_mul_right' divided bodyMass
    _ =
        (100000 : ENNReal)⁻¹ *
          (Kakeya.realRpowENN rho
              (critical.structuralLoss / 2) *
            bodyMass) := by
      ring
    _ ≤ (100000 : ENNReal)⁻¹ * croppedMass :=
      mul_le_mul_left' croppedDense _
    _ ≤ ordinaryMass := ordinaryOverlap

end Prop62V4SelectedIncidenceScalarReceipt

namespace Prop62PaperAudit.V4

/--
The additional scalar data needed by the selected-incidence coarse witness.

Besides the ordinary-overlap receipt, this record strengthens the existing
V4 coarse-density estimate from the structural loss to half that loss.  Both
thresholds are chosen before the runtime scales and source.
-/
structure Prop62V4SelectedIncidencePureScalarExtension
    (polylogExponent cwaPower packetDensityExponent
      cwaLossExponent : ℕ)
    (sigma outputLoss : ℝ)
    (routing :
      Prop62V4PureCriticalFloorRoutingData
        polylogExponent cwaPower packetDensityExponent cwaLossExponent
        sigma outputLoss)
    (scalar :
      Prop62V4PureScalarInputs
        polylogExponent cwaPower packetDensityExponent cwaLossExponent
        sigma outputLoss routing) where
  overlap :
    Prop62V4SelectedIncidenceScalarReceipt
      outputLoss routing.critical
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_scalar : delta₀ ≤ scalar.delta₀
  delta₀_le_overlap : delta₀ ≤ overlap.delta₀
  reduced_coarse_density :
    ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
      ∀ {rho : ℝ}, 0 < rho →
        rho ≤ Real.rpow delta outputLoss →
          (576 * (55296 * Kakeya.deltaTubeVolume 1) : ENNReal) *
              Kakeya.realRpowENN rho
                (routing.critical.structuralLoss / 2) ≤
            Kakeya.realRpowENN delta
              ((packetDensityExponent : ℝ) *
                routing.numerics.hierarchy.stableLoss)

/--
Choose one threshold for the selected-incidence half-loss density and the
fixed ordinary-overlap loss.
-/
theorem prop62V4_selected_incidence_pure_scalar_extension
    (polylogExponent cwaPower packetDensityExponent
      cwaLossExponent : ℕ)
    (sigma outputLoss : ℝ)
    (outputLossPos : 0 < outputLoss)
    (routing :
      Prop62V4PureCriticalFloorRoutingData
        polylogExponent cwaPower packetDensityExponent cwaLossExponent
        sigma outputLoss)
    (scalar :
      Prop62V4PureScalarInputs
        polylogExponent cwaPower packetDensityExponent cwaLossExponent
        sigma outputLoss routing) :
    Nonempty
      (Prop62V4SelectedIncidencePureScalarExtension
        polylogExponent cwaPower packetDensityExponent cwaLossExponent
        sigma outputLoss routing scalar) := by
  rcases
      prop62V4_selected_incidence_scalar_receipt
        outputLoss outputLossPos routing.critical
    with
    ⟨overlap⟩
  let structuralLoss := routing.critical.structuralLoss
  let stableLoss := routing.numerics.hierarchy.stableLoss
  let exponentSum :=
    prop62V4CriticalExponentSum
      cwaPower packetDensityExponent cwaLossExponent
  have exponentSumPos : 0 < exponentSum := by
    dsimp only [exponentSum, prop62V4CriticalExponentSum]
    positivity
  have structuralExponentBound :
      structuralLoss * (1000 * exponentSum) ≤ outputLoss := by
    have structuralLossLe :
        structuralLoss ≤ outputLoss / (1000 * exponentSum) := by
      exact routing.critical.structuralLoss_le.trans <| by
        unfold prop62V4CriticalStructuralBudget
        exact min_le_right _ _
    rwa [le_div_iff₀ (mul_pos (by norm_num) exponentSumPos)]
      at structuralLossLe
  have packetLe :
      (packetDensityExponent : ℝ) ≤ exponentSum := by
    dsimp only [exponentSum, prop62V4CriticalExponentSum]
    have cwaNonneg : (0 : ℝ) ≤ cwaPower := by positivity
    have cwaLossNonneg : (0 : ℝ) ≤ cwaLossExponent := by
      positivity
    linarith
  have packetTimes :
      (packetDensityExponent : ℝ) * structuralLoss ≤
        outputLoss / 1000 := by
    have scaled :=
      mul_le_mul_of_nonneg_right packetLe
        routing.critical.structuralLoss_pos.le
    dsimp only [structuralLoss] at scaled ⊢
    nlinarith
  have halfGap :
      (packetDensityExponent : ℝ) * stableLoss <
        outputLoss * (structuralLoss / 2) := by
    dsimp only [stableLoss]
    rw [routing.numerics.hierarchy.stableLoss_eq]
    dsimp only [wz2PaperFinalStableLoss, structuralLoss] at *
    nlinarith [
      routing.critical.structuralLoss_pos,
      mul_pos outputLossPos routing.critical.structuralLoss_pos
    ]
  let gap : ℝ :=
    outputLoss * (structuralLoss / 2) -
      (packetDensityExponent : ℝ) * stableLoss
  have gapPos : 0 < gap := by
    dsimp only [gap]
    linarith
  let coefficient : ENNReal :=
    576 * (55296 * Kakeya.deltaTubeVolume 1)
  have coefficientFinite : coefficient ≠ ⊤ := by
    dsimp only [coefficient]
    exact
      ENNReal.mul_ne_top (by norm_num) <|
        ENNReal.mul_ne_top (by norm_num)
          deltaTubeVolume_one_ne_top
  rcases
      exists_delta_realRpowENN_bound
        coefficient coefficientFinite gapPos
    with
    ⟨densityDelta, densityDeltaPos, _densityDeltaLeOne,
      coefficientAbsorption⟩
  let delta₀ :=
    min scalar.delta₀ (min overlap.delta₀ densityDelta)
  have delta₀Pos : 0 < delta₀ := by
    exact
      lt_min scalar.delta₀_pos <|
        lt_min overlap.delta₀_pos densityDeltaPos
  refine
    ⟨{
      overlap := overlap
      delta₀ := delta₀
      delta₀_pos := delta₀Pos
      delta₀_le_scalar := min_le_left _ _
      delta₀_le_overlap :=
        (min_le_right _ _).trans (min_le_left _ _)
      reduced_coarse_density := ?_
    }⟩
  intro delta deltaPos deltaLe rho rhoPos rhoUpper
  have coefficientBound :
      coefficient ≤ Kakeya.realRpowENN delta (-gap) :=
    coefficientAbsorption delta deltaPos <|
      deltaLe.trans <|
        (min_le_right _ _).trans (min_le_right _ _)
  have targetPower :
      Kakeya.realRpowENN rho (structuralLoss / 2) ≤
        Kakeya.realRpowENN delta
          (outputLoss * (structuralLoss / 2)) :=
    pure_wz2_target_power_upper
      deltaPos rhoPos.le rhoUpper <| by
        dsimp only [structuralLoss]
        exact div_nonneg routing.critical.structuralLoss_pos.le (by norm_num)
  calc
    (576 * (55296 * Kakeya.deltaTubeVolume 1) : ENNReal) *
          Kakeya.realRpowENN rho
            (routing.critical.structuralLoss / 2) ≤
        Kakeya.realRpowENN delta (-gap) *
          Kakeya.realRpowENN delta
            (outputLoss * (structuralLoss / 2)) := by
      exact mul_le_mul coefficientBound targetPower bot_le bot_le
    _ =
        Kakeya.realRpowENN delta
          ((packetDensityExponent : ℝ) * stableLoss) := by
      rw [← realRpowENN_add deltaPos]
      congr 1
      dsimp only [gap]
      ring

end Prop62PaperAudit.V4

end Kakeya.Assouad

end
