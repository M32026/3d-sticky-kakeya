import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4CriticalFloorRouting
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62PaperFinalV4ScalarThreshold
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperNearbyTopLevelConvexWolff

/-!
# Pure critical-floor scalar inputs for Proposition 6.2 V4

This module reproduces the scalar threshold interface used by the final V4
assembly while retaining a `PureWZ2CriticalFloorSelectionData` witness.
It does not convert that witness to the historical carrier-based critical
floor and does not assume an ordinary-to-cropped floor reduction.
-/

noncomputable section

namespace Kakeya.Assouad.Prop62PaperAudit.V4

open Kakeya.Assouad

private theorem pureScalar_directionLevelCount_le_logEnvelope
    {delta : ℝ}
    (deltaPos : 0 < delta)
    (deltaLeOne : delta ≤ 1) :
    (pureWZ2Prop62DirectionLevelCount delta : ENNReal) ≤
      2 * ENNReal.ofReal (1 + Real.log delta⁻¹) := by
  have logNonneg : 0 ≤ Real.log delta⁻¹ :=
    Real.log_nonneg ((one_le_inv₀ deltaPos).mpr deltaLeOne)
  have quotientNonneg :
      0 ≤ Real.log delta⁻¹ / Real.log 2 := by
    positivity
  have floorLe :
      (Nat.floor (Real.log delta⁻¹ / Real.log 2) : ℝ) ≤
        Real.log delta⁻¹ / Real.log 2 :=
    Nat.floor_le quotientNonneg
  have logTwoHalf : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have bound :
        Real.log (1 / 2 : ℝ) ≤ (1 / 2 : ℝ) - 1 :=
      Real.log_le_sub_one_of_pos (by norm_num)
    have rewrite :
        Real.log (1 / 2 : ℝ) = -Real.log 2 := by
      rw [Real.log_div (by norm_num) (by norm_num)]
      simp
    rw [rewrite] at bound
    linarith
  have quotientLe :
      Real.log delta⁻¹ / Real.log 2 ≤
        2 * Real.log delta⁻¹ := by
    rw [div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
    nlinarith
  have realBound :
      (pureWZ2Prop62DirectionLevelCount delta : ℝ) ≤
        2 * (1 + Real.log delta⁻¹) := by
    change
      ((Nat.floor (Real.log (1 / delta) / Real.log 2) + 1 : ℕ) : ℝ) ≤
        2 * (1 + Real.log delta⁻¹)
    rw [show 1 / delta = delta⁻¹ by simp]
    norm_num only [Nat.cast_add, Nat.cast_one]
    linarith
  have converted := ENNReal.ofReal_mono realBound
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)] at converted
  norm_num at converted ⊢
  simpa using converted

private theorem pureScalar_ratio_le_output_power
    {delta rho outputLoss : ℝ}
    (deltaPos : 0 < delta)
    (rhoPos : 0 < rho)
    (rhoLower : Real.rpow delta (1 - outputLoss) ≤ rho) :
    delta / rho ≤ Real.rpow delta outputLoss := by
  rw [div_le_iff₀ rhoPos]
  calc
    delta = Real.rpow delta 1 := (Real.rpow_one delta).symm
    _ =
        Real.rpow delta (1 - outputLoss) *
          Real.rpow delta outputLoss := by
      calc
        Real.rpow delta 1 =
            Real.rpow delta ((1 - outputLoss) + outputLoss) := by
          congr 1
          ring
        _ =
            Real.rpow delta (1 - outputLoss) *
              Real.rpow delta outputLoss :=
          Real.rpow_add deltaPos (1 - outputLoss) outputLoss
    _ ≤ rho * Real.rpow delta outputLoss :=
      mul_le_mul_of_nonneg_right rhoLower
        (Real.rpow_nonneg deltaPos.le outputLoss)
    _ = Real.rpow delta outputLoss * rho := mul_comm _ _

/--
The complete scalar threshold bundle consumed after metric-parent and
four-degree witnesses are fixed.  It is deliberately indexed by the pure
critical-floor routing receipt rather than by
`WZ2PaperFinalParameterSelectionData`.
-/
structure Prop62V4PureScalarInputs
    (polylogExponent cwaPower packetDensityExponent cwaLossExponent : ℕ)
    (sigma outputLoss : ℝ)
    (routing :
      Prop62V4PureCriticalFloorRoutingData
        polylogExponent cwaPower packetDensityExponent cwaLossExponent
        sigma outputLoss) where
  metric_loss :
    (cwaPower : ℝ) * routing.numerics.hierarchy.stableLoss ≤
      outputLoss / 100
  packet_loss :
    (packetDensityExponent : ℝ) *
        routing.numerics.hierarchy.stableLoss < 1
  source_to_working :
    routing.numerics.hierarchy.sourceLoss ≤
      routing.numerics.hierarchy.stableLoss
  structural_to_final :
    routing.critical.structuralLoss ≤
      routing.numerics.hierarchy.finalStrongLoss
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one_hundred : delta₀ ≤ 1 / 100
  fixed_grid_density :
    ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
      Kakeya.realRpowENN delta
          routing.numerics.hierarchy.stableLoss ≤
        (1 / 2 : ENNReal) *
          Kakeya.realRpowENN delta
            routing.numerics.hierarchy.sourceLoss
  rho_small :
    ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
      ∀ {rho : ℝ},
        rho ≤ Real.rpow delta outputLoss →
          rho ≤ 1 / 24
  rho_power_small :
    ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
      ∀ {rho : ℝ},
        rho ≤ Real.rpow delta outputLoss →
          rho ≤ 1 / 100
  ratio_small :
    ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
      ∀ {rho : ℝ}, 0 < rho →
        Real.rpow delta (1 - outputLoss) ≤ rho →
          delta / rho ≤ 1 / 24
  rho_critical :
    ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
      ∀ {rho : ℝ},
        rho ≤ Real.rpow delta outputLoss →
          rho ≤ routing.critical.delta₀
  ratio_critical :
    ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
      ∀ {rho : ℝ}, 0 < rho →
        Real.rpow delta (1 - outputLoss) ≤ rho →
          delta / rho ≤ routing.critical.delta₀
  parent_cwa :
    ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
      ∀ {rho : ℝ}, 0 < rho →
        rho ≤ Real.rpow delta outputLoss →
          Kakeya.realRpowENN delta
              (-(cwaLossExponent : ℝ) *
                routing.numerics.hierarchy.stableLoss) ≤
            Kakeya.realRpowENN rho
              (-routing.critical.structuralLoss)
  fiber_cwa :
    ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
      ∀ {rho : ℝ}, 0 < rho →
        Real.rpow delta (1 - outputLoss) ≤ rho →
          Kakeya.realRpowENN delta
              (-(cwaLossExponent : ℝ) *
                routing.numerics.hierarchy.stableLoss) ≤
            Kakeya.realRpowENN (delta / rho)
              (-routing.critical.structuralLoss)
  coarse_density :
    ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
      ∀ {rho : ℝ}, 0 < rho →
        rho ≤ Real.rpow delta outputLoss →
          (576 * (55296 * Kakeya.deltaTubeVolume 1) : ENNReal) *
              Kakeya.realRpowENN rho
                routing.critical.structuralLoss ≤
            Kakeya.realRpowENN delta
              ((packetDensityExponent : ℝ) *
                routing.numerics.hierarchy.stableLoss)
  fiber_density :
    ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
      ∀ {rho : ℝ}, 0 < rho →
        Real.rpow delta (1 - outputLoss) ≤ rho →
          Kakeya.realRpowENN (delta / rho)
                routing.critical.structuralLoss *
              (55296 * Kakeya.deltaTubeVolume 1) ≤
            ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
              ((2 : ENNReal)⁻¹ *
                Kakeya.realRpowENN delta
                  ((packetDensityExponent : ℝ) *
                    routing.numerics.hierarchy.stableLoss))
  fiber_trace_density :
    ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
      ∀ {rho : ℝ}, 0 < rho →
        Real.rpow delta (1 - outputLoss) ≤ rho →
          Kakeya.realRpowENN (delta / rho)
                routing.critical.structuralLoss *
              (55296 * Kakeya.deltaTubeVolume 1) ≤
            ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
              (100 : ENNReal)⁻¹ *
              (Kakeya.realRpowENN delta
                  routing.numerics.hierarchy.sourceLoss / 2) *
              ((2 : ENNReal)⁻¹ *
                Kakeya.realRpowENN delta
                  ((packetDensityExponent : ℝ) *
                    routing.numerics.hierarchy.stableLoss))
  coarse_constant :
    ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
      ∀ {rho : ℝ}, 0 < rho →
        rho ≤ Real.rpow delta outputLoss →
          55296 * Kakeya.deltaTubeVolume 1 ≤
            Kakeya.realRpowENN rho
              (-(routing.numerics.hierarchy.capLoss -
                routing.numerics.hierarchy.criticalFloorLoss))
  fiber_constant :
    ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
      ∀ {rho : ℝ}, 0 < rho →
        Real.rpow delta (1 - outputLoss) ≤ rho →
          55296 * Kakeya.deltaTubeVolume 1 ≤
            Kakeya.realRpowENN (delta / rho)
              (-(routing.numerics.hierarchy.capLoss -
                routing.numerics.hierarchy.criticalFloorLoss))
  product_absorption :
    ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
      ∀ {rho : ℝ}, 0 < rho →
        Real.rpow delta (1 - outputLoss) ≤ rho →
        rho ≤ Real.rpow delta outputLoss →
        ∀ {regularity : ℕ},
          (regularity : ENNReal) ≤
              logarithmicLoss delta ^ polylogExponent →
          let desiredProduct :=
            (4 * (55296 * Kakeya.deltaTubeVolume 1)) *
              logarithmicLoss delta ^ polylogExponent *
              Kakeya.realRpowENN delta
                (2 - routing.numerics.hierarchy.sourceLoss -
                  routing.numerics.hierarchy.capLoss +
                  outputLoss *
                    (routing.numerics.hierarchy.componentLoss +
                      routing.numerics.hierarchy.capLoss))
          desiredProduct ≤
            wz1PaperRefinementFraction delta 61 *
              Kakeya.realRpowENN delta
                routing.numerics.hierarchy.sourceLoss *
              Kakeya.realRpowENN delta 2
  final_coarse_multiplicity :
    ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
      ∀ {rho : ℝ}, 0 < rho →
        Real.rpow delta (1 - outputLoss) ≤ rho →
        rho ≤ Real.rpow delta outputLoss →
        ∀ {regularity : ℕ},
          (regularity : ENNReal) ≤
              logarithmicLoss delta ^ polylogExponent →
          (regularity : ENNReal) *
              Kakeya.realRpowENN rho
                (2 - sigma - routing.numerics.hierarchy.capLoss) ≤
            Kakeya.realRpowENN rho
              (2 - sigma -
                routing.numerics.hierarchy.finalStrongLoss)
  final_fiber_multiplicity :
    ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
      ∀ {rho : ℝ}, 0 < rho →
        Real.rpow delta (1 - outputLoss) ≤ rho →
          Kakeya.realRpowENN (delta / rho)
              (2 - sigma - routing.numerics.hierarchy.capLoss) ≤
            Kakeya.realRpowENN (delta / rho)
              (2 - sigma -
                routing.numerics.hierarchy.finalStrongLoss)
  final_cwa_parent :
    ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
      ∀ {rho : ℝ}, 0 < rho →
        rho ≤ Real.rpow delta outputLoss →
          (wz2PaperNearbyTopLevelDimensionConstant : ENNReal) *
              Kakeya.realRpowENN rho
                (-3 *
                  (routing.numerics.hierarchy.finalStrongLoss / 4)) ≤
            Kakeya.realRpowENN rho
              (-routing.numerics.hierarchy.finalStrongLoss)
  final_cwa_parent_nearby :
    ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
      ∀ {rho : ℝ}, 0 < rho →
        rho ≤ Real.rpow delta outputLoss →
          Kakeya.realRpowENN delta
              (-(cwaLossExponent : ℝ) *
                routing.numerics.hierarchy.stableLoss) ≤
            Kakeya.realRpowENN rho
              (-(routing.numerics.hierarchy.finalStrongLoss / 4))
  final_cwa_fiber :
    ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
      ∀ {rho : ℝ}, 0 < rho →
        Real.rpow delta (1 - outputLoss) ≤ rho →
          Kakeya.realRpowENN delta
              (-(cwaLossExponent : ℝ) *
                routing.numerics.hierarchy.stableLoss) ≤
            Kakeya.realRpowENN (delta / rho)
              (-routing.numerics.hierarchy.finalStrongLoss)
  final_coarse_carrier :
    ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
      ∀ {rho : ℝ}, 0 < rho →
        rho ≤ Real.rpow delta outputLoss →
          55296 * Kakeya.deltaTubeVolume 1 ≤
            Kakeya.realRpowENN rho
              (-routing.numerics.hierarchy.finalStrongLoss)
  final_fiber_carrier :
    ∀ {delta : ℝ}, 0 < delta → delta ≤ delta₀ →
      ∀ {rho : ℝ}, 0 < rho →
        Real.rpow delta (1 - outputLoss) ≤ rho →
          55296 * Kakeya.deltaTubeVolume 1 ≤
            Kakeya.realRpowENN (delta / rho)
              (-routing.numerics.hierarchy.finalStrongLoss)

/--
Choose one common source-scale threshold for every purely scalar inequality
used by the V4 metric, four-degree, and final assembly stages.
-/
theorem prop62V4_pure_scalar_inputs
    (polylogExponent cwaPower packetDensityExponent
      cwaLossExponent : ℕ)
    (sigma outputLoss : ℝ)
    (outputLossPos : 0 < outputLoss)
    (routing :
      Prop62V4PureCriticalFloorRoutingData
        polylogExponent cwaPower packetDensityExponent cwaLossExponent
        sigma outputLoss) :
    Nonempty
      (Prop62V4PureScalarInputs
        polylogExponent cwaPower packetDensityExponent cwaLossExponent
        sigma outputLoss routing) := by
  let numerics := routing.numerics
  let hierarchy := numerics.hierarchy
  let critical := routing.critical
  rcases
      WZ2PaperFinalLossHierarchyData.nearbyFixedGridDensityThreshold
        hierarchy
    with
    ⟨fixedGridDensity⟩
  have criticalCapGap :
      hierarchy.criticalFloorLoss < hierarchy.capLoss :=
    hierarchy.critical_internal.trans hierarchy.internal_cap
  rcases
      wz2_paper_final_fiber_geometric_absorption
        hierarchy.criticalFloorLoss hierarchy.capLoss
        criticalCapGap
    with ⟨criticalGeometry⟩
  let targetThreshold : ℝ :=
    min (1 / 100 : ℝ)
      (min critical.delta₀
        (min criticalGeometry.delta₀ numerics.fiber.delta₀))
  have targetThresholdPos : 0 < targetThreshold := by
    dsimp only [targetThreshold]
    exact lt_min (by norm_num) <|
      lt_min critical.delta₀_pos <|
        lt_min criticalGeometry.delta₀_pos numerics.fiber.delta₀_pos
  rcases
      pure_wz2_exists_delta₀_rpow_le
        targetThresholdPos outputLossPos
    with ⟨scaleDelta, scaleDeltaPos, scaleDeltaOne, scaleSmall⟩
  let geometry : ENNReal :=
    55296 * Kakeya.deltaTubeVolume 1
  have geometryTop : geometry ≠ ⊤ := by
    dsimp only [geometry]
    exact ENNReal.mul_ne_top
      (ENNReal.natCast_ne_top 55296)
      deltaTubeVolume_one_ne_top
  let coarseDensityConstant : ENNReal := 576 * geometry
  have coarseDensityConstantTop : coarseDensityConstant ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by norm_num) geometryTop
  let criticalGap : ℝ :=
    outputLoss * critical.structuralLoss -
      (packetDensityExponent : ℝ) * hierarchy.stableLoss
  have criticalGapPos : 0 < criticalGap := by
    dsimp only [criticalGap]
    linarith [numerics.packet_critical_gap]
  rcases
      exists_delta_realRpowENN_bound
        coarseDensityConstant coarseDensityConstantTop
        criticalGapPos
    with
    ⟨coarseDensityDelta, coarseDensityDeltaPos,
      coarseDensityDeltaOne, coarseDensityBound⟩
  let jacobian : ENNReal :=
    ENNReal.ofReal ((1 / 100 : ℝ) ^ 3)
  have jacobianZero : jacobian ≠ 0 := by
    dsimp only [jacobian]
    exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have jacobianTop : jacobian ≠ ⊤ := ENNReal.ofReal_ne_top
  let fiberDensityConstant : ENNReal :=
    2 * geometry * jacobian⁻¹
  have fiberDensityConstantTop : fiberDensityConstant ≠ ⊤ := by
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by norm_num) geometryTop)
      (ENNReal.inv_ne_top.mpr jacobianZero)
  rcases
      exists_delta_realRpowENN_bound
        fiberDensityConstant fiberDensityConstantTop
        criticalGapPos
    with
    ⟨fiberDensityBaseDelta, fiberDensityBaseDeltaPos,
      fiberDensityBaseDeltaOne, fiberDensityBound⟩
  let exponentSum : ℝ :=
    prop62V4CriticalExponentSum
      cwaPower packetDensityExponent cwaLossExponent
  have exponentSumPos : 0 < exponentSum := by
    dsimp only [exponentSum, prop62V4CriticalExponentSum]
    positivity
  have structuralExponentBound :
      critical.structuralLoss *
          (1000 * exponentSum) ≤ outputLoss := by
    have structuralLossLe :
        critical.structuralLoss ≤
          outputLoss / (1000 * exponentSum) := by
      exact critical.structuralLoss_le.trans <| by
        unfold prop62V4CriticalStructuralBudget
        exact min_le_right _ _
    rwa [le_div_iff₀ (mul_pos (by norm_num) exponentSumPos)]
      at structuralLossLe
  have traceCoefficientLt :
      1 + 2 * (packetDensityExponent : ℝ) <
        1000 * exponentSum := by
    dsimp only [exponentSum, prop62V4CriticalExponentSum]
    have cwaNonneg : (0 : ℝ) ≤ cwaPower := by positivity
    have packetNonneg :
        (0 : ℝ) ≤ packetDensityExponent := by positivity
    have cwaLossNonneg :
        (0 : ℝ) ≤ cwaLossExponent := by positivity
    linarith
  have traceWeightedBound :
      critical.structuralLoss *
          (1 + 2 * (packetDensityExponent : ℝ)) <
        outputLoss := by
    exact
      (mul_lt_mul_of_pos_left
        traceCoefficientLt critical.structuralLoss_pos).trans_le
          structuralExponentBound
  let fiberTraceGap : ℝ :=
    outputLoss * critical.structuralLoss -
      hierarchy.sourceLoss -
      (packetDensityExponent : ℝ) * hierarchy.stableLoss
  have fiberTraceGapPos : 0 < fiberTraceGap := by
    dsimp only [fiberTraceGap]
    rw [hierarchy.sourceLoss_eq, hierarchy.stableLoss_eq]
    dsimp only [wz2PaperFinalSourceLoss, wz2PaperFinalStableLoss]
    nlinarith [critical.structuralLoss_pos, traceWeightedBound]
  let fiberTraceDensityConstant : ENNReal :=
    2 * 2 * 100 * geometry * jacobian⁻¹
  have fiberTraceDensityConstantTop :
      fiberTraceDensityConstant ≠ ⊤ := by
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.mul_ne_top
          (ENNReal.mul_ne_top (by norm_num) (by norm_num))
          (by norm_num))
        geometryTop)
      (ENNReal.inv_ne_top.mpr jacobianZero)
  rcases
      exists_delta_realRpowENN_bound
        fiberTraceDensityConstant fiberTraceDensityConstantTop
        fiberTraceGapPos
    with
    ⟨fiberTraceDensityDelta, fiberTraceDensityDeltaPos,
      fiberTraceDensityDeltaOne, fiberTraceDensityBound⟩
  let fiberDensityDelta : ℝ :=
    min fiberDensityBaseDelta fiberTraceDensityDelta
  have fiberDensityDeltaPos : 0 < fiberDensityDelta := by
    exact lt_min fiberDensityBaseDeltaPos fiberTraceDensityDeltaPos
  have fiberDensityDeltaOne : fiberDensityDelta ≤ 1 :=
    (min_le_left _ _).trans fiberDensityBaseDeltaOne
  let dimensionConstant : ENNReal :=
    wz2PaperNearbyTopLevelDimensionConstant
  have dimensionConstantTop : dimensionConstant ≠ ⊤ := by
    exact ENNReal.natCast_ne_top _
  let finalCWAGap : ℝ :=
    outputLoss * (hierarchy.finalStrongLoss / 4)
  have finalCWAGapPos : 0 < finalCWAGap := by
    dsimp only [finalCWAGap]
    exact
      mul_pos outputLossPos
        (div_pos hierarchy.finalStrongLoss_pos (by norm_num))
  rcases
      exists_delta_realRpowENN_bound
        dimensionConstant dimensionConstantTop finalCWAGapPos
    with
    ⟨finalCWADelta, finalCWADeltaPos,
      finalCWADeltaOne, finalCWABound⟩
  let productGap : ℝ := critical.structuralLoss
  have productGapPos : 0 < productGap := by
    dsimp only [productGap]
    exact critical.structuralLoss_pos
  let productConstant : ENNReal := 4 * geometry
  have productConstantTop : productConstant ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by norm_num) geometryTop
  rcases
      exists_delta_C_pow_log_absorbed_ennreal
        productConstant productConstantTop
        2 (by norm_num) productGapPos
        (show 0 < polylogExponent + 61 by omega)
    with
    ⟨productDelta, productDeltaPos, productDeltaOne, productBound⟩
  have componentFinal :
      hierarchy.componentLoss < hierarchy.finalStrongLoss := by
    have densityGap :
        0 <
          hierarchy.fiberDensityLoss -
            hierarchy.componentLoss - hierarchy.capLoss := by
      nlinarith [hierarchy.density_gap_pos,
        hierarchy.sourceLoss_pos, critical.structuralLoss_pos]
    have componentDensity :
        hierarchy.componentLoss < hierarchy.fiberDensityLoss := by
      linarith [densityGap, hierarchy.capLoss_pos]
    exact componentDensity.trans hierarchy.density_final
  have capFinal :
      hierarchy.capLoss < hierarchy.finalStrongLoss :=
    hierarchy.cap_component.trans componentFinal
  let coarseMultiplicityGap : ℝ :=
    outputLoss *
      (hierarchy.finalStrongLoss - hierarchy.capLoss)
  have coarseMultiplicityGapPos : 0 < coarseMultiplicityGap := by
    dsimp only [coarseMultiplicityGap]
    positivity
  rcases
      exists_delta_C_pow_log_absorbed_ennreal
        (1 : ENNReal) (by norm_num)
        2 (by norm_num) coarseMultiplicityGapPos
        (show 0 < polylogExponent + 1 by omega)
    with
    ⟨coarseMultiplicityDelta, coarseMultiplicityDeltaPos,
      coarseMultiplicityDeltaOne, coarseMultiplicityBound⟩
  let delta₀ :=
    min fixedGridDensity.delta₀
      (min scaleDelta
        (min coarseDensityDelta
          (min fiberDensityDelta
            (min finalCWADelta
              (min productDelta
                (min coarseMultiplicityDelta
                  (min numerics.component.delta₀ (Real.exp (-1)))))))))
  have delta₀Pos : 0 < delta₀ := by
    dsimp only [delta₀]
    exact lt_min fixedGridDensity.delta₀_pos <|
      lt_min scaleDeltaPos <|
        lt_min coarseDensityDeltaPos <|
          lt_min fiberDensityDeltaPos <|
            lt_min finalCWADeltaPos <|
              lt_min productDeltaPos <|
                lt_min coarseMultiplicityDeltaPos <|
                  lt_min numerics.component.delta₀_pos
                    (Real.exp_pos _)
  have delta₀LeHundred : delta₀ ≤ 1 / 100 :=
    (min_le_left _ _).trans
      fixedGridDensity.delta₀_le_one_hundred
  refine
    ⟨{
      metric_loss := numerics.metric_loss
      packet_loss := numerics.packet_loss
      source_to_working := hierarchy.source_stable.le
      structural_to_final := numerics.structural_final.le
      delta₀ := delta₀
      delta₀_pos := delta₀Pos
      delta₀_le_one_hundred := delta₀LeHundred
      fixed_grid_density := ?_
      rho_small := ?_
      rho_power_small := ?_
      ratio_small := ?_
      rho_critical := ?_
      ratio_critical := ?_
      parent_cwa := ?_
      fiber_cwa := ?_
      coarse_density := ?_
      fiber_density := ?_
      fiber_trace_density := ?_
      coarse_constant := ?_
      fiber_constant := ?_
      product_absorption := ?_
      final_coarse_multiplicity := ?_
      final_fiber_multiplicity := ?_
      final_cwa_parent := ?_
      final_cwa_parent_nearby := ?_
      final_cwa_fiber := ?_
      final_coarse_carrier := ?_
      final_fiber_carrier := ?_
    }⟩
  · intro delta deltaPos deltaLe
    exact fixedGridDensity.fixed_grid_density deltaPos <|
      deltaLe.trans (min_le_left _ _)
  · intro delta deltaPos deltaLe rho rhoUpper
    have scaleLe : delta ≤ scaleDelta :=
      deltaLe.trans <| (min_le_right _ _).trans (min_le_left _ _)
    exact rhoUpper.trans <|
      (scaleSmall delta deltaPos scaleLe).trans <|
        (min_le_left _ _).trans (by norm_num)
  · intro delta deltaPos deltaLe rho rhoUpper
    have scaleLe : delta ≤ scaleDelta :=
      deltaLe.trans <| (min_le_right _ _).trans (min_le_left _ _)
    exact rhoUpper.trans <|
      (scaleSmall delta deltaPos scaleLe).trans <|
        min_le_left _ _
  · intro delta deltaPos deltaLe rho rhoPos rhoLower
    have scaleLe : delta ≤ scaleDelta :=
      deltaLe.trans <| (min_le_right _ _).trans (min_le_left _ _)
    have ratioUpper :
        delta / rho ≤ Real.rpow delta outputLoss :=
      pureScalar_ratio_le_output_power deltaPos rhoPos rhoLower
    exact ratioUpper.trans <|
      (scaleSmall delta deltaPos scaleLe).trans <|
        (min_le_left _ _).trans (by norm_num)
  · intro delta deltaPos deltaLe rho rhoUpper
    have scaleLe : delta ≤ scaleDelta :=
      deltaLe.trans <| (min_le_right _ _).trans (min_le_left _ _)
    exact rhoUpper.trans <|
      (scaleSmall delta deltaPos scaleLe).trans <|
        (min_le_right _ _).trans (min_le_left _ _)
  · intro delta deltaPos deltaLe rho rhoPos rhoLower
    have scaleLe : delta ≤ scaleDelta :=
      deltaLe.trans <| (min_le_right _ _).trans (min_le_left _ _)
    have ratioUpper :
        delta / rho ≤ Real.rpow delta outputLoss :=
      pureScalar_ratio_le_output_power deltaPos rhoPos rhoLower
    exact ratioUpper.trans <|
      (scaleSmall delta deltaPos scaleLe).trans <|
        (min_le_right _ _).trans (min_le_left _ _)
  · intro delta deltaPos deltaLe rho rhoPos rhoUpper
    have deltaLeOne : delta ≤ 1 :=
      deltaLe.trans <| delta₀LeHundred.trans (by norm_num)
    have exponentLe :
        -(outputLoss * critical.structuralLoss) ≤
          -(cwaLossExponent : ℝ) * hierarchy.stableLoss := by
      linarith [numerics.cwa_critical_gap]
    exact
      (pure_wz2_rpowENN_antitone
        deltaPos deltaLeOne exponentLe).trans <|
        pure_wz2_target_negative_power_lower
          deltaPos rhoPos rhoUpper critical.structuralLoss_pos.le
  · intro delta deltaPos deltaLe rho rhoPos rhoLower
    have deltaLeOne : delta ≤ 1 :=
      deltaLe.trans <| delta₀LeHundred.trans (by norm_num)
    have ratioUpper :
        delta / rho ≤ Real.rpow delta outputLoss :=
      pureScalar_ratio_le_output_power deltaPos rhoPos rhoLower
    have exponentLe :
        -(outputLoss * critical.structuralLoss) ≤
          -(cwaLossExponent : ℝ) * hierarchy.stableLoss := by
      linarith [numerics.cwa_critical_gap]
    exact
      (pure_wz2_rpowENN_antitone
        deltaPos deltaLeOne exponentLe).trans <|
        pure_wz2_target_negative_power_lower
          deltaPos (div_pos deltaPos rhoPos) ratioUpper
          critical.structuralLoss_pos.le
  · intro delta deltaPos deltaLe rho rhoPos rhoUpper
    have scaleLe : delta ≤ coarseDensityDelta :=
      deltaLe.trans <| (min_le_right _ _).trans <|
        (min_le_right _ _).trans (min_le_left _ _)
    have targetPower :=
      pure_wz2_target_power_upper
        deltaPos rhoPos.le rhoUpper critical.structuralLoss_pos.le
    calc
      (576 * (55296 * Kakeya.deltaTubeVolume 1) : ENNReal) *
            Kakeya.realRpowENN rho critical.structuralLoss ≤
          Kakeya.realRpowENN delta (-criticalGap) *
            Kakeya.realRpowENN delta
              (outputLoss * critical.structuralLoss) := by
        exact mul_le_mul
          (coarseDensityBound delta deltaPos scaleLe)
          targetPower bot_le bot_le
      _ =
          Kakeya.realRpowENN delta
            ((packetDensityExponent : ℝ) * hierarchy.stableLoss) := by
        rw [← realRpowENN_add deltaPos]
        congr 1
        dsimp only [criticalGap]
        ring
  · intro delta deltaPos deltaLe rho rhoPos rhoLower
    have scaleLe : delta ≤ fiberDensityDelta :=
      deltaLe.trans <| (min_le_right _ _).trans <|
        (min_le_right _ _).trans <|
          (min_le_right _ _).trans (min_le_left _ _)
    have ratioUpper :
        delta / rho ≤ Real.rpow delta outputLoss :=
      pureScalar_ratio_le_output_power deltaPos rhoPos rhoLower
    have targetPower :=
      pure_wz2_target_power_upper
        deltaPos (div_pos deltaPos rhoPos).le ratioUpper
        critical.structuralLoss_pos.le
    have raw :
        fiberDensityConstant *
            Kakeya.realRpowENN (delta / rho)
              critical.structuralLoss ≤
          Kakeya.realRpowENN delta
            ((packetDensityExponent : ℝ) * hierarchy.stableLoss) := by
      calc
        fiberDensityConstant *
              Kakeya.realRpowENN (delta / rho)
                critical.structuralLoss ≤
            Kakeya.realRpowENN delta (-criticalGap) *
              Kakeya.realRpowENN delta
                (outputLoss * critical.structuralLoss) := by
          exact mul_le_mul
            (fiberDensityBound delta deltaPos <|
              scaleLe.trans (min_le_left _ _))
            targetPower bot_le bot_le
        _ =
            Kakeya.realRpowENN delta
              ((packetDensityExponent : ℝ) * hierarchy.stableLoss) := by
          rw [← realRpowENN_add deltaPos]
          congr 1
          dsimp only [criticalGap]
          ring
    have scaled :=
      mul_le_mul_left' raw (jacobian * (2 : ENNReal)⁻¹)
    have twoZero : (2 : ENNReal) ≠ 0 := by norm_num
    have twoTop : (2 : ENNReal) ≠ ⊤ := by norm_num
    have leftIdentity :
        (jacobian * (2 : ENNReal)⁻¹) *
              (fiberDensityConstant *
                Kakeya.realRpowENN (delta / rho)
                  critical.structuralLoss) =
          Kakeya.realRpowENN (delta / rho)
              critical.structuralLoss * geometry := by
      dsimp only [fiberDensityConstant]
      calc
        _ =
            (jacobian * jacobian⁻¹) *
              ((2 : ENNReal)⁻¹ * 2) *
              (Kakeya.realRpowENN (delta / rho)
                critical.structuralLoss * geometry) := by
          ring
        _ = _ := by
          rw [ENNReal.mul_inv_cancel jacobianZero jacobianTop,
            ENNReal.inv_mul_cancel twoZero twoTop]
          simp
    have rightIdentity :
        (jacobian * (2 : ENNReal)⁻¹) *
              Kakeya.realRpowENN delta
                ((packetDensityExponent : ℝ) * hierarchy.stableLoss) =
          jacobian *
            ((2 : ENNReal)⁻¹ *
              Kakeya.realRpowENN delta
                ((packetDensityExponent : ℝ) * hierarchy.stableLoss)) := by
      ring
    rw [leftIdentity, rightIdentity] at scaled
    change
      Kakeya.realRpowENN (delta / rho)
            critical.structuralLoss * geometry ≤
        jacobian *
          ((2 : ENNReal)⁻¹ *
            Kakeya.realRpowENN delta
              ((packetDensityExponent : ℝ) * hierarchy.stableLoss))
    exact scaled
  · intro delta deltaPos deltaLe rho rhoPos rhoLower
    have scaleLe : delta ≤ fiberDensityDelta :=
      deltaLe.trans <| (min_le_right _ _).trans <|
        (min_le_right _ _).trans <|
          (min_le_right _ _).trans (min_le_left _ _)
    have traceScaleLe : delta ≤ fiberTraceDensityDelta :=
      scaleLe.trans (min_le_right _ _)
    have ratioUpper :
        delta / rho ≤ Real.rpow delta outputLoss :=
      pureScalar_ratio_le_output_power deltaPos rhoPos rhoLower
    have targetPower :=
      pure_wz2_target_power_upper
        deltaPos (div_pos deltaPos rhoPos).le ratioUpper
        critical.structuralLoss_pos.le
    have raw :
        fiberTraceDensityConstant *
            Kakeya.realRpowENN (delta / rho)
              critical.structuralLoss ≤
          Kakeya.realRpowENN delta
            (hierarchy.sourceLoss +
              (packetDensityExponent : ℝ) * hierarchy.stableLoss) := by
      calc
        fiberTraceDensityConstant *
              Kakeya.realRpowENN (delta / rho)
                critical.structuralLoss ≤
            Kakeya.realRpowENN delta (-fiberTraceGap) *
              Kakeya.realRpowENN delta
                (outputLoss * critical.structuralLoss) := by
          exact mul_le_mul
            (fiberTraceDensityBound delta deltaPos traceScaleLe)
            targetPower bot_le bot_le
        _ =
            Kakeya.realRpowENN delta
              (hierarchy.sourceLoss +
                (packetDensityExponent : ℝ) *
                  hierarchy.stableLoss) := by
          rw [← realRpowENN_add deltaPos]
          congr 1
          dsimp only [fiberTraceGap]
          ring
    let traceWeight : ENNReal :=
      jacobian * (100 : ENNReal)⁻¹ *
        (2 : ENNReal)⁻¹ * (2 : ENNReal)⁻¹
    have scaled := mul_le_mul_left' raw traceWeight
    have twoZero : (2 : ENNReal) ≠ 0 := by norm_num
    have twoTop : (2 : ENNReal) ≠ ⊤ := by norm_num
    have hundredZero : (100 : ENNReal) ≠ 0 := by norm_num
    have hundredTop : (100 : ENNReal) ≠ ⊤ := by norm_num
    have leftIdentity :
        traceWeight *
              (fiberTraceDensityConstant *
                Kakeya.realRpowENN (delta / rho)
                  critical.structuralLoss) =
          Kakeya.realRpowENN (delta / rho)
              critical.structuralLoss * geometry := by
      dsimp only [traceWeight, fiberTraceDensityConstant]
      calc
        _ =
            (jacobian * jacobian⁻¹) *
              ((100 : ENNReal)⁻¹ * 100) *
              ((2 : ENNReal)⁻¹ * 2) *
              ((2 : ENNReal)⁻¹ * 2) *
              (Kakeya.realRpowENN (delta / rho)
                critical.structuralLoss * geometry) := by
          ring
        _ = _ := by
          rw [ENNReal.mul_inv_cancel jacobianZero jacobianTop,
            ENNReal.inv_mul_cancel hundredZero hundredTop,
            ENNReal.inv_mul_cancel twoZero twoTop]
          simp
    have rightIdentity :
        traceWeight *
              Kakeya.realRpowENN delta
                (hierarchy.sourceLoss +
                  (packetDensityExponent : ℝ) *
                    hierarchy.stableLoss) =
          jacobian * (100 : ENNReal)⁻¹ *
              (Kakeya.realRpowENN delta hierarchy.sourceLoss / 2) *
              ((2 : ENNReal)⁻¹ *
                Kakeya.realRpowENN delta
                  ((packetDensityExponent : ℝ) *
                    hierarchy.stableLoss)) := by
      rw [realRpowENN_add deltaPos]
      dsimp only [traceWeight]
      simp only [div_eq_mul_inv]
      ring
    rw [leftIdentity, rightIdentity] at scaled
    exact scaled
  · intro delta deltaPos deltaLe rho rhoPos rhoUpper
    have scaleLe : delta ≤ scaleDelta :=
      deltaLe.trans <| (min_le_right _ _).trans (min_le_left _ _)
    have rhoLe :
        rho ≤ criticalGeometry.delta₀ :=
      rhoUpper.trans <|
        (scaleSmall delta deltaPos scaleLe).trans <|
          (min_le_right _ _).trans <|
            (min_le_right _ _).trans (min_le_left _ _)
    exact criticalGeometry.absorb rho rhoPos rhoLe
  · intro delta deltaPos deltaLe rho rhoPos rhoLower
    have scaleLe : delta ≤ scaleDelta :=
      deltaLe.trans <| (min_le_right _ _).trans (min_le_left _ _)
    have ratioUpper :
        delta / rho ≤ Real.rpow delta outputLoss :=
      pureScalar_ratio_le_output_power deltaPos rhoPos rhoLower
    have ratioLe :
        delta / rho ≤ criticalGeometry.delta₀ :=
      ratioUpper.trans <|
        (scaleSmall delta deltaPos scaleLe).trans <|
          (min_le_right _ _).trans <|
            (min_le_right _ _).trans (min_le_left _ _)
    exact
      criticalGeometry.absorb
        (delta / rho) (div_pos deltaPos rhoPos) ratioLe
  · intro delta deltaPos deltaLe rho rhoPos rhoLower rhoUpper regularity
      _regularityLe
    dsimp
    have productLe : delta ≤ productDelta :=
      deltaLe.trans <| (min_le_right _ _).trans <|
        (min_le_right _ _).trans <|
          (min_le_right _ _).trans <|
            (min_le_right _ _).trans <|
              (min_le_right _ _).trans (min_le_left _ _)
    have componentLe : delta ≤ numerics.component.delta₀ :=
      deltaLe.trans <| (min_le_right _ _).trans <|
        (min_le_right _ _).trans <|
          (min_le_right _ _).trans <|
            (min_le_right _ _).trans <|
              (min_le_right _ _).trans <|
                (min_le_right _ _).trans <|
                  (min_le_right _ _).trans (min_le_left _ _)
    have expLe : delta ≤ Real.exp (-1) :=
      deltaLe.trans <| (min_le_right _ _).trans <|
        (min_le_right _ _).trans <|
          (min_le_right _ _).trans <|
            (min_le_right _ _).trans <|
              (min_le_right _ _).trans <|
                (min_le_right _ _).trans <|
                  (min_le_right _ _).trans (min_le_right _ _)
    let level : ENNReal := logarithmicLoss delta
    let logTerm : ENNReal := ENNReal.ofReal (Real.log (1 / delta))
    let envelope : ENNReal :=
      2 * ENNReal.ofReal (1 + Real.log delta⁻¹)
    have envelopeEq :
        envelope =
          ENNReal.ofReal (2 * (1 + Real.log delta⁻¹)) := by
      dsimp only [envelope]
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    have deltaLeOne : delta ≤ 1 := by
      exact expLe.trans <| by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (by norm_num)
    have levelLe : level ≤ envelope := by
      have bound :=
        pureScalar_directionLevelCount_le_logEnvelope deltaPos deltaLeOne
      dsimp only [level, envelope, logarithmicLoss]
      exact bound
    have logPos : 0 < Real.log (1 / delta) := by
      apply Real.log_pos
      apply one_lt_one_div deltaPos
      exact expLe.trans_lt <|
        (Real.exp_lt_one_iff.mpr (by norm_num))
    have logOne : (1 : ENNReal) ≤ logTerm := by
      rw [← ENNReal.ofReal_one]
      apply ENNReal.ofReal_mono
      have deltaExp : delta * Real.exp 1 ≤ 1 := by
        calc
          delta * Real.exp 1 ≤ Real.exp (-1) * Real.exp 1 := by
            gcongr
          _ = 1 := by
            rw [← Real.exp_add]
            norm_num
      have expLeInv : Real.exp 1 ≤ 1 / delta := by
        rw [le_div_iff₀ deltaPos]
        simpa [mul_comm] using deltaExp
      simpa using Real.log_le_log (Real.exp_pos 1) expLeInv
    have logLeEnvelope : logTerm ≤ envelope := by
      calc
        logTerm ≤
            ENNReal.ofReal (1 + Real.log delta⁻¹) := by
          dsimp only [logTerm]
          apply ENNReal.ofReal_mono
          rw [show 1 / delta = delta⁻¹ by simp]
          linarith
        _ ≤ envelope := by
          dsimp only [envelope]
          simpa using
            mul_le_mul_right'
              (by norm_num : (1 : ENNReal) ≤ 2)
              (ENNReal.ofReal (1 + Real.log delta⁻¹))
    have envelopeOne : (1 : ENNReal) ≤ envelope :=
      logOne.trans logLeEnvelope
    have levelPower :
        level ^ polylogExponent ≤
          envelope ^ (polylogExponent + 61) := by
      calc
        level ^ polylogExponent ≤ envelope ^ polylogExponent := by
          gcongr
        _ ≤ envelope ^ (polylogExponent + 61) :=
          pow_le_pow_right' envelopeOne (by omega)
    have logarithmicAbsorption :
        productConstant * level ^ polylogExponent ≤
          Kakeya.realRpowENN delta (-productGap) := by
      calc
        productConstant * level ^ polylogExponent ≤
            productConstant *
              envelope ^ (polylogExponent + 61) := by
          exact mul_le_mul_left' levelPower productConstant
        _ =
            productConstant *
              ENNReal.ofReal (2 * (1 + Real.log delta⁻¹)) ^
                (polylogExponent + 61) := by
          rw [envelopeEq]
        _ ≤ Kakeya.realRpowENN delta (-productGap) :=
          productBound delta deltaPos productLe
    have componentAbsorption :=
      numerics.component.absorb delta deltaPos componentLe
    have desiredLeComponent :
        (4 * geometry) * level ^ polylogExponent *
              Kakeya.realRpowENN delta
                (2 - hierarchy.sourceLoss - hierarchy.capLoss +
                  outputLoss *
                    (hierarchy.componentLoss + hierarchy.capLoss)) ≤
          (2 *
              (Kakeya.realRpowENN delta
                  (-critical.structuralLoss) *
                (wz2PaperPreparedOneParentFiniteLoss
                    hierarchy.sourceLoss * geometry))) *
            Kakeya.realRpowENN delta
              (2 - hierarchy.sourceLoss - hierarchy.capLoss +
                outputLoss *
                  (hierarchy.componentLoss + hierarchy.capLoss)) := by
      have finiteLossOne :
          (1 : ENNReal) ≤
            wz2PaperPreparedOneParentFiniteLoss hierarchy.sourceLoss := by
        dsimp only [wz2PaperPreparedOneParentFiniteLoss]
        exact one_le_mul
          (by simp [packingConstant10000])
          (one_le_pow₀ (by norm_num))
      have geometryOne : (1 : ENNReal) ≤ geometry := by
        dsimp only [geometry]
        calc
          (1 : ENNReal) ≤ 55296 := by norm_num
          _ ≤ 55296 * Kakeya.deltaTubeVolume 1 := by
            simpa using
              mul_le_mul_left'
                one_le_deltaTubeVolume_one (55296 : ENNReal)
      have expandedStructural :
          Kakeya.realRpowENN delta (-critical.structuralLoss) ≤
            2 * (Kakeya.realRpowENN delta
                (-critical.structuralLoss) *
              (wz2PaperPreparedOneParentFiniteLoss
                hierarchy.sourceLoss * geometry)) := by
        have combinedOne :
            (1 : ENNReal) ≤
              2 *
                (wz2PaperPreparedOneParentFiniteLoss
                  hierarchy.sourceLoss * geometry) :=
          one_le_mul (by norm_num) (one_le_mul finiteLossOne geometryOne)
        calc
          Kakeya.realRpowENN delta (-critical.structuralLoss) =
              Kakeya.realRpowENN delta
                (-critical.structuralLoss) * 1 := by simp
          _ ≤
              Kakeya.realRpowENN delta
                (-critical.structuralLoss) *
                (2 * (wz2PaperPreparedOneParentFiniteLoss
                  hierarchy.sourceLoss * geometry)) := by
            exact mul_le_mul_left' combinedOne _
          _ = _ := by ring
      calc
        (4 * geometry) * level ^ polylogExponent *
              Kakeya.realRpowENN delta
                (2 - hierarchy.sourceLoss - hierarchy.capLoss +
                  outputLoss *
                    (hierarchy.componentLoss + hierarchy.capLoss)) ≤
            Kakeya.realRpowENN delta
                (-critical.structuralLoss) *
              Kakeya.realRpowENN delta
                (2 - hierarchy.sourceLoss - hierarchy.capLoss +
                  outputLoss *
                    (hierarchy.componentLoss + hierarchy.capLoss)) := by
          exact mul_le_mul_right'
            (by
              dsimp only [productConstant, productGap]
                at logarithmicAbsorption
              exact logarithmicAbsorption)
            _
        _ ≤
            (2 *
                (Kakeya.realRpowENN delta
                    (-critical.structuralLoss) *
                  (wz2PaperPreparedOneParentFiniteLoss
                    hierarchy.sourceLoss * geometry))) *
              Kakeya.realRpowENN delta
                (2 - hierarchy.sourceLoss - hierarchy.capLoss +
                  outputLoss *
                    (hierarchy.componentLoss + hierarchy.capLoss)) := by
          exact mul_le_mul_right' expandedStructural _
    have componentRightLe :
        (1 / 2 : ENNReal) *
              wz1PaperRefinementFraction delta
                (61 + polylogExponent) *
              Kakeya.realRpowENN delta
                (2 + 2 * hierarchy.sourceLoss) ≤
          wz1PaperRefinementFraction delta 61 *
            Kakeya.realRpowENN delta hierarchy.sourceLoss *
            Kakeya.realRpowENN delta 2 := by
      have fractionSplit :
          wz1PaperRefinementFraction delta
              (61 + polylogExponent) =
            wz1PaperRefinementFraction delta 61 *
              wz1PaperRefinementFraction delta polylogExponent := by
        simp [wz1PaperRefinementFraction, pow_add]
      have fractionLeOne :
          wz1PaperRefinementFraction delta polylogExponent ≤ 1 := by
        unfold wz1PaperRefinementFraction
        apply pow_le_one₀
        · positivity
        · exact ENNReal.inv_le_one.mpr logOne
      have sourcePowerLeOne :
          Kakeya.realRpowENN delta hierarchy.sourceLoss ≤ 1 := by
        simpa [Kakeya.realRpowENN] using
          pure_wz2_rpowENN_antitone
            deltaPos deltaLeOne hierarchy.sourceLoss_pos.le
      have exponentIdentity :
          (2 + 2 * hierarchy.sourceLoss : ℝ) =
            2 + hierarchy.sourceLoss + hierarchy.sourceLoss := by
        ring
      have sourcePowerSplit :
          Kakeya.realRpowENN delta (2 + 2 * hierarchy.sourceLoss) =
          Kakeya.realRpowENN delta 2 *
            Kakeya.realRpowENN delta hierarchy.sourceLoss *
            Kakeya.realRpowENN delta hierarchy.sourceLoss := by
        rw [exponentIdentity,
          realRpowENN_add deltaPos, realRpowENN_add deltaPos]
      rw [fractionSplit, sourcePowerSplit]
      calc
        (1 / 2 : ENNReal) *
                (wz1PaperRefinementFraction delta 61 *
                  wz1PaperRefinementFraction delta polylogExponent) *
                (Kakeya.realRpowENN delta 2 *
                  Kakeya.realRpowENN delta hierarchy.sourceLoss *
                  Kakeya.realRpowENN delta hierarchy.sourceLoss) =
            (wz1PaperRefinementFraction delta 61 *
              Kakeya.realRpowENN delta hierarchy.sourceLoss *
              Kakeya.realRpowENN delta 2) *
              ((1 / 2 : ENNReal) *
                wz1PaperRefinementFraction delta polylogExponent *
                Kakeya.realRpowENN delta hierarchy.sourceLoss) := by
          ring
        _ ≤
            (wz1PaperRefinementFraction delta 61 *
              Kakeya.realRpowENN delta hierarchy.sourceLoss *
              Kakeya.realRpowENN delta 2) * 1 := by
          gcongr
          calc
            (1 / 2 : ENNReal) *
                  wz1PaperRefinementFraction delta polylogExponent *
                  Kakeya.realRpowENN delta hierarchy.sourceLoss ≤
                (1 / 2 : ENNReal) * 1 * 1 := by
              gcongr
            _ ≤ 1 := by norm_num
        _ = _ := by simp
    calc
      _ ≤ _ := desiredLeComponent
      _ ≤ _ := componentAbsorption
      _ ≤ _ := componentRightLe
  · intro delta deltaPos deltaLe rho rhoPos rhoLower rhoUpper regularity
      regularityLe
    have scaleLe : delta ≤ coarseMultiplicityDelta :=
      deltaLe.trans <| (min_le_right _ _).trans <|
        (min_le_right _ _).trans <|
          (min_le_right _ _).trans <|
            (min_le_right _ _).trans <|
              (min_le_right _ _).trans <|
                (min_le_right _ _).trans (min_le_left _ _)
    have deltaLeOne : delta ≤ 1 :=
      deltaLe.trans <| delta₀LeHundred.trans (by norm_num)
    let envelope : ENNReal :=
      2 * ENNReal.ofReal (1 + Real.log delta⁻¹)
    have envelopeEq :
        envelope =
          ENNReal.ofReal (2 * (1 + Real.log delta⁻¹)) := by
      dsimp only [envelope]
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    have levelLe : logarithmicLoss delta ≤ envelope := by
      have bound :=
        pureScalar_directionLevelCount_le_logEnvelope deltaPos deltaLeOne
      dsimp only [envelope, logarithmicLoss]
      exact bound
    have logNonnegative : 0 ≤ Real.log delta⁻¹ :=
      Real.log_nonneg ((one_le_inv₀ deltaPos).mpr deltaLeOne)
    have envelopeOne : (1 : ENNReal) ≤ envelope := by
      dsimp only [envelope]
      calc
        (1 : ENNReal) ≤
            ENNReal.ofReal (1 + Real.log delta⁻¹) := by
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_mono (by linarith)
        _ ≤
            2 * ENNReal.ofReal (1 + Real.log delta⁻¹) := by
          simpa using
            mul_le_mul_right'
              (by norm_num : (1 : ENNReal) ≤ 2)
              (ENNReal.ofReal (1 + Real.log delta⁻¹))
    have levelPower :
        logarithmicLoss delta ^ polylogExponent ≤
          envelope ^ (polylogExponent + 1) := by
      calc
        logarithmicLoss delta ^ polylogExponent ≤
            envelope ^ polylogExponent := by
          gcongr
        _ ≤ envelope ^ (polylogExponent + 1) :=
          pow_le_pow_right' envelopeOne (by omega)
    have logarithmicBound :
        logarithmicLoss delta ^ polylogExponent ≤
          Kakeya.realRpowENN delta (-coarseMultiplicityGap) := by
      calc
        logarithmicLoss delta ^ polylogExponent ≤
            envelope ^ (polylogExponent + 1) := levelPower
        _ =
            (1 : ENNReal) *
              envelope ^ (polylogExponent + 1) := by simp
        _ =
            (1 : ENNReal) *
              ENNReal.ofReal (2 * (1 + Real.log delta⁻¹)) ^
                (polylogExponent + 1) := by
          rw [envelopeEq]
        _ ≤ Kakeya.realRpowENN delta (-coarseMultiplicityGap) :=
          coarseMultiplicityBound delta deltaPos scaleLe
    have rhoGap :
        Kakeya.realRpowENN rho
            (hierarchy.finalStrongLoss - hierarchy.capLoss) ≤
          Kakeya.realRpowENN delta coarseMultiplicityGap :=
      pure_wz2_target_power_upper
        deltaPos rhoPos.le rhoUpper <| by
          linarith [hierarchy.cap_component, numerics.structural_final]
    have productLeOne :
        logarithmicLoss delta ^ polylogExponent *
            Kakeya.realRpowENN rho
              (hierarchy.finalStrongLoss - hierarchy.capLoss) ≤ 1 := by
      calc
        logarithmicLoss delta ^ polylogExponent *
              Kakeya.realRpowENN rho
                (hierarchy.finalStrongLoss - hierarchy.capLoss) ≤
            Kakeya.realRpowENN delta (-coarseMultiplicityGap) *
              Kakeya.realRpowENN delta coarseMultiplicityGap := by
          exact mul_le_mul logarithmicBound rhoGap bot_le bot_le
        _ = 1 := by
          rw [← realRpowENN_add deltaPos]
          simp [Kakeya.realRpowENN]
    have exponentSplit :
        Kakeya.realRpowENN rho
            (2 - sigma - hierarchy.capLoss) =
          Kakeya.realRpowENN rho
              (2 - sigma - hierarchy.finalStrongLoss) *
            Kakeya.realRpowENN rho
              (hierarchy.finalStrongLoss - hierarchy.capLoss) := by
      rw [← realRpowENN_add rhoPos]
      congr 1
      ring
    rw [exponentSplit]
    calc
      (regularity : ENNReal) *
            (Kakeya.realRpowENN rho
                (2 - sigma - hierarchy.finalStrongLoss) *
              Kakeya.realRpowENN rho
                (hierarchy.finalStrongLoss - hierarchy.capLoss)) ≤
          logarithmicLoss delta ^ polylogExponent *
            (Kakeya.realRpowENN rho
                (2 - sigma - hierarchy.finalStrongLoss) *
              Kakeya.realRpowENN rho
                (hierarchy.finalStrongLoss - hierarchy.capLoss)) := by
        gcongr
      _ =
          Kakeya.realRpowENN rho
              (2 - sigma - hierarchy.finalStrongLoss) *
            (logarithmicLoss delta ^ polylogExponent *
              Kakeya.realRpowENN rho
                (hierarchy.finalStrongLoss - hierarchy.capLoss)) := by
        ring
      _ ≤
          Kakeya.realRpowENN rho
            (2 - sigma - hierarchy.finalStrongLoss) := by
        simpa using mul_le_mul_left'
          productLeOne
          (Kakeya.realRpowENN rho
            (2 - sigma - hierarchy.finalStrongLoss))
  · intro delta deltaPos deltaLe rho rhoPos rhoLower
    have ratioUpper :
        delta / rho ≤ Real.rpow delta outputLoss :=
      pureScalar_ratio_le_output_power deltaPos rhoPos rhoLower
    have ratioOne : delta / rho ≤ 1 :=
      ratioUpper.trans <|
        Real.rpow_le_one deltaPos.le
          (deltaLe.trans <| delta₀LeHundred.trans (by norm_num))
          outputLossPos.le
    exact
      pure_wz2_rpowENN_antitone
        (div_pos deltaPos rhoPos) ratioOne <| by
          linarith [hierarchy.cap_component, numerics.structural_final]
  · intro delta deltaPos deltaLe rho rhoPos rhoUpper
    have finalCwaLe : delta ≤ finalCWADelta :=
      deltaLe.trans <| (min_le_right _ _).trans <|
        (min_le_right _ _).trans <|
          (min_le_right _ _).trans <|
            (min_le_right _ _).trans (min_le_left _ _)
    have constantBound :
        dimensionConstant ≤
          Kakeya.realRpowENN delta
            (-(outputLoss * (hierarchy.finalStrongLoss / 4))) := by
      simpa only [finalCWAGap] using
        finalCWABound delta deltaPos finalCwaLe
    have targetConstantBound :
        dimensionConstant ≤
          Kakeya.realRpowENN rho
            (-(hierarchy.finalStrongLoss / 4)) :=
      constantBound.trans <|
        pure_wz2_target_negative_power_lower
          deltaPos rhoPos rhoUpper
          (div_nonneg hierarchy.finalStrongLoss_pos.le (by norm_num))
    calc
      dimensionConstant *
            Kakeya.realRpowENN rho
              (-3 * (hierarchy.finalStrongLoss / 4)) ≤
          Kakeya.realRpowENN rho
              (-(hierarchy.finalStrongLoss / 4)) *
            Kakeya.realRpowENN rho
              (-3 * (hierarchy.finalStrongLoss / 4)) := by
        gcongr
      _ =
          Kakeya.realRpowENN rho
            (-hierarchy.finalStrongLoss) := by
        rw [← realRpowENN_add rhoPos]
        congr 1
        ring
  · intro delta deltaPos deltaLe rho rhoPos rhoUpper
    have deltaLeOne : delta ≤ 1 :=
      deltaLe.trans <| delta₀LeHundred.trans (by norm_num)
    have exponentLe :
        -(outputLoss * (hierarchy.finalStrongLoss / 4)) ≤
          -(cwaLossExponent : ℝ) * hierarchy.stableLoss := by
      linarith [numerics.cwa_final_gap]
    exact
      (pure_wz2_rpowENN_antitone
        deltaPos deltaLeOne exponentLe).trans <|
        pure_wz2_target_negative_power_lower
          deltaPos rhoPos rhoUpper
          (div_nonneg hierarchy.finalStrongLoss_pos.le (by norm_num))
  · intro delta deltaPos deltaLe rho rhoPos rhoLower
    have deltaLeOne : delta ≤ 1 :=
      deltaLe.trans <| delta₀LeHundred.trans (by norm_num)
    have ratioUpper :
        delta / rho ≤ Real.rpow delta outputLoss :=
      pureScalar_ratio_le_output_power deltaPos rhoPos rhoLower
    have exponentLe :
        -(outputLoss * hierarchy.finalStrongLoss) ≤
          -(cwaLossExponent : ℝ) * hierarchy.stableLoss := by
      have stableLossPos : 0 < hierarchy.stableLoss :=
        hierarchy.sourceLoss_pos.trans hierarchy.source_stable
      have cwaTermNonneg :
          0 ≤ (cwaLossExponent : ℝ) * hierarchy.stableLoss :=
        mul_nonneg (by positivity) stableLossPos.le
      linarith [numerics.cwa_final_gap]
    exact
      (pure_wz2_rpowENN_antitone
        deltaPos deltaLeOne exponentLe).trans <|
        pure_wz2_target_negative_power_lower
          deltaPos (div_pos deltaPos rhoPos) ratioUpper
          hierarchy.finalStrongLoss_pos.le
  · intro delta deltaPos deltaLe rho rhoPos rhoUpper
    have scaleLe : delta ≤ scaleDelta :=
      deltaLe.trans <| (min_le_right _ _).trans (min_le_left _ _)
    have rhoFiberLe : rho ≤ numerics.fiber.delta₀ :=
      rhoUpper.trans <|
        (scaleSmall delta deltaPos scaleLe).trans <|
          (min_le_right _ _).trans <|
            (min_le_right _ _).trans (min_le_right _ _)
    have raw := numerics.fiber.absorb rho rhoPos rhoFiberLe
    exact raw.trans <|
      pure_wz2_rpowENN_antitone
        rhoPos
        (rhoUpper.trans <|
          Real.rpow_le_one deltaPos.le
            (deltaLe.trans <| delta₀LeHundred.trans (by norm_num))
            outputLossPos.le)
        (by linarith [hierarchy.fiberDensityLoss_pos])
  · intro delta deltaPos deltaLe rho rhoPos rhoLower
    have scaleLe : delta ≤ scaleDelta :=
      deltaLe.trans <| (min_le_right _ _).trans (min_le_left _ _)
    have ratioUpper :
        delta / rho ≤ Real.rpow delta outputLoss :=
      pureScalar_ratio_le_output_power deltaPos rhoPos rhoLower
    have ratioFiberLe :
        delta / rho ≤ numerics.fiber.delta₀ :=
      ratioUpper.trans <|
        (scaleSmall delta deltaPos scaleLe).trans <|
          (min_le_right _ _).trans <|
            (min_le_right _ _).trans (min_le_right _ _)
    have raw :=
      numerics.fiber.absorb
        (delta / rho) (div_pos deltaPos rhoPos) ratioFiberLe
    exact raw.trans <|
      pure_wz2_rpowENN_antitone
        (div_pos deltaPos rhoPos)
        (ratioUpper.trans <|
          Real.rpow_le_one deltaPos.le
            (deltaLe.trans <| delta₀LeHundred.trans (by norm_num))
            outputLossPos.le)
        (by linarith [hierarchy.fiberDensityLoss_pos])

/--
One pure critical selection together with every scalar threshold required by
the V4 continuation.  This is the handoff record intended for the final
assembly: the critical witness and all inequalities are definitionally tied
to the same selected structural loss.
-/
structure Prop62V4PureScalarRoutingData
    (polylogExponent cwaPower packetDensityExponent cwaLossExponent : ℕ)
    (sigma outputLoss : ℝ) where
  routing :
    Prop62V4PureCriticalFloorRoutingData
      polylogExponent cwaPower packetDensityExponent cwaLossExponent
      sigma outputLoss
  scalar :
    Prop62V4PureScalarInputs
      polylogExponent cwaPower packetDensityExponent cwaLossExponent
      sigma outputLoss routing

theorem prop62V4_pure_scalar_routing_of_selection
    (polylogExponent cwaPower packetDensityExponent
      cwaLossExponent : ℕ)
    (sigma outputLoss : ℝ)
    (outputLossPos : 0 < outputLoss)
    (outputLossLeOne : outputLoss ≤ 1)
    (critical :
      PureWZ2CriticalFloorSelectionData sigma
        (wz2PaperCriticalFloorLoss outputLoss)
        (prop62V4CriticalStructuralBudget
          cwaPower packetDensityExponent cwaLossExponent outputLoss)) :
    Nonempty
      (Prop62V4PureScalarRoutingData
        polylogExponent cwaPower packetDensityExponent cwaLossExponent
        sigma outputLoss) := by
  have structuralLossInternal :
      critical.structuralLoss ≤
        wz2PaperInternalStrongLoss outputLoss := by
    exact critical.structuralLoss_le.trans <| by
      unfold prop62V4CriticalStructuralBudget
      exact min_le_left _ _
  have structuralLossExponent :
      critical.structuralLoss ≤
        outputLoss /
          (1000 *
            prop62V4CriticalExponentSum
              cwaPower packetDensityExponent cwaLossExponent) := by
    exact critical.structuralLoss_le.trans <| by
      unfold prop62V4CriticalStructuralBudget
      exact min_le_right _ _
  rcases
      prop62V4_critical_floor_numerics
        polylogExponent cwaPower packetDensityExponent cwaLossExponent
        outputLoss critical.structuralLoss outputLossPos outputLossLeOne
        critical.structuralLoss_pos structuralLossInternal
        structuralLossExponent
    with ⟨numerics⟩
  let routing :
      Prop62V4PureCriticalFloorRoutingData
        polylogExponent cwaPower packetDensityExponent cwaLossExponent
        sigma outputLoss :=
    { critical := critical, numerics := numerics }
  rcases
      prop62V4_pure_scalar_inputs
        polylogExponent cwaPower packetDensityExponent cwaLossExponent
        sigma outputLoss outputLossPos routing
    with ⟨scalar⟩
  exact ⟨{ routing := routing, scalar := scalar }⟩

theorem PureWZ2CriticalPackage.prop62V4_pure_scalar_routing
    {sigma outputLoss : ℝ}
    (critical : PureWZ2CriticalPackage sigma)
    (polylogExponent cwaPower packetDensityExponent
      cwaLossExponent : ℕ)
    (outputLossPos : 0 < outputLoss)
    (outputLossLeOne : outputLoss ≤ 1) :
    Nonempty
      (Prop62V4PureScalarRoutingData
        polylogExponent cwaPower packetDensityExponent cwaLossExponent
        sigma outputLoss) := by
  rcases
      Kakeya.Assouad.Prop62PaperAudit.V4.PureWZ2CriticalPackage.prop62V4_pure_critical_floor_routing
        critical
        polylogExponent cwaPower packetDensityExponent cwaLossExponent
        outputLossPos outputLossLeOne
    with ⟨routing⟩
  rcases
      prop62V4_pure_scalar_inputs
        polylogExponent cwaPower packetDensityExponent cwaLossExponent
        sigma outputLoss outputLossPos routing
    with ⟨scalar⟩
  exact ⟨{ routing := routing, scalar := scalar }⟩

end Kakeya.Assouad.Prop62PaperAudit.V4

end
