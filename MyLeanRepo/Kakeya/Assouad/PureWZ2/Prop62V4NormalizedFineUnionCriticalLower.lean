import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4FinalFiberCriticalWitness
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4WindowedCoarseTrace
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralUnitRescalingVolume

/-!
# Critical lower bounds retained by the normalized rich V4 producer

The normalized Proposition 6.2 kernel already constructs a pure critical
witness on every exact final complete fibre.  This module transfers that
witness back through the literal unit-rescaling map to the unchanged final
fibre shading.  It is the normalized-source analogue of
`Prop62V4FineUnionCriticalLower`.
-/

noncomputable section

namespace Kakeya.Assouad.Prop62PaperAudit.V4

open MeasureTheory
open Kakeya.Assouad

attribute [local instance] Classical.propDecidable

private theorem normalizedFineUnion_realRpowENN_sqrt
    {delta : ℝ} (hdelta : 0 < delta) (exponent : ℝ) :
    Kakeya.realRpowENN (Real.sqrt delta) exponent =
      Kakeya.realRpowENN delta (exponent / 2) := by
  simp only [Kakeya.realRpowENN]
  congr 1
  rw [show Real.sqrt delta = Real.rpow delta (1 / 2 : ℝ) by
    simp [Real.sqrt_eq_rpow]]
  calc
    Real.rpow (Real.rpow delta (1 / 2 : ℝ)) exponent =
        Real.rpow delta ((1 / 2 : ℝ) * exponent) :=
      (Real.rpow_mul hdelta.le (1 / 2 : ℝ) exponent).symm
    _ = Real.rpow delta (exponent / 2) := by
      congr 1
      ring

private theorem normalizedFineUnion_realRpowENN_negative_inverse
    {scale : ℝ} (scalePos : 0 < scale) (exponent : ℝ) :
    (Kakeya.realRpowENN scale (-exponent))⁻¹ =
      Kakeya.realRpowENN scale exponent := by
  simp only [Kakeya.realRpowENN]
  calc
    (ENNReal.ofReal (Real.rpow scale (-exponent)))⁻¹ =
        ENNReal.ofReal ((Real.rpow scale (-exponent))⁻¹) :=
      (ENNReal.ofReal_inv_of_pos
        (Real.rpow_pos_of_pos scalePos (-exponent))).symm
    _ = ENNReal.ofReal (Real.rpow scale exponent) := by
      congr 1
      have negativePower :
          Real.rpow scale (-exponent) =
            (Real.rpow scale exponent)⁻¹ :=
        Real.rpow_neg scalePos.le exponent
      rw [negativePower, inv_inv]

private theorem normalizedFineUnion_ofReal_inverse_square_inverse
    {scale : ℝ} (scalePos : 0 < scale) :
    (ENNReal.ofReal ((1 / scale : ℝ) ^ 2))⁻¹ =
      Kakeya.realRpowENN scale 2 := by
  simp only [Kakeya.realRpowENN]
  calc
    (ENNReal.ofReal ((1 / scale : ℝ) ^ 2))⁻¹ =
        ENNReal.ofReal (((1 / scale : ℝ) ^ 2)⁻¹) :=
      (ENNReal.ofReal_inv_of_pos
        (sq_pos_of_pos (one_div_pos.mpr scalePos))).symm
    _ = ENNReal.ofReal (scale ^ 2) := by
      congr 1
      field_simp [scalePos.ne']
    _ = ENNReal.ofReal (Real.rpow scale 2) := by
      exact congrArg ENNReal.ofReal (Real.rpow_two scale).symm

namespace Prop62V4RichCertificateCompanionData.FixedGridPureScalar

variable
    {polylogExponent cwaPower packetDensityExponent cwaLossExponent : ℕ}
    {delta sigma sourceLoss normalizationLoss eta outputLoss : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {normalizationExponent : ℕ}
    {normalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent}
    {rho : WZ2PaperRequestedScale delta}
    {hdelta : 0 < delta}
    {preparation : FixedGridPreparationData
      (rho := rho.1) normalized.croppedRefined hdelta}
    {fineParentDistanceConstant : ℝ}
    {parentConstant fiberConstant : ENNReal}
    {metricCertificate : PureWZ2Prop62MetricParentsV4Certificate
      preparation.cleanup.refined rho fineParentDistanceConstant
        parentConstant fiberConstant}
    {routing : Prop62V4PureCriticalFloorRoutingData
      polylogExponent cwaPower packetDensityExponent cwaLossExponent
        sigma outputLoss}
    (rich : Prop62V4RichCertificateCompanionData
      (eta := eta)
      (packetDensityExponent := packetDensityExponent)
      (cwaLossExponent := cwaLossExponent)
      (polylogExponent := polylogExponent)
      hdelta
      (prop62V4FixedGridMetricCompanionOfCertificate
        normalized preparation metricCertificate))
    (scalar : Prop62V4PureScalarInputs
      polylogExponent cwaPower packetDensityExponent cwaLossExponent
        sigma outputLoss routing)
    (deltaLe : delta ≤ scalar.delta₀)
    (rhoLower : Real.rpow delta (1 - outputLoss) ≤ rho.1)
    (sourceLoss_le : sourceLoss ≤ routing.numerics.hierarchy.sourceLoss)
    (eta_eq : eta = routing.numerics.hierarchy.stableLoss)

include scalar deltaLe rhoLower sourceLoss_le eta_eq

/-- The critical floor on the exact-image ordinary witness, pulled back to the
unchanged final complete-fibre shading. -/
theorem parent_fiber_union_critical_lower
    (parent : Fin rich.outputCertificate.coarse.family.card) :
    Kakeya.realRpowENN (delta / rho.1)
          (sigma + wz2PaperCriticalFloorLoss outputLoss) ≤
      (ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
          ENNReal.ofReal ((1 / rho.1 : ℝ) ^ 2)) *
        volume
          (restrictPaperShading
            (wz2PaperFullFiberSubfamily
              rich.outputCertificate.refinement.selected.family
              rich.outputCertificate.coarse.family parent)
            rich.outputCertificate.refinement.refined).union := by
  let scalarInputs := critical_inputs rich scalar deltaLe rhoLower
    sourceLoss_le eta_eq parent
  let witness := rich.fixedGridFinalFiberCriticalWitness parent scalarInputs
  let fiberShading :=
    PureWZ2CroppedCriticalNormalizationData.criticalFinalFiberShading
      (normalized := normalized)
      rich.fixedGridComposedSelected rich.fixedGridComposedShading
      rich.outputCertificate.coarse.family parent
  let ordinaryTrace :=
    PureWZ2CroppedCriticalNormalizationData.criticalFinalFiberOrdinaryTrace
      (normalized := normalized)
      rich.fixedGridComposedSelected rich.fixedGridComposedShading
      rich.outputCertificate.coarse.family parent
  let certificate :=
    PureWZ2CroppedCriticalNormalizationData.criticalFinalFiberRescalingCertificate
      normalized rich.fixedGridComposedSelected
      rich.outputCertificate.coarse.family rich.outputCertificate.cover parent
      (rich.outputCertificate.rescaled_fiber_input parent)
  have hratioPos : 0 < delta / rho.1 :=
    div_pos hdelta metricCertificate.rho_pos
  have hcritical :
      Kakeya.realRpowENN (delta / rho.1)
            (sigma + wz2PaperCriticalFloorLoss outputLoss) ≤
        volume witness.ordinaryShading.union := by
    exact routing.critical.volume_floor
      (delta / rho.1) hratioPos
      (scalar.ratio_critical hdelta deltaLe
        metricCertificate.rho_pos rhoLower)
      witness.ordinaryFamily witness.ordinary_nonempty
      witness.ordinaryShading witness.ordinary_cwa witness.ordinary_dense
  have hunion :
      witness.ordinaryShading.union =
        wz2PaperLiteralUnitRescalingMap
            (rich.outputCertificate.coarse.family.tube parent)
            metricCertificate.rho_pos '' ordinaryTrace.union := by
    change
      (certificate.literalExactImageShading ordinaryTrace).union =
        wz2PaperLiteralUnitRescalingMap
            (rich.outputCertificate.coarse.family.tube parent)
            metricCertificate.rho_pos '' ordinaryTrace.union
    exact
      Kakeya.Assouad.WZ2PaperAssouadToLiteralRescalingCertificate.literalExactImageShading_union_eq
        certificate ordinaryTrace
  have hvolume :
      volume witness.ordinaryShading.union =
        (ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
            ENNReal.ofReal ((1 / rho.1 : ℝ) ^ 2)) *
          volume ordinaryTrace.union := by
    rw [hunion]
    exact wz2_paper_literal_unit_rescaling_volume
      (rich.outputCertificate.coarse.family.tube parent)
      metricCertificate.rho_pos ordinaryTrace.union
      (measurableSet_shading_union ordinaryTrace)
  have hsubset : ordinaryTrace.union ⊆ fiberShading.union := by
    rintro point ⟨index, hpoint⟩
    exact ⟨index,
      Kakeya.Assouad.PureWZ2CroppedCriticalNormalizationData.criticalFinalFiberOrdinaryTrace_subset
        normalized rich.fixedGridComposedSelected
        rich.fixedGridComposedShading
        rich.outputCertificate.coarse.family parent index hpoint⟩
  calc
    Kakeya.realRpowENN (delta / rho.1)
          (sigma + wz2PaperCriticalFloorLoss outputLoss) ≤
        volume witness.ordinaryShading.union := hcritical
    _ = (ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
          ENNReal.ofReal ((1 / rho.1 : ℝ) ^ 2)) *
        volume ordinaryTrace.union := hvolume
    _ ≤ (ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
          ENNReal.ofReal ((1 / rho.1 : ℝ) ^ 2)) *
        volume fiberShading.union := by gcongr
    _ = _ := rfl

/-- The exact final-fibre floor and the selected-parent cell-count bound give
a lower bound for the unchanged terminal balanced-cell mass. -/
theorem balanced_cellMass_critical_lower
    (rhoUpper : rho.1 ≤ Real.rpow delta outputLoss)
    (parent : Fin rich.outputCertificate.coarse.family.card) :
    (55296 * Kakeya.deltaTubeVolume 1 : ENNReal)⁻¹ *
          ENNReal.ofReal rho.1 *
          (ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
            ENNReal.ofReal ((1 / rho.1 : ℝ) ^ 2))⁻¹ *
          Kakeya.realRpowENN (delta / rho.1)
            (sigma + wz2PaperCriticalFloorLoss outputLoss) ≤
      rich.outputCertificate.balanced.cellMass := by
  let output := rich.outputCertificate
  let cellCount : ENNReal := (output.selectedParentCells parent).card
  let jacobian : ENNReal :=
    ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
      ENNReal.ofReal ((1 / rho.1 : ℝ) ^ 2)
  let geometry : ENNReal := 55296 * Kakeya.deltaTubeVolume 1
  let criticalPower : ENNReal :=
    Kakeya.realRpowENN (delta / rho.1)
      (sigma + wz2PaperCriticalFloorLoss outputLoss)
  have fiberLower :
      criticalPower ≤ jacobian *
        volume (output.windowedFullFiberShading parent).union := by
    have raw :=
      parent_fiber_union_critical_lower rich scalar deltaLe rhoLower
        sourceLoss_le eta_eq parent
    change criticalPower ≤ jacobian *
      volume (output.windowedFullFiberShading parent).union
    exact raw
  have fiberLowerExplicit :
      jacobian⁻¹ * criticalPower ≤
        volume (output.windowedFullFiberShading parent).union := by
    have hjacobianPos : 0 < jacobian := by
      dsimp only [jacobian]
      exact ENNReal.mul_pos
        (ENNReal.ofReal_pos.mpr (by norm_num)).ne'
        (ENNReal.ofReal_pos.mpr
          (sq_pos_of_pos (one_div_pos.mpr metricCertificate.rho_pos))).ne'
    have hjacobianTop : jacobian ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    exact (ENNReal.inv_mul_le_iff hjacobianPos.ne' hjacobianTop).2
      (by simpa only [mul_comm] using fiberLower)
  have fiberUpper :
      volume (output.windowedFullFiberShading parent).union ≤
        cellCount * output.balanced.cellMass := by
    simpa only [cellCount] using
      output.windowedFullFiberShading_union_volume_upper parent
  have cellCountScale :
      cellCount * ENNReal.ofReal rho.1 ≤ geometry := by
    simpa only [cellCount, geometry] using
      output.selectedParentCells_card_mul_scale_le
        metricCertificate.rho_pos
        (scalar.rho_small hdelta deltaLe rhoUpper) parent
  have scaled :
      ENNReal.ofReal rho.1 * (jacobian⁻¹ * criticalPower) ≤
        geometry * output.balanced.cellMass := by
    calc
      ENNReal.ofReal rho.1 * (jacobian⁻¹ * criticalPower) ≤
          ENNReal.ofReal rho.1 *
            volume (output.windowedFullFiberShading parent).union := by gcongr
      _ ≤ ENNReal.ofReal rho.1 *
          (cellCount * output.balanced.cellMass) := by gcongr
      _ = (cellCount * ENNReal.ofReal rho.1) *
          output.balanced.cellMass := by ring
      _ ≤ geometry * output.balanced.cellMass := by gcongr
  have geometryPos : 0 < geometry := by
    dsimp only [geometry]
    exact ENNReal.mul_pos (by norm_num)
      (zero_lt_one.trans_le one_le_deltaTubeVolume_one).ne'
  have geometryTop : geometry ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) deltaTubeVolume_one_ne_top
  calc
    (55296 * Kakeya.deltaTubeVolume 1 : ENNReal)⁻¹ *
          ENNReal.ofReal rho.1 *
          (ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
            ENNReal.ofReal ((1 / rho.1 : ℝ) ^ 2))⁻¹ *
          Kakeya.realRpowENN (delta / rho.1)
            (sigma + wz2PaperCriticalFloorLoss outputLoss) =
        geometry⁻¹ *
          (ENNReal.ofReal rho.1 * (jacobian⁻¹ * criticalPower)) := by
      simp only [geometry, jacobian, criticalPower]
      ring
    _ ≤ output.balanced.cellMass :=
      (ENNReal.inv_mul_le_iff geometryPos.ne' geometryTop).2 scaled

/-- A clean arbitrary-scale form of the same balanced-cell floor.  All fixed
geometric constants are absorbed by the pre-runtime V4 scalar schedule. -/
theorem balanced_cellMass_power_lower
    (rhoUpper : rho.1 ≤ Real.rpow delta outputLoss)
    (parent : Fin rich.outputCertificate.coarse.family.card) :
    Kakeya.realRpowENN rho.1 3 *
          Kakeya.realRpowENN (delta / rho.1)
            (sigma + 2 * routing.numerics.hierarchy.finalStrongLoss) ≤
      rich.outputCertificate.balanced.cellMass := by
  let finalLoss := routing.numerics.hierarchy.finalStrongLoss
  let floorLoss := wz2PaperCriticalFloorLoss outputLoss
  let ratio := delta / rho.1
  let jacobian : ENNReal :=
    ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
      ENNReal.ofReal ((1 / rho.1 : ℝ) ^ 2)
  let geometry : ENNReal := 55296 * Kakeya.deltaTubeVolume 1
  let rawPower := Kakeya.realRpowENN ratio (sigma + floorLoss)
  have rhoPos : 0 < rho.1 := metricCertificate.rho_pos
  have ratioPos : 0 < ratio := div_pos hdelta rhoPos
  have ratioOne : ratio ≤ 1 :=
    (scalar.ratio_small hdelta deltaLe rhoPos rhoLower).trans (by norm_num)
  have floorLossLeFinal : floorLoss ≤ finalLoss := by
    have componentLtFinal :
        routing.numerics.hierarchy.componentLoss < finalLoss := by
      dsimp only [finalLoss]
      rw [routing.numerics.hierarchy.componentLoss_eq,
        routing.numerics.hierarchy.finalStrongLoss_eq]
      dsimp only [wz2PaperFinalComponentLoss, wz2PaperFinalStrongLoss]
      have outputLossPos : 0 < outputLoss := by
        have hpos := routing.numerics.hierarchy.finalStrongLoss_pos
        rw [routing.numerics.hierarchy.finalStrongLoss_eq] at hpos
        dsimp only [wz2PaperFinalStrongLoss] at hpos
        linarith
      linarith
    have chain :
        routing.numerics.hierarchy.criticalFloorLoss ≤
          routing.numerics.hierarchy.finalStrongLoss :=
      (((routing.numerics.hierarchy.critical_internal.trans
        routing.numerics.hierarchy.internal_cap).trans
          routing.numerics.hierarchy.cap_component).trans
            componentLtFinal).le
    simpa only [floorLoss, finalLoss,
      routing.numerics.hierarchy.criticalFloorLoss_eq] using chain
  have geometryBound :
      geometry ≤ Kakeya.realRpowENN ratio (-finalLoss) := by
    simpa only [geometry, ratio, finalLoss] using
      scalar.final_fiber_carrier hdelta deltaLe rhoPos rhoLower
  have geometryInverseLower :
      Kakeya.realRpowENN ratio finalLoss ≤ geometry⁻¹ := by
    have inverseBound := ENNReal.inv_le_inv.mpr geometryBound
    rw [normalizedFineUnion_realRpowENN_negative_inverse
      ratioPos finalLoss] at inverseBound
    exact inverseBound
  have jacobianLe :
      jacobian ≤ ENNReal.ofReal ((1 / rho.1 : ℝ) ^ 2) := by
    dsimp only [jacobian]
    calc
      ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
            ENNReal.ofReal ((1 / rho.1 : ℝ) ^ 2) ≤
          1 * ENNReal.ofReal ((1 / rho.1 : ℝ) ^ 2) := by
        gcongr
        norm_num
      _ = _ := one_mul _
  have jacobianInverseLower :
      Kakeya.realRpowENN rho.1 2 ≤ jacobian⁻¹ := by
    have inverseBound := ENNReal.inv_le_inv.mpr jacobianLe
    rw [normalizedFineUnion_ofReal_inverse_square_inverse rhoPos] at inverseBound
    exact inverseBound
  have rhoThree :
      Kakeya.realRpowENN rho.1 3 =
        ENNReal.ofReal rho.1 * Kakeya.realRpowENN rho.1 2 := by
    rw [show ENNReal.ofReal rho.1 =
      Kakeya.realRpowENN rho.1 1 by
        simp [Kakeya.realRpowENN, Real.rpow_one]]
    rw [← realRpowENN_add rhoPos]
    norm_num
  have ratioPower :
      Kakeya.realRpowENN ratio (sigma + 2 * finalLoss) ≤
        Kakeya.realRpowENN ratio finalLoss * rawPower := by
    rw [show Kakeya.realRpowENN ratio finalLoss * rawPower =
        Kakeya.realRpowENN ratio (sigma + floorLoss + finalLoss) by
      dsimp only [rawPower]
      rw [← realRpowENN_add ratioPos]
      congr 1
      ring]
    exact pure_wz2_rpowENN_antitone ratioPos ratioOne (by linarith)
  have rawLower :
      geometry⁻¹ * ENNReal.ofReal rho.1 * jacobian⁻¹ * rawPower ≤
        rich.outputCertificate.balanced.cellMass := by
    simpa only [geometry, jacobian, ratio, rawPower] using
      balanced_cellMass_critical_lower rich scalar deltaLe rhoLower
        sourceLoss_le eta_eq rhoUpper parent
  calc
    Kakeya.realRpowENN rho.1 3 *
          Kakeya.realRpowENN (delta / rho.1)
            (sigma + 2 * routing.numerics.hierarchy.finalStrongLoss) =
        (ENNReal.ofReal rho.1 * Kakeya.realRpowENN rho.1 2) *
          Kakeya.realRpowENN ratio (sigma + 2 * finalLoss) := by
      rw [rhoThree]
    _ ≤ (ENNReal.ofReal rho.1 * Kakeya.realRpowENN rho.1 2) *
          (Kakeya.realRpowENN ratio finalLoss * rawPower) := by gcongr
    _ ≤ ENNReal.ofReal rho.1 * jacobian⁻¹ *
          (geometry⁻¹ * rawPower) := by gcongr
    _ = geometry⁻¹ * ENNReal.ofReal rho.1 *
          jacobian⁻¹ * rawPower := by ring
    _ ≤ rich.outputCertificate.balanced.cellMass := rawLower

/-- Square-root specialization in the exact exponent required by WZ1 Lemma
5.3. -/
theorem balanced_cellMass_critical_lower_at_sqrt
    (rhoUpper : rho.1 ≤ Real.rpow delta outputLoss)
    (hrho : rho.1 = Real.sqrt delta)
    (parent : Fin rich.outputCertificate.coarse.family.card) :
    Kakeya.realRpowENN delta
          (3 / 2 + sigma / 2 +
            routing.numerics.hierarchy.finalStrongLoss) ≤
      rich.outputCertificate.balanced.cellMass := by
  let finalLoss := routing.numerics.hierarchy.finalStrongLoss
  let floorLoss := wz2PaperCriticalFloorLoss outputLoss
  let ratio := delta / rho.1
  let jacobian : ENNReal :=
    ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
      ENNReal.ofReal ((1 / rho.1 : ℝ) ^ 2)
  let geometry : ENNReal := 55296 * Kakeya.deltaTubeVolume 1
  let rawPower := Kakeya.realRpowENN ratio (sigma + floorLoss)
  have rhoPos : 0 < rho.1 := metricCertificate.rho_pos
  have ratioPos : 0 < ratio := div_pos hdelta rhoPos
  have deltaOne : delta ≤ 1 :=
    deltaLe.trans <| scalar.delta₀_le_one_hundred.trans (by norm_num)
  have ratioEq : ratio = Real.sqrt delta := by
    dsimp only [ratio]
    rw [hrho]
    apply (div_eq_iff (Real.sqrt_pos.2 hdelta).ne').2
    nlinarith [Real.sq_sqrt hdelta.le]
  have rhoPower (exponent : ℝ) :
      Kakeya.realRpowENN rho.1 exponent =
        Kakeya.realRpowENN delta (exponent / 2) := by
    rw [hrho]
    exact normalizedFineUnion_realRpowENN_sqrt hdelta exponent
  have ratioPower (exponent : ℝ) :
      Kakeya.realRpowENN ratio exponent =
        Kakeya.realRpowENN delta (exponent / 2) := by
    rw [ratioEq]
    exact normalizedFineUnion_realRpowENN_sqrt hdelta exponent
  have ofRealRho :
      ENNReal.ofReal rho.1 = Kakeya.realRpowENN rho.1 1 := by
    simp [Kakeya.realRpowENN, Real.rpow_one]
  have floorLossLeFinal : floorLoss ≤ finalLoss := by
    have componentLtFinal :
        routing.numerics.hierarchy.componentLoss < finalLoss := by
      dsimp only [finalLoss]
      rw [routing.numerics.hierarchy.componentLoss_eq,
        routing.numerics.hierarchy.finalStrongLoss_eq]
      dsimp only [wz2PaperFinalComponentLoss, wz2PaperFinalStrongLoss]
      have outputLossPos : 0 < outputLoss := by
        have hpos := routing.numerics.hierarchy.finalStrongLoss_pos
        rw [routing.numerics.hierarchy.finalStrongLoss_eq] at hpos
        dsimp only [wz2PaperFinalStrongLoss] at hpos
        linarith
      linarith
    have chain :
        routing.numerics.hierarchy.criticalFloorLoss ≤
          routing.numerics.hierarchy.finalStrongLoss :=
      (((routing.numerics.hierarchy.critical_internal.trans
        routing.numerics.hierarchy.internal_cap).trans
          routing.numerics.hierarchy.cap_component).trans
            componentLtFinal).le
    simpa only [floorLoss, finalLoss,
      routing.numerics.hierarchy.criticalFloorLoss_eq] using chain
  have geometryBound :
      geometry ≤ Kakeya.realRpowENN ratio (-finalLoss) := by
    simpa only [geometry, ratio, finalLoss] using
      scalar.final_fiber_carrier hdelta deltaLe rhoPos rhoLower
  have geometryInverseLower :
      Kakeya.realRpowENN ratio finalLoss ≤ geometry⁻¹ := by
    have inverseBound := ENNReal.inv_le_inv.mpr geometryBound
    rw [normalizedFineUnion_realRpowENN_negative_inverse
      ratioPos finalLoss] at inverseBound
    exact inverseBound
  have jacobianLe :
      jacobian ≤ ENNReal.ofReal ((1 / rho.1 : ℝ) ^ 2) := by
    dsimp only [jacobian]
    calc
      ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
            ENNReal.ofReal ((1 / rho.1 : ℝ) ^ 2) ≤
          1 * ENNReal.ofReal ((1 / rho.1 : ℝ) ^ 2) := by
        gcongr
        norm_num
      _ = _ := one_mul _
  have jacobianInverseLower :
      Kakeya.realRpowENN rho.1 2 ≤ jacobian⁻¹ := by
    have inverseBound := ENNReal.inv_le_inv.mpr jacobianLe
    rw [normalizedFineUnion_ofReal_inverse_square_inverse rhoPos] at inverseBound
    exact inverseBound
  have targetExponentLe :
      (3 + sigma + floorLoss + finalLoss) / 2 ≤
        3 / 2 + sigma / 2 + finalLoss := by
    linarith
  have powerLower :
      Kakeya.realRpowENN delta
            (3 / 2 + sigma / 2 + finalLoss) ≤
        Kakeya.realRpowENN ratio finalLoss *
          ENNReal.ofReal rho.1 *
          Kakeya.realRpowENN rho.1 2 * rawPower := by
    calc
      Kakeya.realRpowENN delta
            (3 / 2 + sigma / 2 + finalLoss) ≤
          Kakeya.realRpowENN delta
            ((3 + sigma + floorLoss + finalLoss) / 2) :=
        pure_wz2_rpowENN_antitone hdelta deltaOne targetExponentLe
      _ = Kakeya.realRpowENN ratio finalLoss *
            ENNReal.ofReal rho.1 *
            Kakeya.realRpowENN rho.1 2 * rawPower := by
        dsimp only [rawPower]
        rw [ofRealRho, rhoPower, rhoPower, ratioPower, ratioPower]
        rw [← realRpowENN_add hdelta, ← realRpowENN_add hdelta,
          ← realRpowENN_add hdelta]
        congr 1
        dsimp only [floorLoss, finalLoss]
        ring
  have rawLower :
      geometry⁻¹ * ENNReal.ofReal rho.1 * jacobian⁻¹ * rawPower ≤
        rich.outputCertificate.balanced.cellMass := by
    simpa only [geometry, jacobian, ratio, rawPower] using
      balanced_cellMass_critical_lower rich scalar deltaLe rhoLower
        sourceLoss_le eta_eq rhoUpper parent
  calc
    Kakeya.realRpowENN delta
          (3 / 2 + sigma / 2 +
            routing.numerics.hierarchy.finalStrongLoss) ≤
        Kakeya.realRpowENN ratio finalLoss *
          ENNReal.ofReal rho.1 *
          Kakeya.realRpowENN rho.1 2 * rawPower := by
      simpa only [finalLoss] using powerLower
    _ ≤ geometry⁻¹ * ENNReal.ofReal rho.1 *
          jacobian⁻¹ * rawPower := by gcongr
    _ ≤ rich.outputCertificate.balanced.cellMass := rawLower

end Prop62V4RichCertificateCompanionData.FixedGridPureScalar

end Kakeya.Assouad.Prop62PaperAudit.V4

end
