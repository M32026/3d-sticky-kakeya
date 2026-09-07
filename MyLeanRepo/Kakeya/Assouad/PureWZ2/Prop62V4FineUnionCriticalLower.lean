import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4DirectNode6FixedScale
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4WindowedCoarseTrace
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralUnitRescalingVolume

/-!
# Critical lower bound on the direct V4 final fine union

This module uses the exact ordinary image inside each bounded final fiber.
The critical floor is applied only to that genuine ordinary shading; the new
exact-image union identity and the literal Jacobian formula then transfer the
lower bound back to the unchanged final cropped fiber, and hence to the full
final refinement.
-/

noncomputable section

namespace Kakeya.Assouad.Prop62PaperAudit.V4

open MeasureTheory
open Kakeya.Assouad

attribute [local instance] Classical.propDecidable

private theorem fineUnion_realRpowENN_sqrt
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

private theorem realRpowENN_negative_inverse
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

private theorem ofReal_inverse_square_inverse
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

namespace Prop62V4BoundedFinalFiber

/-- The ordinary shading stored by the bounded final-fiber witness is the
exact literal affine image, with no cubical saturation. -/
theorem witness_ordinary_union_eq
    {delta rho structuralLoss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {parent : Fin coarse.card}
    {sourceConstant : ENNReal}
    (rescaling :
      PureWZ2Prop62MetricFiberRescalingInput
        cover parent sourceConstant)
    (sourceShading :
      WZ1PaperTubeShading
        (wz2PaperFullFiberSubfamily fine coarse parent).family)
    (boundedBase : HasBoundedBase rescaling.sourceFamily 4)
    (packetDensity : ENNReal)
    (packetMassLower :
      packetDensity *
          (wz2PaperFullFiberSubfamily fine coarse parent).family.enncard *
          Kakeya.realRpowENN delta 2 ≤
        sourceShading.mass)
    (cwaAbsorption :
      (81000000 : ENNReal) * sourceConstant ≤
        Kakeya.realRpowENN (delta / rho) (-structuralLoss))
    (densityAbsorption :
      Kakeya.realRpowENN (delta / rho) structuralLoss *
          (55296 * Kakeya.deltaTubeVolume 1) ≤
        ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) * packetDensity) :
    (Prop62V4BoundedFinalFiber.witness
      rescaling sourceShading boundedBase packetDensity
      packetMassLower cwaAbsorption densityAbsorption).ordinaryShading.union =
      wz2PaperLiteralUnitRescalingMap (coarse.tube parent) rescaling.rho_pos ''
        sourceShading.union := by
  apply
    WZ2PaperAssouadToLiteralRescalingCertificate.literalExactCroppedImageShading_union_eq

end Prop62V4BoundedFinalFiber

namespace Prop62V4DirectCroppedProducerData

/--
The pure critical floor on one exact final fiber, transferred back through
the literal affine image.  The conclusion remains on that same restricted
parent-fiber shading; no comparison with the full final union occurs here.
-/
theorem parent_fiber_union_critical_lower
    {delta sigma outputLoss : ℝ}
    {routing :
      Prop62V4PureCriticalFloorRoutingData 10 8 2 51 sigma outputLoss}
    (scalar : Prop62V4PureScalarInputs 10 8 2 51 sigma outputLoss routing)
    (cfg :
      PureWZ2C2GrainConfiguration
        sigma routing.numerics.hierarchy.sourceLoss delta)
    (rho : WZ2PaperRequestedScale delta)
    (hdelta : 0 < delta)
    (produced :
      Prop62V4DirectCroppedProducerData
        (workingEta := routing.numerics.hierarchy.stableLoss)
        cfg rho hdelta)
    (deltaLe : delta ≤ scalar.delta₀)
    (rhoLower : Real.rpow delta (1 - outputLoss) ≤ rho.1)
    (parent : Fin produced.rich.outputCertificate.coarse.family.card) :
    Kakeya.realRpowENN (delta / rho.1)
          (sigma + wz2PaperCriticalFloorLoss outputLoss) ≤
      (ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
          ENNReal.ofReal ((1 / rho.1 : ℝ) ^ 2)) *
        volume
          (restrictPaperShading
            (wz2PaperFullFiberSubfamily
              produced.finalRefinement.selected.family
              produced.rich.outputCertificate.coarse.family parent)
            produced.finalRefinement.refined).union := by
  let sourceShading :=
    restrictPaperShading
      (wz2PaperFullFiberSubfamily
        produced.finalRefinement.selected.family
        produced.rich.outputCertificate.coarse.family parent)
      produced.finalRefinement.refined
  let rescaling :=
    produced.rich.outputCertificate.rescaled_fiber_input parent
  let fiberWitness :=
    Prop62V4BoundedFinalFiber.witness
      (structuralLoss := routing.critical.structuralLoss)
      rescaling sourceShading
      (produced.rescaling_source_bounded_base parent)
      ((2 : ENNReal)⁻¹ *
        Kakeya.realRpowENN delta
          (2 * routing.numerics.hierarchy.stableLoss))
      (produced.packet_mass_lower (routing := routing) rfl parent)
      (produced.rich.terminal_fiber_constant_bound.trans <|
        scalar.fiber_cwa hdelta deltaLe
          produced.metricCertificate.rho_pos rhoLower)
      (scalar.fiber_density hdelta deltaLe
        produced.metricCertificate.rho_pos rhoLower)
  have ratioCritical : delta / rho.1 ≤ routing.critical.delta₀ :=
    scalar.ratio_critical hdelta deltaLe
      produced.metricCertificate.rho_pos rhoLower
  have criticalLower :
      Kakeya.realRpowENN (delta / rho.1)
            (sigma + wz2PaperCriticalFloorLoss outputLoss) ≤
        volume fiberWitness.ordinaryShading.union :=
    routing.critical.volume_floor
      (delta / rho.1)
      (div_pos hdelta produced.metricCertificate.rho_pos)
      ratioCritical
      fiberWitness.ordinaryFamily fiberWitness.ordinary_nonempty
      fiberWitness.ordinaryShading fiberWitness.ordinary_cwa
      fiberWitness.ordinary_dense
  have exactImageVolume :
      volume fiberWitness.ordinaryShading.union =
        (ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
            ENNReal.ofReal ((1 / rho.1 : ℝ) ^ 2)) *
          volume sourceShading.union := by
    rw [Prop62V4BoundedFinalFiber.witness_ordinary_union_eq]
    exact
      wz2_paper_literal_unit_rescaling_volume
        (produced.rich.outputCertificate.coarse.family.tube parent)
        rescaling.rho_pos sourceShading.union sourceShading.union_measurable
  exact criticalLower.trans_eq exactImageVolume

/-- The parent-fiber critical lower bound solved explicitly for its unchanged
restricted source union. -/
theorem parent_fiber_union_critical_lower_explicit
    {delta sigma outputLoss : ℝ}
    {routing :
      Prop62V4PureCriticalFloorRoutingData 10 8 2 51 sigma outputLoss}
    (scalar : Prop62V4PureScalarInputs 10 8 2 51 sigma outputLoss routing)
    (cfg :
      PureWZ2C2GrainConfiguration
        sigma routing.numerics.hierarchy.sourceLoss delta)
    (rho : WZ2PaperRequestedScale delta)
    (hdelta : 0 < delta)
    (produced :
      Prop62V4DirectCroppedProducerData
        (workingEta := routing.numerics.hierarchy.stableLoss)
        cfg rho hdelta)
    (deltaLe : delta ≤ scalar.delta₀)
    (rhoLower : Real.rpow delta (1 - outputLoss) ≤ rho.1)
    (parent : Fin produced.rich.outputCertificate.coarse.family.card) :
    (ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
          ENNReal.ofReal ((1 / rho.1 : ℝ) ^ 2))⁻¹ *
        Kakeya.realRpowENN (delta / rho.1)
          (sigma + wz2PaperCriticalFloorLoss outputLoss) ≤
      volume
        (restrictPaperShading
          (wz2PaperFullFiberSubfamily
            produced.finalRefinement.selected.family
            produced.rich.outputCertificate.coarse.family parent)
          produced.finalRefinement.refined).union := by
  let jacobian : ENNReal :=
    ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
      ENNReal.ofReal ((1 / rho.1 : ℝ) ^ 2)
  have jacobianPos : 0 < jacobian := by
    dsimp only [jacobian]
    exact ENNReal.mul_pos
      (ENNReal.ofReal_pos.mpr (by norm_num)).ne'
      (ENNReal.ofReal_pos.mpr (sq_pos_of_pos <|
        one_div_pos.mpr produced.metricCertificate.rho_pos)).ne'
  have jacobianTop : jacobian ≠ ⊤ := by
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  apply (ENNReal.inv_mul_le_iff jacobianPos.ne' jacobianTop).2
  simpa only [jacobian] using
    parent_fiber_union_critical_lower
      scalar cfg rho hdelta produced deltaLe rhoLower parent

/--
Raw balanced-cell floor obtained from one exact final fiber.  The proof keeps
the selected-parent-cell cardinality visible until the final multiplication
by `rho`; it uses no coarse critical floor or whole-fine overlap estimate.
-/
theorem balanced_cellMass_critical_lower
    {delta sigma outputLoss : ℝ}
    {routing :
      Prop62V4PureCriticalFloorRoutingData 10 8 2 51 sigma outputLoss}
    (scalar : Prop62V4PureScalarInputs 10 8 2 51 sigma outputLoss routing)
    (cfg :
      PureWZ2C2GrainConfiguration
        sigma routing.numerics.hierarchy.sourceLoss delta)
    (rho : WZ2PaperRequestedScale delta)
    (hdelta : 0 < delta)
    (produced :
      Prop62V4DirectCroppedProducerData
        (workingEta := routing.numerics.hierarchy.stableLoss)
        cfg rho hdelta)
    (deltaLe : delta ≤ scalar.delta₀)
    (rhoLower : Real.rpow delta (1 - outputLoss) ≤ rho.1)
    (rhoUpper : rho.1 ≤ Real.rpow delta outputLoss)
    (parent : Fin produced.rich.outputCertificate.coarse.family.card) :
    (55296 * Kakeya.deltaTubeVolume 1 : ENNReal)⁻¹ *
          ENNReal.ofReal rho.1 *
          (ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
            ENNReal.ofReal ((1 / rho.1 : ℝ) ^ 2))⁻¹ *
          Kakeya.realRpowENN (delta / rho.1)
            (sigma + wz2PaperCriticalFloorLoss outputLoss) ≤
      produced.rich.outputCertificate.balanced.cellMass := by
  let output := produced.rich.outputCertificate
  let cellCount : ENNReal :=
    (output.selectedParentCells parent).card
  let jacobian : ENNReal :=
    ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
      ENNReal.ofReal ((1 / rho.1 : ℝ) ^ 2)
  let geometry : ENNReal := 55296 * Kakeya.deltaTubeVolume 1
  let criticalPower : ENNReal :=
    Kakeya.realRpowENN (delta / rho.1)
      (sigma + wz2PaperCriticalFloorLoss outputLoss)
  have fiberLower :
      jacobian⁻¹ * criticalPower ≤
        volume (output.windowedFullFiberShading parent).union := by
    simpa only [output, jacobian, criticalPower,
      PureWZ2Prop62FourDegreeOutputCertificate.windowedFullFiberShading,
      produced.finalRefinement_selected_family,
      produced.finalRefinement_refined]
      using parent_fiber_union_critical_lower_explicit
        scalar cfg rho hdelta produced deltaLe rhoLower parent
  have fiberUpper :
      volume (output.windowedFullFiberShading parent).union ≤
        cellCount * output.balanced.cellMass := by
    simpa only [cellCount] using
      output.windowedFullFiberShading_union_volume_upper parent
  have cellCountScale :
      cellCount * ENNReal.ofReal rho.1 ≤ geometry := by
    simpa only [cellCount, geometry] using
      output.selectedParentCells_card_mul_scale_le
        produced.metricCertificate.rho_pos
        (scalar.rho_small hdelta deltaLe rhoUpper) parent
  have scaled :
      ENNReal.ofReal rho.1 * (jacobian⁻¹ * criticalPower) ≤
        geometry * output.balanced.cellMass := by
    calc
      ENNReal.ofReal rho.1 * (jacobian⁻¹ * criticalPower) ≤
          ENNReal.ofReal rho.1 *
            volume (output.windowedFullFiberShading parent).union := by
        gcongr
      _ ≤
          ENNReal.ofReal rho.1 *
            (cellCount * output.balanced.cellMass) := by
        gcongr
      _ =
          (cellCount * ENNReal.ofReal rho.1) *
            output.balanced.cellMass := by ring
      _ ≤ geometry * output.balanced.cellMass := by
        gcongr
  have geometryPos : 0 < geometry := by
    dsimp only [geometry]
    exact ENNReal.mul_pos
      (by norm_num)
      (zero_lt_one.trans_le one_le_deltaTubeVolume_one).ne'
  have geometryTop : geometry ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by norm_num) deltaTubeVolume_one_ne_top
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

/-- Square-root specialization of the raw balanced-cell floor. -/
theorem balanced_cellMass_critical_lower_at_sqrt
    {delta sigma outputLoss : ℝ}
    {routing :
      Prop62V4PureCriticalFloorRoutingData 10 8 2 51 sigma outputLoss}
    (scalar : Prop62V4PureScalarInputs 10 8 2 51 sigma outputLoss routing)
    (cfg :
      PureWZ2C2GrainConfiguration
        sigma routing.numerics.hierarchy.sourceLoss delta)
    (rho : WZ2PaperRequestedScale delta)
    (hdelta : 0 < delta)
    (produced :
      Prop62V4DirectCroppedProducerData
        (workingEta := routing.numerics.hierarchy.stableLoss)
        cfg rho hdelta)
    (deltaLe : delta ≤ scalar.delta₀)
    (rhoLower : Real.rpow delta (1 - outputLoss) ≤ rho.1)
    (rhoUpper : rho.1 ≤ Real.rpow delta outputLoss)
    (hrho : rho.1 = Real.sqrt delta)
    (parent : Fin produced.rich.outputCertificate.coarse.family.card) :
    Kakeya.realRpowENN delta
          (3 / 2 + sigma / 2 +
            routing.numerics.hierarchy.finalStrongLoss) ≤
      produced.rich.outputCertificate.balanced.cellMass := by
  let finalLoss := routing.numerics.hierarchy.finalStrongLoss
  let floorLoss := wz2PaperCriticalFloorLoss outputLoss
  let ratio := delta / rho.1
  let jacobian : ENNReal :=
    ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
      ENNReal.ofReal ((1 / rho.1 : ℝ) ^ 2)
  let geometry : ENNReal := 55296 * Kakeya.deltaTubeVolume 1
  let rawPower : ENNReal :=
    Kakeya.realRpowENN ratio (sigma + floorLoss)
  have rhoPos : 0 < rho.1 := produced.metricCertificate.rho_pos
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
    exact fineUnion_realRpowENN_sqrt hdelta exponent
  have ratioPower (exponent : ℝ) :
      Kakeya.realRpowENN ratio exponent =
        Kakeya.realRpowENN delta (exponent / 2) := by
    rw [ratioEq]
    exact fineUnion_realRpowENN_sqrt hdelta exponent
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
    rw [realRpowENN_negative_inverse ratioPos finalLoss] at inverseBound
    exact inverseBound
  have compressionLeOne :
      ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) ≤ 1 := by
    norm_num
  have jacobianLe :
      jacobian ≤ ENNReal.ofReal ((1 / rho.1 : ℝ) ^ 2) := by
    dsimp only [jacobian]
    calc
      ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
            ENNReal.ofReal ((1 / rho.1 : ℝ) ^ 2) ≤
          1 * ENNReal.ofReal ((1 / rho.1 : ℝ) ^ 2) := by
        gcongr
      _ = _ := one_mul _
  have jacobianInverseLower :
      Kakeya.realRpowENN rho.1 2 ≤ jacobian⁻¹ := by
    have inverseBound := ENNReal.inv_le_inv.mpr jacobianLe
    rw [ofReal_inverse_square_inverse rhoPos] at inverseBound
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
      _ =
          Kakeya.realRpowENN ratio finalLoss *
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
        produced.rich.outputCertificate.balanced.cellMass := by
    simpa only [geometry, jacobian, ratio, rawPower] using
      balanced_cellMass_critical_lower
        scalar cfg rho hdelta produced deltaLe rhoLower rhoUpper parent
  calc
    Kakeya.realRpowENN delta
          (3 / 2 + sigma / 2 +
            routing.numerics.hierarchy.finalStrongLoss) ≤
        Kakeya.realRpowENN ratio finalLoss *
          ENNReal.ofReal rho.1 *
          Kakeya.realRpowENN rho.1 2 * rawPower := by
      simpa only [finalLoss] using powerLower
    _ ≤ geometry⁻¹ * ENNReal.ofReal rho.1 * jacobian⁻¹ * rawPower := by
      gcongr
    _ ≤ produced.rich.outputCertificate.balanced.cellMass := rawLower

/-- The parent-fiber bound weakens to the union of the full final
refinement. -/
theorem fine_union_critical_lower_at_parent
    {delta sigma outputLoss : ℝ}
    {routing :
      Prop62V4PureCriticalFloorRoutingData 10 8 2 51 sigma outputLoss}
    (scalar : Prop62V4PureScalarInputs 10 8 2 51 sigma outputLoss routing)
    (cfg :
      PureWZ2C2GrainConfiguration
        sigma routing.numerics.hierarchy.sourceLoss delta)
    (rho : WZ2PaperRequestedScale delta)
    (hdelta : 0 < delta)
    (produced :
      Prop62V4DirectCroppedProducerData
        (workingEta := routing.numerics.hierarchy.stableLoss)
        cfg rho hdelta)
    (deltaLe : delta ≤ scalar.delta₀)
    (rhoLower : Real.rpow delta (1 - outputLoss) ≤ rho.1)
    (parent : Fin produced.rich.outputCertificate.coarse.family.card) :
    Kakeya.realRpowENN (delta / rho.1)
          (sigma + wz2PaperCriticalFloorLoss outputLoss) ≤
      (ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
          ENNReal.ofReal ((1 / rho.1 : ℝ) ^ 2)) *
        volume produced.finalRefinement.refined.union := by
  let sourceShading :=
    restrictPaperShading
      (wz2PaperFullFiberSubfamily
        produced.finalRefinement.selected.family
        produced.rich.outputCertificate.coarse.family parent)
      produced.finalRefinement.refined
  have sourceUnionSubset :
      sourceShading.union ⊆ produced.finalRefinement.refined.union := by
    rintro point ⟨source, pointMem⟩
    exact
      ⟨(wz2PaperFullFiberSubfamily
          produced.rich.outputCertificate.refinement.selected.family
          produced.rich.outputCertificate.coarse.family parent).embedding source,
        pointMem⟩
  calc
    Kakeya.realRpowENN (delta / rho.1)
          (sigma + wz2PaperCriticalFloorLoss outputLoss) ≤
        (ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
            ENNReal.ofReal ((1 / rho.1 : ℝ) ^ 2)) *
          volume sourceShading.union := by
      exact parent_fiber_union_critical_lower
        scalar cfg rho hdelta produced deltaLe rhoLower parent
    _ ≤
        (ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
            ENNReal.ofReal ((1 / rho.1 : ℝ) ^ 2)) *
          volume produced.finalRefinement.refined.union := by
      gcongr

/-- Parent-free form: the direct producer's terminal coarse family is
nonempty, so one exact complete fiber already supplies the critical lower
bound for the full final fine union. -/
theorem fine_union_critical_lower
    {delta sigma outputLoss : ℝ}
    {routing :
      Prop62V4PureCriticalFloorRoutingData 10 8 2 51 sigma outputLoss}
    (scalar : Prop62V4PureScalarInputs 10 8 2 51 sigma outputLoss routing)
    (cfg :
      PureWZ2C2GrainConfiguration
        sigma routing.numerics.hierarchy.sourceLoss delta)
    (rho : WZ2PaperRequestedScale delta)
    (hdelta : 0 < delta)
    (produced :
      Prop62V4DirectCroppedProducerData
        (workingEta := routing.numerics.hierarchy.stableLoss)
        cfg rho hdelta)
    (deltaLe : delta ≤ scalar.delta₀)
    (rhoLower : Real.rpow delta (1 - outputLoss) ≤ rho.1) :
    Kakeya.realRpowENN (delta / rho.1)
          (sigma + wz2PaperCriticalFloorLoss outputLoss) ≤
      (ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
          ENNReal.ofReal ((1 / rho.1 : ℝ) ^ 2)) *
        volume produced.finalRefinement.refined.union := by
  let parent : Fin produced.rich.outputCertificate.coarse.family.card :=
    produced.rich.outputCertificate.cover.toWZ1PaperTubeCover.parent
      ⟨0, produced.rich.outputCertificate.refined_nonempty⟩
  exact
    fine_union_critical_lower_at_parent
      scalar cfg rho hdelta produced deltaLe rhoLower parent

/-- The same lower bound solved explicitly for the final fine-union volume. -/
theorem fine_union_critical_lower_explicit
    {delta sigma outputLoss : ℝ}
    {routing :
      Prop62V4PureCriticalFloorRoutingData 10 8 2 51 sigma outputLoss}
    (scalar : Prop62V4PureScalarInputs 10 8 2 51 sigma outputLoss routing)
    (cfg :
      PureWZ2C2GrainConfiguration
        sigma routing.numerics.hierarchy.sourceLoss delta)
    (rho : WZ2PaperRequestedScale delta)
    (hdelta : 0 < delta)
    (produced :
      Prop62V4DirectCroppedProducerData
        (workingEta := routing.numerics.hierarchy.stableLoss)
        cfg rho hdelta)
    (deltaLe : delta ≤ scalar.delta₀)
    (rhoLower : Real.rpow delta (1 - outputLoss) ≤ rho.1) :
    (ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
          ENNReal.ofReal ((1 / rho.1 : ℝ) ^ 2))⁻¹ *
        Kakeya.realRpowENN (delta / rho.1)
          (sigma + wz2PaperCriticalFloorLoss outputLoss) ≤
      volume produced.finalRefinement.refined.union := by
  let jacobian : ENNReal :=
    ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
      ENNReal.ofReal ((1 / rho.1 : ℝ) ^ 2)
  have jacobianPos : 0 < jacobian := by
    dsimp only [jacobian]
    exact ENNReal.mul_pos
      (ENNReal.ofReal_pos.mpr (by norm_num)).ne'
      (ENNReal.ofReal_pos.mpr (sq_pos_of_pos <|
        one_div_pos.mpr produced.metricCertificate.rho_pos)).ne'
  have jacobianTop : jacobian ≠ ⊤ := by
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  apply (ENNReal.inv_mul_le_iff jacobianPos.ne' jacobianTop).2
  simpa only [jacobian] using
    fine_union_critical_lower scalar cfg rho hdelta produced deltaLe rhoLower

end Prop62V4DirectCroppedProducerData

end Kakeya.Assouad.Prop62PaperAudit.V4

end
