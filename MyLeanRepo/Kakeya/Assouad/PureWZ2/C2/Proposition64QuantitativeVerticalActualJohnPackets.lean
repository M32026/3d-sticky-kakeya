import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64CenteredActualJohnPacketCWA
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64QuantitativeVerticalJointSelection
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64QuantitativeVerticalCarrierTransport

/-!
# Quantitative vertical actual-John packets

This is the parent-count-free bridge from a joint selected target cover to
Definition 2.12 `rescaledFiber` data.  The joint witness retains, for every
target parent, one complete source actual-John fiber, an explicit injection,
and the weighted cardinality ratio paid by that same packet.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

/-- Same-witness packet data retained by the simultaneous target selection.
It stores no target CWA and no arbitrary-family callback. -/
structure QuantitativeVerticalJointActualJohnPacketReceipt
    {sourceDelta sourceRho targetDelta targetRho : ℝ}
    {sourceConstant : ENNReal}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant)
    (targetFine : Kakeya.Streamlined.TubeFamily targetDelta)
    (targetCoarse : Kakeya.Streamlined.TubeFamily targetRho)
    (targetCover : WZ2PaperPurePartitioningCover targetFine targetCoarse) where
  sourceParent : Fin targetCoarse.card → Fin sourceScale.coarse.card
  sourceIndex :
    ∀ targetParent,
      Fin (wz2PaperOrdinaryFullFiberIndices
        targetFine targetCoarse targetParent).card →
        Fin sourceFine.card
  sourceIndex_injective :
    ∀ targetParent, Function.Injective (sourceIndex targetParent)
  source_mem :
    ∀ targetParent index,
      sourceIndex targetParent index ∈
        wz2PaperOrdinaryFullFiberIndices sourceFine sourceScale.coarse
          (sourceParent targetParent)
  weight : ENNReal
  retentionConstant : ENNReal
  weight_ne_zero : weight ≠ 0
  weight_ne_top : weight ≠ ⊤
  cardinality_retention :
    ∀ targetParent,
      weight *
          ((wz2PaperOrdinaryFullFiberIndices sourceFine sourceScale.coarse
            (sourceParent targetParent)).card : ENNReal) ≤
        retentionConstant *
          ((wz2PaperOrdinaryFullFiberIndices targetFine targetCoarse
            targetParent).card : ENNReal)

/-- Uniform geometric/scalar ledger for all packets at one coordinate.
Unlike the packet receipt, these data are family-free except for the actual
John determinant estimate forced by the two displayed parent tubes. -/
structure QuantitativeVerticalActualJohnTransportReceipt
    {sourceDelta sourceRho targetDelta targetRho : ℝ}
    {sourceConstant : ENNReal}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant)
    (targetFine : Kakeya.Streamlined.TubeFamily targetDelta)
    (targetCoarse : Kakeya.Streamlined.TubeFamily targetRho)
    (targetCover : WZ2PaperPurePartitioningCover targetFine targetCoarse)
    (packet : QuantitativeVerticalJointActualJohnPacketReceipt
      sourceScale targetFine targetCoarse targetCover)
    (physical : Point3 ≃ᵃ[ℝ] Point3)
    (targetRho_pos : 0 < targetRho) where
  lipschitzFactor : ℝ
  lipschitzFactor_nonnegative : 0 ≤ lipschitzFactor
  lipschitz :
    ∀ first second,
      dist (physical first) (physical second) ≤
        lipschitzFactor * dist first second
  factor : ℝ
  factor_one : 1 ≤ factor
  factor_radius :
    lipschitzFactor * (sourceRho + 1 / 2) +
        (targetRho + 1 / 2) ≤ factor * targetDelta
  inverseVolumeConstant : ENNReal
  inverse_volume_bound :
    ∀ targetParent,
      let sourceFiber := Classical.choice
        (sourceScale.rescaledFiber (packet.sourceParent targetParent))
      let targetJohn := WZ2PaperAssouadUnitRescalingData.ofTube
        (targetCoarse.tube targetParent) targetRho_pos
      ENNReal.ofReal
          |LinearMap.det
            ((sourceFiber.normalization.map.symm.trans
              (physical.trans targetJohn.map)).symm.linear :
                Point3 →ₗ[ℝ] Point3)| ≤
        inverseVolumeConstant

/-- Uniform inverse-Jacobian bound for the actual Proposition 6.4 combined
map.  All parent dependence cancels into the two displayed radii. -/
theorem pureWZ2Proposition64ActualJohnCoordinateChange_inverse_det_le
    {sourceRho targetRho : ℝ}
    (hsourceRho : 0 < sourceRho) (htargetRho : 0 < targetRho)
    (sourceParent : Kakeya.DeltaTube sourceRho)
    (targetParent : Kakeya.DeltaTube targetRho)
    (sourceJohn : WZ2PaperAssouadUnitRescalingData sourceParent)
    (targetJohn : WZ2PaperAssouadUnitRescalingData targetParent)
    (g : ℝ → ℝ) (slabCenter anchorHeight halfHeight normalization : ℝ)
    (translation isotropicCenter : Point3) {scale : ℝ}
    (hhalfHeight : 0 < halfHeight)
    (hnormalization : 0 < normalization)
    (hscale : 0 < scale) :
    ENNReal.ofReal
        |LinearMap.det
          ((pureWZ2Proposition64ActualJohnCoordinateChange sourceJohn
            targetJohn g slabCenter anchorHeight halfHeight normalization
            translation isotropicCenter scale hhalfHeight hnormalization
            hscale).symm.linear : Point3 →ₗ[ℝ] Point3)| ≤
      (432 : ENNReal) * Kakeya.realRpowENN targetRho 2 *
        ENNReal.ofReal (1 + 2 * targetRho) *
          ENNReal.ofReal
            (normalization * halfHeight / (scale ^ 3 * sourceRho ^ 2)) := by
  let coordinateChange :=
    pureWZ2Proposition64ActualJohnCoordinateChange sourceJohn targetJohn g
      slabCenter anchorHeight halfHeight normalization translation
      isotropicCenter scale hhalfHeight hnormalization hscale
  let combined := pureWZ2Proposition64CombinedAffineEquiv g slabCenter
    anchorHeight halfHeight normalization translation isotropicCenter scale
      hhalfHeight hnormalization hscale
  have hsourceDetLower :=
    wz2Paper_outerJohn_abs_det_lower sourceParent hsourceRho
  have htargetDetUpper :=
    pureWZ2Proposition64_outerJohn_detENN_le_general
      htargetRho targetParent targetJohn
  have hcombinedDet :
      |LinearMap.det (combined.linear : Point3 →ₗ[ℝ] Point3)| =
        scale ^ 3 / (normalization * halfHeight) := by
    have hraw :
        LinearMap.det (combined.linear : Point3 →ₗ[ℝ] Point3) =
          scale ^ 3 * (1 / (normalization * halfHeight)) := by
      let translated := pureWZ2Proposition64TranslatedAffineEquiv g slabCenter
        anchorHeight halfHeight normalization translation hhalfHeight
          hnormalization
      let isotropic := pureWZ2Proposition64IsotropicAffineEquiv
        isotropicCenter scale hscale
      have hcombinedLinear :
          (combined.linear : Point3 →ₗ[ℝ] Point3) =
            (isotropic.linear : Point3 →ₗ[ℝ] Point3).comp
              (translated.linear : Point3 →ₗ[ℝ] Point3) := by
        rfl
      rw [hcombinedLinear, LinearMap.det_comp]
      change LinearMap.det
          (scale • (LinearMap.id : Point3 →ₗ[ℝ] Point3)) *
            LinearMap.det _ = _
      rw [LinearMap.det_smul, LinearMap.det_id]
      have htranslated :
          LinearMap.det (translated.linear : Point3 →ₗ[ℝ] Point3) =
            1 / (normalization * halfHeight) := by
        dsimp only [translated, pureWZ2Proposition64TranslatedAffineEquiv]
        exact pureWZ2Proposition64Linear_det
          (g anchorHeight) halfHeight normalization
      rw [htranslated]
      norm_num [Module.finrank_fin_fun]
    rw [hraw, abs_of_pos]
    · ring
    · positivity
  have hlinear : coordinateChange.linear =
      sourceJohn.map.symm.linear.trans
        (combined.linear.trans targetJohn.map.linear) := rfl
  have hsourceLinear :
      (sourceJohn.map.symm.linear : Point3 →ₗ[ℝ] Point3) =
        sourceJohn.parent_convex_body.outerJohnEllipsoidMap := rfl
  have htargetLinear :
      (targetJohn.map.linear : Point3 →ₗ[ℝ] Point3) =
        targetJohn.parent_convex_body.outerJohnEllipsoidMap.symm := rfl
  have hcoordinateDet :
      |LinearMap.det (coordinateChange.linear : Point3 →ₗ[ℝ] Point3)| =
        |LinearMap.det
          (sourceJohn.parent_convex_body.outerJohnEllipsoidMap :
            Point3 →ₗ[ℝ] Point3)| *
          (scale ^ 3 / (normalization * halfHeight)) *
            |LinearMap.det
              (targetJohn.parent_convex_body.outerJohnEllipsoidMap :
                Point3 →ₗ[ℝ] Point3)|⁻¹ := by
    rw [hlinear]
    have hcomposition :
        ((sourceJohn.map.symm.linear.trans
          (combined.linear.trans targetJohn.map.linear) :
            Point3 ≃ₗ[ℝ] Point3) : Point3 →ₗ[ℝ] Point3) =
          (targetJohn.map.linear : Point3 →ₗ[ℝ] Point3).comp
            ((combined.linear : Point3 →ₗ[ℝ] Point3).comp
              (sourceJohn.map.symm.linear : Point3 →ₗ[ℝ] Point3)) := by
      ext point
      rfl
    rw [hcomposition, LinearMap.det_comp, LinearMap.det_comp, abs_mul,
      abs_mul, hsourceLinear, htargetLinear, LinearEquiv.det_coe_symm,
      abs_inv, hcombinedDet]
    ring
  have hsourceDetPos : 0 < |LinearMap.det
      (sourceJohn.parent_convex_body.outerJohnEllipsoidMap :
        Point3 →ₗ[ℝ] Point3)| :=
    abs_pos.mpr (LinearEquiv.isUnit_det'
      sourceJohn.parent_convex_body.outerJohnEllipsoidMap).ne_zero
  have htargetDetPos : 0 < |LinearMap.det
      (targetJohn.parent_convex_body.outerJohnEllipsoidMap :
        Point3 →ₗ[ℝ] Point3)| :=
    abs_pos.mpr (LinearEquiv.isUnit_det'
      targetJohn.parent_convex_body.outerJohnEllipsoidMap).ne_zero
  have htargetDetReal :
      |LinearMap.det
        (targetJohn.parent_convex_body.outerJohnEllipsoidMap :
          Point3 →ₗ[ℝ] Point3)| ≤
        108 * targetRho ^ 2 * (1 + 2 * targetRho) := by
    have hnonneg :
        0 ≤ 108 * targetRho ^ 2 * (1 + 2 * targetRho) := by positivity
    rw [show Kakeya.realRpowENN targetRho 2 =
        ENNReal.ofReal (targetRho ^ 2) by
          simp [Kakeya.realRpowENN, Real.rpow_two],
      ← ENNReal.ofReal_ofNat (n := 108),
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 108),
      ← ENNReal.ofReal_mul
        (by positivity : 0 ≤ 108 * targetRho ^ 2)] at htargetDetUpper
    exact (ENNReal.ofReal_le_ofReal_iff hnonneg).mp htargetDetUpper
  have hinverseReal :
      |LinearMap.det
        (coordinateChange.symm.linear : Point3 →ₗ[ℝ] Point3)| ≤
      432 * targetRho ^ 2 * (1 + 2 * targetRho) *
        (normalization * halfHeight / (scale ^ 3 * sourceRho ^ 2)) := by
    have hsymm : coordinateChange.symm.linear =
        coordinateChange.linear.symm := rfl
    rw [hsymm, LinearEquiv.det_coe_symm, abs_inv, hcoordinateDet]
    let sourceDet := |LinearMap.det
      (sourceJohn.parent_convex_body.outerJohnEllipsoidMap :
        Point3 →ₗ[ℝ] Point3)|
    let targetDet := |LinearMap.det
      (targetJohn.parent_convex_body.outerJohnEllipsoidMap :
        Point3 →ₗ[ℝ] Point3)|
    have hdenominatorPos :
        0 < sourceDet * (scale ^ 3 / (normalization * halfHeight)) *
          targetDet⁻¹ := by positivity
    apply (inv_le_iff_one_le_mul₀ hdenominatorPos).2
    dsimp only [sourceDet, targetDet]
    field_simp [hscale.ne', hsourceRho.ne', hhalfHeight.ne',
      hnormalization.ne', hsourceDetPos.ne', htargetDetPos.ne']
    nlinarith [hsourceDetLower, htargetDetReal]
  calc
    _ ≤ ENNReal.ofReal
        (432 * targetRho ^ 2 * (1 + 2 * targetRho) *
          (normalization * halfHeight / (scale ^ 3 * sourceRho ^ 2))) :=
      ENNReal.ofReal_mono hinverseReal
    _ = _ := by
      rw [show Kakeya.realRpowENN targetRho 2 =
        ENNReal.ofReal (targetRho ^ 2) by
          simp [Kakeya.realRpowENN, Real.rpow_two],
        ← ENNReal.ofReal_ofNat (n := 432),
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 432),
        ← ENNReal.ofReal_mul
          (by positivity : 0 ≤ 432 * targetRho ^ 2),
        ← ENNReal.ofReal_mul
          (by positivity :
            0 ≤ 432 * targetRho ^ 2 * (1 + 2 * targetRho))]

/-- Family-free Lipschitz ledger for the Proposition 6.4 physical map. -/
theorem pureWZ2Proposition64CombinedAffineEquiv_dist_le
    (g : ℝ → ℝ) (slabCenter anchorHeight halfHeight normalization : ℝ)
    (translation isotropicCenter : Point3) {scale : ℝ}
    (hanchorSlope : |g anchorHeight| ≤ 8)
    (hhalfHeight : 0 < halfHeight) (hhalfHeightOne : halfHeight ≤ 1)
    (hnormalization : 9 ≤ normalization)
    (hscale : 0 < scale)
    (first second : Point3) :
    dist
        (pureWZ2Proposition64CombinedAffineEquiv g slabCenter anchorHeight
          halfHeight normalization translation isotropicCenter scale
          hhalfHeight (by linarith) hscale first)
        (pureWZ2Proposition64CombinedAffineEquiv g slabCenter anchorHeight
          halfHeight normalization translation isotropicCenter scale
          hhalfHeight (by linarith) hscale second) ≤
      (scale * (11 / halfHeight)) * dist first second := by
  let translated := pureWZ2Proposition64TranslatedAffineEquiv g slabCenter
    anchorHeight halfHeight normalization translation hhalfHeight (by linarith)
  let combined := pureWZ2Proposition64CombinedAffineEquiv g slabCenter
    anchorHeight halfHeight normalization translation isotropicCenter scale
      hhalfHeight (by linarith) hscale
  let isotropic := pureWZ2Proposition64IsotropicAffineEquiv
    isotropicCenter scale hscale
  have hcombinedApply : ∀ point, combined point =
      pureWZ2Proposition64IsotropicMap isotropicCenter scale
        (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
          halfHeight normalization translation point) := by
    intro point
    simp [combined, translated, isotropic, AffineEquiv.trans_apply]
  change dist (combined first) (combined second) ≤ _
  rw [hcombinedApply first, hcombinedApply second]
  rw [pureWZ2Proposition64IsotropicMap_dist isotropicCenter hscale]
  have htranslated :
      dist
          (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
            halfHeight normalization translation first)
          (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
            halfHeight normalization translation second) ≤
        (11 / halfHeight) * dist first second := by
    rw [dist_eq_norm, pureWZ2Proposition64TranslatedMap_sub, ← dist_eq_norm]
    have hmapIdentity :
        pureWZ2Proposition64Map g slabCenter anchorHeight halfHeight
            normalization =
          pureWZ2Proposition64Map (fun _ => g anchorHeight) slabCenter 0
            halfHeight normalization := by
      funext point
      ext coordinate
      fin_cases coordinate <;>
        simp [pureWZ2Proposition64Map, point3]
    rw [hmapIdentity]
    exact pureWZ2Proposition64Map_dist_le hhalfHeight hhalfHeightOne
      (by linarith) hanchorSlope slabCenter first second
  calc
    scale * dist
        (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
          halfHeight normalization translation first)
        (pureWZ2Proposition64TranslatedMap g slabCenter anchorHeight
          halfHeight normalization translation second) ≤
        scale * ((11 / halfHeight) * dist first second) := by gcongr
    _ = _ := by ring

/-- Automatically close the homothetic and inverse-Jacobian ledger for a
packet coordinate under the actual combined Proposition 6.4 map. -/
noncomputable def quantitativeVerticalActualJohnTransport_of_combined
    {sourceDelta sourceRho targetDelta targetRho : ℝ}
    {sourceConstant : ENNReal}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant)
    (targetFine : Kakeya.Streamlined.TubeFamily targetDelta)
    (targetCoarse : Kakeya.Streamlined.TubeFamily targetRho)
    (targetCover : WZ2PaperPurePartitioningCover targetFine targetCoarse)
    (targetDelta_pos : 0 < targetDelta)
    (targetRho_pos : 0 < targetRho)
    (packet : QuantitativeVerticalJointActualJohnPacketReceipt
      sourceScale targetFine targetCoarse targetCover)
    (g : ℝ → ℝ) (slabCenter anchorHeight halfHeight normalization : ℝ)
    (translation isotropicCenter : Point3) {scale : ℝ}
    (hanchorSlope : |g anchorHeight| ≤ 8)
    (hhalfHeight : 0 < halfHeight) (hhalfHeightOne : halfHeight ≤ 1)
    (hnormalization : 9 ≤ normalization)
    (hscale : 0 < scale) :
    QuantitativeVerticalActualJohnTransportReceipt sourceScale targetFine
      targetCoarse targetCover packet
        (pureWZ2Proposition64CombinedAffineEquiv g slabCenter anchorHeight
          halfHeight normalization translation isotropicCenter scale
          hhalfHeight (by linarith) hscale) targetRho_pos := by
  let lipschitzFactor := scale * (11 / halfHeight)
  let factor :=
    1 + (lipschitzFactor * (sourceRho + 1 / 2) +
      (targetRho + 1 / 2)) / targetDelta
  let inverseVolumeConstant :=
    (432 : ENNReal) * Kakeya.realRpowENN targetRho 2 *
      ENNReal.ofReal (1 + 2 * targetRho) *
        ENNReal.ofReal
          (normalization * halfHeight / (scale ^ 3 * sourceRho ^ 2))
  refine {
    lipschitzFactor := lipschitzFactor
    lipschitzFactor_nonnegative := by
      dsimp only [lipschitzFactor]
      positivity
    lipschitz := ?_
    factor := factor
    factor_one := by
      dsimp only [factor]
      have hsum : 0 ≤ lipschitzFactor * (sourceRho + 1 / 2) +
          (targetRho + 1 / 2) := by
        have hsource : 0 ≤ sourceRho := sourceScale.rho_pos.le
        dsimp only [lipschitzFactor]
        positivity
      exact le_add_of_nonneg_right (div_nonneg hsum targetDelta_pos.le)
    factor_radius := by
      dsimp only [factor]
      have hdelta := targetDelta_pos.ne'
      rw [add_mul, div_mul_cancel₀ _ hdelta]
      linarith
    inverseVolumeConstant := inverseVolumeConstant
    inverse_volume_bound := ?_
  }
  · exact pureWZ2Proposition64CombinedAffineEquiv_dist_le g slabCenter
      anchorHeight halfHeight normalization translation isotropicCenter
      hanchorSlope hhalfHeight hhalfHeightOne hnormalization hscale
  · intro targetParent
    let sourceFiber := Classical.choice
      (sourceScale.rescaledFiber (packet.sourceParent targetParent))
    let targetJohn := WZ2PaperAssouadUnitRescalingData.ofTube
      (targetCoarse.tube targetParent) targetRho_pos
    exact pureWZ2Proposition64ActualJohnCoordinateChange_inverse_det_le
      sourceScale.rho_pos targetRho_pos
      (sourceScale.coarse.tube (packet.sourceParent targetParent))
      (targetCoarse.tube targetParent)
      sourceFiber.normalization targetJohn g slabCenter anchorHeight
      halfHeight normalization translation isotropicCenter hhalfHeight
      (by linarith) hscale

/-- The common Definition 2.12 constant produced by the packet transport. -/
def quantitativeVerticalActualJohnPacketConstant
    (sourceConstant weight retentionConstant inverseVolumeConstant : ENNReal)
    (factor : ℝ) : ENNReal :=
  (inverseVolumeConstant *
      ENNReal.ofReal (27 * (2 * factor - 1) ^ 3)) *
    ((weight⁻¹ * retentionConstant) * sourceConstant)

/-- Build a complete Definition 2.12 scale witness without any global coarse
parent count.  Each `rescaledFiber` is transported from its synchronized
source actual-John fiber. -/
noncomputable def quantitativeVertical_scaleCoverData_of_actualJohnPackets
    {sourceDelta sourceRho targetDelta targetRho : ℝ}
    {sourceConstant : ENNReal}
    {sourceFine : Kakeya.Streamlined.TubeFamily sourceDelta}
    (sourceScale :
      WZ2PaperPureScaleCoverData sourceFine sourceRho sourceConstant)
    (targetFine : Kakeya.Streamlined.TubeFamily targetDelta)
    (targetCoarse : Kakeya.Streamlined.TubeFamily targetRho)
    (targetCover : WZ2PaperPurePartitioningCover targetFine targetCoarse)
    (targetDelta_pos : 0 < targetDelta)
    (targetRho_pos : 0 < targetRho)
    (packet : QuantitativeVerticalJointActualJohnPacketReceipt
      sourceScale targetFine targetCoarse targetCover)
    (physical : Point3 ≃ᵃ[ℝ] Point3)
    (transport : QuantitativeVerticalActualJohnTransportReceipt
      sourceScale targetFine targetCoarse targetCover packet physical
        targetRho_pos)
    (targetConstant : ENNReal)
    (packetConstant_le :
      quantitativeVerticalActualJohnPacketConstant sourceConstant
          packet.weight packet.retentionConstant
          transport.inverseVolumeConstant transport.factor ≤
        targetConstant)
    (fullFiberUniform :
      WZ2PaperPureFullFibersAreCUniform targetFine targetCoarse
        targetConstant) :
    WZ2PaperPureScaleCoverData targetFine targetRho targetConstant := by
  refine {
    delta_pos := targetDelta_pos
    rho_pos := targetRho_pos
    coarse := targetCoarse
    cover := targetCover
    full_fiber_uniform := fullFiberUniform
    rescaledFiber := ?_
  }
  intro targetParent
  let sourceParent := packet.sourceParent targetParent
  let sourceFiber := Classical.choice
    (sourceScale.rescaledFiber sourceParent)
  let targetJohn := WZ2PaperAssouadUnitRescalingData.ofTube
    (targetCoarse.tube targetParent) targetRho_pos
  refine ⟨{
    normalization := targetJohn
    convex_wolff := ?_
  }⟩
  have hraw := pureWZ2Proposition64_parentCenteredActualJohnPacket_cwa
    sourceParent targetParent sourceFiber targetJohn
    (packet.sourceIndex targetParent)
    (packet.sourceIndex_injective targetParent)
    (packet.source_mem targetParent)
    packet.weight packet.retentionConstant packet.weight_ne_zero
    packet.weight_ne_top (packet.cardinality_retention targetParent)
    physical transport.lipschitzFactor_nonnegative transport.lipschitz
    sourceScale.rho_pos.le targetDelta_pos targetRho_pos.le
    transport.factor_one transport.factor_radius
  intro convexSet hconvex
  have hpacketConstantLe := packetConstant_le
  unfold quantitativeVerticalActualJohnPacketConstant at hpacketConstantLe
  calc
    (wz2PaperPureUnitRescaledFullFiberBodyFamily
        (fine := targetFine) (coarse := targetCoarse)
        targetParent targetJohn).containedCount convexSet ≤
      (ENNReal.ofReal
          |LinearMap.det
            ((sourceFiber.normalization.map.symm.trans
              (physical.trans targetJohn.map)).symm.linear :
                Point3 →ₗ[ℝ] Point3)| *
        ENNReal.ofReal (27 * (2 * transport.factor - 1) ^ 3)) *
          ((packet.weight⁻¹ * packet.retentionConstant) * sourceConstant) *
            volume convexSet *
              (wz2PaperPureUnitRescaledFullFiberBodyFamily
                (fine := targetFine) (coarse := targetCoarse)
                targetParent targetJohn).enncard := hraw convexSet hconvex
    _ ≤
      (transport.inverseVolumeConstant *
        ENNReal.ofReal (27 * (2 * transport.factor - 1) ^ 3)) *
          ((packet.weight⁻¹ * packet.retentionConstant) * sourceConstant) *
            volume convexSet *
              (wz2PaperPureUnitRescaledFullFiberBodyFamily
                (fine := targetFine) (coarse := targetCoarse)
                targetParent targetJohn).enncard := by
      gcongr
      exact transport.inverse_volume_bound targetParent
    _ ≤ targetConstant * volume convexSet *
          (wz2PaperPureUnitRescaledFullFiberBodyFamily
            (fine := targetFine) (coarse := targetCoarse)
            targetParent targetJohn).enncard := by
      gcongr

namespace PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData

variable
    {sigma workLoss sourceDelta targetDelta₀ outputLoss : ℝ}
    {hsourceSmall : sourceDelta ≤
      pureWZ2Proposition64Lemma35SourceCeiling targetDelta₀}
    (quantitativeOutput : PureWZ2QuantitativeNormalizedHierarchyOutput
      sigma workLoss sourceDelta)
    (geometry : PureWZ2Proposition64Lemma35GeometricData
      quantitativeOutput.normalized hsourceSmall)
    (frostman : SelectedSourceFrostmanReceipt geometry)
    (floor : PureWZ2CroppedCriticalFloorSelectionData
      sigma outputLoss outputLoss)

private noncomputable abbrev initialED :=
  quantitativeVerticalPaperED quantitativeOutput geometry frostman

/-- Source synchronization attached to raw target-parent geometry before
selection.  It is transported through the occupied-parent embedding; no
source parent is chosen after selection. -/
structure QuantitativeVerticalSourceSynchronizedRawParentReceipt
    (raw : QuantitativeVerticalRawColoredParentReceipt
      quantitativeOutput geometry frostman floor) where
  sourceCoordinate :
    Fin (quantitativeVerticalRequestedScaleSchedule
      quantitativeOutput geometry floor).levelCount →
      Fin (quantitativeVerticalRequestedScaleSchedule
        quantitativeOutput geometry floor).levelCount
  sourceParent :
    ∀ coordinate,
      Fin (raw.coarse coordinate).card →
        Fin (quantitativeVerticalMatchedSourceNearby
          quantitativeOutput geometry floor
            (sourceCoordinate coordinate)).scaleData.coarse.card
  source_mem :
    ∀ coordinate source,
      geometry.finalSourceEmbedding
          (initialED quantitativeOutput geometry frostman) source ∈
        wz2PaperOrdinaryFullFiberIndices
          quantitativeOutput.normalized.source.family
          (quantitativeVerticalMatchedSourceNearby
            quantitativeOutput geometry floor
              (sourceCoordinate coordinate)).scaleData.coarse
          (sourceParent coordinate (raw.parent coordinate source))
  target_scale_eq :
    ∀ coordinate,
      raw.actualScale coordinate =
        pureWZ2Proposition64RepresentativeTransportScale
          (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
          pureWZ2Proposition64Lemma35Scale
          (quantitativeVerticalMatchedSourceNearby
            quantitativeOutput geometry floor
              (sourceCoordinate coordinate)).rho

/-- Canonical injection from one joint-selected target tube back to the
original quantitative source family. -/
noncomputable def quantitativeVerticalJointSourceIndex
    (joint : QuantitativeVerticalJointFiniteSelectionReceipt
      quantitativeOutput geometry frostman floor) :
    Fin joint.selected.family.card ↪
      Fin quantitativeOutput.normalized.source.family.card :=
  {
    toFun := fun index =>
      geometry.finalSourceEmbedding
        (initialED quantitativeOutput geometry frostman)
        (joint.selected.embedding index)
    inj' := fun _ _ equality =>
      joint.selected.embedding.injective
        ((geometry.finalSourceEmbedding
          (initialED quantitativeOutput geometry frostman)).injective equality)
  }

/-- Same-witness packet output required from simultaneous selection: each
target full fiber is monochromatic for one matched source parent and retains
a weighted fraction of that complete source fiber. -/
structure QuantitativeVerticalJointPacketRetentionReceipt
    (joint : QuantitativeVerticalJointFiniteSelectionReceipt
      quantitativeOutput geometry frostman floor) where
  sourceCoordinate :
    Fin joint.coordinateCount →
      Fin (quantitativeVerticalRequestedScaleSchedule
        quantitativeOutput geometry floor).levelCount
  sourceParent :
    ∀ coordinate : Fin joint.coordinateCount,
      Fin (joint.coarse coordinate).card →
        Fin (quantitativeVerticalMatchedSourceNearby
          quantitativeOutput geometry floor
            (sourceCoordinate coordinate)).scaleData.coarse.card
  source_mem :
    ∀ coordinate targetParent index,
      quantitativeVerticalJointSourceIndex
          quantitativeOutput geometry frostman floor joint
          ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent) index).1 ∈
        wz2PaperOrdinaryFullFiberIndices
          quantitativeOutput.normalized.source.family
          (quantitativeVerticalMatchedSourceNearby
            quantitativeOutput geometry floor
              (sourceCoordinate coordinate)).scaleData.coarse
          (sourceParent coordinate targetParent)
  weight : ENNReal
  retentionConstant : ENNReal
  weight_ne_zero : weight ≠ 0
  weight_ne_top : weight ≠ ⊤
  cardinality_retention :
    ∀ coordinate targetParent,
      weight *
          ((wz2PaperOrdinaryFullFiberIndices
            quantitativeOutput.normalized.source.family
            (quantitativeVerticalMatchedSourceNearby
              quantitativeOutput geometry floor
                (sourceCoordinate coordinate)).scaleData.coarse
            (sourceParent coordinate targetParent)).card : ENNReal) ≤
        retentionConstant *
          ((wz2PaperOrdinaryFullFiberIndices joint.selected.family
            (joint.coarse coordinate) targetParent).card : ENNReal)

/-- Minimal selector provenance needed for packet CWA.  Weighted
cardinality is not a field: it is derived uniformly below from occupancy and
the global number of source tubes. -/
structure QuantitativeVerticalJointSourceParentReceipt
    (joint : QuantitativeVerticalJointFiniteSelectionReceipt
      quantitativeOutput geometry frostman floor) where
  sourceCoordinate :
    Fin joint.coordinateCount →
      Fin (quantitativeVerticalRequestedScaleSchedule
        quantitativeOutput geometry floor).levelCount
  sourceParent :
    ∀ coordinate : Fin joint.coordinateCount,
      Fin (joint.coarse coordinate).card →
        Fin (quantitativeVerticalMatchedSourceNearby
          quantitativeOutput geometry floor
            (sourceCoordinate coordinate)).scaleData.coarse.card
  source_mem :
    ∀ coordinate targetParent index,
      quantitativeVerticalJointSourceIndex
          quantitativeOutput geometry frostman floor joint
          ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent) index).1 ∈
        wz2PaperOrdinaryFullFiberIndices
          quantitativeOutput.normalized.source.family
          (quantitativeVerticalMatchedSourceNearby
            quantitativeOutput geometry floor
              (sourceCoordinate coordinate)).scaleData.coarse
          (sourceParent coordinate targetParent)
  target_occupied :
    ∀ coordinate targetParent,
      0 < (wz2PaperOrdinaryFullFiberIndices joint.selected.family
        (joint.coarse coordinate) targetParent).card
  target_scale_eq :
    ∀ coordinate,
      joint.actualScale coordinate =
        pureWZ2Proposition64RepresentativeTransportScale
          (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
          pureWZ2Proposition64Lemma35Scale
          (quantitativeVerticalMatchedSourceNearby
            quantitativeOutput geometry floor
              (sourceCoordinate coordinate)).rho

namespace QuantitativeVerticalJointSourceParentReceipt

/-- Transport raw source-parent synchronization along the exact occupied
parent embedding produced by the simultaneous selector. -/
noncomputable def ofSelectionWithParentProvenance
    (raw : QuantitativeVerticalRawColoredParentReceipt
      quantitativeOutput geometry frostman floor)
    (sync : QuantitativeVerticalSourceSynchronizedRawParentReceipt
      quantitativeOutput geometry frostman floor raw)
    (selection :
      QuantitativeVerticalRawColoredParentReceipt.SelectionWithParentProvenance
        quantitativeOutput geometry frostman floor raw) :
    QuantitativeVerticalJointSourceParentReceipt
      quantitativeOutput geometry frostman floor selection.joint where
  sourceCoordinate := fun coordinate =>
    sync.sourceCoordinate
      (Fin.cast selection.coordinateCount_eq coordinate)
  sourceParent := fun coordinate targetParent =>
    sync.sourceParent
      (Fin.cast selection.coordinateCount_eq coordinate)
      (selection.ambientParent coordinate targetParent)
  source_mem := by
    intro coordinate targetParent index
    let targetIndex :=
      ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent) index).1
    have hcoverParent :
        (selection.joint.cover coordinate).parent targetIndex =
          targetParent := by
      apply (selection.joint.cover coordinate).fullFiber_parent_unique
        (selection.joint.actualScale_pos coordinate).le
      · exact (selection.joint.cover coordinate).parent_mem_fullFiber targetIndex
      · exact ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent) index).2
    have hrawParent :
        raw.parent (Fin.cast selection.coordinateCount_eq coordinate)
            (selection.joint.selected.embedding targetIndex) =
          selection.ambientParent coordinate targetParent := by
      rw [← hcoverParent]
      exact (selection.parent_eq coordinate targetIndex).symm
    have hmem := sync.source_mem
      (Fin.cast selection.coordinateCount_eq coordinate)
      (selection.joint.selected.embedding targetIndex)
    change
      geometry.finalSourceEmbedding
          (initialED quantitativeOutput geometry frostman)
          (selection.joint.selected.embedding targetIndex) ∈
        wz2PaperOrdinaryFullFiberIndices
          quantitativeOutput.normalized.source.family
          (quantitativeVerticalMatchedSourceNearby
            quantitativeOutput geometry floor
              (sync.sourceCoordinate
                (Fin.cast selection.coordinateCount_eq coordinate))).scaleData.coarse
          (sync.sourceParent
            (Fin.cast selection.coordinateCount_eq coordinate)
            (selection.ambientParent coordinate targetParent))
    rw [← hrawParent]
    exact hmem
  target_occupied := by
    intro coordinate targetParent
    rcases selection.parent_occupied coordinate targetParent with
      ⟨source, hsource⟩
    have hparent :
        (selection.joint.cover coordinate).parent source = targetParent := by
      apply (selection.ambientParent coordinate).injective
      rw [selection.parent_eq coordinate source]
      exact hsource
    apply Finset.card_pos.mpr
    refine ⟨source, ?_⟩
    rw [(selection.joint.cover coordinate).mem_fullFiber_iff_parent_eq
      (selection.joint.actualScale_pos coordinate).le]
    exact hparent
  target_scale_eq := by
    intro coordinate
    rw [selection.actualScale_eq coordinate]
    exact sync.target_scale_eq
      (Fin.cast selection.coordinateCount_eq coordinate)

/-- Occupancy gives a uniform packet ratio with no extra tube selection:
`#(source fiber) ≤ #sourceFamily · #(occupied target fiber)`. -/
noncomputable def toPacketRetention
    (joint : QuantitativeVerticalJointFiniteSelectionReceipt
      quantitativeOutput geometry frostman floor)
    (receipt : QuantitativeVerticalJointSourceParentReceipt
      quantitativeOutput geometry frostman floor joint) :
    QuantitativeVerticalJointPacketRetentionReceipt
      quantitativeOutput geometry frostman floor joint where
  sourceCoordinate := receipt.sourceCoordinate
  sourceParent := receipt.sourceParent
  source_mem := receipt.source_mem
  weight := 1
  retentionConstant :=
    quantitativeOutput.normalized.source.family.enncard
  weight_ne_zero := one_ne_zero
  weight_ne_top := ENNReal.one_ne_top
  cardinality_retention := by
    intro coordinate targetParent
    let sourceFiber :=
      wz2PaperOrdinaryFullFiberIndices
        quantitativeOutput.normalized.source.family
        (quantitativeVerticalMatchedSourceNearby
          quantitativeOutput geometry floor
            (receipt.sourceCoordinate coordinate)).scaleData.coarse
        (receipt.sourceParent coordinate targetParent)
    let targetFiber :=
      wz2PaperOrdinaryFullFiberIndices joint.selected.family
        (joint.coarse coordinate) targetParent
    have hsource :
        sourceFiber.card ≤
          quantitativeOutput.normalized.source.family.card := by
      simpa using Finset.card_le_univ sourceFiber
    have htarget : 1 ≤ targetFiber.card :=
      receipt.target_occupied coordinate targetParent
    have hnat :
        sourceFiber.card ≤
          quantitativeOutput.normalized.source.family.card *
            targetFiber.card := by
      exact hsource.trans
        (Nat.le_mul_of_pos_right _ htarget)
    have henn :
        (sourceFiber.card : ENNReal) ≤
          (quantitativeOutput.normalized.source.family.card : ENNReal) *
            (targetFiber.card : ENNReal) := by
      exact_mod_cast hnat
    simpa [sourceFiber, targetFiber,
      Kakeya.Streamlined.TubeFamily.enncard] using henn

end QuantitativeVerticalJointSourceParentReceipt

namespace QuantitativeVerticalJointPacketRetentionReceipt

/-- Project one coordinate to the generic actual-John packet interface.
Injectivity comes from the exact source and selected-family embeddings. -/
noncomputable def packet
    (joint : QuantitativeVerticalJointFiniteSelectionReceipt
      quantitativeOutput geometry frostman floor)
    (receipt : QuantitativeVerticalJointPacketRetentionReceipt
      quantitativeOutput geometry frostman floor joint)
    (coordinate : Fin joint.coordinateCount) :
    QuantitativeVerticalJointActualJohnPacketReceipt
      (quantitativeVerticalMatchedSourceNearby
        quantitativeOutput geometry floor
          (receipt.sourceCoordinate coordinate)).scaleData
      joint.selected.family (joint.coarse coordinate)
      (joint.cover coordinate) where
  sourceParent := receipt.sourceParent coordinate
  sourceIndex := fun targetParent index =>
    quantitativeVerticalJointSourceIndex
      quantitativeOutput geometry frostman floor joint
      ((wz2PaperOrdinaryFullFiberIndexEquiv targetParent) index).1
  sourceIndex_injective := by
    intro targetParent first second equality
    apply (wz2PaperOrdinaryFullFiberIndexEquiv targetParent).injective
    apply Subtype.ext
    exact (quantitativeVerticalJointSourceIndex
      quantitativeOutput geometry frostman floor joint).injective equality
  source_mem := receipt.source_mem coordinate
  weight := receipt.weight
  retentionConstant := receipt.retentionConstant
  weight_ne_zero := receipt.weight_ne_zero
  weight_ne_top := receipt.weight_ne_top
  cardinality_retention := receipt.cardinality_retention coordinate

end QuantitativeVerticalJointPacketRetentionReceipt

namespace QuantitativeVerticalJointFiniteSelectionReceipt

/-- The actual common Proposition 6.4 physical map retained by the geometric
prefix. -/
noncomputable def actualJohnPhysical :
    Point3 ≃ᵃ[ℝ] Point3 :=
  pureWZ2Proposition64CombinedAffineEquiv
    quantitativeOutput.normalized.prepared.restrictedRaw.slope
    quantitativeOutput.normalized.prepared.slab.center
    quantitativeOutput.normalized.prepared.slab.anchorHeight
    quantitativeOutput.normalized.prepared.slab.halfHeight
    quantitativeOutput.normalized.prepared.normalization
    geometry.common.translation geometry.cleanup.popular.center
    pureWZ2Proposition64Lemma35Scale
    quantitativeOutput.normalized.prepared.slab.halfHeight_pos
    (by linarith [quantitativeOutput.normalized.normalization_nine])
    (by linarith [geometry.scales.scale_one])

/-- Deterministic packet selected at one coordinate from source-parent
provenance. -/
noncomputable def actualJohnPacket
    (joint : QuantitativeVerticalJointFiniteSelectionReceipt
      quantitativeOutput geometry frostman floor)
    (parents : QuantitativeVerticalJointSourceParentReceipt
      quantitativeOutput geometry frostman floor joint)
    (coordinate : Fin joint.coordinateCount) :=
  ((parents.toPacketRetention quantitativeOutput geometry frostman floor joint
    ).packet quantitativeOutput geometry frostman floor joint coordinate)

/-- Geometry automatically supplies the Lipschitz, homothetic, and
inverse-volume ledger at every selected coordinate. -/
noncomputable def actualJohnTransport
    (joint : QuantitativeVerticalJointFiniteSelectionReceipt
      quantitativeOutput geometry frostman floor)
    (parents : QuantitativeVerticalJointSourceParentReceipt
      quantitativeOutput geometry frostman floor joint)
    (coordinate : Fin joint.coordinateCount) :=
  quantitativeVerticalActualJohnTransport_of_combined
    (quantitativeVerticalMatchedSourceNearby
      quantitativeOutput geometry floor
        (parents.sourceCoordinate coordinate)).scaleData
    joint.selected.family (joint.coarse coordinate) (joint.cover coordinate)
    geometry.scales.finalDelta_pos (joint.actualScale_pos coordinate)
    (joint.actualJohnPacket quantitativeOutput geometry frostman floor
      parents coordinate)
    quantitativeOutput.normalized.prepared.restrictedRaw.slope
    quantitativeOutput.normalized.prepared.slab.center
    quantitativeOutput.normalized.prepared.slab.anchorHeight
    quantitativeOutput.normalized.prepared.slab.halfHeight
    quantitativeOutput.normalized.prepared.normalization
    geometry.common.translation geometry.cleanup.popular.center
    quantitativeOutput.normalized.prepared.normalized.anchor_value_bound
    quantitativeOutput.normalized.prepared.slab.halfHeight_pos
    (by
      show quantitativeOutput.normalized.prepared.slab.halfHeight ≤ 1
      linarith [quantitativeOutput.normalized.halfHeight_small])
    quantitativeOutput.normalized.normalization_nine
    (by
      show 0 < pureWZ2Proposition64Lemma35Scale
      linarith [geometry.scales.scale_one])

/-- The remaining pre-run scalar obligation.  It is family-free except for
the explicit source-family cardinality already charged by packet retention;
it stores no CWA and no parent-count estimate. -/
structure ActualJohnScheduleAbsorptionReceipt
    (joint : QuantitativeVerticalJointFiniteSelectionReceipt
      quantitativeOutput geometry frostman floor)
    (parents : QuantitativeVerticalJointSourceParentReceipt
      quantitativeOutput geometry frostman floor joint) : Prop where
  scaleAbsorption :
    ∀ coordinate,
      let packet := joint.actualJohnPacket quantitativeOutput
        geometry frostman floor parents coordinate
      let transport := joint.actualJohnTransport quantitativeOutput
        geometry frostman floor parents coordinate
      max (joint.degreeConstant coordinate)
        (quantitativeVerticalActualJohnPacketConstant
          (Kakeya.realRpowENN sourceDelta
            (-quantitativeOutput.normalized.inputLoss))
          packet.weight packet.retentionConstant
          transport.inverseVolumeConstant transport.factor) ≤
        Kakeya.realRpowENN
          (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
          (-floor.structuralLoss)

/-- Assemble the exact nearby-scale CWA on the same selected family using
only actual-John packets; no global target-parent count is used. -/
theorem actualJohnNearby
    (joint : QuantitativeVerticalJointFiniteSelectionReceipt
      quantitativeOutput geometry frostman floor)
    (parents : QuantitativeVerticalJointSourceParentReceipt
      quantitativeOutput geometry frostman floor joint)
    (absorption : ActualJohnScheduleAbsorptionReceipt
      quantitativeOutput geometry frostman floor joint parents) :
    WZ2PaperPureCWAAtNearbyScales joint.finalED.subfamily.family
      (Kakeya.realRpowENN
        (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
        (-floor.structuralLoss)) := by
  change WZ2PaperPureCWAAtNearbyScales joint.selected.family _
  let outputConstant := Kakeya.realRpowENN
    (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
    (-floor.structuralLoss)
  have outputOne : 1 ≤ outputConstant := by
    dsimp only [outputConstant]
    rw [Kakeya.realRpowENN, ENNReal.one_le_ofReal]
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos
      geometry.scales.finalDelta_pos
      (geometry.scales.finalDelta_le_one_ninety_six.trans (by norm_num))
      (by linarith [floor.structuralLoss_pos])
  have outputTop : outputConstant ≠ ⊤ := by
    simp [outputConstant, Kakeya.realRpowENN]
  apply pureWZ2_nearby_from_finite_witnesses
    geometry.scales.finalDelta_pos outputOne outputTop
    (by
      change WZ2PaperOrdinaryIsEssentiallyDistinct
        joint.finalED.subfamily.family
      exact joint.finalED.essentially_distinct)
    joint.coordinateCount joint.coordinateCount_pos
    (fun coordinate => ⟨joint.actualScale coordinate, ?_⟩)
    joint.rounding
  let sourceScale :=
    (quantitativeVerticalMatchedSourceNearby
      quantitativeOutput geometry floor
        (parents.sourceCoordinate coordinate)).scaleData
  let packet := joint.actualJohnPacket quantitativeOutput geometry frostman
    floor parents coordinate
  let transport := joint.actualJohnTransport quantitativeOutput geometry
    frostman floor parents coordinate
  have habsorb := absorption.scaleAbsorption coordinate
  have hdegree :
      joint.degreeConstant coordinate ≤ outputConstant :=
    (le_max_left _ _).trans habsorb
  have hpacket :
      quantitativeVerticalActualJohnPacketConstant
          (Kakeya.realRpowENN sourceDelta
            (-quantitativeOutput.normalized.inputLoss))
          packet.weight packet.retentionConstant
          transport.inverseVolumeConstant transport.factor ≤
        outputConstant :=
    (le_max_right _ _).trans habsorb
  exact quantitativeVertical_scaleCoverData_of_actualJohnPackets
    sourceScale joint.selected.family (joint.coarse coordinate)
    (joint.cover coordinate) geometry.scales.finalDelta_pos
    (joint.actualScale_pos coordinate) packet
    (actualJohnPhysical quantitativeOutput geometry)
    transport outputConstant hpacket
    (fun first second =>
      (joint.fullFiberUniform coordinate first second).trans (by gcongr))

/-- Final vertical assembly through the actual-John nearby channel. -/
theorem verticalRediscretizationActualJohn
    (joint : QuantitativeVerticalJointFiniteSelectionReceipt
      quantitativeOutput geometry frostman floor)
    (parents : QuantitativeVerticalJointSourceParentReceipt
      quantitativeOutput geometry frostman floor joint)
    (absorption : ActualJohnScheduleAbsorptionReceipt
      quantitativeOutput geometry frostman floor joint parents)
    (scalars : ScalarReceipt
      quantitativeOutput geometry frostman floor joint) :
    Nonempty (PureWZ2VerticalRediscretizationData
      quantitativeOutput.normalized.prepared.normalized
      (pureWZ2Proposition64Lemma35FinalDelta sourceDelta) outputLoss) := by
  let ed := joint.finalED
  apply geometry.assembleVerticalRediscretizationOfCriticalFloor
    quantitativeOutput ed floor
  exact {
    nearby := joint.actualJohnNearby quantitativeOutput geometry frostman floor
      parents absorption
    finalDelta_le_floor := scalars.finalDelta_le_floor
    ed_loss_ne_top := joint.finalLoss_ne_top
    density_absorption := scalars.density_absorption
    cwa_absorption := scalars.cwa_absorption
    volume_absorption := scalars.volume_absorption
    local_constant_absorption := scalars.local_constant_absorption
    global_constant_absorption := scalars.global_constant_absorption
  }

end QuantitativeVerticalJointFiniteSelectionReceipt

end PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData

end Kakeya.Assouad

end
