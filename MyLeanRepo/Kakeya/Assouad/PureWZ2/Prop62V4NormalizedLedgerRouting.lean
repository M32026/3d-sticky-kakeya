import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4NormalizedFixedGrid
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4PureRefinementComposition
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4ThreeLossRouting

/-!
# Proposition 6.2 V4 normalized-ledger routing

The complete normalization source loss and the normalized cropped loss are
different parameters.  This module routes the cropped volume and density
ledger at the latter loss, which is exactly the final hierarchy source loss.
It stops before the universal and Node 3 assemblies.
-/

noncomputable section

namespace Kakeya.Assouad.Prop62PaperAudit.V4

open Kakeya.Assouad
open MeasureTheory

private theorem prop62V4_oneLogFraction_le_half
    {delta : ℝ}
    (deltaPos : 0 < delta)
    (deltaSmall : delta ≤ Real.exp (-2)) :
    wz1PaperRefinementFraction delta 1 ≤ (1 / 2 : ENNReal) := by
  have expNegPos : 0 < Real.exp (-2) := Real.exp_pos _
  have inverse : Real.exp 2 ≤ delta⁻¹ := by
    have bound := (inv_le_inv₀ expNegPos deltaPos).mpr deltaSmall
    simpa [Real.exp_neg] using bound
  have logBound : 2 ≤ Real.log delta⁻¹ := by
    rw [← Real.log_exp 2]
    exact Real.log_le_log (Real.exp_pos 2) inverse
  unfold wz1PaperRefinementFraction
  simp only [pow_one, one_div]
  rw [ENNReal.inv_le_inv]
  have two : (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) := by
    norm_num
  rw [two]
  simpa [one_div] using ENNReal.ofReal_mono logBound

namespace Prop62V4ThreeLossRoutingData

variable
    {polylogExponent cwaPower packetDensityExponent cwaLossExponent : ℕ}
    {sigma outputLoss delta : ℝ}
    {routing :
      Prop62V4PureCriticalFloorRoutingData
        polylogExponent cwaPower packetDensityExponent cwaLossExponent
        sigma outputLoss}
    (three : Prop62V4ThreeLossRoutingData routing)
    {source :
      PureWZ2ExtremalConfiguration sigma three.sourceLoss delta}
    {normalizationExponent : ℕ}
    (normalized :
      PureWZ2CroppedCriticalNormalizationData
        (outputLoss := three.normalizationLoss)
        source normalizationExponent)

/--
The original extremal source weakened to the hierarchy source loss.
The family and shading are definitionally unchanged.
-/
noncomputable def hierarchySource :
    PureWZ2ExtremalConfiguration
      sigma routing.numerics.hierarchy.sourceLoss delta where
  family := source.family
  shading := source.shading
  extremal :=
    source.extremal.mono_loss three.sourceLoss_le_hierarchy

/--
A same-geometry normalization view whose outer source index is the hierarchy
source loss.  The output is weakened to the stable loss only to satisfy the
normalization API's required half-loss separation.
-/
noncomputable def hierarchySourceNormalization :
    PureWZ2CroppedCriticalNormalizationData
      (outputLoss := routing.numerics.hierarchy.stableLoss)
      (hierarchySource
        (delta := delta) (source := source) three)
      normalizationExponent where
  input_loss_le_half := by
    rw [routing.numerics.hierarchy.sourceLoss_eq,
      routing.numerics.hierarchy.stableLoss_eq]
    dsimp only [wz2PaperFinalSourceLoss, wz2PaperFinalStableLoss]
    exact le_of_eq (by ring)
  selected := normalized.selected
  selected_nonempty := normalized.selected_nonempty
  ordinaryRefined := normalized.ordinaryRefined
  ordinary_subshading := normalized.ordinary_subshading
  retained_mass := normalized.retained_mass
  frame := normalized.frame
  croppedFamily := normalized.croppedFamily
  indexEquiv := normalized.indexEquiv
  ordinary_carrier_image_eq := normalized.ordinary_carrier_image_eq
  ordinary_axial_window := normalized.ordinary_axial_window
  ordinary_per_tube := by
    intro index
    have densityPower :
        Kakeya.realRpowENN delta
            routing.numerics.hierarchy.sourceLoss ≤
          Kakeya.realRpowENN delta three.sourceLoss :=
      Kakeya.Assouad.realRpowENN_antitone
        normalized.final_extremal.delta_pos
        normalized.final_extremal.delta_le_one
        three.sourceLoss_le_hierarchy
    calc
      (Kakeya.realRpowENN delta
            routing.numerics.hierarchy.sourceLoss / 2) *
            volume (normalized.selected.family.tube index).carrier ≤
          (Kakeya.realRpowENN delta three.sourceLoss / 2) *
            volume (normalized.selected.family.tube index).carrier := by
        gcongr
      _ ≤ volume (normalized.ordinaryRefined.carrier index) :=
        normalized.ordinary_per_tube index
  croppedRefined := normalized.croppedRefined
  cropped_carrier_eq_dense_cubicalization :=
    normalized.cropped_carrier_eq_dense_cubicalization
  cropped_cubical := normalized.cropped_cubical
  line_class := normalized.line_class
  cropped_top_level_cwa := by
    intro convexSet convex
    have normalizationToStable :
        three.normalizationLoss ≤
          routing.numerics.hierarchy.stableLoss := by
      rw [three.normalizationLoss_eq]
      exact routing.numerics.hierarchy.source_stable.le
    have constantLe :
        Kakeya.realRpowENN delta (-three.normalizationLoss) ≤
          Kakeya.realRpowENN delta
            (-routing.numerics.hierarchy.stableLoss) :=
      Kakeya.Assouad.realRpowENN_antitone
        normalized.final_extremal.delta_pos
        normalized.final_extremal.delta_le_one
        (by linarith)
    exact
      (normalized.cropped_top_level_cwa convexSet convex).trans <| by
        gcongr
  final_extremal :=
    normalized.final_extremal.mono_loss <| by
      rw [three.normalizationLoss_eq]
      exact routing.numerics.hierarchy.source_stable.le
  ordinary_cell_containment := normalized.ordinary_cell_containment
  ordinary_bounded_base := normalized.ordinary_bounded_base

@[simp] theorem hierarchySourceNormalization_croppedFamily :
    (Prop62V4ThreeLossRoutingData.hierarchySourceNormalization
      three normalized).croppedFamily =
      normalized.croppedFamily :=
  rfl

@[simp] theorem hierarchySourceNormalization_croppedRefined :
    (Prop62V4ThreeLossRoutingData.hierarchySourceNormalization
      three normalized).croppedRefined =
      normalized.croppedRefined :=
  rfl

/--
The existing `Prop62V4NormalizedSourceLedger`, instantiated at exactly
`routing.numerics.hierarchy.sourceLoss`.
-/
noncomputable def normalizedSourceLedger :
    Prop62V4RichCertificateCompanionData.Prop62V4NormalizedSourceLedger
      (normalized :=
        Prop62V4ThreeLossRoutingData.hierarchySourceNormalization
          three normalized) where
  source_volume_upper := by
    change
      volume normalized.croppedRefined.union ≤
        Kakeya.realRpowENN delta
          (sigma - routing.numerics.hierarchy.sourceLoss)
    have powerEq :
        Kakeya.realRpowENN delta
            (sigma - routing.numerics.hierarchy.sourceLoss) =
          Kakeya.realRpowENN delta
            (sigma - three.normalizationLoss) :=
      congrArg (Kakeya.realRpowENN delta) <| by
        rw [three.normalizationLoss_eq]
    rw [powerEq]
    exact normalized.final_extremal.volume_upper

end Prop62V4ThreeLossRoutingData

/--
The two normalized-source facts at the final hierarchy source loss.

The outer source of `normalized` remains at `three.sourceLoss`; only the
cropped ledger is routed through `three.normalizationLoss`, which equals
`routing.numerics.hierarchy.sourceLoss`.
-/
structure Prop62V4NormalizedLedgerRoutingData
    {polylogExponent cwaPower packetDensityExponent cwaLossExponent : ℕ}
    {sigma outputLoss delta : ℝ}
    {routing :
      Prop62V4PureCriticalFloorRoutingData
        polylogExponent cwaPower packetDensityExponent cwaLossExponent
        sigma outputLoss}
    (three : Prop62V4ThreeLossRoutingData routing)
    {source :
      PureWZ2ExtremalConfiguration sigma three.sourceLoss delta}
    {normalizationExponent : ℕ}
    (normalized :
      PureWZ2CroppedCriticalNormalizationData
        (outputLoss := three.normalizationLoss)
        source normalizationExponent) : Prop where
  source_volume_upper :
    volume normalized.croppedRefined.union ≤
      Kakeya.realRpowENN delta
        (sigma - routing.numerics.hierarchy.sourceLoss)
  one_log_density_absorption :
    wz1PaperRefinementFraction delta 1 *
          Kakeya.realRpowENN delta
            routing.numerics.hierarchy.sourceLoss ≤
      (1 / 2 : ENNReal) *
        Kakeya.realRpowENN delta
          routing.numerics.hierarchy.sourceLoss

/--
A uniform threshold, fixed before the normalized source, for the exact
hierarchy-source ledger and its one-log density absorption.
-/
structure Prop62V4NormalizedLedgerRoutingReceipt
    {polylogExponent cwaPower packetDensityExponent cwaLossExponent : ℕ}
    {sigma outputLoss : ℝ}
    (routing :
      Prop62V4PureCriticalFloorRoutingData
        polylogExponent cwaPower packetDensityExponent cwaLossExponent
        sigma outputLoss)
    (three : Prop62V4ThreeLossRoutingData routing) where
  delta₀ : ℝ
  delta₀_pos : 0 < delta₀
  delta₀_le_one_twelfth : delta₀ ≤ 1 / 12
  route :
    ∀ {delta : ℝ},
      0 < delta →
      delta ≤ delta₀ →
      ∀ {source :
          PureWZ2ExtremalConfiguration sigma three.sourceLoss delta},
        ∀ {normalizationExponent : ℕ},
          ∀ normalized :
              PureWZ2CroppedCriticalNormalizationData
                (outputLoss := three.normalizationLoss)
                source normalizationExponent,
            Nonempty
              (Prop62V4NormalizedLedgerRoutingData
                three normalized)

/--
Construct the hierarchy-source ledger and one-log absorption uniformly in
the physical scale and normalized source.
-/
theorem prop62V4_normalized_ledger_routing
    {polylogExponent cwaPower packetDensityExponent cwaLossExponent : ℕ}
    {sigma outputLoss : ℝ}
    (routing :
      Prop62V4PureCriticalFloorRoutingData
        polylogExponent cwaPower packetDensityExponent cwaLossExponent
        sigma outputLoss)
    (three : Prop62V4ThreeLossRoutingData routing) :
    Nonempty
      (Prop62V4NormalizedLedgerRoutingReceipt routing three) := by
  let delta₀ : ℝ := min (1 / 12) (Real.exp (-2))
  have delta₀Pos : 0 < delta₀ := by
    dsimp only [delta₀]
    positivity
  refine
    ⟨{
      delta₀ := delta₀
      delta₀_pos := delta₀Pos
      delta₀_le_one_twelfth := min_le_left _ _
      route := ?_
    }⟩
  intro delta deltaPos deltaLe source normalizationExponent normalized
  have deltaLeExp : delta ≤ Real.exp (-2) :=
    deltaLe.trans (min_le_right _ _)
  have fractionLe :
      wz1PaperRefinementFraction delta 1 ≤ (1 / 2 : ENNReal) :=
    prop62V4_oneLogFraction_le_half deltaPos deltaLeExp
  refine
    ⟨{
      source_volume_upper := ?_
      one_log_density_absorption := ?_
    }⟩
  · simpa only [three.normalizationLoss_eq] using
      normalized.final_extremal.volume_upper
  · exact
      mul_le_mul_right' fractionLe
        (Kakeya.realRpowENN delta
          routing.numerics.hierarchy.sourceLoss)

namespace Prop62V4RichCertificateCompanionData

variable
    {polylogExponent cwaPower packetDensityExponent cwaLossExponent : ℕ}
    {sigma outputLoss delta : ℝ}
    {routing :
      Prop62V4PureCriticalFloorRoutingData
        polylogExponent cwaPower packetDensityExponent cwaLossExponent
        sigma outputLoss}
    {three : Prop62V4ThreeLossRoutingData routing}
    {source :
      PureWZ2ExtremalConfiguration sigma three.sourceLoss delta}
    {normalizationExponent : ℕ}
    {normalized :
      PureWZ2CroppedCriticalNormalizationData
        (outputLoss := three.normalizationLoss)
        source normalizationExponent}
    {rho : WZ2PaperRequestedScale delta}
    {hdelta : 0 < delta}
    {preparation :
      FixedGridPreparationData
        (rho := rho.1) normalized.croppedRefined hdelta}
    {fineParentDistanceConstant : ℝ}
    {parentConstant fiberConstant : ENNReal}
    {metricCertificate :
      PureWZ2Prop62MetricParentsV4Certificate
        preparation.cleanup.refined rho fineParentDistanceConstant
          parentConstant fiberConstant}
    {eta : ℝ}
    (rich :
      Prop62V4RichCertificateCompanionData
        (eta := eta)
        (packetDensityExponent := packetDensityExponent)
        (cwaLossExponent := cwaLossExponent)
        (polylogExponent := polylogExponent)
        hdelta
        (prop62V4FixedGridMetricCompanionOfCertificate
          normalized preparation metricCertificate))

/--
The exact mass and volume ledger at
`routing.numerics.hierarchy.sourceLoss`.
-/
theorem fixedGridMetric_hierarchySourceMassVolumeLedger
    (deltaSmall : delta ≤ 1 / 12)
    (ledger :
      Prop62V4NormalizedLedgerRoutingData three normalized) :
    (wz1PaperRefinementFraction delta 11 *
          Kakeya.realRpowENN delta
            routing.numerics.hierarchy.sourceLoss *
          rich.outputCertificate.refinement.selected.family.enncard *
          Kakeya.realRpowENN delta 2 ≤
        (prop62V4FixedGridMetricCompanionOfCertificate
          normalized preparation metricCertificate
        ).metric.refinement.refined.mass) ∧
      (volume
          (prop62V4FixedGridMetricCompanionOfCertificate
            normalized preparation metricCertificate
          ).metric.refinement.refined.union ≤
        Kakeya.realRpowENN delta
          (sigma - routing.numerics.hierarchy.sourceLoss)) := by
  have selectedBodyMassLower :
      rich.outputCertificate.refinement.selected.family.enncard *
          Kakeya.realRpowENN delta 2 ≤
        (wz1PaperBodyFamily normalized.croppedFamily).mass := by
    calc
      rich.outputCertificate.refinement.selected.family.enncard *
            Kakeya.realRpowENN delta 2 ≤
          normalized.croppedFamily.enncard *
            Kakeya.realRpowENN delta 2 := by
        exact mul_le_mul_right'
          (fixedGridFinal_enncard_le_normalized
            (normalized := normalized)
            (preparation := preparation)
            (metricCertificate := metricCertificate)
            rich)
          (Kakeya.realRpowENN delta 2)
      _ ≤
          (wz1PaperBodyFamily normalized.croppedFamily).mass :=
        pureWZ2_prop62_paper_body_mass_lower
          hdelta deltaSmall normalized.line_class
  have fixedGridMassLower :
      ((1 / 2 : ENNReal) *
          Kakeya.realRpowENN delta
            routing.numerics.hierarchy.sourceLoss) *
            (rich.outputCertificate.refinement.selected.family.enncard *
              Kakeya.realRpowENN delta 2) ≤
        preparation.cleanup.refined.mass := by
    calc
      ((1 / 2 : ENNReal) *
            Kakeya.realRpowENN delta
              routing.numerics.hierarchy.sourceLoss) *
              (rich.outputCertificate.refinement.selected.family.enncard *
                Kakeya.realRpowENN delta 2) ≤
          (1 / 2 : ENNReal) *
            (Kakeya.realRpowENN delta
                routing.numerics.hierarchy.sourceLoss *
              (wz1PaperBodyFamily normalized.croppedFamily).mass) := by
        simpa only [mul_assoc] using
          mul_le_mul_left'
            (mul_le_mul_left'
              selectedBodyMassLower
              (Kakeya.realRpowENN delta
                routing.numerics.hierarchy.sourceLoss))
            (1 / 2 : ENNReal)
      _ ≤
          (1 / 2 : ENNReal) * normalized.croppedRefined.mass := by
        gcongr
        have powerEq :
            Kakeya.realRpowENN delta
                routing.numerics.hierarchy.sourceLoss =
              Kakeya.realRpowENN delta three.normalizationLoss :=
          congrArg (Kakeya.realRpowENN delta)
            three.normalizationLoss_eq.symm
        rw [powerEq]
        exact normalized.final_extremal.dense
      _ = normalized.croppedRefined.mass / 2 := by
        simp only [ENNReal.div_eq_inv_mul, mul_one]
      _ ≤ preparation.cleanup.refined.mass :=
        preparation.cleanup.mass_retention
  have metricRetained :
      wz1PaperRefinementFraction delta 10 *
            preparation.cleanup.refined.mass ≤
        (prop62V4FixedGridMetricCompanionOfCertificate
          normalized preparation metricCertificate
        ).metric.refinement.refined.mass :=
    (prop62V4FixedGridMetricCompanionOfCertificate
      normalized preparation metricCertificate).metric.refinement.retained_mass
  constructor
  · calc
      wz1PaperRefinementFraction delta 11 *
            Kakeya.realRpowENN delta
              routing.numerics.hierarchy.sourceLoss *
            rich.outputCertificate.refinement.selected.family.enncard *
            Kakeya.realRpowENN delta 2 =
          wz1PaperRefinementFraction delta 10 *
            (wz1PaperRefinementFraction delta 1 *
              (Kakeya.realRpowENN delta
                  routing.numerics.hierarchy.sourceLoss *
                rich.outputCertificate.refinement.selected.family.enncard *
                Kakeya.realRpowENN delta 2)) := by
        simp only [wz1PaperRefinementFraction]
        rw [show 11 = 10 + 1 by norm_num, pow_add]
        ring
      _ ≤
          wz1PaperRefinementFraction delta 10 *
            (((1 / 2 : ENNReal) *
                Kakeya.realRpowENN delta
                  routing.numerics.hierarchy.sourceLoss) *
              (rich.outputCertificate.refinement.selected.family.enncard *
                Kakeya.realRpowENN delta 2)) := by
        simpa only [mul_assoc, mul_comm, mul_left_comm] using
          mul_le_mul_right'
            (mul_le_mul_right'
              ledger.one_log_density_absorption
              (rich.outputCertificate.refinement.selected.family.enncard *
                Kakeya.realRpowENN delta 2))
            (wz1PaperRefinementFraction delta 10)
      _ ≤
          wz1PaperRefinementFraction delta 10 *
            preparation.cleanup.refined.mass := by
        gcongr
      _ ≤ _ := metricRetained
  · exact
      (measure_mono <|
        fixedGridMetric_refined_union_subset_normalized
          (normalized := normalized)
          (preparation := preparation)
          (metricCertificate := metricCertificate)).trans
        ledger.source_volume_upper

end Prop62V4RichCertificateCompanionData

end Kakeya.Assouad.Prop62PaperAudit.V4

end
