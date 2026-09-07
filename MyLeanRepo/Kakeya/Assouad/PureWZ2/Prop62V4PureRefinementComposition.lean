import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62V4RichCertificateCompanion
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62PaperFinalV4FixedGridPreparation
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperRefinementComposition

/-!
# Pure V4 refinement composition

The normalization output is already a cropped family with its cubical
shading.  The rich Target-3 certificate refines that shading with exponent
`10`, and the canonical Target-4 certificate refines the resulting shading
with exponent `50`.  This module composes those exact dependent witnesses
back to the normalized cropped family.

No family, shading, or cover is selected here.
-/

noncomputable section

namespace Kakeya.Assouad.Prop62PaperAudit.V4

open MeasureTheory
open Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- Regard one rich metric-parent certificate as its canonical companion. -/
noncomputable def prop62V4MetricCompanionOfCertificate
    {delta sigma sourceLoss normalizationLoss : ℝ}
    {source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {normalizationExponent : ℕ}
    (normalized :
      PureWZ2CroppedCriticalNormalizationData
        (outputLoss := normalizationLoss)
        source normalizationExponent)
    {rho : WZ2PaperRequestedScale delta}
    {fineParentDistanceConstant : ℝ}
    {parentConstant fiberConstant : ENNReal}
    (metricCertificate :
      PureWZ2Prop62MetricParentsV4Certificate
        normalized.croppedRefined rho fineParentDistanceConstant
          parentConstant fiberConstant) :
    Prop62V4MetricParentsRichCompanionData
      normalized.croppedRefined rho fineParentDistanceConstant
        parentConstant fiberConstant where
  certificate := metricCertificate

namespace Prop62V4RichCertificateCompanionData

variable
    {delta sigma sourceLoss normalizationLoss : ℝ}
    {source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {normalizationExponent : ℕ}
    {normalized :
      PureWZ2CroppedCriticalNormalizationData
        (outputLoss := normalizationLoss)
        source normalizationExponent}
    {rho : WZ2PaperRequestedScale delta}
    {fineParentDistanceConstant : ℝ}
    {parentConstant fiberConstant : ENNReal}
    {metricCertificate :
      PureWZ2Prop62MetricParentsV4Certificate
        normalized.croppedRefined rho fineParentDistanceConstant
          parentConstant fiberConstant}
    {eta : ℝ}
    {packetDensityExponent cwaLossExponent polylogExponent : ℕ}
    (rich :
      Prop62V4RichCertificateCompanionData
        (eta := eta)
        (packetDensityExponent := packetDensityExponent)
        (cwaLossExponent := cwaLossExponent)
        (polylogExponent := polylogExponent)
        normalized.final_extremal.delta_pos
        (prop62V4MetricCompanionOfCertificate
          normalized metricCertificate))

/-- The exact nested tube subfamily of the normalized cropped family. -/
noncomputable def composedSelected :
    Kakeya.Streamlined.TubeSubfamily normalized.croppedFamily :=
  (prop62V4MetricCompanionOfCertificate
      normalized metricCertificate).metric.refinement.selected.comp
    rich.outputCertificate.refinement.selected

/--
The final selected shading, viewed on the exact composed subfamily of the
normalized cropped family.
-/
noncomputable def composedShading :
    WZ1PaperTubeShading rich.composedSelected.family :=
  rich.outputCertificate.refinement.refined

/-- The final Section 6 cover on the exact composed fine family. -/
noncomputable def composedCover :
    PureWZ2Section6Cover
      rich.composedSelected.family
      rich.outputCertificate.coarse.family :=
  rich.outputCertificate.cover

/--
The metric ten-log refinement followed by the canonical four-degree
fifty-log refinement.
-/
noncomputable def composedRefinement :
    WZ1PaperRefinement normalized.croppedRefined 60 := by
  simpa using
    (Classical.choice <|
      wz2_paper_refinement_composition
        normalized.croppedRefined 10 50
        (prop62V4MetricCompanionOfCertificate
          normalized metricCertificate).metric.refinement
        rich.outputCertificate.refinement).toRefinement

@[simp] theorem composedRefinement_selected :
    rich.composedRefinement.selected = rich.composedSelected :=
  rfl

@[simp] theorem composedRefinement_selected_family :
    rich.composedRefinement.selected.family =
      rich.outputCertificate.refinement.selected.family :=
  rfl

@[simp] theorem composedSelected_embedding
    (index : Fin rich.composedSelected.family.card) :
    rich.composedSelected.embedding index =
      (prop62V4MetricCompanionOfCertificate
        normalized metricCertificate).metric.refinement.selected.embedding
        (rich.outputCertificate.refinement.selected.embedding index) :=
  rfl

@[simp] theorem composedRefinement_refined :
    rich.composedRefinement.refined =
      rich.outputCertificate.refinement.refined :=
  rfl

@[simp] theorem composedShading_eq :
    rich.composedShading =
      rich.outputCertificate.refinement.refined :=
  rfl

theorem composed_subshading
    (index : Fin rich.composedSelected.family.card) :
    rich.composedShading.carrier index ⊆
      normalized.croppedRefined.carrier
        (rich.composedSelected.embedding index) :=
  rich.composedRefinement.subshading index

theorem composed_retained_mass :
    wz1PaperRefinementFraction delta 60 *
        normalized.croppedRefined.mass ≤
      rich.composedShading.mass :=
  rich.composedRefinement.retained_mass

theorem composed_retained_mass_pure :
    wz2PaperPureRefinementFraction delta 60 *
        normalized.croppedRefined.mass ≤
      rich.composedShading.mass := by
  simpa [wz2PaperPureRefinementFraction,
    wz1PaperRefinementFraction] using rich.composed_retained_mass

theorem composed_cubical :
    WZ1PaperIsCubicalShading rich.composedShading :=
  rich.outputCertificate.refined_cubical

@[simp] theorem final_family_eq_publicOutput :
    rich.composedSelected.family =
      rich.publicOutput.refinement.selected.family :=
  rfl

@[simp] theorem final_shading_eq_publicOutput :
    rich.composedShading =
      rich.publicOutput.refinement.refined :=
  rfl

@[simp] theorem final_coarse_eq_publicOutput :
    rich.outputCertificate.coarse.family =
      rich.publicOutput.coarse.family :=
  rfl

theorem final_cover_eq_publicOutput :
    HEq rich.outputCertificate.cover rich.publicOutput.cover :=
  HEq.rfl

theorem composedCover_eq_outputCertificate :
    HEq rich.composedCover rich.outputCertificate.cover :=
  HEq.rfl

theorem composedCover_eq_publicOutput :
    HEq rich.composedCover rich.publicOutput.cover :=
  HEq.rfl

end Prop62V4RichCertificateCompanionData

/--
Regard a rich metric-parent certificate built after fixed-grid cleanup as its
canonical companion.  This packages the existing certificate without making
another choice.
-/
noncomputable def prop62V4FixedGridMetricCompanionOfCertificate
    {delta sigma sourceLoss normalizationLoss : ℝ}
    {source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {normalizationExponent : ℕ}
    (normalized :
      PureWZ2CroppedCriticalNormalizationData
        (outputLoss := normalizationLoss)
        source normalizationExponent)
    {rho : WZ2PaperRequestedScale delta}
    {hdelta : 0 < delta}
    (preparation :
      FixedGridPreparationData
        (rho := rho.1) normalized.croppedRefined hdelta)
    {fineParentDistanceConstant : ℝ}
    {parentConstant fiberConstant : ENNReal}
    (metricCertificate :
      PureWZ2Prop62MetricParentsV4Certificate
        preparation.cleanup.refined rho fineParentDistanceConstant
          parentConstant fiberConstant) :
    Prop62V4MetricParentsRichCompanionData
      preparation.cleanup.refined rho fineParentDistanceConstant
        parentConstant fiberConstant where
  certificate := metricCertificate

namespace Prop62V4RichCertificateCompanionData

variable
    {delta sigma sourceLoss normalizationLoss : ℝ}
    {source :
      PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    {normalizationExponent : ℕ}
    {normalized :
      PureWZ2CroppedCriticalNormalizationData
        (outputLoss := normalizationLoss)
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
    {packetDensityExponent cwaLossExponent polylogExponent : ℕ}
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
The fixed-grid one-log refinement followed by the exact metric ten-log
refinement.  This is the source-shading ledger consumed before the terminal
four-degree fifty-log refinement.
-/
noncomputable def fixedGridMetricComposedRefinement :
    WZ1PaperRefinement normalized.croppedRefined 11 := by
  simpa using
    (Classical.choice <|
      wz2_paper_refinement_composition
        normalized.croppedRefined 1 10
        preparation.fixedGridRefinement
        (prop62V4FixedGridMetricCompanionOfCertificate
          normalized preparation metricCertificate).metric.refinement
    ).toRefinement

@[simp] theorem fixedGridMetricComposedRefinement_selected_family :
    (fixedGridMetricComposedRefinement
      (normalized := normalized)
      (preparation := preparation)
      (metricCertificate := metricCertificate)).selected.family =
      (prop62V4FixedGridMetricCompanionOfCertificate
        normalized preparation metricCertificate
      ).metric.refinement.selected.family :=
  rfl

@[simp] theorem fixedGridMetricComposedRefinement_refined :
    (fixedGridMetricComposedRefinement
      (normalized := normalized)
      (preparation := preparation)
      (metricCertificate := metricCertificate)).refined =
      (prop62V4FixedGridMetricCompanionOfCertificate
        normalized preparation metricCertificate
      ).metric.refinement.refined :=
  rfl

/--
The exact metric-refined union is contained in the normalized source union.
The witness is the composed one-plus-ten-log refinement itself.
-/
theorem fixedGridMetric_refined_union_subset_normalized :
    (prop62V4FixedGridMetricCompanionOfCertificate
        normalized preparation metricCertificate
      ).metric.refinement.refined.union ⊆
      normalized.croppedRefined.union := by
  rw [← fixedGridMetricComposedRefinement_refined
    (normalized := normalized)
    (preparation := preparation)
    (metricCertificate := metricCertificate)]
  rintro point ⟨index, pointMem⟩
  exact
    ⟨(fixedGridMetricComposedRefinement
        (normalized := normalized)
        (preparation := preparation)
        (metricCertificate := metricCertificate)).selected.embedding index,
      (fixedGridMetricComposedRefinement
        (normalized := normalized)
        (preparation := preparation)
        (metricCertificate := metricCertificate)).subshading index pointMem⟩

/--
The terminal four-degree family is the already selected subfamily of the
metric family, hence its cardinality is bounded by the normalized source
cardinality without making another selection.
-/
theorem fixedGridFinal_enncard_le_normalized :
    rich.outputCertificate.refinement.selected.family.enncard ≤
      normalized.croppedFamily.enncard := by
  have cardBound :
      rich.outputCertificate.refinement.selected.family.card ≤
        normalized.croppedFamily.card := by
    have bound :=
      Fintype.card_le_of_injective
        (fun index =>
        (fixedGridMetricComposedRefinement
          (normalized := normalized)
          (preparation := preparation)
          (metricCertificate := metricCertificate)).selected.embedding
            (rich.outputCertificate.refinement.selected.embedding index))
        (by
          intro first second equality
          apply rich.outputCertificate.refinement.selected.embedding.injective
          exact
            (fixedGridMetricComposedRefinement
              (normalized := normalized)
              (preparation := preparation)
              (metricCertificate := metricCertificate)
            ).selected.embedding.injective equality)
    simpa only [Fintype.card_fin] using bound
  simpa only [Kakeya.Streamlined.TubeFamily.enncard] using
    (show
      (rich.outputCertificate.refinement.selected.family.card : ENNReal) ≤
        (normalized.croppedFamily.card : ENNReal) by
      exact_mod_cast cardBound)

/--
The source-loss union-volume fact not retained by
`PureWZ2CroppedCriticalNormalizationData`.

The mass ledger below needs no extra geometric field: it uses only
`final_extremal.dense` and one scalar absorption.  Keeping the volume field
separate avoids any dependence on the implementation of `ordinaryRefined`.
-/
structure Prop62V4NormalizedSourceLedger : Prop where
  source_volume_upper :
    volume normalized.croppedRefined.union ≤
      Kakeya.realRpowENN delta (sigma - sourceLoss)

/--
The exact terminal family embeds through the canonical normalized family all
the way back into the original source family.
-/
theorem fixedGridFinal_enncard_le_source :
    rich.outputCertificate.refinement.selected.family.enncard ≤
      source.family.enncard := by
  have cardBound :
      rich.outputCertificate.refinement.selected.family.card ≤
        source.family.card := by
    have bound :=
      Fintype.card_le_of_injective
        (fun index =>
          normalized.selected.embedding
            (normalized.indexEquiv.symm
              ((fixedGridMetricComposedRefinement
                (normalized := normalized)
                (preparation := preparation)
                (metricCertificate := metricCertificate)
              ).selected.embedding
                (rich.outputCertificate.refinement.selected.embedding
                  index))))
        (by
          intro first second equality
          apply rich.outputCertificate.refinement.selected.embedding.injective
          apply
            (fixedGridMetricComposedRefinement
              (normalized := normalized)
              (preparation := preparation)
              (metricCertificate := metricCertificate)
            ).selected.embedding.injective
          apply normalized.indexEquiv.symm.injective
          exact normalized.selected.embedding.injective equality)
    simpa only [Fintype.card_fin] using bound
  simpa only [Kakeya.Streamlined.TubeFamily.enncard] using
    (show
      (rich.outputCertificate.refinement.selected.family.card : ENNReal) ≤
        (source.family.card : ENNReal) by
      exact_mod_cast cardBound)

/--
The exact source-mass premise for `productMultiplicityInputs`.

Only the fixed-grid one-log and metric ten-log refinements are charged here.
The terminal family enters solely through its existing embedding into the
metric-selected family; the later fifty-log loss is paid by the generic
product theorem.
-/
theorem fixedGridMetric_sourceMassLower
    (deltaSmall : delta ≤ 1 / 12)
    (oneLogDensityAbsorption :
      wz1PaperRefinementFraction delta 1 *
          Kakeya.realRpowENN delta sourceLoss ≤
        (1 / 2 : ENNReal) *
          Kakeya.realRpowENN delta normalizationLoss) :
    wz1PaperRefinementFraction delta 11 *
          Kakeya.realRpowENN delta sourceLoss *
          rich.outputCertificate.refinement.selected.family.enncard *
          Kakeya.realRpowENN delta 2 ≤
      (prop62V4FixedGridMetricCompanionOfCertificate
        normalized preparation metricCertificate
      ).metric.refinement.refined.mass := by
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
          Kakeya.realRpowENN delta normalizationLoss) *
            (rich.outputCertificate.refinement.selected.family.enncard *
              Kakeya.realRpowENN delta 2) ≤
        preparation.cleanup.refined.mass := by
    calc
      ((1 / 2 : ENNReal) *
            Kakeya.realRpowENN delta normalizationLoss) *
              (rich.outputCertificate.refinement.selected.family.enncard *
                Kakeya.realRpowENN delta 2) ≤
          (1 / 2 : ENNReal) *
            (Kakeya.realRpowENN delta normalizationLoss *
              (wz1PaperBodyFamily normalized.croppedFamily).mass) := by
        simpa only [mul_assoc] using
          mul_le_mul_left'
            (mul_le_mul_left'
              selectedBodyMassLower
              (Kakeya.realRpowENN delta normalizationLoss))
            (1 / 2 : ENNReal)
      _ ≤
          (1 / 2 : ENNReal) *
            normalized.croppedRefined.mass := by
        gcongr
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
  calc
    wz1PaperRefinementFraction delta 11 *
          Kakeya.realRpowENN delta sourceLoss *
          rich.outputCertificate.refinement.selected.family.enncard *
          Kakeya.realRpowENN delta 2 =
        wz1PaperRefinementFraction delta 10 *
          (wz1PaperRefinementFraction delta 1 *
            (Kakeya.realRpowENN delta sourceLoss *
              rich.outputCertificate.refinement.selected.family.enncard *
              Kakeya.realRpowENN delta 2)) := by
      simp only [wz1PaperRefinementFraction]
      rw [show 11 = 10 + 1 by norm_num, pow_add]
      ring
    _ ≤
        wz1PaperRefinementFraction delta 10 *
          (((1 / 2 : ENNReal) *
              Kakeya.realRpowENN delta normalizationLoss) *
            (rich.outputCertificate.refinement.selected.family.enncard *
              Kakeya.realRpowENN delta 2)) := by
      simpa only [mul_assoc, mul_comm, mul_left_comm] using
        mul_le_mul_right'
          (mul_le_mul_right'
            oneLogDensityAbsorption
            (rich.outputCertificate.refinement.selected.family.enncard *
              Kakeya.realRpowENN delta 2))
          (wz1PaperRefinementFraction delta 10)
    _ ≤
        wz1PaperRefinementFraction delta 10 *
          preparation.cleanup.refined.mass := by
      gcongr
    _ ≤ _ := metricRetained

/--
The exact source-volume premise for `productMultiplicityInputs`, on the same
one-plus-ten-log shading used by `fixedGridMetric_sourceMassLower`.
-/
theorem fixedGridMetric_sourceVolumeUpper
    (ledger :
      Prop62V4NormalizedSourceLedger
        (normalized := normalized)) :
    volume
        (prop62V4FixedGridMetricCompanionOfCertificate
          normalized preparation metricCertificate
        ).metric.refinement.refined.union ≤
      Kakeya.realRpowENN delta (sigma - sourceLoss) := by
  exact
    (measure_mono <|
      fixedGridMetric_refined_union_subset_normalized
        (normalized := normalized)
        (preparation := preparation)
        (metricCertificate := metricCertificate)).trans
      ledger.source_volume_upper

/--
The mass and volume inputs required by the generic product-multiplicity
assembly, both attached to the exact metric-refined shading and the exact
terminal four-degree family.
-/
theorem fixedGridMetric_sourceMassVolumeLedger
    (deltaSmall : delta ≤ 1 / 12)
    (oneLogDensityAbsorption :
      wz1PaperRefinementFraction delta 1 *
          Kakeya.realRpowENN delta sourceLoss ≤
        (1 / 2 : ENNReal) *
          Kakeya.realRpowENN delta normalizationLoss)
    (ledger :
      Prop62V4NormalizedSourceLedger
        (normalized := normalized)) :
    (wz1PaperRefinementFraction delta 11 *
          Kakeya.realRpowENN delta sourceLoss *
          rich.outputCertificate.refinement.selected.family.enncard *
          Kakeya.realRpowENN delta 2 ≤
        (prop62V4FixedGridMetricCompanionOfCertificate
          normalized preparation metricCertificate
        ).metric.refinement.refined.mass) ∧
      (volume
          (prop62V4FixedGridMetricCompanionOfCertificate
            normalized preparation metricCertificate
          ).metric.refinement.refined.union ≤
        Kakeya.realRpowENN delta (sigma - sourceLoss)) :=
  ⟨rich.fixedGridMetric_sourceMassLower
      deltaSmall oneLogDensityAbsorption,
    fixedGridMetric_sourceVolumeUpper
      (normalized := normalized)
      (preparation := preparation)
      (metricCertificate := metricCertificate)
      ledger⟩

/-- The metric ten-log and canonical four-degree fifty-log refinement. -/
noncomputable def fixedGridInnerComposedRefinement :
    WZ1PaperRefinement preparation.cleanup.refined 60 := by
  simpa using
    (Classical.choice <|
      wz2_paper_refinement_composition
        preparation.cleanup.refined 10 50
        (prop62V4FixedGridMetricCompanionOfCertificate
          normalized preparation metricCertificate).metric.refinement
        rich.outputCertificate.refinement).toRefinement

/--
The exact one-log, ten-log, and fifty-log selection as one subfamily of the
normalized cropped family.
-/
noncomputable def fixedGridComposedSelected :
    Kakeya.Streamlined.TubeSubfamily normalized.croppedFamily :=
  preparation.fixedGridRefinement.selected.comp
    ((prop62V4FixedGridMetricCompanionOfCertificate
      normalized preparation metricCertificate).metric.refinement.selected.comp
        rich.outputCertificate.refinement.selected)

/-- The final shading on the exact three-stage selected family. -/
noncomputable def fixedGridComposedShading :
    WZ1PaperTubeShading rich.fixedGridComposedSelected.family :=
  rich.outputCertificate.refinement.refined

/-- The exact `1 + 10 + 50 = 61` refinement of the normalized shading. -/
noncomputable def fixedGridComposedRefinement :
    WZ1PaperRefinement normalized.croppedRefined 61 :=
  preparation.composeSixtyLogRefinement
    rich.fixedGridInnerComposedRefinement

/-- The final Section 6 cover on the exact 61-log fine family. -/
noncomputable def fixedGridComposedCover :
    PureWZ2Section6Cover
      rich.fixedGridComposedSelected.family
      rich.outputCertificate.coarse.family :=
  rich.outputCertificate.cover

@[simp] theorem fixedGridComposedRefinement_selected :
    rich.fixedGridComposedRefinement.selected =
      rich.fixedGridComposedSelected :=
  rfl

@[simp] theorem fixedGridComposedRefinement_selected_family :
    rich.fixedGridComposedRefinement.selected.family =
      rich.outputCertificate.refinement.selected.family :=
  rfl

@[simp] theorem fixedGridComposedSelected_embedding
    (index : Fin rich.fixedGridComposedSelected.family.card) :
    rich.fixedGridComposedSelected.embedding index =
      preparation.fixedGridRefinement.selected.embedding
        ((prop62V4FixedGridMetricCompanionOfCertificate
          normalized preparation metricCertificate
        ).metric.refinement.selected.embedding
          (rich.outputCertificate.refinement.selected.embedding index)) :=
  rfl

@[simp] theorem fixedGridComposedRefinement_refined :
    rich.fixedGridComposedRefinement.refined =
      rich.outputCertificate.refinement.refined :=
  rfl

@[simp] theorem fixedGridComposedShading_eq :
    rich.fixedGridComposedShading =
      rich.outputCertificate.refinement.refined :=
  rfl

theorem fixedGridComposed_subshading
    (index : Fin rich.fixedGridComposedSelected.family.card) :
    rich.fixedGridComposedShading.carrier index ⊆
      normalized.croppedRefined.carrier
        (rich.fixedGridComposedSelected.embedding index) :=
  rich.fixedGridComposedRefinement.subshading index

theorem fixedGridComposed_retained_mass :
    wz1PaperRefinementFraction delta 61 *
        normalized.croppedRefined.mass ≤
      rich.fixedGridComposedShading.mass :=
  rich.fixedGridComposedRefinement.retained_mass

theorem fixedGridComposed_retained_mass_pure :
    wz2PaperPureRefinementFraction delta 61 *
        normalized.croppedRefined.mass ≤
      rich.fixedGridComposedShading.mass := by
  simpa [wz2PaperPureRefinementFraction,
    wz1PaperRefinementFraction] using rich.fixedGridComposed_retained_mass

theorem fixedGridComposed_cubical :
    WZ1PaperIsCubicalShading rich.fixedGridComposedShading :=
  rich.outputCertificate.refined_cubical

@[simp] theorem fixedGridFinal_family_eq_publicOutput :
    rich.fixedGridComposedSelected.family =
      rich.publicOutput.refinement.selected.family :=
  rfl

@[simp] theorem fixedGridFinal_shading_eq_publicOutput :
    rich.fixedGridComposedShading =
      rich.publicOutput.refinement.refined :=
  rfl

@[simp] theorem fixedGridFinal_coarse_eq_publicOutput :
    rich.outputCertificate.coarse.family =
      rich.publicOutput.coarse.family :=
  rfl

theorem fixedGridComposedCover_eq_outputCertificate :
    HEq rich.fixedGridComposedCover rich.outputCertificate.cover :=
  HEq.rfl

theorem fixedGridComposedCover_eq_publicOutput :
    HEq rich.fixedGridComposedCover rich.publicOutput.cover :=
  HEq.rfl

end Prop62V4RichCertificateCompanionData

end Kakeya.Assouad.Prop62PaperAudit.V4

end
