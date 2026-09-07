import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9WholeCellSaturation
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63M9SameExtremizerAssembly

/-!
# Ordinary trace source of the Proposition 6.3 whole-cell saturation

The selected metric fibre is definitionally the inner member of the composed
subfamily of the initial normalized family.  The whole-cell saturation is
therefore a legitimate final shading for the normalization trace.
-/

noncomputable section
namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set

variable
    {delta Delta sigma stickyLoss localLoss commonSliceLoss chartLoss
      tau epsilon₁ epsilon₃ coefficient initialInputLoss
      initialOutputLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration
      sigma initialInputLoss delta}
    {firstScale : WZ2PaperRequestedScale delta}
    {logExponent normalizationExponent : ℕ}
    (initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := initialOutputLoss) initialSource
      normalizationExponent)
    {firstSticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      initialNormalized.croppedRefined firstScale logExponent}
    {retainedFactor : ENNReal}
    (first : Proposition63FirstChartData
      (localLoss := localLoss) (commonSliceLoss := commonSliceLoss)
      (chartLoss := chartLoss) (tau := tau) (epsilon₁ := epsilon₁)
      (epsilon₃ := epsilon₃) (coefficient := coefficient)
      firstSticky Delta retainedFactor)

/-- The first metric fibre, regarded as a subfamily of the initial normalized
cropped family.  Its family is definitionally the family supporting the
whole-cell saturation. -/
def Proposition63FirstChartData.wholeCellSelected :
    Kakeya.Streamlined.TubeSubfamily
    initialNormalized.croppedFamily :=
  firstSticky.selected.comp first.metricFiber.fiberFamily

/-- The whole-cell saturation with its ambient normalized-family indexing
made explicit. -/
def Proposition63FirstChartData.wholeCellShading : WZ1PaperTubeShading
    (first.wholeCellSelected initialNormalized).family :=
  first.chartSelection.saturated

@[simp] theorem Proposition63FirstChartData.wholeCellSelected_family :
    (first.wholeCellSelected initialNormalized).family =
      first.metricFiber.fiberFamily.family :=
  rfl

@[simp] theorem Proposition63FirstChartData.wholeCellSelected_embedding
    (index : Fin (first.wholeCellSelected initialNormalized).family.card) :
    (first.wholeCellSelected initialNormalized).embedding index =
      firstSticky.selected.embedding
        (first.metricFiber.fiberFamily.embedding index) :=
  rfl

theorem Proposition63FirstChartData.wholeCellShading_sub_initialNormalized
    (index : Fin (first.wholeCellSelected initialNormalized).family.card) :
    (first.wholeCellShading initialNormalized).carrier index ⊆
      initialNormalized.croppedRefined.carrier
        ((first.wholeCellSelected initialNormalized).embedding index) := by
  intro point hpoint
  have hselected :=
    first.chartSelection.saturated_sub_selectedFiber index hpoint
  have hrefined : point ∈ firstSticky.refined.carrier
      (first.metricFiber.fiberFamily.embedding index) :=
    first.rebalanced.subshading
      (first.metricFiber.fiberFamily.embedding index) hselected
  exact firstSticky.subshading
    (first.metricFiber.fiberFamily.embedding index) hrefined

/-- The canonical ordinary trace of the whole-cell saturation. -/
def Proposition63FirstChartData.wholeCellOrdinaryTrace :
    Kakeya.Streamlined.TubeShading
      (first.wholeCellSelected initialNormalized).family :=
  initialNormalized.finalOrdinaryTrace
    (first.wholeCellSelected initialNormalized)
    (first.wholeCellShading initialNormalized)

/-- Normalization supplies its canonical trace lower bound on the exact
whole-cell shading. -/
theorem Proposition63FirstChartData.wholeCellOrdinaryTrace_mass_lower :
    (100 : ENNReal)⁻¹ *
          (Kakeya.realRpowENN delta initialInputLoss / 2) *
          (first.wholeCellShading initialNormalized).mass ≤
      (first.wholeCellOrdinaryTrace initialNormalized).mass := by
  exact initialNormalized.finalOrdinaryTrace_mass_lower_normalized
    (first.wholeCellSelected initialNormalized)
    (first.wholeCellShading initialNormalized)
    first.delta_pos first.chartSelection.saturated_cubical
    (first.wholeCellShading_sub_initialNormalized initialNormalized)

/-- The chart source-density lower bound survives whole-cell saturation and
then passes through the normalized ordinary trace. -/
theorem Proposition63FirstChartData.wholeCellOrdinaryTrace_source_mass_lower :
    (100 : ENNReal)⁻¹ *
          (Kakeya.realRpowENN delta initialInputLoss / 2) *
          ((first.sliceDensity / 2) *
            first.metricFiber.fiberFamily.family.enncard *
            Kakeya.realRpowENN delta 2) ≤
      (first.wholeCellOrdinaryTrace initialNormalized).mass := by
  calc
    (100 : ENNReal)⁻¹ *
          (Kakeya.realRpowENN delta initialInputLoss / 2) *
          ((first.sliceDensity / 2) *
            first.metricFiber.fiberFamily.family.enncard *
            Kakeya.realRpowENN delta 2) ≤
        (100 : ENNReal)⁻¹ *
          (Kakeya.realRpowENN delta initialInputLoss / 2) *
          first.chartSelection.sourceShading.mass := by
      gcongr
      exact first.chartRescaled.source_mass
    _ ≤ (100 : ENNReal)⁻¹ *
          (Kakeya.realRpowENN delta initialInputLoss / 2) *
          (first.wholeCellShading initialNormalized).mass := by
      gcongr
      exact first.chartSelection.sourceShading_mass_le_saturated_mass
    _ ≤ (first.wholeCellOrdinaryTrace initialNormalized).mass :=
      first.wholeCellOrdinaryTrace_mass_lower initialNormalized

/-- Rebuild the literal image and extremality on the saturated shading while
retaining the frozen metric-fibre rescaling certificate. -/
theorem Proposition63FirstChartData.wholeCellFullFiberOutput_nonempty
    (hloss : stickyLoss ≤ chartLoss)
    (hchartLoss : 0 < chartLoss)
    (hscaleOne : firstScale.1 ≤ 1)
    (hscaleSmall : delta / firstScale.1 ≤ 1 / 24)
    (hdensityAbsorb :
      Kakeya.realRpowENN (delta / firstScale.1) chartLoss *
          (55296 * Kakeya.deltaTubeVolume 1) ≤
        ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
          (first.sliceDensity / 2)) :
    Nonempty (WZ2PaperPureRescaledFullFiberOutput
      (sigma := sigma) (loss := chartLoss)
      (first.wholeCellShading initialNormalized)
      (firstSticky.coarse.tube first.metricFiber.parent)
      firstSticky.coarse_extremal.delta_pos) := by
  rcases proposition63_literal_unit_rescaled_shading
      first.metricFiber (first.wholeCellShading initialNormalized)
      hscaleOne hscaleSmall with ⟨literalImage⟩
  have hsourceSub : PaperIsSubshading
      (first.wholeCellShading initialNormalized)
      first.metricFiber.sourceFiber := fun index =>
    (first.chartSelection.saturated_sub_selectedFiber index).trans
      (first.metricFiber.source_subshading index)
  have hsourceMass :
      (first.sliceDensity / 2) *
          first.metricFiber.fiberFamily.family.enncard *
          Kakeya.realRpowENN delta 2 ≤
        (first.wholeCellShading initialNormalized).mass :=
    first.chartRescaled.source_mass.trans
      first.chartSelection.sourceShading_mass_le_saturated_mass
  have hextremal := rescaledSubfiber_extremal_of_source_density
    first.metricFiber.frozenRescaled hsourceSub literalImage
    (first.sliceDensity / 2) hsourceMass hloss hchartLoss hscaleSmall
    hdensityAbsorb
  exact ⟨{
    familyData := first.metricFiber.frozenRescaled.familyData
    literalShading := literalImage
    jacobianConstant := first.metricFiber.frozenRescaled.jacobianConstant
    jacobianConstant_one :=
      first.metricFiber.frozenRescaled.jacobianConstant_one
    jacobianConstant_finite :=
      first.metricFiber.frozenRescaled.jacobianConstant_finite
    rescalingCertificate :=
      first.metricFiber.frozenRescaled.rescalingCertificate
    extremal := hextremal
    source_cardinality_eq :=
      first.metricFiber.frozenRescaled.source_cardinality_eq
  }⟩

/-- The public ordinary family of a rescaled whole-cell output has the
standard quadratic body-mass upper bound. -/
theorem Proposition63FirstChartData.wholeCell_public_body_mass_upper
    (output : WZ2PaperPureRescaledFullFiberOutput
      (sigma := sigma) (loss := chartLoss)
      (first.wholeCellShading initialNormalized)
      (firstSticky.coarse.tube first.metricFiber.parent)
      firstSticky.coarse_extremal.delta_pos)
    (hscaleOne : delta / firstScale.1 ≤ 1) :
    output.rescalingCertificate.publicFamily.toBodyFamily.mass ≤
      (55296 * Kakeya.deltaTubeVolume 1) *
        Kakeya.realRpowENN (delta / firstScale.1) 2 *
          first.metricFiber.fiberFamily.family.enncard := by
  have targetNonempty :
      output.rescalingCertificate.publicFamily.Nonempty :=
    output.extremal.nonempty
  let index : Fin output.rescalingCertificate.publicFamily.card :=
    ⟨0, targetNonempty⟩
  have tubeVolumeUpper :
      Kakeya.deltaTubeVolume (delta / firstScale.1) ≤
        24 * Kakeya.realRpowENN (delta / firstScale.1) 2 *
          Kakeya.deltaTubeVolume 1 := by
    have upper := tube_volume_scaling.2.2
      (delta / firstScale.1) output.extremal.delta_pos hscaleOne
      (output.rescalingCertificate.publicFamily.tube index)
    rwa [tube_volume_scaling.1
      (delta / firstScale.1)
      (output.rescalingCertificate.publicFamily.tube index)] at upper
  rw [tubeFamily_mass_eq_nominal]
  change output.rescalingCertificate.publicFamily.enncard *
      Kakeya.deltaTubeVolume (delta / firstScale.1) ≤ _
  rw [output.source_cardinality_eq]
  calc
    first.metricFiber.fiberFamily.family.enncard *
          Kakeya.deltaTubeVolume (delta / firstScale.1) ≤
        first.metricFiber.fiberFamily.family.enncard *
          (24 * Kakeya.realRpowENN (delta / firstScale.1) 2 *
            Kakeya.deltaTubeVolume 1) := by gcongr
    _ ≤ first.metricFiber.fiberFamily.family.enncard *
          (55296 * Kakeya.realRpowENN (delta / firstScale.1) 2 *
            Kakeya.deltaTubeVolume 1) := by
      gcongr
      norm_num
    _ = _ := by ring

/-- The honest normalization trace satisfies the aggregate density inequality
needed by the critical-witness adapter.  Unlike the invalid direct cropped
image shortcut, this statement pays the normalization density factor
explicitly. -/
theorem Proposition63FirstChartData.wholeCell_trace_massLower
    (output : WZ2PaperPureRescaledFullFiberOutput
      (sigma := sigma) (loss := chartLoss)
      (first.wholeCellShading initialNormalized)
      (firstSticky.coarse.tube first.metricFiber.parent)
      firstSticky.coarse_extremal.delta_pos)
    (hscaleOne : delta / firstScale.1 ≤ 1)
    (hdensityAbsorb :
      Kakeya.realRpowENN (delta / firstScale.1) chartLoss *
          (55296 * Kakeya.deltaTubeVolume 1) ≤
        ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
          ((100 : ENNReal)⁻¹ *
            (Kakeya.realRpowENN delta initialInputLoss / 2) *
            (first.sliceDensity / 2))) :
    Kakeya.realRpowENN (delta / firstScale.1) chartLoss *
          output.rescalingCertificate.publicFamily.toBodyFamily.mass ≤
      (ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
          ENNReal.ofReal ((1 / firstScale.1 : ℝ) ^ 2)) *
        (first.wholeCellOrdinaryTrace initialNormalized).mass := by
  have bodyUpper := first.wholeCell_public_body_mass_upper
    initialNormalized output hscaleOne
  have traceLower := first.wholeCellOrdinaryTrace_source_mass_lower
    initialNormalized
  have scaleIdentity :
      ENNReal.ofReal ((1 / firstScale.1 : ℝ) ^ 2) *
          Kakeya.realRpowENN delta 2 =
        Kakeya.realRpowENN (delta / firstScale.1) 2 := by
    simp only [Kakeya.realRpowENN]
    have deltaTwo : Real.rpow delta 2 = delta ^ 2 :=
      Real.rpow_two delta
    have ratioTwo :
        Real.rpow (delta / firstScale.1) 2 =
          (delta / firstScale.1) ^ 2 :=
      Real.rpow_two (delta / firstScale.1)
    rw [deltaTwo, ratioTwo]
    rw [← ENNReal.ofReal_mul (sq_nonneg (1 / firstScale.1))]
    congr 1
    field_simp [(first.delta_pos.trans_le firstScale.2.1).ne']
  calc
    _ ≤ Kakeya.realRpowENN (delta / firstScale.1) chartLoss *
        ((55296 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN (delta / firstScale.1) 2 *
            first.metricFiber.fiberFamily.family.enncard) := by gcongr
    _ = (Kakeya.realRpowENN (delta / firstScale.1) chartLoss *
          (55296 * Kakeya.deltaTubeVolume 1)) *
        (Kakeya.realRpowENN (delta / firstScale.1) 2 *
          first.metricFiber.fiberFamily.family.enncard) := by ring
    _ ≤ (ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
          ((100 : ENNReal)⁻¹ *
            (Kakeya.realRpowENN delta initialInputLoss / 2) *
            (first.sliceDensity / 2))) *
        (Kakeya.realRpowENN (delta / firstScale.1) 2 *
          first.metricFiber.fiberFamily.family.enncard) := by gcongr
    _ = (ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
          ENNReal.ofReal ((1 / firstScale.1 : ℝ) ^ 2)) *
        ((100 : ENNReal)⁻¹ *
          (Kakeya.realRpowENN delta initialInputLoss / 2) *
          ((first.sliceDensity / 2) *
            first.metricFiber.fiberFamily.family.enncard *
              Kakeya.realRpowENN delta 2)) := by
      rw [← scaleIdentity]
      ring
    _ ≤ _ := mul_le_mul_left' traceLower _

/-- With a full rescaled-fibre output built on the saturated shading, the
remaining hypothesis is exactly the scalar comparison required by the
aggregate trace constructor. -/
noncomputable def
    Proposition63FirstChartData.wholeCellChartOrdinaryExtremalSourceOfTraceMass
    (output : WZ2PaperPureRescaledFullFiberOutput
      (sigma := sigma) (loss := chartLoss)
      (first.wholeCellShading initialNormalized)
      (firstSticky.coarse.tube first.metricFiber.parent)
      firstSticky.coarse_extremal.delta_pos)
    (massLower :
      Kakeya.realRpowENN (delta / firstScale.1) chartLoss *
            output.rescalingCertificate.publicFamily.toBodyFamily.mass ≤
        (ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
            ENNReal.ofReal ((1 / firstScale.1 : ℝ) ^ 2)) *
          (first.wholeCellOrdinaryTrace initialNormalized).mass) :
    PureWZ2ExtremalConfiguration sigma chartLoss
      (delta / firstScale.1) :=
  proposition63ChartOrdinaryExtremalSourceOfTraceMass
    initialNormalized
    (first.wholeCellSelected initialNormalized)
    (first.wholeCellShading initialNormalized)
    (firstSticky.coarse.tube first.metricFiber.parent)
    firstSticky.coarse_extremal.delta_pos output massLower
    first.chartSelection.chartLabel.chart

end Kakeya.Assouad.PureWZ2
end
