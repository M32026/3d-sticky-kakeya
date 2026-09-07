import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Node05ConditionalAssembly
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64FinalAssembly
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64PaperEDAssembly

/-!
# Source-faithful Proposition 6.4 geometric and ED producer

This module keeps the common-window source selection, its exact affine image,
the isotropic cleanup, and the paper essentially-distinct selection on one
dependent witness.  Quantitative extremality and final CWA estimates remain
separate inputs to the final assembly.
-/

noncomputable section

namespace Kakeya.Assouad

namespace PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData

variable
    {sigma workLoss sourceDelta targetDelta₀ : ℝ}
    {output : PureWZ2NormalizedHierarchyOutput
      sigma workLoss sourceDelta}
    {hsourceSmall : sourceDelta ≤
      pureWZ2Proposition64Lemma35SourceCeiling targetDelta₀}

/-- The exact common-window source subfamily used by the geometric prefix. -/
noncomputable abbrev selectedSource
    (geometry : PureWZ2Proposition64Lemma35GeometricData
      output hsourceSmall) :
    Kakeya.Streamlined.TubeSubfamily output.source.family :=
  Kakeya.Streamlined.TubeSubfamily.fromFinset
    output.source.family geometry.common.selected

/-- The literal selected short-slab shading. -/
noncomputable abbrev selectedShading
    (geometry : PureWZ2Proposition64Lemma35GeometricData
      output hsourceSmall) :
    WZ1PaperTubeShading geometry.selectedSource.family :=
  restrictPaperShading geometry.selectedSource output.prepared.slab.shading

/-- The source local-grain field restricted to the common-window family. -/
noncomputable abbrev selectedLocal
    (geometry : PureWZ2Proposition64Lemma35GeometricData
      output hsourceSmall) :
    PureWZ2LocalGrainData geometry.selectedShading sigma
      (Kakeya.realRpowENN sourceDelta (-workLoss)) :=
  output.hierarchy.localGrains.restrictSubfamilyWithShading geometry.selectedSource
    geometry.selectedShading
    (fun index _point hpoint => output.prepared.slab.subshading
      (geometry.selectedSource.embedding index) hpoint)

/-- Repackage the selected exact image with provenance back to the original
hierarchy family. -/
noncomputable def imageData
    (geometry : PureWZ2Proposition64Lemma35GeometricData
      output hsourceSmall) :
    PureWZ2Proposition64CommonWindowImageData
      (targetDelta := pureWZ2Proposition64Lemma35ImageDelta sourceDelta)
      output.prepared.restrictedRaw.slope output.prepared.slab.center
      output.prepared.slab.anchorHeight output.prepared.slab.halfHeight
      output.prepared.normalization output.source.family
      output.prepared.slab.shading geometry.common
      output.prepared.slab.halfHeight_pos
      output.prepared.normalized.normalization_pos :=
  geometry.common.toImage output.source.line_class
    output.prepared.slab.halfHeight_pos output.halfHeight_small
    output.prepared.normalization_one
    output.prepared.normalized.anchor_value_bound geometry.scales.imageDelta_pos
    (by
      rw [← output.prepared.normalized.slope_eq]
      exact output.prepared.normalized.normalized)

/-- The exact affine-image shading consumed by the stored isotropic cleanup. -/
noncomputable abbrev exactShading
    (geometry : PureWZ2Proposition64Lemma35GeometricData
      output hsourceSmall) :
    WZ1PaperTubeShading geometry.imageData.image.family :=
  pureWZ2Proposition64ExactImageShading
    output.source.extremal.delta_pos
    output.prepared.restrictedRaw.slope output.prepared.slab.center
    output.prepared.slab.anchorHeight output.prepared.slab.halfHeight
    output.prepared.normalization geometry.common.translation
    output.prepared.slab.halfHeight_pos output.normalization_nine
    output.prepared.normalized.anchor_value_bound geometry.scales.image_radius
    geometry.selectedSource.family geometry.selectedShading
    (output.source.line_class.subfamily geometry.selectedSource)
    (geometry.common.image_mem_axisBox output.source.extremal.delta_pos
      geometry.scales.sourceDelta_small
      output.prepared.slab.halfHeight_pos
      (by linarith [output.halfHeight_small]) output.normalization_nine
      output.prepared.normalized.anchor_value_bound output.source.line_class
      output.prepared.shading_subset_shortSlab)

/-- Every exact-image carrier still names its literal source tube in the
pre-window hierarchy family. -/
theorem exactCarrier_provenance
    (geometry : PureWZ2Proposition64Lemma35GeometricData
      output hsourceSmall) :
    ∀ target, geometry.exactShading.carrier target ⊆
      pureWZ2Proposition64TranslatedMap
          output.prepared.restrictedRaw.slope output.prepared.slab.center
          output.prepared.slab.anchorHeight output.prepared.slab.halfHeight
          output.prepared.normalization geometry.common.translation ''
        output.prepared.slab.shading.carrier
          (geometry.imageData.image.sourceParent target) := by
  intro target point hpoint
  rcases hpoint with ⟨sourcePoint, hsourcePoint, rfl⟩
  exact ⟨sourcePoint, hsourcePoint, rfl⟩

/-- The exact-image family retains its source index injectively all the way
back to the normalized hierarchy family. -/
theorem imageData_sourceParent_injective
    (geometry : PureWZ2Proposition64Lemma35GeometricData
      output hsourceSmall) :
    Function.Injective geometry.imageData.image.sourceParent := by
  intro first second equality
  change geometry.selectedSource.embedding first =
    geometry.selectedSource.embedding second at equality
  exact geometry.selectedSource.embedding.injective equality

/-- The final ED family embeds injectively in the original normalized source
family through the exact ED, isotropic, and affine-image provenance maps. -/
def finalSourceEmbedding
    (geometry : PureWZ2Proposition64Lemma35GeometricData
      output hsourceSmall)
    {K : ENNReal}
    (ed : PureWZ2Proposition64PaperEDCleanupData
      geometry.cleanup.finalShading K) :
    Fin ed.subfamily.family.card ↪ Fin output.source.family.card where
  toFun := fun index => geometry.imageData.image.sourceParent
    (geometry.cleanup.sourceParent (ed.sourceParent index))
  inj' := by
    intro first second equality
    have himage := geometry.imageData_sourceParent_injective equality
    have hcleanupInjective :
        Function.Injective geometry.cleanup.sourceParent := by
      rw [geometry.cleanup.sourceParent_eq]
      exact Function.injective_id
    have hparent := hcleanupInjective himage
    have hedInjective : Function.Injective ed.sourceParent := by
      rw [ed.sourceParent_eq]
      exact ed.subfamily.embedding.injective
    exact hedInjective hparent

/-- Every point of the selected short-slab shading remains in the exact slab
used by the affine normalization. -/
theorem selectedShading_height
    (geometry : PureWZ2Proposition64Lemma35GeometricData
      output hsourceSmall) :
    ∀ point ∈ geometry.selectedShading.union,
      point 2 ∈ Set.Icc
        (output.prepared.slab.center - output.prepared.slab.halfHeight)
        (output.prepared.slab.center + output.prepared.slab.halfHeight) := by
  rintro point ⟨index, hpoint⟩
  have hslab := output.prepared.slab.carrier_eq
    (geometry.selectedSource.embedding index)
  have hpoint' : point ∈ output.prepared.slab.shading.carrier
      (geometry.selectedSource.embedding index) := hpoint
  rw [hslab, output.prepared.slab.slab_eq] at hpoint'
  exact hpoint'.2

/-- The ordinary all-height bounds survive the short-slab restriction because
the restricted raw slope is literally the same function. -/
theorem restrictedGlobalBounds
    (_geometry : PureWZ2Proposition64Lemma35GeometricData
      output hsourceSmall) :
    PureWZ2RawC2GlobalBoundData output.prepared.restrictedRaw where
  value_bound := by
    intro z
    rw [output.prepared.restrictedRaw_slope]
    exact output.globalBounds.value_bound z
  first_derivative_bound := by
    intro z
    rw [output.prepared.restrictedRaw_slope]
    exact output.globalBounds.first_derivative_bound z
  second_derivative_bound := by
    intro z
    rw [output.prepared.restrictedRaw_slope]
    exact output.globalBounds.second_derivative_bound z

/-- The all-slab AD receipt restricts from the terminal hierarchy shading to
the exact short-slab shading used by Proposition 6.4. -/
theorem restrictedGlobalSlabAD
    (_geometry : PureWZ2Proposition64Lemma35GeometricData
      output hsourceSmall) :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      PureWZ2PaperADSet1
        (globalGrainProjection output.prepared.restrictedRaw.slope
          (globalGrainSlab output.prepared.slab.shading.union z sourceDelta))
        sourceDelta (1 - sigma)
          (24000 * Kakeya.realRpowENN sourceDelta (-workLoss)) := by
  intro z hz
  rw [output.prepared.restrictedRaw_slope]
  apply (output.raw_global_slab_ad z hz).mono
  apply Set.image_mono
  intro point hpoint
  exact ⟨⟨output.prepared.slab.subshading.union_subset hpoint.1.1,
    hpoint.1.2⟩, hpoint.2⟩

/-- The deterministic common-window translation has bounded second
horizontal coordinate, as required by the slab-AD transport. -/
theorem translation_one_abs_le_two
    (geometry : PureWZ2Proposition64Lemma35GeometricData
      output hsourceSmall) :
    |geometry.common.translation 1| ≤ 2 := by
  rw [geometry.common.translation_eq]
  let index := geometry.common.window.2
  change |(point3 (-pureWZ2Proposition64WindowCenter
      geometry.common.window.1)
      (-pureWZ2Proposition64WindowCenter index) 0) 1| ≤ 2
  have hone : (point3 (-pureWZ2Proposition64WindowCenter
      geometry.common.window.1)
      (-pureWZ2Proposition64WindowCenter index) 0) 1 =
      -pureWZ2Proposition64WindowCenter index := by
    simp [point3]
  rw [hone]
  simp only [pureWZ2Proposition64WindowCenter]
  have hindexNonneg : 0 ≤ (index : ℝ) := by positivity
  have hindex : (index : ℝ) ≤ 6 := by
    exact_mod_cast Nat.le_pred_of_lt index.isLt
  rw [abs_le]
  constructor <;> linarith

/-- Run the exact paper-ED selection on the geometric prefix.  The only
external geometric input is the parameter Frostman bound on the literal
common-window source family; all scale and line-class facts come from the
stored prefix. -/
theorem exists_paperED
    (geometry : PureWZ2Proposition64Lemma35GeometricData
      output hsourceSmall)
    (hFrostman : TubeParameterFrostmanBound geometry.selectedSource.family
      (Kakeya.realRpowENN sourceDelta (-workLoss))) :
    let K := Kakeya.realRpowENN sourceDelta (-workLoss) *
      Kakeya.realRpowENN
        (24000 * output.prepared.normalization *
          pureWZ2Proposition64Lemma35FinalDelta sourceDelta /
            output.prepared.slab.halfHeight) 2 *
      geometry.selectedSource.family.enncard
    Nonempty (PureWZ2Proposition64PaperEDCleanupData
      geometry.cleanup.finalShading K) := by
  dsimp only
  refine pureWZ2Proposition64_exactPaperEDSelection
    output.prepared.restrictedRaw.slope output.prepared.slab.center
    output.prepared.slab.anchorHeight output.prepared.slab.halfHeight
    output.prepared.normalization geometry.common.translation
    geometry.selectedSource.family geometry.common.translation_height
    output.prepared.slab.halfHeight_pos
    output.prepared.slab.halfHeight_le_one output.normalization_nine
    output.prepared.normalized.anchor_value_bound ?_
    (output.source.line_class.subfamily geometry.selectedSource)
    geometry.imageData.line_class geometry.exactShading
    geometry.cleanup.popular geometry.scales.width_pos
    geometry.scales.imageDelta_pos geometry.scales.finalDelta_pos
    geometry.scales.finalDelta_le_one_ninety_six geometry.scales.scale_one
    geometry.scales.retube_radius geometry.scales.box_scale _ hFrostman
    (by
      rw [output.normalization_eq]
      exact geometry.scales.parameter_window_lower)
    (by
      rw [output.normalization_eq]
      exact geometry.scales.parameter_window_upper)
  · have hcenter := output.prepared.slab.source_window 0 (by norm_num)
    rw [mul_zero, add_zero] at hcenter
    exact abs_le.mpr hcenter

/-- The paper-ED output carries the final line-class certificate directly; no
line-class statement about discarded zero-mass ambient tubes is needed. -/
theorem paperED_lineClass
    (geometry : PureWZ2Proposition64Lemma35GeometricData
      output hsourceSmall)
    {K : ENNReal}
    (ed : PureWZ2Proposition64PaperEDCleanupData
      geometry.cleanup.finalShading K) :
    WZ1PaperIsLineClass ed.subfamily.family := by
  apply ed.lineClass_of_positiveSource
  apply pureWZ2Proposition64_positiveIsotropicFamily_lineClass
    geometry.cleanup.popular geometry.imageData.line_class
    geometry.scales.width_pos geometry.scales.imageDelta_pos
    geometry.scales.finalDelta_pos
    geometry.scales.finalDelta_le_one_ninety_six geometry.scales.scale_one
    geometry.scales.retube_radius geometry.scales.box_scale

/-- The stored ED selection and exact-image provenance determine the full
source-parent provenance of the final selected family. -/
theorem exists_finalProvenance
    (geometry : PureWZ2Proposition64Lemma35GeometricData
      output hsourceSmall)
    {K : ENNReal}
    (ed : PureWZ2Proposition64PaperEDCleanupData
      geometry.cleanup.finalShading K) :
    Nonempty (PureWZ2Proposition64FinalProvenanceData
      (normalized := output.prepared.normalized)
      (image := geometry.imageData.image)
      (exactCarrier_provenance := geometry.exactCarrier_provenance)
      (cleanup := geometry.cleanup) ed) :=
  pureWZ2Proposition64_finalProvenance
    (normalized := output.prepared.normalized)
    (image := geometry.imageData.image)
    (exactCarrier_provenance := geometry.exactCarrier_provenance)
    (cleanup := geometry.cleanup) ed

/-- The geometric prefix already contains the full final local-grain package
before the terminal loss constant is absorbed. -/
noncomputable def cleanupLocal
    (geometry : PureWZ2Proposition64Lemma35GeometricData
      output hsourceSmall) :
    PureWZ2LocalGrainData geometry.cleanup.finalShading sigma
      (192 * Kakeya.realRpowENN sourceDelta (-workLoss)) :=
  geometry.cleanup.toExactLocalGrainData geometry.selectedLocal
    geometry.exactData output.prepared.slab.halfHeight_le_one
    (by
      rw [output.normalization_eq]
      exact geometry.scales.scale_large)
    geometry.scales.source_scale
    (by
      intro point
      rcases point.property with ⟨index, hpoint⟩
      exact output.hierarchy.planeMap_vertical_bound
        ⟨point, ⟨geometry.selectedSource.embedding index,
          output.prepared.slab.subshading
            (geometry.selectedSource.embedding index) hpoint⟩⟩)
    geometry.scales.incidence_budget geometry.scales.projection_budget

/-- The vertical normal bound belongs to the same exact cleanup witness as
`cleanupLocal`. -/
theorem cleanupLocal_vertical_bound
    (geometry : PureWZ2Proposition64Lemma35GeometricData
      output hsourceSmall) :
    ∀ point, |geometry.cleanupLocal.planeMap point 2| ≤ 1 / 2 := by
  apply geometry.cleanup.toExactLocalGrainData_vertical_bound
    geometry.selectedLocal geometry.exactData
    output.prepared.slab.halfHeight_le_one
    (by
      rw [output.normalization_eq]
      exact geometry.scales.scale_large)
    geometry.scales.source_scale
    (by
      intro point
      rcases point.property with ⟨index, hpoint⟩
      exact output.hierarchy.planeMap_vertical_bound
        ⟨point, ⟨geometry.selectedSource.embedding index,
          output.prepared.slab.subshading
            (geometry.selectedSource.embedding index) hpoint⟩⟩)
    geometry.scales.incidence_budget geometry.scales.projection_budget
    geometry.scales.vertical_budget

/-- The genuinely quantitative tail left after the exact geometry and paper-ED
selection have been fixed.  Each field concerns the same final shading. -/
structure FinalQuantitativeReceipt
    (geometry : PureWZ2Proposition64Lemma35GeometricData
      output hsourceSmall)
    {K : ENNReal}
    (ed : PureWZ2Proposition64PaperEDCleanupData
      geometry.cleanup.finalShading K)
    (outputLoss : ℝ) where
  nearbyLoss : ℝ
  nearby : WZ2PaperPureCWAAtNearbyScales ed.subfamily.family
    (Kakeya.realRpowENN
      (pureWZ2Proposition64Lemma35FinalDelta sourceDelta) (-nearbyLoss))
  nearby_le_output : nearbyLoss ≤ outputLoss
  cwa_absorption :
    4 * Kakeya.realRpowENN
        (pureWZ2Proposition64Lemma35FinalDelta sourceDelta) (-nearbyLoss) ≤
      Kakeya.realRpowENN
        (pureWZ2Proposition64Lemma35FinalDelta sourceDelta) (-outputLoss)
  dense : ed.finalShading.IsLambdaDense
    (Kakeya.realRpowENN
      (pureWZ2Proposition64Lemma35FinalDelta sourceDelta) outputLoss)
  volume_upper : MeasureTheory.volume ed.finalShading.union ≤
    Kakeya.realRpowENN
      (pureWZ2Proposition64Lemma35FinalDelta sourceDelta)
        (sigma - outputLoss)
  local_constant_absorption :
    192 * Kakeya.realRpowENN sourceDelta (-workLoss) ≤
      Kakeya.realRpowENN
        (pureWZ2Proposition64Lemma35FinalDelta sourceDelta) (-outputLoss)
  global_constant_absorption :
    7077888 * (24000 * Kakeya.realRpowENN sourceDelta (-workLoss)) ≤
      Kakeya.realRpowENN
        (pureWZ2Proposition64Lemma35FinalDelta sourceDelta) (-outputLoss)

/-- Close all deterministic Proposition 6.4 geometry from one normalized
hierarchy and one paper-ED selection.  The remaining arguments are precisely
the final quantitative Lemma-3.5 receipts; common-window, affine-image,
isotropic, ED, provenance, and local-grain data are not callback inputs. -/
theorem assembleVerticalRediscretization
    (geometry : PureWZ2Proposition64Lemma35GeometricData
      output hsourceSmall)
    {K : ENNReal}
    (ed : PureWZ2Proposition64PaperEDCleanupData
      geometry.cleanup.finalShading K)
    (hfinalNonempty : ed.subfamily.family.Nonempty)
    {outputLoss : ℝ}
    (receipt : FinalQuantitativeReceipt geometry ed outputLoss) :
    Nonempty (PureWZ2VerticalRediscretizationData
      output.prepared.normalized
      (pureWZ2Proposition64Lemma35FinalDelta sourceDelta) outputLoss) := by
  rcases geometry.exists_finalProvenance ed with ⟨provenance⟩
  apply pureWZ2Proposition64_assembleVerticalRediscretization
    geometry.exactCarrier_provenance ed provenance
    geometry.restrictedGlobalBounds
    output.valueBudget output.firstBudget output.secondBudget
    (by
      rintro point ⟨index, hpoint⟩
      rw [output.prepared.slab.carrier_eq,
        output.prepared.slab.slab_eq] at hpoint
      exact hpoint.2)
    geometry.restrictedGlobalSlabAD
    geometry.translation_one_abs_le_two (geometry.paperED_lineClass ed)
    (geometry.scales.finalDelta_le_one_ninety_six.trans (by norm_num))
    geometry.scales.finalDelta_le_one_ninety_six receipt.nearby
    receipt.nearby_le_output receipt.cwa_absorption receipt.dense
    receipt.volume_upper hfinalNonempty
    geometry.cleanupLocal geometry.cleanupLocal_vertical_bound
    (by
      have hscalePos : 0 < pureWZ2Proposition64Lemma35Scale :=
        lt_of_lt_of_le zero_lt_one geometry.scales.scale_one
      have hquotient :
          2 * pureWZ2Proposition64Lemma35FinalDelta sourceDelta /
              pureWZ2Proposition64Lemma35Scale = 90 * sourceDelta := by
        unfold pureWZ2Proposition64Lemma35FinalDelta
        field_simp [hscalePos.ne']
        ring
      rw [hquotient]
      nlinarith [output.halfHeight_slab_ad,
        output.prepared.slab.halfHeight_pos,
        output.source.extremal.delta_pos])
    (by
      rw [output.normalization_eq]
      exact geometry.scales.analytic_scale_le)
    receipt.local_constant_absorption receipt.global_constant_absorption

end PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData

end Kakeya.Assouad

end
