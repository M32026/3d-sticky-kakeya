import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64CroppedTopLevelCWA
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64CriticalFloorAssembly

/-!
# Top-level CWA on the exact Proposition 6.4 output

The quantitative mass ledger gives the weighted cardinality needed to
restrict the source top-level CWA.  The combined physical affine map then
transports that restricted cropped CWA to the final centered family.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

namespace PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData

variable
    {sigma workLoss sourceDelta targetDelta₀ : ℝ}
    {quantitativeOutput : PureWZ2QuantitativeNormalizedHierarchyOutput
      sigma workLoss sourceDelta}
    {hsourceSmall : sourceDelta ≤
      pureWZ2Proposition64Lemma35SourceCeiling targetDelta₀}

/-- The exact source-cardinality weight retained by the R3-to-R4 mass
ledger. -/
noncomputable def pureWZ2Proposition64TopWeight : ENNReal :=
  pureWZ2Proposition64QuantitativeMassCoefficient quantitativeOutput *
    Kakeya.realRpowENN sourceDelta 2

/-- The target-cardinality coefficient obtained from the ED mass loss and
the uniform quadratic upper bound for cropped target carriers. -/
noncomputable def pureWZ2Proposition64TopRetention (K : ENNReal) : ENNReal :=
  (147 * (K + 1)) *
    (55296 * Kakeya.deltaTubeVolume 1 *
      Kakeya.realRpowENN
        (pureWZ2Proposition64Lemma35FinalDelta sourceDelta) 2)

/-- The cropped carrier factor for the fixed Proposition-6.4 map. -/
noncomputable def pureWZ2Proposition64TopCarrierFactor : ℝ :=
  12 * pureWZ2Proposition64Lemma35Scale /
      quantitativeOutput.normalized.prepared.slab.halfHeight + 4

/-- The final selected family retains source cardinality with the exact
coefficient already present in the quantitative mass ledger. -/
theorem paperED_weighted_cardinality_retention
    (geometry : PureWZ2Proposition64Lemma35GeometricData
      quantitativeOutput.normalized hsourceSmall)
    {K : ENNReal}
    (ed : PureWZ2Proposition64PaperEDCleanupData
      geometry.cleanup.finalShading K) :
    pureWZ2Proposition64TopWeight
        (quantitativeOutput := quantitativeOutput) *
        quantitativeOutput.normalized.source.family.enncard ≤
      pureWZ2Proposition64TopRetention (sourceDelta := sourceDelta) K *
        ed.subfamily.family.enncard := by
  have hsourceSmall' : sourceDelta ≤ 1 / 12 := by
    nlinarith [geometry.scales.sourceDelta_small]
  have hsourceBody :
      quantitativeOutput.normalized.source.family.enncard *
          Kakeya.realRpowENN sourceDelta 2 ≤
        (wz1PaperBodyFamily
          quantitativeOutput.normalized.source.family).mass :=
    pureWZ2_paperBody_mass_lower
      quantitativeOutput.normalized.source.extremal.delta_pos hsourceSmall'
      quantitativeOutput.normalized.source.line_class
  have htargetMass :
      ed.finalShading.mass ≤
        (55296 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN
            (pureWZ2Proposition64Lemma35FinalDelta sourceDelta) 2 *
          ed.subfamily.family.enncard := by
    simpa using wz2_paper_shading_mass_upper
      geometry.scales.finalDelta_pos
      (geometry.scales.finalDelta_le_one_ninety_six.trans (by norm_num))
      (geometry.paperED_lineClass ed) ed.finalShading
  calc
    pureWZ2Proposition64TopWeight
          (quantitativeOutput := quantitativeOutput) *
          quantitativeOutput.normalized.source.family.enncard =
        pureWZ2Proposition64QuantitativeMassCoefficient quantitativeOutput *
          (quantitativeOutput.normalized.source.family.enncard *
            Kakeya.realRpowENN sourceDelta 2) := by
      unfold pureWZ2Proposition64TopWeight
      ring
    _ ≤ pureWZ2Proposition64QuantitativeMassCoefficient quantitativeOutput *
          (wz1PaperBodyFamily
            quantitativeOutput.normalized.source.family).mass := by gcongr
    _ ≤ 147 * (K + 1) * ed.finalShading.mass :=
      geometry.paperED_quantitative_mass_ledger quantitativeOutput ed
    _ ≤ 147 * (K + 1) *
          ((55296 * Kakeya.deltaTubeVolume 1) *
            Kakeya.realRpowENN
              (pureWZ2Proposition64Lemma35FinalDelta sourceDelta) 2 *
            ed.subfamily.family.enncard) := by gcongr
    _ = pureWZ2Proposition64TopRetention (sourceDelta := sourceDelta) K *
          ed.subfamily.family.enncard := by
      unfold pureWZ2Proposition64TopRetention
      ring

theorem pureWZ2Proposition64TopWeight_ne_zero :
    (pureWZ2Proposition64TopWeight
      (quantitativeOutput := quantitativeOutput)) ≠ 0 := by
  unfold pureWZ2Proposition64TopWeight
    pureWZ2Proposition64QuantitativeMassCoefficient
  repeat' apply mul_ne_zero
  · exact (ENNReal.ofReal_pos.mpr
      (pow_pos pureWZ2Proposition64Lemma35Scale_pos 3)).ne'
  · exact (ENNReal.ofReal_pos.mpr
      (by
        have hwidthPos : 0 < pureWZ2Proposition64Lemma35Width := by
          unfold pureWZ2Proposition64Lemma35Width
          exact one_div_pos.mpr (mul_pos (by norm_num)
            pureWZ2Proposition64Lemma35Scale_pos)
        exact div_pos (pow_pos hwidthPos 3) (by norm_num))).ne'
  · apply (ENNReal.ofReal_pos.mpr ?_).ne'
    exact one_div_pos.mpr (mul_pos
      (lt_of_lt_of_le (by norm_num)
        quantitativeOutput.normalized.normalization_nine)
      quantitativeOutput.normalized.prepared.slab.halfHeight_pos)
  · apply (ENNReal.ofReal_pos.mpr ?_).ne'
    nlinarith [quantitativeOutput.normalized.prepared.slab.halfHeight_pos]
  · exact (ENNReal.ofReal_pos.mpr (by norm_num : (0 : ℝ) < 1 / 6)).ne'
  · exact (ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos
        quantitativeOutput.normalized.source.extremal.delta_pos _)).ne'
  · exact (ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos
        quantitativeOutput.normalized.source.extremal.delta_pos 2)).ne'

theorem pureWZ2Proposition64TopWeight_ne_top :
    (pureWZ2Proposition64TopWeight
      (quantitativeOutput := quantitativeOutput)) ≠ ⊤ := by
  unfold pureWZ2Proposition64TopWeight
    pureWZ2Proposition64QuantitativeMassCoefficient
  have hdensity : Kakeya.realRpowENN sourceDelta
      quantitativeOutput.densityLoss ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  have hsourceScale : Kakeya.realRpowENN sourceDelta 2 ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  exact ENNReal.mul_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top <|
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top <|
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top <|
          ENNReal.mul_ne_top ENNReal.ofReal_ne_top <|
            ENNReal.mul_ne_top ENNReal.ofReal_ne_top hdensity)
    hsourceScale

/-- The exact final ED family has a top-level cropped CWA obtained entirely
from the original source top-level CWA and the R4 mass/provenance ledger. -/
theorem paperED_topLevelCWA
    (geometry : PureWZ2Proposition64Lemma35GeometricData
      quantitativeOutput.normalized hsourceSmall)
    {K : ENNReal}
    (ed : PureWZ2Proposition64PaperEDCleanupData
      geometry.cleanup.finalShading K) :
    WZ2PaperConvexWolffBound ed.subfamily.family
      ((ENNReal.ofReal
            (quantitativeOutput.normalized.prepared.normalization *
              quantitativeOutput.normalized.prepared.slab.halfHeight /
                pureWZ2Proposition64Lemma35Scale ^ 3) *
          ENNReal.ofReal
            (27 *
              (2 * pureWZ2Proposition64TopCarrierFactor
                (quantitativeOutput := quantitativeOutput) - 1) ^ 3)) *
        (((pureWZ2Proposition64TopWeight
              (quantitativeOutput := quantitativeOutput))⁻¹ *
            pureWZ2Proposition64TopRetention
              (sourceDelta := sourceDelta) K) *
          Kakeya.realRpowENN sourceDelta
            (-quantitativeOutput.normalized.inputLoss))) := by
  rcases geometry.exists_finalProvenance ed with ⟨provenance⟩
  let sourceIndex := geometry.finalSourceEmbedding ed
  have hcentered : ∀ index,
      wz2PaperTubeMidpoint (ed.subfamily.family.tube index) =
        wz1TubeAxisZeroPoint (ed.subfamily.family.tube index) := by
    intro index
    have hfinalLine := geometry.paperED_lineClass ed index
    rw [ed.tube_provenance index] at hfinalLine
    rw [ed.tube_provenance index]
    apply pureWZ2Proposition64IsotropicRebasedPaperTube_midpoint
    simpa [pureWZ2Proposition64IsotropicPaperFamily,
      pureWZ2Proposition64IsotropicRebasedPaperTube,
      pureWZ2Proposition64IsotropicPaperTube] using hfinalLine.vertical
  apply pureWZ2Proposition64_croppedTopLevelCWA_of_combined_image
    sourceIndex quantitativeOutput.normalized.prepared.restrictedRaw.slope
    quantitativeOutput.normalized.prepared.slab.center
    quantitativeOutput.normalized.prepared.slab.anchorHeight
    geometry.common.translation geometry.cleanup.popular.center
    quantitativeOutput.normalized.source.extremal.delta_pos
    geometry.scales.finalDelta_pos
    (geometry.scales.finalDelta_le_one_ninety_six.trans (by norm_num))
    quantitativeOutput.normalized.prepared.slab.halfHeight_pos
    quantitativeOutput.normalized.prepared.slab.halfHeight_le_one
    (by linarith [quantitativeOutput.normalized.normalization_nine])
    pureWZ2Proposition64Lemma35Scale_pos
    geometry.common.translation_height
  · have hcenter := quantitativeOutput.normalized.prepared.slab.source_window
      0 (by norm_num)
    rw [mul_zero, add_zero] at hcenter
    exact abs_le.mpr hcenter
  · exact geometry.cleanup.popular.center_mem 2
  · exact quantitativeOutput.normalized.prepared.normalized.anchor_value_bound
  · exact quantitativeOutput.normalized.source.line_class
  · exact geometry.paperED_lineClass ed
  · exact hcentered
  · intro index
    change _ = _ '' (_ '' tubeAxisLine
      (quantitativeOutput.normalized.source.family.tube (sourceIndex index)))
    have hsource : sourceIndex index = provenance.sourceParent index := by
      simp [sourceIndex, finalSourceEmbedding, provenance.sourceParent_eq]
    rw [hsource]
    exact provenance.axis_provenance index
  · unfold pureWZ2Proposition64TopCarrierFactor
    have hratioPos : 0 < 12 * pureWZ2Proposition64Lemma35Scale /
        quantitativeOutput.normalized.prepared.slab.halfHeight := by
      exact div_pos (mul_pos (by norm_num)
        pureWZ2Proposition64Lemma35Scale_pos)
        quantitativeOutput.normalized.prepared.slab.halfHeight_pos
    linarith
  · unfold pureWZ2Proposition64TopCarrierFactor
    linarith
  · unfold pureWZ2Proposition64TopCarrierFactor
      pureWZ2Proposition64Lemma35FinalDelta
    have hfinalPos := geometry.scales.finalDelta_pos
    have hhalfPos :=
      quantitativeOutput.normalized.prepared.slab.halfHeight_pos
    have hscalePos := pureWZ2Proposition64Lemma35Scale_pos
    have hratioPos : 0 < 12 * pureWZ2Proposition64Lemma35Scale /
        quantitativeOutput.normalized.prepared.slab.halfHeight := by
      exact div_pos (mul_pos (by norm_num) hscalePos) hhalfPos
    calc
      180 * pureWZ2Proposition64Lemma35Scale * sourceDelta =
          4 * (45 * pureWZ2Proposition64Lemma35Scale * sourceDelta) := by ring
      _ ≤ (12 * pureWZ2Proposition64Lemma35Scale /
              quantitativeOutput.normalized.prepared.slab.halfHeight + 4) *
            (45 * pureWZ2Proposition64Lemma35Scale * sourceDelta) := by
        apply mul_le_mul_of_nonneg_right
        · linarith [hratioPos]
        · exact hfinalPos.le
  · exact quantitativeOutput.normalized.source.top_level_cwa
  · exact pureWZ2Proposition64TopWeight_ne_zero
      (quantitativeOutput := quantitativeOutput)
  · exact pureWZ2Proposition64TopWeight_ne_top
      (quantitativeOutput := quantitativeOutput)
  · exact geometry.paperED_weighted_cardinality_retention ed

end PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData

end Kakeya.Assouad

end
