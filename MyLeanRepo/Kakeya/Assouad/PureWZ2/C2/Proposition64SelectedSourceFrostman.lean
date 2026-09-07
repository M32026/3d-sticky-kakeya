import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64CriticalFloorAssembly
import MyLeanRepo.Kakeya.Assouad.PropStickyConvexWolffSubfamilyTransfer

/-!
# Exact selected-source Frostman prefix for Proposition 6.4

The common-window family used by `exists_paperED` is a genuine subfamily of
the normalized hierarchy source.  Restricting the source paper CWA first
requires a cardinality-retention estimate for that exact subfamily.  This
module derives that estimate from one quantitative indexed-mass receipt and
then absorbs the closed paper-carrier prism constant `3200`.

The receipt below is deliberately attached to the supplied normalized output
and its literal common-window geometry.  It does not permit replacing the
configuration, shading, slope, or affine map.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

namespace PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData

variable
    {sigma workLoss sourceDelta targetDelta₀ : ℝ}
    {output : PureWZ2NormalizedHierarchyOutput
      sigma workLoss sourceDelta}
    {hsourceSmall : sourceDelta ≤
      pureWZ2Proposition64Lemma35SourceCeiling targetDelta₀}

/-- The mass weight retained before the common-window cardinality comparison. -/
noncomputable def selectedSourceWeight
    (geometry : PureWZ2Proposition64Lemma35GeometricData
      output hsourceSmall)
    (densityLoss : ℝ) : ENNReal :=
  ENNReal.ofReal (2 * output.prepared.slab.halfHeight) *
    (ENNReal.ofReal (1 / 6) *
      Kakeya.realRpowENN sourceDelta densityLoss)

/-- The fixed paper-carrier cost in the common-window cardinality comparison. -/
noncomputable def selectedSourceRetention : ENNReal :=
  147 * (55296 * Kakeya.deltaTubeVolume 1)

/-- The exact quantitative datum missing from a plain normalized hierarchy.

The first field is the R3 indexed-mass retention on the literal hierarchy
shading.  The second field is the family-free scalar absorption needed after
the `3200` parameter-prism estimate.  No runtime family can be substituted:
both fields are indexed by `output` and its exact `geometry`. -/
structure SelectedSourceFrostmanReceipt
    (geometry : PureWZ2Proposition64Lemma35GeometricData
      output hsourceSmall) where
  densityLoss : ℝ
  source_bounded_base : HasBoundedBase output.source.family 4
  normalized_mass_retention :
    ENNReal.ofReal (1 / 6) *
        (Kakeya.realRpowENN sourceDelta densityLoss *
          (wz1PaperBodyFamily output.source.family).mass) ≤
      output.hierarchy.shading.mass
  frostman_absorption :
    3200 *
        ((geometry.selectedSourceWeight densityLoss)⁻¹ *
            selectedSourceRetention *
          Kakeya.realRpowENN sourceDelta (-output.inputLoss)) ≤
      Kakeya.realRpowENN sourceDelta (-workLoss)

namespace SelectedSourceFrostmanReceipt

/-- Project the quantitative R3 mass field and a `3200` paper-CWA scalar
absorption to the exact selected-source receipt. -/
noncomputable def ofQuantitative3200
    (quantitativeOutput : PureWZ2QuantitativeNormalizedHierarchyOutput
      sigma workLoss sourceDelta)
    {hsourceSmall : sourceDelta ≤
      pureWZ2Proposition64Lemma35SourceCeiling targetDelta₀}
    (geometry : PureWZ2Proposition64Lemma35GeometricData
      quantitativeOutput.normalized hsourceSmall)
    (sourceBoundedBase :
      HasBoundedBase quantitativeOutput.normalized.source.family 4)
    (absorption :
      3200 *
          ((geometry.selectedSourceWeight
              quantitativeOutput.densityLoss)⁻¹ *
              selectedSourceRetention *
            Kakeya.realRpowENN sourceDelta
              (-quantitativeOutput.normalized.inputLoss)) ≤
        Kakeya.realRpowENN sourceDelta (-workLoss)) :
    SelectedSourceFrostmanReceipt geometry where
  densityLoss := quantitativeOutput.densityLoss
  source_bounded_base := sourceBoundedBase
  normalized_mass_retention := quantitativeOutput.normalized_mass_retention
  frostman_absorption := absorption

/-- The older `4232 = 8 * 23^2` prism budget also closes the sharper current
`3200 = 8 * 20^2` selected-source receipt. -/
noncomputable def ofQuantitative4232
    (quantitativeOutput : PureWZ2QuantitativeNormalizedHierarchyOutput
      sigma workLoss sourceDelta)
    {hsourceSmall : sourceDelta ≤
      pureWZ2Proposition64Lemma35SourceCeiling targetDelta₀}
    (geometry : PureWZ2Proposition64Lemma35GeometricData
      quantitativeOutput.normalized hsourceSmall)
    (sourceBoundedBase :
      HasBoundedBase quantitativeOutput.normalized.source.family 4)
    (absorption :
      4232 *
          ((geometry.selectedSourceWeight
              quantitativeOutput.densityLoss)⁻¹ *
              selectedSourceRetention *
            Kakeya.realRpowENN sourceDelta
              (-quantitativeOutput.normalized.inputLoss)) ≤
        Kakeya.realRpowENN sourceDelta (-workLoss)) :
    SelectedSourceFrostmanReceipt geometry :=
  ofQuantitative3200 quantitativeOutput geometry sourceBoundedBase <|
    absorption.trans' <| by
    gcongr
    norm_num

end SelectedSourceFrostmanReceipt

theorem selectedSourceWeight_pos
    (geometry : PureWZ2Proposition64Lemma35GeometricData
      output hsourceSmall)
    (densityLoss : ℝ) :
    0 < geometry.selectedSourceWeight densityLoss := by
  unfold selectedSourceWeight
  apply ENNReal.mul_pos
  · apply (ENNReal.ofReal_pos.mpr ?_).ne'
    nlinarith [output.prepared.slab.halfHeight_pos]
  · exact (ENNReal.mul_pos (by norm_num) <|
      (ENNReal.ofReal_pos.mpr
        (Real.rpow_pos_of_pos output.source.extremal.delta_pos _)).ne').ne'

theorem selectedSourceWeight_ne_top
    (geometry : PureWZ2Proposition64Lemma35GeometricData
      output hsourceSmall)
    (densityLoss : ℝ) :
    geometry.selectedSourceWeight densityLoss ≠ ⊤ := by
  unfold selectedSourceWeight
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top <|
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by
      simp [Kakeya.realRpowENN])

/-- The quantitative hierarchy mass forces cardinality retention on the exact
common-window source selected by `lemma35GeometricData`. -/
theorem selectedSource_weighted_cardinality
    (geometry : PureWZ2Proposition64Lemma35GeometricData
      output hsourceSmall)
    (receipt : SelectedSourceFrostmanReceipt geometry) :
    geometry.selectedSourceWeight receipt.densityLoss *
        output.source.family.enncard ≤
      selectedSourceRetention * geometry.selectedSource.family.enncard := by
  have hsourceDeltaSmall : sourceDelta ≤ 1 / 24 := by
    nlinarith [geometry.scales.sourceDelta_small]
  have hsourceBody :
      output.source.family.enncard *
          Kakeya.realRpowENN sourceDelta 2 ≤
        (wz1PaperBodyFamily output.source.family).mass :=
    pureWZ2_paperBody_mass_lower output.source.extremal.delta_pos
      (hsourceDeltaSmall.trans (by norm_num))
      output.source.line_class
  have hselectedMass :
      geometry.selectedShading.mass ≤
        (55296 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN sourceDelta 2 *
            geometry.selectedSource.family.enncard :=
    wz2_paper_shading_mass_upper
      output.source.extremal.delta_pos hsourceDeltaSmall
      (output.source.line_class.subfamily geometry.selectedSource)
      geometry.selectedShading
  have hscalePos :
      0 < Kakeya.realRpowENN sourceDelta 2 :=
    ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos output.source.extremal.delta_pos 2)
  have hscaleTop :
      Kakeya.realRpowENN sourceDelta 2 ≠ ⊤ := by
    simp [Kakeya.realRpowENN]
  apply (ENNReal.mul_le_mul_iff_left hscalePos.ne' hscaleTop).mp
  calc
    (geometry.selectedSourceWeight receipt.densityLoss *
          output.source.family.enncard) *
        Kakeya.realRpowENN sourceDelta 2 =
        ENNReal.ofReal (2 * output.prepared.slab.halfHeight) *
          (ENNReal.ofReal (1 / 6) *
            Kakeya.realRpowENN sourceDelta receipt.densityLoss) *
          (output.source.family.enncard *
            Kakeya.realRpowENN sourceDelta 2) := by
      unfold selectedSourceWeight
      ring
    _ ≤ ENNReal.ofReal (2 * output.prepared.slab.halfHeight) *
          (ENNReal.ofReal (1 / 6) *
            Kakeya.realRpowENN sourceDelta receipt.densityLoss) *
          (wz1PaperBodyFamily output.source.family).mass := by
      gcongr
    _ = ENNReal.ofReal (2 * output.prepared.slab.halfHeight) *
          (ENNReal.ofReal (1 / 6) *
            (Kakeya.realRpowENN sourceDelta receipt.densityLoss *
              (wz1PaperBodyFamily output.source.family).mass)) := by
      ring
    _ ≤ ENNReal.ofReal (2 * output.prepared.slab.halfHeight) *
          output.hierarchy.shading.mass := by
      gcongr
      exact receipt.normalized_mass_retention
    _ ≤ 3 * output.prepared.slab.shading.mass :=
      output.prepared.slab.mass_fraction
    _ ≤ 3 * (49 * geometry.selectedShading.mass) := by
      gcongr
      rw [geometry.selectedShading_mass]
      exact geometry.common.retained_mass
    _ = 147 * geometry.selectedShading.mass := by ring
    _ ≤ 147 *
          ((55296 * Kakeya.deltaTubeVolume 1) *
            Kakeya.realRpowENN sourceDelta 2 *
              geometry.selectedSource.family.enncard) := by
      gcongr
    _ = (selectedSourceRetention *
          geometry.selectedSource.family.enncard) *
        Kakeya.realRpowENN sourceDelta 2 := by
      unfold selectedSourceRetention
      ring

/-- The `3200` paper-CWA prism estimate is absorbed on the literal selected
source consumed by `exists_paperED`. -/
theorem selectedSource_frostman
    (geometry : PureWZ2Proposition64Lemma35GeometricData
      output hsourceSmall)
    (receipt : SelectedSourceFrostmanReceipt geometry) :
    TubeParameterFrostmanBound geometry.selectedSource.family
      (Kakeya.realRpowENN sourceDelta (-workLoss)) := by
  have hselectedCWA :
      WZ2PaperConvexWolffBound geometry.selectedSource.family
        (((geometry.selectedSourceWeight receipt.densityLoss)⁻¹ *
            selectedSourceRetention) *
          Kakeya.realRpowENN sourceDelta (-output.inputLoss)) :=
    output.source.top_level_cwa.subfamily_of_weighted_cardinality
      geometry.selectedSource
      (geometry.selectedSourceWeight_pos receipt.densityLoss).ne'
      (geometry.selectedSourceWeight_ne_top receipt.densityLoss)
      (geometry.selectedSource_weighted_cardinality receipt)
  have hraw :=
    pureWZ2Proposition64_parameterFrostman_of_croppedCWA
      output.source.extremal.delta_pos geometry.selectedSource.family
      (output.source.line_class.subfamily geometry.selectedSource)
      (((geometry.selectedSourceWeight receipt.densityLoss)⁻¹ *
          selectedSourceRetention) *
        Kakeya.realRpowENN sourceDelta (-output.inputLoss))
      hselectedCWA
  intro radius hsourceRadius hradiusOne reference
  exact (hraw radius hsourceRadius hradiusOne reference).trans <| by
    gcongr
    simpa [mul_assoc] using receipt.frostman_absorption

/-- Close the entire exact geometric/ED prefix once the sole quantitative
selected-source receipt has been supplied. -/
theorem exists_paperED_of_selectedSourceReceipt
    (geometry : PureWZ2Proposition64Lemma35GeometricData
      output hsourceSmall)
    (receipt : SelectedSourceFrostmanReceipt geometry) :
    let K := Kakeya.realRpowENN sourceDelta (-workLoss) *
      Kakeya.realRpowENN
        (24000 * output.prepared.normalization *
          pureWZ2Proposition64Lemma35FinalDelta sourceDelta /
            output.prepared.slab.halfHeight) 2 *
      geometry.selectedSource.family.enncard
    Nonempty (PureWZ2Proposition64PaperEDCleanupData
      geometry.cleanup.finalShading K) :=
  geometry.exists_paperED (geometry.selectedSource_frostman receipt)

end PureWZ2NormalizedHierarchyOutput.PureWZ2Proposition64Lemma35GeometricData

end Kakeya.Assouad

end
