import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.AnchoredReferenceScale
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.ScaledReferenceBridge
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.TopScaleSingleParent

/-!
# Nearby-scale assembly from anchored reference scales

Construct all small anchored owner covers, make one simultaneous weighted
selection, produce literal scale witnesses at every reference coordinate,
and join them to the top single-parent witness.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

/-- All data produced by one finite anchored nearby-scale assembly. -/
structure PureWZ2AnchoredNearbyAssemblyData
    {delta : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : Kakeya.Streamlined.TubeShading source}
    (fine : PureWZ2LocalizedDistinctReanchoringData sourceShading)
    (A : ℝ)
    (coordinateCount : ℕ)
    (outputConstant : ENNReal) where
  selected : WZ2PaperPureTubeSubfamily fine.family
  shading : Kakeya.Streamlined.TubeShading selected.family
  subshading :
    ∀ index,
      shading.carrier index ⊆
        sourceShading.carrier
          (fine.sourceIndex (selected.embedding index))
  selectionRetentionConstant : ENNReal
  selectionRetentionConstant_eq :
    selectionRetentionConstant =
      pureWZ2FiniteAnchoredRetentionConstant
        A coordinateCount fine.family.card
  retained_mass_raw :
    sourceShading.mass ≤
      ((fine.cellCount : ENNReal) *
        (fine.distinctnessLoss : ENNReal) *
        selectionRetentionConstant) *
          shading.mass
  literal_cwa :
    WZ2PaperPureCWAAtNearbyScales
      selected.family outputConstant

/--
Finite structural assembly.  All asymptotic choices are exposed as explicit
inequalities on the resulting constants.
-/
theorem pureWZ2_anchored_nearby_assembly
    {delta A : ℝ}
    (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1)
    (hA : 1 ≤ A)
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : Kakeya.Streamlined.TubeShading source}
    (fine : PureWZ2LocalizedDistinctReanchoringData sourceShading)
    (hfineRadius : fine.radius ≤ 1 / 4)
    (coordinateCount : ℕ)
    (coordinateCountPos : 0 < coordinateCount)
    (ratio : ℝ)
    (ratioOne : 1 < ratio)
    (scheduleTop : delta * ratio ^ coordinateCount = 1)
    (smallScale : 200 * A ≤ ratio)
    (inputConstant density outputConstant : ENNReal)
    (density_ne_zero : density ≠ 0)
    (density_ne_top : density ≠ ⊤)
    (sourceDense : sourceShading.IsLambdaDense density)
    (fullFiberData :
      PureWZ2GWZFullFiberStructure
        (A := A) source inputConstant)
    (outputOne : 1 ≤ outputConstant)
    (outputTop : outputConstant ≠ ⊤)
    (radiusLt : ENNReal.ofReal (8 * A) < outputConstant)
    (ratioLt : ENNReal.ofReal ratio < outputConstant)
    (referenceConstant_le :
      let selectionRetention :=
        pureWZ2FiniteAnchoredRetentionConstant
          A coordinateCount fine.family.card
      let degreeConstant :=
        pureWZ2FiniteAnchoredDegreeConstant
          coordinateCount fine.family.card
      let globalRetention :=
        pureWZ2ReanchoredGlobalRetentionConstant
          density fine.cellCount fine.distinctnessLoss
            selectionRetention
      let fiberRatio :=
        pureWZ2ReanchoredFiberRatioConstant
          inputConstant
          (pureWZ2CompleteFiberOverlapBound A)
          globalRetention degreeConstant
      pureWZ2AnchoredReferenceScaleConstant
          degreeConstant inputConstant fiberRatio ≤
        outputConstant)
    (topConstant_le :
      let selectionRetention :=
        pureWZ2FiniteAnchoredRetentionConstant
          A coordinateCount fine.family.card
      let globalRetention :=
        pureWZ2ReanchoredGlobalRetentionConstant
          density fine.cellCount fine.distinctnessLoss
            selectionRetention
      pureWZ2TopScaleConstant
          inputConstant
          (pureWZ2UnitScaleCompleteFiberOverlapBound A)
          globalRetention ≤
        outputConstant) :
    Nonempty
      (PureWZ2AnchoredNearbyAssemblyData
        fine A coordinateCount outputConstant) := by
  let scale :
      Fin coordinateCount →
        Kakeya.Streamlined.AdmissibleScale delta := fun coordinate =>
    ⟨delta * ratio ^ coordinate.val,
      by
        have hpow : 1 ≤ ratio ^ coordinate.val :=
          one_le_pow₀ ratioOne.le
        nlinarith,
      by
        have hpow :
            ratio ^ coordinate.val ≤ ratio ^ coordinateCount := by
          gcongr
          · exact ratioOne.le
          · exact coordinate.isLt.le
        calc
          delta * ratio ^ coordinate.val ≤
              delta * ratio ^ coordinateCount := by
            gcongr
          _ = 1 := scheduleTop⟩
  have hscaleSmall :
      ∀ coordinate,
        (scale coordinate).1 ≤ 1 / (200 * A) := by
    intro coordinate
    have hcoordinate :
        coordinate.val + 1 ≤ coordinateCount := by omega
    have hpow :
        ratio ^ (coordinate.val + 1) ≤
          ratio ^ coordinateCount := by
      gcongr
      exact ratioOne.le
    have hscaled :
        delta * ratio ^ (coordinate.val + 1) ≤ 1 := by
      calc
        delta * ratio ^ (coordinate.val + 1) ≤
            delta * ratio ^ coordinateCount := by
          gcongr
        _ = 1 := scheduleTop
    have hratioPos : 0 < ratio := by linarith
    have hApos : 0 < A := by linarith
    change delta * ratio ^ coordinate.val ≤ 1 / (200 * A)
    rw [pow_succ] at hscaled
    apply (le_div_iff₀ (by positivity : 0 < 200 * A)).mpr
    calc
      delta * ratio ^ coordinate.val * (200 * A) ≤
          delta * ratio ^ coordinate.val * ratio := by
        gcongr
      _ = delta * ratio ^ (coordinate.val + 1) := by
        rw [pow_succ]
        ring
      _ ≤ 1 := hscaled
  let scaleData :
      ∀ coordinate,
        PureWZ2GWZScaleData
          (A := A) source (scale coordinate) inputConstant :=
    fun coordinate =>
      Classical.choice (fullFiberData.scale (scale coordinate))
  let oneScale :
      ∀ coordinate,
        PureWZ2OneScaleAnchoredOwnerCoverData
          fine (scaleData coordinate) :=
    fun coordinate =>
      Classical.choice
        (pureWZ2_one_scale_anchored_owner_cover
          hdelta hA fine hfineRadius
          (scaleData coordinate) (hscaleSmall coordinate))
  let coloring :
      ∀ coordinate,
        PureWZ2OneScaleAnchoredColoringData
          fine (scaleData coordinate) (oneScale coordinate) :=
    fun coordinate =>
      Classical.choice
        (pureWZ2_one_scale_anchored_coloring
          hdelta hA fine hfineRadius
          (scaleData coordinate) (hscaleSmall coordinate)
          (oneScale coordinate))
  let weight : Fin fine.family.card → ENNReal :=
    fun index => volume (fine.shading.carrier index)
  let selection :
      PureWZ2FiniteAnchoredSelectionData
        fine coordinateCount scale scaleData oneScale coloring weight :=
    Classical.choice
      (pureWZ2_finite_anchored_selection
        fine coordinateCount coordinateCountPos
        scale scaleData oneScale coloring weight)
  let shading := selection.selectedShading
  let globalRetention :=
    pureWZ2ReanchoredGlobalRetentionConstant
      density fine.cellCount fine.distinctnessLoss
        selection.retentionConstant
  have hcardinality :
      source.enncard ≤
        globalRetention * selection.selected.family.enncard := by
    simpa [globalRetention,
      pureWZ2ReanchoredGlobalRetentionConstant] using
      selection.source_cardinality_retention
        hdelta hdeltaOne fine density
        density_ne_zero density_ne_top sourceDense
  have hreferenceBound :
      pureWZ2AnchoredReferenceScaleConstant
          selection.degreeConstant inputConstant
          (pureWZ2ReanchoredFiberRatioConstant
            inputConstant
            (pureWZ2CompleteFiberOverlapBound A)
            globalRetention selection.degreeConstant) ≤
        outputConstant := by
    dsimp only [globalRetention]
    rw [selection.retentionConstant_eq,
      selection.degreeConstant_eq]
    exact referenceConstant_le
  have htopBound :
      pureWZ2TopScaleConstant
          inputConstant
          (pureWZ2UnitScaleCompleteFiberOverlapBound A)
          globalRetention ≤
        outputConstant := by
    dsimp only [globalRetention]
    rw [selection.retentionConstant_eq]
    exact topConstant_le
  have hsmallCovers :
      ∀ coordinate : Fin coordinateCount,
        WZ2PaperPureScaleCoverData
          selection.selected.family
          (8 * A * delta * ratio ^ coordinate.val)
          outputConstant := by
    intro coordinate
    let reference :=
      Classical.choice
        (pureWZ2_anchored_reference_scale
          hdelta hdeltaOne hA fine coordinateCount
          scale scaleData oneScale coloring selection
          sourceDense density_ne_zero density_ne_top
          coordinate (hscaleSmall coordinate))
    let widened :=
      reference.mono
        hreferenceBound
    simpa [scale, mul_assoc] using widened
  let topScale : Kakeya.Streamlined.AdmissibleScale delta :=
    ⟨1, hdeltaOne, le_rfl⟩
  let topScaleData :
      PureWZ2GWZScaleData
        (A := A) source topScale inputConstant :=
    Classical.choice (fullFiberData.scale topScale)
  have htopCover :
      WZ2PaperPureScaleCoverData
        selection.selected.family (8 * A) outputConstant := by
    let top :=
      Classical.choice
        (pureWZ2_top_scale_single_parent
          hdelta hdeltaOne hA fine hfineRadius
          selection.selected topScaleData rfl
          globalRetention hcardinality)
    exact top.mono
      htopBound
  have hcwa :=
    pureWZ2_nearby_from_scaled_reference_scales
      hdelta outputOne outputTop
      (by
        intro first second hne
        rw [selection.selected.tube_eq,
          selection.selected.tube_eq]
        exact fine.paper_distinct
          (selection.selected.embedding first)
          (selection.selected.embedding second)
          (selection.selected.embedding.injective.ne hne))
      (8 * A) ratio
      (by nlinarith) radiusLt ratioOne ratioLt
      coordinateCount scheduleTop
      hsmallCovers htopCover
  have hrawMass :
      sourceShading.mass ≤
        ((fine.cellCount : ENNReal) *
          (fine.distinctnessLoss : ENNReal) *
          selection.retentionConstant) *
            shading.mass := by
    calc
      sourceShading.mass ≤
          (fine.cellCount : ENNReal) *
            (fine.distinctnessLoss : ENNReal) *
            fine.shading.mass :=
        fine.mass_retained
      _ ≤
          (fine.cellCount : ENNReal) *
            (fine.distinctnessLoss : ENNReal) *
            (selection.retentionConstant * shading.mass) := by
        gcongr
        exact selection.shading_mass_retained
      _ = _ := by ring
  exact
    ⟨{
      selected := selection.selected
      shading := shading
      subshading := by
        intro index point hpoint
        exact fine.subshading
          (selection.selected.embedding index) hpoint
      selectionRetentionConstant :=
        selection.retentionConstant
      selectionRetentionConstant_eq :=
        selection.retentionConstant_eq
      retained_mass_raw := hrawMass
      literal_cwa := hcwa
    }⟩

end Kakeya.Assouad

end
