import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.CompleteToStrictFiberRatio
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.ReanchoredCardinalityRetention
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.ReanchoredFrostmanTransfer
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.ReanchoredParentVolume

/-!
# One anchored reference-scale witness

Assemble one selected monochromatic anchored cover into literal pure
Definition 2.12 scale data.  The construction uses only complete GWZ fibers.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

/-- Source-to-final indexed cardinality loss. -/
def pureWZ2ReanchoredGlobalRetentionConstant
    (density localizationLoss distinctnessLoss selectionLoss : ENNReal) :
    ENNReal :=
  density⁻¹ * (localizationLoss * distinctnessLoss * selectionLoss)

/-- Original complete-fiber to final strict-fiber cardinality loss. -/
def pureWZ2ReanchoredFiberRatioConstant
    (inputConstant overlapConstant globalRetention degreeConstant : ENNReal) :
    ENNReal :=
  inputConstant * (overlapConstant * globalRetention) * degreeConstant

/-- Frostman constant on one final strict reanchored fiber. -/
def pureWZ2ReanchoredStrictFrostmanConstant
    (inputConstant fiberRatio : ENNReal) : ENNReal :=
  212776173 * inputConstant * fiberRatio * 1280

/-- Common uniformity and actual-John CWA constant at one reference scale. -/
def pureWZ2AnchoredReferenceScaleConstant
    (degreeConstant inputConstant fiberRatio : ENNReal) : ENNReal :=
  max degreeConstant
    (27 * pureWZ2ReanchoredStrictFrostmanConstant
      inputConstant fiberRatio)

/--
One coordinate of the simultaneous anchored selection produces literal
Definition 2.12 scale data at radius `8 * A * rho`.
-/
theorem pureWZ2_anchored_reference_scale
    {delta A : ℝ}
    (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1)
    (hA : 1 ≤ A)
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : Kakeya.Streamlined.TubeShading source}
    (fine : PureWZ2LocalizedDistinctReanchoringData sourceShading)
    (coordinateCount : ℕ)
    {inputConstant density : ENNReal}
    (scale :
      Fin coordinateCount →
        Kakeya.Streamlined.AdmissibleScale delta)
    (scaleData :
      ∀ coordinate,
        PureWZ2GWZScaleData
          (A := A) source (scale coordinate) inputConstant)
    (oneScale :
      ∀ coordinate,
        PureWZ2OneScaleAnchoredOwnerCoverData
          fine (scaleData coordinate))
    (coloring :
      ∀ coordinate,
        PureWZ2OneScaleAnchoredColoringData
          fine (scaleData coordinate) (oneScale coordinate))
    (selection :
      PureWZ2FiniteAnchoredSelectionData
        fine coordinateCount scale scaleData oneScale coloring
          (fun index => volume (fine.shading.carrier index)))
    (sourceDense : sourceShading.IsLambdaDense density)
    (density_ne_zero : density ≠ 0)
    (density_ne_top : density ≠ ⊤)
    (coordinate : Fin coordinateCount)
    (hscaleSmall :
      (scale coordinate).1 ≤ 1 / (200 * A)) :
    let globalRetention :=
      pureWZ2ReanchoredGlobalRetentionConstant
        density fine.cellCount fine.distinctnessLoss
          selection.retentionConstant
    let fiberRatio :=
      pureWZ2ReanchoredFiberRatioConstant
        inputConstant
        (pureWZ2CompleteFiberOverlapBound A)
        globalRetention selection.degreeConstant
    Nonempty
      (WZ2PaperPureScaleCoverData
        selection.selected.family
        (8 * A * (scale coordinate).1)
        (pureWZ2AnchoredReferenceScaleConstant
          selection.degreeConstant inputConstant fiberRatio)) := by
  dsimp only
  let globalRetention :=
    pureWZ2ReanchoredGlobalRetentionConstant
      density fine.cellCount fine.distinctnessLoss
        selection.retentionConstant
  let fiberRatio :=
    pureWZ2ReanchoredFiberRatioConstant
      inputConstant
      (pureWZ2CompleteFiberOverlapBound A)
      globalRetention selection.degreeConstant
  let frostmanConstant :=
    pureWZ2ReanchoredStrictFrostmanConstant
      inputConstant fiberRatio
  let outputConstant :=
    pureWZ2AnchoredReferenceScaleConstant
      selection.degreeConstant inputConstant fiberRatio
  rcases
      (coloring coordinate).monochromatic_cover
        hdelta hA selection.selected
        (selection.colorVector coordinate)
        (selection.monochromatic coordinate) with
    ⟨monochromatic⟩
  have hglobalRetention :
      source.enncard ≤
        globalRetention * selection.selected.family.enncard := by
    simpa [globalRetention,
      pureWZ2ReanchoredGlobalRetentionConstant, mul_assoc] using
      selection.source_cardinality_retention
        hdelta hdeltaOne fine density
        density_ne_zero density_ne_top sourceDense
  have hfiberRatio :
      ∀ parent : Fin monochromatic.selectedCoarse.family.card,
        ((scaleData coordinate).fullFiberIndices
          ((oneScale coordinate).originalParent
            (monochromatic.selectedCoarse.embedding parent))).card ≤
          fiberRatio *
            (wz2PaperOrdinaryFullFiberIndices
              selection.selected.family
              monochromatic.selectedCoarse.family parent).card := by
    intro parent
    have hratio :=
      pureWZ2_complete_to_strict_fiber_ratio
        hdelta hA hscaleSmall monochromatic
        selection.degreeConstant globalRetention
        (selection.degree_uniform coordinate)
        hglobalRetention parent
    simpa [fiberRatio,
      pureWZ2ReanchoredFiberRatioConstant, mul_assoc] using hratio
  have hselectedUniform :
      WZ2PaperPureFullFibersAreCUniform
        selection.selected.family
        monochromatic.selectedCoarse.family
        selection.degreeConstant := by
    intro first second
    have hfirst :
        0 <
          ((Finset.univ :
            Finset (Fin selection.selected.family.card)).filter
              fun index =>
                (oneScale coordinate).cover.parent
                    (selection.selected.embedding index) =
                  monochromatic.selectedCoarse.embedding first).card := by
      rw [← monochromatic.fullFiberIndices_eq_owner first]
      exact
        Finset.card_pos.mpr
          (monochromatic.full_fiber_nonempty first)
    have hsecond :
        0 <
          ((Finset.univ :
            Finset (Fin selection.selected.family.card)).filter
              fun index =>
                (oneScale coordinate).cover.parent
                    (selection.selected.embedding index) =
                  monochromatic.selectedCoarse.embedding second).card := by
      rw [← monochromatic.fullFiberIndices_eq_owner second]
      exact
        Finset.card_pos.mpr
          (monochromatic.full_fiber_nonempty second)
    have huniform :=
      selection.degree_uniform coordinate
        (monochromatic.selectedCoarse.embedding first)
        (monochromatic.selectedCoarse.embedding second)
        hfirst hsecond
    rw [wz2PaperOrdinaryFullFiberCount,
      wz2PaperOrdinaryFullFiberCount,
      monochromatic.fullFiberIndices_eq_owner first,
      monochromatic.fullFiberIndices_eq_owner second]
    exact huniform
  have hrhoPos :
      0 < 8 * A * (scale coordinate).1 := by
    have hscalePos : 0 < (scale coordinate).1 :=
      hdelta.trans_le (scale coordinate).property.1
    positivity
  refine
    ⟨{
      delta_pos := hdelta
      rho_pos := hrhoPos
      coarse := monochromatic.selectedCoarse.family
      cover := monochromatic.cover
      full_fiber_uniform := fun first second =>
        (hselectedUniform first second).trans <| by
          gcongr
          exact le_max_left _ _
      rescaledFiber := ?_
    }⟩
  intro parent
  let strictIndices :=
    wz2PaperOrdinaryFullFiberIndices
      selection.selected.family
      monochromatic.selectedCoarse.family parent
  let strictSub :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset
      selection.selected.family strictIndices
  let sourceIndex :
      Fin selection.selected.family.card ↪ Fin source.card :=
    selection.selected.embedding.trans fine.sourceIndex
  let axialShift : Fin selection.selected.family.card → ℝ :=
    fun index => fine.axialShift (selection.selected.embedding index)
  let originalParent :=
    (scaleData coordinate).coarse.tube
      ((oneScale coordinate).originalParent
        (monochromatic.selectedCoarse.embedding parent))
  let reanchoredParent :=
    monochromatic.selectedCoarse.family.tube parent
  have hdirection :
      ∀ index,
        (selection.selected.family.tube index).direction =
          (source.tube (sourceIndex index)).direction := by
    intro index
    rw [selection.selected.tube_eq]
    exact fine.direction_eq (selection.selected.embedding index)
  have hsourceBase :
      ∀ index,
        (source.tube (sourceIndex index)).base =
          (selection.selected.family.tube index).base +
            axialShift index •
              (selection.selected.family.tube index).direction := by
    intro index
    rw [selection.selected.tube_eq]
    exact fine.source_base_eq (selection.selected.embedding index)
  have haxial :
      ∀ index, |axialShift index| ≤ 1 :=
    fun index =>
      fine.axialShift_bound (selection.selected.embedding index)
  have hselectedComplete :
      ∀ index ∈ strictIndices,
        sourceIndex index ∈
          (scaleData coordinate).fullFiberIndices
            ((oneScale coordinate).originalParent
              (monochromatic.selectedCoarse.embedding parent)) := by
    intro index hindex
    exact
      monochromatic.strict_fiber_mem_complete_fiber
        parent index hindex
  have hcompleteCarrier :
      ∀ index ∈
          (scaleData coordinate).fullFiberIndices
            ((oneScale coordinate).originalParent
              (monochromatic.selectedCoarse.embedding parent)),
        (source.tube index).carrier ⊆
          wz2PaperCenteredDilatedCarrier A originalParent := by
    intro index hindex
    rw [(scaleData coordinate).fullFiberIndices_eq] at hindex
    exact (Finset.mem_filter.mp hindex).2
  have hparentVolume :
      volume reanchoredParent.carrier ≤
        (1280 : ENNReal) *
          volume
            (wz2PaperCenteredDilatedCarrier A originalParent) := by
    exact
      pureWZ2_reanchored_parent_volume_ratio
        hA
        (show 0 < (scale coordinate).1 by
          exact hdelta.trans_le (scale coordinate).property.1)
        (scale coordinate).property.2
        reanchoredParent originalParent
  have hfrostman :
      ∀ convexSet : Set Point3,
        Convex ℝ convexSet →
        convexSet ⊆ reanchoredParent.carrier →
          strictSub.family.toBodyFamily.containedMass convexSet *
              volume reanchoredParent.carrier ≤
            frostmanConstant *
              strictSub.family.toBodyFamily.mass *
              volume convexSet := by
    have htransfer :=
      pureWZ2_reanchored_strict_fiber_frostman
        hdelta
        (show 0 < (scale coordinate).1 by
          exact hdelta.trans_le (scale coordinate).property.1)
        hA sourceIndex axialShift
        hdirection hsourceBase haxial
        originalParent reanchoredParent strictIndices
        (monochromatic.full_fiber_nonempty parent)
        ((scaleData coordinate).fullFiberIndices
          ((oneScale coordinate).originalParent
            (monochromatic.selectedCoarse.embedding parent)))
        hselectedComplete hcompleteCarrier
        inputConstant fiberRatio 1280
        (hfiberRatio parent)
        ((scaleData coordinate).full_fiber_frostman
          ((oneScale coordinate).originalParent
            (monochromatic.selectedCoarse.embedding parent)))
        hparentVolume
    simpa [strictSub, strictIndices, frostmanConstant,
      pureWZ2ReanchoredStrictFrostmanConstant] using htransfer
  let normalization :=
    WZ2PaperAssouadUnitRescalingData.ofTube
      reanchoredParent hrhoPos
  have hstrictCarrier :
      ∀ index : Fin strictSub.family.card,
        (strictSub.family.tube index).carrier ⊆
          wz2PaperCenteredDilatedCarrier 1 reanchoredParent := by
    intro index
    have hmember :
        strictSub.embedding index ∈ strictIndices :=
      Finset.orderEmbOfFin_mem strictIndices rfl index
    have hcontainment :=
      (mem_wz2PaperOrdinaryFullFiberIndices_iff
        parent (strictSub.embedding index)).mp hmember
    have hdilated :
        wz2PaperCenteredDilatedCarrier 1 reanchoredParent =
          reanchoredParent.carrier := by
      simp [wz2PaperCenteredDilatedCarrier,
        AffineMap.homothety]
    rw [hdilated]
    rw [strictSub.tube_eq]
    exact hcontainment
  have hnormalized :=
    gwz_frostman_to_john_rescaled_convex_wolff
      hdelta hrhoPos (show (1 : ℝ) ≤ 1 by norm_num)
      parent strictSub hstrictCarrier normalization
      frostmanConstant (by
        intro convexSet hconvex hsubset
        have hdilated :
            wz2PaperCenteredDilatedCarrier 1 reanchoredParent =
              reanchoredParent.carrier := by
          simp [wz2PaperCenteredDilatedCarrier,
            AffineMap.homothety]
        rw [hdilated] at hsubset
        have hresult := hfrostman convexSet hconvex hsubset
        rw [hdilated]
        exact hresult)
  let expected :=
    wz2PaperPureUnitRescaledFullFiberBodyFamily
      (fine := selection.selected.family)
      (coarse := monochromatic.selectedCoarse.family)
      parent normalization
  have hbody :
      ∀ index : Fin strictSub.family.card,
        ({
          card := strictSub.family.card
          body := fun index : Fin strictSub.family.card =>
            ⟨normalization.map ''
              (strictSub.family.tube index).carrier⟩
        } : Kakeya.Streamlined.BodyFamily).body index =
          expected.body index := by
    intro index
    simp only [expected,
      wz2PaperPureUnitRescaledFullFiberBodyFamily]
    rw [strictSub.tube_eq]
    rfl
  have hfinal :
      WZ2PaperBodyConvexWolffBound expected
        (27 * frostmanConstant) := by
    exact cwb_transfer_reindex (Equiv.refl _) hbody hnormalized
  exact
    ⟨{
      normalization := normalization
      convex_wolff := fun convexSet hconvex =>
        (hfinal convexSet hconvex).trans <| by
          gcongr
          exact le_max_right _ _
    }⟩

end Kakeya.Assouad

end
