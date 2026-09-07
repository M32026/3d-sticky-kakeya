import MyLeanRepo.Kakeya.Assouad.PureWZ2.LocalizedActualFiberLineCover
import MyLeanRepo.Kakeya.Assouad.PureWZ2.PropSticky
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.WeightedGraphSelection
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperRefinementHelpers

/-!
# Parent-level weighted selection of complete actual fibers

At one actual pure Definition 2.12 scale, weight every actual parent by the
shaded mass of its complete strict fiber.  A bounded-degree independent-set
selection is then performed on the parents, not on the fine tubes.  Every
selected parent retains its entire complete actual fiber.

The caller-scale family is a WZ line-cover family made from one representative
of each selected actual fiber.  It is deliberately not asserted to be a
public ordinary carrier-containment cover: finite unit-segment containment is
not determined by the supporting-line metric.  Instead the output records the
exact equality between each caller WZ fiber and its complete actual strict
fiber, together with the original actual-John witness.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

/-- Shaded mass of one complete actual pure strict fiber. -/
def pureWZ2ActualFiberShadedMass
    {delta actual : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily actual}
    (shading : WZ1PaperTubeShading fine)
    (parent : Fin coarse.card) : ENNReal :=
  ∑ source ∈
      wz2PaperOrdinaryFullFiberIndices fine coarse parent,
    volume (shading.carrier source)

/-- The complete actual pure fibers partition total shaded mass. -/
theorem sum_pureWZ2ActualFiberShadedMass
    {delta actual : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily actual}
    (cover : WZ2PaperPurePartitioningCover fine coarse)
    (hactual : 0 ≤ actual)
    (shading : WZ1PaperTubeShading fine) :
    ∑ parent : Fin coarse.card,
        pureWZ2ActualFiberShadedMass shading parent =
      shading.mass := by
  have fiberEq :
      ∀ parent : Fin coarse.card,
        wz2PaperOrdinaryFullFiberIndices fine coarse parent =
          Finset.univ.filter fun source =>
            cover.parent source = parent := by
    intro parent
    ext source
    rw [cover.mem_fullFiber_iff_parent_eq hactual]
    simp
  simp_rw [pureWZ2ActualFiberShadedMass, fiberEq]
  exact
    Finset.sum_fiberwise_of_maps_to
      (s := Finset.univ)
      (t := Finset.univ)
      (g := cover.parent)
      (fun _ _ => Finset.mem_univ _)
      (fun source => volume (shading.carrier source))

/--
One caller-scale WZ cover obtained by selecting complete actual parent fibers.

The selected fine family is exactly the union of the displayed actual fibers.
The caller parent map is synchronized with the actual pure parent map, and
`complete_actual_fiber` records equality after ambient reindexing.
-/
structure PureWZ2ParentLevelWholeFiberSelectionData
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {requested : WZ2PaperRequestedScale delta}
    {C : ENNReal}
    (nearby :
      WZ2PaperPureNearbyScaleCoverData fine requested C)
    (caller : WZ2PaperRequestedScale delta)
    (shading : WZ1PaperTubeShading fine)
    (degree : ℕ) where
  selectedParents :
    Finset (Fin nearby.scaleData.coarse.card)
  selectedParents_nonempty :
    selectedParents.Nonempty
  selectedFineIndices : Finset (Fin fine.card)
  selectedFineIndices_eq :
    selectedFineIndices =
      Finset.univ.filter fun source =>
        nearby.scaleData.cover.parent source ∈ selectedParents
  selected :
    Kakeya.Streamlined.TubeSubfamily fine
  selected_eq :
    selected =
      Kakeya.Streamlined.TubeSubfamily.fromFinset
        fine selectedFineIndices
  selectedShading :
    WZ1PaperTubeShading selected.family
  selectedShading_eq :
    selectedShading =
      restrictPaperShading selected shading
  callerCoarse :
    Kakeya.Streamlined.TubeFamily caller.1
  actualParent :
    Fin callerCoarse.card ↪
      Fin nearby.scaleData.coarse.card
  actualParent_mem :
    ∀ parent, actualParent parent ∈ selectedParents
  callerCover :
    WZ1PaperTubeCover selected.family callerCoarse
  section6Cover :
    PureWZ2Section6Cover selected.family callerCoarse
  actual_parent_compatibility :
    ∀ source,
      actualParent (callerCover.parent source) =
        nearby.scaleData.cover.parent
          (selected.embedding source)
  complete_actual_fiber :
    ∀ parent : Fin callerCoarse.card,
      Finset.image selected.embedding
          (wz2PaperFullFiberIndices
            selected.family callerCoarse parent) =
        wz2PaperOrdinaryFullFiberIndices
          fine nearby.scaleData.coarse
          (actualParent parent)
  retained_mass :
    shading.mass ≤
      (degree + 1 : ENNReal) * selectedShading.mass
  actual_full_fiber_uniform :
    WZ2PaperPureFullFibersAreCUniform
      fine nearby.scaleData.coarse C
  actual_rescaledFiber :
    ∀ parent : Fin callerCoarse.card,
      Nonempty
        (WZ2PaperPureUnitRescaledFullFiberData
          (fine := fine)
          (coarse := nearby.scaleData.coarse)
          (actualParent parent) C)

/--
Select a bounded-degree independent set of actual parents, retaining every
fine tube in each selected complete actual fiber.

The conflict relation is exactly caller-scale WZ line conflict between the
chosen fine representatives.  Its degree bound is an explicit mathematical
input; no fine-scale packing estimate is silently substituted for it.
-/
theorem pure_wz2_parent_level_whole_fiber_selection
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {requested : WZ2PaperRequestedScale delta}
    {C : ENNReal}
    (nearby :
      WZ2PaperPureNearbyScaleCoverData fine requested C)
    (caller : WZ2PaperRequestedScale delta)
    (shading : WZ1PaperTubeShading fine)
    (shadingMassPos : 0 < shading.mass)
    (fineLine : WZ1PaperIsLineClass fine)
    (fineBase :
      ∀ source, ‖(fine.tube source).base‖ ≤ 5)
    (actualSmall : nearby.rho ≤ 1 / 10000)
    (actualCaller :
      1200000 * nearby.rho ≤ caller.1)
    (representative :
      Fin nearby.scaleData.coarse.card →
        Fin fine.card)
    (representative_mem :
      ∀ parent,
        representative parent ∈
          wz2PaperOrdinaryFullFiberIndices
            fine nearby.scaleData.coarse parent)
    (degree : ℕ)
    (conflictDegree :
      ∀ fixed,
        (Finset.univ.filter fun other =>
          other ≠ fixed ∧
            wz1PaperLineDistance
                (fine.tube (representative fixed))
                (fine.tube (representative other)) ≤
              1600 * caller.1).card ≤ degree) :
    Nonempty
      (PureWZ2ParentLevelWholeFiberSelectionData
        nearby caller shading degree) := by
  let weight :
      Fin nearby.scaleData.coarse.card → ENNReal :=
    pureWZ2ActualFiberShadedMass shading
  let conflict :
      Fin nearby.scaleData.coarse.card →
        Fin nearby.scaleData.coarse.card → Prop :=
    fun first second =>
      second ≠ first ∧
        wz1PaperLineDistance
            (fine.tube (representative first))
            (fine.tube (representative second)) ≤
          1600 * caller.1
  have conflictSymmetric :
      ∀ first second,
        conflict first second →
          conflict second first := by
    intro first second hconflict
    refine ⟨hconflict.1.symm, ?_⟩
    rw [wz1PaperLineDistance_symm]
    exact hconflict.2
  have conflictIrreflexive :
      ∀ parent, ¬conflict parent parent := by
    intro parent hconflict
    exact hconflict.1 rfl
  have conflictDegree' :
      ∀ fixed,
        (Finset.univ.filter fun other =>
          conflict fixed other).card ≤ degree := by
    exact conflictDegree
  rcases
      pureWZ2_greedy_independent_set_weighted
        (D := degree)
        (weight := weight)
        conflictSymmetric conflictIrreflexive
        (fun fixed => by
          rw [Finset.filter_congr_decidable]
          exact conflictDegree' fixed)
    with
    ⟨selectedParents, selectedIndependent, retainedWeight⟩
  have actualPos : 0 < nearby.rho :=
    nearby.scaleData.rho_pos
  have deltaActual : delta ≤ nearby.rho :=
    requested.2.1.trans nearby.requested_le
  have callerPos : 0 < caller.1 := by
    have hscaled : 0 < 1200000 * nearby.rho := by
      positivity
    exact hscaled.trans_le actualCaller
  have totalWeight :
      (∑ parent : Fin nearby.scaleData.coarse.card,
          weight parent) =
        shading.mass := by
    exact
      sum_pureWZ2ActualFiberShadedMass
        nearby.scaleData.cover actualPos.le shading
  have selectedParentsNonempty :
      selectedParents.Nonempty := by
    by_contra hnonempty
    have hempty : selectedParents = ∅ := by
      simpa using hnonempty
    rw [hempty] at retainedWeight
    simp only [Finset.sum_empty, mul_zero] at retainedWeight
    rw [totalWeight] at retainedWeight
    exact (not_le_of_gt shadingMassPos) retainedWeight
  let selectedFineIndices : Finset (Fin fine.card) :=
    Finset.univ.filter fun source =>
      nearby.scaleData.cover.parent source ∈ selectedParents
  let selected :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset
      fine selectedFineIndices
  let selectedShading :=
    restrictPaperShading selected shading
  have selectedEmbeddingMem :
      ∀ source : Fin selected.family.card,
        selected.embedding source ∈ selectedFineIndices := by
    intro source
    exact
      Finset.orderEmbOfFin_mem
        selectedFineIndices rfl source
  have selectedAmbientSurjective :
      ∀ source ∈ selectedFineIndices,
        ∃ selectedSource : Fin selected.family.card,
          selected.embedding selectedSource = source := by
    intro source hsource
    let member : selectedFineIndices := ⟨source, hsource⟩
    let selectedSource : Fin selected.family.card :=
      (selectedFineIndices.orderIsoOfFin rfl).symm member
    exact
      ⟨selectedSource,
        congrArg Subtype.val
          (selectedFineIndices.orderIsoOfFin rfl
            |>.apply_symm_apply member)⟩
  let selectedParentEquiv :
      Fin selectedParents.card ≃ selectedParents :=
    (selectedParents.orderIsoOfFin rfl).toEquiv
  let actualParentEmbedding :
      Fin selectedParents.card ↪
        Fin nearby.scaleData.coarse.card :=
    (selectedParents.orderEmbOfFin rfl).toEmbedding
  let callerCoarse :
      Kakeya.Streamlined.TubeFamily caller.1 :=
    {
      card := selectedParents.card
      tube := fun parent =>
        wz2PaperRelabelTube (targetScale := caller.1)
          (wz2PaperCanonicalLineTube
            (fine.tube
              (representative
                (actualParentEmbedding parent))))
    }
  let callerParent :
      Fin selected.family.card →
        Fin callerCoarse.card :=
    fun source =>
      selectedParentEquiv.symm
        ⟨nearby.scaleData.cover.parent
            (selected.embedding source),
          (Finset.mem_filter.mp
            (selectedEmbeddingMem source)).2⟩
  have actualParentCompatibility :
      ∀ source,
        actualParentEmbedding (callerParent source) =
          nearby.scaleData.cover.parent
            (selected.embedding source) := by
    intro source
    exact
      congrArg Subtype.val
        (selectedParentEquiv.apply_symm_apply
          ⟨nearby.scaleData.cover.parent
              (selected.embedding source),
            (Finset.mem_filter.mp
              (selectedEmbeddingMem source)).2⟩)
  have callerParentSurjective :
      Function.Surjective callerParent := by
    intro parent
    let actualParent := actualParentEmbedding parent
    let ambientSource := representative actualParent
    have ambientSourceParent :
        nearby.scaleData.cover.parent ambientSource =
          actualParent :=
      (nearby.scaleData.cover.mem_fullFiber_iff_parent_eq
        actualPos.le actualParent ambientSource).mp
        (representative_mem actualParent)
    have actualParentMem :
        actualParent ∈ selectedParents :=
      Finset.orderEmbOfFin_mem selectedParents rfl parent
    have ambientSourceSelected :
        ambientSource ∈ selectedFineIndices := by
      exact
        Finset.mem_filter.mpr
          ⟨Finset.mem_univ ambientSource,
            ambientSourceParent.symm ▸ actualParentMem⟩
    rcases
        selectedAmbientSurjective
          ambientSource ambientSourceSelected
      with
      ⟨source, hsource⟩
    refine ⟨source, ?_⟩
    apply actualParentEmbedding.injective
    rw [actualParentCompatibility, hsource,
      ambientSourceParent]
  have callerCoarseLine :
      WZ1PaperIsLineClass callerCoarse := by
    intro parent
    exact
      wz2PaperRelabelTube_lineClass
        (wz2PaperCanonicalLineTube_lineClass
          (fineLine
            (representative
              (actualParentEmbedding parent))))
  have callerStronglySeparated :
      ∀ first second : Fin callerCoarse.card,
        first ≠ second →
          1600 * caller.1 <
            wz1PaperLineDistance
              (callerCoarse.tube first)
              (callerCoarse.tube second) := by
    intro first second hne
    have actualNe :
        actualParentEmbedding first ≠
          actualParentEmbedding second :=
      actualParentEmbedding.injective.ne hne
    have firstMem :
        actualParentEmbedding first ∈ selectedParents :=
      Finset.orderEmbOfFin_mem selectedParents rfl first
    have secondMem :
        actualParentEmbedding second ∈ selectedParents :=
      Finset.orderEmbOfFin_mem selectedParents rfl second
    have hnot :
        ¬conflict
          (actualParentEmbedding first)
          (actualParentEmbedding second) :=
      selectedIndependent
        (actualParentEmbedding first) firstMem
        (actualParentEmbedding second) secondMem actualNe
    have hdistance :
        ¬wz1PaperLineDistance
              (fine.tube
                (representative
                  (actualParentEmbedding first)))
              (fine.tube
                (representative
                  (actualParentEmbedding second))) ≤
            1600 * caller.1 := by
      intro hle
      exact hnot ⟨actualNe.symm, hle⟩
    change
      1600 * caller.1 <
        wz1PaperLineDistance
          (wz2PaperRelabelTube
            (wz2PaperCanonicalLineTube
              (fine.tube
                (representative
                  (actualParentEmbedding first)))))
          (wz2PaperRelabelTube
            (wz2PaperCanonicalLineTube
              (fine.tube
                (representative
                  (actualParentEmbedding second)))))
    rw [wz2PaperRelabelTube_lineDistance_both,
      wz1PaperLineDistance_canonicalLineTube
        (fineLine
          (representative
            (actualParentEmbedding first)))
        (fineLine
          (representative
            (actualParentEmbedding second)))]
    exact lt_of_not_ge hdistance
  have callerParentCovers :
      ∀ source,
        WZ1PaperTubeCovers
          (selected.family.tube source)
          (callerCoarse.tube (callerParent source)) := by
    intro source
    let actualParent :=
      actualParentEmbedding (callerParent source)
    have sourceActual :
        selected.embedding source ∈
          wz2PaperOrdinaryFullFiberIndices
            fine nearby.scaleData.coarse actualParent := by
      apply
        (nearby.scaleData.cover.mem_fullFiber_iff_parent_eq
          actualPos.le actualParent
          (selected.embedding source)).mpr
      exact (actualParentCompatibility source).symm
    have hcover :=
      wz2_pure_actual_fullFiber_lineCoveredBy_representative
        nearby.scaleData.cover nearby.scaleData.delta_pos
        deltaActual actualSmall actualCaller fineLine fineBase
        actualParent (representative actualParent)
        (representative_mem actualParent)
        (selected.embedding source) sourceActual
    rw [selected.tube_eq]
    simpa [callerCoarse, actualParent] using hcover
  let callerCover :
      WZ1PaperTubeCover selected.family callerCoarse :=
    {
      parent := callerParent
      parent_surjective := callerParentSurjective
      parent_covers := callerParentCovers
      parent_unique := by
        intro source candidate candidateCovers
        by_contra hne
        have hseparated :=
          callerStronglySeparated
            candidate (callerParent source) hne
        have htriangle :=
          wz1PaperLineDistance_triangle
            (callerCoarse.tube candidate)
            (selected.family.tube source)
            (callerCoarse.tube (callerParent source))
        have hsymmetry :
            wz1PaperLineDistance
                (callerCoarse.tube candidate)
                (selected.family.tube source) =
              wz1PaperLineDistance
                (selected.family.tube source)
                (callerCoarse.tube candidate) :=
          wz1PaperLineDistance_symm _ _
        rw [hsymmetry] at htriangle
        have assignedCovers :=
          callerParentCovers source
        unfold WZ1PaperTubeCovers at candidateCovers assignedCovers
        have hupper :
            wz1PaperLineDistance
                (callerCoarse.tube candidate)
                (callerCoarse.tube
                  (callerParent source)) ≤
              caller.1 := by
          linarith [
            htriangle,
            candidateCovers,
            assignedCovers]
        exact
          (not_le_of_gt hseparated)
            (hupper.trans (by
              nlinarith [callerPos]))
    }
  let section6Cover :
      PureWZ2Section6Cover
        selected.family callerCoarse :=
    {
      fine_line_class := fineLine.subfamily selected
      coarse_line_class := callerCoarseLine
      covers := fun source =>
        ⟨callerCover.parent source,
          callerCover.parent_covers source⟩
      parent_hit := by
        intro parent
        rcases callerCover.parent_surjective parent with
          ⟨source, hsource⟩
        refine ⟨source, ?_⟩
        rw [← hsource]
        exact callerCover.parent_covers source
      coarse_essentially_distinct := by
        intro first second hne
        exact
          (show caller.1 < 1600 * caller.1 by
            nlinarith [callerPos]).trans
            (callerStronglySeparated first second hne)
    }
  have selectedMass :
      selectedShading.mass =
        ∑ parent ∈ selectedParents, weight parent := by
    have localMass :
        selectedShading.mass =
          ∑ source ∈ selectedFineIndices,
            volume (shading.carrier source) := by
      rw [restrictPaperShading_mass]
      let equivalence :
          Fin selected.family.card ≃ selectedFineIndices :=
        (selectedFineIndices.orderIsoOfFin rfl).toEquiv
      exact
        Fintype.sum_equiv equivalence
          (fun source =>
            volume
              (shading.carrier
                (selected.embedding source)))
          (fun source : selectedFineIndices =>
            volume (shading.carrier source.1))
          (fun _ => rfl) |>.trans
          (Finset.sum_coe_sort selectedFineIndices
            (fun source => volume (shading.carrier source)))
    have fiberwise :
        ∑ parent ∈ selectedParents,
            ∑ source ∈ selectedFineIndices with
                nearby.scaleData.cover.parent source = parent,
              volume (shading.carrier source) =
          ∑ source ∈ selectedFineIndices,
            volume (shading.carrier source) :=
      Finset.sum_fiberwise_of_maps_to
        (s := selectedFineIndices)
        (t := selectedParents)
        (g := nearby.scaleData.cover.parent)
        (fun source hsource =>
          (Finset.mem_filter.mp hsource).2)
        (fun source => volume (shading.carrier source))
    have fiberTerm :
        ∀ parent ∈ selectedParents,
          (∑ source ∈ selectedFineIndices with
              nearby.scaleData.cover.parent source = parent,
            volume (shading.carrier source)) =
          weight parent := by
      intro parent hparent
      have hindices :
          selectedFineIndices.filter
              (fun source =>
                nearby.scaleData.cover.parent source = parent) =
            wz2PaperOrdinaryFullFiberIndices
              fine nearby.scaleData.coarse parent := by
        ext source
        rw [nearby.scaleData.cover.mem_fullFiber_iff_parent_eq
          actualPos.le]
        simp only [selectedFineIndices,
          Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · exact fun h => h.2
        · intro hsource
          exact ⟨hsource ▸ hparent, hsource⟩
      rw [Finset.sum_filter]
      rw [← Finset.sum_filter]
      rw [hindices]
      rfl
    rw [localMass, ← fiberwise]
    apply Finset.sum_congr rfl
    intro parent hparent
    exact fiberTerm parent hparent
  have retainedMass :
      shading.mass ≤
        (degree + 1 : ENNReal) *
          selectedShading.mass := by
    rw [← totalWeight, selectedMass]
    exact retainedWeight
  have completeActualFiber :
      ∀ parent : Fin callerCoarse.card,
        Finset.image selected.embedding
            (wz2PaperFullFiberIndices
              selected.family callerCoarse parent) =
          wz2PaperOrdinaryFullFiberIndices
            fine nearby.scaleData.coarse
            (actualParentEmbedding parent) := by
    intro parent
    ext ambientSource
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨source, hsource, rfl⟩
      have parentEq :
          callerCover.parent source = parent := by
        exact
          (callerCover.parent_unique source parent
            ((mem_wz2PaperFullFiberIndices_iff
              parent source).mp hsource)).symm
      change callerParent source = parent at parentEq
      apply
        (nearby.scaleData.cover.mem_fullFiber_iff_parent_eq
          actualPos.le
          (actualParentEmbedding parent)
          (selected.embedding source)).mpr
      exact
        (actualParentCompatibility source).symm.trans
          (congrArg actualParentEmbedding parentEq)
    · intro hambient
      have ambientParent :
          nearby.scaleData.cover.parent ambientSource =
            actualParentEmbedding parent :=
        (nearby.scaleData.cover.mem_fullFiber_iff_parent_eq
          actualPos.le
          (actualParentEmbedding parent)
          ambientSource).mp hambient
      have ambientSelected :
          ambientSource ∈ selectedFineIndices := by
        exact
          Finset.mem_filter.mpr
            ⟨Finset.mem_univ ambientSource,
              ambientParent.symm ▸
                Finset.orderEmbOfFin_mem
                  selectedParents rfl parent⟩
      rcases
          selectedAmbientSurjective
            ambientSource ambientSelected
        with
        ⟨source, hsource⟩
      have callerParentEq :
          callerCover.parent source = parent := by
        apply actualParentEmbedding.injective
        rw [actualParentCompatibility, hsource,
          ambientParent]
      refine ⟨source, ?_, hsource⟩
      apply
        (mem_wz2PaperFullFiberIndices_iff
          parent source).mpr
      rw [← callerParentEq]
      exact callerCover.parent_covers source
  exact
    ⟨{
      selectedParents := selectedParents
      selectedParents_nonempty :=
        selectedParentsNonempty
      selectedFineIndices := selectedFineIndices
      selectedFineIndices_eq := rfl
      selected := selected
      selected_eq := rfl
      selectedShading := selectedShading
      selectedShading_eq := rfl
      callerCoarse := callerCoarse
      actualParent := actualParentEmbedding
      actualParent_mem := fun parent =>
        Finset.orderEmbOfFin_mem
          selectedParents rfl parent
      callerCover := callerCover
      section6Cover := section6Cover
      actual_parent_compatibility :=
        actualParentCompatibility
      complete_actual_fiber :=
        completeActualFiber
      retained_mass := retainedMass
      actual_full_fiber_uniform :=
        nearby.scaleData.full_fiber_uniform
      actual_rescaledFiber := fun parent =>
        nearby.scaleData.rescaledFiber
          (actualParentEmbedding parent)
    }⟩

end Kakeya.Assouad

end
