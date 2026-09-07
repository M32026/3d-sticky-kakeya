import MyLeanRepo.Kakeya.Assouad.PureWZ2.FiniteMaximalQuotientNet
import MyLeanRepo.Kakeya.Assouad.PureWZ2.CanonicalLineTube
import MyLeanRepo.Kakeya.Assouad.PureWZ2.CenteredLineTube
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Section6CoverParentMap
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.WeightedGraphSelection
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralSeparationConstants
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperDoubledParentCarrierCover
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12LocalizedEssentialDistinctness
import MyLeanRepo.Kakeya.Assouad.WZ1.PaperPackingRefinement

/-!
# Direct mass-retaining caller selection in the WZ line metric

This producer starts from the cropped fine family itself.  It does not pass
through an arbitrary actual Definition 2.12 parent representative and
therefore needs no bound on the stored finite-segment base points.

A maximal `rho / 4` line net supplies a canonical quotient of all fine tubes.
The net centers have bounded `1600 * rho` conflict degree.  Weighted
independent-set selection on the complete quotient classes retains a fixed
share of shaded mass and produces a strongly separated caller family.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

def pureWZ2DirectCallerConflictDegree : ℕ :=
  102401 ^ 5

structure PureWZ2DirectCallerLineSelectionData
    {delta : ℝ}
    (fine : Kakeya.Streamlined.TubeFamily delta)
    (shading : WZ1PaperTubeShading fine)
    (caller : WZ2PaperRequestedScale delta) where
  caller_pos : 0 < caller.1
  selected : Kakeya.Streamlined.TubeSubfamily fine
  selected_nonempty : selected.family.Nonempty
  ambient_line_class : WZ1PaperIsLineClass fine
  selectedShading : WZ1PaperTubeShading selected.family
  selectedShading_eq :
    selectedShading = restrictPaperShading selected shading
  coarse : Kakeya.Streamlined.TubeFamily caller.1
  coarse_nonempty : coarse.Nonempty
  coarse_centered :
    ∀ parent,
      wz2PaperCenteredLineTube (targetScale := caller.1)
          (coarse.tube parent) =
        coarse.tube parent
  midpoint_local :
    ∀ parent,
      ‖wz2PaperTubeMidpoint (coarse.tube parent)‖ ≤ 1
  strongly_separated :
    ∀ first second, first ≠ second →
      1600 * caller.1 <
        wz1PaperLineDistance
          (coarse.tube first) (coarse.tube second)
  callerCover : WZ1PaperTubeCover selected.family coarse
  section6Cover : PureWZ2Section6Cover selected.family coarse
  ordinary_distinct :
    WZ2PaperOrdinaryIsEssentiallyDistinct coarse
  complete_fiber :
    ∀ parent,
      wz2PaperFullFiberIndices
          selected.family coarse parent =
        callerCover.fiberIndices parent
  retained_mass :
    shading.mass ≤
      (pureWZ2DirectCallerConflictDegree + 1 : ENNReal) *
        selectedShading.mass

theorem pureWZ2_direct_caller_line_selection
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading fine)
    (caller : WZ2PaperRequestedScale delta)
    (deltaPos : 0 < delta)
    (fineNonempty : fine.Nonempty)
    (shadingMassPos : 0 < shading.mass)
    (fineLine : WZ1PaperIsLineClass fine) :
    Nonempty
      (PureWZ2DirectCallerLineSelectionData
        fine shading caller) := by
  let rho := caller.1
  have rhoPos : 0 < rho := deltaPos.trans_le caller.2.1
  let distance : Fin fine.card → Fin fine.card → ℝ :=
    fun first second =>
      wz1PaperLineDistance
        (fine.tube first) (fine.tube second)
  have distanceSymmetric :
      ∀ first second, distance first second = distance second first :=
    fun first second => wz1PaperLineDistance_symm _ _
  have distanceSelf : ∀ index, distance index index = 0 := by
    intro index
    have directionNe :
        wz1PaperDirection (fine.tube index) ≠ 0 := by
      intro hzero
      have hnorm := wz1PaperDirection_norm (fine.tube index)
      rw [hzero, norm_zero] at hnorm
      norm_num at hnorm
    simp [distance, wz1PaperLineDistance,
      InnerProductGeometry.angle_self directionNe]
  let net : WZ2FiniteMaximalQuotientNetData
      fine.card distance (rho / 4) :=
    Classical.choice <|
      wz2_finite_maximal_quotient_net
        fine.card fineNonempty distance distanceSymmetric
        distanceSelf (rho / 4) (by positivity)
  let centerFamily :
      Kakeya.Streamlined.TubeFamily (rho / 4) :=
    {
      card := net.centers.card
      tube := fun center =>
        wz2PaperRelabelTube (targetScale := rho / 4)
          (wz2PaperCanonicalLineTube
            (fine.tube (net.centerEmbedding center)))
    }
  have centerLine : WZ1PaperIsLineClass centerFamily := by
    intro center
    exact
      wz2PaperRelabelTube_lineClass
        (wz2PaperCanonicalLineTube_lineClass
          (fineLine (net.centerEmbedding center)))
  have centerDistinct : WZ1PaperIsEssentiallyDistinct centerFamily := by
    intro first second hne
    change
      rho / 4 <
        wz1PaperLineDistance
          (wz2PaperRelabelTube
            (wz2PaperCanonicalLineTube
              (fine.tube (net.centerEmbedding first))))
          (wz2PaperRelabelTube
            (wz2PaperCanonicalLineTube
              (fine.tube (net.centerEmbedding second))))
    rw [wz2PaperRelabelTube_lineDistance_both,
      wz1PaperLineDistance_canonicalLineTube
        (fineLine (net.centerEmbedding first))
        (fineLine (net.centerEmbedding second))]
    exact net.centers_separated first second hne
  have centerConflictDegree :
      ∀ fixed : Fin centerFamily.card,
        (Finset.univ.filter fun other =>
          other ≠ fixed ∧
            wz1PaperLineDistance
                (centerFamily.tube other)
                (centerFamily.tube fixed) ≤
              1600 * rho).card ≤
          pureWZ2DirectCallerConflictDegree := by
    intro fixed
    have packing :=
      tube_packing_bound_general centerDistinct centerLine
        (by positivity : 0 < rho / 4)
        (1600 * rho) (by positivity) fixed
    have ceilEq :
        Nat.ceil (8 * (1600 * rho) / (rho / 4)) = 51200 := by
      have algebra :
          8 * (1600 * rho) / (rho / 4) = 51200 := by
        field_simp [rhoPos.ne']
        ring
      rw [algebra]
      norm_num
    rw [ceilEq] at packing
    have subset :
        Finset.univ.filter (fun other =>
          other ≠ fixed ∧
            wz1PaperLineDistance
                (centerFamily.tube other)
                (centerFamily.tube fixed) ≤
              1600 * rho) ⊆
          Finset.univ.filter (fun other =>
            wz1PaperLineDistance
                (centerFamily.tube other)
                (centerFamily.tube fixed) ≤
              1600 * rho) := by
      intro other hother
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (Finset.mem_filter.mp hother).2.2⟩
    exact
      (Finset.card_le_card subset).trans <| by
        simpa [pureWZ2DirectCallerConflictDegree] using packing
  let centerWeight : Fin net.centers.card → ENNReal :=
    fun center =>
      ∑ source ∈ Finset.univ.filter
          (fun source => net.center source = center),
        volume (shading.carrier source)
  have totalCenterWeight :
      (∑ center : Fin net.centers.card, centerWeight center) =
        shading.mass := by
    change
      (∑ center : Fin net.centers.card,
          ∑ source ∈ Finset.univ.filter
              (fun source => net.center source = center),
            volume (shading.carrier source)) =
        ∑ source : Fin fine.card,
          volume (shading.carrier source)
    exact
      Finset.sum_fiberwise_of_maps_to
        (s := Finset.univ)
        (t := Finset.univ)
        (g := net.center)
        (fun _ _ => Finset.mem_univ _)
        (fun source => volume (shading.carrier source))
  let conflict :
      Fin net.centers.card → Fin net.centers.card → Prop :=
    fun first second =>
      second ≠ first ∧
        wz1PaperLineDistance
            (centerFamily.tube first)
            (centerFamily.tube second) ≤
          1600 * rho
  have conflictSymmetric :
      ∀ first second, conflict first second → conflict second first := by
    intro first second h
    refine ⟨h.1.symm, ?_⟩
    rw [wz1PaperLineDistance_symm]
    exact h.2
  have conflictIrreflexive : ∀ index, ¬conflict index index := by
    intro index h
    exact h.1 rfl
  have conflictDegree :
      ∀ fixed,
        (Finset.univ.filter fun other =>
          conflict fixed other).card ≤
            pureWZ2DirectCallerConflictDegree := by
    intro fixed
    have eqFilter :
        (Finset.univ.filter fun other => conflict fixed other) =
          Finset.univ.filter fun other =>
            other ≠ fixed ∧
              wz1PaperLineDistance
                  (centerFamily.tube other)
                  (centerFamily.tube fixed) ≤
                1600 * rho := by
      ext other
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h
        exact ⟨h.1, by
          rw [wz1PaperLineDistance_symm]
          exact h.2⟩
      · intro h
        exact ⟨h.1, by
          rw [wz1PaperLineDistance_symm]
          exact h.2⟩
    rw [eqFilter]
    exact centerConflictDegree fixed
  rcases
      pureWZ2_greedy_independent_set_weighted
        (D := pureWZ2DirectCallerConflictDegree)
        (weight := centerWeight)
        conflictSymmetric conflictIrreflexive
        (by
          intro fixed
          rw [Finset.filter_congr_decidable]
          exact conflictDegree fixed)
    with
    ⟨selectedCenterIndices, independent, retainedWeight⟩
  have selectedCenterIndicesNonempty :
      selectedCenterIndices.Nonempty := by
    by_contra hempty
    have hzero :
        ∑ index ∈ selectedCenterIndices,
          centerWeight index = 0 := by
      have : selectedCenterIndices = ∅ := by simpa using hempty
      rw [this]
      simp
    rw [hzero, mul_zero, totalCenterWeight] at retainedWeight
    exact (not_le_of_gt shadingMassPos) retainedWeight
  let selectedFineIndices : Finset (Fin fine.card) :=
    Finset.univ.filter fun source =>
      net.center source ∈ selectedCenterIndices
  let selected :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset
      fine selectedFineIndices
  let selectedShading :=
    restrictPaperShading selected shading
  let selectedCenterEquiv :
      Fin selectedCenterIndices.card ≃ selectedCenterIndices :=
    (selectedCenterIndices.orderIsoOfFin rfl).toEquiv
  let coarse : Kakeya.Streamlined.TubeFamily rho :=
    {
      card := selectedCenterIndices.card
      tube := fun parent =>
        wz2PaperCenteredLineTube (targetScale := rho)
          (fine.tube
            (net.centerEmbedding
              ((selectedCenterEquiv parent).1)))
    }
  let parent : Fin selected.family.card → Fin coarse.card :=
    fun source =>
      selectedCenterEquiv.symm
        ⟨net.center (selected.embedding source),
          (Finset.mem_filter.mp
            (Finset.orderEmbOfFin_mem
              selectedFineIndices rfl source)).2⟩
  have centerOfParent :
      ∀ source,
        (selectedCenterEquiv (parent source)).1 =
          net.center (selected.embedding source) := by
    intro source
    exact congrArg Subtype.val
      (selectedCenterEquiv.apply_symm_apply
        ⟨net.center (selected.embedding source),
          (Finset.mem_filter.mp
            (Finset.orderEmbOfFin_mem
              selectedFineIndices rfl source)).2⟩)
  have parentCovers :
      ∀ source,
        WZ1PaperTubeCovers
          (selected.family.tube source)
          (coarse.tube (parent source)) := by
    intro source
    let centerIndex :=
      (selectedCenterEquiv (parent source)).1
    have centerIndexEq :
        centerIndex = net.center (selected.embedding source) :=
      centerOfParent source
    unfold WZ1PaperTubeCovers
    rw [selected.tube_eq]
    change
      wz1PaperLineDistance
          (fine.tube (selected.embedding source))
          (wz2PaperCenteredLineTube
            (fine.tube (net.centerEmbedding centerIndex))) ≤
        rho / 2
    rw [wz1PaperLineDistance_centeredLineTube_right
      (fineLine (selected.embedding source))
      (fineLine (net.centerEmbedding centerIndex))]
    rw [centerIndexEq]
    exact (net.center_close (selected.embedding source)).trans <| by
      linarith
  have parentSurjective : Function.Surjective parent := by
    intro coarseParent
    let ambientCenter :=
      net.centerEmbedding (selectedCenterEquiv coarseParent).1
    have ambientSelected : ambientCenter ∈ selectedFineIndices := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [net.center_fixed]
      exact (selectedCenterEquiv coarseParent).2
    let source : Fin selected.family.card :=
      (selectedFineIndices.orderIsoOfFin rfl).symm
        ⟨ambientCenter, ambientSelected⟩
    refine ⟨source, ?_⟩
    apply selectedCenterEquiv.injective
    apply Subtype.ext
    rw [centerOfParent]
    have sourceEq :
        selected.embedding source = ambientCenter :=
      congrArg Subtype.val
        (selectedFineIndices.orderIsoOfFin rfl
          |>.apply_symm_apply
            ⟨ambientCenter, ambientSelected⟩)
    rw [sourceEq, net.center_fixed]
  have coarseStrong :
      ∀ first second, first ≠ second →
        1600 * rho <
          wz1PaperLineDistance
            (coarse.tube first) (coarse.tube second) := by
    intro first second hne
    have selectedNe :
        (selectedCenterEquiv first).1 ≠
          (selectedCenterEquiv second).1 := by
      intro heq
      exact hne (selectedCenterEquiv.injective (Subtype.ext heq))
    have notConflict :=
      independent
        (selectedCenterEquiv first).1 (selectedCenterEquiv first).2
        (selectedCenterEquiv second).1 (selectedCenterEquiv second).2
        selectedNe
    have notLe :
        ¬wz1PaperLineDistance
            (centerFamily.tube (selectedCenterEquiv first).1)
            (centerFamily.tube (selectedCenterEquiv second).1) ≤
          1600 * rho := by
      intro hle
      exact notConflict ⟨selectedNe.symm, hle⟩
    change
      1600 * rho <
        wz1PaperLineDistance
          (wz2PaperCenteredLineTube
            (fine.tube
              (net.centerEmbedding
                (selectedCenterEquiv first).1)))
          (wz2PaperCenteredLineTube
            (fine.tube
              (net.centerEmbedding
                (selectedCenterEquiv second).1)))
    rw [wz1PaperLineDistance_centeredLineTube_both
        (fineLine
          (net.centerEmbedding (selectedCenterEquiv first).1))
        (fineLine
          (net.centerEmbedding (selectedCenterEquiv second).1))]
    apply lt_of_not_ge
    intro hle
    apply notLe
    change
      wz1PaperLineDistance
          (wz2PaperRelabelTube
            (targetScale := rho / 4)
            (wz2PaperCanonicalLineTube
              (fine.tube
                (net.centerEmbedding
                  (selectedCenterEquiv first).1))))
          (wz2PaperRelabelTube
            (targetScale := rho / 4)
            (wz2PaperCanonicalLineTube
              (fine.tube
                (net.centerEmbedding
                  (selectedCenterEquiv second).1)))) ≤
        1600 * rho
    rw [wz2PaperRelabelTube_lineDistance_both,
      wz1PaperLineDistance_canonicalLineTube
        (fineLine
          (net.centerEmbedding (selectedCenterEquiv first).1))
        (fineLine
          (net.centerEmbedding (selectedCenterEquiv second).1))]
    exact hle
  let callerCover : WZ1PaperTubeCover selected.family coarse :=
    {
      parent := parent
      parent_surjective := parentSurjective
      parent_covers := parentCovers
      parent_unique := by
        intro source candidate candidateCovers
        by_contra hne
        have separated :=
          coarseStrong candidate (parent source) hne
        have triangle :=
          wz1PaperLineDistance_triangle
            (coarse.tube candidate)
            (selected.family.tube source)
            (coarse.tube (parent source))
        have symmetry :
            wz1PaperLineDistance
                (coarse.tube candidate)
                (selected.family.tube source) =
              wz1PaperLineDistance
                (selected.family.tube source)
                (coarse.tube candidate) :=
          wz1PaperLineDistance_symm _ _
        rw [symmetry] at triangle
        unfold WZ1PaperTubeCovers at candidateCovers parentCovers
        exact
          (not_le_of_gt separated)
            (triangle.trans (by
              linarith [candidateCovers, parentCovers source]))
    }
  let section6Cover : PureWZ2Section6Cover selected.family coarse :=
    {
      fine_line_class := fineLine.subfamily selected
      coarse_line_class := by
        intro coarseParent
        exact
          wz2PaperCenteredLineTube_lineClass
            (fineLine
              (net.centerEmbedding
                (selectedCenterEquiv coarseParent).1))
      covers := fun source =>
        ⟨callerCover.parent source, callerCover.parent_covers source⟩
      parent_hit := by
        intro coarseParent
        rcases callerCover.parent_surjective coarseParent with
          ⟨source, hsource⟩
        exact ⟨source, hsource ▸ callerCover.parent_covers source⟩
      coarse_essentially_distinct := by
        intro first second hne
        exact
          (show rho < 1600 * rho by nlinarith [rhoPos]).trans
            (coarseStrong first second hne)
    }
  have coarseOrdinaryDistinct :
      WZ2PaperOrdinaryIsEssentiallyDistinct coarse :=
    wz2_paper_localized_ordinary_isEssentiallyDistinct
      rhoPos section6Cover.coarse_line_class
      (by
        intro coarseParent
        change
          ‖wz2PaperTubeMidpoint
            (wz2PaperCenteredLineTube
              (fine.tube
                (net.centerEmbedding
                  (selectedCenterEquiv coarseParent).1)))‖ ≤ 3
        exact
          wz2PaperCenteredLineTube_midpoint_norm_le_one
            (fineLine
              (net.centerEmbedding
                (selectedCenterEquiv coarseParent).1))
            |>.trans (by norm_num))
      (by
        intro first second hne
        have strong := coarseStrong first second hne
        dsimp only [
          wz2PaperLocalizedDoubledFiberLineDistanceConstant
        ]
        linarith)
  have selectedMassEq :
      selectedShading.mass =
        ∑ center ∈ selectedCenterIndices,
          centerWeight center := by
    rw [restrictPaperShading_mass]
    let equivalence :
        Fin selected.family.card ≃ selectedFineIndices :=
      (selectedFineIndices.orderIsoOfFin rfl).toEquiv
    calc
      (∑ source : Fin selected.family.card,
          volume (shading.carrier (selected.embedding source))) =
          ∑ source ∈ selectedFineIndices,
            volume (shading.carrier source) := by
        exact
          (Fintype.sum_equiv equivalence
            (fun source : Fin selected.family.card =>
              volume (shading.carrier (selected.embedding source)))
            (fun source : selectedFineIndices =>
              volume (shading.carrier source.1))
            (fun _ => rfl)).trans
            (Finset.sum_coe_sort selectedFineIndices
              (fun source => volume (shading.carrier source)))
      _ =
          ∑ center ∈ selectedCenterIndices,
            centerWeight center := by
        have fiberwise :=
          Finset.sum_fiberwise_of_maps_to
            (s := selectedFineIndices)
            (t := selectedCenterIndices)
            (g := net.center)
            (fun source hsource =>
              (Finset.mem_filter.mp hsource).2)
            (fun source => volume (shading.carrier source))
        rw [fiberwise.symm]
        apply Finset.sum_congr rfl
        intro center centerSelected
        unfold centerWeight
        apply Finset.sum_congr
        · ext source
          simp only [selectedFineIndices, Finset.mem_filter,
            Finset.mem_univ, true_and]
          constructor
          · exact fun h => h.2
          · intro h
            exact ⟨h ▸ centerSelected, h⟩
        · intro _ _
          rfl
  have completeFiber :
      ∀ coarseParent,
        wz2PaperFullFiberIndices
            selected.family coarse coarseParent =
          callerCover.fiberIndices coarseParent := by
    intro coarseParent
    ext source
    simp only [mem_wz2PaperFullFiberIndices_iff,
      WZ1PaperTubeCover.fiberIndices, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · intro sourceCovers
      exact
        (callerCover.parent_unique
          source coarseParent sourceCovers).symm
    · intro parentEq
      rw [← parentEq]
      exact callerCover.parent_covers source
  exact
    ⟨{
      caller_pos := rhoPos
      selected := selected
      selected_nonempty := by
        rcases selectedCenterIndicesNonempty with
          ⟨center, centerSelected⟩
        have ambientSelected :
            net.centerEmbedding center ∈ selectedFineIndices := by
          apply Finset.mem_filter.mpr
          refine ⟨Finset.mem_univ _, ?_⟩
          rw [net.center_fixed]
          exact centerSelected
        change 0 < selectedFineIndices.card
        exact Finset.card_pos.mpr
          ⟨net.centerEmbedding center, ambientSelected⟩
      ambient_line_class := fineLine
      selectedShading := selectedShading
      selectedShading_eq := rfl
      coarse := coarse
      coarse_nonempty := by
        change 0 < selectedCenterIndices.card
        exact selectedCenterIndicesNonempty.card_pos
      coarse_centered := by
        intro parent
        change
          wz2PaperCenteredLineTube (targetScale := rho)
              (wz2PaperCenteredLineTube (targetScale := rho)
                (fine.tube
                  (net.centerEmbedding
                    (selectedCenterEquiv parent).1))) =
            wz2PaperCenteredLineTube (targetScale := rho)
              (fine.tube
                (net.centerEmbedding
                  (selectedCenterEquiv parent).1))
        exact
          wz2PaperCenteredLineTube_recenter
            (sourceScale := delta)
            (middleScale := rho)
            (targetScale := rho)
            (fineLine
              (net.centerEmbedding
                (selectedCenterEquiv parent).1))
      midpoint_local := by
        intro parent
        exact
          wz2PaperCenteredLineTube_midpoint_norm_le_one
            (fineLine
              (net.centerEmbedding
                (selectedCenterEquiv parent).1))
      strongly_separated := coarseStrong
      callerCover := callerCover
      section6Cover := section6Cover
      ordinary_distinct := coarseOrdinaryDistinct
      complete_fiber := completeFiber
      retained_mass := by
        rw [selectedMassEq, ← totalCenterWeight]
        exact retainedWeight
    }⟩

end Kakeya.Assouad

end
