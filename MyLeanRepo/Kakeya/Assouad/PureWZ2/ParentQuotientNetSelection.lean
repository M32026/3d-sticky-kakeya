import MyLeanRepo.Kakeya.Assouad.PureWZ2.FiniteMaximalQuotientNet
import MyLeanRepo.Kakeya.Assouad.PureWZ2.ParentLevelWholeFiberSelection
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12LocalizedDoubledFiber
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralSeparationConstants

/-!
# Quotient-net selection of complete actual fibers

Actual Definition 2.12 parents may repeat the same supporting line at
different longitudinal positions, so their caller-scale line-conflict graph
need not have bounded degree.  The correct construction first forms a maximal
`caller / 4` net in the supporting-line metric.  All actual parents assigned
to one center remain whole; no actual complete fiber is cut.

The net centers are already essentially distinct at radius `caller / 4`.
Finite line packing therefore bounds their `1600 * caller` conflict degree by
an absolute constant.  Weighted independent selection on the center weights
retains a fixed share of total shaded mass.  The resulting caller WZ fiber is
proved to be exactly the union of the complete actual strict fibers assigned
to its selected center.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

/-- Absolute packing degree for a `1600 * caller` neighborhood of a
`caller / 4`-separated line net. -/
def pureWZ2ParentQuotientNetConflictDegree : ℕ :=
  102401 ^ 5

/--
One mass-retaining caller WZ cover obtained from a quotient net of actual
Definition 2.12 parents.
-/
structure PureWZ2ParentQuotientNetSelectionData
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {requested : WZ2PaperRequestedScale delta}
    {C : ENNReal}
    (nearby :
      WZ2PaperPureNearbyScaleCoverData fine requested C)
    (caller : WZ2PaperRequestedScale delta)
    (shading : WZ1PaperTubeShading fine) where
  representative :
    Fin nearby.scaleData.coarse.card →
      Fin fine.card
  representative_mem :
    ∀ parent,
      representative parent ∈
        wz2PaperOrdinaryFullFiberIndices
          fine nearby.scaleData.coarse parent
  net :
    WZ2FiniteMaximalQuotientNetData
      nearby.scaleData.coarse.card
      (fun first second =>
        wz1PaperLineDistance
          (fine.tube (representative first))
          (fine.tube (representative second)))
      (caller.1 / 4)
  selectedCenters :
    Finset (Fin net.centers.card)
  selectedCenters_nonempty :
    selectedCenters.Nonempty
  selectedCenterEmbedding :
    Fin selectedCenters.card ↪ Fin net.centers.card
  selectedCenterEmbedding_eq :
    selectedCenterEmbedding =
      (selectedCenters.orderEmbOfFin rfl).toEmbedding
  selectedActualParents :
    Finset (Fin nearby.scaleData.coarse.card)
  selectedActualParents_eq :
    selectedActualParents =
      Finset.univ.filter fun actual =>
        net.center actual ∈ selectedCenters
  selectedFineIndices : Finset (Fin fine.card)
  selectedFineIndices_eq :
    selectedFineIndices =
      Finset.univ.filter fun source =>
        nearby.scaleData.cover.parent source ∈
          selectedActualParents
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
  callerCenter :
    Fin callerCoarse.card ↪ Fin net.centers.card
  callerCenter_mem :
    ∀ parent, callerCenter parent ∈ selectedCenters
  caller_tube_eq :
    ∀ parent,
      callerCoarse.tube parent =
        wz2PaperRelabelTube
          (targetScale := caller.1)
          (wz2PaperCanonicalLineTube
            (fine.tube
              (representative
                (net.centerEmbedding
                  (callerCenter parent)))))
  caller_strongly_separated :
    ∀ first second, first ≠ second →
      1600 * caller.1 <
        wz1PaperLineDistance
          (callerCoarse.tube first)
          (callerCoarse.tube second)
  caller_midpoint_norm_le_six :
    ∀ parent,
      ‖wz2PaperTubeMidpoint
        (callerCoarse.tube parent)‖ ≤ 6
  callerCover :
    WZ1PaperTubeCover selected.family callerCoarse
  section6Cover :
    PureWZ2Section6Cover selected.family callerCoarse
  ambient_fine_line_class :
    WZ1PaperIsLineClass fine
  center_compatibility :
    ∀ source,
      net.center
          (nearby.scaleData.cover.parent
            (selected.embedding source)) =
        callerCenter (callerCover.parent source)
  complete_actual_fiber_union :
    ∀ parent : Fin callerCoarse.card,
      Finset.image selected.embedding
          (wz2PaperFullFiberIndices
            selected.family callerCoarse parent) =
        Finset.biUnion
          (Finset.univ.filter fun actual =>
            net.center actual = callerCenter parent)
          (wz2PaperOrdinaryFullFiberIndices
            fine nearby.scaleData.coarse)
  retained_mass :
    shading.mass ≤
      (pureWZ2ParentQuotientNetConflictDegree : ENNReal) *
        selectedShading.mass
  actual_full_fiber_uniform :
    WZ2PaperPureFullFibersAreCUniform
      fine nearby.scaleData.coarse C
  actual_rescaledFiber :
    ∀ parent : Fin callerCoarse.card,
      ∀ actual,
        net.center actual = callerCenter parent →
          Nonempty
            (WZ2PaperPureUnitRescaledFullFiberData
              (fine := fine)
              (coarse := nearby.scaleData.coarse)
              actual C)

theorem PureWZ2ParentQuotientNetSelectionData.selected_ambient_surjective
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {requested : WZ2PaperRequestedScale delta}
    {C : ENNReal}
    {nearby :
      WZ2PaperPureNearbyScaleCoverData fine requested C}
    {caller : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    (data :
      PureWZ2ParentQuotientNetSelectionData
        nearby caller shading) :
    ∀ source ∈ data.selectedFineIndices,
      ∃ selectedSource : Fin data.selected.family.card,
        data.selected.embedding selectedSource = source := by
  rw [data.selected_eq]
  intro source hsource
  let member : data.selectedFineIndices :=
    ⟨source, hsource⟩
  let selectedSource :
      Fin (Kakeya.Streamlined.TubeSubfamily.fromFinset
        fine data.selectedFineIndices).family.card :=
    (data.selectedFineIndices.orderIsoOfFin rfl).symm member
  exact
    ⟨selectedSource,
      congrArg Subtype.val
        (data.selectedFineIndices.orderIsoOfFin rfl
          |>.apply_symm_apply member)⟩

/--
The ambient fine tube used as the center of a quotient caller belongs to the
complete actual fiber indexed by that center.
-/
theorem PureWZ2ParentQuotientNetSelectionData.callerCenterSource_mem
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {requested : WZ2PaperRequestedScale delta}
    {C : ENNReal}
    {nearby :
      WZ2PaperPureNearbyScaleCoverData fine requested C}
    {caller : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    (data :
      PureWZ2ParentQuotientNetSelectionData
        nearby caller shading)
    (parent : Fin data.callerCoarse.card) :
    data.representative
          (data.net.centerEmbedding
            (data.callerCenter parent)) ∈
      wz2PaperOrdinaryFullFiberIndices
        fine nearby.scaleData.coarse
        (data.net.centerEmbedding
          (data.callerCenter parent)) :=
  data.representative_mem _

/--
Distinct quotient callers have distinct ambient center sources.  The actual
pure cover recovers the selected center actual parent from its representative,
and both center embeddings are injective.
-/
theorem PureWZ2ParentQuotientNetSelectionData.callerCenterSource_injective
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {requested : WZ2PaperRequestedScale delta}
    {C : ENNReal}
    {nearby :
      WZ2PaperPureNearbyScaleCoverData fine requested C}
    {caller : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    (data :
      PureWZ2ParentQuotientNetSelectionData
        nearby caller shading) :
    Function.Injective fun parent : Fin data.callerCoarse.card =>
      data.representative
        (data.net.centerEmbedding
          (data.callerCenter parent)) := by
  intro first second hsource
  apply data.callerCenter.injective
  apply data.net.centerEmbedding.injective
  have hfirst :
      nearby.scaleData.cover.parent
          (data.representative
            (data.net.centerEmbedding
              (data.callerCenter first))) =
        data.net.centerEmbedding
          (data.callerCenter first) :=
    (nearby.scaleData.cover.mem_fullFiber_iff_parent_eq
      nearby.scaleData.rho_pos.le
      (data.net.centerEmbedding
        (data.callerCenter first))
      (data.representative
        (data.net.centerEmbedding
          (data.callerCenter first)))).mp
      (data.callerCenterSource_mem first)
  have hsecond :
      nearby.scaleData.cover.parent
          (data.representative
            (data.net.centerEmbedding
              (data.callerCenter second))) =
        data.net.centerEmbedding
          (data.callerCenter second) :=
    (nearby.scaleData.cover.mem_fullFiber_iff_parent_eq
      nearby.scaleData.rho_pos.le
      (data.net.centerEmbedding
        (data.callerCenter second))
      (data.representative
        (data.net.centerEmbedding
          (data.callerCenter second)))).mp
      (data.callerCenterSource_mem second)
  have hsource' :
      data.representative
          (data.net.centerEmbedding
            (data.callerCenter first)) =
        data.representative
          (data.net.centerEmbedding
            (data.callerCenter second)) :=
    hsource
  calc
    data.net.centerEmbedding (data.callerCenter first) =
        nearby.scaleData.cover.parent
          (data.representative
            (data.net.centerEmbedding
              (data.callerCenter first))) :=
      hfirst.symm
    _ =
        nearby.scaleData.cover.parent
          (data.representative
            (data.net.centerEmbedding
              (data.callerCenter second))) := by
      rw [hsource']
    _ = data.net.centerEmbedding (data.callerCenter second) :=
      hsecond

/--
The quotient caller stores a genuine ordinary common child: its center source
tube is contained in the caller tube after the prescribed same-axis radius
relabeling.
-/
theorem PureWZ2ParentQuotientNetSelectionData.callerCenterSource_carrier_subset
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {requested : WZ2PaperRequestedScale delta}
    {C : ENNReal}
    {nearby :
      WZ2PaperPureNearbyScaleCoverData fine requested C}
    {caller : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    (data :
      PureWZ2ParentQuotientNetSelectionData
        nearby caller shading)
    (parent : Fin data.callerCoarse.card) :
    (fine.tube
      (data.representative
        (data.net.centerEmbedding
          (data.callerCenter parent)))).carrier ⊆
      (data.callerCoarse.tube parent).carrier := by
  rw [data.caller_tube_eq parent,
    ← wz2PaperCanonicalLineTube_carrier]
  unfold Kakeya.DeltaTube.carrier
  dsimp only [wz2PaperRelabelTube]
  exact
    Metric.cthickening_mono caller.2.1
      (Kakeya.unitSegment
        (wz2PaperCanonicalLineTube
          (fine.tube
            (data.representative
              (data.net.centerEmbedding
                (data.callerCenter parent))))).base
        (wz2PaperCanonicalLineTube
          (fine.tube
            (data.representative
              (data.net.centerEmbedding
                (data.callerCenter parent))))).direction)

/--
The quotient caller family is essentially distinct in the ordinary Assouad
centered-dilation sense.
-/
theorem PureWZ2ParentQuotientNetSelectionData.caller_ordinary_distinct
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {requested : WZ2PaperRequestedScale delta}
    {C : ENNReal}
    {nearby :
      WZ2PaperPureNearbyScaleCoverData fine requested C}
    {caller : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    (data :
      PureWZ2ParentQuotientNetSelectionData
        nearby caller shading) :
    WZ2PaperOrdinaryIsEssentiallyDistinct
      data.callerCoarse := by
  intro first second hne
  constructor
  · intro hcontained
    have hdistance :=
      wz2_paper_bounded_centered_doubled_containment_lineDistance_le
        (nearby.scaleData.delta_pos.trans_le caller.2.1)
        (nearby.scaleData.delta_pos.trans_le caller.2.1)
        (data.section6Cover.coarse_line_class first)
        (data.section6Cover.coarse_line_class second)
        6
        (data.caller_midpoint_norm_le_six first)
        hcontained
    have hseparated :=
      data.caller_strongly_separated first second hne
    have hcaller :
        0 < caller.1 :=
      nearby.scaleData.delta_pos.trans_le caller.2.1
    norm_num at hdistance
    linarith
  · intro hcontained
    have hdistance :=
      wz2_paper_bounded_centered_doubled_containment_lineDistance_le
        (nearby.scaleData.delta_pos.trans_le caller.2.1)
        (nearby.scaleData.delta_pos.trans_le caller.2.1)
        (data.section6Cover.coarse_line_class second)
        (data.section6Cover.coarse_line_class first)
        6
        (data.caller_midpoint_norm_le_six second)
        hcontained
    have hseparated :=
      data.caller_strongly_separated second first hne.symm
    have hcaller :
        0 < caller.1 :=
      nearby.scaleData.delta_pos.trans_le caller.2.1
    norm_num at hdistance
    linarith

/--
Any ambient fine tube in an actual class assigned to a quotient caller is
line-covered by that caller.  This is the reusable provenance form of the
cover constructed inside `pure_wz2_parent_quotient_net_selection`.
-/
theorem PureWZ2ParentQuotientNetSelectionData.caller_covers_of_actual_center
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {requested : WZ2PaperRequestedScale delta}
    {C : ENNReal}
    {nearby :
      WZ2PaperPureNearbyScaleCoverData fine requested C}
    {caller : WZ2PaperRequestedScale delta}
    {shading : WZ1PaperTubeShading fine}
    (data :
      PureWZ2ParentQuotientNetSelectionData
        nearby caller shading)
    (source : Fin fine.card)
    (actualParent : Fin nearby.scaleData.coarse.card)
    (callerParent : Fin data.callerCoarse.card)
    (sourceParent :
      nearby.scaleData.cover.parent source = actualParent)
    (actualCenter :
      data.net.center actualParent =
        data.callerCenter callerParent) :
    WZ1PaperTubeCovers
      (fine.tube source)
      (data.callerCoarse.tube callerParent) := by
  have centerSelected :
      data.net.center actualParent ∈ data.selectedCenters := by
    rw [actualCenter]
    exact data.callerCenter_mem callerParent
  have actualSelected :
      actualParent ∈ data.selectedActualParents := by
    rw [data.selectedActualParents_eq]
    exact
      Finset.mem_filter.mpr
        ⟨Finset.mem_univ actualParent, centerSelected⟩
  have sourceSelected :
      source ∈ data.selectedFineIndices := by
    rw [data.selectedFineIndices_eq]
    exact
      Finset.mem_filter.mpr
        ⟨Finset.mem_univ source,
          sourceParent.symm ▸ actualSelected⟩
  rcases
      data.selected_ambient_surjective source sourceSelected
    with
    ⟨selectedSource, selectedSourceEq⟩
  have callerParentEq :
      data.callerCover.parent selectedSource =
        callerParent := by
    apply data.callerCenter.injective
    rw [← data.center_compatibility selectedSource,
      selectedSourceEq, sourceParent, actualCenter]
  have hcover :=
    data.callerCover.parent_covers selectedSource
  rw [data.selected.tube_eq, selectedSourceEq,
    callerParentEq] at hcover
  exact hcover

/--
Construct the quotient net and select a fixed-mass share of its centers.

The scale gap `2400000 * actual ≤ caller` splits the caller line-cover budget
equally between motion inside one actual complete fiber and motion from its
representative to the quotient-net center.
-/
theorem pure_wz2_parent_quotient_net_selection
    {delta : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {requested : WZ2PaperRequestedScale delta}
    {C : ENNReal}
    (nearby :
      WZ2PaperPureNearbyScaleCoverData fine requested C)
    (caller : WZ2PaperRequestedScale delta)
    (shading : WZ1PaperTubeShading fine)
    (fineNonempty : fine.Nonempty)
    (shadingMassPos : 0 < shading.mass)
    (fineLine : WZ1PaperIsLineClass fine)
    (fineBase :
      ∀ source, ‖(fine.tube source).base‖ ≤ 5)
    (actualSmall : nearby.rho ≤ 1 / 10000)
    (actualCaller :
      2400000 * nearby.rho ≤ caller.1) :
    Nonempty
      (PureWZ2ParentQuotientNetSelectionData
        nearby caller shading) := by
  have actualPos : 0 < nearby.rho :=
    nearby.scaleData.rho_pos
  have callerPos : 0 < caller.1 := by
    have hscaled : 0 < 2400000 * nearby.rho := by
      positivity
    exact hscaled.trans_le actualCaller
  have deltaActual : delta ≤ nearby.rho :=
    requested.2.1.trans nearby.requested_le
  have actualFibersNonempty :
      ∀ parent : Fin nearby.scaleData.coarse.card,
        (wz2PaperOrdinaryFullFiberIndices
          fine nearby.scaleData.coarse parent).Nonempty :=
    nearby.scaleData.cover.fullFiber_nonempty_of_uniform
      fineNonempty nearby.scaleData.full_fiber_uniform
  let representative :
      Fin nearby.scaleData.coarse.card → Fin fine.card :=
    fun parent =>
      Classical.choose (actualFibersNonempty parent)
  have representativeMem :
      ∀ parent,
        representative parent ∈
          wz2PaperOrdinaryFullFiberIndices
            fine nearby.scaleData.coarse parent :=
    fun parent =>
      Classical.choose_spec (actualFibersNonempty parent)
  let parentDistance :
      Fin nearby.scaleData.coarse.card →
        Fin nearby.scaleData.coarse.card → ℝ :=
    fun first second =>
      wz1PaperLineDistance
        (fine.tube (representative first))
        (fine.tube (representative second))
  have parentDistanceSymmetric :
      ∀ first second,
        parentDistance first second =
          parentDistance second first := by
    intro first second
    exact wz1PaperLineDistance_symm _ _
  have representativeDirectionNonzero :
      ∀ parent,
        wz1PaperDirection
            (fine.tube (representative parent)) ≠ 0 := by
    intro parent hzero
    have hnorm :=
      wz1PaperDirection_norm
        (fine.tube (representative parent))
    rw [hzero] at hnorm
    norm_num at hnorm
  have parentDistanceSelf :
      ∀ parent, parentDistance parent parent = 0 := by
    intro parent
    simp [parentDistance, wz1PaperLineDistance,
      InnerProductGeometry.angle_self
        (representativeDirectionNonzero parent)]
  have actualParentCountPos :
      0 < nearby.scaleData.coarse.card := by
    rcases
        nearby.scaleData.cover.covers
          ⟨0, fineNonempty⟩
      with
      ⟨parent, _⟩
    exact lt_of_le_of_lt (Nat.zero_le parent.val) parent.isLt
  rcases
      wz2_finite_maximal_quotient_net
        nearby.scaleData.coarse.card actualParentCountPos
        parentDistance parentDistanceSymmetric
        parentDistanceSelf (caller.1 / 4)
        (by positivity)
    with
    ⟨net⟩
  let centerFamily :
      Kakeya.Streamlined.TubeFamily (caller.1 / 4) :=
    {
      card := net.centers.card
      tube := fun center =>
        wz2PaperRelabelTube
          (targetScale := caller.1 / 4)
          (wz2PaperCanonicalLineTube
            (fine.tube
              (representative
                (net.centerEmbedding center))))
    }
  have centerFamilyLine :
      WZ1PaperIsLineClass centerFamily := by
    intro center
    exact
      wz2PaperRelabelTube_lineClass
        (wz2PaperCanonicalLineTube_lineClass
          (fineLine
            (representative
              (net.centerEmbedding center))))
  have centerFamilyDistinct :
      WZ1PaperIsEssentiallyDistinct centerFamily := by
    intro first second hne
    have hseparated :=
      net.centers_separated first second hne
    change
      caller.1 / 4 <
        wz1PaperLineDistance
          (wz2PaperRelabelTube
            (wz2PaperCanonicalLineTube
              (fine.tube
                (representative
                  (net.centerEmbedding first)))))
          (wz2PaperRelabelTube
            (wz2PaperCanonicalLineTube
              (fine.tube
                (representative
                  (net.centerEmbedding second)))))
    rw [wz2PaperRelabelTube_lineDistance_both,
      wz1PaperLineDistance_canonicalLineTube
        (fineLine
          (representative
            (net.centerEmbedding first)))
        (fineLine
          (representative
            (net.centerEmbedding second)))]
    exact hseparated
  have centerConflictDegree :
      ∀ fixed : Fin centerFamily.card,
        (Finset.univ.filter fun other =>
          wz1PaperLineDistance
              (centerFamily.tube other)
              (centerFamily.tube fixed) ≤
            1600 * caller.1).card ≤
          pureWZ2ParentQuotientNetConflictDegree := by
    intro fixed
    have hpacking :=
      tube_packing_bound_general
        centerFamilyDistinct centerFamilyLine
        (by positivity : 0 < caller.1 / 4)
        (1600 * caller.1)
        (by positivity)
        fixed
    have hceil :
        Nat.ceil
            (8 * (1600 * caller.1) /
              (caller.1 / 4)) =
          51200 := by
      have halgebra :
          8 * (1600 * caller.1) /
              (caller.1 / 4) =
            51200 := by
        field_simp [callerPos.ne']
        ring
      rw [halgebra]
      norm_num
    rw [hceil] at hpacking
    simpa [pureWZ2ParentQuotientNetConflictDegree]
      using hpacking
  let actualWeight :
      Fin nearby.scaleData.coarse.card → ENNReal :=
    pureWZ2ActualFiberShadedMass shading
  let centerWeight :
      Fin net.centers.card → ENNReal :=
    fun center =>
      ∑ actual ∈ Finset.univ.filter
          (fun actual =>
            net.center actual = center),
        actualWeight actual
  have totalActualWeight :
      (∑ actual : Fin nearby.scaleData.coarse.card,
          actualWeight actual) =
        shading.mass :=
    sum_pureWZ2ActualFiberShadedMass
      nearby.scaleData.cover actualPos.le shading
  have totalCenterWeight :
      (∑ center : Fin net.centers.card,
          centerWeight center) =
        ∑ actual : Fin nearby.scaleData.coarse.card,
          actualWeight actual := by
    exact
      Finset.sum_fiberwise_of_maps_to
        (s := Finset.univ)
        (t := Finset.univ)
        (g := net.center)
        (fun _ _ => Finset.mem_univ _)
        actualWeight
  let adjacent :
      Fin net.centers.card →
        Fin net.centers.card → Prop :=
    fun first second =>
      wz1PaperLineDistance
          (centerFamily.tube first)
          (centerFamily.tube second) ≤
        1600 * caller.1
  have adjacentReflexive :
      ∀ center, adjacent center center := by
    intro center
    have hdirection :
        wz1PaperDirection
            (centerFamily.tube center) ≠ 0 := by
      intro hzero
      have hnorm :=
        wz1PaperDirection_norm
          (centerFamily.tube center)
      rw [hzero] at hnorm
      norm_num at hnorm
    have hzero :
        wz1PaperLineDistance
            (centerFamily.tube center)
            (centerFamily.tube center) = 0 := by
      simp [wz1PaperLineDistance,
        InnerProductGeometry.angle_self hdirection]
    change
      wz1PaperLineDistance
          (centerFamily.tube center)
          (centerFamily.tube center) ≤
        1600 * caller.1
    rw [hzero]
    positivity
  have adjacentSymmetric :
      ∀ first second,
        adjacent first second →
          adjacent second first := by
    intro first second hadjacent
    change
      wz1PaperLineDistance
          (centerFamily.tube second)
          (centerFamily.tube first) ≤
        1600 * caller.1
    rw [wz1PaperLineDistance_symm]
    exact hadjacent
  have adjacentDegree :
      ∀ center,
        (Finset.univ.filter
          (adjacent center)).card ≤
          pureWZ2ParentQuotientNetConflictDegree := by
    intro center
    have heq :
        (Finset.univ.filter
            (adjacent center)) =
          Finset.univ.filter fun other =>
            wz1PaperLineDistance
                (centerFamily.tube other)
                (centerFamily.tube center) ≤
              1600 * caller.1 := by
      ext other
      simp only [Finset.mem_filter,
        Finset.mem_univ, true_and]
      change
        wz1PaperLineDistance
              (centerFamily.tube center)
              (centerFamily.tube other) ≤
            1600 * caller.1 ↔
          wz1PaperLineDistance
              (centerFamily.tube other)
              (centerFamily.tube center) ≤
            1600 * caller.1
      rw [wz1PaperLineDistance_symm]
    rw [heq]
    exact centerConflictDegree center
  rcases
      exists_independent_set_mass_retention
        centerWeight adjacent
        adjacentReflexive adjacentSymmetric
        pureWZ2ParentQuotientNetConflictDegree
        adjacentDegree
    with
    ⟨selectedCenters, selectedIndependent,
      retainedCenterWeight⟩
  have selectedCentersNonempty :
      selectedCenters.Nonempty := by
    by_contra hnonempty
    have hempty : selectedCenters = ∅ := by
      simpa using hnonempty
    rw [hempty] at retainedCenterWeight
    simp only [Finset.sum_empty, mul_zero]
      at retainedCenterWeight
    rw [totalCenterWeight, totalActualWeight]
      at retainedCenterWeight
    exact
      (not_le_of_gt shadingMassPos)
        retainedCenterWeight
  let selectedCenterEmbedding :
      Fin selectedCenters.card ↪
        Fin net.centers.card :=
    (selectedCenters.orderEmbOfFin rfl).toEmbedding
  let selectedActualParents :
      Finset (Fin nearby.scaleData.coarse.card) :=
    Finset.univ.filter fun actual =>
      net.center actual ∈ selectedCenters
  let selectedFineIndices :
      Finset (Fin fine.card) :=
    Finset.univ.filter fun source =>
      nearby.scaleData.cover.parent source ∈
        selectedActualParents
  let selected :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset
      fine selectedFineIndices
  let selectedShading :=
    restrictPaperShading selected shading
  have selectedEmbeddingMem :
      ∀ source : Fin selected.family.card,
        selected.embedding source ∈
          selectedFineIndices := by
    intro source
    exact
      Finset.orderEmbOfFin_mem
        selectedFineIndices rfl source
  have selectedAmbientSurjective :
      ∀ source ∈ selectedFineIndices,
        ∃ selectedSource : Fin selected.family.card,
          selected.embedding selectedSource = source := by
    intro source hsource
    let member : selectedFineIndices :=
      ⟨source, hsource⟩
    let selectedSource : Fin selected.family.card :=
      (selectedFineIndices.orderIsoOfFin rfl).symm member
    exact
      ⟨selectedSource,
        congrArg Subtype.val
          (selectedFineIndices.orderIsoOfFin rfl
            |>.apply_symm_apply member)⟩
  let selectedCenterEquiv :
      Fin selectedCenters.card ≃ selectedCenters :=
    (selectedCenters.orderIsoOfFin rfl).toEquiv
  let callerCoarse :
      Kakeya.Streamlined.TubeFamily caller.1 :=
    {
      card := selectedCenters.card
      tube := fun callerParent =>
        wz2PaperRelabelTube
          (targetScale := caller.1)
          (wz2PaperCanonicalLineTube
            (fine.tube
              (representative
                (net.centerEmbedding
                  (selectedCenterEmbedding callerParent)))))
    }
  let callerParent :
      Fin selected.family.card →
        Fin callerCoarse.card :=
    fun source =>
      selectedCenterEquiv.symm
        ⟨net.center
            (nearby.scaleData.cover.parent
              (selected.embedding source)),
          (Finset.mem_filter.mp
            ((Finset.mem_filter.mp
              (selectedEmbeddingMem source)).2)).2⟩
  have centerCompatibility :
      ∀ source,
        net.center
            (nearby.scaleData.cover.parent
              (selected.embedding source)) =
          selectedCenterEmbedding
            (callerParent source) := by
    intro source
    exact
      (congrArg Subtype.val
        (selectedCenterEquiv.apply_symm_apply
          ⟨net.center
              (nearby.scaleData.cover.parent
                (selected.embedding source)),
            (Finset.mem_filter.mp
              ((Finset.mem_filter.mp
                (selectedEmbeddingMem source)).2)).2⟩)).symm
  have callerCoarseLine :
      WZ1PaperIsLineClass callerCoarse := by
    intro callerParent
    exact
      wz2PaperRelabelTube_lineClass
        (wz2PaperCanonicalLineTube_lineClass
          (fineLine
            (representative
              (net.centerEmbedding
                (selectedCenterEmbedding callerParent)))))
  have callerStronglySeparated :
      ∀ first second : Fin callerCoarse.card,
        first ≠ second →
          1600 * caller.1 <
            wz1PaperLineDistance
              (callerCoarse.tube first)
              (callerCoarse.tube second) := by
    intro first second hne
    have ambientNe :
        selectedCenterEmbedding first ≠
          selectedCenterEmbedding second :=
      selectedCenterEmbedding.injective.ne hne
    have firstMem :
        selectedCenterEmbedding first ∈
          selectedCenters :=
      Finset.orderEmbOfFin_mem
        selectedCenters rfl first
    have secondMem :
        selectedCenterEmbedding second ∈
          selectedCenters :=
      Finset.orderEmbOfFin_mem
        selectedCenters rfl second
    have hnot :=
      selectedIndependent
        (selectedCenterEmbedding first) firstMem
        (selectedCenterEmbedding second) secondMem
        ambientNe
    have hnot' :
        ¬wz1PaperLineDistance
              (centerFamily.tube
                (selectedCenterEmbedding first))
              (centerFamily.tube
                (selectedCenterEmbedding second)) ≤
            1600 * caller.1 := by
      exact hnot
    change
      1600 * caller.1 <
        wz1PaperLineDistance
          (wz2PaperRelabelTube
            (wz2PaperCanonicalLineTube
              (fine.tube
                (representative
                  (net.centerEmbedding
                    (selectedCenterEmbedding first))))))
          (wz2PaperRelabelTube
            (wz2PaperCanonicalLineTube
              (fine.tube
                (representative
                  (net.centerEmbedding
                    (selectedCenterEmbedding second))))))
    have hdistance :
        wz1PaperLineDistance
            (centerFamily.tube
              (selectedCenterEmbedding first))
            (centerFamily.tube
              (selectedCenterEmbedding second)) =
          wz1PaperLineDistance
            (fine.tube
              (representative
                (net.centerEmbedding
                  (selectedCenterEmbedding first))))
            (fine.tube
              (representative
                (net.centerEmbedding
                  (selectedCenterEmbedding second)))) := by
      rw [wz2PaperRelabelTube_lineDistance_both,
        wz1PaperLineDistance_canonicalLineTube
          (fineLine
            (representative
              (net.centerEmbedding
                (selectedCenterEmbedding first))))
          (fineLine
            (representative
              (net.centerEmbedding
                (selectedCenterEmbedding second))))]
    rw [wz2PaperRelabelTube_lineDistance_both,
      wz1PaperLineDistance_canonicalLineTube
        (fineLine
          (representative
            (net.centerEmbedding
              (selectedCenterEmbedding first))))
        (fineLine
          (representative
            (net.centerEmbedding
              (selectedCenterEmbedding second))))]
    exact
      lt_of_not_ge (hdistance ▸ hnot')
  have callerParentCovers :
      ∀ source,
        WZ1PaperTubeCovers
          (selected.family.tube source)
          (callerCoarse.tube
            (callerParent source)) := by
    intro source
    let actualParent :=
      nearby.scaleData.cover.parent
        (selected.embedding source)
    let centerIndex := net.center actualParent
    let centerActual := net.centerEmbedding centerIndex
    have sourceActual :
        selected.embedding source ∈
          wz2PaperOrdinaryFullFiberIndices
            fine nearby.scaleData.coarse
            actualParent :=
      nearby.scaleData.cover.parent_mem_fullFiber
        (selected.embedding source)
    have sourceContainment :
        (fine.tube
          (selected.embedding source)).carrier ⊆
          (nearby.scaleData.coarse.tube
            actualParent).carrier :=
      (mem_wz2PaperOrdinaryFullFiberIndices_iff
        actualParent
        (selected.embedding source)).mp
        sourceActual
    have representativeContainment :
        (fine.tube
          (representative actualParent)).carrier ⊆
          (nearby.scaleData.coarse.tube
            actualParent).carrier :=
      (mem_wz2PaperOrdinaryFullFiberIndices_iff
        actualParent
        (representative actualParent)).mp
        (representativeMem actualParent)
    have withinActual :
        wz1PaperLineDistance
            (fine.tube (selected.embedding source))
            (fine.tube (representative actualParent)) ≤
          600000 * nearby.rho :=
      wz1PaperLineDistance_le_of_common_actual_parent
        nearby.scaleData.delta_pos deltaActual
        actualSmall
        (fineLine (selected.embedding source))
        (fineLine (representative actualParent))
        (fineBase (selected.embedding source))
        (fineBase (representative actualParent))
        sourceContainment representativeContainment
    have toCenter :
        wz1PaperLineDistance
            (fine.tube (representative actualParent))
            (fine.tube (representative centerActual)) ≤
          caller.1 / 4 := by
      exact net.center_close actualParent
    have toCallerRepresentative :
        wz1PaperLineDistance
            (fine.tube (selected.embedding source))
            (fine.tube (representative centerActual)) ≤
          caller.1 / 2 := by
      calc
        wz1PaperLineDistance
              (fine.tube (selected.embedding source))
              (fine.tube (representative centerActual))
            ≤
              wz1PaperLineDistance
                  (fine.tube (selected.embedding source))
                  (fine.tube (representative actualParent)) +
                wz1PaperLineDistance
                  (fine.tube (representative actualParent))
                  (fine.tube (representative centerActual)) :=
          wz1PaperLineDistance_triangle _ _ _
        _ ≤ 600000 * nearby.rho + caller.1 / 4 := by
          gcongr
        _ ≤ caller.1 / 2 := by
          nlinarith [actualCaller]
    unfold WZ1PaperTubeCovers
    rw [selected.tube_eq]
    change
      wz1PaperLineDistance
          (fine.tube (selected.embedding source))
          (wz2PaperRelabelTube
            (wz2PaperCanonicalLineTube
              (fine.tube
                (representative
                  (net.centerEmbedding
                    (selectedCenterEmbedding
                      (callerParent source))))))) ≤
        caller.1 / 2
    rw [wz2PaperRelabelTube_lineDistance_right]
    have hcenter :
        net.centerEmbedding
            (selectedCenterEmbedding
              (callerParent source)) =
          centerActual := by
      dsimp only [centerActual, centerIndex,
        actualParent]
      rw [← centerCompatibility source]
    rw [hcenter]
    have hcanonical :
        wz1PaperLineDistance
            (fine.tube (selected.embedding source))
            (wz2PaperCanonicalLineTube
              (fine.tube
                (representative centerActual))) =
          wz1PaperLineDistance
            (fine.tube (selected.embedding source))
            (fine.tube
              (representative centerActual)) := by
      unfold wz1PaperLineDistance
      rw [wz2PaperCanonicalLineTube_axisZero
          (fineLine (representative centerActual)),
        wz2PaperCanonicalLineTube_paperDirection
          (fineLine (representative centerActual))]
    rw [hcanonical]
    exact toCallerRepresentative
  have callerParentSurjective :
      Function.Surjective callerParent := by
    intro callerIndex
    let centerIndex :=
      selectedCenterEmbedding callerIndex
    let actualParent :=
      net.centerEmbedding centerIndex
    let ambientSource :=
      representative actualParent
    have actualParentCenter :
        net.center actualParent = centerIndex := by
      exact net.center_fixed centerIndex
    have centerSelected :
        centerIndex ∈ selectedCenters :=
      Finset.orderEmbOfFin_mem
        selectedCenters rfl callerIndex
    have actualSelected :
        actualParent ∈ selectedActualParents := by
      exact
        Finset.mem_filter.mpr
          ⟨Finset.mem_univ actualParent,
            actualParentCenter.symm ▸ centerSelected⟩
    have ambientParent :
        nearby.scaleData.cover.parent ambientSource =
          actualParent :=
      (nearby.scaleData.cover.mem_fullFiber_iff_parent_eq
        actualPos.le actualParent ambientSource).mp
        (representativeMem actualParent)
    have ambientSelected :
        ambientSource ∈ selectedFineIndices := by
      exact
        Finset.mem_filter.mpr
          ⟨Finset.mem_univ ambientSource,
            ambientParent.symm ▸ actualSelected⟩
    rcases
        selectedAmbientSurjective
          ambientSource ambientSelected
      with
      ⟨source, hsource⟩
    refine ⟨source, ?_⟩
    apply selectedCenterEmbedding.injective
    rw [← centerCompatibility source,
      hsource, ambientParent, actualParentCenter]
  let callerCover :
      WZ1PaperTubeCover
        selected.family callerCoarse :=
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
            (callerCoarse.tube
              (callerParent source))
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
          linarith
        exact
          (not_le_of_gt hseparated)
            (hupper.trans (by
              nlinarith [callerPos]))
    }
  let section6Cover :
      PureWZ2Section6Cover
        selected.family callerCoarse :=
    {
      fine_line_class :=
        fineLine.subfamily selected
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
  have selectedFineMass :
      selectedShading.mass =
        ∑ actual ∈ selectedActualParents,
          actualWeight actual := by
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
            (fun source =>
              volume (shading.carrier source)))
    have fiberwise :
        ∑ actual ∈ selectedActualParents,
            ∑ source ∈ selectedFineIndices with
                nearby.scaleData.cover.parent source =
                  actual,
              volume (shading.carrier source) =
          ∑ source ∈ selectedFineIndices,
            volume (shading.carrier source) :=
      Finset.sum_fiberwise_of_maps_to
        (s := selectedFineIndices)
        (t := selectedActualParents)
        (g := nearby.scaleData.cover.parent)
        (fun source hsource =>
          (Finset.mem_filter.mp hsource).2)
        (fun source =>
          volume (shading.carrier source))
    have fiberTerm :
        ∀ actual ∈ selectedActualParents,
          (∑ source ∈ selectedFineIndices with
              nearby.scaleData.cover.parent source =
                actual,
            volume (shading.carrier source)) =
          actualWeight actual := by
      intro actual hactual
      have hindices :
          selectedFineIndices.filter
              (fun source =>
                nearby.scaleData.cover.parent source =
                  actual) =
            wz2PaperOrdinaryFullFiberIndices
              fine nearby.scaleData.coarse actual := by
        ext source
        rw [nearby.scaleData.cover
          |>.mem_fullFiber_iff_parent_eq actualPos.le]
        simp only [selectedFineIndices,
          Finset.mem_filter, Finset.mem_univ,
          true_and]
        constructor
        · exact fun h => h.2
        · intro hsource
          exact ⟨hsource ▸ hactual, hsource⟩
      rw [Finset.sum_filter, ← Finset.sum_filter,
        hindices]
      rfl
    rw [localMass, ← fiberwise]
    apply Finset.sum_congr rfl
    intro actual hactual
    exact fiberTerm actual hactual
  have selectedActualWeight :
      (∑ actual ∈ selectedActualParents,
          actualWeight actual) =
        ∑ center ∈ selectedCenters,
          centerWeight center := by
    symm
    have fiberwise :=
      Finset.sum_fiberwise_of_maps_to
        (s := selectedActualParents)
        (t := selectedCenters)
        (g := net.center)
        (fun actual hactual =>
          (Finset.mem_filter.mp hactual).2)
        actualWeight
    calc
      ∑ center ∈ selectedCenters,
          centerWeight center =
          ∑ center ∈ selectedCenters,
            ∑ actual ∈ selectedActualParents with
                net.center actual = center,
              actualWeight actual := by
        apply Finset.sum_congr rfl
        intro center hcenter
        unfold centerWeight
        apply Finset.sum_congr
        · ext actual
          simp only [Finset.mem_filter,
            Finset.mem_univ, true_and]
          constructor
          · intro hactual
            exact
              ⟨Finset.mem_filter.mpr
                  ⟨Finset.mem_univ actual,
                    hactual ▸ hcenter⟩,
                hactual⟩
          · exact fun hactual => hactual.2
        · intro _ _
          rfl
      _ = ∑ actual ∈ selectedActualParents,
          actualWeight actual := fiberwise
  have retainedMass :
      shading.mass ≤
        (pureWZ2ParentQuotientNetConflictDegree :
          ENNReal) * selectedShading.mass := by
    rw [← totalActualWeight,
      ← totalCenterWeight,
      selectedFineMass,
      selectedActualWeight]
    exact retainedCenterWeight
  have completeActualFiberUnion :
      ∀ parent : Fin callerCoarse.card,
        Finset.image selected.embedding
            (wz2PaperFullFiberIndices
              selected.family callerCoarse parent) =
          Finset.biUnion
            (Finset.univ.filter fun actual =>
              net.center actual =
                selectedCenterEmbedding parent)
            (wz2PaperOrdinaryFullFiberIndices
              fine nearby.scaleData.coarse) := by
    intro parent
    ext ambientSource
    simp only [Finset.mem_image]
    constructor
    · rintro ⟨source, hsource, rfl⟩
      have callerParentEq :
          callerCover.parent source = parent :=
        (callerCover.parent_unique source parent
          ((mem_wz2PaperFullFiberIndices_iff
            parent source).mp hsource)).symm
      change callerParent source = parent
        at callerParentEq
      let actual :=
        nearby.scaleData.cover.parent
          (selected.embedding source)
      have actualCenter :
          net.center actual =
            selectedCenterEmbedding parent := by
        calc
          net.center actual =
              selectedCenterEmbedding
                (callerParent source) :=
            centerCompatibility source
          _ = selectedCenterEmbedding parent := by
            rw [callerParentEq]
      have actualMem :
          actual ∈
            Finset.univ.filter fun current =>
              net.center current =
                selectedCenterEmbedding parent :=
        Finset.mem_filter.mpr
          ⟨Finset.mem_univ actual, actualCenter⟩
      have sourceMem :
          selected.embedding source ∈
            wz2PaperOrdinaryFullFiberIndices
              fine nearby.scaleData.coarse actual :=
        nearby.scaleData.cover.parent_mem_fullFiber
          (selected.embedding source)
      exact
        Finset.mem_biUnion.mpr
          ⟨actual, actualMem, sourceMem⟩
    · intro hsource
      rcases Finset.mem_biUnion.mp hsource with
        ⟨actual, actualMem, sourceActual⟩
      have actualCenter :
          net.center actual =
            selectedCenterEmbedding parent :=
        (Finset.mem_filter.mp actualMem).2
      have ambientParent :
          nearby.scaleData.cover.parent ambientSource =
            actual :=
        (nearby.scaleData.cover
          |>.mem_fullFiber_iff_parent_eq
            actualPos.le actual ambientSource).mp
          sourceActual
      have actualSelected :
          actual ∈ selectedActualParents := by
        have centerSelected :
            selectedCenterEmbedding parent ∈
              selectedCenters :=
          Finset.orderEmbOfFin_mem
            selectedCenters rfl parent
        exact
          Finset.mem_filter.mpr
            ⟨Finset.mem_univ actual,
              actualCenter.symm ▸ centerSelected⟩
      have ambientSelected :
          ambientSource ∈ selectedFineIndices :=
        Finset.mem_filter.mpr
          ⟨Finset.mem_univ ambientSource,
            ambientParent.symm ▸ actualSelected⟩
      rcases
          selectedAmbientSurjective
            ambientSource ambientSelected
        with
        ⟨source, hsourceEq⟩
      have callerParentEq :
          callerCover.parent source = parent := by
        change callerParent source = parent
        apply selectedCenterEmbedding.injective
        rw [← centerCompatibility source,
          hsourceEq, ambientParent, actualCenter]
      refine ⟨source, ?_, hsourceEq⟩
      apply
        (mem_wz2PaperFullFiberIndices_iff
          parent source).mpr
      rw [← callerParentEq]
      exact callerCover.parent_covers source
  exact
    ⟨{
      representative := representative
      representative_mem := representativeMem
      net := net
      selectedCenters := selectedCenters
      selectedCenters_nonempty :=
        selectedCentersNonempty
      selectedCenterEmbedding :=
        selectedCenterEmbedding
      selectedCenterEmbedding_eq := rfl
      selectedActualParents :=
        selectedActualParents
      selectedActualParents_eq := rfl
      selectedFineIndices := selectedFineIndices
      selectedFineIndices_eq := rfl
      selected := selected
      selected_eq := rfl
      selectedShading := selectedShading
      selectedShading_eq := rfl
      callerCoarse := callerCoarse
      callerCenter := selectedCenterEmbedding
      callerCenter_mem := fun parent =>
        Finset.orderEmbOfFin_mem
          selectedCenters rfl parent
      caller_tube_eq := fun _ => rfl
      caller_strongly_separated :=
        callerStronglySeparated
      caller_midpoint_norm_le_six := by
        intro parent
        rw [show
          callerCoarse.tube parent =
            wz2PaperRelabelTube
              (targetScale := caller.1)
              (wz2PaperCanonicalLineTube
                (fine.tube
                  (representative
                    (net.centerEmbedding
                      (selectedCenterEmbedding parent))))) by rfl]
        change
          ‖wz2PaperTubeMidpoint
            (wz2PaperCanonicalLineTube
              (fine.tube
                (representative
                  (net.centerEmbedding
                    (selectedCenterEmbedding parent)))))‖ ≤ 6
        have hmidpoint :
            wz2PaperTubeMidpoint
                (wz2PaperCanonicalLineTube
                  (fine.tube
                    (representative
                      (net.centerEmbedding
                        (selectedCenterEmbedding parent))))) =
              wz2PaperTubeMidpoint
                (fine.tube
                  (representative
                    (net.centerEmbedding
                      (selectedCenterEmbedding parent)))) := by
          unfold wz2PaperCanonicalLineTube
          split_ifs
          · rfl
          · simp [wz2PaperTubeMidpoint, reverseTube]
            module
        rw [hmidpoint]
        unfold wz2PaperTubeMidpoint
        have hdirectionHalf :
            ‖(1 / 2 : ℝ) •
                (fine.tube
                  (representative
                    (net.centerEmbedding
                      (selectedCenterEmbedding parent)))).direction‖ ≤
              1 / 2 := by
          rw [norm_smul, Real.norm_eq_abs,
            (fine.tube
              (representative
                (net.centerEmbedding
                  (selectedCenterEmbedding parent)))).direction_unit]
          norm_num
        calc
          ‖(fine.tube
                (representative
                  (net.centerEmbedding
                    (selectedCenterEmbedding parent)))).base +
              (1 / 2 : ℝ) •
                (fine.tube
                  (representative
                    (net.centerEmbedding
                      (selectedCenterEmbedding parent)))).direction‖ ≤
              ‖(fine.tube
                (representative
                  (net.centerEmbedding
                    (selectedCenterEmbedding parent)))).base‖ +
                ‖(1 / 2 : ℝ) •
                  (fine.tube
                    (representative
                      (net.centerEmbedding
                        (selectedCenterEmbedding parent)))).direction‖ :=
            norm_add_le _ _
          _ ≤ 5 + 1 / 2 := by
            apply add_le_add
            · exact
                fineBase
                  (representative
                    (net.centerEmbedding
                      (selectedCenterEmbedding parent)))
            · exact hdirectionHalf
          _ ≤ 6 := by norm_num
      callerCover := callerCover
      section6Cover := section6Cover
      ambient_fine_line_class := fineLine
      center_compatibility :=
        centerCompatibility
      complete_actual_fiber_union :=
        completeActualFiberUnion
      retained_mass := retainedMass
      actual_full_fiber_uniform :=
        nearby.scaleData.full_fiber_uniform
      actual_rescaledFiber := fun _ actual _ =>
        nearby.scaleData.rescaledFiber actual
    }⟩

end Kakeya.Assouad

end
