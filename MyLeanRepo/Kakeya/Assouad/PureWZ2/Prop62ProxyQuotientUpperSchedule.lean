import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62GlobalUpperEnvelopeParentSelection
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ProxyQuotientUpperUniformity
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ProxyQuotientUpperCWA
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ProxyQuotientMetricFiberUniformity
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ProxyQuotientUpperRounding
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62UpperSchedule

/-!
# Proposition 6.2 quotient upper schedule

This module packages one upper quotient-envelope level and then a finite
upper schedule.  Every level uses the same supplied strong center coloring:
the `UpperScaleInput.ColoringData` is obtained by deterministic restriction,
never by a second coloring choice.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- Change only the selected-set index of a cleanup receipt. -/
def pureWZ2Prop62CleanupReceiptCast
    {Leaf Node : Type}
    [Fintype Leaf] [DecidableEq Leaf]
    [Fintype Node] [DecidableEq Node]
    {depth : ℕ}
    {tree : PureWZ2Prop62FiniteTree Leaf Node depth}
    {firstSelected secondSelected : Finset Leaf}
    (selected_eq : firstSelected = secondSelected)
    (receipt :
      PureWZ2Prop62CleanupReceipt tree firstSelected) :
    PureWZ2Prop62CleanupReceipt tree secondSelected :=
  selected_eq ▸ receipt

@[simp]
theorem pureWZ2Prop62CleanupReceiptCast_core
    {Leaf Node : Type}
    [Fintype Leaf] [DecidableEq Leaf]
    [Fintype Node] [DecidableEq Node]
    {depth : ℕ}
    {tree : PureWZ2Prop62FiniteTree Leaf Node depth}
    {firstSelected secondSelected : Finset Leaf}
    (selected_eq : firstSelected = secondSelected)
    (receipt :
      PureWZ2Prop62CleanupReceipt tree firstSelected) :
    (pureWZ2Prop62CleanupReceiptCast selected_eq receipt).core =
      receipt.core := by
  subst secondSelected
  rfl

namespace PureWZ2Prop62ProxySelectedMeshCells

/--
The proxy mesh is ordinarily essentially distinct once its common residue
class separates distinct occupied cells by more than the doubled-carrier
threshold.
-/
theorem coarse_ordinary_essentially_distinct
    {delta scale proxyScale rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    {oldData : WZ2PaperPureScaleCoverData fine scale C}
    {proxyTube : Fin oldData.coarse.card → Kakeya.DeltaTube proxyScale}
    {width : ℝ}
    (mesh :
      PureWZ2Prop62ProxySelectedMeshCells
        (rho := rho) oldData proxyTube width)
    (proxyLine :
      ∀ parent, WZ1PaperTubeInLineClass (proxyTube parent))
    (widthPos : 0 < width)
    (stride : ℕ)
    (sameColor :
      ∀ first second,
        first ∈ mesh.selectedParents →
        second ∈ mesh.selectedParents →
        pureWZ2Prop62LineColor width stride
            (proxyTube first) =
          pureWZ2Prop62LineColor width stride
            (proxyTube second))
    (strongSeparation :
      360 * rho < ((stride : ℝ) - 1) * width) :
    WZ2PaperOrdinaryIsEssentiallyDistinct mesh.coarse := by
  intro first second distinct
  let firstCell := (mesh.cellEquiv first).1
  let secondCell := (mesh.cellEquiv second).1
  have firstCellMem : firstCell ∈ mesh.occupiedCells :=
    (mesh.cellEquiv first).2
  have secondCellMem : secondCell ∈ mesh.occupiedCells :=
    (mesh.cellEquiv second).2
  have firstRepresentative :=
    mesh.representative_mem firstCell firstCellMem
  have secondRepresentative :=
    mesh.representative_mem secondCell secondCellMem
  have cellNe : firstCell ≠ secondCell := by
    intro equality
    apply distinct
    apply mesh.cellEquiv.injective
    exact Subtype.ext equality
  have colorEq :=
    sameColor
      (mesh.representative firstCell)
      (mesh.representative secondCell)
      firstRepresentative.1 secondRepresentative.1
  have representativeSeparated :=
    pureWZ2_prop62_sameLineColor_distinctCell_separated
      widthPos
      (proxyTube (mesh.representative firstCell))
      (proxyTube (mesh.representative secondCell))
      (proxyLine _) (proxyLine _) colorEq <| by
        rw [firstRepresentative.2, secondRepresentative.2]
        exact cellNe
  have metricSeparated :
      60 * rho <
        wz1PaperLineDistance
          (mesh.coarse.tube first)
          (mesh.coarse.tube second) := by
    change
      60 * rho <
        wz1PaperLineDistance
          (wz2PaperCenteredLineTube
            (targetScale := rho)
            (proxyTube (mesh.representative firstCell)))
          (wz2PaperCenteredLineTube
            (targetScale := rho)
            (proxyTube (mesh.representative secondCell)))
    rw [wz1PaperLineDistance_centeredLineTube_both
      (proxyLine _) (proxyLine _)]
    linarith
  constructor
  · intro containment
    have close :=
      wz2_paper_bounded_centered_doubled_containment_lineDistance_le
        mesh.rho_pos mesh.rho_pos
        (mesh.coarse_line_class proxyLine first)
        (mesh.coarse_line_class proxyLine second)
        1
        (wz2PaperCenteredLineTube_midpoint_norm_le_one
          (proxyLine
            (mesh.representative (mesh.cellEquiv first))))
        containment
    norm_num at close
    linarith
  · intro containment
    have close :=
      wz2_paper_bounded_centered_doubled_containment_lineDistance_le
        mesh.rho_pos mesh.rho_pos
        (mesh.coarse_line_class proxyLine second)
        (mesh.coarse_line_class proxyLine first)
        1
        (wz2PaperCenteredLineTube_midpoint_norm_le_one
          (proxyLine
            (mesh.representative (mesh.cellEquiv second))))
        containment
    have symmetry :=
      wz1PaperLineDistance_symm
        (mesh.coarse.tube second) (mesh.coarse.tube first)
    norm_num at close
    rw [symmetry] at close
    linarith

end PureWZ2Prop62ProxySelectedMeshCells

namespace PureWZ2Prop62GlobalUpperEnvelopeParentSelectionData

variable
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow}
    {fineNonempty : fine.Nonempty}
    {quotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        schedule fineNonempty}
    {width : ℝ}
    {packetCoordinate : Fin schedule.levelCount}
    {strideBase : ℕ}
    {weight : Fin fine.card → ENNReal}
    {metric :
      PureWZ2Prop62ProxyAncestryMetricOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight}
    {coloring :
      PureWZ2Prop62UpperEnvelopeCenterColoringData
        (quotient := quotient) rho packetCoordinate}
    {baseSelectedParents :
      Finset (Fin metric.metricParents.card)}
    {completeFiber :
      Fin metric.metricParents.card → Finset (Fin fine.card)}
    {parentWeight :
      Fin metric.metricParents.card → ENNReal}
    (global :
      PureWZ2Prop62GlobalUpperEnvelopeParentSelectionData
        schedule fineNonempty quotient width packetCoordinate
        strideBase weight metric coloring baseSelectedParents
        completeFiber parentWeight)

theorem selectedChild_monochromatic
    (fineLine : WZ1PaperIsLineClass fine)
    (fineBase : ∀ source, ‖(fine.tube source).base‖ ≤ 5)
    (rhoPos : 0 < rho)
    (selectedChildren :
      WZ2PaperPureTubeSubfamily metric.metricParents)
    (selectedChildren_subset :
      ∀ child,
        selectedChildren.embedding child ∈ global.selectedParents)
    (selectedParentsMonochromatic :
      ∀ parent ∈ global.selectedParents,
        ∀ coordinate :
            schedule.ProxyUpperCoordinate rho packetCoordinate,
          coloring.metricParentColor metric coordinate parent =
            global.selectedColor coordinate)
    (coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate)
    (child : Fin selectedChildren.family.card) :
    (metric.upperEnvelopeScaleInput
      fineLine fineBase rhoPos coordinate).childColor
        (coloring.toUpperEnvelopeColoring
          metric fineLine fineBase rhoPos coordinate)
        (selectedChildren.embedding child) =
      global.selectedColor coordinate := by
  simpa only [
    PureWZ2Prop62UpperEnvelopeCenterColoringData.toUpperEnvelopeColoring_childColor
  ] using
    selectedParentsMonochromatic
      (selectedChildren.embedding child)
      (selectedChildren_subset child)
      coordinate

noncomputable def selectedUpperCover
    (fineLine : WZ1PaperIsLineClass fine)
    (fineBase : ∀ source, ‖(fine.tube source).base‖ ≤ 5)
    (rhoPos : 0 < rho)
    (selectedChildren :
      WZ2PaperPureTubeSubfamily metric.metricParents)
    (selectedChildren_subset :
      ∀ child,
        selectedChildren.embedding child ∈ global.selectedParents)
    (selectedParentsMonochromatic :
      ∀ parent ∈ global.selectedParents,
        ∀ coordinate :
            schedule.ProxyUpperCoordinate rho packetCoordinate,
          coloring.metricParentColor metric coordinate parent =
            global.selectedColor coordinate)
    (coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate) :
    (metric.upperEnvelopeScaleInput
      fineLine fineBase rhoPos coordinate).MonochromaticCoverData
        (coloring.toUpperEnvelopeColoring
          metric fineLine fineBase rhoPos coordinate)
        selectedChildren :=
  Classical.choice <|
    PureWZ2Prop62UpperScaleInput.ColoringData.monochromatic_cover
      (metric.upperEnvelopeScaleInput
        fineLine fineBase rhoPos coordinate)
      (coloring.toUpperEnvelopeColoring
        metric fineLine fineBase rhoPos coordinate)
      selectedChildren (global.selectedColor coordinate)
      (global.selectedChild_monochromatic
        fineLine fineBase rhoPos selectedChildren
        selectedChildren_subset selectedParentsMonochromatic
        coordinate)

theorem selectedUpperCover_parent_owner_eq
    (fineLine : WZ1PaperIsLineClass fine)
    (fineBase : ∀ source, ‖(fine.tube source).base‖ ≤ 5)
    (rhoPos : 0 < rho)
    (selectedChildren :
      WZ2PaperPureTubeSubfamily metric.metricParents)
    (selectedChildren_subset :
      ∀ child,
        selectedChildren.embedding child ∈ global.selectedParents)
    (selectedParentsMonochromatic :
      ∀ parent ∈ global.selectedParents,
        ∀ coordinate :
            schedule.ProxyUpperCoordinate rho packetCoordinate,
          coloring.metricParentColor metric coordinate parent =
            global.selectedColor coordinate)
    (coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate)
    (child : Fin selectedChildren.family.card) :
    (global.selectedUpperCover
        fineLine fineBase rhoPos selectedChildren
        selectedChildren_subset selectedParentsMonochromatic
        coordinate).selectedParents.embedding
        ((global.selectedUpperCover
          fineLine fineBase rhoPos selectedChildren
          selectedChildren_subset selectedParentsMonochromatic
          coordinate).cover.parent child) =
      metric.upperEnvelopeOwner coordinate
        (selectedChildren.embedding child) :=
  (global.selectedUpperCover
    fineLine fineBase rhoPos selectedChildren
    selectedChildren_subset selectedParentsMonochromatic
    coordinate).parent_owner_eq child

/--
Terminal one-scale witness assembled from the same strong center coloring.
Uniformity and fiber CWA are supplied by the dedicated preceding modules.
-/
structure PureWZ2Prop62ProxyQuotientUpperScaleWitness
    (fineLine : WZ1PaperIsLineClass fine)
    (fineBase : ∀ source, ‖(fine.tube source).base‖ ≤ 5)
    (rhoPos : 0 < rho)
    (selectedChildren :
      WZ2PaperPureTubeSubfamily metric.metricParents)
    (selectedChildren_subset :
      ∀ child,
        selectedChildren.embedding child ∈ global.selectedParents)
    (selectedParentsMonochromatic :
      ∀ parent ∈ global.selectedParents,
        ∀ coordinate :
            schedule.ProxyUpperCoordinate rho packetCoordinate,
          coloring.metricParentColor metric coordinate parent =
            global.selectedColor coordinate)
    (coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate)
    (outputConstant : ENNReal) where
  coverConstant : ENNReal
  bodyConstant : ENNReal
  fullFiberUniform :
    WZ2PaperPureFullFibersAreCUniform
      selectedChildren.family
      (global.selectedUpperCover
        fineLine fineBase rhoPos selectedChildren
        selectedChildren_subset selectedParentsMonochromatic
        coordinate).selectedParents.family
      coverConstant
  normalization :
    ∀ parent : Fin
        (global.selectedUpperCover
          fineLine fineBase rhoPos selectedChildren
          selectedChildren_subset selectedParentsMonochromatic
          coordinate).selectedParents.family.card,
      WZ2PaperAssouadUnitRescalingData
        ((global.selectedUpperCover
          fineLine fineBase rhoPos selectedChildren
          selectedChildren_subset selectedParentsMonochromatic
          coordinate).selectedParents.family.tube parent)
  fiberCWA :
    ∀ parent : Fin
        (global.selectedUpperCover
          fineLine fineBase rhoPos selectedChildren
          selectedChildren_subset selectedParentsMonochromatic
          coordinate).selectedParents.family.card,
      WZ2PaperBodyConvexWolffBound
        (wz2PaperPureUnitRescaledFullFiberBodyFamily
          (fine := selectedChildren.family)
          (coarse :=
            (global.selectedUpperCover
              fineLine fineBase rhoPos selectedChildren
              selectedChildren_subset selectedParentsMonochromatic
              coordinate).selectedParents.family)
          parent (normalization parent))
        bodyConstant
  constant_le :
    max coverConstant bodyConstant ≤ outputConstant

end PureWZ2Prop62GlobalUpperEnvelopeParentSelectionData

namespace PureWZ2Prop62GlobalUpperEnvelopeParentSelectionData.PureWZ2Prop62ProxyQuotientUpperScaleWitness

variable
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow}
    {fineNonempty : fine.Nonempty}
    {quotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        schedule fineNonempty}
    {width : ℝ}
    {packetCoordinate : Fin schedule.levelCount}
    {strideBase : ℕ}
    {weight : Fin fine.card → ENNReal}
    {metric :
      PureWZ2Prop62ProxyAncestryMetricOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight}
    {coloring :
      PureWZ2Prop62UpperEnvelopeCenterColoringData
        (quotient := quotient) rho packetCoordinate}
    {baseSelectedParents :
      Finset (Fin metric.metricParents.card)}
    {completeFiber :
      Fin metric.metricParents.card → Finset (Fin fine.card)}
    {parentWeight :
      Fin metric.metricParents.card → ENNReal}
    {global :
      PureWZ2Prop62GlobalUpperEnvelopeParentSelectionData
        schedule fineNonempty quotient width packetCoordinate
        strideBase weight metric coloring baseSelectedParents
        completeFiber parentWeight}
    {fineLine : WZ1PaperIsLineClass fine}
    {fineBase : ∀ source, ‖(fine.tube source).base‖ ≤ 5}
    {rhoPos : 0 < rho}
    {selectedChildren :
      WZ2PaperPureTubeSubfamily metric.metricParents}
    {selectedChildren_subset :
      ∀ child,
        selectedChildren.embedding child ∈ global.selectedParents}
    {selectedParentsMonochromatic :
      ∀ parent ∈ global.selectedParents,
        ∀ coordinate :
            schedule.ProxyUpperCoordinate rho packetCoordinate,
          coloring.metricParentColor metric coordinate parent =
            global.selectedColor coordinate}
    {coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate}
    {outputConstant : ENNReal}
    (witness :
      PureWZ2Prop62ProxyQuotientUpperScaleWitness
        global fineLine fineBase rhoPos selectedChildren
        selectedChildren_subset selectedParentsMonochromatic
        coordinate outputConstant)

/-- The exact derived `UpperScaleInput.ColoringData` used by this witness. -/
def derivedColoring :
    (metric.upperEnvelopeScaleInput
      fineLine fineBase rhoPos coordinate).ColoringData :=
  coloring.toUpperEnvelopeColoring
    metric fineLine fineBase rhoPos coordinate

/-- The monochromatic cover generated from that exact derived coloring. -/
noncomputable def exactCoverData :=
  global.selectedUpperCover
    fineLine fineBase rhoPos selectedChildren
    selectedChildren_subset selectedParentsMonochromatic coordinate

/-- The closed pure Definition 2.12 witness at this one upper scale. -/
noncomputable def scaleData :
    WZ2PaperPureScaleCoverData
      selectedChildren.family
      (pureWZ2Prop62UpperEnvelopeFactor *
        schedule.actualScale coordinate.1)
      outputConstant := by
  let selectedCover :=
    global.selectedUpperCover
      fineLine fineBase rhoPos selectedChildren
      selectedChildren_subset selectedParentsMonochromatic coordinate
  exact
  (selectedCover.toPureScaleData
    witness.coverConstant witness.bodyConstant
    witness.fullFiberUniform witness.normalization
    witness.fiberCWA).mono witness.constant_le

end PureWZ2Prop62GlobalUpperEnvelopeParentSelectionData.PureWZ2Prop62ProxyQuotientUpperScaleWitness

/--
A finite schedule record without the unnecessary upper bound
`baseScale ≤ 1`.  Only the actual output scales and the nearby-scale rounding
inequalities used by Definition 2.12 are retained.
-/
structure PureWZ2Prop62ProxyQuotientUpperScheduleData
    {rho : ℝ}
    (parents : Kakeya.Streamlined.TubeFamily rho)
    (outputConstant : ENNReal) where
  output_finite : WZ2PaperFiniteErrorConstant outputConstant
  parent_distinct : WZ2PaperOrdinaryIsEssentiallyDistinct parents
  coordinateCount : ℕ
  coordinateCount_pos : 0 < coordinateCount
  actualScale : Fin coordinateCount → ℝ
  scaleData :
    ∀ coordinate,
      WZ2PaperPureScaleCoverData
        parents (actualScale coordinate) outputConstant
  rounding :
    ∀ requested : WZ2PaperRequestedScale rho,
      ∃ coordinate : Fin coordinateCount,
        requested.1 ≤ actualScale coordinate ∧
          ENNReal.ofReal (actualScale coordinate) <
            outputConstant * ENNReal.ofReal requested.1

/--
Assemble a thin quotient upper schedule directly from terminal one-scale
witnesses.  Unlike the legacy schedule record, this theorem does not assume
that any chosen actual scale is at most one.
-/
noncomputable def pureWZ2Prop62ProxyQuotientUpperSchedule
    {rho : ℝ}
    {parents : Kakeya.Streamlined.TubeFamily rho}
    {outputConstant : ENNReal}
    (outputFinite : WZ2PaperFiniteErrorConstant outputConstant)
    (parentDistinct :
      WZ2PaperOrdinaryIsEssentiallyDistinct parents)
    (coordinateCount : ℕ)
    (coordinateCountPos : 0 < coordinateCount)
    (actualScale : Fin coordinateCount → ℝ)
    (scaleData :
      ∀ coordinate,
        WZ2PaperPureScaleCoverData
          parents (actualScale coordinate) outputConstant)
    (rounding :
      ∀ requested : WZ2PaperRequestedScale rho,
        ∃ coordinate : Fin coordinateCount,
          requested.1 ≤ actualScale coordinate ∧
            ENNReal.ofReal (actualScale coordinate) <
              outputConstant * ENNReal.ofReal requested.1) :
    PureWZ2Prop62ProxyQuotientUpperScheduleData
      parents outputConstant where
  output_finite := outputFinite
  parent_distinct := parentDistinct
  coordinateCount := coordinateCount
  coordinateCount_pos := coordinateCountPos
  actualScale := actualScale
  scaleData := scaleData
  rounding := rounding

theorem pureWZ2_prop62_proxyQuotientUpperSchedule_publicPureCWA
    {rho : ℝ}
    {parents : Kakeya.Streamlined.TubeFamily rho}
    {outputConstant : ENNReal}
    (upperSchedule :
      PureWZ2Prop62ProxyQuotientUpperScheduleData
        parents outputConstant) :
    WZ2PaperPureCWAAtNearbyScales parents outputConstant := by
  apply
    pureWZ2_nearby_from_finite_witnesses
      (upperSchedule.scaleData
        ⟨0, upperSchedule.coordinateCount_pos⟩).delta_pos
      upperSchedule.output_finite.1
      upperSchedule.output_finite.2
      upperSchedule.parent_distinct
      upperSchedule.coordinateCount
      upperSchedule.coordinateCount_pos
      (fun coordinate =>
        ⟨upperSchedule.actualScale coordinate,
          upperSchedule.scaleData coordinate⟩)
  exact upperSchedule.rounding

namespace PureWZ2Prop62ProxyQuotientMetricCoreOutput

variable
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant scaleWindow : ENNReal}
    {schedule :
      PureWZ2Prop62LaminarPureSchedule
        fine ambientConstant scaleWindow}
    {fineNonempty : fine.Nonempty}
    {quotient :
      PureWZ2Prop62ProxyQuotientScheduleData
        schedule fineNonempty}
    {width : ℝ}
    {packetCoordinate : Fin schedule.levelCount}
    {strideBase : ℕ}
    {weight : Fin fine.card → ENNReal}
    (output :
      PureWZ2Prop62ProxyQuotientMetricCoreOutput
        (rho := rho) schedule fineNonempty quotient width
          packetCoordinate strideBase weight)
    {SourceColor : Type*}
    [Fintype SourceColor] [DecidableEq SourceColor]
    [Nonempty SourceColor]
    {coloring :
      PureWZ2Prop62UpperEnvelopeCenterColoringData
        (quotient := quotient) rho packetCoordinate}
    {sourceColor : Fin fine.card → SourceColor}
    (adapter :
      PureWZ2Prop62ProxyQuotientPreCoreAdapterData
        schedule fineNonempty quotient width packetCoordinate
        strideBase weight output.metric coloring SourceColor sourceColor)

/-- The final metric parents as a pure subfamily of the ambient metric family. -/
def finalMetricParentsSubfamily :
    WZ2PaperPureTubeSubfamily output.metric.metricParents where
  family := output.restriction.coarseSelected.family
  embedding := output.restriction.coarseSelected.embedding
  tube_eq := output.restriction.coarseSelected.tube_eq

/--
The final metric parents inherit ordinary essential distinctness from the
strongly separated proxy mesh used to construct the Section 6 parents.
-/
theorem finalMetricParents_ordinary_distinct
    (fineLine : WZ1PaperIsLineClass fine)
    (widthPos : 0 < width)
    (strongSeparation :
      360 * rho <
        (((strideBase + 1 : ℕ) : ℝ) - 1) * width) :
    WZ2PaperOrdinaryIsEssentiallyDistinct
      output.restriction.coarseSelected.family := by
  have sameColor :
      ∀ first second,
        first ∈ output.metric.mesh.selectedParents →
        second ∈ output.metric.mesh.selectedParents →
        pureWZ2Prop62LineColor width (strideBase + 1)
            (schedule.coordinateProxyTube
              fineNonempty packetCoordinate first) =
          pureWZ2Prop62LineColor width (strideBase + 1)
            (schedule.coordinateProxyTube
              fineNonempty packetCoordinate second) := by
    intro first second firstMem secondMem
    rw [output.metric.mesh_selectedParents_eq,
      output.metric.selectedParents_eq] at firstMem secondMem
    rcases Finset.mem_image.mp firstMem with
      ⟨firstSource, firstSourceMem, firstEq⟩
    rcases Finset.mem_image.mp secondMem with
      ⟨secondSource, secondSourceMem, secondEq⟩
    have firstResidue :=
      output.metric.selection.selected_residue
        firstSource firstSourceMem
    have secondResidue :=
      output.metric.selection.selected_residue
        secondSource secondSourceMem
    simpa only [firstEq, secondEq] using
      firstResidue.trans secondResidue.symm
  have metricDistinct :
      WZ2PaperOrdinaryIsEssentiallyDistinct
        output.metric.metricParents := by
    change
      WZ2PaperOrdinaryIsEssentiallyDistinct
        output.metric.metricInput.coarse
    rw [output.metric.metric_coarse_eq]
    exact
      output.metric.mesh.coarse_ordinary_essentially_distinct
        (schedule.coordinateProxyTube_lineClass
          fineNonempty fineLine packetCoordinate)
        widthPos (strideBase + 1) sameColor strongSeparation
  exact metricDistinct.subfamily output.finalMetricParentsSubfamily

/-- Every final metric parent belongs to the globally selected color class. -/
theorem finalMetricParent_mem_global
    (preliminary_eq :
      output.cleanup.preliminary = adapter.preCore.preliminary)
    (parent :
      Fin output.restriction.coarseSelected.family.card) :
    output.finalMetricParentsSubfamily.embedding parent ∈
      adapter.global.selectedParents :=
  adapter.preCore.fiberBin.selectedParents_subset <|
    output.finalMetricParent_mem_DMinusClass
      (adapter := adapter)
      (preliminary_eq := preliminary_eq)
      parent

/--
The ambient indices of the final metric parents are exactly the metric
parents still represented by the unique cleanup core.
-/
theorem finalMetricParents_image_univ_eq_surviving :
    Finset.image output.restriction.coarseSelected.embedding Finset.univ =
      pureWZ2Prop62SurvivingMetricParents
        output.cleanup.core.core
        output.metric.ambientMetricParentOf := by
  ext ambientParent
  constructor
  · intro parentImage
    rcases Finset.mem_image.mp parentImage with
      ⟨parent, _parentMem, rfl⟩
    rcases output.restriction.section6Cover.parent_hit parent with
      ⟨source, sourceCovered⟩
    let selectedSource :=
      output.restriction.fineSelected.embedding source
    let anchor :=
      output.metric.mesh.complete.selectedFine.embedding selectedSource
    have selectedSourcePulledBack :
        selectedSource ∈ output.pulledBack := by
      have selectedSourceImage :
          selectedSource ∈
            Finset.image output.restriction.fineSelected.embedding
              Finset.univ :=
        Finset.mem_image.mpr
          ⟨source, Finset.mem_univ source, rfl⟩
      rwa [output.restriction.fine_image_univ] at selectedSourceImage
    have anchorCore : anchor ∈ output.cleanup.core.core := by
      have anchorAmbientCore : anchor ∈ output.ambientCore := by
        rw [← output.image_eq]
        exact Finset.mem_image.mpr
          ⟨selectedSource, selectedSourcePulledBack, rfl⟩
      rwa [output.ambientCore_eq] at anchorAmbientCore
    apply
      mem_pureWZ2Prop62SurvivingMetricParents.mpr
    refine ⟨anchor, anchorCore, ?_⟩
    have covered :
        WZ1PaperTubeCovers
          (output.metric.selectedFine.tube selectedSource)
          (output.metric.metricParents.tube
            (output.restriction.coarseSelected.embedding parent)) := by
      simpa only [selectedSource,
        output.restriction.fineSelected.tube_eq,
        output.restriction.coarseSelected.tube_eq] using
          sourceCovered
    change
      output.metric.ambientMetricParentOf
          (output.metric.mesh.complete.selectedFine.embedding
            selectedSource) =
        output.restriction.coarseSelected.embedding parent
    rw [output.metric.ambientMetricParentOf_embedding]
    exact
      (output.metric.section6Cover.toWZ1PaperTubeCover
        |>.parent_unique selectedSource
          (output.restriction.coarseSelected.embedding parent)
          covered).symm
  · intro parentSurvives
    rcases
        mem_pureWZ2Prop62SurvivingMetricParents.mp parentSurvives
      with ⟨anchor, anchorCore, rfl⟩
    have anchorAmbientCore : anchor ∈ output.ambientCore := by
      rwa [output.ambientCore_eq]
    have anchorImage :
        anchor ∈
          Finset.image
            output.metric.mesh.complete.selectedFine.embedding
            output.pulledBack := by
      rwa [output.image_eq]
    rcases Finset.mem_image.mp anchorImage with
      ⟨selectedSource, selectedSourcePulledBack, anchorEq⟩
    have selectedSourceImage :
        selectedSource ∈
          Finset.image output.restriction.fineSelected.embedding
            Finset.univ := by
      rw [output.restriction.fine_image_univ]
      exact selectedSourcePulledBack
    rcases Finset.mem_image.mp selectedSourceImage with
      ⟨source, _sourceMem, selectedSourceEq⟩
    let parent := output.restriction.lineCover.parent source
    refine Finset.mem_image.mpr
      ⟨parent, Finset.mem_univ parent, ?_⟩
    have sourceCovered :
        WZ1PaperTubeCovers
          (output.metric.selectedFine.tube selectedSource)
          (output.metric.metricParents.tube
            (output.restriction.coarseSelected.embedding parent)) := by
      simpa only [selectedSourceEq,
        output.restriction.fineSelected.tube_eq,
        output.restriction.coarseSelected.tube_eq, parent] using
          output.restriction.lineCover.parent_covers source
    have parentEq :
        output.metric.metricParentOf selectedSource =
          output.restriction.coarseSelected.embedding parent :=
      (output.metric.section6Cover.toWZ1PaperTubeCover
        |>.parent_unique selectedSource
          (output.restriction.coarseSelected.embedding parent)
          sourceCovered).symm
    rw [← anchorEq,
      output.metric.ambientMetricParentOf_embedding, parentEq]

/-- The pre-core whole leaves form exact complete ambient metric fibers. -/
theorem wholeMetricFiber_eq_ambientCompleteMetricFiber
    (parent : Fin output.metric.metricParents.card)
    (parentMem :
      parent ∈
        Finset.image output.metric.ambientMetricParentOf
          adapter.preCore.wholeLeaves) :
    pureWZ2Prop62WholeMetricFiber
        adapter.preCore.wholeLeaves
        output.metric.ambientMetricParentOf parent =
      output.metric.ambientCompleteMetricFiber parent := by
  ext leaf
  constructor
  · intro leafMem
    have leafData :=
      mem_pureWZ2Prop62WholeMetricFiber.mp leafMem
    have leafWhole : leaf ∈ adapter.preCore.wholeLeaves :=
      leafData.1
    rw [adapter.preCore.wholeLeaves_eq] at leafWhole
    rcases Finset.mem_biUnion.mp leafWhole with
      ⟨fiberParent, fiberParentMem, leafFiber⟩
    have leafHull :=
      (output.metric.mem_ambientCompleteMetricFiber_iff
        fiberParent leaf).mp leafFiber |>.1
    exact
      (output.metric.mem_ambientCompleteMetricFiber_iff
        parent leaf).mpr ⟨leafHull, leafData.2⟩
  · intro leafFiber
    rcases Finset.mem_image.mp parentMem with
      ⟨witness, witnessWhole, witnessParent⟩
    have parentSelected :
        parent ∈ adapter.preCore.fiberBin.selectedParents := by
      have witnessSelected :=
        adapter.preCore.wholeLeaf_parent_selected
          witness witnessWhole
      rwa [witnessParent] at witnessSelected
    apply mem_pureWZ2Prop62WholeMetricFiber.mpr
    constructor
    · exact
        adapter.preCore.complete_metric_fibers
          parent parentSelected leafFiber
    · exact
        (output.metric.mem_ambientCompleteMetricFiber_iff
          parent leaf).mp leafFiber |>.2

/-- The pre-core whole metric fibers inherit the selected `DMinus` band. -/
theorem wholeMetricFiber_band :
    ∀ parent ∈
        Finset.image output.metric.ambientMetricParentOf
          adapter.preCore.wholeLeaves,
      adapter.preCore.fiberBin.DMinus ≤
          (pureWZ2Prop62WholeMetricFiber
            adapter.preCore.wholeLeaves
            output.metric.ambientMetricParentOf parent).card ∧
        (pureWZ2Prop62WholeMetricFiber
          adapter.preCore.wholeLeaves
          output.metric.ambientMetricParentOf parent).card <
            2 * adapter.preCore.fiberBin.DMinus := by
  intro parent parentMem
  have parentSelected :
      parent ∈ adapter.preCore.fiberBin.selectedParents := by
    rcases Finset.mem_image.mp parentMem with
      ⟨leaf, leafWhole, rfl⟩
    apply adapter.preCore.wholeLeaf_parent_selected
    exact leafWhole
  have band := adapter.preCore.DMinus_band parent parentSelected
  rw [output.wholeMetricFiber_eq_ambientCompleteMetricFiber
    (adapter := adapter) parent parentMem]
  exact band

/-- On the pre-core whole leaves, quotient leaf centers equal metric-parent centers. -/
theorem wholeLeafCenter_eq_upperQuotientCenter
    (fineLine : WZ1PaperIsLineClass fine)
    (fineBase : ∀ source, ‖(fine.tube source).base‖ ≤ 5)
    (rhoPos : 0 < rho)
    (widthPos : 0 < width)
    (packetScaleLeRho :
      schedule.actualScale packetCoordinate ≤ rho)
    (sixWidthLe : 6 * width ≤ rho / 2)
    (leaf : Fin fine.card)
    (leafMem : leaf ∈ adapter.preCore.wholeLeaves)
    (coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate) :
    quotient.leafCenter coordinate.1 leaf =
      output.metric.upperQuotientCenter coordinate
        (output.metric.ambientMetricParentOf leaf) := by
  have leafWhole : leaf ∈ adapter.preCore.wholeLeaves :=
    leafMem
  rw [adapter.preCore.wholeLeaves_eq] at leafWhole
  rcases Finset.mem_biUnion.mp leafWhole with
    ⟨parent, _parentMem, leafFiber⟩
  have leafHull :=
    (output.metric.mem_ambientCompleteMetricFiber_iff
      parent leaf).mp leafFiber |>.1
  rcases
      output.metric.mesh.complete.selectedFine_ambient_surjective
        leaf leafHull
    with ⟨source, sourceEq⟩
  have sourceParent :
      output.metric.section6Cover.toWZ1PaperTubeCover.parent source =
        output.metric.ambientMetricParentOf leaf := by
    change output.metric.metricParentOf source =
      output.metric.ambientMetricParentOf leaf
    rw [← output.metric.ambientMetricParentOf_embedding source,
      sourceEq]
  simpa only [sourceEq] using
    output.metric.upperQuotientCenter_source
      fineLine fineBase rhoPos widthPos packetScaleLeRho sixWidthLe
      coordinate
      (parent := output.metric.ambientMetricParentOf leaf)
      (source := source)
      sourceParent

/--
Canonical one-scale upper cover on the final metric-parent family.  Its
coloring is the deterministic restriction of the one supplied strong center
coloring.
-/
noncomputable def finalUpperCover
    (preliminary_eq :
      output.cleanup.preliminary = adapter.preCore.preliminary)
    (fineLine : WZ1PaperIsLineClass fine)
    (fineBase : ∀ source, ‖(fine.tube source).base‖ ≤ 5)
    (rhoPos : 0 < rho)
    (coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate) :=
  adapter.global.selectedUpperCover
    (fineLine := fineLine)
    (fineBase := fineBase)
    (rhoPos := rhoPos)
    (selectedChildren := output.finalMetricParentsSubfamily)
    (selectedChildren_subset :=
      output.finalMetricParent_mem_global
        (adapter := adapter)
        (preliminary_eq := preliminary_eq))
    (selectedParentsMonochromatic := adapter.global.monochromatic)
    coordinate

/--
Every strict fiber of the exact final upper cover is an injective reindexing
of an upper strict fiber of the surviving ambient metric parents.
-/
theorem finalUpperCover_fullFiber_image_eq_upperStrictFiber
    (preliminary_eq :
      output.cleanup.preliminary = adapter.preCore.preliminary)
    (fineLine : WZ1PaperIsLineClass fine)
    (fineBase : ∀ source, ‖(fine.tube source).base‖ ≤ 5)
    (rhoPos : 0 < rho)
    (coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate)
    (parent : Fin
      (output.finalUpperCover
        (adapter := adapter) (preliminary_eq := preliminary_eq)
        fineLine fineBase rhoPos coordinate).selectedParents.family.card) :
    ∃ anchor ∈ output.cleanup.core.core,
      (output.metric.upperEnvelopeScaleInput
        fineLine fineBase rhoPos coordinate).owner
          (output.metric.ambientMetricParentOf anchor) =
          (output.finalUpperCover
            (adapter := adapter) (preliminary_eq := preliminary_eq)
            fineLine fineBase rhoPos coordinate).selectedParents.embedding
            parent ∧
        Finset.image output.restriction.coarseSelected.embedding
            (wz2PaperOrdinaryFullFiberIndices
              output.restriction.coarseSelected.family
              (output.finalUpperCover
                (adapter := adapter) (preliminary_eq := preliminary_eq)
                fineLine fineBase rhoPos coordinate).selectedParents.family
                parent) =
          pureWZ2Prop62UpperStrictFiberAt
            output.cleanup.core.core
            output.metric.ambientMetricParentOf
            (output.metric.upperQuotientCenter coordinate)
            anchor := by
  let coverData :=
    output.finalUpperCover
      (adapter := adapter) (preliminary_eq := preliminary_eq)
      fineLine fineBase rhoPos coordinate
  let fiber :=
    wz2PaperOrdinaryFullFiberIndices
      output.finalMetricParentsSubfamily.family
      coverData.selectedParents.family parent
  rcases coverData.full_fiber_nonempty parent with
    ⟨referenceChild, referenceChildMem⟩
  let referenceAmbientParent :=
    output.restriction.coarseSelected.embedding referenceChild
  have referenceSurvives :
      referenceAmbientParent ∈
        pureWZ2Prop62SurvivingMetricParents
          output.cleanup.core.core
          output.metric.ambientMetricParentOf := by
    rw [← output.finalMetricParents_image_univ_eq_surviving]
    exact Finset.mem_image.mpr
      ⟨referenceChild, Finset.mem_univ referenceChild, rfl⟩
  rcases
      mem_pureWZ2Prop62SurvivingMetricParents.mp referenceSurvives
    with ⟨anchor, anchorMem, anchorParentEq⟩
  have referenceOwner :
      output.metric.upperEnvelopeOwner coordinate
          (output.restriction.coarseSelected.embedding
            referenceChild) =
        coverData.selectedParents.embedding parent := by
    have referenceFiltered :
        referenceChild ∈ Finset.univ.filter fun current =>
          (output.metric.upperEnvelopeScaleInput
              fineLine fineBase rhoPos coordinate).owner
              (output.finalMetricParentsSubfamily.embedding current) =
            coverData.selectedParents.embedding parent := by
      rw [← coverData.fullFiberIndices_eq_owner parent]
      exact referenceChildMem
    exact (Finset.mem_filter.mp referenceFiltered).2
  have anchorOwner :
      (output.metric.upperEnvelopeScaleInput
        fineLine fineBase rhoPos coordinate).owner
          (output.metric.ambientMetricParentOf anchor) =
        coverData.selectedParents.embedding parent := by
    change
      output.metric.upperEnvelopeOwner coordinate
          (output.metric.ambientMetricParentOf anchor) =
        coverData.selectedParents.embedding parent
    rw [anchorParentEq]
    exact referenceOwner
  have fiberImage :
      Finset.image output.restriction.coarseSelected.embedding fiber =
        pureWZ2Prop62UpperStrictFiberAt
          output.cleanup.core.core
          output.metric.ambientMetricParentOf
          (output.metric.upperQuotientCenter coordinate)
          anchor := by
    ext ambientParent
    constructor
    · intro ambientParentMem
      rcases Finset.mem_image.mp ambientParentMem with
        ⟨child, childMem, rfl⟩
      apply Finset.mem_filter.mpr
      constructor
      · rw [← output.finalMetricParents_image_univ_eq_surviving]
        exact Finset.mem_image.mpr
          ⟨child, Finset.mem_univ child, rfl⟩
      · have childOwner :
            output.metric.upperEnvelopeOwner coordinate
                (output.restriction.coarseSelected.embedding child) =
              coverData.selectedParents.embedding parent := by
          have childFiltered :
              child ∈ Finset.univ.filter fun current =>
                (output.metric.upperEnvelopeScaleInput
                    fineLine fineBase rhoPos coordinate).owner
                    (output.finalMetricParentsSubfamily.embedding current) =
                  coverData.selectedParents.embedding parent := by
            rw [← coverData.fullFiberIndices_eq_owner parent]
            exact childMem
          exact (Finset.mem_filter.mp childFiltered).2
        calc
          output.metric.upperQuotientCenter coordinate
              (output.restriction.coarseSelected.embedding child) =
              (output.metric.upperCenters coordinate).embedding
                (output.metric.upperEnvelopeOwner coordinate
                  (output.restriction.coarseSelected.embedding child)) :=
            (output.metric.upperEnvelopeOwner_ambient
              coordinate
              (output.restriction.coarseSelected.embedding child)).symm
          _ =
              (output.metric.upperCenters coordinate).embedding
                (output.metric.upperEnvelopeOwner coordinate
                  (output.restriction.coarseSelected.embedding
                    referenceChild)) := by
            exact congrArg
              (output.metric.upperCenters coordinate).embedding
              (childOwner.trans referenceOwner.symm)
          _ =
              output.metric.upperQuotientCenter coordinate
                referenceAmbientParent :=
            output.metric.upperEnvelopeOwner_ambient coordinate
              referenceAmbientParent
          _ =
              output.metric.upperQuotientCenter coordinate
                (output.metric.ambientMetricParentOf anchor) :=
            congrArg
              (output.metric.upperQuotientCenter coordinate)
              anchorParentEq.symm
    · intro ambientParentMem
      have ambientData := Finset.mem_filter.mp ambientParentMem
      have ambientInFinal :
          ambientParent ∈
            Finset.image output.restriction.coarseSelected.embedding
              Finset.univ := by
        rw [output.finalMetricParents_image_univ_eq_surviving]
        exact ambientData.1
      rcases Finset.mem_image.mp ambientInFinal with
        ⟨child, _childMem, childEq⟩
      refine Finset.mem_image.mpr ⟨child, ?_, childEq⟩
      change
        child ∈
          wz2PaperOrdinaryFullFiberIndices
            output.finalMetricParentsSubfamily.family
            coverData.selectedParents.family parent
      rw [coverData.fullFiberIndices_eq_owner]
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ child, ?_⟩
      have centerEq :
          output.metric.upperQuotientCenter coordinate
              (output.restriction.coarseSelected.embedding child) =
            output.metric.upperQuotientCenter coordinate
              referenceAmbientParent := by
        rw [childEq, ← anchorParentEq]
        exact ambientData.2
      have ownerEq :
          output.metric.upperEnvelopeOwner coordinate
              (output.restriction.coarseSelected.embedding child) =
            output.metric.upperEnvelopeOwner coordinate
              referenceAmbientParent := by
        apply
          (output.metric.upperCenters coordinate).embedding.injective
        rw [output.metric.upperEnvelopeOwner_ambient,
          output.metric.upperEnvelopeOwner_ambient]
        exact centerEq
      exact ownerEq.trans referenceOwner
  exact ⟨anchor, anchorMem, anchorOwner, fiberImage⟩

/-- Cardinality form of the exact-cover/upper-strict-fiber reindexing. -/
theorem finalUpperCover_fullFiber_card_eq_upperStrictFiber
    (preliminary_eq :
      output.cleanup.preliminary = adapter.preCore.preliminary)
    (fineLine : WZ1PaperIsLineClass fine)
    (fineBase : ∀ source, ‖(fine.tube source).base‖ ≤ 5)
    (rhoPos : 0 < rho)
    (coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate)
    (parent : Fin
      (output.finalUpperCover
        (adapter := adapter) (preliminary_eq := preliminary_eq)
        fineLine fineBase rhoPos coordinate).selectedParents.family.card) :
    ∃ anchor ∈ output.cleanup.core.core,
      ((wz2PaperOrdinaryFullFiberIndices
        output.restriction.coarseSelected.family
        (output.finalUpperCover
          (adapter := adapter) (preliminary_eq := preliminary_eq)
          fineLine fineBase rhoPos coordinate).selectedParents.family
          parent).card : ENNReal) =
        ((pureWZ2Prop62UpperStrictFiberAt
          output.cleanup.core.core
          output.metric.ambientMetricParentOf
          (output.metric.upperQuotientCenter coordinate)
          anchor).card : ENNReal) := by
  rcases
      output.finalUpperCover_fullFiber_image_eq_upperStrictFiber
        (adapter := adapter) (preliminary_eq := preliminary_eq)
        fineLine fineBase rhoPos coordinate parent
    with ⟨anchor, anchorMem, _anchorOwner, fiberImage⟩
  refine ⟨anchor, anchorMem, ?_⟩
  have cardImage :=
    Finset.card_image_of_injective
      (wz2PaperOrdinaryFullFiberIndices
        output.restriction.coarseSelected.family
        (output.finalUpperCover
          (adapter := adapter) (preliminary_eq := preliminary_eq)
          fineLine fineBase rhoPos coordinate).selectedParents.family
          parent)
      output.restriction.coarseSelected.embedding.injective
  exact_mod_cast cardImage.symm.trans (congrArg Finset.card fiberImage)

/--
Concrete upper strict-fiber uniformity for the exact cover used by the final
schedule.  The proof invokes the quotient-prefix theorem on the unique cleanup
receipt and then reindexes its surviving ambient metric parents through
`finalUpperCover`.
-/
theorem finalUpperCover_fullFibers_uniform
    (preliminary_eq :
      output.cleanup.preliminary = adapter.preCore.preliminary)
    (fineLine : WZ1PaperIsLineClass fine)
    (fineBase : ∀ source, ‖(fine.tube source).base‖ ≤ 5)
    (rhoPos : 0 < rho)
    (widthPos : 0 < width)
    (packetScaleLeRho :
      schedule.actualScale packetCoordinate ≤ rho)
    (sixWidthLe : 6 * width ≤ rho / 2)
    (Bcopy Cold Λ : ENNReal)
    (centerCopyBound :
      ∀ coordinate :
          schedule.ProxyUpperCoordinate rho packetCoordinate,
        ∀ center,
          ((quotient.centerActualParents
            coordinate.1 center).card : ENNReal) ≤ Bcopy)
    (ambientUniform :
      ∀ coordinate :
          schedule.ProxyUpperCoordinate rho packetCoordinate,
        WZ2PaperPureFullFibersAreCUniform
          fine (schedule.scaleData coordinate.1).coarse Cold)
    (densityLoss_le : output.quotientDensityLoss ≤ Λ)
    (coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate) :
    WZ2PaperPureFullFibersAreCUniform
      output.restriction.coarseSelected.family
      (output.finalUpperCover
        (adapter := adapter) (preliminary_eq := preliminary_eq)
        fineLine fineBase rhoPos coordinate).selectedParents.family
      (2 * Bcopy * Cold * Λ) := by
  let selected_eq :
      output.cleanup.preliminary =
        adapter.preCore.leafBin.selected :=
    preliminary_eq.trans adapter.preCore.preliminary_eq
  let receipt :
      PureWZ2Prop62CleanupReceipt
        output.cleanup.auxiliary.tree
        adapter.preCore.leafBin.selected :=
    pureWZ2Prop62CleanupReceiptCast
      selected_eq output.cleanup.core
  have selectedParentsMonochromatic :
      ∀ parent ∈
          Finset.image output.metric.ambientMetricParentOf
            adapter.preCore.wholeLeaves,
        ∀ current :
            schedule.ProxyUpperCoordinate rho packetCoordinate,
          (output.metric.upperEnvelopeScaleInput
            fineLine fineBase rhoPos current).childColor
              (coloring.toUpperEnvelopeColoring
                output.metric fineLine fineBase rhoPos current)
              parent =
            adapter.global.selectedColor current := by
    intro parent parentMem current
    rcases Finset.mem_image.mp parentMem with
      ⟨leaf, leafWhole, rfl⟩
    have parentSelected :=
      adapter.preCore.wholeLeaf_parent_selected leaf leafWhole
    simpa only [
      PureWZ2Prop62UpperEnvelopeCenterColoringData.toUpperEnvelopeColoring_childColor
    ] using
      adapter.global.monochromatic
        (output.metric.ambientMetricParentOf leaf)
        (adapter.preCore.fiberBin.selectedParents_subset parentSelected)
        current
  have receiptDensity :
      ∀ current :
          schedule.ProxyUpperCoordinate rho packetCoordinate,
        ∀ anchor ∈ receipt.core,
          ((output.cleanup.auxiliary.prefixNodeAt
            (current.1.1 + 1) anchor).card : ENNReal) ≤
              Λ *
                ((receipt.core ∩
                  output.cleanup.auxiliary.prefixNodeAt
                    (current.1.1 + 1) anchor).card : ENNReal) := by
    intro current anchor anchorMem
    have anchorMemOriginal :
        anchor ∈ output.cleanup.core.core := by
      simpa only [receipt,
        pureWZ2Prop62CleanupReceiptCast_core] using anchorMem
    have treeFiber :=
      output.cleanup.auxiliary.tree_fiber_upperCoordinate_prefix_eq
        current anchor
    have coreTreeFiberNonempty :
        (output.cleanup.core.core ∩
          output.cleanup.auxiliary.tree.fiber
            (current.1.1 + 1)
            (output.cleanup.auxiliary.nodeAt
              (current.1.1 + 1) anchor)).Nonempty := by
      rw [treeFiber]
      refine ⟨anchor, Finset.mem_inter.mpr
        ⟨anchorMemOriginal, ?_⟩⟩
      simp only [
        PureWZ2Prop62ProxyQuotientAuxiliaryLevel.prefixNodeAt,
        Finset.mem_filter, Finset.mem_univ, true_and
      ]
      exact
        schedule.proxyUpperCenterPrefixEquivalent_refl
          fineNonempty quotient rho packetCoordinate _ anchor
    have raw :=
      pureWZ2_prop62_receipt_upper_prefix_density
        output.cleanup.auxiliary.tree
        output.cleanup.preliminary output.cleanup.core
        (current.1.1 + 1) (by omega)
        (output.cleanup.auxiliary.nodeAt
          (current.1.1 + 1) anchor)
        coreTreeFiberNonempty
    rw [treeFiber] at raw
    have exactDensity :
        ((output.cleanup.auxiliary.prefixNodeAt
          (current.1.1 + 1) anchor).card : ENNReal) ≤
            output.quotientDensityLoss *
              ((output.cleanup.core.core ∩
                output.cleanup.auxiliary.prefixNodeAt
                  (current.1.1 + 1) anchor).card : ENNReal) := by
      simpa only [
        PureWZ2Prop62ProxyQuotientMetricCoreOutput.quotientDensityLoss,
        Kakeya.Streamlined.TubeFamily.enncard,
        Fintype.card_fin, mul_assoc
      ] using raw
    calc
      ((output.cleanup.auxiliary.prefixNodeAt
          (current.1.1 + 1) anchor).card : ENNReal) ≤
          output.quotientDensityLoss *
            ((output.cleanup.core.core ∩
              output.cleanup.auxiliary.prefixNodeAt
                (current.1.1 + 1) anchor).card : ENNReal) :=
        exactDensity
      _ ≤
          Λ *
            ((output.cleanup.core.core ∩
              output.cleanup.auxiliary.prefixNodeAt
                (current.1.1 + 1) anchor).card : ENNReal) := by
        gcongr
      _ =
          Λ *
            ((receipt.core ∩
              output.cleanup.auxiliary.prefixNodeAt
                (current.1.1 + 1) anchor).card : ENNReal) := by
        rw [pureWZ2Prop62CleanupReceiptCast_core]
  intro first second
  rcases
      output.finalUpperCover_fullFiber_card_eq_upperStrictFiber
        (adapter := adapter) (preliminary_eq := preliminary_eq)
        fineLine fineBase rhoPos coordinate first
    with ⟨firstAnchor, firstAnchorMem, firstCard⟩
  rcases
      output.finalUpperCover_fullFiber_card_eq_upperStrictFiber
        (adapter := adapter) (preliminary_eq := preliminary_eq)
        fineLine fineBase rhoPos coordinate second
    with ⟨secondAnchor, secondAnchorMem, secondCard⟩
  have strictUniform :=
    pureWZ2_prop62_proxyQuotient_upperStrictFiber_uniform
      output.cleanup.auxiliary output.metric
      adapter.preCore.wholeLeaves
      output.metric.ambientMetricParentOf
      sourceColor
      (∑ parent ∈ adapter.preCore.fiberBin.selectedParents,
        output.metric.metricParentWeight parent)
      adapter.preCore.leafBin receipt coloring fineLine fineBase rhoPos
      adapter.global.selectedColor selectedParentsMonochromatic
      (output.wholeLeafCenter_eq_upperQuotientCenter
        (adapter := adapter) fineLine fineBase rhoPos widthPos
        packetScaleLeRho sixWidthLe)
      adapter.preCore.fiberBin.DMinus
      adapter.preCore.fiberBin.DMinus_pos
      (fun parent parentMem => by
        have band :=
          output.wholeMetricFiber_band
            (adapter := adapter) parent parentMem
        exact ⟨band.1, band.2.le⟩)
      Bcopy Cold Λ centerCopyBound ambientUniform receiptDensity
      coordinate firstAnchor secondAnchor
      (by
        simpa only [receipt,
          pureWZ2Prop62CleanupReceiptCast_core] using firstAnchorMem)
      (by
        simpa only [receipt,
          pureWZ2Prop62CleanupReceiptCast_core] using secondAnchorMem)
  rw [wz2PaperOrdinaryFullFiberCount,
    wz2PaperOrdinaryFullFiberCount, firstCard, secondCard]
  simpa only [receipt,
    pureWZ2Prop62CleanupReceiptCast_core] using strictUniform

/-- The one-density-loss constant produced by the upper body-CWA argument. -/
def finalUpperBodyConstant
    (Λ sourceConstant : ENNReal) : ENNReal :=
  (Λ * sourceConstant) *
    pureWZ2Prop62UpperEnvelopeGeometricLoss * 2

/-- Canonical John normalization for one parent of the exact upper cover. -/
noncomputable def finalUpperNormalization
    (preliminary_eq :
      output.cleanup.preliminary = adapter.preCore.preliminary)
    (fineLine : WZ1PaperIsLineClass fine)
    (fineBase : ∀ source, ‖(fine.tube source).base‖ ≤ 5)
    (rhoPos : 0 < rho)
    (coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate)
    (parent : Fin
      (output.finalUpperCover
        (adapter := adapter) (preliminary_eq := preliminary_eq)
        fineLine fineBase rhoPos coordinate).selectedParents.family.card) :
    WZ2PaperAssouadUnitRescalingData
      ((output.finalUpperCover
        (adapter := adapter) (preliminary_eq := preliminary_eq)
        fineLine fineBase rhoPos coordinate).selectedParents.family.tube
        parent) :=
  WZ2PaperAssouadUnitRescalingData.ofTube _
    (mul_pos
      (by norm_num [pureWZ2Prop62UpperEnvelopeFactor])
      (schedule.scaleData coordinate.1).rho_pos)

/--
Concrete upper body CWA for one parent of the exact final cover.

The active children, target-contained children, target cardinality, pre-core
fiber band, and core ownership are all reconstructed here.  The remaining
inputs are precisely the packetwise geometric containment and ambient
packet-sum estimate.  The output pays the cleanup density `Λ` once.
-/
theorem finalUpperFiber_bodyCWA
    (preliminary_eq :
      output.cleanup.preliminary = adapter.preCore.preliminary)
    (fineLine : WZ1PaperIsLineClass fine)
    (fineBase : ∀ source, ‖(fine.tube source).base‖ ≤ 5)
    (rhoPos : 0 < rho)
    (widthPos : 0 < width)
    (packetScaleLeRho :
      schedule.actualScale packetCoordinate ≤ rho)
    (sixWidthLe : 6 * width ≤ rho / 2)
    (Λ sourceConstant : ENNReal)
    (densityLoss_le : output.quotientDensityLoss ≤ Λ)
    (coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate)
    (parent : Fin
      (output.finalUpperCover
        (adapter := adapter) (preliminary_eq := preliminary_eq)
        fineLine fineBase rhoPos coordinate).selectedParents.family.card)
    (containedLeafSet :
      Fin fine.card → Set Point3 → Finset (Fin fine.card))
    (contained_packet :
      ∀ anchor ∈ output.cleanup.core.core,
        ∀ convexSet,
          ∀ child ∈
              pureWZ2Prop62UpperCoverContainedAmbientFiber
                output.finalMetricParentsSubfamily
                (output.finalUpperCover
                  (adapter := adapter)
                  (preliminary_eq := preliminary_eq)
                  fineLine fineBase rhoPos coordinate).selectedParents.family
                parent
                (output.finalUpperNormalization
                  (adapter := adapter)
                  (preliminary_eq := preliminary_eq)
                  fineLine fineBase rhoPos coordinate parent)
                convexSet,
            ((adapter.preCore.wholeLeaves ∩
              quotient.centerPacketIndices coordinate.1
                (quotient.leafCenter coordinate.1 anchor)).filter
              fun leaf =>
                output.metric.ambientMetricParentOf leaf = child) ⊆
              containedLeafSet anchor convexSet)
    (ambient_cwa :
      ∀ anchor ∈ output.cleanup.core.core,
        ∀ convexSet, Convex ℝ convexSet →
          ((containedLeafSet anchor convexSet).card : ENNReal) ≤
            sourceConstant *
              (pureWZ2Prop62UpperEnvelopeGeometricLoss *
                MeasureTheory.volume convexSet) *
              ((output.cleanup.auxiliary.prefixNodeAt
                (coordinate.1.1 + 1) anchor).card : ENNReal)) :
    WZ2PaperBodyConvexWolffBound
      (wz2PaperPureUnitRescaledFullFiberBodyFamily
        (fine := output.restriction.coarseSelected.family)
        (coarse :=
          (output.finalUpperCover
            (adapter := adapter) (preliminary_eq := preliminary_eq)
            fineLine fineBase rhoPos coordinate).selectedParents.family)
        parent
        (output.finalUpperNormalization
          (adapter := adapter) (preliminary_eq := preliminary_eq)
          fineLine fineBase rhoPos coordinate parent))
      (finalUpperBodyConstant Λ sourceConstant) := by
  let coverData :=
    output.finalUpperCover
      (adapter := adapter) (preliminary_eq := preliminary_eq)
      fineLine fineBase rhoPos coordinate
  let normalization :=
    output.finalUpperNormalization
      (adapter := adapter) (preliminary_eq := preliminary_eq)
      fineLine fineBase rhoPos coordinate parent
  rcases
      output.finalUpperCover_fullFiber_image_eq_upperStrictFiber
        (adapter := adapter) (preliminary_eq := preliminary_eq)
        fineLine fineBase rhoPos coordinate parent
    with ⟨anchor, anchorCore, anchorOwner, fiberImage⟩
  have preliminarySubsetWhole :
      output.cleanup.preliminary ⊆ adapter.preCore.wholeLeaves := by
    intro leaf leafMem
    apply adapter.preCore.preliminary_subset_whole_fibers
    rw [← preliminary_eq]
    exact leafMem
  have anchorWhole : anchor ∈ adapter.preCore.wholeLeaves :=
    preliminarySubsetWhole (output.cleanup.core.core_subset anchorCore)
  have wholeMonochromatic :
      ∀ leaf ∈ adapter.preCore.wholeLeaves,
        ∀ current :
            schedule.ProxyUpperCoordinate rho packetCoordinate,
          coloring.leafColor current leaf =
            adapter.global.selectedColor current := by
    intro leaf leafMem current
    apply adapter.leaf_monochromatic
    rwa [adapter.wholeLeaves_eq]
  have coreParentSelected :
      ∀ leaf ∈ output.cleanup.core.core,
        output.metric.ambientMetricParentOf leaf ∈
          Finset.image output.finalMetricParentsSubfamily.embedding
            Finset.univ := by
    intro leaf leafCore
    change
      output.metric.ambientMetricParentOf leaf ∈
        Finset.image output.restriction.coarseSelected.embedding
          Finset.univ
    rw [output.finalMetricParents_image_univ_eq_surviving]
    exact
      mem_pureWZ2Prop62SurvivingMetricParents.mpr
        ⟨leaf, leafCore, rfl⟩
  have activeFiberBand :
      ∀ child ∈
          pureWZ2Prop62UpperCoverAmbientFiber
            output.finalMetricParentsSubfamily
            coverData.selectedParents.family parent,
        adapter.preCore.fiberBin.DMinus ≤
            (adapter.preCore.wholeLeaves.filter fun leaf =>
              output.metric.ambientMetricParentOf leaf = child).card ∧
          (adapter.preCore.wholeLeaves.filter fun leaf =>
            output.metric.ambientMetricParentOf leaf = child).card <
              2 * adapter.preCore.fiberBin.DMinus := by
    intro child childMem
    have childStrict :
        child ∈
          pureWZ2Prop62UpperStrictFiberAt
            output.cleanup.core.core
            output.metric.ambientMetricParentOf
            (output.metric.upperQuotientCenter coordinate) anchor := by
      rw [← fiberImage]
      exact childMem
    have childData := Finset.mem_filter.mp childStrict
    have childWholeImage :
        child ∈
          Finset.image output.metric.ambientMetricParentOf
            adapter.preCore.wholeLeaves := by
      rcases
          mem_pureWZ2Prop62SurvivingMetricParents.mp childData.1
        with ⟨leaf, leafCore, rfl⟩
      exact Finset.mem_image.mpr
        ⟨leaf,
          preliminarySubsetWhole
            (output.cleanup.core.core_subset leafCore),
          rfl⟩
    have band :=
      output.wholeMetricFiber_band
        (adapter := adapter) child childWholeImage
    have fiberEq :
        (adapter.preCore.wholeLeaves.filter fun leaf =>
          output.metric.ambientMetricParentOf leaf = child) =
          pureWZ2Prop62WholeMetricFiber
            adapter.preCore.wholeLeaves
            output.metric.ambientMetricParentOf child := by
      ext leaf
      simp [pureWZ2Prop62WholeMetricFiber]
    rw [fiberEq]
    exact band
  have raw :=
    coloring.quotientUpperCover_parent_body_cwa
      (fineLine := fineLine)
      (fineBase := fineBase)
      (rhoPos := rhoPos)
      (wholeLeaves := adapter.preCore.wholeLeaves)
      (preliminary := output.cleanup.preliminary)
      (preliminary_subset_wholeLeaves := preliminarySubsetWhole)
      (selectedColor := adapter.global.selectedColor)
      (monochromatic := wholeMonochromatic)
      (auxiliary := output.cleanup.auxiliary)
      (receipt := output.cleanup.core)
      (output := output.metric)
      (selectedChildren := output.finalMetricParentsSubfamily)
      (coordinate := coordinate)
      (coverData := coverData)
      (parent := parent)
      (normalization := normalization)
      (anchor := anchor)
      (anchorMem := anchorCore)
      (anchor_owner := anchorOwner)
      (core_parent_selected := coreParentSelected)
      (leafCenter_eq_upperCenter :=
        fun leaf leafMem =>
          output.wholeLeafCenter_eq_upperQuotientCenter
            (adapter := adapter) fineLine fineBase rhoPos widthPos
            packetScaleLeRho sixWidthLe leaf leafMem coordinate)
      (DMinus := adapter.preCore.fiberBin.DMinus)
      (DMinus_pos := adapter.preCore.fiberBin.DMinus_pos)
      (wholeMetricFiber_band := activeFiberBand)
      (containedLeafSet := containedLeafSet anchor)
      (contained_packet := contained_packet anchor anchorCore)
      (sourceConstant := sourceConstant)
      (ambient_cwa := ambient_cwa anchor anchorCore)
  change
    WZ2PaperBodyConvexWolffBound
      (wz2PaperPureUnitRescaledFullFiberBodyFamily
        (fine := output.restriction.coarseSelected.family)
        (coarse := coverData.selectedParents.family)
        parent normalization)
      (finalUpperBodyConstant Λ sourceConstant)
  have constantBound :
      (PureWZ2Prop62UpperEnvelopeCenterColoringData.pureWZ2Prop62ReceiptDensityLoss
            (schedule.levelCount + 1) fine.card
              output.cleanup.preliminary.card *
          sourceConstant) *
          pureWZ2Prop62UpperEnvelopeGeometricLoss * 2 ≤
        finalUpperBodyConstant Λ sourceConstant := by
    dsimp only [finalUpperBodyConstant]
    gcongr
    simpa only [
      PureWZ2Prop62ProxyQuotientMetricCoreOutput.quotientDensityLoss,
      PureWZ2Prop62UpperEnvelopeCenterColoringData.pureWZ2Prop62ReceiptDensityLoss,
      Kakeya.Streamlined.TubeFamily.enncard,
      Fintype.card_fin
    ] using densityLoss_le
  intro convexSet convex
  exact (raw convexSet convex).trans <|
    mul_le_mul_right'
      (mul_le_mul_right' constantBound
        (MeasureTheory.volume convexSet))
      (wz2PaperPureUnitRescaledFullFiberBodyFamily
        (fine := output.restriction.coarseSelected.family)
        (coarse := coverData.selectedParents.family)
        parent normalization).enncard

/--
Construct the terminal pure scale witness from the already proved upper
strict-fiber uniformity and upper-fiber CWA statements.
-/
noncomputable def finalUpperScaleData_ofComponents
    (preliminary_eq :
      output.cleanup.preliminary = adapter.preCore.preliminary)
    (fineLine : WZ1PaperIsLineClass fine)
    (fineBase : ∀ source, ‖(fine.tube source).base‖ ≤ 5)
    (rhoPos : 0 < rho)
    (coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate)
    (coverConstant bodyConstant outputConstant : ENNReal)
    (fullFiberUniform :
      WZ2PaperPureFullFibersAreCUniform
        output.restriction.coarseSelected.family
        (output.finalUpperCover
          (adapter := adapter) (preliminary_eq := preliminary_eq)
          fineLine fineBase rhoPos coordinate).selectedParents.family
        coverConstant)
    (normalization :
      ∀ parent : Fin
          (output.finalUpperCover
            (adapter := adapter) (preliminary_eq := preliminary_eq)
            fineLine fineBase rhoPos coordinate).selectedParents.family.card,
        WZ2PaperAssouadUnitRescalingData
          ((output.finalUpperCover
            (adapter := adapter) (preliminary_eq := preliminary_eq)
            fineLine fineBase rhoPos coordinate).selectedParents.family.tube
            parent))
    (fiberCWA :
      ∀ parent : Fin
          (output.finalUpperCover
            (adapter := adapter) (preliminary_eq := preliminary_eq)
            fineLine fineBase rhoPos coordinate).selectedParents.family.card,
        WZ2PaperBodyConvexWolffBound
          (wz2PaperPureUnitRescaledFullFiberBodyFamily
            (fine := output.restriction.coarseSelected.family)
            (coarse :=
              (output.finalUpperCover
                (adapter := adapter) (preliminary_eq := preliminary_eq)
                fineLine fineBase rhoPos coordinate).selectedParents.family)
            parent (normalization parent))
          bodyConstant)
    (constant_le :
      max coverConstant bodyConstant ≤ outputConstant) :
    WZ2PaperPureScaleCoverData
      output.restriction.coarseSelected.family
      (pureWZ2Prop62UpperEnvelopeFactor *
        schedule.actualScale coordinate.1)
      outputConstant := by
  let witness :
      adapter.global.PureWZ2Prop62ProxyQuotientUpperScaleWitness
        fineLine fineBase rhoPos
        output.finalMetricParentsSubfamily
        (output.finalMetricParent_mem_global
          (adapter := adapter)
          (preliminary_eq := preliminary_eq))
        adapter.global.monochromatic coordinate outputConstant :=
    {
      coverConstant := coverConstant
      bodyConstant := bodyConstant
      fullFiberUniform := fullFiberUniform
      normalization := normalization
      fiberCWA := fiberCWA
      constant_le := constant_le
    }
  exact witness.scaleData

/-- Exact constant of the concrete quotient upper scale construction. -/
def finalUpperScaleConstant
    (Bcopy Cold Λ sourceConstant : ENNReal) : ENNReal :=
  max (2 * Bcopy * Cold * Λ)
    (finalUpperBodyConstant Λ sourceConstant)

/--
Concrete per-coordinate producer for the exact final upper cover.

The strict-fiber comparison and every rescaled-fiber CWA are proved
internally.  In particular, the cover constant is exactly
`2 * Bcopy * Cold * Λ`, while the body constant contains exactly the one
cleanup-density factor occurring in `finalUpperBodyConstant`.
-/
noncomputable def finalUpperScaleData
    (preliminary_eq :
      output.cleanup.preliminary = adapter.preCore.preliminary)
    (fineLine : WZ1PaperIsLineClass fine)
    (fineBase : ∀ source, ‖(fine.tube source).base‖ ≤ 5)
    (rhoPos : 0 < rho)
    (widthPos : 0 < width)
    (packetScaleLeRho :
      schedule.actualScale packetCoordinate ≤ rho)
    (sixWidthLe : 6 * width ≤ rho / 2)
    (Bcopy Cold Λ sourceConstant : ENNReal)
    (centerCopyBound :
      ∀ coordinate :
          schedule.ProxyUpperCoordinate rho packetCoordinate,
        ∀ center,
          ((quotient.centerActualParents
            coordinate.1 center).card : ENNReal) ≤ Bcopy)
    (ambientUniform :
      ∀ coordinate :
          schedule.ProxyUpperCoordinate rho packetCoordinate,
        WZ2PaperPureFullFibersAreCUniform
          fine (schedule.scaleData coordinate.1).coarse Cold)
    (densityLoss_le : output.quotientDensityLoss ≤ Λ)
    (coordinate :
      schedule.ProxyUpperCoordinate rho packetCoordinate)
    (containedLeafSet :
      Fin fine.card → Set Point3 → Finset (Fin fine.card))
    (contained_packet :
      ∀ parent : Fin
          (output.finalUpperCover
            (adapter := adapter) (preliminary_eq := preliminary_eq)
            fineLine fineBase rhoPos coordinate).selectedParents.family.card,
        ∀ anchor ∈ output.cleanup.core.core,
          ∀ convexSet,
            ∀ child ∈
                pureWZ2Prop62UpperCoverContainedAmbientFiber
                  output.finalMetricParentsSubfamily
                  (output.finalUpperCover
                    (adapter := adapter)
                    (preliminary_eq := preliminary_eq)
                    fineLine fineBase rhoPos coordinate).selectedParents.family
                  parent
                  (output.finalUpperNormalization
                    (adapter := adapter)
                    (preliminary_eq := preliminary_eq)
                    fineLine fineBase rhoPos coordinate parent)
                  convexSet,
              ((adapter.preCore.wholeLeaves ∩
                quotient.centerPacketIndices coordinate.1
                  (quotient.leafCenter coordinate.1 anchor)).filter
                fun leaf =>
                  output.metric.ambientMetricParentOf leaf = child) ⊆
                    containedLeafSet anchor convexSet)
    (ambient_cwa :
      ∀ parent : Fin
          (output.finalUpperCover
            (adapter := adapter) (preliminary_eq := preliminary_eq)
            fineLine fineBase rhoPos coordinate).selectedParents.family.card,
        ∀ anchor ∈ output.cleanup.core.core,
          ∀ convexSet, Convex ℝ convexSet →
            ((containedLeafSet anchor convexSet).card : ENNReal) ≤
              sourceConstant *
                (pureWZ2Prop62UpperEnvelopeGeometricLoss *
                  MeasureTheory.volume convexSet) *
                ((output.cleanup.auxiliary.prefixNodeAt
                  (coordinate.1.1 + 1) anchor).card : ENNReal)) :
    WZ2PaperPureScaleCoverData
      output.restriction.coarseSelected.family
      (pureWZ2Prop62UpperEnvelopeFactor *
        schedule.actualScale coordinate.1)
      (finalUpperScaleConstant Bcopy Cold Λ sourceConstant) := by
  exact
    output.finalUpperScaleData_ofComponents
      (adapter := adapter) (preliminary_eq := preliminary_eq)
      (fineLine := fineLine)
      (fineBase := fineBase)
      (rhoPos := rhoPos)
      (coordinate := coordinate)
      (coverConstant := 2 * Bcopy * Cold * Λ)
      (bodyConstant := finalUpperBodyConstant Λ sourceConstant)
      (outputConstant :=
        finalUpperScaleConstant Bcopy Cold Λ sourceConstant)
      (fullFiberUniform :=
      output.finalUpperCover_fullFibers_uniform
        (adapter := adapter) (preliminary_eq := preliminary_eq)
        fineLine fineBase rhoPos widthPos packetScaleLeRho sixWidthLe
        Bcopy Cold Λ centerCopyBound
        ambientUniform densityLoss_le coordinate)
      (normalization := fun parent =>
        output.finalUpperNormalization
        (adapter := adapter) (preliminary_eq := preliminary_eq)
        fineLine fineBase rhoPos coordinate parent)
      (fiberCWA := fun parent =>
        output.finalUpperFiber_bodyCWA
        (adapter := adapter) (preliminary_eq := preliminary_eq)
        fineLine fineBase rhoPos widthPos packetScaleLeRho sixWidthLe
        Λ sourceConstant densityLoss_le coordinate parent containedLeafSet
        (contained_packet parent) (ambient_cwa parent))
      (constant_le := le_rfl)

/--
Concrete finite upper schedule over the quotient upper-coordinate type.
There is no `actualScale ≤ 1` premise: only the requested-scale rounding
inequalities consumed by the public Definition 2.12 statement are required.
-/
noncomputable def finalUpperSchedule_ofComponents
    (preliminary_eq :
      output.cleanup.preliminary = adapter.preCore.preliminary)
    (fineLine : WZ1PaperIsLineClass fine)
    (fineBase : ∀ source, ‖(fine.tube source).base‖ ≤ 5)
    (rhoPos : 0 < rho)
    (outputConstant : ENNReal)
    (outputFinite : WZ2PaperFiniteErrorConstant outputConstant)
    (parentDistinct :
      WZ2PaperOrdinaryIsEssentiallyDistinct
        output.restriction.coarseSelected.family)
    (upperNonempty :
      Nonempty
        (schedule.ProxyUpperCoordinate rho packetCoordinate))
    (coverConstant bodyConstant :
      schedule.ProxyUpperCoordinate rho packetCoordinate → ENNReal)
    (fullFiberUniform :
      ∀ coordinate,
        WZ2PaperPureFullFibersAreCUniform
          output.restriction.coarseSelected.family
          (output.finalUpperCover
            (adapter := adapter) (preliminary_eq := preliminary_eq)
            fineLine fineBase rhoPos coordinate).selectedParents.family
          (coverConstant coordinate))
    (normalization :
      ∀ coordinate,
        ∀ parent : Fin
            (output.finalUpperCover
              (adapter := adapter) (preliminary_eq := preliminary_eq)
              fineLine fineBase rhoPos coordinate).selectedParents.family.card,
          WZ2PaperAssouadUnitRescalingData
            ((output.finalUpperCover
              (adapter := adapter) (preliminary_eq := preliminary_eq)
              fineLine fineBase rhoPos coordinate).selectedParents.family.tube
              parent))
    (fiberCWA :
      ∀ coordinate,
        ∀ parent : Fin
            (output.finalUpperCover
              (adapter := adapter) (preliminary_eq := preliminary_eq)
              fineLine fineBase rhoPos coordinate).selectedParents.family.card,
          WZ2PaperBodyConvexWolffBound
            (wz2PaperPureUnitRescaledFullFiberBodyFamily
              (fine := output.restriction.coarseSelected.family)
              (coarse :=
                (output.finalUpperCover
                  (adapter := adapter) (preliminary_eq := preliminary_eq)
                  fineLine fineBase rhoPos coordinate).selectedParents.family)
              parent (normalization coordinate parent))
            (bodyConstant coordinate))
    (constant_le :
      ∀ coordinate,
        max (coverConstant coordinate) (bodyConstant coordinate) ≤
          outputConstant)
    (rounding :
      ∀ requested : WZ2PaperRequestedScale rho,
        ∃ coordinate :
            schedule.ProxyUpperCoordinate rho packetCoordinate,
          requested.1 ≤
              pureWZ2Prop62UpperEnvelopeFactor *
                schedule.actualScale coordinate.1 ∧
            ENNReal.ofReal
                (pureWZ2Prop62UpperEnvelopeFactor *
                  schedule.actualScale coordinate.1) <
              outputConstant * ENNReal.ofReal requested.1) :
    PureWZ2Prop62ProxyQuotientUpperScheduleData
      output.restriction.coarseSelected.family outputConstant := by
  let Upper :=
    schedule.ProxyUpperCoordinate rho packetCoordinate
  let upperEquiv : Fin (Fintype.card Upper) ≃ Upper :=
    (Fintype.equivFin Upper).symm
  let actualScale : Fin (Fintype.card Upper) → ℝ :=
    fun index =>
      pureWZ2Prop62UpperEnvelopeFactor *
        schedule.actualScale (upperEquiv index).1
  let scaleData :
      ∀ index : Fin (Fintype.card Upper),
        WZ2PaperPureScaleCoverData
          output.restriction.coarseSelected.family
          (actualScale index) outputConstant :=
    fun index =>
      output.finalUpperScaleData_ofComponents
        (adapter := adapter) (preliminary_eq := preliminary_eq)
        fineLine fineBase rhoPos (upperEquiv index)
        (coverConstant (upperEquiv index))
        (bodyConstant (upperEquiv index))
        outputConstant
        (fullFiberUniform (upperEquiv index))
        (normalization (upperEquiv index))
        (fiberCWA (upperEquiv index))
        (constant_le (upperEquiv index))
  refine
    pureWZ2Prop62ProxyQuotientUpperSchedule
      outputFinite parentDistinct
      (Fintype.card Upper)
      (Fintype.card_pos_iff.mpr upperNonempty)
      actualScale scaleData ?_
  intro requested
  rcases rounding requested with
    ⟨coordinate, requestedLe, window⟩
  let index := upperEquiv.symm coordinate
  refine ⟨index, ?_, ?_⟩
  · simpa [actualScale, index] using requestedLe
  · simpa [actualScale, index] using window

theorem finalMetricParents_publicPureCWA_ofComponents
    (preliminary_eq :
      output.cleanup.preliminary = adapter.preCore.preliminary)
    (fineLine : WZ1PaperIsLineClass fine)
    (fineBase : ∀ source, ‖(fine.tube source).base‖ ≤ 5)
    (rhoPos : 0 < rho)
    (outputConstant : ENNReal)
    (outputFinite : WZ2PaperFiniteErrorConstant outputConstant)
    (parentDistinct :
      WZ2PaperOrdinaryIsEssentiallyDistinct
        output.restriction.coarseSelected.family)
    (upperNonempty :
      Nonempty
        (schedule.ProxyUpperCoordinate rho packetCoordinate))
    (coverConstant bodyConstant :
      schedule.ProxyUpperCoordinate rho packetCoordinate → ENNReal)
    (fullFiberUniform :
      ∀ coordinate,
        WZ2PaperPureFullFibersAreCUniform
          output.restriction.coarseSelected.family
          (output.finalUpperCover
            (adapter := adapter) (preliminary_eq := preliminary_eq)
            fineLine fineBase rhoPos coordinate).selectedParents.family
          (coverConstant coordinate))
    (normalization :
      ∀ coordinate,
        ∀ parent : Fin
            (output.finalUpperCover
              (adapter := adapter) (preliminary_eq := preliminary_eq)
              fineLine fineBase rhoPos coordinate).selectedParents.family.card,
          WZ2PaperAssouadUnitRescalingData
            ((output.finalUpperCover
              (adapter := adapter) (preliminary_eq := preliminary_eq)
              fineLine fineBase rhoPos coordinate).selectedParents.family.tube
              parent))
    (fiberCWA :
      ∀ coordinate,
        ∀ parent : Fin
            (output.finalUpperCover
              (adapter := adapter) (preliminary_eq := preliminary_eq)
              fineLine fineBase rhoPos coordinate).selectedParents.family.card,
          WZ2PaperBodyConvexWolffBound
            (wz2PaperPureUnitRescaledFullFiberBodyFamily
              (fine := output.restriction.coarseSelected.family)
              (coarse :=
                (output.finalUpperCover
                  (adapter := adapter) (preliminary_eq := preliminary_eq)
                  fineLine fineBase rhoPos coordinate).selectedParents.family)
              parent (normalization coordinate parent))
            (bodyConstant coordinate))
    (constant_le :
      ∀ coordinate,
        max (coverConstant coordinate) (bodyConstant coordinate) ≤
          outputConstant)
    (rounding :
      ∀ requested : WZ2PaperRequestedScale rho,
        ∃ coordinate :
            schedule.ProxyUpperCoordinate rho packetCoordinate,
          requested.1 ≤
              pureWZ2Prop62UpperEnvelopeFactor *
                schedule.actualScale coordinate.1 ∧
            ENNReal.ofReal
                (pureWZ2Prop62UpperEnvelopeFactor *
                  schedule.actualScale coordinate.1) <
              outputConstant * ENNReal.ofReal requested.1) :
    WZ2PaperPureCWAAtNearbyScales
      output.restriction.coarseSelected.family outputConstant :=
  pureWZ2_prop62_proxyQuotientUpperSchedule_publicPureCWA <|
    output.finalUpperSchedule_ofComponents
      (adapter := adapter) (preliminary_eq := preliminary_eq)
      fineLine fineBase rhoPos outputConstant outputFinite
      parentDistinct upperNonempty
      coverConstant bodyConstant fullFiberUniform normalization
      fiberCWA constant_le rounding

/--
Concrete finite upper schedule.  Each coordinate is produced from the same
strong coloring, the quotient-prefix uniformity theorem, and the dual-set
upper body-CWA theorem.
-/
noncomputable def finalUpperSchedule
    (preliminary_eq :
      output.cleanup.preliminary = adapter.preCore.preliminary)
    (fineLine : WZ1PaperIsLineClass fine)
    (fineBase : ∀ source, ‖(fine.tube source).base‖ ≤ 5)
    (rhoPos : 0 < rho)
    (widthPos : 0 < width)
    (packetScaleLtRho :
      schedule.actualScale packetCoordinate < rho)
    (rhoLeOne : rho ≤ 1)
    (sixWidthLe : 6 * width ≤ rho / 2)
    (strongSeparation :
      360 * rho <
        (((strideBase + 1 : ℕ) : ℝ) - 1) * width)
    (Bcopy Cold Λ sourceConstant : ENNReal)
    (centerCopyBound :
      ∀ coordinate :
          schedule.ProxyUpperCoordinate rho packetCoordinate,
        ∀ center,
          ((quotient.centerActualParents
            coordinate.1 center).card : ENNReal) ≤ Bcopy)
    (ambientUniform :
      ∀ coordinate :
          schedule.ProxyUpperCoordinate rho packetCoordinate,
        WZ2PaperPureFullFibersAreCUniform
          fine (schedule.scaleData coordinate.1).coarse Cold)
    (densityLoss_le : output.quotientDensityLoss ≤ Λ)
    (outputFinite :
      WZ2PaperFiniteErrorConstant
        (finalUpperScaleConstant Bcopy Cold Λ sourceConstant))
    (envelope_absorption :
      (pureWZ2Prop62UpperEnvelopeFactor : ENNReal) * scaleWindow ≤
        finalUpperScaleConstant Bcopy Cold Λ sourceConstant)
    (containedLeafSet :
      schedule.ProxyUpperCoordinate rho packetCoordinate →
        Fin fine.card → Set Point3 → Finset (Fin fine.card))
    (contained_packet :
      ∀ coordinate :
          schedule.ProxyUpperCoordinate rho packetCoordinate,
        ∀ parent : Fin
            (output.finalUpperCover
              (adapter := adapter) (preliminary_eq := preliminary_eq)
              fineLine fineBase rhoPos coordinate).selectedParents.family.card,
          ∀ anchor ∈ output.cleanup.core.core,
            ∀ convexSet,
              ∀ child ∈
                  pureWZ2Prop62UpperCoverContainedAmbientFiber
                    output.finalMetricParentsSubfamily
                    (output.finalUpperCover
                      (adapter := adapter)
                      (preliminary_eq := preliminary_eq)
                      fineLine fineBase rhoPos coordinate).selectedParents.family
                    parent
                    (output.finalUpperNormalization
                      (adapter := adapter)
                      (preliminary_eq := preliminary_eq)
                      fineLine fineBase rhoPos coordinate parent)
                    convexSet,
                ((adapter.preCore.wholeLeaves ∩
                  quotient.centerPacketIndices coordinate.1
                    (quotient.leafCenter coordinate.1 anchor)).filter
                  fun leaf =>
                    output.metric.ambientMetricParentOf leaf = child) ⊆
                      containedLeafSet coordinate anchor convexSet)
    (ambient_cwa :
      ∀ coordinate :
          schedule.ProxyUpperCoordinate rho packetCoordinate,
        ∀ parent : Fin
            (output.finalUpperCover
              (adapter := adapter) (preliminary_eq := preliminary_eq)
              fineLine fineBase rhoPos coordinate).selectedParents.family.card,
          ∀ anchor ∈ output.cleanup.core.core,
            ∀ convexSet, Convex ℝ convexSet →
              ((containedLeafSet
                coordinate anchor convexSet).card : ENNReal) ≤
                sourceConstant *
                  (pureWZ2Prop62UpperEnvelopeGeometricLoss *
                    MeasureTheory.volume convexSet) *
                  ((output.cleanup.auxiliary.prefixNodeAt
                    (coordinate.1.1 + 1) anchor).card : ENNReal))
    :
    PureWZ2Prop62ProxyQuotientUpperScheduleData
      output.restriction.coarseSelected.family
      (finalUpperScaleConstant Bcopy Cold Λ sourceConstant) := by
  have packetScaleLeRho :
      schedule.actualScale packetCoordinate ≤ rho :=
    packetScaleLtRho.le
  have upperNonempty :
      Nonempty
        (schedule.ProxyUpperCoordinate rho packetCoordinate) :=
    schedule.proxyUpperCoordinate_nonempty
      packetCoordinate packetScaleLtRho rhoLeOne
  have rounding :
      ∀ requested : WZ2PaperRequestedScale rho,
        ∃ coordinate :
            schedule.ProxyUpperCoordinate rho packetCoordinate,
          requested.1 ≤
              pureWZ2Prop62UpperEnvelopeFactor *
                schedule.actualScale coordinate.1 ∧
            ENNReal.ofReal
                (pureWZ2Prop62UpperEnvelopeFactor *
                  schedule.actualScale coordinate.1) <
              finalUpperScaleConstant Bcopy Cold Λ sourceConstant *
                ENNReal.ofReal requested.1 :=
    schedule.proxyUpperEnvelope_rounding
      packetCoordinate packetScaleLtRho
      (finalUpperScaleConstant Bcopy Cold Λ sourceConstant)
      envelope_absorption
  let Upper :=
    schedule.ProxyUpperCoordinate rho packetCoordinate
  let upperEquiv : Fin (Fintype.card Upper) ≃ Upper :=
    (Fintype.equivFin Upper).symm
  let actualScale : Fin (Fintype.card Upper) → ℝ :=
    fun index =>
      pureWZ2Prop62UpperEnvelopeFactor *
        schedule.actualScale (upperEquiv index).1
  let scaleData :
      ∀ index : Fin (Fintype.card Upper),
        WZ2PaperPureScaleCoverData
          output.restriction.coarseSelected.family
          (actualScale index)
          (finalUpperScaleConstant
            Bcopy Cold Λ sourceConstant) :=
    fun index =>
      output.finalUpperScaleData
        (adapter := adapter) (preliminary_eq := preliminary_eq)
        fineLine fineBase rhoPos widthPos packetScaleLeRho sixWidthLe
        Bcopy Cold Λ sourceConstant
        centerCopyBound ambientUniform densityLoss_le
        (upperEquiv index) (containedLeafSet (upperEquiv index))
        (contained_packet (upperEquiv index))
        (ambient_cwa (upperEquiv index))
  refine
    pureWZ2Prop62ProxyQuotientUpperSchedule
      outputFinite
      (output.finalMetricParents_ordinary_distinct
        fineLine widthPos strongSeparation)
      (Fintype.card Upper)
      (Fintype.card_pos_iff.mpr upperNonempty)
      actualScale scaleData ?_
  intro requested
  rcases rounding requested with
    ⟨coordinate, requestedLe, window⟩
  let index := upperEquiv.symm coordinate
  refine ⟨index, ?_, ?_⟩
  · simpa [actualScale, index] using requestedLe
  · simpa [actualScale, index] using window

/--
Public nearby-scale CWA obtained from the concrete quotient upper schedule.
No preassembled upper uniformity or upper fiber-CWA family is an input.
-/
theorem finalMetricParents_publicPureCWA
    (preliminary_eq :
      output.cleanup.preliminary = adapter.preCore.preliminary)
    (fineLine : WZ1PaperIsLineClass fine)
    (fineBase : ∀ source, ‖(fine.tube source).base‖ ≤ 5)
    (rhoPos : 0 < rho)
    (widthPos : 0 < width)
    (packetScaleLtRho :
      schedule.actualScale packetCoordinate < rho)
    (rhoLeOne : rho ≤ 1)
    (sixWidthLe : 6 * width ≤ rho / 2)
    (strongSeparation :
      360 * rho <
        (((strideBase + 1 : ℕ) : ℝ) - 1) * width)
    (Bcopy Cold Λ sourceConstant : ENNReal)
    (centerCopyBound :
      ∀ coordinate :
          schedule.ProxyUpperCoordinate rho packetCoordinate,
        ∀ center,
          ((quotient.centerActualParents
            coordinate.1 center).card : ENNReal) ≤ Bcopy)
    (ambientUniform :
      ∀ coordinate :
          schedule.ProxyUpperCoordinate rho packetCoordinate,
        WZ2PaperPureFullFibersAreCUniform
          fine (schedule.scaleData coordinate.1).coarse Cold)
    (densityLoss_le : output.quotientDensityLoss ≤ Λ)
    (outputFinite :
      WZ2PaperFiniteErrorConstant
        (finalUpperScaleConstant Bcopy Cold Λ sourceConstant))
    (envelope_absorption :
      (pureWZ2Prop62UpperEnvelopeFactor : ENNReal) * scaleWindow ≤
        finalUpperScaleConstant Bcopy Cold Λ sourceConstant)
    (containedLeafSet :
      schedule.ProxyUpperCoordinate rho packetCoordinate →
        Fin fine.card → Set Point3 → Finset (Fin fine.card))
    (contained_packet :
      ∀ coordinate :
          schedule.ProxyUpperCoordinate rho packetCoordinate,
        ∀ parent : Fin
            (output.finalUpperCover
              (adapter := adapter) (preliminary_eq := preliminary_eq)
              fineLine fineBase rhoPos coordinate).selectedParents.family.card,
          ∀ anchor ∈ output.cleanup.core.core,
            ∀ convexSet,
              ∀ child ∈
                  pureWZ2Prop62UpperCoverContainedAmbientFiber
                    output.finalMetricParentsSubfamily
                    (output.finalUpperCover
                      (adapter := adapter)
                      (preliminary_eq := preliminary_eq)
                      fineLine fineBase rhoPos coordinate).selectedParents.family
                    parent
                    (output.finalUpperNormalization
                      (adapter := adapter)
                      (preliminary_eq := preliminary_eq)
                      fineLine fineBase rhoPos coordinate parent)
                    convexSet,
                ((adapter.preCore.wholeLeaves ∩
                  quotient.centerPacketIndices coordinate.1
                    (quotient.leafCenter coordinate.1 anchor)).filter
                  fun leaf =>
                    output.metric.ambientMetricParentOf leaf = child) ⊆
                      containedLeafSet coordinate anchor convexSet)
    (ambient_cwa :
      ∀ coordinate :
          schedule.ProxyUpperCoordinate rho packetCoordinate,
        ∀ parent : Fin
            (output.finalUpperCover
              (adapter := adapter) (preliminary_eq := preliminary_eq)
              fineLine fineBase rhoPos coordinate).selectedParents.family.card,
          ∀ anchor ∈ output.cleanup.core.core,
            ∀ convexSet, Convex ℝ convexSet →
              ((containedLeafSet
                coordinate anchor convexSet).card : ENNReal) ≤
                sourceConstant *
                  (pureWZ2Prop62UpperEnvelopeGeometricLoss *
                    MeasureTheory.volume convexSet) *
                  ((output.cleanup.auxiliary.prefixNodeAt
                    (coordinate.1.1 + 1) anchor).card : ENNReal))
    :
    WZ2PaperPureCWAAtNearbyScales
      output.restriction.coarseSelected.family
      (finalUpperScaleConstant Bcopy Cold Λ sourceConstant) :=
  pureWZ2_prop62_proxyQuotientUpperSchedule_publicPureCWA <|
    output.finalUpperSchedule
      (adapter := adapter) (preliminary_eq := preliminary_eq)
      fineLine fineBase rhoPos widthPos packetScaleLtRho rhoLeOne sixWidthLe
      strongSeparation Bcopy Cold Λ sourceConstant
      centerCopyBound ambientUniform densityLoss_le outputFinite
      envelope_absorption containedLeafSet
      contained_packet ambient_cwa

end PureWZ2Prop62ProxyQuotientMetricCoreOutput

end Kakeya.Assouad

end
