import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62CompleteColorClass
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62MetricPacketProducer

/-!
# Proposition 6.2 metric parents: preliminary leaf set and packet hull

The dependent color class is selected before the dyadic leaf-weight bin.  Its
old-parent image determines the complete packet hull used to construct the
metric parents.  The actual preliminary leaf set remains the dyadic selected
subset inside that hull and is pulled back through the hull reindexing.

This distinction is essential: packet-level mesh and ancestry coordinates are
constant on old strict packets, while the source-conflict color is genuinely a
leaf color.  All are chosen in one dependent vector, but only the packet hull
is completed before the one augmented-tree cleanup.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

structure PureWZ2Prop62MetricPreliminaryOutput
    {delta scale rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    (oldData : WZ2PaperPureScaleCoverData fine scale C)
    {coordinateCount : ℕ}
    (Color : Fin coordinateCount → Type*)
    [∀ coordinate, Fintype (Color coordinate)]
    [∀ coordinate, DecidableEq (Color coordinate)]
    [∀ coordinate, Nonempty (Color coordinate)]
    (color : ∀ coordinate, Fin fine.card → Color coordinate)
    (weight : Fin fine.card → ENNReal)
    (preliminary :
      PureWZ2Prop62PreliminarySelectionData
        coordinateCount Color color weight)
    (width M : ℝ) where
  metric :
    PureWZ2Prop62MetricPacketOutput
      (rho := rho) oldData width M
  metric_parents_eq :
    metric.selectedParents =
      preliminary.selectedOldParents (oldData := oldData)
  colorClass_subset_packet_hull :
    preliminary.colorClass ⊆
      metric.mesh.complete.selectedFineIndices
  selectedPreliminary :
    Finset (Fin metric.selectedFine.card)
  selectedPreliminary_eq :
    selectedPreliminary =
      Finset.univ.filter fun source =>
        metric.mesh.complete.selectedFine.embedding source ∈
          preliminary.selected
  selectedPreliminary_nonempty :
    selectedPreliminary.Nonempty
  selectedPreliminary_image_eq :
    Finset.image metric.mesh.complete.selectedFine.embedding
        selectedPreliminary =
      preliminary.selected

theorem pureWZ2_prop62_metric_preliminary_output
    {delta scale rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    (oldData : WZ2PaperPureScaleCoverData fine scale C)
    {coordinateCount : ℕ}
    (Color : Fin coordinateCount → Type*)
    [∀ coordinate, Fintype (Color coordinate)]
    [∀ coordinate, DecidableEq (Color coordinate)]
    [∀ coordinate, Nonempty (Color coordinate)]
    (color : ∀ coordinate, Fin fine.card → Color coordinate)
    (weight : Fin fine.card → ENNReal)
    (preliminary :
      PureWZ2Prop62PreliminarySelectionData
        coordinateCount Color color weight)
    (width M : ℝ)
    (rhoPos : 0 < rho)
    (fineNonempty : fine.Nonempty)
    (fineLine : WZ1PaperIsLineClass fine)
    (fineLocal :
      ∀ source,
        ‖wz2PaperTubeMidpoint (fine.tube source)‖ ≤ M)
    (widthPos : 0 < width)
    (stride : ℕ)
    (sameResidue :
      ∀ first second,
        first ∈ preliminary.selectedOldParents (oldData := oldData) →
        second ∈ preliminary.selectedOldParents (oldData := oldData) →
          pureWZ2Prop62LineColor width stride
              (oldData.coarse.tube first) =
            pureWZ2Prop62LineColor width stride
              (oldData.coarse.tube second))
    (strongSeparation :
      360 * rho < ((stride : ℝ) - 1) * width)
    (packetBound :
      (16 * M + 44) * scale + 6 * width ≤ rho / 2)
    (oldLine : WZ1PaperIsLineClass oldData.coarse) :
    Nonempty
      (PureWZ2Prop62MetricPreliminaryOutput
        (rho := rho) oldData Color color weight preliminary width M) := by
  let selectedParents :=
    preliminary.selectedOldParents (oldData := oldData)
  have selectedParentsNonempty : selectedParents.Nonempty :=
    preliminary.selectedOldParents_nonempty
  rcases
      pureWZ2_prop62_metric_packet_output
        oldData width M rhoPos fineNonempty fineLine fineLocal
        selectedParents selectedParentsNonempty widthPos stride
        sameResidue strongSeparation packetBound oldLine
    with ⟨metric, metricParents⟩
  have colorClassSubset :
      preliminary.colorClass ⊆
        metric.mesh.complete.selectedFineIndices := by
    intro source sourceMem
    unfold PureWZ2CompleteParentRestrictionData.selectedFineIndices
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ source, ?_⟩
    rw [metric.mesh_selectedParents_eq, metricParents]
    exact
      Finset.mem_image.mpr
        ⟨source, sourceMem, rfl⟩
  let selectedPreliminary :
      Finset (Fin metric.selectedFine.card) :=
    Finset.univ.filter fun source =>
      metric.mesh.complete.selectedFine.embedding source ∈
        preliminary.selected
  have selectedPreliminaryNonempty :
      selectedPreliminary.Nonempty := by
    rcases preliminary.selected_nonempty with ⟨source, sourceMem⟩
    have sourceColorClass :
        source ∈ preliminary.colorClass :=
      preliminary.selected_subset_colorClass sourceMem
    have sourceHull :
        source ∈ metric.mesh.complete.selectedFineIndices :=
      colorClassSubset sourceColorClass
    rcases
        metric.mesh.complete.selectedFine_ambient_surjective
          source sourceHull
      with ⟨selectedSource, selectedSourceEq⟩
    exact
      ⟨selectedSource,
        Finset.mem_filter.mpr
          ⟨Finset.mem_univ selectedSource, by
            rw [selectedSourceEq]
            exact sourceMem⟩⟩
  have selectedPreliminaryImage :
      Finset.image metric.mesh.complete.selectedFine.embedding
          selectedPreliminary =
        preliminary.selected := by
    ext source
    constructor
    · intro sourceImage
      rcases Finset.mem_image.mp sourceImage with
        ⟨selectedSource, selectedSourceMem, rfl⟩
      exact (Finset.mem_filter.mp selectedSourceMem).2
    · intro sourceMem
      have sourceColorClass :
          source ∈ preliminary.colorClass :=
        preliminary.selected_subset_colorClass sourceMem
      have sourceHull :
          source ∈ metric.mesh.complete.selectedFineIndices :=
        colorClassSubset sourceColorClass
      rcases
          metric.mesh.complete.selectedFine_ambient_surjective
            source sourceHull
        with ⟨selectedSource, selectedSourceEq⟩
      exact
        Finset.mem_image.mpr
          ⟨selectedSource,
            Finset.mem_filter.mpr
              ⟨Finset.mem_univ selectedSource, by
                rw [selectedSourceEq]
                exact sourceMem⟩,
            selectedSourceEq⟩
  exact
    ⟨{
      metric := metric
      metric_parents_eq := metricParents
      colorClass_subset_packet_hull := colorClassSubset
      selectedPreliminary := selectedPreliminary
      selectedPreliminary_eq := rfl
      selectedPreliminary_nonempty := selectedPreliminaryNonempty
      selectedPreliminary_image_eq := selectedPreliminaryImage
    }⟩

namespace PureWZ2Prop62MetricPreliminaryOutput

variable
    {delta scale rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {C : ENNReal}
    {oldData : WZ2PaperPureScaleCoverData fine scale C}
    {coordinateCount : ℕ}
    {Color : Fin coordinateCount → Type*}
    [∀ coordinate, Fintype (Color coordinate)]
    [∀ coordinate, DecidableEq (Color coordinate)]
    [∀ coordinate, Nonempty (Color coordinate)]
    {color : ∀ coordinate, Fin fine.card → Color coordinate}
    {weight : Fin fine.card → ENNReal}
    {preliminary :
      PureWZ2Prop62PreliminarySelectionData
        coordinateCount Color color weight}
    {width M : ℝ}
    (output :
      PureWZ2Prop62MetricPreliminaryOutput
        (rho := rho) oldData Color color weight preliminary width M)

theorem selectedPreliminary_monochromatic
    (source : Fin output.metric.selectedFine.card)
    (sourceMem : source ∈ output.selectedPreliminary)
    (coordinate : Fin coordinateCount) :
    color coordinate
        (output.metric.mesh.complete.selectedFine.embedding source) =
      preliminary.colorVector coordinate := by
  have ambientMem :
      output.metric.mesh.complete.selectedFine.embedding source ∈
        preliminary.selected := by
    rw [output.selectedPreliminary_eq] at sourceMem
    exact (Finset.mem_filter.mp sourceMem).2
  exact
    preliminary.selected_monochromatic
      (output.metric.mesh.complete.selectedFine.embedding source)
      ambientMem coordinate

end PureWZ2Prop62MetricPreliminaryOutput

end Kakeya.Assouad

end
