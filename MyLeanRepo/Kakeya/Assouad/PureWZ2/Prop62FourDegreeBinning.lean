import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62FourDegreeIncidence
import MyLeanRepo.Kakeya.Assouad.PropStickyExactCellBalancingHelpers

/-!
# Proposition 6.2: the three ordered degree bins

Starting from the packet-cell edge pool, this module performs exactly the
three dyadic selections in the paper:

1. fine-cell degree in the original pool;
2. `(parent, coarse-cell)` degree after the first restriction;
3. coarse-cell degree after the second restriction.

The degrees are recomputed after each restriction.  The output records the
three actual logarithmic bin counts and derives the common `J^3` retention
only from explicit upper bounds on those counts.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

namespace PureWZ2Prop62FourDegreeIncidenceData

variable
    {Parent FineCell CoarseCell : Type*}
    [DecidableEq Parent]
    [DecidableEq FineCell]
    [DecidableEq CoarseCell]
    (data :
      PureWZ2Prop62FourDegreeIncidenceData
        Parent FineCell CoarseCell)

/-- The degree of a vertex map on a current edge set. -/
def degreeAlong
    {Vertex : Type*} [DecidableEq Vertex]
    (edges : Finset data.Edge)
    (vertex : data.Edge → Vertex) (value : Vertex) : ℕ :=
  (edges.filter fun edge => vertex edge = value).card

/-- One dyadic vertex-degree selection, weighted by incident edges. -/
structure DegreeBinData
    {Vertex : Type*} [DecidableEq Vertex]
    (edges : Finset data.Edge)
    (vertex : data.Edge → Vertex) where
  level : ℕ
  selectedVertices : Finset Vertex
  selectedVertices_nonempty : selectedVertices.Nonempty
  selectedVertices_subset :
    selectedVertices ⊆ edges.image vertex
  selectedEdges : Finset data.Edge
  selectedEdges_eq :
    selectedEdges =
      edges.filter fun edge => vertex edge ∈ selectedVertices
  selectedEdges_nonempty : selectedEdges.Nonempty
  selectedEdges_subset : selectedEdges ⊆ edges
  degree_band :
    ∀ value ∈ selectedVertices,
      2 ^ level ≤ data.degreeAlong edges vertex value ∧
        data.degreeAlong edges vertex value < 2 ^ (level + 1)
  binCount : ℕ
  binCount_eq :
    binCount = Nat.log 2 edges.card + 1
  retention :
    edges.card ≤ binCount * selectedEdges.card

theorem degree_sum_over_image
    {Vertex : Type*} [DecidableEq Vertex]
    (edges : Finset data.Edge)
    (vertex : data.Edge → Vertex) :
    (∑ value ∈ edges.image vertex,
        data.degreeAlong edges vertex value) =
      edges.card := by
  have fiberwise :=
    Finset.sum_card_fiberwise_eq_card_filter
      edges (edges.image vertex) vertex
  calc
    (∑ value ∈ edges.image vertex,
        data.degreeAlong edges vertex value) =
        (edges.filter fun edge =>
          vertex edge ∈ edges.image vertex).card := by
      simpa [degreeAlong] using fiberwise
    _ = edges.card := by
      apply congrArg Finset.card
      ext edge
      simp only [Finset.mem_filter]
      constructor
      · exact fun edgeMem => edgeMem.1
      · intro edgeMem
        exact
          ⟨edgeMem,
            Finset.mem_image.mpr ⟨edge, edgeMem, rfl⟩⟩

theorem image_vertex_degree_pos
    {Vertex : Type*} [DecidableEq Vertex]
    (edges : Finset data.Edge)
    (vertex : data.Edge → Vertex) :
    ∀ value ∈ edges.image vertex,
      0 < data.degreeAlong edges vertex value := by
  intro value valueMem
  rcases Finset.mem_image.mp valueMem with
    ⟨edge, edgeMem, edgeValue⟩
  exact
    Finset.card_pos.mpr
      ⟨edge,
        Finset.mem_filter.mpr ⟨edgeMem, edgeValue⟩⟩

theorem pureWZ2_prop62_degree_bin
    {Vertex : Type*} [DecidableEq Vertex]
    (edges : Finset data.Edge)
    (vertex : data.Edge → Vertex)
    (edges_nonempty : edges.Nonempty) :
    Nonempty (data.DegreeBinData edges vertex) := by
  let activeVertices : Finset Vertex :=
    edges.image vertex
  have activeVertices_nonempty : activeVertices.Nonempty := by
    rcases edges_nonempty with ⟨edge, edgeMem⟩
    exact
      ⟨vertex edge,
        Finset.mem_image.mpr ⟨edge, edgeMem, rfl⟩⟩
  have activeDegree_pos :
      ∀ value ∈ activeVertices,
        0 < data.degreeAlong edges vertex value := by
    simpa [activeVertices] using
      data.image_vertex_degree_pos edges vertex
  rcases
      dyadic_band_pigeonhole
        activeVertices
        (data.degreeAlong edges vertex)
        activeVertices_nonempty activeDegree_pos
    with
    ⟨level, selectedVertices, selectedVerticesNonempty,
      selectedVerticesSubset, degreeBand, retention⟩
  let selectedEdges : Finset data.Edge :=
    edges.filter fun edge =>
      vertex edge ∈ selectedVertices
  have selectedEdges_subset : selectedEdges ⊆ edges := by
    exact Finset.filter_subset _ _
  have selectedEdges_card :
      selectedEdges.card =
        ∑ value ∈ selectedVertices,
          data.degreeAlong edges vertex value := by
    have fiberwise :=
      Finset.sum_card_fiberwise_eq_card_filter
        edges selectedVertices vertex
    simpa [selectedEdges, degreeAlong] using fiberwise.symm
  have selectedEdges_nonempty : selectedEdges.Nonempty := by
    have selectedDegreeSum_pos :
        0 <
          ∑ value ∈ selectedVertices,
            data.degreeAlong edges vertex value := by
      apply Finset.sum_pos
      · intro value valueMem
        exact
          lt_of_lt_of_le
            (by positivity : 0 < 2 ^ level)
            (degreeBand value valueMem).1
      · exact selectedVerticesNonempty
    exact
      Finset.card_pos.mp
        (by simpa [selectedEdges_card] using selectedDegreeSum_pos)
  let binCount : ℕ :=
    Nat.log 2 edges.card + 1
  have totalDegree :
      (∑ value ∈ activeVertices,
          data.degreeAlong edges vertex value) =
        edges.card := by
    simpa [activeVertices] using
      data.degree_sum_over_image edges vertex
  have selectedRetention :
      edges.card ≤ binCount * selectedEdges.card := by
    have retention' := retention
    rw [totalDegree] at retention'
    calc
      edges.card ≤
          binCount *
            ∑ value ∈ selectedVertices,
              data.degreeAlong edges vertex value := by
        simpa [binCount] using retention'
      _ = binCount * selectedEdges.card := by
        rw [selectedEdges_card]
  exact
    ⟨{
      level := level
      selectedVertices := selectedVertices
      selectedVertices_nonempty := selectedVerticesNonempty
      selectedVertices_subset := by
        simpa [activeVertices] using selectedVerticesSubset
      selectedEdges := selectedEdges
      selectedEdges_eq := rfl
      selectedEdges_nonempty := selectedEdges_nonempty
      selectedEdges_subset := selectedEdges_subset
      degree_band := degreeBand
      binCount := binCount
      binCount_eq := rfl
      retention := selectedRetention
    }⟩

namespace DegreeBinData

variable
    {Vertex : Type*} [DecidableEq Vertex]
    {edges : Finset data.Edge}
    {vertex : data.Edge → Vertex}
    (selection : data.DegreeBinData edges vertex)

theorem degree_upper_of_subset
    {laterEdges : Finset data.Edge}
    (later_subset : laterEdges ⊆ selection.selectedEdges)
    (value : Vertex)
    (degree_pos :
      0 < data.degreeAlong laterEdges vertex value) :
    data.degreeAlong laterEdges vertex value <
      2 ^ (selection.level + 1) := by
  rcases Finset.card_pos.mp degree_pos with
    ⟨edge, edgeMem⟩
  have edgeLater : edge ∈ laterEdges :=
    (Finset.mem_filter.mp edgeMem).1
  have edgeValue : vertex edge = value :=
    (Finset.mem_filter.mp edgeMem).2
  have edgeSelected : edge ∈ selection.selectedEdges :=
    later_subset edgeLater
  have valueSelected : value ∈ selection.selectedVertices := by
    rw [selection.selectedEdges_eq] at edgeSelected
    have vertexSelected :=
      (Finset.mem_filter.mp edgeSelected).2
    simpa [edgeValue] using vertexSelected
  have later_subset_edges : laterEdges ⊆ edges := by
    exact later_subset.trans selection.selectedEdges_subset
  have degree_mono :
      data.degreeAlong laterEdges vertex value ≤
        data.degreeAlong edges vertex value := by
    apply Finset.card_le_card
    intro candidate candidateMem
    have candidateData := Finset.mem_filter.mp candidateMem
    exact
      Finset.mem_filter.mpr
        ⟨later_subset_edges candidateData.1, candidateData.2⟩
  exact
    lt_of_le_of_lt degree_mono
      (selection.degree_band value valueSelected).2

theorem active_card_mul_lower_le_card
    {laterEdges : Finset data.Edge}
    (later_subset : laterEdges ⊆ selection.selectedEdges) :
    (laterEdges.image vertex).card * 2 ^ selection.level ≤
      edges.card := by
  have activeSubset :
      laterEdges.image vertex ⊆ selection.selectedVertices := by
    intro value valueMem
    rcases Finset.mem_image.mp valueMem with
      ⟨edge, edgeMem, rfl⟩
    have edgeSelected := later_subset edgeMem
    rw [selection.selectedEdges_eq] at edgeSelected
    exact (Finset.mem_filter.mp edgeSelected).2
  calc
    (laterEdges.image vertex).card * 2 ^ selection.level =
        ∑ _value ∈ laterEdges.image vertex,
          2 ^ selection.level := by
      simp
    _ ≤
        ∑ value ∈ laterEdges.image vertex,
          data.degreeAlong edges vertex value := by
      apply Finset.sum_le_sum
      intro value valueMem
      exact (selection.degree_band value (activeSubset valueMem)).1
    _ ≤
        ∑ value ∈ edges.image vertex,
          data.degreeAlong edges vertex value := by
      apply Finset.sum_le_sum_of_subset
      intro value valueMem
      rcases Finset.mem_image.mp valueMem with
        ⟨edge, edgeMem, rfl⟩
      exact
        Finset.mem_image.mpr
          ⟨edge, selection.selectedEdges_subset (later_subset edgeMem), rfl⟩
    _ = edges.card :=
      data.degree_sum_over_image edges vertex

end DegreeBinData

/-- The three paper-ordered dyadic restrictions. -/
structure ThreeDegreeBinningData
    (initialEdges : Finset data.Edge) where
  fineCellBin :
    data.DegreeBinData initialEdges data.edgeFineCell
  parentCoarseBin :
    data.DegreeBinData
      fineCellBin.selectedEdges data.edgeParentCoarse
  coarseCellBin :
    data.DegreeBinData
      parentCoarseBin.selectedEdges data.edgeCoarseCell

namespace ThreeDegreeBinningData

variable
    {initialEdges : Finset data.Edge}
    (bins : data.ThreeDegreeBinningData initialEdges)

/-- The paper's `J_0`, after the three ordered degree bins. -/
def finalEdges : Finset data.Edge :=
  bins.coarseCellBin.selectedEdges

theorem finalEdges_nonempty :
    bins.finalEdges.Nonempty :=
  bins.coarseCellBin.selectedEdges_nonempty

theorem finalEdges_subset_parentCoarse :
    bins.finalEdges ⊆
      bins.parentCoarseBin.selectedEdges :=
  bins.coarseCellBin.selectedEdges_subset

theorem finalEdges_subset_fineCell :
    bins.finalEdges ⊆
      bins.fineCellBin.selectedEdges :=
  bins.finalEdges_subset_parentCoarse.trans
    bins.parentCoarseBin.selectedEdges_subset

theorem finalEdges_subset_initial :
    bins.finalEdges ⊆ initialEdges :=
  bins.finalEdges_subset_fineCell.trans
    bins.fineCellBin.selectedEdges_subset

theorem exact_retention :
    initialEdges.card ≤
      bins.fineCellBin.binCount *
        bins.parentCoarseBin.binCount *
          bins.coarseCellBin.binCount *
            bins.finalEdges.card := by
  calc
    initialEdges.card ≤
        bins.fineCellBin.binCount *
          bins.fineCellBin.selectedEdges.card :=
      bins.fineCellBin.retention
    _ ≤
        bins.fineCellBin.binCount *
          (bins.parentCoarseBin.binCount *
            bins.parentCoarseBin.selectedEdges.card) := by
      exact
        Nat.mul_le_mul_left _
          bins.parentCoarseBin.retention
    _ ≤
        bins.fineCellBin.binCount *
          (bins.parentCoarseBin.binCount *
            (bins.coarseCellBin.binCount *
              bins.finalEdges.card)) := by
      exact
        Nat.mul_le_mul_left _
          (Nat.mul_le_mul_left _
            bins.coarseCellBin.retention)
    _ =
        bins.fineCellBin.binCount *
          bins.parentCoarseBin.binCount *
            bins.coarseCellBin.binCount *
              bins.finalEdges.card := by
      ring

theorem common_log_retention
    (J : ℕ)
    (fine_le : bins.fineCellBin.binCount ≤ J)
    (parentCoarse_le :
      bins.parentCoarseBin.binCount ≤ J)
    (coarse_le : bins.coarseCellBin.binCount ≤ J) :
    initialEdges.card ≤ J ^ 3 * bins.finalEdges.card := by
  have coefficient_le :
      bins.fineCellBin.binCount *
          bins.parentCoarseBin.binCount *
            bins.coarseCellBin.binCount ≤
        J ^ 3 := by
    calc
      bins.fineCellBin.binCount *
          bins.parentCoarseBin.binCount *
            bins.coarseCellBin.binCount ≤
          J * J * J := by
        exact
          Nat.mul_le_mul
            (Nat.mul_le_mul fine_le parentCoarse_le)
            coarse_le
      _ = J ^ 3 := by ring
  exact
    bins.exact_retention.trans
      (Nat.mul_le_mul_right
        bins.finalEdges.card coefficient_le)

theorem final_fineCellDegree_upper
    (fineCell : FineCell)
    (degree_pos :
      0 < data.fineCellDegree bins.finalEdges fineCell) :
    data.fineCellDegree bins.finalEdges fineCell <
      2 ^ (bins.fineCellBin.level + 1) := by
  simpa [fineCellDegree, degreeAlong] using
    DegreeBinData.degree_upper_of_subset
      data bins.fineCellBin
      bins.finalEdges_subset_fineCell
      fineCell
      (by simpa [fineCellDegree, degreeAlong] using degree_pos)

theorem final_parentCoarseDegree_upper
    (parent : Parent) (coarseCell : CoarseCell)
    (degree_pos :
      0 <
        data.parentCoarseDegree
          bins.finalEdges parent coarseCell) :
    data.parentCoarseDegree bins.finalEdges parent coarseCell <
      2 ^ (bins.parentCoarseBin.level + 1) := by
  simpa [
    parentCoarseDegree, degreeAlong,
    edgeParentCoarse
  ] using
    DegreeBinData.degree_upper_of_subset
      data bins.parentCoarseBin
      bins.finalEdges_subset_parentCoarse
      (parent, coarseCell)
      (by
        simpa [
          parentCoarseDegree, degreeAlong,
          edgeParentCoarse
        ] using degree_pos)

theorem final_coarseDegree_upper
    (coarseCell : CoarseCell)
    (degree_pos :
      0 < data.coarseDegree bins.finalEdges coarseCell) :
    data.coarseDegree bins.finalEdges coarseCell <
      2 ^ (bins.coarseCellBin.level + 1) := by
  simpa [coarseDegree, degreeAlong] using
    DegreeBinData.degree_upper_of_subset
      data bins.coarseCellBin
      (laterEdges := bins.finalEdges)
      (by
        intro edge edgeMem
        exact edgeMem)
      coarseCell
      (by simpa [coarseDegree, degreeAlong] using degree_pos)

end ThreeDegreeBinningData

theorem pureWZ2_prop62_three_degree_binning
    (initialEdges : Finset data.Edge)
    (initialEdges_nonempty : initialEdges.Nonempty) :
    Nonempty (data.ThreeDegreeBinningData initialEdges) := by
  rcases
      data.pureWZ2_prop62_degree_bin
        initialEdges data.edgeFineCell initialEdges_nonempty
    with ⟨fineCellBin⟩
  rcases
      data.pureWZ2_prop62_degree_bin
        fineCellBin.selectedEdges data.edgeParentCoarse
        fineCellBin.selectedEdges_nonempty
    with ⟨parentCoarseBin⟩
  rcases
      data.pureWZ2_prop62_degree_bin
        parentCoarseBin.selectedEdges data.edgeCoarseCell
        parentCoarseBin.selectedEdges_nonempty
    with ⟨coarseCellBin⟩
  exact
    ⟨{
      fineCellBin := fineCellBin
      parentCoarseBin := parentCoarseBin
      coarseCellBin := coarseCellBin
    }⟩

end PureWZ2Prop62FourDegreeIncidenceData

end Kakeya.Assouad

end
