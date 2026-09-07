import MyLeanRepo.Kakeya.Assouad.WZ1.SimultaneousDegreeRegularization.TCore

/-!
# Proposition 6.2: the four-degree packet-cell incidence graph

This module freezes the finite incidence graph used at the start of the
four-degree regularization lemma.  An edge is literally a metric-parent and
fine-cell pair.  Its coarse cell is derived from the fine cell, so the three
coordinates cannot become inconsistent after restriction.

All degrees are defined for an arbitrary subcollection of the initial edge
pool.  This is the form needed by the three dyadic bins and the subsequent
T-core deletion.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

structure PureWZ2Prop62FourDegreeIncidenceData
    (Parent FineCell CoarseCell : Type*)
    [DecidableEq Parent]
    [DecidableEq FineCell]
    [DecidableEq CoarseCell] where
  coarseCellOf : FineCell → CoarseCell
  edgePool : Finset (Parent × FineCell)

namespace PureWZ2Prop62FourDegreeIncidenceData

variable
    {Parent FineCell CoarseCell : Type*}
    [DecidableEq Parent]
    [DecidableEq FineCell]
    [DecidableEq CoarseCell]
    (data :
      PureWZ2Prop62FourDegreeIncidenceData
        Parent FineCell CoarseCell)

/-- An edge of the initial packet-cell incidence pool. -/
abbrev Edge :=
  {edge : Parent × FineCell // edge ∈ data.edgePool}

/-- The metric-parent endpoint of an incidence edge. -/
def edgeParent (edge : data.Edge) : Parent :=
  edge.1.1

/-- The fixed fine-cell endpoint of an incidence edge. -/
def edgeFineCell (edge : data.Edge) : FineCell :=
  edge.1.2

/-- The unique fixed coarse cell containing the fine-cell endpoint. -/
def edgeCoarseCell (edge : data.Edge) : CoarseCell :=
  data.coarseCellOf (data.edgeFineCell edge)

/-- The paired `(P,Q)` endpoint used for the third degree. -/
def edgeParentCoarse (edge : data.Edge) : Parent × CoarseCell :=
  (data.edgeParent edge, data.edgeCoarseCell edge)

/-- The full initial edge set, reindexed by its literal subtype. -/
def allEdges : Finset data.Edge :=
  Finset.univ

/-- `K(P)`: the number of current packet-cells incident to a parent. -/
def parentDegree (edges : Finset data.Edge) (parent : Parent) : ℕ :=
  (edges.filter fun edge => data.edgeParent edge = parent).card

/-- `d(q)`: the number of current parents incident to a fine cell. -/
def fineCellDegree (edges : Finset data.Edge) (fineCell : FineCell) : ℕ :=
  (edges.filter fun edge => data.edgeFineCell edge = fineCell).card

/-- `n(P,Q)`: the number of current fine cells joining `P` to `Q`. -/
def parentCoarseDegree
    (edges : Finset data.Edge)
    (parent : Parent) (coarseCell : CoarseCell) : ℕ :=
  (edges.filter fun edge =>
    data.edgeParent edge = parent ∧
      data.edgeCoarseCell edge = coarseCell).card

/-- `D(Q)`: the number of current packet-cell edges inside `Q`. -/
def coarseDegree
    (edges : Finset data.Edge) (coarseCell : CoarseCell) : ℕ :=
  (edges.filter fun edge =>
    data.edgeCoarseCell edge = coarseCell).card

def IsActiveParent
    (edges : Finset data.Edge) (parent : Parent) : Prop :=
  0 < data.parentDegree edges parent

def IsActiveFineCell
    (edges : Finset data.Edge) (fineCell : FineCell) : Prop :=
  0 < data.fineCellDegree edges fineCell

def IsActiveParentCoarse
    (edges : Finset data.Edge)
    (parent : Parent) (coarseCell : CoarseCell) : Prop :=
  0 < data.parentCoarseDegree edges parent coarseCell

def IsActiveCoarseCell
    (edges : Finset data.Edge) (coarseCell : CoarseCell) : Prop :=
  0 < data.coarseDegree edges coarseCell

/-- The positive support of `K(P)`. -/
def activeParents (edges : Finset data.Edge) : Finset Parent :=
  edges.image data.edgeParent

/-- The positive support of `d(q)`. -/
def activeFineCells (edges : Finset data.Edge) : Finset FineCell :=
  edges.image data.edgeFineCell

/-- The positive support of `n(P,Q)` as a set of pairs. -/
def activeParentCoarsePairs
    (edges : Finset data.Edge) : Finset (Parent × CoarseCell) :=
  edges.image data.edgeParentCoarse

/-- The positive support of `D(Q)`. -/
def activeCoarseCells (edges : Finset data.Edge) : Finset CoarseCell :=
  edges.image data.edgeCoarseCell

/-- The active fine cells lying in a fixed coarse cell `Q`. -/
def activeFineCellsAt
    (edges : Finset data.Edge) (coarseCell : CoarseCell) :
    Finset FineCell :=
  data.activeFineCells edges |>.filter fun fineCell =>
    data.coarseCellOf fineCell = coarseCell

/-- The parents with positive `(P,Q)` degree at a fixed `Q`. -/
def activeParentsAt
    (edges : Finset data.Edge) (coarseCell : CoarseCell) :
    Finset Parent :=
  (edges.filter fun edge =>
    data.edgeCoarseCell edge = coarseCell).image data.edgeParent

@[simp]
theorem mem_activeParents_iff
    (edges : Finset data.Edge) (parent : Parent) :
    parent ∈ data.activeParents edges ↔
      0 < data.parentDegree edges parent := by
  constructor
  · intro parentMem
    rcases Finset.mem_image.mp parentMem with
      ⟨edge, edgeMem, edgeParent⟩
    exact
      Finset.card_pos.mpr
        ⟨edge,
          Finset.mem_filter.mpr
            ⟨edgeMem, edgeParent⟩⟩
  · intro degreePos
    rcases Finset.card_pos.mp degreePos with
      ⟨edge, edgeMem⟩
    exact
      Finset.mem_image.mpr
        ⟨edge, (Finset.mem_filter.mp edgeMem).1,
          (Finset.mem_filter.mp edgeMem).2⟩

@[simp]
theorem mem_activeFineCells_iff
    (edges : Finset data.Edge) (fineCell : FineCell) :
    fineCell ∈ data.activeFineCells edges ↔
      0 < data.fineCellDegree edges fineCell := by
  constructor
  · intro cellMem
    rcases Finset.mem_image.mp cellMem with
      ⟨edge, edgeMem, edgeCell⟩
    exact
      Finset.card_pos.mpr
        ⟨edge,
          Finset.mem_filter.mpr
            ⟨edgeMem, edgeCell⟩⟩
  · intro degreePos
    rcases Finset.card_pos.mp degreePos with
      ⟨edge, edgeMem⟩
    exact
      Finset.mem_image.mpr
        ⟨edge, (Finset.mem_filter.mp edgeMem).1,
          (Finset.mem_filter.mp edgeMem).2⟩

@[simp]
theorem mem_activeParentCoarsePairs_iff
    (edges : Finset data.Edge)
    (pair : Parent × CoarseCell) :
    pair ∈ data.activeParentCoarsePairs edges ↔
      0 < data.parentCoarseDegree edges pair.1 pair.2 := by
  constructor
  · intro pairMem
    rcases Finset.mem_image.mp pairMem with
      ⟨edge, edgeMem, edgePair⟩
    have parentEq :
        data.edgeParent edge = pair.1 :=
      congrArg Prod.fst edgePair
    have coarseEq :
        data.edgeCoarseCell edge = pair.2 :=
      congrArg Prod.snd edgePair
    exact
      Finset.card_pos.mpr
        ⟨edge,
          Finset.mem_filter.mpr
            ⟨edgeMem, parentEq, coarseEq⟩⟩
  · intro degreePos
    rcases Finset.card_pos.mp degreePos with
      ⟨edge, edgeMem⟩
    have edgeData := Finset.mem_filter.mp edgeMem
    exact
      Finset.mem_image.mpr
        ⟨edge, edgeData.1,
          Prod.ext edgeData.2.1 edgeData.2.2⟩

@[simp]
theorem mem_activeCoarseCells_iff
    (edges : Finset data.Edge) (coarseCell : CoarseCell) :
    coarseCell ∈ data.activeCoarseCells edges ↔
      0 < data.coarseDegree edges coarseCell := by
  constructor
  · intro cellMem
    rcases Finset.mem_image.mp cellMem with
      ⟨edge, edgeMem, edgeCell⟩
    exact
      Finset.card_pos.mpr
        ⟨edge,
          Finset.mem_filter.mpr
            ⟨edgeMem, edgeCell⟩⟩
  · intro degreePos
    rcases Finset.card_pos.mp degreePos with
      ⟨edge, edgeMem⟩
    exact
      Finset.mem_image.mpr
        ⟨edge, (Finset.mem_filter.mp edgeMem).1,
          (Finset.mem_filter.mp edgeMem).2⟩

@[simp]
theorem mem_activeFineCellsAt_iff
    (edges : Finset data.Edge)
    (coarseCell : CoarseCell) (fineCell : FineCell) :
    fineCell ∈ data.activeFineCellsAt edges coarseCell ↔
      0 < data.fineCellDegree edges fineCell ∧
        data.coarseCellOf fineCell = coarseCell := by
  simp [activeFineCellsAt]

@[simp]
theorem mem_activeParentsAt_iff
    (edges : Finset data.Edge)
    (coarseCell : CoarseCell) (parent : Parent) :
    parent ∈ data.activeParentsAt edges coarseCell ↔
      0 < data.parentCoarseDegree edges parent coarseCell := by
  constructor
  · intro parentMem
    rcases Finset.mem_image.mp parentMem with
      ⟨edge, edgeMem, edgeParent⟩
    have edgeData := Finset.mem_filter.mp edgeMem
    exact
      Finset.card_pos.mpr
        ⟨edge,
          Finset.mem_filter.mpr
            ⟨edgeData.1, edgeParent, edgeData.2⟩⟩
  · intro degreePos
    rcases Finset.card_pos.mp degreePos with
      ⟨edge, edgeMem⟩
    have edgeData := Finset.mem_filter.mp edgeMem
    exact
      Finset.mem_image.mpr
        ⟨edge,
          Finset.mem_filter.mpr
            ⟨edgeData.1, edgeData.2.2⟩,
          edgeData.2.1⟩

/-- Double count the current edge set over its parent fibers. -/
theorem card_eq_sum_parentDegree
    (edges : Finset data.Edge) :
    edges.card =
      ∑ parent ∈ data.activeParents edges,
        data.parentDegree edges parent := by
  symm
  have fiberwise :=
    Finset.sum_card_fiberwise_eq_card_filter
      edges (data.activeParents edges) data.edgeParent
  calc
    (∑ parent ∈ data.activeParents edges,
        data.parentDegree edges parent) =
        (edges.filter fun edge =>
          data.edgeParent edge ∈
            data.activeParents edges).card := by
      simpa [parentDegree] using fiberwise
    _ = edges.card := by
      apply congrArg Finset.card
      ext edge
      simp only [Finset.mem_filter]
      constructor
      · exact fun edgeData => edgeData.1
      · intro edgeMem
        exact
          ⟨edgeMem,
            Finset.mem_image.mpr
              ⟨edge, edgeMem, rfl⟩⟩

/-- Double count the current edge set over its fine-cell fibers. -/
theorem card_eq_sum_fineCellDegree
    (edges : Finset data.Edge) :
    edges.card =
      ∑ fineCell ∈ data.activeFineCells edges,
        data.fineCellDegree edges fineCell := by
  symm
  have fiberwise :=
    Finset.sum_card_fiberwise_eq_card_filter
      edges (data.activeFineCells edges) data.edgeFineCell
  calc
    (∑ fineCell ∈ data.activeFineCells edges,
        data.fineCellDegree edges fineCell) =
        (edges.filter fun edge =>
          data.edgeFineCell edge ∈
            data.activeFineCells edges).card := by
      simpa [fineCellDegree] using fiberwise
    _ = edges.card := by
      apply congrArg Finset.card
      ext edge
      simp only [Finset.mem_filter]
      constructor
      · exact fun edgeData => edgeData.1
      · intro edgeMem
        exact
          ⟨edgeMem,
            Finset.mem_image.mpr
              ⟨edge, edgeMem, rfl⟩⟩

/-- For fixed `Q`, `D(Q)` is the sum of `d(q)` over its positive support. -/
theorem coarseDegree_eq_sum_fineCellDegree
    (edges : Finset data.Edge) (coarseCell : CoarseCell) :
    data.coarseDegree edges coarseCell =
      ∑ fineCell ∈ data.activeFineCellsAt edges coarseCell,
        data.fineCellDegree edges fineCell := by
  symm
  calc
    (∑ fineCell ∈ data.activeFineCellsAt edges coarseCell,
        data.fineCellDegree edges fineCell) =
        (edges.filter fun edge =>
          data.edgeFineCell edge ∈
            data.activeFineCellsAt edges coarseCell).card := by
      simpa [fineCellDegree] using
        (Finset.sum_card_fiberwise_eq_card_filter
          edges
          (data.activeFineCellsAt edges coarseCell)
          data.edgeFineCell)
    _ = data.coarseDegree edges coarseCell := by
      apply congrArg Finset.card
      ext edge
      simp only [
        Finset.mem_filter,
        mem_activeFineCellsAt_iff,
        fineCellDegree,
        Nat.card_pos,
        coarseDegree
      ]
      constructor
      · rintro ⟨edgeMem, _degreePos, edgeCoarse⟩
        exact ⟨edgeMem, edgeCoarse⟩
      · rintro ⟨edgeMem, edgeCoarse⟩
        refine ⟨edgeMem, ?_, edgeCoarse⟩
        exact
          Finset.card_pos.mpr
            ⟨edge, Finset.mem_filter.mpr ⟨edgeMem, rfl⟩⟩

/-- For fixed `Q`, `D(Q)` is the sum of `n(P,Q)` over its positive support. -/
theorem coarseDegree_eq_sum_parentCoarseDegree
    (edges : Finset data.Edge) (coarseCell : CoarseCell) :
    data.coarseDegree edges coarseCell =
      ∑ parent ∈ data.activeParentsAt edges coarseCell,
        data.parentCoarseDegree edges parent coarseCell := by
  let coarseEdges : Finset data.Edge :=
    edges.filter fun edge =>
      data.edgeCoarseCell edge = coarseCell
  symm
  calc
    (∑ parent ∈ data.activeParentsAt edges coarseCell,
        data.parentCoarseDegree edges parent coarseCell) =
        (coarseEdges.filter fun edge =>
          data.edgeParent edge ∈
            data.activeParentsAt edges coarseCell).card := by
      have fiberwise :=
        Finset.sum_card_fiberwise_eq_card_filter
          coarseEdges
          (data.activeParentsAt edges coarseCell)
          data.edgeParent
      simpa [
        coarseEdges, parentCoarseDegree,
        Finset.filter_filter, and_assoc, and_left_comm,
        and_comm
      ] using fiberwise
    _ = coarseEdges.card := by
      apply congrArg Finset.card
      ext edge
      simp only [
        coarseEdges, Finset.mem_filter,
        mem_activeParentsAt_iff,
        parentCoarseDegree
      ]
      constructor
      · exact fun edgeMem => edgeMem.1
      · intro edgeMem
        refine ⟨edgeMem, ?_⟩
        exact
          Finset.card_pos.mpr
            ⟨edge,
              Finset.mem_filter.mpr
                ⟨edgeMem.1, rfl, edgeMem.2⟩⟩
    _ = data.coarseDegree edges coarseCell := by
      rfl

/-- The paper identity
`D(Q) = ∑_{q ∈ A(Q)} d(q) = ∑_{P : n(P,Q)>0} n(P,Q)`. -/
theorem coarseDegree_eq_degree_sums
    (edges : Finset data.Edge) (coarseCell : CoarseCell) :
    data.coarseDegree edges coarseCell =
        ∑ fineCell ∈ data.activeFineCellsAt edges coarseCell,
          data.fineCellDegree edges fineCell ∧
      data.coarseDegree edges coarseCell =
        ∑ parent ∈ data.activeParentsAt edges coarseCell,
          data.parentCoarseDegree edges parent coarseCell :=
  ⟨data.coarseDegree_eq_sum_fineCellDegree edges coarseCell,
    data.coarseDegree_eq_sum_parentCoarseDegree edges coarseCell⟩

end PureWZ2Prop62FourDegreeIncidenceData

end Kakeya.Assouad

end
