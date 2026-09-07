import MyLeanRepo.Kakeya.Assouad.WZ1.InducedTripleRefinement
import MyLeanRepo.Kakeya.Assouad.WZ1.WideFixedCellNormalizationStatements

/-!
# Split statements for the wide fixed-cell selection

The paper's fixed-cell step has two finite combinatorial stages before the
final exponent bookkeeping:

1. select one absolute grid-cell triple retaining a fixed fraction of the
   current graph;
2. apply Lemma 37 inside that cell and replace the ambient cell classes by
   the active projections of the same refined graph.

These statements preserve one graph throughout and expose the precise losses
that the final analytic assembly must absorb.
-/

noncomputable section

namespace Kakeya.Assouad

open scoped ENNReal

/--
An absolute upper bound for the number of `1/100` grid-cell triples meeting
three planar sets contained in the radius-three ball.
-/
def wz1WideFixedCellCountLoss : ENNReal :=
  (10 : ENNReal) ^ (18 : ℕ)

/-- One heavy `1/100` grid-cell triple in a bounded tripartite graph. -/
structure WZ1WideFixedHeavyCellData
    (F G₁ G₂ : DiscreteSet 2)
    (H : Finset (Point2 × Point2 × Point2)) where
  centerF : Point2
  centerG₁ : Point2
  centerG₂ : Point2
  ambientCellF : DiscreteSet 2
  ambientCellG₁ : DiscreteSet 2
  ambientCellG₂ : DiscreteSet 2
  inducedH : Finset (Point2 × Point2 × Point2)
  ambientCellF_eq :
    ambientCellF =
      F.filter
        (fun point => gridCenter (1 / 100) point = centerF)
  ambientCellG₁_eq :
    ambientCellG₁ =
      G₁.filter
        (fun point => gridCenter (1 / 100) point = centerG₁)
  ambientCellG₂_eq :
    ambientCellG₂ =
      G₂.filter
        (fun point => gridCenter (1 / 100) point = centerG₂)
  inducedH_eq :
    inducedH =
      H.filter
        (fun edge =>
          gridCenter (1 / 100) edge.1 = centerF ∧
            gridCenter (1 / 100) edge.2.1 = centerG₁ ∧
            gridCenter (1 / 100) edge.2.2 = centerG₂)
  inducedH_nonempty : inducedH.Nonempty
  inducedH_subset : inducedH ⊆ H
  inducedH_support :
    ∀ edge ∈ inducedH,
      edge.1 ∈ ambientCellF ∧
        edge.2.1 ∈ ambientCellG₁ ∧
        edge.2.2 ∈ ambientCellG₂
  ambientCellF_nonempty : ambientCellF.Nonempty
  ambientCellG₁_nonempty : ambientCellG₁.Nonempty
  ambientCellG₂_nonempty : ambientCellG₂.Nonempty
  ambientCellF_subset : ambientCellF ⊆ F
  ambientCellG₁_subset : ambientCellG₁ ⊆ G₁
  ambientCellG₂_subset : ambientCellG₂ ⊆ G₂
  ambientCellF_ball :
    ∀ point ∈ ambientCellF, dist point centerF ≤ 1 / 100
  ambientCellG₁_ball :
    ∀ point ∈ ambientCellG₁, dist point centerG₁ ≤ 1 / 100
  ambientCellG₂_ball :
    ∀ point ∈ ambientCellG₂, dist point centerG₂ ≤ 1 / 100
  edge_retention :
    (H.card : ENNReal) ≤
      wz1WideFixedCellCountLoss * (inducedH.card : ENNReal)

/--
Select a heavy fixed grid-cell triple from a graph supported on three
radius-three planar sets.
-/
def WZ1WideFixedHeavyCellStatement : Prop :=
  ∀ (F G₁ G₂ : DiscreteSet 2)
    (H : Finset (Point2 × Point2 × Point2)),
    H.Nonempty →
    (∀ edge ∈ H,
      edge.1 ∈ F ∧ edge.2.1 ∈ G₁ ∧ edge.2.2 ∈ G₂) →
    (∀ point ∈ F, dist point 0 ≤ 3) →
    (∀ point ∈ G₁, dist point 0 ≤ 3) →
    (∀ point ∈ G₂, dist point 0 ≤ 3) →
      Nonempty (WZ1WideFixedHeavyCellData F G₁ G₂ H)

/--
The same-graph combinatorial package after refining one heavy cell and
replacing its ambient classes by the active projections of the refinement.
-/
structure WZ1WideFixedRefinedActiveData
    {delta epsilon eta : ℝ}
    {parameters : WZ1Proposition8_9Parameters epsilon}
    {F G₁ G₂ : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    {data :
      WZ1Proposition8_9CommonStripData
        delta epsilon eta parameters F G₁ G₂ H}
    (coarse :
      WZ1Proposition8_9WideCoarseData
        delta epsilon eta parameters F G₁ G₂ H data) where
  heavy :
    WZ1WideFixedHeavyCellData
      coarse.coarseF coarse.coarseG₁ coarse.coarseG₂ coarse.coarseH
  cellH : Finset (Point2 × Point2 × Point2)
  cellF : DiscreteSet 2
  cellG₁ : DiscreteSet 2
  cellG₂ : DiscreteSet 2
  cellH_subset : cellH ⊆ heavy.inducedH
  cellF_eq : cellF = wz1ActiveTripleProjection cellH 0
  cellG₁_eq : cellG₁ = wz1ActiveTripleProjection cellH 1
  cellG₂_eq : cellG₂ = wz1ActiveTripleProjection cellH 2
  cellF_nonempty : cellF.Nonempty
  cellG₁_nonempty : cellG₁.Nonempty
  cellG₂_nonempty : cellG₂.Nonempty
  cellH_nonempty : cellH.Nonempty
  cellF_subset : cellF ⊆ heavy.ambientCellF
  cellG₁_subset : cellG₁ ⊆ heavy.ambientCellG₁
  cellG₂_subset : cellG₂ ⊆ heavy.ambientCellG₂
  cellH_support :
    ∀ edge ∈ cellH,
      edge.1 ∈ cellF ∧
        edge.2.1 ∈ cellG₁ ∧
        edge.2.2 ∈ cellG₂
  cellF_separated : cellF.IsDeltaSeparated coarse.scale
  cellG₁_separated : cellG₁.IsDeltaSeparated coarse.scale
  cellG₂_separated : cellG₂.IsDeltaSeparated coarse.scale
  uniform_margin :
    WZ1UniformTripleDensity
      ((Kakeya.realRpowENN delta eta / (2 ^ 27 : ENNReal)) /
        (16 * wz1WideFixedCellCountLoss))
      cellF cellG₁ cellG₂ cellH
  cellF_retention :
    ((Kakeya.realRpowENN delta eta / (2 ^ 27 : ENNReal)) /
        (16 * wz1WideFixedCellCountLoss)) *
        coarse.coarseF.enncard ≤
      cellF.enncard
  cellG₁_retention :
    ((Kakeya.realRpowENN delta eta / (2 ^ 27 : ENNReal)) /
        (16 * wz1WideFixedCellCountLoss)) *
        coarse.coarseG₁.enncard ≤
      cellG₁.enncard
  cellG₂_retention :
    ((Kakeya.realRpowENN delta eta / (2 ^ 27 : ENNReal)) /
        (16 * wz1WideFixedCellCountLoss)) *
        coarse.coarseG₂.enncard ≤
      cellG₂.enncard
  quantitative_separation :
    ∀ edge ∈ cellH,
      1 / 3 ≤ dist edge.1 0 ∧
        2 / 5 ≤ dist edge.2.1 edge.2.2

/--
Refine one heavy cell using Lemma 37 and retain the active projections of
that exact refined graph.
-/
def WZ1WideFixedRefinedActiveStatement : Prop :=
  WZ1WideFixedHeavyCellStatement →
    WZ1TripartiteHypergraphRefinementStatement →
      ∀ {delta epsilon eta : ℝ}
        {parameters : WZ1Proposition8_9Parameters epsilon}
        {F G₁ G₂ : DiscreteSet 2}
        {H : Finset (Point2 × Point2 × Point2)}
        {data :
          WZ1Proposition8_9CommonStripData
            delta epsilon eta parameters F G₁ G₂ H}
        (coarse :
          WZ1Proposition8_9WideCoarseData
            delta epsilon eta parameters F G₁ G₂ H data),
        coarse.scale ≤ 1 / 20 →
          Nonempty (WZ1WideFixedRefinedActiveData coarse)

end Kakeya.Assouad
