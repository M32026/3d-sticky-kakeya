import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.WeightedOSBranchingUniformRefinementStatement

/-!
# Globalize one local certificate across uniform finite cells

If a global measurable set is partitioned into finitely many comparable
positive cells, then a local subset supported on only a few cells controls
the thickening of the whole global set.  The total number of global cells
cancels between the global area and thickening estimates.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

/--
Cancellation-free finite-cell globalization.

`globalSet` is the disjoint union of the occupied cells.  Every two cell
areas are comparable by `R`, every cell has `rho`-thickening area at most
`V`, and `localSet` is contained in the union of at most `M` occupied cells.
If `L ≤ volume localSet`, then

`L * volume (cthickening rho globalSet) ≤
  R * M * V * volume globalSet`.

The statement avoids division and does not assume the total number of global
cells is known.
-/
def FiniteUniformCellGlobalizationStatement : Prop :=
  ∀ (α : Type) [DecidableEq α],
    ∀ cells : Finset α,
      cells.Nonempty →
        ∀ cellSet : α → Set Point2,
          (∀ cell ∈ cells, MeasurableSet (cellSet cell)) →
          (∀ cell₁ ∈ cells, ∀ cell₂ ∈ cells,
            cell₁ ≠ cell₂ →
              Disjoint (cellSet cell₁) (cellSet cell₂)) →
          (∀ cell ∈ cells, volume (cellSet cell) ≠ 0) →
          ∀ R : ENNReal,
            (∀ cell₁ ∈ cells, ∀ cell₂ ∈ cells,
              volume (cellSet cell₁) ≤
                R * volume (cellSet cell₂)) →
            ∀ globalSet : Set Point2,
              globalSet = finiteAtomUnion cells cellSet →
              ∀ rho : ℝ, 0 ≤ rho →
                ∀ V : ENNReal,
                  (∀ cell ∈ cells,
                    volume
                        (Metric.cthickening rho (cellSet cell)) ≤
                      V) →
                  ∀ selected : Finset α,
                    selected ⊆ cells →
                    ∀ M : ℕ, selected.card ≤ M →
                      ∀ localSet : Set Point2,
                        localSet ⊆ finiteAtomUnion selected cellSet →
                        ∀ L : ENNReal,
                          L ≤ volume localSet →
                            L *
                                volume
                                  (Metric.cthickening rho globalSet) ≤
                              R * (M : ENNReal) * V *
                                volume globalSet

end Kakeya.Assouad
