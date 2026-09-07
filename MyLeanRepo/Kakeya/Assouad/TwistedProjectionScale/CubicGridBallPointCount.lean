import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.CubicGridPartitionTree

/-!
# Point count from intersecting cubic-grid cells
-/

noncomputable section

namespace Kakeya.Assouad

/--
If every occupied level cell has the same cardinality, the points in one ball
are bounded by the number of level cells meeting that ball times the common
cell cardinality.
-/
lemma cubicGrid_ballCount_le_cells_mul_card
    {A : DiscreteSet 3}
    {base level cellCard : ℕ}
    {x : Point 3} {r : ℝ}
    (hcellCard :
      ∀ cell ∈ cubicGridPartition base level A,
        cell.card = cellCard) :
    A.ballCount x r ≤
      (((cubicGridPartition base level A).filter
        (fun cell => ∃ p ∈ cell, dist p x ≤ r)).card : ENNReal) *
        (cellCard : ENNReal) := by
  let selected :=
    (cubicGridPartition base level A).filter
      (fun cell => ∃ p ∈ cell, dist p x ≤ r)
  let pointsInBall :=
    A.filter fun p => dist p x ≤ r
  have hcover :
      pointsInBall ⊆ selected.biUnion id := by
    intro point hpoint
    have hpointA := (Finset.mem_filter.mp hpoint).1
    have hpointBall := (Finset.mem_filter.mp hpoint).2
    let cell := cubicGridCell base level A point
    have hcell :
        cell ∈ cubicGridPartition base level A :=
      Finset.mem_image.mpr ⟨point, hpointA, rfl⟩
    have hpointCell : point ∈ cell := by
      simp [cell, cubicGridCell, hpointA]
    have hselected : cell ∈ selected :=
      Finset.mem_filter.mpr
        ⟨hcell, ⟨point, hpointCell, hpointBall⟩⟩
    exact Finset.mem_biUnion.mpr
      ⟨cell, hselected, hpointCell⟩
  have hcard :
      pointsInBall.card ≤
        ∑ cell ∈ selected, cell.card := by
    exact
      (Finset.card_le_card hcover).trans
        Finset.card_biUnion_le
  have hsum :
      ∑ cell ∈ selected, cell.card =
        selected.card * cellCard := by
    calc
      ∑ cell ∈ selected, cell.card =
          ∑ _cell ∈ selected, cellCard := by
        apply Finset.sum_congr rfl
        intro cell hcell
        exact hcellCard cell
          (Finset.mem_filter.mp hcell).1
      _ = selected.card * cellCard := by
        simp [Finset.sum_const]
  rw [hsum] at hcard
  simpa [DiscreteSet.ballCount, pointsInBall,
    selected, Nat.cast_mul] using
    (show
      (pointsInBall.card : ENNReal) ≤
        (selected.card * cellCard : ℕ) by
      exact_mod_cast hcard)

end Kakeya.Assouad
