import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CommonSliceAxialAssembly
import Mathlib.Combinatorics.Pigeonhole

/-!
# Finite weighted label selection

One label retains at least the average weight of a finite weighted set.
This is used to select a horizontal chart and a separated interval residue
simultaneously in Proposition 6.3.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

attribute [local instance] Classical.propDecidable

theorem exists_weighted_label_retaining_average
    {Item Label : Type*} [Fintype Item] [Fintype Label] [Nonempty Label]
    (weight : Item → ENNReal) (label : Item → Label) :
    ∃ chosen : Label,
      (∑ item, weight item) ≤
        (Fintype.card Label : ENNReal) *
          ∑ item, if label item = chosen then weight item else 0 := by
  let labelWeight : Label → ENNReal := fun chosen =>
    ∑ item, if label item = chosen then weight item else 0
  rcases Kakeya.Assouad.exists_ge_average labelWeight with
    ⟨chosen, hchosen⟩
  refine ⟨chosen, ?_⟩
  have hpartition : (∑ candidate, labelWeight candidate) =
      ∑ item, weight item := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro item _
    simp [labelWeight]
  rw [hpartition] at hchosen
  exact hchosen

end Kakeya.Assouad.PureWZ2

end
