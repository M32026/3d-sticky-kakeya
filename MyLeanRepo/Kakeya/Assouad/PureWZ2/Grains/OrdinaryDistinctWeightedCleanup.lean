import MyLeanRepo.Kakeya.Assouad.WZ1.GreedyIndependentSet
import MyLeanRepo.Kakeya.Assouad.AnisotropicRescaling.SelectedTubeFamily
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12

/-!
# Weighted cleanup for Definition 2.12 ordinary distinctness

The ordinary conflict relation is symmetric: two indexed tubes conflict when
either carrier lies in the centered two-fold dilation of the other.  A
bounded-degree greedy independent set therefore produces a genuine indexed
subfamily satisfying both noncontainment clauses of Assouad Definition 2.12,
while retaining an arbitrary nonnegative external weight.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

attribute [local instance] Classical.propDecidable

/-- The symmetric centered-doubled containment conflict relation. -/
def ordinaryContainmentConflict
    {delta : ℝ}
    (family : Kakeya.Streamlined.TubeFamily delta)
    (first second : Fin family.card) : Prop :=
  first ≠ second ∧
    ((family.tube first).carrier ⊆
        wz2PaperCenteredDilatedCarrier 2 (family.tube second) ∨
      (family.tube second).carrier ⊆
        wz2PaperCenteredDilatedCarrier 2 (family.tube first))

/-- Weighted greedy cleanup in the exact ordinary Definition 2.12 sense. -/
theorem ordinary_distinct_weighted_cleanup
    {delta : ℝ}
    (family : Kakeya.Streamlined.TubeFamily delta)
    (weight : Fin family.card → ENNReal)
    (degreeBound : ℕ)
    (hdegree :
      ∀ first,
        ((Finset.univ : Finset (Fin family.card)).filter fun second =>
          ordinaryContainmentConflict family first second).card ≤
            degreeBound) :
    ∃ selected : Finset (Fin family.card),
      WZ2PaperOrdinaryIsEssentiallyDistinct
        (selectedTubeFamily family selected) ∧
      (degreeBound + 1 : ENNReal) *
          (∑ index ∈ selected, weight index) ≥
        ∑ index : Fin family.card, weight index := by
  classical
  let relation : Fin family.card → Fin family.card → Prop :=
    ordinaryContainmentConflict family
  have hsymm :
      ∀ first second, relation first second → relation second first := by
    intro first second hconflict
    exact ⟨hconflict.1.symm, hconflict.2.symm⟩
  rcases
      greedy_weighted_independent_set
        (Finset.univ : Finset (Fin family.card))
        weight relation hsymm degreeBound (by
          intro first _
          exact hdegree first)
    with ⟨selected, _hselected, hindependent, hweight⟩
  have hdistinct :
      WZ2PaperOrdinaryIsEssentiallyDistinct
        (selectedTubeFamily family selected) := by
    intro first second hne
    let ambientFirst : Fin family.card :=
      (selected.equivFin.symm first).1
    let ambientSecond : Fin family.card :=
      (selected.equivFin.symm second).1
    have hfirstMem : ambientFirst ∈ selected :=
      (selected.equivFin.symm first).2
    have hsecondMem : ambientSecond ∈ selected :=
      (selected.equivFin.symm second).2
    have hambientNe : ambientFirst ≠ ambientSecond := by
      intro heq
      apply hne
      exact selected.equivFin.symm.injective (Subtype.ext heq)
    have hnoConflict : ¬relation ambientFirst ambientSecond :=
      hindependent ambientFirst hfirstMem ambientSecond hsecondMem hambientNe
    have hnoContainment :
        ¬((family.tube ambientFirst).carrier ⊆
              wz2PaperCenteredDilatedCarrier 2
                (family.tube ambientSecond) ∨
          (family.tube ambientSecond).carrier ⊆
              wz2PaperCenteredDilatedCarrier 2
                (family.tube ambientFirst)) := by
      intro hcontainment
      exact hnoConflict ⟨hambientNe, hcontainment⟩
    have hboth := not_or.mp hnoContainment
    simpa only [selectedTubeFamily_tube] using hboth
  exact ⟨selected, hdistinct, by simpa using hweight⟩

end Kakeya.Assouad.PureWZ2

end
