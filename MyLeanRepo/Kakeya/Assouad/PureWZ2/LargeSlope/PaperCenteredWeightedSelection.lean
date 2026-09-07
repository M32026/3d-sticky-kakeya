import MyLeanRepo.Kakeya.Assouad.PropStickyFiniteParentRegularization
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12PureHitParentRestriction
import MyLeanRepo.Kakeya.Assouad.WZ1.GreedyIndependentSet

/-!
# Weighted selection for public centered distinctness

The public Definition 2.12 conflict relation is carrier containment in either
centered two-fold dilation.  This module applies the generic finite weighted
independent-set theorem directly to that relation.  It does not pass through
the volume-intersection predicate `DeltaTube.EssentiallyDistinct`.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- The symmetric public conflict relation on an indexed ordinary family. -/
def pureWZ2PaperCenteredConflict
    {rho : ℝ}
    (family : Kakeya.Streamlined.TubeFamily rho)
    (first second : Fin family.card) : Prop :=
  first ≠ second ∧
    ((family.tube first).carrier ⊆
        wz2PaperCenteredDilatedCarrier 2 (family.tube second) ∨
      (family.tube second).carrier ⊆
        wz2PaperCenteredDilatedCarrier 2 (family.tube first))

theorem pureWZ2PaperCenteredConflict_symmetric
    {rho : ℝ}
    (family : Kakeya.Streamlined.TubeFamily rho)
    (first second : Fin family.card) :
    pureWZ2PaperCenteredConflict family first second →
      pureWZ2PaperCenteredConflict family second first := by
  rintro ⟨hne, hconflict⟩
  exact ⟨hne.symm, hconflict.symm⟩

/--
A bounded public-centered conflict degree admits a public essentially
distinct subfamily retaining the corresponding fraction of paper shading
mass.  The output shading is the literal restriction along the selected tube
embedding.
-/
theorem pureWZ2_paper_weighted_centered_distinct_selection
    {rho : ℝ}
    (family : Kakeya.Streamlined.TubeFamily rho)
    (shading : WZ1PaperTubeShading family)
    (degree : ℕ)
    (hdegree : ∀ reference,
      ((Finset.univ : Finset (Fin family.card)).filter
        (pureWZ2PaperCenteredConflict family reference)).card ≤ degree) :
    ∃ selected : Finset (Fin family.card),
      let subfamily :=
        Kakeya.Streamlined.TubeSubfamily.fromFinset family selected
      WZ2PaperOrdinaryIsEssentiallyDistinct subfamily.family ∧
        (∀ index : Fin family.card,
          index ∈ selected ∨
            ∃ representative ∈ selected,
              pureWZ2PaperCenteredConflict
                family index representative) ∧
        shading.mass ≤
          (degree + 1 : ENNReal) *
            (restrictPaperShading subfamily shading).mass := by
  let weight : Fin family.card → ENNReal := fun index =>
    volume (shading.carrier index)
  rcases greedy_weighted_independent_set
      (Finset.univ : Finset (Fin family.card)) weight
      (pureWZ2PaperCenteredConflict family)
      (pureWZ2PaperCenteredConflict_symmetric family) degree
      (fun reference _ => hdegree reference) with
    ⟨heavy, _hheavy, hheavyIndependent, hheavyMass⟩
  let candidates : Finset (Finset (Fin family.card)) :=
    (Finset.univ : Finset (Finset (Fin family.card))).filter fun selected =>
      heavy ⊆ selected ∧
        ∀ first ∈ selected, ∀ second ∈ selected, first ≠ second →
          ¬pureWZ2PaperCenteredConflict family first second
  have hcandidates : candidates.Nonempty := by
    refine ⟨heavy, ?_⟩
    simp only [candidates, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨Finset.Subset.rfl, hheavyIndependent⟩
  rcases Finset.exists_max_image candidates Finset.card hcandidates with
    ⟨selected, hselectedCandidate, hselectedMax⟩
  have hselectedSpec := (Finset.mem_filter.mp hselectedCandidate).2
  have hheavySelected : heavy ⊆ selected := hselectedSpec.1
  have hindependent := hselectedSpec.2
  have hmaximal : ∀ index : Fin family.card,
      index ∈ selected ∨
        ∃ representative ∈ selected,
          pureWZ2PaperCenteredConflict family index representative := by
    intro index
    by_cases hindex : index ∈ selected
    · exact Or.inl hindex
    · right
      by_contra hnone
      have hdistinct : ∀ representative ∈ selected,
          ¬pureWZ2PaperCenteredConflict family index representative := by
        simpa [not_exists] using hnone
      let enlarged := insert index selected
      have henlargedIndependent :
          ∀ first ∈ enlarged, ∀ second ∈ enlarged, first ≠ second →
            ¬pureWZ2PaperCenteredConflict family first second := by
        intro first hfirst second hsecond hne
        rcases Finset.mem_insert.mp hfirst with rfl | hfirstSelected
        · rcases Finset.mem_insert.mp hsecond with hsecondEq | hsecondSelected
          · exact False.elim (hne hsecondEq.symm)
          · exact hdistinct second hsecondSelected
        · rcases Finset.mem_insert.mp hsecond with rfl | hsecondSelected
          · intro hconflict
            exact hdistinct first hfirstSelected
              (pureWZ2PaperCenteredConflict_symmetric family _ _
                hconflict)
          · exact hindependent first hfirstSelected second hsecondSelected hne
      have henlargedCandidate : enlarged ∈ candidates := by
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_, henlargedIndependent⟩
        exact hheavySelected.trans (Finset.subset_insert index selected)
      have hmaxCard := hselectedMax enlarged henlargedCandidate
      have hcard : enlarged.card = selected.card + 1 := by
        simp [enlarged, hindex]
      rw [hcard] at hmaxCard
      omega
  have hmass :
      (∑ index, weight index) ≤
        (degree + 1 : ENNReal) * ∑ index ∈ selected, weight index := by
    calc
      (∑ index, weight index) ≤
          (degree + 1 : ENNReal) * ∑ index ∈ heavy, weight index :=
        hheavyMass
      _ ≤ (degree + 1 : ENNReal) * ∑ index ∈ selected, weight index := by
        gcongr
  let subfamily :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset family selected
  have hdistinct :
      WZ2PaperOrdinaryIsEssentiallyDistinct subfamily.family := by
    intro first second hne
    have hambientNe :
        subfamily.embedding first ≠ subfamily.embedding second :=
      subfamily.embedding.injective.ne hne
    have hfirstMem : subfamily.embedding first ∈ selected :=
      Finset.orderEmbOfFin_mem selected rfl first
    have hsecondMem : subfamily.embedding second ∈ selected :=
      Finset.orderEmbOfFin_mem selected rfl second
    have hnotConflict := hindependent
      (subfamily.embedding first) hfirstMem
      (subfamily.embedding second) hsecondMem hambientNe
    constructor
    · intro hcontain
      apply hnotConflict
      exact ⟨hambientNe, Or.inl (by
        simpa only [subfamily.tube_eq] using hcontain)⟩
    · intro hcontain
      apply hnotConflict
      exact ⟨hambientNe, Or.inr (by
        simpa only [subfamily.tube_eq] using hcontain)⟩
  refine ⟨selected, hdistinct, hmaximal, ?_⟩
  rw [restrictPaperShading_fromFinset_mass]
  change
    (∑ index : Fin family.card, volume (shading.carrier index)) ≤
      (degree + 1 : ENNReal) *
        ∑ index ∈ selected, volume (shading.carrier index)
  simpa [weight] using hmass

/-- ENNReal-valued public conflict-degree cleanup.  The finite maximum
actual degree is used internally, so the output loses only `degreeBound + 1`
and no arbitrary ceiling factor. -/
theorem pureWZ2_paper_weighted_centered_distinct_selection_ennreal
    {rho : ℝ}
    (family : Kakeya.Streamlined.TubeFamily rho)
    (shading : WZ1PaperTubeShading family)
    (degreeBound : ENNReal)
    (hdegree : ∀ reference,
      (((Finset.univ : Finset (Fin family.card)).filter
        (pureWZ2PaperCenteredConflict family reference)).card : ENNReal) ≤
          degreeBound) :
    ∃ selected : Finset (Fin family.card),
      let subfamily :=
        Kakeya.Streamlined.TubeSubfamily.fromFinset family selected
      WZ2PaperOrdinaryIsEssentiallyDistinct subfamily.family ∧
        (∀ index : Fin family.card,
          index ∈ selected ∨
            ∃ representative ∈ selected,
              pureWZ2PaperCenteredConflict family index representative) ∧
        shading.mass ≤
          (degreeBound + 1) *
            (restrictPaperShading subfamily shading).mass := by
  let conflictDegree : Fin family.card → ℕ := fun reference =>
    ((Finset.univ : Finset (Fin family.card)).filter
      (pureWZ2PaperCenteredConflict family reference)).card
  let degree : ℕ := Finset.univ.sup conflictDegree
  have hdegreeNat : ∀ reference, conflictDegree reference ≤ degree := by
    intro reference
    exact Finset.le_sup (Finset.mem_univ reference)
  rcases pureWZ2_paper_weighted_centered_distinct_selection
      family shading degree hdegreeNat with
    ⟨selected, hdistinct, hmaximal, hmass⟩
  have hdegreeMax : (degree : ENNReal) ≤ degreeBound := by
    by_cases hcard : family.card = 0
    · have hzero : degree = 0 := by
        apply Nat.eq_zero_of_le_zero
        apply Finset.sup_le
        intro reference _
        have himpossible : reference.val < 0 := by
          simpa [hcard] using reference.isLt
        omega
      simp [hzero]
    · have hnonempty :
          (Finset.univ : Finset (Fin family.card)).Nonempty := by
        have hpos : 0 < family.card := Nat.pos_of_ne_zero hcard
        exact ⟨⟨0, hpos⟩, Finset.mem_univ _⟩
      rcases Finset.exists_mem_eq_sup Finset.univ hnonempty conflictDegree with
        ⟨reference, _href, hmax⟩
      change ((Finset.univ.sup conflictDegree : ℕ) : ENNReal) ≤ degreeBound
      rw [hmax]
      simpa [conflictDegree] using hdegree reference
  refine ⟨selected, hdistinct, hmaximal, hmass.trans ?_⟩
  gcongr

end Kakeya.Assouad
