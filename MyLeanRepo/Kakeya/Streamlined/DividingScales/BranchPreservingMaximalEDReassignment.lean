import MyLeanRepo.Kakeya.Streamlined.CombinatorialLemmas.EssentiallyDistinctSubfamily

/-!
# Branch-preserving maximal essentially-distinct reassignment

Suppose non-essentially-distinct candidate tubes always have the same branch
label.  A maximal essentially-distinct subfamily then dominates every
candidate without crossing branches.

The output keeps all candidate indices through a surjective representative
map onto the selected subfamily.  It makes no geometric cover claim.
-/

noncomputable section

open scoped Classical

namespace Kakeya.Streamlined

/-- Maximal ED selection together with a branch-preserving representative. -/
structure BranchPreservingMaximalEDPackage
    {rho : ℝ}
    (candidate : TubeFamily rho)
    {Branch : Type*}
    (branch : Fin candidate.card → Branch) where
  selectedIndices : Finset (Fin candidate.card)
  selectedDistinct :
    ∀ first ∈ selectedIndices,
    ∀ second ∈ selectedIndices,
      first ≠ second →
        (candidate.tube first).EssentiallyDistinct
          (candidate.tube second)
  representative :
    Fin candidate.card → Fin selectedIndices.card
  representative_eq_or_conflict :
    ∀ index,
      selectedIndices.orderEmbOfFin rfl (representative index) = index ∨
        ¬(candidate.tube index).EssentiallyDistinct
          (candidate.tube
            (selectedIndices.orderEmbOfFin rfl
              (representative index)))
  representative_sameBranch :
    ∀ index,
      branch
          (selectedIndices.orderEmbOfFin rfl
            (representative index)) =
        branch index
  representative_surjective :
    Function.Surjective representative

namespace BranchPreservingMaximalEDPackage

variable
    {rho : ℝ}
    {candidate : TubeFamily rho}
    {Branch : Type*}
    {branch : Fin candidate.card → Branch}

/-- The selected candidate tube family. -/
def selectedFamily
    (package :
      BranchPreservingMaximalEDPackage candidate branch) :
    TubeSubfamily candidate :=
  TubeSubfamily.fromFinset candidate package.selectedIndices

/-- Ambient index of one selected representative. -/
def selectedEmbedding
    (package :
      BranchPreservingMaximalEDPackage candidate branch) :
    Fin package.selectedIndices.card → Fin candidate.card :=
  package.selectedIndices.orderEmbOfFin rfl

/-- The selected family is pairwise essentially distinct. -/
theorem selectedFamily_essentiallyDistinct
    (package :
      BranchPreservingMaximalEDPackage candidate branch) :
    package.selectedFamily.family.IsEssentiallyDistinct := by
  intro first second hne
  let ambientFirst := package.selectedEmbedding first
  let ambientSecond := package.selectedEmbedding second
  have hfirst :
      ambientFirst ∈ package.selectedIndices :=
    Finset.orderEmbOfFin_mem package.selectedIndices rfl first
  have hsecond :
      ambientSecond ∈ package.selectedIndices :=
    Finset.orderEmbOfFin_mem package.selectedIndices rfl second
  have hambientNe : ambientFirst ≠ ambientSecond := by
    intro heq
    exact hne <|
      (package.selectedIndices.orderEmbOfFin rfl).injective heq
  rw [TubeSubfamily.tube_eq, TubeSubfamily.tube_eq]
  exact
    package.selectedDistinct
      ambientFirst hfirst ambientSecond hsecond hambientNe

/-- Every selected ambient index is fixed by the representative map. -/
theorem representative_of_selected
    (package :
      BranchPreservingMaximalEDPackage candidate branch)
    (selected : Fin package.selectedIndices.card) :
    package.representative (package.selectedEmbedding selected) =
      selected := by
  rcases
      package.representative_eq_or_conflict
        (package.selectedEmbedding selected) with
    heq | hconflict
  · exact
      (package.selectedIndices.orderEmbOfFin rfl).injective heq
  · have hselected :
        package.selectedEmbedding selected ∈
          package.selectedIndices :=
      Finset.orderEmbOfFin_mem package.selectedIndices rfl selected
    have hrepresentative :
        package.selectedEmbedding
            (package.representative
              (package.selectedEmbedding selected)) ∈
          package.selectedIndices :=
      Finset.orderEmbOfFin_mem package.selectedIndices rfl _
    have hdistinct :=
      package.selectedDistinct
        (package.selectedEmbedding selected) hselected
        (package.selectedEmbedding
          (package.representative
            (package.selectedEmbedding selected)))
        hrepresentative
    by_contra hne
    have hambientNe :
        package.selectedEmbedding selected ≠
          package.selectedEmbedding
            (package.representative
              (package.selectedEmbedding selected)) := by
      exact fun heq =>
        hne ((package.selectedIndices.orderEmbOfFin rfl).injective heq.symm)
    exact hconflict (hdistinct hambientNe)

end BranchPreservingMaximalEDPackage

/--
A maximal ED subfamily gives a surjective representative map that preserves
every branch label respected by the conflict relation.
-/
theorem exists_branchPreservingMaximalEDPackage
    {rho : ℝ}
    (candidate : TubeFamily rho)
    {Branch : Type*}
    (branch : Fin candidate.card → Branch)
    (hconflictBranch :
      ∀ first second,
        ¬(candidate.tube first).EssentiallyDistinct
            (candidate.tube second) →
          branch first = branch second) :
    Nonempty
      (BranchPreservingMaximalEDPackage candidate branch) := by
  classical
  rcases
      exists_maximal_essentially_distinct_subfamily candidate with
    ⟨selectedIndices, hselectedDistinct, hmaximal⟩
  let ambientRepresentative :
      Fin candidate.card → Fin candidate.card :=
    fun index =>
      if hselected : index ∈ selectedIndices then
        index
      else
        Classical.choose (hmaximal index hselected)
  have hrepresentativeMem :
      ∀ index, ambientRepresentative index ∈ selectedIndices := by
    intro index
    by_cases hselected : index ∈ selectedIndices
    · simpa [ambientRepresentative, hselected] using hselected
    · simpa [ambientRepresentative, hselected] using
        (Classical.choose_spec
          (hmaximal index hselected)).1
  have hrepresentativeData :
      ∀ index,
        ambientRepresentative index = index ∨
          ¬(candidate.tube index).EssentiallyDistinct
            (candidate.tube (ambientRepresentative index)) := by
    intro index
    by_cases hselected : index ∈ selectedIndices
    · exact Or.inl (by simp [ambientRepresentative, hselected])
    · exact Or.inr <| by
        simpa [ambientRepresentative, hselected] using
          (Classical.choose_spec
            (hmaximal index hselected)).2
  have himage :
      Finset.image
          (selectedIndices.orderEmbOfFin rfl)
          Finset.univ =
        selectedIndices :=
    Finset.image_orderEmbOfFin_univ selectedIndices rfl
  let representative
      (index : Fin candidate.card) :
      Fin selectedIndices.card :=
    Classical.choose <| Finset.mem_image.mp <| by
      rw [himage]
      exact hrepresentativeMem index
  have hrepresentativeSpec :
      ∀ index,
        selectedIndices.orderEmbOfFin rfl
            (representative index) =
          ambientRepresentative index := by
    intro index
    exact
      (Classical.choose_spec <| Finset.mem_image.mp <| by
        rw [himage]
        exact hrepresentativeMem index).2
  have hsurjective : Function.Surjective representative := by
    intro selected
    let ambient := selectedIndices.orderEmbOfFin rfl selected
    have hambientMem :
        ambient ∈ selectedIndices :=
      Finset.orderEmbOfFin_mem selectedIndices rfl selected
    refine ⟨ambient, ?_⟩
    apply (selectedIndices.orderEmbOfFin rfl).injective
    rw [hrepresentativeSpec]
    simp [ambientRepresentative, hambientMem, ambient]
  exact
    ⟨{
      selectedIndices := selectedIndices
      selectedDistinct := hselectedDistinct
      representative := representative
      representative_eq_or_conflict := by
        intro index
        rw [hrepresentativeSpec]
        exact hrepresentativeData index
      representative_sameBranch := by
        intro index
        rw [hrepresentativeSpec]
        rcases hrepresentativeData index with heq | hconflict
        · rw [heq]
        · exact (hconflictBranch index
            (ambientRepresentative index) hconflict).symm
      representative_surjective := hsurjective
    }⟩

end Kakeya.Streamlined
