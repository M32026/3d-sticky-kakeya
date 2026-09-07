import MyLeanRepo.Kakeya.Assouad.PropStickyFiniteFiberRatio

/-!
# Restrict a paper partitioning cover to selected tubes and hit parents

After repeated pigeonholing, the selected fine family need not meet every
ambient coarse parent.  The correct restricted cover therefore retains
exactly the coarse parents hit by a selected source tube.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/-- Ambient coarse indices hit by the selected fine subfamily. -/
def WZ2PaperPartitioningCover.hitParentIndices
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (selected : Kakeya.Streamlined.TubeSubfamily fine) :
    Finset (Fin coarse.card) :=
  Finset.univ.image fun index =>
    cover.parent (selected.embedding index)

/-- The genuine coarse subfamily consisting of the hit parents. -/
def WZ2PaperPartitioningCover.hitParentSubfamily
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (selected : Kakeya.Streamlined.TubeSubfamily fine) :
    Kakeya.Streamlined.TubeSubfamily coarse :=
  Kakeya.Streamlined.TubeSubfamily.fromFinset coarse
    (cover.hitParentIndices selected)

/-- The hit-parent index assigned to one selected source tube. -/
def WZ2PaperPartitioningCover.hitParent
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (selected : Kakeya.Streamlined.TubeSubfamily fine) :
    Fin selected.family.card →
      Fin (cover.hitParentSubfamily selected).family.card := fun index =>
  let parents := cover.hitParentIndices selected
  let equivalence : Fin parents.card ≃ parents :=
    (parents.orderIsoOfFin rfl).toEquiv
  equivalence.symm
    ⟨cover.parent (selected.embedding index), by
      apply Finset.mem_image.mpr
      exact ⟨index, Finset.mem_univ _, rfl⟩⟩

@[simp] theorem WZ2PaperPartitioningCover.hitParent_ambient
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (selected : Kakeya.Streamlined.TubeSubfamily fine)
    (index : Fin selected.family.card) :
    (cover.hitParentSubfamily selected).embedding
        (cover.hitParent selected index) =
      cover.parent (selected.embedding index) := by
  let parents := cover.hitParentIndices selected
  let equivalence : Fin parents.card ≃ parents :=
    (parents.orderIsoOfFin rfl).toEquiv
  change
    (parents.orderEmbOfFin rfl)
        (equivalence.symm
          ⟨cover.parent (selected.embedding index), _⟩) =
      cover.parent (selected.embedding index)
  exact congrArg Subtype.val
    (equivalence.apply_symm_apply
      ⟨cover.parent (selected.embedding index), by
        apply Finset.mem_image.mpr
        exact ⟨index, Finset.mem_univ _, rfl⟩⟩)

theorem WZ2PaperPartitioningCover.hitParent_surjective
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (selected : Kakeya.Streamlined.TubeSubfamily fine) :
    Function.Surjective (cover.hitParent selected) := by
  intro parent
  have hparent :
      (cover.hitParentSubfamily selected).embedding parent ∈
        cover.hitParentIndices selected :=
    Finset.orderEmbOfFin_mem
      (cover.hitParentIndices selected) rfl parent
  rcases Finset.mem_image.mp hparent with
    ⟨source, _hsource, hsourceParent⟩
  refine ⟨source, ?_⟩
  apply (cover.hitParentSubfamily selected).embedding.injective
  rw [cover.hitParent_ambient]
  exact hsourceParent

/--
The selected fine family is partitioned by exactly the coarse parents it
still hits.
-/
def WZ2PaperPartitioningCover.restrictToHitParents
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (selected : Kakeya.Streamlined.TubeSubfamily fine) :
    WZ2PaperPartitioningCover
      selected.family (cover.hitParentSubfamily selected).family where
  parent := cover.hitParent selected
  parent_surjective := cover.hitParent_surjective selected
  parent_covers index := by
    rw [selected.tube_eq index,
      (cover.hitParentSubfamily selected).tube_eq,
      cover.hitParent_ambient]
    exact cover.parent_covers (selected.embedding index)
  parent_unique source candidate hcovered := by
    apply (cover.hitParentSubfamily selected).embedding.injective
    rw [cover.hitParent_ambient]
    apply cover.parent_unique (selected.embedding source)
    rw [← selected.tube_eq source,
      ← (cover.hitParentSubfamily selected).tube_eq candidate]
    exact hcovered
  parent_carrier_covers index := by
    rw [selected.tube_eq index,
      (cover.hitParentSubfamily selected).tube_eq,
      cover.hitParent_ambient]
    exact cover.parent_carrier_covers (selected.embedding index)
  literal_parent_unique source candidate hcovered := by
    apply (cover.hitParentSubfamily selected).embedding.injective
    rw [cover.hitParent_ambient]
    apply cover.literal_parent_unique (selected.embedding source)
    rw [← selected.tube_eq source,
      ← (cover.hitParentSubfamily selected).tube_eq candidate]
    exact hcovered
  literal_doubled_fibers_disjoint first second hne := by
    rw [Finset.disjoint_left]
    intro source hfirst hsecond
    have hambientNe :
        (cover.hitParentSubfamily selected).embedding first ≠
          (cover.hitParentSubfamily selected).embedding second :=
      (cover.hitParentSubfamily selected).embedding.injective.ne hne
    have hambientFirst :
        selected.embedding source ∈
          wz2PaperLiteralDoubledFiberIndices fine coarse
            ((cover.hitParentSubfamily selected).embedding first) := by
      simpa [wz2PaperLiteralDoubledFiberIndices,
        selected.tube_eq source,
        (cover.hitParentSubfamily selected).tube_eq first] using hfirst
    have hambientSecond :
        selected.embedding source ∈
          wz2PaperLiteralDoubledFiberIndices fine coarse
            ((cover.hitParentSubfamily selected).embedding second) := by
      simpa [wz2PaperLiteralDoubledFiberIndices,
        selected.tube_eq source,
        (cover.hitParentSubfamily selected).tube_eq second] using hsecond
    exact
      ((Finset.disjoint_left.mp
          (cover.literal_doubled_fibers_disjoint
            ((cover.hitParentSubfamily selected).embedding first)
            ((cover.hitParentSubfamily selected).embedding second)
            hambientNe))
        hambientFirst) hambientSecond
  doubled_fibers_disjoint first second hne := by
    rw [Finset.disjoint_left]
    intro source hfirst hsecond
    have hambientNe :
        (cover.hitParentSubfamily selected).embedding first ≠
          (cover.hitParentSubfamily selected).embedding second := by
      intro heq
      exact hne
        ((cover.hitParentSubfamily selected).embedding.injective heq)
    have hambientFirst :
        selected.embedding source ∈
          wz2PaperDoubledFiberIndices fine coarse
            ((cover.hitParentSubfamily selected).embedding first) := by
      simpa [wz2PaperDoubledFiberIndices, selected.tube_eq source,
        (cover.hitParentSubfamily selected).tube_eq first] using hfirst
    have hambientSecond :
        selected.embedding source ∈
          wz2PaperDoubledFiberIndices fine coarse
            ((cover.hitParentSubfamily selected).embedding second) := by
      simpa [wz2PaperDoubledFiberIndices, selected.tube_eq source,
        (cover.hitParentSubfamily selected).tube_eq second] using hsecond
    exact
      ((Finset.disjoint_left.mp
          (cover.doubled_fibers_disjoint
            ((cover.hitParentSubfamily selected).embedding first)
            ((cover.hitParentSubfamily selected).embedding second)
            hambientNe))
        hambientFirst) hambientSecond

/--
If `selected` is a subfamily of `ambientSelected`, separation of the ambient
hit parents transfers to the hit parents still used by `selected`.
-/
theorem WZ2PaperPartitioningCover.hitParentSeparation_transfer
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPartitioningCover fine coarse)
    (ambientSelected selected :
      Kakeya.Streamlined.TubeSubfamily fine)
    (hsub : ∀ (i : Fin selected.family.card),
      ∃ (j : Fin ambientSelected.family.card),
        selected.embedding i = ambientSelected.embedding j)
    (separationThreshold : ℝ)
    (hsep :
      ∀ (first second :
          Fin (cover.hitParentSubfamily
            ambientSelected).family.card),
        first ≠ second →
          separationThreshold <
            wz1PaperLineDistance
              ((cover.hitParentSubfamily
                ambientSelected).family.tube first)
              ((cover.hitParentSubfamily
                ambientSelected).family.tube second)) :
    ∀ (first second :
        Fin (cover.hitParentSubfamily selected).family.card),
      first ≠ second →
        separationThreshold <
          wz1PaperLineDistance
            ((cover.hitParentSubfamily selected).family.tube first)
            ((cover.hitParentSubfamily selected).family.tube second) := by
  let selectedIndices := cover.hitParentIndices selected
  let ambientIndices := cover.hitParentIndices ambientSelected
  have hsubset : selectedIndices ⊆ ambientIndices := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, _, rfl⟩
    rcases hsub i with ⟨j, hj⟩
    have h :
        cover.parent (selected.embedding i) =
          cover.parent (ambientSelected.embedding j) := by
      rw [hj]
    rw [h]
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  let inclusion :
      Fin (cover.hitParentSubfamily selected).family.card ↪
        Fin (cover.hitParentSubfamily
          ambientSelected).family.card :=
    Kakeya.Streamlined.TubeSubfamily.fromFinsetInclusion
      coarse selectedIndices ambientIndices hsubset
  have h_tube :
      ∀ (i : Fin (cover.hitParentSubfamily selected).family.card),
        (cover.hitParentSubfamily selected).family.tube i =
          (cover.hitParentSubfamily
            ambientSelected).family.tube (inclusion i) := by
    intro i
    have h1 :
        (cover.hitParentSubfamily selected).family.tube i =
          coarse.tube
            ((cover.hitParentSubfamily selected).embedding i) :=
      (cover.hitParentSubfamily selected).tube_eq i
    have h2 :
        (cover.hitParentSubfamily
            ambientSelected).family.tube (inclusion i) =
          coarse.tube
            ((cover.hitParentSubfamily
              ambientSelected).embedding (inclusion i)) :=
      (cover.hitParentSubfamily
        ambientSelected).tube_eq (inclusion i)
    have h3 :
        (cover.hitParentSubfamily
            ambientSelected).embedding (inclusion i) =
          (cover.hitParentSubfamily selected).embedding i :=
      Kakeya.Streamlined.TubeSubfamily.fromFinsetInclusion_ambient
        coarse selectedIndices ambientIndices hsubset i
    rw [h1, h2, h3]
  intro first second hne
  have h_inclusion_ne :
      inclusion first ≠ inclusion second := by
    intro h
    exact hne (inclusion.injective h)
  have h_main :=
    hsep (inclusion first) (inclusion second) h_inclusion_ne
  rw [h_tube first, h_tube second]
  exact h_main

end Kakeya.Assouad

end
