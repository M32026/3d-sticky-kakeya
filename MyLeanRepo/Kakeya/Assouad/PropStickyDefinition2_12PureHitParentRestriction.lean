import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12

/-!
# Pure hit-parent restrictions

Restrict a literal Assouad partitioning cover to a selected fine subfamily
and exactly the coarse parents still hit by the uniquely derived strict
full-fiber parent map.

This construction remains entirely in the public Definition 2.12 model.  It
uses ordinary carriers, strict full fibers, and centered doubled-fiber
disjointness; no assigned or line-distance cover is introduced.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

namespace WZ2PaperOrdinaryIsEssentiallyDistinct

/-- Ordinary essential distinctness is inherited by an indexed subfamily. -/
theorem subfamily
    {rho : ℝ}
    {ambient : Kakeya.Streamlined.TubeFamily rho}
    (distinct : WZ2PaperOrdinaryIsEssentiallyDistinct ambient)
    (selected : WZ2PaperPureTubeSubfamily ambient) :
    WZ2PaperOrdinaryIsEssentiallyDistinct selected.family := by
  intro first second hne
  have hambientNe :
      selected.embedding first ≠ selected.embedding second :=
    selected.embedding.injective.ne hne
  simpa only [selected.tube_eq] using
    distinct (selected.embedding first) (selected.embedding second)
      hambientNe

end WZ2PaperOrdinaryIsEssentiallyDistinct

namespace WZ2PaperPurePartitioningCover

/-- Ambient coarse indices hit by a selected pure fine subfamily. -/
def hitParentIndices
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPurePartitioningCover fine coarse)
    (selected : WZ2PaperPureTubeSubfamily fine) :
    Finset (Fin coarse.card) :=
  Finset.univ.image fun index =>
    cover.parent (selected.embedding index)

/-- The coarse subfamily consisting exactly of the hit literal parents. -/
noncomputable def hitParentSubfamily
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPurePartitioningCover fine coarse)
    (selected : WZ2PaperPureTubeSubfamily fine) :
    WZ2PaperPureTubeSubfamily coarse :=
  WZ2PaperPureTubeSubfamily.fromFinset coarse
    (cover.hitParentIndices selected)

/-- The hit-parent index of one selected source tube. -/
noncomputable def hitParent
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPurePartitioningCover fine coarse)
    (selected : WZ2PaperPureTubeSubfamily fine) :
    Fin selected.family.card →
      Fin (cover.hitParentSubfamily selected).family.card := fun index =>
  let parents := cover.hitParentIndices selected
  let equivalence : Fin parents.card ≃ parents :=
    (parents.orderIsoOfFin rfl).toEquiv
  equivalence.symm
    ⟨cover.parent (selected.embedding index), by
      exact Finset.mem_image.mpr
        ⟨index, Finset.mem_univ index, rfl⟩⟩

@[simp] theorem hitParent_ambient
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPurePartitioningCover fine coarse)
    (selected : WZ2PaperPureTubeSubfamily fine)
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
        exact Finset.mem_image.mpr
          ⟨index, Finset.mem_univ index, rfl⟩⟩)

theorem hitParent_surjective
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPurePartitioningCover fine coarse)
    (selected : WZ2PaperPureTubeSubfamily fine) :
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

theorem hitParentSubfamily_nonempty
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPurePartitioningCover fine coarse)
    (selected : WZ2PaperPureTubeSubfamily fine)
    (hselected : selected.family.Nonempty) :
    (cover.hitParentSubfamily selected).family.Nonempty := by
  let source : Fin selected.family.card := ⟨0, hselected⟩
  exact Fin.pos_iff_nonempty.mpr
    ⟨cover.hitParent selected source⟩

/--
Restrict a pure partitioning cover to a selected fine family and exactly its
hit strict-fiber parents.
-/
noncomputable def restrictToHitParents
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPurePartitioningCover fine coarse)
    (selected : WZ2PaperPureTubeSubfamily fine) :
    WZ2PaperPurePartitioningCover
      selected.family
      (cover.hitParentSubfamily selected).family where
  covers source := by
    refine ⟨cover.hitParent selected source, ?_⟩
    rw [mem_wz2PaperOrdinaryFullFiberIndices_iff]
    rw [selected.tube_eq,
      (cover.hitParentSubfamily selected).tube_eq,
      cover.hitParent_ambient]
    exact
      (mem_wz2PaperOrdinaryFullFiberIndices_iff
        (cover.parent (selected.embedding source))
        (selected.embedding source)).mp
        (cover.parent_mem_fullFiber (selected.embedding source))
  doubled_fibers_disjoint first second hne := by
    rw [Finset.disjoint_left]
    intro source hfirst hsecond
    have hambientNe :
        (cover.hitParentSubfamily selected).embedding first ≠
          (cover.hitParentSubfamily selected).embedding second :=
      (cover.hitParentSubfamily selected).embedding.injective.ne hne
    have hambientFirst :
        selected.embedding source ∈
          wz2PaperOrdinaryDilatedFiberIndices
            2 fine coarse
            ((cover.hitParentSubfamily selected).embedding first) := by
      simpa only [
        mem_wz2PaperOrdinaryDilatedFiberIndices_iff,
        selected.tube_eq,
        (cover.hitParentSubfamily selected).tube_eq
      ] using hfirst
    have hambientSecond :
        selected.embedding source ∈
          wz2PaperOrdinaryDilatedFiberIndices
            2 fine coarse
            ((cover.hitParentSubfamily selected).embedding second) := by
      simpa only [
        mem_wz2PaperOrdinaryDilatedFiberIndices_iff,
        selected.tube_eq,
        (cover.hitParentSubfamily selected).tube_eq
      ] using hsecond
    exact
      ((Finset.disjoint_left.mp
          (cover.doubled_fibers_disjoint
            ((cover.hitParentSubfamily selected).embedding first)
            ((cover.hitParentSubfamily selected).embedding second)
            hambientNe))
        hambientFirst) hambientSecond

theorem restrictToHitParents_fullFiberIndices_eq
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPurePartitioningCover fine coarse)
    (hrho : 0 ≤ rho)
    (selected : WZ2PaperPureTubeSubfamily fine)
    (parent :
      Fin (cover.hitParentSubfamily selected).family.card) :
    wz2PaperOrdinaryFullFiberIndices
        selected.family
        (cover.hitParentSubfamily selected).family parent =
      Finset.univ.filter fun source =>
        cover.parent (selected.embedding source) =
          (cover.hitParentSubfamily selected).embedding parent := by
  ext source
  simp only [
    mem_wz2PaperOrdinaryFullFiberIndices_iff,
    selected.tube_eq,
    (cover.hitParentSubfamily selected).tube_eq,
    Finset.mem_filter,
    Finset.mem_univ,
    true_and
  ]
  simpa only [mem_wz2PaperOrdinaryFullFiberIndices_iff] using
    (cover.mem_fullFiber_iff_parent_eq
      hrho
      ((cover.hitParentSubfamily selected).embedding parent)
      (selected.embedding source))

/--
Uniform selected degrees of the derived ambient parent map are exactly
uniform strict full-fiber cardinalities of the pure hit-parent restriction.
-/
theorem restrictToHitParents_fullFiber_uniform_of_subfamily
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (cover : WZ2PaperPurePartitioningCover fine coarse)
    (hrho : 0 ≤ rho)
    (selected : WZ2PaperPureTubeSubfamily fine)
    (C : ENNReal)
    (degreeUniform :
      ∀ first second : Fin coarse.card,
        0 <
            ((Finset.univ :
              Finset (Fin selected.family.card)).filter fun source =>
                cover.parent (selected.embedding source) = first).card →
        0 <
            ((Finset.univ :
              Finset (Fin selected.family.card)).filter fun source =>
                cover.parent (selected.embedding source) = second).card →
        (((Finset.univ :
          Finset (Fin selected.family.card)).filter fun source =>
            cover.parent (selected.embedding source) = first).card :
          ENNReal) ≤
          C *
            (((Finset.univ :
              Finset (Fin selected.family.card)).filter fun source =>
                cover.parent (selected.embedding source) = second).card :
              ENNReal)) :
    WZ2PaperPureFullFibersAreCUniform
      selected.family
      (cover.hitParentSubfamily selected).family C := by
  intro first second
  rcases cover.hitParent_surjective selected first with
    ⟨firstSource, hfirstSource⟩
  rcases cover.hitParent_surjective selected second with
    ⟨secondSource, hsecondSource⟩
  have hfirstAmbient :
      cover.parent (selected.embedding firstSource) =
        (cover.hitParentSubfamily selected).embedding first := by
    rw [← cover.hitParent_ambient selected firstSource, hfirstSource]
  have hsecondAmbient :
      cover.parent (selected.embedding secondSource) =
        (cover.hitParentSubfamily selected).embedding second := by
    rw [← cover.hitParent_ambient selected secondSource, hsecondSource]
  have hfirstPositive :
      0 <
        ((Finset.univ :
          Finset (Fin selected.family.card)).filter fun source =>
            cover.parent (selected.embedding source) =
              (cover.hitParentSubfamily selected).embedding first).card :=
    Finset.card_pos.mpr
      ⟨firstSource,
        Finset.mem_filter.mpr
          ⟨Finset.mem_univ firstSource, hfirstAmbient⟩⟩
  have hsecondPositive :
      0 <
        ((Finset.univ :
          Finset (Fin selected.family.card)).filter fun source =>
            cover.parent (selected.embedding source) =
              (cover.hitParentSubfamily selected).embedding second).card :=
    Finset.card_pos.mpr
      ⟨secondSource,
        Finset.mem_filter.mpr
          ⟨Finset.mem_univ secondSource, hsecondAmbient⟩⟩
  rw [
    wz2PaperOrdinaryFullFiberCount,
    wz2PaperOrdinaryFullFiberCount,
    cover.restrictToHitParents_fullFiberIndices_eq hrho selected first,
    cover.restrictToHitParents_fullFiberIndices_eq hrho selected second
  ]
  exact
    degreeUniform
      ((cover.hitParentSubfamily selected).embedding first)
      ((cover.hitParentSubfamily selected).embedding second)
      hfirstPositive hsecondPositive

end WZ2PaperPurePartitioningCover

end Kakeya.Assouad

end
