import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62InsertedCWA
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.WeightedGraphSelection

/-!
# Proposition 6.2 metric parents: one upper partitioning level

At one old scale above `rho`, modified ancestors contain their assigned
metric parents.  Color the graph in which two modified ancestors conflict
when their centered doubled fibers have a common child.  A monochromatic
restriction is then a literal ordinary partitioning cover, and its strict
fibers are exactly the owner classes.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

noncomputable def pureWZ2Prop62IdentitySubfamily
    {rho : ℝ}
    (family : Kakeya.Streamlined.TubeFamily rho) :
    WZ2PaperPureTubeSubfamily family where
  family := family
  embedding := Function.Embedding.refl _
  tube_eq _ := rfl

structure PureWZ2Prop62UpperScaleInput
    {rho upper : ℝ}
    (children : Kakeya.Streamlined.TubeFamily rho)
    (parents : Kakeya.Streamlined.TubeFamily upper)
    (degree : ℕ) where
  rho_pos : 0 < rho
  upper_pos : 0 < upper
  owner : Fin children.card → Fin parents.card
  owner_surjective : Function.Surjective owner
  owner_containment :
    ∀ child,
      (children.tube child).carrier ⊆
        (parents.tube (owner child)).carrier
  conflict_degree :
    ∀ fixed,
      (Finset.univ.filter fun other =>
        other ≠ fixed ∧
          (wz2PaperOrdinaryDilatedFiberIndices
              2 children parents fixed ∩
            wz2PaperOrdinaryDilatedFiberIndices
              2 children parents other).Nonempty).card ≤
        degree

namespace PureWZ2Prop62UpperScaleInput

variable
    {rho upper : ℝ}
    {children : Kakeya.Streamlined.TubeFamily rho}
    {parents : Kakeya.Streamlined.TubeFamily upper}
    {degree : ℕ}
    (input :
      PureWZ2Prop62UpperScaleInput children parents degree)

structure ColoringData
    (input :
      PureWZ2Prop62UpperScaleInput children parents degree) where
  color : Fin parents.card → Fin (degree + 1)
  proper :
    ∀ first second, first ≠ second →
      (wz2PaperOrdinaryDilatedFiberIndices
          2 children parents first ∩
        wz2PaperOrdinaryDilatedFiberIndices
          2 children parents second).Nonempty →
      color first ≠ color second

theorem exists_coloring :
    Nonempty (ColoringData input) := by
  let conflict : Fin parents.card → Fin parents.card → Prop :=
    fun first second =>
      second ≠ first ∧
        (wz2PaperOrdinaryDilatedFiberIndices
            2 children parents first ∩
          wz2PaperOrdinaryDilatedFiberIndices
            2 children parents second).Nonempty
  have symmetric :
      ∀ first second, conflict first second →
        conflict second first := by
    intro first second hconflict
    exact
      ⟨hconflict.1.symm, by
        simpa [Finset.inter_comm] using hconflict.2⟩
  have irreflexive :
      ∀ parent, ¬ conflict parent parent := by
    intro parent hconflict
    exact hconflict.1 rfl
  rcases
      pureWZ2_greedy_proper_coloring
        (D := degree) symmetric irreflexive
        (fun fixed => by
          rw [Finset.filter_congr_decidable]
          exact input.conflict_degree fixed)
    with ⟨color, proper⟩
  exact
    ⟨{
      color := color
      proper := by
        intro first second hne hoverlap
        exact proper first second ⟨hne.symm, hoverlap⟩
    }⟩

def childColor
    (coloring : ColoringData input)
    (child : Fin children.card) :
    Fin (degree + 1) :=
  coloring.color (input.owner child)

structure MonochromaticCoverData
    (coloring : ColoringData input)
    (selected : WZ2PaperPureTubeSubfamily children) where
  selectedParents : WZ2PaperPureTubeSubfamily parents
  cover :
    WZ2PaperPurePartitioningCover
      selected.family selectedParents.family
  parent_owner_eq :
    ∀ child,
      selectedParents.embedding (cover.parent child) =
        input.owner (selected.embedding child)
  fullFiberIndices_eq_owner :
    ∀ parent,
      wz2PaperOrdinaryFullFiberIndices
          selected.family selectedParents.family parent =
        Finset.univ.filter fun child =>
          input.owner (selected.embedding child) =
            selectedParents.embedding parent
  full_fiber_nonempty :
    ∀ parent,
      (wz2PaperOrdinaryFullFiberIndices
        selected.family selectedParents.family parent).Nonempty

theorem ColoringData.monochromatic_cover
    (coloring : ColoringData input)
    (selected : WZ2PaperPureTubeSubfamily children)
    (selectedColor : Fin (degree + 1))
    (monochromatic :
      ∀ child,
        input.childColor coloring (selected.embedding child) =
          selectedColor) :
    Nonempty (input.MonochromaticCoverData coloring selected) := by
  let owner : Fin selected.family.card → Fin parents.card :=
    fun child => input.owner (selected.embedding child)
  let parentIndices : Finset (Fin parents.card) :=
    Finset.univ.image owner
  let selectedParents :=
    WZ2PaperPureTubeSubfamily.fromFinset parents parentIndices
  let parentEquiv : Fin parentIndices.card ≃ parentIndices :=
    (parentIndices.orderIsoOfFin rfl).toEquiv
  have ownerMem :
      ∀ child, owner child ∈ parentIndices := by
    intro child
    exact Finset.mem_image.mpr
      ⟨child, Finset.mem_univ child, rfl⟩
  let selectedParent :
      Fin selected.family.card →
        Fin selectedParents.family.card :=
    fun child =>
      parentEquiv.symm ⟨owner child, ownerMem child⟩
  have selectedParentAmbient :
      ∀ child,
        selectedParents.embedding (selectedParent child) =
          owner child := by
    intro child
    exact congrArg Subtype.val
      (parentEquiv.apply_symm_apply
        ⟨owner child, ownerMem child⟩)
  have selectedParentContainment :
      ∀ child,
        (selected.family.tube child).carrier ⊆
          (selectedParents.family.tube
            (selectedParent child)).carrier := by
    intro child
    rw [selected.tube_eq, selectedParents.tube_eq,
      selectedParentAmbient]
    exact input.owner_containment (selected.embedding child)
  have selectedParentColor :
      ∀ parent,
        coloring.color (selectedParents.embedding parent) =
          selectedColor := by
    intro parent
    have hparent :
        selectedParents.embedding parent ∈ parentIndices :=
      Finset.orderEmbOfFin_mem parentIndices rfl parent
    rcases Finset.mem_image.mp hparent with
      ⟨child, _, hchild⟩
    have hmono := monochromatic child
    dsimp only [childColor] at hmono
    change coloring.color (owner child) = selectedColor at hmono
    rwa [hchild] at hmono
  have doubledDisjoint :
      ∀ first second : Fin selectedParents.family.card,
        first ≠ second →
        Disjoint
          (wz2PaperOrdinaryDilatedFiberIndices
            2 selected.family selectedParents.family first)
          (wz2PaperOrdinaryDilatedFiberIndices
            2 selected.family selectedParents.family second) := by
    intro first second hne
    rw [Finset.disjoint_left]
    intro child hfirst hsecond
    have ambientFirst :
        selected.embedding child ∈
          wz2PaperOrdinaryDilatedFiberIndices
            2 children parents
            (selectedParents.embedding first) := by
      simpa only [
        mem_wz2PaperOrdinaryDilatedFiberIndices_iff,
        selected.tube_eq, selectedParents.tube_eq
      ] using hfirst
    have ambientSecond :
        selected.embedding child ∈
          wz2PaperOrdinaryDilatedFiberIndices
            2 children parents
            (selectedParents.embedding second) := by
      simpa only [
        mem_wz2PaperOrdinaryDilatedFiberIndices_iff,
        selected.tube_eq, selectedParents.tube_eq
      ] using hsecond
    have ambientNe :=
      selectedParents.embedding.injective.ne hne
    have colorNe :=
      coloring.proper
        (selectedParents.embedding first)
        (selectedParents.embedding second)
        ambientNe
        ⟨selected.embedding child,
          Finset.mem_inter.mpr
            ⟨ambientFirst, ambientSecond⟩⟩
    exact colorNe
      ((selectedParentColor first).trans
        (selectedParentColor second).symm)
  let cover :
      WZ2PaperPurePartitioningCover
        selected.family selectedParents.family :=
    {
      covers := fun child =>
        ⟨selectedParent child,
          (mem_wz2PaperOrdinaryFullFiberIndices_iff
            (selectedParent child) child).mpr
            (selectedParentContainment child)⟩
      doubled_fibers_disjoint := doubledDisjoint
    }
  have fullFiberIndices :
      ∀ parent,
        wz2PaperOrdinaryFullFiberIndices
            selected.family selectedParents.family parent =
          Finset.univ.filter fun child =>
            owner child = selectedParents.embedding parent := by
    intro parent
    ext child
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      mem_wz2PaperOrdinaryFullFiberIndices_iff]
    constructor
    · intro strictContainment
      by_contra howner
      have ownerDoubled :
          selected.embedding child ∈
            wz2PaperOrdinaryDilatedFiberIndices
              2 children parents (owner child) := by
        rw [mem_wz2PaperOrdinaryDilatedFiberIndices_iff]
        exact
          (input.owner_containment (selected.embedding child)).trans
            (wz2_paper_carrier_subset_centeredDilatedTwo
              (parents.tube (owner child)) input.upper_pos.le)
      have candidateDoubled :
          selected.embedding child ∈
            wz2PaperOrdinaryDilatedFiberIndices
              2 children parents
              (selectedParents.embedding parent) := by
        rw [mem_wz2PaperOrdinaryDilatedFiberIndices_iff]
        simpa only [selected.tube_eq, selectedParents.tube_eq] using
          strictContainment.trans
            (wz2_paper_carrier_subset_centeredDilatedTwo
              (selectedParents.family.tube parent) input.upper_pos.le)
      have colorNe :=
        coloring.proper
          (owner child)
          (selectedParents.embedding parent)
          howner
          ⟨selected.embedding child,
            Finset.mem_inter.mpr
              ⟨ownerDoubled, candidateDoubled⟩⟩
      have ownerColor :
          coloring.color (owner child) = selectedColor := by
        have hmono := monochromatic child
        exact hmono
      exact colorNe
        (ownerColor.trans (selectedParentColor parent).symm)
    · intro howner
      rw [selected.tube_eq, selectedParents.tube_eq, ← howner]
      exact input.owner_containment (selected.embedding child)
  have fullFiberNonempty :
      ∀ parent,
        (wz2PaperOrdinaryFullFiberIndices
          selected.family selectedParents.family parent).Nonempty := by
    intro parent
    have hparent :
        selectedParents.embedding parent ∈ parentIndices :=
      Finset.orderEmbOfFin_mem parentIndices rfl parent
    rcases Finset.mem_image.mp hparent with
      ⟨child, _, hchild⟩
    exact
      ⟨child, by
        rw [fullFiberIndices parent]
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ child, hchild⟩⟩
  have parentOwner :
      ∀ child,
        selectedParents.embedding (cover.parent child) =
          owner child := by
    intro child
    have hmember := cover.parent_mem_fullFiber child
    rw [fullFiberIndices (cover.parent child)] at hmember
    exact (Finset.mem_filter.mp hmember).2.symm
  exact
    ⟨{
      selectedParents := selectedParents
      cover := cover
      parent_owner_eq := parentOwner
      fullFiberIndices_eq_owner := fullFiberIndices
      full_fiber_nonempty := fullFiberNonempty
    }⟩

theorem ColoringData.full_monochromatic_cover
    (coloring : ColoringData input)
    (selectedColor : Fin (degree + 1))
    (monochromatic :
      ∀ child,
        input.childColor coloring child = selectedColor) :
    Nonempty
      (input.MonochromaticCoverData coloring
        (pureWZ2Prop62IdentitySubfamily children)) := by
  apply coloring.monochromatic_cover
  intro child
  exact monochromatic child

namespace MonochromaticCoverData

noncomputable def toPureScaleData
    {rho upper : ℝ}
    {children : Kakeya.Streamlined.TubeFamily rho}
    {parents : Kakeya.Streamlined.TubeFamily upper}
    {degree : ℕ}
    {input :
      PureWZ2Prop62UpperScaleInput children parents degree}
    {coloring : ColoringData input}
    {selected : WZ2PaperPureTubeSubfamily children}
    (data : input.MonochromaticCoverData coloring selected)
    (coverConstant bodyConstant : ENNReal)
    (fullFiberUniform :
      WZ2PaperPureFullFibersAreCUniform
        selected.family data.selectedParents.family coverConstant)
    (normalization :
      ∀ parent : Fin data.selectedParents.family.card,
        WZ2PaperAssouadUnitRescalingData
          (data.selectedParents.family.tube parent))
    (fiberCWA :
      ∀ parent : Fin data.selectedParents.family.card,
        WZ2PaperBodyConvexWolffBound
          (wz2PaperPureUnitRescaledFullFiberBodyFamily
            (fine := selected.family)
            (coarse := data.selectedParents.family)
            parent (normalization parent))
          bodyConstant) :
    WZ2PaperPureScaleCoverData
      selected.family upper (max coverConstant bodyConstant) where
  delta_pos := input.rho_pos
  rho_pos := input.upper_pos
  coarse := data.selectedParents.family
  cover := data.cover
  full_fiber_uniform first second :=
    (fullFiberUniform first second).trans <| by
      gcongr
      exact le_max_left _ _
  rescaledFiber parent :=
    ⟨{
      normalization := normalization parent
      convex_wolff := by
        intro convexSet convex
        exact
          (fiberCWA parent convexSet convex).trans <| by
            gcongr
            exact le_max_right coverConstant bodyConstant
    }⟩

end MonochromaticCoverData

end PureWZ2Prop62UpperScaleInput

end Kakeya.Assouad

end
