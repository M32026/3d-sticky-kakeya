import MyLeanRepo.Kakeya.Streamlined.DividingScales.ConditionalCellRestriction
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.FullContainmentBranching

/-!
# Uniform cover systems on conditional branches

Restrict every independently chosen paper-grid cover to one finite
conditional parent cell.  The selected coarse subfamilies remain essentially
distinct, ambient parent identities are preserved, and every restricted cover
has the original common uniformity constant.

This packages the combinatorial closure theorem into the existing local
uniform-structure interface, so all closed geometric and Frostman-transfer
modules can be reused on a recursive branch.
-/

noncomputable section

namespace Kakeya.Streamlined

/-- All restricted paper-grid covers on one conditional branch. -/
structure ConditionalBranchSystem
    {depth : ℕ} {delta A C : ℝ} {F : TubeFamily delta}
    {hdelta_le_one : delta ≤ 1}
    (U : ConditionallyUniformLocalDilatedDiscreteUniformTubeStructure
      depth (A := A) (C := C) F hdelta_le_one)
    {m : ℕ} (scale : Fin m → UniformScaleIndex delta)
    (parent : Fin m → ℕ) where
  selectedCoarse : ∀ r, TubeSubfamily (U.coarse r)
  restrictedCover : ∀ r,
    LocalDilatedTubeCover A C
      (TubeSubfamily.fromFinset F
        (conditionalParentCell U.coarse U.cover scale parent)).family
      (selectedCoarse r).family
  coarse_distinct :
    ∀ r, (selectedCoarse r).family.IsEssentiallyDistinct
  parent_compatible : ∀ r i,
    (selectedCoarse r).embedding ((restrictedCover r).parent i) =
      (U.cover r).parent
        ((TubeSubfamily.fromFinset F
          (conditionalParentCell U.coarse U.cover
            scale parent)).embedding i)
  selectedCoarse_image : ∀ r,
    Finset.image (selectedCoarse r).embedding Finset.univ =
      Finset.image (U.cover r).parent
        (conditionalParentCell U.coarse U.cover scale parent)
  assignedUniform : ∀ r,
    (restrictedCover r).toDilatedTubeCover.toFactoring.FibersAreCUniform
      U.assignedUniformity

namespace ConditionalBranchSystem

/-- View a conditional branch as a complete local uniform grid structure. -/
def toLocal
    {depth : ℕ} {delta A C : ℝ} {F : TubeFamily delta}
    {hdelta_le_one : delta ≤ 1}
    {U : ConditionallyUniformLocalDilatedDiscreteUniformTubeStructure
      depth (A := A) (C := C) F hdelta_le_one}
    {m : ℕ} {scale : Fin m → UniformScaleIndex delta}
    {parent : Fin m → ℕ}
    (B : ConditionalBranchSystem U scale parent) :
    LocalDilatedDiscreteUniformTubeStructure
      (A := A) (C := C)
      (TubeSubfamily.fromFinset F
        (conditionalParentCell U.coarse U.cover scale parent)).family
      hdelta_le_one where
  coarse r := (B.selectedCoarse r).family
  cover := B.restrictedCover
  coarse_distinct := B.coarse_distinct
  assignedUniformity := U.assignedUniformity
  one_le_assignedUniformity := U.one_le_assignedUniformity
  assignedUniformity_ne_top := U.assignedUniformity_ne_top
  assignedUniform := B.assignedUniform
  uniformity :=
    RandomTranslation.fullContainmentBranchingLoss
        A U.coverDilation_one *
      U.assignedUniformity
  assignedUniformity_le_uniformity := by
    calc
      U.assignedUniformity = 1 * U.assignedUniformity := by simp
      _ ≤
          RandomTranslation.fullContainmentBranchingLoss
              A U.coverDilation_one *
            U.assignedUniformity := by
        gcongr
        exact
          RandomTranslation.one_le_fullContainmentBranchingLoss
            A U.coverDilation_one
  one_le_uniformity := by
    simpa using
      mul_le_mul'
        (RandomTranslation.one_le_fullContainmentBranchingLoss
          A U.coverDilation_one)
        U.one_le_assignedUniformity
  uniformity_ne_top :=
    ENNReal.mul_ne_top
      (RandomTranslation.fullContainmentBranchingLoss_ne_top
        A U.coverDilation_one)
      U.assignedUniformity_ne_top
  uniform r :=
    (B.restrictedCover r).toDilatedTubeCover
      |>.fullContainmentFibersAreCUniform_of_ownerCount
        (RandomTranslation.one_le_fullContainmentBranchingLoss
          A U.coverDilation_one)
        (B.assignedUniform r)
        (fun selectedParent =>
          RandomTranslation.fullContainmentOwnerCount_le_branchingLoss
            A U.coverDilation_one
            (U.delta_pos.trans_le
              (uniformScale delta hdelta_le_one r).property.1)
            (uniformScale delta hdelta_le_one r).property.2
            (B.coarse_distinct r)
            (B.restrictedCover r).toDilatedTubeCover
            selectedParent)

@[simp] lemma toLocal_uniformity
    {depth : ℕ} {delta A C : ℝ} {F : TubeFamily delta}
    {hdelta_le_one : delta ≤ 1}
    {U : ConditionallyUniformLocalDilatedDiscreteUniformTubeStructure
      depth (A := A) (C := C) F hdelta_le_one}
    {m : ℕ} {scale : Fin m → UniformScaleIndex delta}
    {parent : Fin m → ℕ}
    (B : ConditionalBranchSystem U scale parent) :
    B.toLocal.uniformity =
      RandomTranslation.fullContainmentBranchingLoss
          A U.coverDilation_one *
        U.assignedUniformity :=
  rfl

end ConditionalBranchSystem

namespace ConditionallyUniformLocalDilatedDiscreteUniformTubeStructure

variable {depth : ℕ} {delta A C : ℝ} {F : TubeFamily delta}
variable {hdelta_le_one : delta ≤ 1}
variable (U : ConditionallyUniformLocalDilatedDiscreteUniformTubeStructure
  depth (A := A) (C := C) F hdelta_le_one)

/-- Construct the full restricted grid structure on a conditional branch. -/
lemma exists_conditionalBranchSystem
    {m : ℕ} (hm : m ≤ depth)
    (scale : Fin m → UniformScaleIndex delta)
    (parent : Fin m → ℕ) :
    Nonempty (ConditionalBranchSystem U scale parent) := by
  have hmain : ∀ r : UniformScaleIndex delta,
      ∃ R : TubeSubfamily (U.coarse r),
        R.family.IsEssentiallyDistinct ∧
        ∃ Q : LocalDilatedTubeCover A C
            (TubeSubfamily.fromFinset F
              (conditionalParentCell U.coarse U.cover
                scale parent)).family
            R.family,
          (∀ i, R.embedding (Q.parent i) =
            (U.cover r).parent
              ((TubeSubfamily.fromFinset F
                (conditionalParentCell U.coarse U.cover
                  scale parent)).embedding i)) ∧
          Q.toDilatedTubeCover.toFactoring.FibersAreCUniform
            U.assignedUniformity := by
    intro r
    exact U.exists_restrictedCover_conditionalCell_isCUniform
      hm scale parent r
  choose R hR Q hcompat huniform using hmain
  exact ⟨{
    selectedCoarse := R
    restrictedCover := Q
    coarse_distinct := hR
    parent_compatible := hcompat
    selectedCoarse_image := by
      intro r
      ext j
      constructor
      · intro hj
        rcases Finset.mem_image.mp hj with ⟨j', _hj', rfl⟩
        rcases (Q r).parent_surjective j' with ⟨i, hi⟩
        have hi_cell :
            (TubeSubfamily.fromFinset F
              (conditionalParentCell U.coarse U.cover
                scale parent)).embedding i ∈
              conditionalParentCell U.coarse U.cover
                scale parent :=
          Finset.orderEmbOfFin_mem
            (conditionalParentCell U.coarse U.cover
              scale parent) rfl i
        refine Finset.mem_image.mpr ⟨_, hi_cell, ?_⟩
        rw [← hcompat r i, hi]
      · intro hj
        rcases Finset.mem_image.mp hj with ⟨original, horiginal, hparent⟩
        have horiginal_image :
            original ∈
              Finset.image
                (TubeSubfamily.fromFinset F
                  (conditionalParentCell U.coarse U.cover
                    scale parent)).embedding Finset.univ := by
          change original ∈
            Finset.image
              ((conditionalParentCell U.coarse U.cover
                scale parent).orderEmbOfFin rfl) Finset.univ
          rw [Finset.image_orderEmbOfFin_univ
            (conditionalParentCell U.coarse U.cover scale parent) rfl]
          exact horiginal
        rcases Finset.mem_image.mp horiginal_image with
          ⟨i, _hi, hi_original⟩
        refine Finset.mem_image.mpr
          ⟨(Q r).parent i, Finset.mem_univ _, ?_⟩
        rw [hcompat r i, hi_original, hparent]
    assignedUniform := huniform
  }⟩

end ConditionallyUniformLocalDilatedDiscreteUniformTubeStructure

end Kakeya.Streamlined
