import MyLeanRepo.Kakeya.Streamlined.DividingScales.ConditionalFactors
import MyLeanRepo.Kakeya.Streamlined.DividingScales.JointUniformLocalCover

/-!
# Joint uniformity on a conditional branch

Fixing `m` historical parent coordinates and then taking a pair cell for two
new endpoint covers gives an ambient `(m + 2)`-coordinate conditional cell.
Consequently finite-depth conditional uniformity induces pair-cell uniformity
on every branch with `m + 1 ≤ depth`.

This is the recursive closure used by Section 7: the first split uses ambient
pair cells, the second uses triple cells after one historical coordinate, and
so on.  No transition between the independent covers is chosen.
-/

noncomputable section

namespace Kakeya.Streamlined

namespace ConditionalBranchSystem

variable {depth : ℕ} {delta A C : ℝ} {F : TubeFamily delta}
variable {hdelta_le_one : delta ≤ 1}
variable {U : ConditionallyUniformLocalDilatedDiscreteUniformTubeStructure
  depth (A := A) (C := C) F hdelta_le_one}
variable {m : ℕ} {scale : Fin m → UniformScaleIndex delta}
variable {parent : Fin m → ℕ}

/--
The ambient image of one branch-local pair cell is the conditional cell
obtained by appending the two endpoint parent coordinates.
-/
lemma image_jointParentCell_eq_conditionalParentCell
    (B : ConditionalBranchSystem U scale parent)
    (r s : UniformScaleIndex delta)
    (j : Fin (B.selectedCoarse r).family.card)
    (k : Fin (B.selectedCoarse s).family.card) :
    let S := TubeSubfamily.fromFinset F
      (conditionalParentCell U.coarse U.cover scale parent)
    let scale' :=
      appendConditionalScale (appendConditionalScale scale r) s
    let parent' :=
      appendConditionalParent
        (appendConditionalParent parent
          ((B.selectedCoarse r).embedding j).val)
        ((B.selectedCoarse s).embedding k).val
    Finset.image S.embedding
        (jointParentCell
          (fun q => (B.selectedCoarse q).family)
          B.restrictedCover r s j k) =
      conditionalParentCell U.coarse U.cover scale' parent' := by
  classical
  let I := conditionalParentCell U.coarse U.cover scale parent
  let S := TubeSubfamily.fromFinset F I
  let scaleR := appendConditionalScale scale r
  let parentJ := appendConditionalParent parent
    ((B.selectedCoarse r).embedding j).val
  let scale' := appendConditionalScale scaleR s
  let parent' := appendConditionalParent parentJ
    ((B.selectedCoarse s).embedding k).val
  dsimp only
  ext original
  constructor
  · intro horiginal
    rcases Finset.mem_image.mp horiginal with
      ⟨i, hi, rfl⟩
    have hpair :
        (B.restrictedCover r).parent i = j ∧
          (B.restrictedCover s).parent i = k :=
      (mem_jointParentCell_iff
        (fun q => (B.selectedCoarse q).family)
        B.restrictedCover r s j k i).mp hi
    rw [mem_conditionalParentCell_iff]
    intro t
    refine Fin.lastCases ?_ (fun oldR => ?_) t
    · rw [appendConditionalScale_last,
        appendConditionalParent_last]
      have hcompat := B.parent_compatible s i
      rw [hpair.2] at hcompat
      exact congrArg Fin.val hcompat.symm
    · refine Fin.lastCases ?_ (fun old => ?_) oldR
      · rw [appendConditionalScale_castSucc,
          appendConditionalParent_castSucc,
          appendConditionalScale_last,
          appendConditionalParent_last]
        have hcompat := B.parent_compatible r i
        rw [hpair.1] at hcompat
        exact congrArg Fin.val hcompat.symm
      · have hiI : S.embedding i ∈ I :=
          Finset.orderEmbOfFin_mem I rfl i
        have hold :=
          (mem_conditionalParentCell_iff
            U.coarse U.cover scale parent (S.embedding i)).mp hiI old
        rw [appendConditionalScale_castSucc,
          appendConditionalParent_castSucc,
          appendConditionalScale_castSucc,
          appendConditionalParent_castSucc]
        exact hold
  · intro horiginal
    have hall :=
      (mem_conditionalParentCell_iff
        U.coarse U.cover scale' parent' original).mp horiginal
    have hold : original ∈ I := by
      rw [mem_conditionalParentCell_iff]
      intro t
      have h := hall t.castSucc.castSucc
      dsimp only [scale', parent', scaleR, parentJ] at h
      rw [appendConditionalScale_castSucc,
        appendConditionalParent_castSucc,
        appendConditionalScale_castSucc,
        appendConditionalParent_castSucc] at h
      exact h
    have himage :
        original ∈ Finset.image S.embedding Finset.univ := by
      change original ∈
        Finset.image (I.orderEmbOfFin rfl) Finset.univ
      rw [Finset.image_orderEmbOfFin_univ I rfl]
      exact hold
    rcases Finset.mem_image.mp himage with
      ⟨i, _hi, hi_original⟩
    refine Finset.mem_image.mpr ⟨i, ?_, hi_original⟩
    rw [mem_jointParentCell_iff]
    constructor
    · apply (B.selectedCoarse r).embedding.injective
      rw [B.parent_compatible r i, hi_original]
      have h := hall (Fin.last m).castSucc
      dsimp only [scale', parent', scaleR, parentJ] at h
      apply Fin.ext
      rw [appendConditionalScale_castSucc,
        appendConditionalParent_castSucc,
        appendConditionalScale_last,
        appendConditionalParent_last] at h
      exact h
    · apply (B.selectedCoarse s).embedding.injective
      rw [B.parent_compatible s i, hi_original]
      have h := hall (Fin.last (m + 1))
      dsimp only [scale', parent', scaleR, parentJ] at h
      apply Fin.ext
      rw [appendConditionalScale_last,
        appendConditionalParent_last] at h
      exact h

/-- Cardinality form of the branch pair-cell identification. -/
lemma jointParentCell_card_eq_conditionalParentCell_card
    (B : ConditionalBranchSystem U scale parent)
    (r s : UniformScaleIndex delta)
    (j : Fin (B.selectedCoarse r).family.card)
    (k : Fin (B.selectedCoarse s).family.card) :
    let scale' :=
      appendConditionalScale (appendConditionalScale scale r) s
    let parent' :=
      appendConditionalParent
        (appendConditionalParent parent
          ((B.selectedCoarse r).embedding j).val)
        ((B.selectedCoarse s).embedding k).val
    (jointParentCell
        (fun q => (B.selectedCoarse q).family)
        B.restrictedCover r s j k).card =
      (conditionalParentCell U.coarse U.cover scale' parent').card := by
  classical
  let S := TubeSubfamily.fromFinset F
    (conditionalParentCell U.coarse U.cover scale parent)
  have hcard :=
    Finset.card_image_of_injective
      (jointParentCell
        (fun q => (B.selectedCoarse q).family)
        B.restrictedCover r s j k)
      S.embedding.injective
  rw [B.image_jointParentCell_eq_conditionalParentCell r s j k] at hcard
  exact hcard.symm

/--
View one conditional branch as a joint-uniform local grid structure.
-/
def toJoint
    (B : ConditionalBranchSystem U scale parent)
    (hdepth : m + 1 ≤ depth) :
    JointUniformLocalDilatedDiscreteUniformTubeStructure
      (A := A) (C := C)
      (TubeSubfamily.fromFinset F
        (conditionalParentCell U.coarse U.cover scale parent)).family
      hdelta_le_one where
  toLocalDilatedDiscreteUniformTubeStructure := B.toLocal
  jointUniform r s j k j' k' hjk hjk' := by
    let scale' :=
      appendConditionalScale (appendConditionalScale scale r) s
    let parentJK :=
      appendConditionalParent
        (appendConditionalParent parent
          ((B.selectedCoarse r).embedding j).val)
        ((B.selectedCoarse s).embedding k).val
    let parentJ'K' :=
      appendConditionalParent
        (appendConditionalParent parent
          ((B.selectedCoarse r).embedding j').val)
        ((B.selectedCoarse s).embedding k').val
    have hcard :=
      B.jointParentCell_card_eq_conditionalParentCell_card r s j k
    have hcard' :=
      B.jointParentCell_card_eq_conditionalParentCell_card r s j' k'
    have hconditional :=
      U.conditionalUniform
        (show 1 ≤ m + 2 by omega)
        (show m + 2 ≤ depth + 1 by omega)
        scale' parentJK parentJ'K'
        (by
          rw [← hcard]
          exact hjk)
        (by
          rw [← hcard']
          exact hjk')
    rw [← hcard, ← hcard'] at hconditional
    exact hconditional

@[simp] lemma toJoint_uniformity
    (B : ConditionalBranchSystem U scale parent)
    (hdepth : m + 1 ≤ depth) :
    (B.toJoint hdepth).uniformity = U.uniformity :=
  U.assigned_to_full.symm

end ConditionalBranchSystem

end Kakeya.Streamlined
