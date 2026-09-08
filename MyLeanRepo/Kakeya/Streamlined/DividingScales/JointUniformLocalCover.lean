import MyLeanRepo.Kakeya.Streamlined.JointUniformDilatedDiscreteUniformRefinement
import MyLeanRepo.Kakeya.Streamlined.IndependentDilatedCoverFiber

/-!
# Joint uniformity for the local related cover

Fix one parent at a paper-grid scale `s` and cover its assigned fine fiber at
another independently selected scale `r`.  The fibers of the resulting local
related cover are exactly the joint parent cells for `(r, s)`.  Consequently
the strengthened Section 2 joint uniformity gives the local cover the same
uniformity constant, without choosing any cross-scale transition map.
-/

noncomputable section

namespace Kakeya.Streamlined

namespace JointUniformLocalDilatedDiscreteUniformTubeStructure

variable {delta A C : ℝ} {F : TubeFamily delta}
variable {hdelta_le_one : delta ≤ 1}
variable (U : JointUniformLocalDilatedDiscreteUniformTubeStructure
  (A := A) (C := C) F hdelta_le_one)

/-- Forget the local geometry and joint regularity, retaining the dilated grid. -/
abbrev toDilated :
    DilatedDiscreteUniformTubeStructure (A := A) F hdelta_le_one :=
  U.toLocalDilatedDiscreteUniformTubeStructure.toDilated

/-- The generic joint cell is definitionally the existing common-child pair cell. -/
lemma jointParentCell_eq_parentPairCell
    (r s : UniformScaleIndex delta)
    (j : Fin (U.coarse r).card)
    (k : Fin (U.coarse s).card) :
    jointParentCell U.coarse U.cover r s j k =
      U.toDilated.parentPairCell r s j k := by
  rfl

/--
The cardinality of a local related-cover fiber equals the corresponding
ambient joint parent cell.
-/
lemma localFiber_card_eq_jointParentCell_card
    (r s : UniformScaleIndex delta)
    (k : Fin (U.coarse s).card)
    (Q : DilatedTubeCover A
      (U.toDilated.fineFiberSubfamily s k).family
      (U.toDilated.relatedSubfamily r s k).family)
    (hpair :
      ∀ j : Fin (U.toDilated.relatedSubfamily r s k).family.card,
        Finset.image
            (U.toDilated.fineFiberSubfamily s k).embedding
            (Finset.univ.filter fun i => Q.parent i = j) =
          U.toDilated.parentPairCell r s
            ((U.toDilated.relatedSubfamily r s k).embedding j) k)
    (j : Fin (U.toDilated.relatedSubfamily r s k).family.card) :
    (Finset.univ.filter fun i => Q.parent i = j).card =
      (jointParentCell U.coarse U.cover r s
        ((U.toDilated.relatedSubfamily r s k).embedding j) k).card := by
  have hcard :=
    Finset.card_image_of_injective
      (Finset.univ.filter fun i => Q.parent i = j)
      (U.toDilated.fineFiberSubfamily s k).embedding.injective
  rw [hpair j] at hcard
  rw [U.jointParentCell_eq_parentPairCell r s
    ((U.toDilated.relatedSubfamily r s k).embedding j) k]
  exact hcard.symm

/--
For every fixed scale-`s` parent, its scale-`r` local related cover is
`U.assignedUniformity`-uniform.  Its parent identities remain the ambient
scale-`r` parent identities.
-/
theorem exists_fineFiber_relatedCover_isCUniform
    (r s : UniformScaleIndex delta)
    (k : Fin (U.coarse s).card) :
    ∃ Q : DilatedTubeCover A
        (U.toDilated.fineFiberSubfamily s k).family
        (U.toDilated.relatedSubfamily r s k).family,
      (∀ i,
        (U.toDilated.relatedSubfamily r s k).embedding (Q.parent i) =
          (U.cover r).parent
            ((U.toDilated.fineFiberSubfamily s k).embedding i)) ∧
      Q.toFactoring.FibersAreCUniform U.assignedUniformity := by
  classical
  rcases
      U.toDilated.exists_fineFiber_relatedCover_exact_pairCells r s k with
    ⟨Q, hparent, hpair⟩
  refine ⟨Q, hparent, U.one_le_assignedUniformity, ?_⟩
  intro j j'
  have hj :
      0 < (Finset.univ.filter fun i => Q.parent i = j).card := by
    rcases Q.parent_surjective j with ⟨i, hi⟩
    exact Finset.card_pos.mpr ⟨i, by simp [hi]⟩
  have hj' :
      0 < (Finset.univ.filter fun i => Q.parent i = j').card := by
    rcases Q.parent_surjective j' with ⟨i, hi⟩
    exact Finset.card_pos.mpr ⟨i, by simp [hi]⟩
  have hcardj :=
    U.localFiber_card_eq_jointParentCell_card r s k Q hpair j
  have hcardj' :=
    U.localFiber_card_eq_jointParentCell_card r s k Q hpair j'
  have hjoint :=
    U.jointUniform r s
      ((U.toDilated.relatedSubfamily r s k).embedding j) k
      ((U.toDilated.relatedSubfamily r s k).embedding j') k
      (by simpa [← hcardj] using hj)
      (by simpa [← hcardj'] using hj')
  change
    ((Finset.univ.filter fun i => Q.parent i = j).card : ENNReal) ≤
      U.assignedUniformity *
        ((Finset.univ.filter fun i => Q.parent i = j').card : ENNReal)
  simpa [hcardj, hcardj'] using hjoint

end JointUniformLocalDilatedDiscreteUniformTubeStructure

end Kakeya.Streamlined
