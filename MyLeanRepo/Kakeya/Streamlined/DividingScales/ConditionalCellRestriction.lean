import MyLeanRepo.Kakeya.Streamlined.ConditionalUniformDilatedDiscreteUniformRefinement
import MyLeanRepo.Kakeya.Streamlined.LocalDilatedTubeCover.Restriction

/-!
# Restricting a cover to a finite conditional parent cell

An existing recursive branch is a cell cut out by `m` ambient parent
coordinates.  Restricting another independent paper-grid cover to that branch
appends one coordinate.  Hence every fiber of the restricted cover is an
`(m + 1)`-coordinate cell, and finite-depth conditional uniformity gives the
restricted cover the same uniformity constant.

This is the combinatorial closure property required by the Section 7
stopping-time recursion.  No transition map between covers is introduced.
-/

noncomputable section

namespace Kakeya.Streamlined

namespace ConditionallyUniformLocalDilatedDiscreteUniformTubeStructure

variable {depth : ℕ} {delta A C : ℝ} {F : TubeFamily delta}
variable {hdelta_le_one : delta ≤ 1}
variable (U : ConditionallyUniformLocalDilatedDiscreteUniformTubeStructure
  depth (A := A) (C := C) F hdelta_le_one)

/--
Restrict one ambient cover to a conditional parent cell using at most
`depth` existing coordinates.  The restricted cover is
`U.assignedUniformity`-uniform because its assigned fibers are the cells
obtained by appending the new parent coordinate.
-/
lemma exists_restrictedCover_conditionalCell_isCUniform
    {m : ℕ} (hm : m ≤ depth)
    (scale : Fin m → UniformScaleIndex delta)
    (parent : Fin m → ℕ)
    (r : UniformScaleIndex delta) :
    let S := TubeSubfamily.fromFinset F
      (conditionalParentCell U.coarse U.cover scale parent)
    ∃ R : TubeSubfamily (U.coarse r),
      R.family.IsEssentiallyDistinct ∧
      ∃ Q : LocalDilatedTubeCover A C S.family R.family,
        (∀ i, R.embedding (Q.parent i) =
          (U.cover r).parent (S.embedding i)) ∧
        Q.toDilatedTubeCover.toFactoring.FibersAreCUniform
          U.assignedUniformity := by
  classical
  let I := conditionalParentCell U.coarse U.cover scale parent
  let S := TubeSubfamily.fromFinset F I
  rcases restrict_local_dilated_tube_cover
      (U.coarse_distinct r) (U.cover r) S with
    ⟨R, hR_distinct, Q, hQ⟩
  refine
    ⟨R, hR_distinct, Q, hQ,
      U.one_le_assignedUniformity, ?_⟩
  let scale' : Fin (m + 1) → UniformScaleIndex delta :=
    Fin.lastCases r scale
  let parent' (j : Fin R.family.card) : Fin (m + 1) → ℕ :=
    Fin.lastCases (R.embedding j).val parent
  have hfiber_image : ∀ j : Fin R.family.card,
      Finset.image S.embedding
          (Finset.univ.filter fun i => Q.parent i = j) =
        conditionalParentCell U.coarse U.cover scale' (parent' j) := by
    intro j
    ext original
    constructor
    · intro horiginal
      rcases Finset.mem_image.mp horiginal with ⟨i, hi, rfl⟩
      have hiQ : Q.parent i = j := (Finset.mem_filter.mp hi).2
      rw [mem_conditionalParentCell_iff]
      intro t
      refine Fin.lastCases ?_ (fun old => ?_) t
      · have hcompat := hQ i
        rw [hiQ] at hcompat
        have hval := congrArg Fin.val hcompat.symm
        rw [show scale' (Fin.last m) = r by simp [scale']]
        rw [show parent' j (Fin.last m) = (R.embedding j).val by
          simp [parent']]
        exact hval
      · have hiI : S.embedding i ∈ I :=
          Finset.orderEmbOfFin_mem I rfl i
        have hold := (mem_conditionalParentCell_iff
          U.coarse U.cover scale parent (S.embedding i)).mp hiI old
        rw [show scale' old.castSucc = scale old by simp [scale']]
        rw [show parent' j old.castSucc = parent old by simp [parent']]
        exact hold
    · intro horiginal
      have holdall := (mem_conditionalParentCell_iff
        U.coarse U.cover scale' (parent' j) original).mp horiginal
      have hold : original ∈ I := by
        rw [mem_conditionalParentCell_iff]
        intro t
        have h := holdall t.castSucc
        rw [show scale' t.castSucc = scale t by simp [scale']] at h
        rw [show parent' j t.castSucc = parent t by simp [parent']] at h
        exact h
      have himage :
          original ∈ Finset.image S.embedding Finset.univ := by
        change original ∈ Finset.image
          (I.orderEmbOfFin rfl) Finset.univ
        rw [Finset.image_orderEmbOfFin_univ I rfl]
        exact hold
      rcases Finset.mem_image.mp himage with
        ⟨i, _hi, hi_original⟩
      refine Finset.mem_image.mpr ⟨i, ?_, hi_original⟩
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ i, ?_⟩
      apply R.embedding.injective
      rw [hQ i, hi_original]
      have h := holdall (Fin.last m)
      apply Fin.ext
      rw [show scale' (Fin.last m) = r by simp [scale']] at h
      rw [show parent' j (Fin.last m) = (R.embedding j).val by
        simp [parent']] at h
      exact h
  intro j j'
  have hj :
      0 < (Finset.univ.filter fun i => Q.parent i = j).card := by
    rcases Q.parent_surjective j with ⟨i, hi⟩
    exact Finset.card_pos.mpr ⟨i, by simp [hi]⟩
  have hj' :
      0 < (Finset.univ.filter fun i => Q.parent i = j').card := by
    rcases Q.parent_surjective j' with ⟨i, hi⟩
    exact Finset.card_pos.mpr ⟨i, by simp [hi]⟩
  have hcard : ∀ j : Fin R.family.card,
      (Finset.univ.filter fun i => Q.parent i = j).card =
        (conditionalParentCell U.coarse U.cover
          scale' (parent' j)).card := by
    intro j
    have h := Finset.card_image_of_injective
      (Finset.univ.filter fun i => Q.parent i = j)
      S.embedding.injective
    rw [hfiber_image j] at h
    exact h.symm
  have hconditional := U.conditionalUniform
    (show 1 ≤ m + 1 by omega)
    (show m + 1 ≤ depth + 1 by omega)
    scale' (parent' j) (parent' j')
    (by simpa [← hcard j] using hj)
    (by simpa [← hcard j'] using hj')
  change
    ((Finset.univ.filter fun i => Q.parent i = j).card : ENNReal) ≤
      U.assignedUniformity *
        ((Finset.univ.filter fun i => Q.parent i = j').card : ENNReal)
  rw [hcard j, hcard j']
  exact hconditional

end ConditionallyUniformLocalDilatedDiscreteUniformTubeStructure

end Kakeya.Streamlined
