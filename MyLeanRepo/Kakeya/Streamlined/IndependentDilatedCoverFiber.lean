import MyLeanRepo.Kakeya.Streamlined.IndependentDilatedCoverRelations

/-!
# A local cover through common-child relation fibers

Fix one parent at a distinguished scale `s`.  The original fine tubes assigned
to it are covered at another distinguished scale `r` by exactly the
`r`-parents related to it through a common fine child.  This is the local
branching structure needed by the Section 7 stopping time.  It does not choose
or assert a global transition map between the two coarse families.
-/

noncomputable section

namespace Kakeya.Streamlined

namespace DilatedDiscreteUniformTubeStructure

variable {delta A : ℝ} {F : TubeFamily delta}
variable {hdelta_le_one : delta ≤ 1}
variable (U : DilatedDiscreteUniformTubeStructure
  (A := A) F hdelta_le_one)

/--
The fine fiber over one `s`-parent has a surjective `A`-dilated cover by the
subfamily of all related `r`-parents.  Parent identities are preserved in the
ambient `r`-cover.
-/
theorem exists_fineFiber_relatedCover
    (r s : UniformScaleIndex delta)
    (k : Fin (U.coarse s).card) :
    ∃ Q : DilatedTubeCover A
        (U.fineFiberSubfamily s k).family
        (U.relatedSubfamily r s k).family,
      ∀ i,
        (U.relatedSubfamily r s k).embedding (Q.parent i) =
          (U.cover r).parent
            ((U.fineFiberSubfamily s k).embedding i) := by
  classical
  let S := U.fineFiberSubfamily s k
  let R := U.relatedSubfamily r s k
  let eS : Fin S.family.card ↪ Fin F.card := S.embedding
  let eR : Fin R.family.card ↪ Fin (U.coarse r).card := R.embedding
  have h_image_eS :
      Finset.image eS Finset.univ = U.fineFiberIndices s k :=
    Finset.image_orderEmbOfFin_univ (U.fineFiberIndices s k) rfl
  have h_image_eR :
      Finset.image eR Finset.univ = U.relatedIndices r s k :=
    Finset.image_orderEmbOfFin_univ (U.relatedIndices r s k) rfl

  let idxInRelated
      (j : Fin (U.coarse r).card)
      (hj : j ∈ U.relatedIndices r s k) :
      Fin R.family.card :=
    have hmem : j ∈ Finset.image eR Finset.univ := by
      rw [h_image_eR]
      exact hj
    Classical.choose (Finset.mem_image.mp hmem)

  have h_idxInRelated_spec :
      ∀ (j : Fin (U.coarse r).card)
        (hj : j ∈ U.relatedIndices r s k),
        eR (idxInRelated j hj) = j := by
    intro j hj
    have hmem : j ∈ Finset.image eR Finset.univ := by
      rw [h_image_eR]
      exact hj
    exact (Classical.choose_spec (Finset.mem_image.mp hmem)).2

  let Qparent (i : Fin S.family.card) : Fin R.family.card :=
    let original := eS i
    let j := (U.cover r).parent original
    have hs_parent : (U.cover s).parent original = k := by
      have hi : original ∈ U.fineFiberIndices s k :=
        Finset.orderEmbOfFin_mem (U.fineFiberIndices s k) rfl i
      exact (U.mem_fineFiberIndices_iff s k original).mp hi
    have hj : j ∈ U.relatedIndices r s k := by
      rw [U.mem_relatedIndices_iff r s k j]
      exact ⟨original, rfl, hs_parent⟩
    idxInRelated j hj

  have hQparent_spec :
      ∀ i,
        eR (Qparent i) = (U.cover r).parent (eS i) := by
    intro i
    exact h_idxInRelated_spec
      ((U.cover r).parent (eS i)) (by
        rw [U.mem_relatedIndices_iff r s k]
        have hi : eS i ∈ U.fineFiberIndices s k :=
          Finset.orderEmbOfFin_mem (U.fineFiberIndices s k) rfl i
        exact ⟨eS i, rfl,
          (U.mem_fineFiberIndices_iff s k (eS i)).mp hi⟩)

  have hQparent_surj : Function.Surjective Qparent := by
    intro j'
    let j := eR j'
    have hj : j ∈ U.relatedIndices r s k :=
      Finset.orderEmbOfFin_mem (U.relatedIndices r s k) rfl j'
    have hrel : U.ParentRelation r s j k :=
      (U.mem_relatedIndices_iff r s k j).mp hj
    rcases hrel with ⟨original, hr_parent, hs_parent⟩
    have horiginal :
        original ∈ U.fineFiberIndices s k := by
      rw [U.mem_fineFiberIndices_iff s k original]
      exact hs_parent
    have hmem : original ∈ Finset.image eS Finset.univ := by
      rw [h_image_eS]
      exact horiginal
    rcases Finset.mem_image.mp hmem with
      ⟨i, _hi, hi_original⟩
    refine ⟨i, ?_⟩
    apply eR.injective
    rw [hQparent_spec i, hi_original, hr_parent]

  have hQnested :
      ∀ i,
        (S.family.tube i).carrier ⊆
          dilatedTubeCarrier A (R.family.tube (Qparent i)) := by
    intro i
    rw [S.tube_eq i, R.tube_eq (Qparent i), hQparent_spec i]
    exact (U.cover r).nested (eS i)

  let Q : DilatedTubeCover A S.family R.family :=
    { parent := Qparent
      parent_surjective := hQparent_surj
      nested := hQnested }
  exact ⟨Q, fun i => hQparent_spec i⟩

/--
For the local related cover, the original fine indices in one local fiber are
exactly the pair cell with the prescribed `r`- and `s`-parents.
-/
theorem exists_fineFiber_relatedCover_exact_pairCells
    (r s : UniformScaleIndex delta)
    (k : Fin (U.coarse s).card) :
    ∃ Q : DilatedTubeCover A
        (U.fineFiberSubfamily s k).family
        (U.relatedSubfamily r s k).family,
      (∀ i,
        (U.relatedSubfamily r s k).embedding (Q.parent i) =
          (U.cover r).parent
            ((U.fineFiberSubfamily s k).embedding i)) ∧
      ∀ j : Fin (U.relatedSubfamily r s k).family.card,
        Finset.image (U.fineFiberSubfamily s k).embedding
            (Finset.univ.filter fun i => Q.parent i = j) =
          U.parentPairCell r s
            ((U.relatedSubfamily r s k).embedding j) k := by
  classical
  rcases U.exists_fineFiber_relatedCover r s k with
    ⟨Q, hQparent⟩
  refine ⟨Q, hQparent, ?_⟩
  intro j
  let S := U.fineFiberSubfamily s k
  let R := U.relatedSubfamily r s k
  ext original
  constructor
  · intro horiginal
    rcases Finset.mem_image.mp horiginal with
      ⟨i, hi, hi_original⟩
    have hQi : Q.parent i = j :=
      (Finset.mem_filter.mp hi).2
    have hs_mem :
        S.embedding i ∈ U.fineFiberIndices s k :=
      Finset.orderEmbOfFin_mem (U.fineFiberIndices s k) rfl i
    have hs_parent :
        (U.cover s).parent (S.embedding i) = k :=
      (U.mem_fineFiberIndices_iff s k (S.embedding i)).mp hs_mem
    rw [U.mem_parentPairCell_iff r s (R.embedding j) k original]
    rw [← hi_original]
    refine ⟨?_, hs_parent⟩
    rw [← hQparent i, hQi]
  · intro horiginal
    have hpair :=
      (U.mem_parentPairCell_iff r s (R.embedding j) k original).mp
        horiginal
    have hs_mem : original ∈ U.fineFiberIndices s k := by
      rw [U.mem_fineFiberIndices_iff s k original]
      exact hpair.2
    have h_image :
        original ∈
          Finset.image S.embedding Finset.univ := by
      change original ∈
        Finset.image
          (U.fineFiberSubfamily s k).embedding Finset.univ
      rw [show
        Finset.image
            (U.fineFiberSubfamily s k).embedding Finset.univ =
          U.fineFiberIndices s k by
        exact Finset.image_orderEmbOfFin_univ
          (U.fineFiberIndices s k) rfl]
      exact hs_mem
    rcases Finset.mem_image.mp h_image with
      ⟨i, _hi, hi_original⟩
    refine Finset.mem_image.mpr ⟨i, ?_, hi_original⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ i, ?_⟩
    apply R.embedding.injective
    rw [hQparent i, hi_original, hpair.1]

end DilatedDiscreteUniformTubeStructure

end Kakeya.Streamlined
