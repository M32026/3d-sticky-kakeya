import MyLeanRepo.Kakeya.Streamlined.DividingScales.ConditionalFactorProfiles

/-!
# Decompose conditional relation indices through one middle scale

For `P.fine ≤ middle ≤ P.coarse`, the fine-to-coarse relation image is the
union over middle-to-coarse relation parents of fine-to-middle pieces.  Each
piece is contained in the corresponding inner-child relation image for any
representative of that middle parent in the historical cell.
-/

noncomputable section

namespace Kakeya.Streamlined

namespace FrostmanConditionalFactorScope

variable {depth : ℕ} {delta A C : ℝ} {F : TubeFamily delta}
variable {hdelta_le_one : delta ≤ 1}
variable {U : ConditionallyUniformLocalDilatedDiscreteUniformTubeStructure
  depth (A := A) (C := C) F hdelta_le_one}

/-- The fine-to-middle piece associated to one middle parent. -/
def splitPiece
    (P : FrostmanConditionalFactorScope U)
    (i : Fin F.card)
    (middle coarse : UniformScaleIndex delta)
    (k : Fin (U.coarse middle).card) :
    Finset (Fin (U.coarse P.fine).card) :=
  ((P.endpointCell i coarse).filter
    (fun original => (U.cover middle).parent original = k)).image
      (U.cover P.fine).parent

/--
The fine-to-coarse relation image is exactly the union of its pieces indexed
by the represented middle-to-coarse parents.
-/
lemma relationIndices_split_eq
    (P : FrostmanConditionalFactorScope U)
    (middle coarse : UniformScaleIndex delta)
    (i : Fin F.card) :
    P.relationIndices i P.fine coarse =
      Finset.biUnion (P.relationIndices i middle coarse)
        (fun k => P.splitPiece i middle coarse k) := by
  classical
  ext j
  simp only [Finset.mem_biUnion]
  constructor
  · rw [mem_relationIndices_iff]
    rintro ⟨original, hhistory, hcoarse, hfine⟩
    let k : Fin (U.coarse middle).card :=
      (U.cover middle).parent original
    have hk : k ∈ P.relationIndices i middle coarse := by
      rw [mem_relationIndices_iff]
      exact ⟨original, hhistory, hcoarse, rfl⟩
    have hj : j ∈ P.splitPiece i middle coarse k := by
      simp only [splitPiece, Finset.mem_image]
      refine ⟨original, ?_, hfine⟩
      simp only [Finset.mem_filter, mem_endpointCell_iff]
      exact ⟨⟨hhistory, hcoarse⟩, rfl⟩
    exact ⟨k, hk, hj⟩
  · rintro ⟨k, _hk, hj⟩
    rw [mem_relationIndices_iff]
    simp only [splitPiece, Finset.mem_image] at hj
    rcases hj with ⟨original, hfilter, hfine⟩
    have hendpoint : original ∈ P.endpointCell i coarse :=
      (Finset.mem_filter.mp hfilter).1
    have hhistory :
        original ∈ conditionalParentCell U.coarse U.cover
          P.scale (P.parentOf i) :=
      (P.mem_endpointCell_iff i original coarse).mp hendpoint |>.1
    have hcoarse :
        (U.cover coarse).parent original =
          (U.cover coarse).parent i :=
      (P.mem_endpointCell_iff i original coarse).mp hendpoint |>.2
    exact ⟨original, hhistory, hcoarse, hfine⟩

/--
If `i_k` lies in the historical cell and has middle parent `k`, then the
piece at `k` is contained in the inner child's fine-to-middle relation image
represented by `i_k`.
-/
lemma splitPiece_subset_innerChild
    (P : FrostmanConditionalFactorScope U)
    (hroom : P.coordinateCount < depth)
    (middle : UniformScaleIndex delta)
    (hfine_middle :
      (uniformScale delta hdelta_le_one P.fine).1 ≤
        (uniformScale delta hdelta_le_one middle).1)
    (coarse : UniformScaleIndex delta)
    (i : Fin F.card)
    (k : Fin (U.coarse middle).card)
    (i_k : Fin F.card)
    (hi_k_history :
      i_k ∈ conditionalParentCell U.coarse U.cover
        P.scale (P.parentOf i))
    (hi_k_middle : (U.cover middle).parent i_k = k) :
    P.splitPiece i middle coarse k ⊆
      (P.innerChild hroom middle hfine_middle).relationIndices
        i_k P.fine middle := by
  classical
  have hparent_eq : P.parentOf i_k = P.parentOf i := by
    funext t
    have h :=
      (mem_conditionalParentCell_iff U.coarse U.cover
        P.scale (P.parentOf i) i_k).mp hi_k_history t
    simpa [parentOf] using h
  intro j hj
  simp only [splitPiece, Finset.mem_image] at hj
  rcases hj with ⟨original, hfilter, rfl⟩
  have hendpoint : original ∈ P.endpointCell i coarse :=
    (Finset.mem_filter.mp hfilter).1
  have hmiddle : (U.cover middle).parent original = k :=
    (Finset.mem_filter.mp hfilter).2
  have hhistory :
      original ∈ conditionalParentCell U.coarse U.cover
        P.scale (P.parentOf i) :=
    (P.mem_endpointCell_iff i original coarse).mp hendpoint |>.1
  rw [mem_relationIndices_iff]
  refine ⟨original, ?_, ?_, rfl⟩
  · rw [mem_conditionalParentCell_iff]
    have hmain :
        ∀ t : Fin (P.coordinateCount + 1),
          ((U.cover
            ((P.innerChild hroom middle hfine_middle).scale t)).parent
              original).val =
            (P.innerChild hroom middle hfine_middle).parentOf i_k t := by
      intro t
      by_cases h : t.val < P.coordinateCount
      · let old : Fin P.coordinateCount := ⟨t.val, h⟩
        have ht : t = old.castSucc := by
          apply Fin.ext
          simp [old]
        rw [ht,
          P.innerChild_scale_castSucc hroom middle hfine_middle old,
          P.innerChild_parentOf_castSucc hroom middle hfine_middle i_k old]
        have hold :
            ((U.cover (P.scale old)).parent original).val =
              P.parentOf i old :=
          (mem_conditionalParentCell_iff U.coarse U.cover
            P.scale (P.parentOf i) original).mp hhistory old
        rw [hparent_eq]
        exact hold
      · have htval : t.val = P.coordinateCount := by omega
        have ht : t = Fin.last P.coordinateCount := by
          apply Fin.ext
          simp [htval]
        rw [ht,
          P.innerChild_scale_last hroom middle hfine_middle,
          P.innerChild_parentOf_last hroom middle hfine_middle i_k,
          hi_k_middle]
        exact congr_arg Fin.val hmiddle
    exact hmain
  · simpa [hi_k_middle] using hmiddle

end FrostmanConditionalFactorScope

end Kakeya.Streamlined
