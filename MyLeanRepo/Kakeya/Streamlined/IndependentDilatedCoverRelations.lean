import MyLeanRepo.Kakeya.Streamlined.DilatedDiscreteUniformRefinement
import MyLeanRepo.Kakeya.Streamlined.TubeRefinement

/-!
# Relations between independent dilated paper-grid covers

The paper-level Section 2 refinement chooses a dilated cover independently at
each distinguished scale.  Therefore the faithful cross-scale object is the
relation saying that two coarse indices are parents of a common selected fine
tube, not a transition map.
-/

noncomputable section

namespace Kakeya.Streamlined

namespace DilatedDiscreteUniformTubeStructure

variable {delta A : ℝ} {F : TubeFamily delta}
variable {hdelta_le_one : delta ≤ 1}
variable (U : DilatedDiscreteUniformTubeStructure
  (A := A) F hdelta_le_one)

/-- Fine indices assigned to one parent at a distinguished grid scale. -/
def fineFiberIndices
    (r : UniformScaleIndex delta)
    (j : Fin (U.coarse r).card) :
    Finset (Fin F.card) :=
  Finset.univ.filter fun i => (U.cover r).parent i = j

@[simp] lemma mem_fineFiberIndices_iff
    (r : UniformScaleIndex delta)
    (j : Fin (U.coarse r).card)
    (i : Fin F.card) :
    i ∈ U.fineFiberIndices r j ↔
      (U.cover r).parent i = j := by
  simp [fineFiberIndices]

/-- The selected fine tubes assigned to one grid-scale parent. -/
def fineFiberSubfamily
    (r : UniformScaleIndex delta)
    (j : Fin (U.coarse r).card) :
    TubeSubfamily F :=
  TubeSubfamily.fromFinset F (U.fineFiberIndices r j)

lemma fineFiberSubfamily_nonempty
    (r : UniformScaleIndex delta)
    (j : Fin (U.coarse r).card) :
    (U.fineFiberSubfamily r j).Nonempty := by
  classical
  rcases (U.cover r).parent_surjective j with ⟨i, hi⟩
  have hmem : i ∈ U.fineFiberIndices r j := by
    rw [U.mem_fineFiberIndices_iff r j i]
    exact hi
  exact Finset.card_pos.mpr ⟨i, hmem⟩

lemma fineFiberSubfamily_essentiallyDistinct
    (hF : F.IsEssentiallyDistinct)
    (r : UniformScaleIndex delta)
    (j : Fin (U.coarse r).card) :
    (U.fineFiberSubfamily r j).family.IsEssentiallyDistinct :=
  (U.fineFiberSubfamily r j).isEssentiallyDistinct hF

/-- Two paper-grid parents are related when they contain one common fine tube
after the fixed universal dilation. -/
def ParentRelation
    (r s : UniformScaleIndex delta)
    (j : Fin (U.coarse r).card)
    (k : Fin (U.coarse s).card) : Prop :=
  ∃ i : Fin F.card,
    (U.cover r).parent i = j ∧
      (U.cover s).parent i = k

/-- Fine indices with prescribed parents at two independent grid scales. -/
def parentPairCell
    (r s : UniformScaleIndex delta)
    (j : Fin (U.coarse r).card)
    (k : Fin (U.coarse s).card) :
    Finset (Fin F.card) :=
  Finset.univ.filter fun i =>
    (U.cover r).parent i = j ∧
      (U.cover s).parent i = k

@[simp] lemma mem_parentPairCell_iff
    (r s : UniformScaleIndex delta)
    (j : Fin (U.coarse r).card)
    (k : Fin (U.coarse s).card)
    (i : Fin F.card) :
    i ∈ U.parentPairCell r s j k ↔
      (U.cover r).parent i = j ∧
        (U.cover s).parent i = k := by
  simp [parentPairCell]

lemma parentRelation_iff_pairCell_nonempty
    (r s : UniformScaleIndex delta)
    (j : Fin (U.coarse r).card)
    (k : Fin (U.coarse s).card) :
    U.ParentRelation r s j k ↔
      (U.parentPairCell r s j k).Nonempty := by
  constructor
  · rintro ⟨i, hri, hsi⟩
    exact ⟨i, by simp [hri, hsi]⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, (U.mem_parentPairCell_iff r s j k i).mp hi⟩

/-- Coarse indices at scale `r` related to a fixed index at scale `s`. -/
def relatedIndices
    (r s : UniformScaleIndex delta)
    (k : Fin (U.coarse s).card) :
    Finset (Fin (U.coarse r).card) := by
  classical
  exact Finset.univ.filter fun j => U.ParentRelation r s j k

@[simp] lemma mem_relatedIndices_iff
    (r s : UniformScaleIndex delta)
    (k : Fin (U.coarse s).card)
    (j : Fin (U.coarse r).card) :
    j ∈ U.relatedIndices r s k ↔
      U.ParentRelation r s j k := by
  classical
  simp [relatedIndices]

/-- Every parent at one grid scale is related to a parent at every other grid
scale, by surjectivity of both fine-to-coarse parent assignments. -/
lemma relatedIndices_nonempty
    (r s : UniformScaleIndex delta)
    (k : Fin (U.coarse s).card) :
    (U.relatedIndices r s k).Nonempty := by
  classical
  rcases (U.cover s).parent_surjective k with ⟨i, hi⟩
  let j := (U.cover r).parent i
  refine ⟨j, ?_⟩
  rw [U.mem_relatedIndices_iff r s k j]
  exact ⟨i, rfl, hi⟩

/-- Every parent at scale `r` is related to some parent at scale `s`. -/
lemma exists_related_right
    (r s : UniformScaleIndex delta)
    (j : Fin (U.coarse r).card) :
    ∃ k : Fin (U.coarse s).card,
      U.ParentRelation r s j k := by
  rcases (U.cover r).parent_surjective j with ⟨i, hi⟩
  exact ⟨(U.cover s).parent i, i, hi, rfl⟩

/-- The related grid-scale tubes form an indexed subfamily. -/
def relatedSubfamily
    (r s : UniformScaleIndex delta)
    (k : Fin (U.coarse s).card) :
    TubeSubfamily (U.coarse r) :=
  TubeSubfamily.fromFinset (U.coarse r) (U.relatedIndices r s k)

lemma relatedSubfamily_nonempty
    (r s : UniformScaleIndex delta)
    (k : Fin (U.coarse s).card) :
    (U.relatedSubfamily r s k).Nonempty := by
  classical
  have hcard : 0 < (U.relatedIndices r s k).card :=
    Finset.card_pos.mpr (U.relatedIndices_nonempty r s k)
  exact hcard

lemma relatedSubfamily_essentiallyDistinct
    (r s : UniformScaleIndex delta)
    (k : Fin (U.coarse s).card) :
    (U.relatedSubfamily r s k).family.IsEssentiallyDistinct :=
  (U.relatedSubfamily r s k).isEssentiallyDistinct
    (U.coarse_distinct r)

/-- The fine fiber over a fixed `s`-parent is the disjoint union of its pair
cells over related `r`-parents. -/
lemma s_fiber_eq_biUnion_pairCells
    (r s : UniformScaleIndex delta)
    (k : Fin (U.coarse s).card) :
    (Finset.univ.filter fun i : Fin F.card =>
        (U.cover s).parent i = k) =
      (U.relatedIndices r s k).biUnion fun j =>
        U.parentPairCell r s j k := by
  classical
  ext i
  constructor
  · intro hi
    have hik : (U.cover s).parent i = k :=
      (Finset.mem_filter.mp hi).2
    let j := (U.cover r).parent i
    refine Finset.mem_biUnion.mpr ⟨j, ?_, ?_⟩
    · rw [U.mem_relatedIndices_iff r s k j]
      exact ⟨i, rfl, hik⟩
    · simp [parentPairCell, j, hik]
  · intro hi
    rcases Finset.mem_biUnion.mp hi with ⟨j, _hj, hij⟩
    have hpair := (U.mem_parentPairCell_iff r s j k i).mp hij
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hpair.2⟩

end DilatedDiscreteUniformTubeStructure

end Kakeya.Streamlined
