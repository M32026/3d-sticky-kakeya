import MyLeanRepo.Kakeya.Streamlined.IndependentDilatedCoverGeometry
import MyLeanRepo.Kakeya.Streamlined.IndependentDilatedCoverRelations
import MyLeanRepo.Kakeya.Streamlined.DilatedTubeCover.FullContainmentFibers

/-!
# Containment fibers for independent dilated covers

The parent map in a `DilatedTubeCover` is an auxiliary surjective choice.  The
paper notation `T[T_rho]`, however, refers to every tube contained in the
chosen coarse tube, not only the selected parent fiber.  This module records
those full containment fibers.

For cross-scale parent families, containment uses the explicit universal
parent dilation `independentCoverParentDilation A`.
-/

noncomputable section

namespace Kakeya.Streamlined

namespace DilatedDiscreteUniformTubeStructure

variable {delta A : ℝ} {F : TubeFamily delta}
variable {hdelta_le_one : delta ≤ 1}
variable (U : DilatedDiscreteUniformTubeStructure
  (A := A) F hdelta_le_one)

/-- All original fine tubes lying in one dilated grid-scale parent. -/
def containedFineIndices
    (r : UniformScaleIndex delta)
    (j : Fin (U.coarse r).card) :
    Finset (Fin F.card) :=
  (U.cover r).fullContainmentFiberIndices j

@[simp] lemma mem_containedFineIndices_iff
    (r : UniformScaleIndex delta)
    (j : Fin (U.coarse r).card)
    (i : Fin F.card) :
    i ∈ U.containedFineIndices r j ↔
      (F.tube i).carrier ⊆
        dilatedTubeCarrier A ((U.coarse r).tube j) := by
  simp [containedFineIndices]

/-- The full fine containment fiber over one grid-scale parent. -/
def containedFineSubfamily
    (r : UniformScaleIndex delta)
    (j : Fin (U.coarse r).card) :
    TubeSubfamily F :=
  (U.cover r).fullContainmentFiberSubfamily j

/-- The chosen parent fiber is contained in the full containment fiber. -/
lemma fineFiberIndices_subset_containedFineIndices
    (r : UniformScaleIndex delta)
    (j : Fin (U.coarse r).card) :
    U.fineFiberIndices r j ⊆ U.containedFineIndices r j := by
  intro i hi
  have hparent :
      (U.cover r).parent i = j :=
    (U.mem_fineFiberIndices_iff r j i).mp hi
  rw [U.mem_containedFineIndices_iff r j i]
  have h := (U.cover r).nested i
  simpa [hparent] using h

lemma containedFineSubfamily_nonempty
    (r : UniformScaleIndex delta)
    (j : Fin (U.coarse r).card) :
    (U.containedFineSubfamily r j).Nonempty := by
  classical
  rcases (U.cover r).parent_surjective j with ⟨i, hi⟩
  have hchosen : i ∈ U.fineFiberIndices r j := by
    rw [U.mem_fineFiberIndices_iff r j i]
    exact hi
  have hfull : i ∈ U.containedFineIndices r j :=
    U.fineFiberIndices_subset_containedFineIndices r j hchosen
  exact Finset.card_pos.mpr ⟨i, hfull⟩

lemma containedFineSubfamily_essentiallyDistinct
    (hF : F.IsEssentiallyDistinct)
    (r : UniformScaleIndex delta)
    (j : Fin (U.coarse r).card) :
    (U.containedFineSubfamily r j).family.IsEssentiallyDistinct :=
  (U.containedFineSubfamily r j).isEssentiallyDistinct hF

/--
All scale-`r` parents lying in the universal dilation of one scale-`s`
parent.  This is the full cross-scale containment fiber.
-/
def containedParentIndices
    (r s : UniformScaleIndex delta)
    (k : Fin (U.coarse s).card) :
    Finset (Fin (U.coarse r).card) := by
  classical
  exact Finset.univ.filter fun j =>
    ((U.coarse r).tube j).carrier ⊆
      dilatedTubeCarrier (independentCoverParentDilation A)
        ((U.coarse s).tube k)

@[simp] lemma mem_containedParentIndices_iff
    (r s : UniformScaleIndex delta)
    (k : Fin (U.coarse s).card)
    (j : Fin (U.coarse r).card) :
    j ∈ U.containedParentIndices r s k ↔
      ((U.coarse r).tube j).carrier ⊆
        dilatedTubeCarrier (independentCoverParentDilation A)
          ((U.coarse s).tube k) := by
  simp [containedParentIndices]

/-- The full containment subfamily of scale-`r` parents. -/
def containedParentSubfamily
    (r s : UniformScaleIndex delta)
    (k : Fin (U.coarse s).card) :
    TubeSubfamily (U.coarse r) :=
  TubeSubfamily.fromFinset
    (U.coarse r) (U.containedParentIndices r s k)

/--
Every assigned common-child relation is contained in the full parent
containment relation.
-/
lemma relatedIndices_subset_containedParentIndices
    (hA : 1 ≤ A) (hdelta : 0 < delta)
    (hF_ball : F.IsInUnitBall)
    (r s : UniformScaleIndex delta)
    (hrs :
      (uniformScale delta hdelta_le_one r).1 ≤
        (uniformScale delta hdelta_le_one s).1)
    (k : Fin (U.coarse s).card) :
    U.relatedIndices r s k ⊆
      U.containedParentIndices r s k := by
  intro j hj
  have hrel : U.ParentRelation r s j k :=
    (U.mem_relatedIndices_iff r s k j).mp hj
  rw [U.mem_containedParentIndices_iff r s k j]
  exact U.related_parent_containment
    hA hdelta hF_ball r s hrs j k hrel

lemma containedParentIndices_nonempty
    (hA : 1 ≤ A) (hdelta : 0 < delta)
    (hF_ball : F.IsInUnitBall)
    (r s : UniformScaleIndex delta)
    (hrs :
      (uniformScale delta hdelta_le_one r).1 ≤
        (uniformScale delta hdelta_le_one s).1)
    (k : Fin (U.coarse s).card) :
    (U.containedParentIndices r s k).Nonempty := by
  classical
  rcases U.relatedIndices_nonempty r s k with ⟨j, hj⟩
  exact ⟨j,
    U.relatedIndices_subset_containedParentIndices
      hA hdelta hF_ball r s hrs k hj⟩

lemma containedParentSubfamily_nonempty
    (hA : 1 ≤ A) (hdelta : 0 < delta)
    (hF_ball : F.IsInUnitBall)
    (r s : UniformScaleIndex delta)
    (hrs :
      (uniformScale delta hdelta_le_one r).1 ≤
        (uniformScale delta hdelta_le_one s).1)
    (k : Fin (U.coarse s).card) :
    (U.containedParentSubfamily r s k).Nonempty := by
  classical
  exact Finset.card_pos.mpr
    (U.containedParentIndices_nonempty
      hA hdelta hF_ball r s hrs k)

lemma containedParentSubfamily_essentiallyDistinct
    (r s : UniformScaleIndex delta)
    (k : Fin (U.coarse s).card) :
    (U.containedParentSubfamily r s k).family.IsEssentiallyDistinct :=
  (U.containedParentSubfamily r s k).isEssentiallyDistinct
    (U.coarse_distinct r)

end DilatedDiscreteUniformTubeStructure

end Kakeya.Streamlined
