import MyLeanRepo.Kakeya.Streamlined.IndependentDilatedCoverOverlap

/-!
# Comparing full containment fibers with assigned uniform fibers

The cover record partitions fine indices through its selected parent map,
whereas the paper's containment fiber includes every fine tube lying in a
dilated parent.  A full fiber is covered by the selected fibers whose parents
lie in one bounded parent-neighborhood.  This gives an explicit comparison
between the two cardinalities.
-/

noncomputable section

namespace Kakeya.Streamlined

namespace DilatedDiscreteUniformTubeStructure

variable {delta A : ℝ} {F : TubeFamily delta}
variable {hdelta_le_one : delta ≤ 1}
variable (U : DilatedDiscreteUniformTubeStructure
  (A := A) F hdelta_le_one)

/--
The full fine containment fiber over `j` is covered by the assigned fibers of
all same-scale parents lying in the universal dilation of `j`.
-/
lemma containedFineIndices_subset_biUnion_fineFiberIndices
    (hA : 1 ≤ A) (hdelta : 0 < delta)
    (hF_ball : F.IsInUnitBall)
    (r : UniformScaleIndex delta)
    (j : Fin (U.coarse r).card) :
    U.containedFineIndices r j ⊆
      (U.containedParentIndices r r j).biUnion
        (U.fineFiberIndices r) := by
  classical
  intro i hi
  let p := (U.cover r).parent i
  have hp : p ∈ U.containedParentIndices r r j := by
    rw [U.mem_containedParentIndices_iff r r j p]
    have hi_contains :
        (F.tube i).carrier ⊆
          dilatedTubeCarrier A ((U.coarse r).tube j) :=
      (U.mem_containedFineIndices_iff r j i).mp hi
    exact common_child_parent_containment hA
      (lt_of_lt_of_le hdelta
        (uniformScale delta hdelta_le_one r).property.1)
      (uniformScale delta hdelta_le_one r).property.2
      le_rfl (F.tube i) (hF_ball i)
      ((U.coarse r).tube p) ((U.coarse r).tube j)
      ((U.cover r).nested i) hi_contains
  refine Finset.mem_biUnion.mpr ⟨p, hp, ?_⟩
  rw [U.mem_fineFiberIndices_iff r p i]

/--
If the same-scale parent neighborhood of `j` has cardinality at most `M`,
then the full containment fiber has cardinality at most
`M * assignedUniformity * selected-fiber-cardinality`.
-/
lemma containedFineCount_le_of_parentCount_le
    (hA : 1 ≤ A) (hdelta : 0 < delta)
    (hF_ball : F.IsInUnitBall)
    (r : UniformScaleIndex delta)
    (j : Fin (U.coarse r).card)
    (M : ENNReal)
    (hparent :
      ((U.containedParentIndices r r j).card : ENNReal) ≤ M) :
    ((U.containedFineIndices r j).card : ENNReal) ≤
      M * U.assignedUniformity *
        (U.cover r).toFactoring.fiberCount j := by
  classical
  let parents := U.containedParentIndices r r j
  let fibers := U.fineFiberIndices r
  have hsubset :
      U.containedFineIndices r j ⊆ parents.biUnion fibers := by
    exact U.containedFineIndices_subset_biUnion_fineFiberIndices
      hA hdelta hF_ball r j
  have hcard_subset :
      ((U.containedFineIndices r j).card : ENNReal) ≤
        ((parents.biUnion fibers).card : ENNReal) := by
    exact_mod_cast Finset.card_le_card hsubset
  have hcard_union :
      ((parents.biUnion fibers).card : ENNReal) ≤
        ∑ p ∈ parents, ((fibers p).card : ENNReal) := by
    have hnat :
        (parents.biUnion fibers).card ≤
          ∑ p ∈ parents, (fibers p).card :=
      Finset.card_biUnion_le
    exact_mod_cast hnat
  have hfiber :
      ∀ p ∈ parents,
        ((fibers p).card : ENNReal) ≤
          U.assignedUniformity *
            (U.cover r).toFactoring.fiberCount j := by
    intro p _hp
    have h := (U.assignedUniform r).2 p j
    have hp :
        ((fibers p).card : ENNReal) =
          (U.cover r).toFactoring.fiberCount p := by
      rfl
    rw [hp]
    exact h
  calc
    ((U.containedFineIndices r j).card : ENNReal)
        ≤ ((parents.biUnion fibers).card : ENNReal) :=
      hcard_subset
    _ ≤ ∑ p ∈ parents, ((fibers p).card : ENNReal) :=
      hcard_union
    _ ≤ ∑ _p ∈ parents,
        U.assignedUniformity *
          (U.cover r).toFactoring.fiberCount j := by
      exact Finset.sum_le_sum fun p hp => hfiber p hp
    _ = (parents.card : ENNReal) *
        (U.assignedUniformity *
          (U.cover r).toFactoring.fiberCount j) := by
      simp [nsmul_eq_mul]
    _ ≤ M * (U.assignedUniformity *
        (U.cover r).toFactoring.fiberCount j) := by
      exact mul_le_mul_right' hparent _
    _ = M * U.assignedUniformity *
        (U.cover r).toFactoring.fiberCount j := by
      ring

end DilatedDiscreteUniformTubeStructure

/--
For each cover dilation `A`, full fine containment fibers are bounded by a
universal parent-overlap constant times the cover uniformity and the selected
fiber size.
-/
def IndependentDilatedCoverFullFiberCountStatement (A : ℝ) : Prop :=
  ∃ M : ENNReal, 0 < M ∧ M ≠ ⊤ ∧
    ∀ delta : ℝ, 0 < delta →
      ∀ hdelta_le_one : delta ≤ 1,
      ∀ F : TubeFamily delta,
        F.IsInUnitBall →
        ∀ U : DilatedDiscreteUniformTubeStructure
            (A := A) F hdelta_le_one,
          ∀ r : UniformScaleIndex delta,
          ∀ j : Fin (U.coarse r).card,
            ((U.containedFineIndices r j).card : ENNReal) ≤
              M * U.assignedUniformity *
                (U.cover r).toFactoring.fiberCount j

theorem independent_dilated_cover_full_fiber_count
    (A : ℝ) (hA : 1 ≤ A) :
    IndependentDilatedCoverFullFiberCountStatement A := by
  rcases
      DilatedDiscreteUniformTubeStructure.contained_parent_packing A hA with
    ⟨C, hC, hpacking⟩
  let M : ENNReal := ENNReal.ofReal C
  have hM : 0 < M := ENNReal.ofReal_pos.mpr hC
  have hM_top : M ≠ ⊤ := ENNReal.ofReal_ne_top
  refine ⟨M, hM, hM_top, ?_⟩
  intro delta hdelta hdelta_le_one F hF_ball U r j
  have hpack :=
    hpacking delta hdelta hdelta_le_one F U r r le_rfl j
  have hscale_pos :
      0 < (uniformScale delta hdelta_le_one r).1 :=
    lt_of_lt_of_le hdelta
      (uniformScale delta hdelta_le_one r).property.1
  have hpack_real :
      ((U.containedParentIndices r r j).card : ℝ) ≤ C := by
    simpa [div_self hscale_pos.ne'] using hpack
  have hpack_enn :
      ((U.containedParentIndices r r j).card : ENNReal) ≤ M := by
    have h :=
      ENNReal.ofReal_le_ofReal hpack_real
    simpa [M] using h
  exact U.containedFineCount_le_of_parentCount_le
    hA hdelta hF_ball r j M hpack_enn

end Kakeya.Streamlined
