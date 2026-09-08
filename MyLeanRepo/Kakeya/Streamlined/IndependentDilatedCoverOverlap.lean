import MyLeanRepo.Kakeya.Streamlined.IndependentDilatedCoverPacking

/-!
# Bounded overlap of independently chosen dilated parents

A fine tube may lie in the fixed dilation of several coarse tubes even though
the cover record chooses only one parent.  Essential distinctness and the
common-child geometry imply that this multiplicity is bounded by a constant
depending only on the universal cover dilation.
-/

noncomputable section

namespace Kakeya.Streamlined

namespace DilatedDiscreteUniformTubeStructure

variable {delta A : ℝ} {F : TubeFamily delta}
variable {hdelta_le_one : delta ≤ 1}
variable (U : DilatedDiscreteUniformTubeStructure
  (A := A) F hdelta_le_one)

/-- All coarse parents at scale `r` whose `A`-dilation contains fine tube `i`. -/
def containingParentIndices
    (r : UniformScaleIndex delta)
    (i : Fin F.card) :
    Finset (Fin (U.coarse r).card) := by
  classical
  exact Finset.univ.filter fun j =>
    (F.tube i).carrier ⊆
      dilatedTubeCarrier A ((U.coarse r).tube j)

@[simp] lemma mem_containingParentIndices_iff
    (r : UniformScaleIndex delta)
    (i : Fin F.card)
    (j : Fin (U.coarse r).card) :
    j ∈ U.containingParentIndices r i ↔
      (F.tube i).carrier ⊆
        dilatedTubeCarrier A ((U.coarse r).tube j) := by
  classical
  simp [containingParentIndices]

/-- The selected parent always belongs to the full geometric parent set. -/
lemma chosenParent_mem_containingParentIndices
    (r : UniformScaleIndex delta)
    (i : Fin F.card) :
    (U.cover r).parent i ∈ U.containingParentIndices r i := by
  rw [U.mem_containingParentIndices_iff r i]
  exact (U.cover r).nested i

/--
Every geometric parent of a fine tube lies in the universal dilation of that
tube's selected parent at the same scale.
-/
lemma containingParentIndices_subset_containedParentIndices
    (hA : 1 ≤ A) (hdelta : 0 < delta)
    (hF_ball : F.IsInUnitBall)
    (r : UniformScaleIndex delta)
    (i : Fin F.card) :
    U.containingParentIndices r i ⊆
      U.containedParentIndices r r ((U.cover r).parent i) := by
  intro j hj
  rw [U.mem_containedParentIndices_iff r r ((U.cover r).parent i) j]
  have hj_contains :
      (F.tube i).carrier ⊆
        dilatedTubeCarrier A ((U.coarse r).tube j) :=
    (U.mem_containingParentIndices_iff r i j).mp hj
  exact common_child_parent_containment hA
    (lt_of_lt_of_le hdelta
      (uniformScale delta hdelta_le_one r).property.1)
    (uniformScale delta hdelta_le_one r).property.2
    le_rfl (F.tube i) (hF_ball i)
    ((U.coarse r).tube j)
    ((U.coarse r).tube ((U.cover r).parent i))
    hj_contains ((U.cover r).nested i)

end DilatedDiscreteUniformTubeStructure

/--
At every distinguished scale, one fine tube has only `O_A(1)` geometric
parents in an essentially-distinct dilated cover.
-/
def IndependentDilatedCoverOverlapStatement (A : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ delta : ℝ, 0 < delta →
      ∀ hdelta_le_one : delta ≤ 1,
      ∀ F : TubeFamily delta,
        F.IsInUnitBall →
        ∀ U : DilatedDiscreteUniformTubeStructure
            (A := A) F hdelta_le_one,
          ∀ r : UniformScaleIndex delta,
          ∀ i : Fin F.card,
            ((U.containingParentIndices r i).card : ℝ) ≤ C

theorem independent_dilated_cover_overlap
    (A : ℝ) (hA : 1 ≤ A) :
    IndependentDilatedCoverOverlapStatement A := by
  rcases DilatedDiscreteUniformTubeStructure.contained_parent_packing A hA with
    ⟨C, hC, hpacking⟩
  refine ⟨C, hC, ?_⟩
  intro delta hdelta hdelta_le_one F hF_ball U r i
  have hsubset :
      U.containingParentIndices r i ⊆
        U.containedParentIndices r r ((U.cover r).parent i) :=
    U.containingParentIndices_subset_containedParentIndices
      hA hdelta hF_ball r i
  have hcard_nat :
      (U.containingParentIndices r i).card ≤
        (U.containedParentIndices r r ((U.cover r).parent i)).card :=
    Finset.card_le_card hsubset
  have hcard_real :
      ((U.containingParentIndices r i).card : ℝ) ≤
        ((U.containedParentIndices r r ((U.cover r).parent i)).card : ℝ) := by
    exact_mod_cast hcard_nat
  have hpack :=
    hpacking delta hdelta hdelta_le_one F U r r le_rfl
      ((U.cover r).parent i)
  calc
    ((U.containingParentIndices r i).card : ℝ)
        ≤ ((U.containedParentIndices r r
            ((U.cover r).parent i)).card : ℝ) := hcard_real
    _ ≤ C *
        ((uniformScale delta hdelta_le_one r).1 /
          (uniformScale delta hdelta_le_one r).1) ^ 4 := hpack
    _ = C := by
      have hscale_pos :
          0 < (uniformScale delta hdelta_le_one r).1 :=
        lt_of_lt_of_le hdelta
          (uniformScale delta hdelta_le_one r).property.1
      field_simp [hscale_pos.ne']

end Kakeya.Streamlined
