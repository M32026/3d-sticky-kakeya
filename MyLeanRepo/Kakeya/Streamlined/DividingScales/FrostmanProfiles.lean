import MyLeanRepo.Kakeya.Streamlined.DividingScales.ReferenceDensity

/-!
# Finite Frostman profiles on the paper grid

Endpoint upper bounds and central existential obstructions are encoded by
finite maxima over parent indices.  This turns the stopping-time recursion
into a scalar finite problem without imposing false profile uniformity across
different parents.
-/

noncomputable section

namespace Kakeya.Streamlined

namespace DilatedDiscreteUniformTubeStructure

variable {delta A : ℝ} {F : TubeFamily delta}
variable {hdelta_le_one : delta ≤ 1}
variable (U : DilatedDiscreteUniformTubeStructure
  (A := A) F hdelta_le_one)

/-- The largest assigned fine-fiber Frostman constant at scale `r`. -/
def fineFrostmanMax
    (hF : F.Nonempty)
    (r : UniformScaleIndex delta) : ENNReal :=
  Finset.univ.sup' (by
    let i : Fin F.card := ⟨0, hF⟩
    exact ⟨(U.cover r).parent i, Finset.mem_univ _⟩)
    (U.assignedFineFiberFrostmanConstant r)

/-- The largest assigned relation-fiber Frostman constant from `r` to `s`. -/
def relationFrostmanMax
    (hF : F.Nonempty)
    (r s : UniformScaleIndex delta) : ENNReal :=
  Finset.univ.sup' (by
    let i : Fin F.card := ⟨0, hF⟩
    exact ⟨(U.cover s).parent i, Finset.mem_univ _⟩)
    (U.assignedRelationFrostmanConstant r s)

/-- Every fine-fiber constant is bounded by the profile maximum. -/
lemma fineFiberFrostmanConstant_le_max
    (hF : F.Nonempty)
    (r : UniformScaleIndex delta)
    (k : Fin (U.coarse r).card) :
    U.assignedFineFiberFrostmanConstant r k ≤
      U.fineFrostmanMax hF r := by
  exact Finset.le_sup' _ (Finset.mem_univ k)

/-- Every relation-fiber constant is bounded by the profile maximum. -/
lemma relationFrostmanConstant_le_max
    (hF : F.Nonempty)
    (r s : UniformScaleIndex delta)
    (k : Fin (U.coarse s).card) :
    U.assignedRelationFrostmanConstant r s k ≤
      U.relationFrostmanMax hF r s := by
  exact Finset.le_sup' _ (Finset.mem_univ k)

/-- A uniform fine-fiber upper bound is equivalent to the maximum bound. -/
lemma fineFrostmanMax_le_iff
    (hF : F.Nonempty)
    (r : UniformScaleIndex delta) (C : ENNReal) :
    U.fineFrostmanMax hF r ≤ C ↔
      ∀ k : Fin (U.coarse r).card,
        U.assignedFineFiberFrostmanConstant r k ≤ C := by
  constructor
  · intro h k
    exact (U.fineFiberFrostmanConstant_le_max hF r k).trans h
  · intro h
    exact Finset.sup'_le _ _ fun k _ => h k

/-- A uniform relation-fiber upper bound is equivalent to the maximum bound. -/
lemma relationFrostmanMax_le_iff
    (hF : F.Nonempty)
    (r s : UniformScaleIndex delta) (C : ENNReal) :
    U.relationFrostmanMax hF r s ≤ C ↔
      ∀ k : Fin (U.coarse s).card,
        U.assignedRelationFrostmanConstant r s k ≤ C := by
  constructor
  · intro h k
    exact (U.relationFrostmanConstant_le_max hF r s k).trans h
  · intro h
    exact Finset.sup'_le _ _ fun k _ => h k

/-- A lower bound for the relation profile maximum has a parent witness. -/
lemma le_relationFrostmanMax_iff
    (hF : F.Nonempty)
    (r s : UniformScaleIndex delta) (C : ENNReal) :
    C ≤ U.relationFrostmanMax hF r s ↔
      ∃ k : Fin (U.coarse s).card,
        C ≤ U.assignedRelationFrostmanConstant r s k := by
  let indices : Finset (Fin (U.coarse s).card) := Finset.univ
  have hindices : indices.Nonempty := by
    let i : Fin F.card := ⟨0, hF⟩
    exact ⟨(U.cover s).parent i, Finset.mem_univ _⟩
  have hmax :=
    Finset.exists_mem_eq_sup' hindices
      (U.assignedRelationFrostmanConstant r s)
  rcases hmax with ⟨kmax, _hkmax, hkmax⟩
  constructor
  · intro h
    refine ⟨kmax, ?_⟩
    rw [← hkmax]
    exact h
  · rintro ⟨k, hk⟩
    exact hk.trans <|
      Finset.le_sup' _ (Finset.mem_univ k)

end DilatedDiscreteUniformTubeStructure

end Kakeya.Streamlined
