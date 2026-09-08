import MyLeanRepo.Kakeya.Streamlined.DividingScales.ConditionalFactorProfiles

/-!
# Katz-Tao deltaMax profiles on conditional factor scopes

This module defines the deltaMax analogs of the Frostman profile infrastructure.

## Global level

* `relationDeltaMaxMax` — maximum over coarse parents of `assignedRelationDeltaMax`.
* `fullRelationDeltaMaxMax` — canonical maximum over coarse parents of the
  full-containment `relationDeltaMax`.

## Conditional factor scope level

* `representedRelationDeltaMax` — deltaMax of one represented conditional
  relation family.
* `relationDeltaMax` — maximum over all represented branches.
* `intermediateDeltaMax` — scope profile used by the abstract stopping logic.

We prove the standard max-le-iff and le-max-iff equivalences, inner-child
equality, and root equality with the global profile.

The root deltaMax is bounded directly by the ambient `F.deltaMax` with no
container loss, because deltaMax is an intrinsic property of the body
carriers and the root relation family is carrier-equivalent to `F`.
-/

noncomputable section

namespace Kakeya.Streamlined

namespace DilatedDiscreteUniformTubeStructure

variable {delta A : ℝ} {F : TubeFamily delta}
variable {hdelta_le_one : delta ≤ 1}
variable (U : DilatedDiscreteUniformTubeStructure
  (A := A) F hdelta_le_one)

/-- The largest assigned relation-fiber deltaMax from `r` to `s`. -/
def relationDeltaMaxMax
    (hF : F.Nonempty)
    (r s : UniformScaleIndex delta) : ENNReal :=
  Finset.univ.sup' (by
    let i : Fin F.card := ⟨0, hF⟩
    exact ⟨(U.cover s).parent i, Finset.mem_univ _⟩)
    (U.assignedRelationDeltaMax r s)

/--
The canonical full-containment relation profile.  This is the same full-fiber
maximum used by `FactorLocalProfileUniformTubeStructure.fullRelationDeltaMaxMax`,
without requiring the extra profile-comparability structure.
-/
def fullRelationDeltaMaxMax
    (r s : UniformScaleIndex delta) : ENNReal :=
  Finset.univ.sup (U.relationDeltaMax r s)

/-- Every relation-fiber deltaMax is bounded by the profile maximum. -/
lemma assignedRelationDeltaMax_le_max
    (hF : F.Nonempty)
    (r s : UniformScaleIndex delta)
    (k : Fin (U.coarse s).card) :
    U.assignedRelationDeltaMax r s k ≤
      U.relationDeltaMaxMax hF r s := by
  exact Finset.le_sup' _ (Finset.mem_univ k)

/-- A uniform relation-fiber upper bound is equivalent to the maximum bound. -/
lemma relationDeltaMaxMax_le_iff
    (hF : F.Nonempty)
    (r s : UniformScaleIndex delta) (C : ENNReal) :
    U.relationDeltaMaxMax hF r s ≤ C ↔
      ∀ k : Fin (U.coarse s).card,
        U.assignedRelationDeltaMax r s k ≤ C := by
  constructor
  · intro h k
    exact (U.assignedRelationDeltaMax_le_max hF r s k).trans h
  · intro h
    exact Finset.sup'_le _ _ fun k _ => h k

/-- A lower bound for the relation profile maximum has a parent witness. -/
lemma le_relationDeltaMaxMax_iff
    (hF : F.Nonempty)
    (r s : UniformScaleIndex delta) (C : ENNReal) :
    C ≤ U.relationDeltaMaxMax hF r s ↔
      ∃ k : Fin (U.coarse s).card,
        C ≤ U.assignedRelationDeltaMax r s k := by
  let indices : Finset (Fin (U.coarse s).card) := Finset.univ
  have hindices : indices.Nonempty := by
    let i : Fin F.card := ⟨0, hF⟩
    exact ⟨(U.cover s).parent i, Finset.mem_univ _⟩
  have hmax :=
    Finset.exists_mem_eq_sup' hindices
      (U.assignedRelationDeltaMax r s)
  rcases hmax with ⟨kmax, _hkmax, hkmax⟩
  constructor
  · intro h
    refine ⟨kmax, ?_⟩
    rw [← hkmax]
    exact h
  · rintro ⟨k, hk⟩
    exact hk.trans <| Finset.le_sup' _ (Finset.mem_univ k)

/--
The assigned maximum is bounded by the canonical full-containment maximum.
This uses only relation inclusion and `deltaMax` monotonicity; it does not
assert that the independent parent maps form a tree.
-/
lemma relationDeltaMaxMax_le_fullRelationDeltaMaxMax
    (hA : 1 ≤ A) (hdelta : 0 < delta)
    (hF : F.Nonempty) (hF_ball : F.IsInUnitBall)
    (r s : UniformScaleIndex delta)
    (hrs :
      (uniformScale delta hdelta_le_one r).1 ≤
        (uniformScale delta hdelta_le_one s).1) :
    U.relationDeltaMaxMax hF r s ≤
      U.fullRelationDeltaMaxMax r s := by
  rw [U.relationDeltaMaxMax_le_iff hF r s]
  intro k
  exact
    (U.assignedRelationDeltaMax_le_relationDeltaMax
      hA hdelta hF_ball r s hrs k).trans
      (Finset.le_sup (s := Finset.univ)
        (f := U.relationDeltaMax r s)
        (Finset.mem_univ k))

end DilatedDiscreteUniformTubeStructure

namespace FrostmanConditionalFactorScope

variable {depth : ℕ} {delta A C : ℝ} {F : TubeFamily delta}
variable {hdelta_le_one : delta ≤ 1}
variable {U : ConditionallyUniformLocalDilatedDiscreteUniformTubeStructure
  depth (A := A) (C := C) F hdelta_le_one}

/-- Katz-Tao deltaMax of one represented conditional relation family. -/
def representedRelationDeltaMax
    (P : FrostmanConditionalFactorScope U)
    (i : Fin F.card)
    (r s : UniformScaleIndex delta) : ENNReal :=
  (P.relationSubfamily i r s).family.toBodyFamily.deltaMax

/-- Maximum represented relation deltaMax on a scope. -/
def relationDeltaMax
    (hF : F.Nonempty)
    (P : FrostmanConditionalFactorScope U)
    (r s : UniformScaleIndex delta) : ENNReal :=
  Finset.univ.sup' (by
    let i : Fin F.card := ⟨0, hF⟩
    exact ⟨i, Finset.mem_univ i⟩)
    fun i => P.representedRelationDeltaMax i r s

/-- Every represented relation deltaMax is bounded by the scope maximum. -/
lemma representedRelationDeltaMax_le_max
    (hF : F.Nonempty)
    (P : FrostmanConditionalFactorScope U)
    (i : Fin F.card)
    (r s : UniformScaleIndex delta) :
    P.representedRelationDeltaMax i r s ≤
      P.relationDeltaMax hF r s := by
  exact Finset.le_sup'
    (fun original : Fin F.card =>
      P.representedRelationDeltaMax original r s)
    (Finset.mem_univ i)

/-- A uniform represented upper bound is equivalent to the scope maximum. -/
lemma relationDeltaMax_le_iff
    (hF : F.Nonempty)
    (P : FrostmanConditionalFactorScope U)
    (r s : UniformScaleIndex delta)
    (bound : ENNReal) :
    P.relationDeltaMax hF r s ≤ bound ↔
      ∀ i : Fin F.card,
        P.representedRelationDeltaMax i r s ≤ bound := by
  constructor
  · intro h i
    exact (P.representedRelationDeltaMax_le_max hF i r s).trans h
  · intro h
    exact Finset.sup'_le _ _ fun i _ => h i

/-- A lower bound for the scope maximum has a represented-cell witness. -/
lemma le_relationDeltaMax_iff
    (hF : F.Nonempty)
    (P : FrostmanConditionalFactorScope U)
    (r s : UniformScaleIndex delta)
    (bound : ENNReal) :
    bound ≤ P.relationDeltaMax hF r s ↔
      ∃ i : Fin F.card,
        bound ≤ P.representedRelationDeltaMax i r s := by
  let indices : Finset (Fin F.card) := Finset.univ
  have hindices : indices.Nonempty := by
    let i : Fin F.card := ⟨0, hF⟩
    exact ⟨i, Finset.mem_univ i⟩
  rcases Finset.exists_mem_eq_sup' hindices
      (fun i => P.representedRelationDeltaMax i r s) with
    ⟨imax, _himax, himax⟩
  constructor
  · intro h
    refine ⟨imax, ?_⟩
    rw [← himax]
    exact h
  · rintro ⟨i, hi⟩
    exact hi.trans <| Finset.le_sup'
      (fun original : Fin F.card =>
        P.representedRelationDeltaMax original r s)
      (Finset.mem_univ i)

/-- Scope profile used by the abstract stopping logic. -/
def intermediateDeltaMax
    (hF : F.Nonempty)
    (P : FrostmanConditionalFactorScope U)
    (q : UniformScaleIndex delta) : ENNReal :=
  P.relationDeltaMax hF P.fine q

/--
For the inner child, the represented fine-to-middle relation image is exactly
the parent scope's fine-to-middle relation image.
-/
lemma innerChild_representedRelationDeltaMax
    (P : FrostmanConditionalFactorScope U)
    (hroom : P.coordinateCount < depth)
    (middle : UniformScaleIndex delta)
    (hfine_middle :
      (uniformScale delta hdelta_le_one P.fine).1 ≤
        (uniformScale delta hdelta_le_one middle).1)
    (i : Fin F.card) :
    representedRelationDeltaMax
        (P.innerChild hroom middle hfine_middle) i P.fine middle =
      P.representedRelationDeltaMax i P.fine middle := by
  unfold representedRelationDeltaMax
  unfold relationSubfamily
  congr 2
  rw [innerChild_relationIndices]

/-- Inner-child maximum equals the parent intermediate maximum. -/
lemma innerChild_relationDeltaMax
    (hF : F.Nonempty)
    (P : FrostmanConditionalFactorScope U)
    (hroom : P.coordinateCount < depth)
    (middle : UniformScaleIndex delta)
    (hfine_middle :
      (uniformScale delta hdelta_le_one P.fine).1 ≤
        (uniformScale delta hdelta_le_one middle).1) :
    relationDeltaMax hF
        (P.innerChild hroom middle hfine_middle) P.fine middle =
      P.relationDeltaMax hF P.fine middle := by
  apply le_antisymm
  · rw [relationDeltaMax_le_iff]
    intro i
    rw [innerChild_representedRelationDeltaMax]
    exact P.representedRelationDeltaMax_le_max hF i P.fine middle
  · rw [relationDeltaMax_le_iff]
    intro i
    rw [← innerChild_representedRelationDeltaMax]
    exact
      representedRelationDeltaMax_le_max hF
        (P.innerChild hroom middle hfine_middle) i P.fine middle

/-- Root represented profile is the existing assigned relation deltaMax. -/
lemma root_representedRelationDeltaMax
    (hdelta : 0 < delta)
    (i : Fin F.card)
    (r s : UniformScaleIndex delta) :
    (FrostmanConditionalFactorState.rootFactor
        (U := U) hdelta).representedRelationDeltaMax i r s =
      DilatedDiscreteUniformTubeStructure.assignedRelationDeltaMax
        U.toLocalDilatedDiscreteUniformTubeStructure.toDilated
        r s ((U.cover s).parent i) := by
  unfold representedRelationDeltaMax
  unfold DilatedDiscreteUniformTubeStructure.assignedRelationDeltaMax
  unfold relationSubfamily
  unfold DilatedDiscreteUniformTubeStructure.relatedSubfamily
  dsimp only [LocalDilatedDiscreteUniformTubeStructure.toDilated]
  congr 2
  rw [root_relationIndices_eq_relatedIndices]
  rfl

/--
The root scope maximum is exactly the existing global assigned relation
deltaMax profile.  Surjectivity of the endpoint cover ensures every parent
is represented by some original fine index.
-/
lemma root_relationDeltaMax
    (hdelta : 0 < delta)
    (hF : F.Nonempty)
    (r s : UniformScaleIndex delta) :
    (FrostmanConditionalFactorState.rootFactor
        (U := U) hdelta).relationDeltaMax hF r s =
      DilatedDiscreteUniformTubeStructure.relationDeltaMaxMax
        U.toLocalDilatedDiscreteUniformTubeStructure.toDilated hF r s := by
  let D := U.toLocalDilatedDiscreteUniformTubeStructure.toDilated
  apply le_antisymm
  · rw [relationDeltaMax_le_iff]
    intro i
    rw [root_representedRelationDeltaMax]
    exact
      DilatedDiscreteUniformTubeStructure.assignedRelationDeltaMax_le_max
        D hF r s ((U.cover s).parent i)
  · rw [DilatedDiscreteUniformTubeStructure.relationDeltaMaxMax_le_iff
        D hF r s]
    intro k
    rcases (U.cover s).parent_surjective k with ⟨i, hi⟩
    rw [← hi, ← root_representedRelationDeltaMax]
    exact
      (FrostmanConditionalFactorState.rootFactor
        (U := U) hdelta).representedRelationDeltaMax_le_max hF i r s

/--
The root represented deltaMax at the canonical endpoints is bounded by the
ambient family deltaMax.

At the finest-to-unit-scale root interval, the relation subfamily contains
all finest-scale parents, which are carrier-equivalent to the original
family `F`.  Therefore its deltaMax is at most `F.deltaMax`.
-/
lemma root_representedRelationDeltaMax_le_ambient
    (hdelta : 0 < delta)
    (hF : F.Nonempty)
    (i : Fin F.card) :
    (FrostmanConditionalFactorState.rootFactor
        (U := U) hdelta).representedRelationDeltaMax i
        (Fin.last (uniformScaleSteps delta))
        (⟨0, Nat.succ_pos _⟩ : UniformScaleIndex delta) ≤
      F.toBodyFamily.deltaMax := by
  let r0 := Fin.last (uniformScaleSteps delta)
  let s0 : UniformScaleIndex delta := ⟨0, Nat.succ_pos _⟩
  let P := FrostmanConditionalFactorState.rootFactor (U := U) hdelta
  let relSub := P.relationSubfamily i r0 s0
  -- The relation subfamily is a subfamily of U.coarse r0
  have h1 : relSub.family.toBodyFamily.deltaMax ≤
        (U.coarse r0).toBodyFamily.deltaMax :=
    subfamily_deltaMax_le relSub.toBodySubfamily
  -- U.coarse r0 is carrier-equivalent to F, so its deltaMax ≤ F.deltaMax
  have h2 : (U.coarse r0).toBodyFamily.deltaMax ≤
        F.toBodyFamily.deltaMax := by
    let S : Subfamily F.toBodyFamily :=
      finestCoarseAsBodySubfamily (U := U)
    exact subfamily_deltaMax_le S
  exact h1.trans h2

/--
The root scope maximum at the canonical endpoints is bounded by the ambient
family deltaMax.
-/
lemma root_relationDeltaMax_le_ambient
    (hdelta : 0 < delta)
    (hF : F.Nonempty) :
    (FrostmanConditionalFactorState.rootFactor
        (U := U) hdelta).relationDeltaMax hF
        (Fin.last (uniformScaleSteps delta))
        (⟨0, Nat.succ_pos _⟩ : UniformScaleIndex delta) ≤
      F.toBodyFamily.deltaMax := by
  rw [relationDeltaMax_le_iff]
  intro i
  exact root_representedRelationDeltaMax_le_ambient hdelta hF i

end FrostmanConditionalFactorScope

end Kakeya.Streamlined
