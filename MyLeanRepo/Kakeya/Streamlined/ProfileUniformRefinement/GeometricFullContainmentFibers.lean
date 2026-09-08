import MyLeanRepo.Kakeya.Streamlined.TubeRefinement
import MyLeanRepo.Kakeya.Streamlined.UniformRefinement.SingleScaleCover
import MyLeanRepo.Kakeya.Streamlined.DilatedTubeCover.FullContainmentFibers

/-!
# Parent-map-free geometric containment fibers

These are the paper fibers determined solely by tube containment in a fixed
dilation of a coarse tube.  No assigned parent map is part of the API.
-/

noncomputable section

namespace Kakeya.Streamlined

/-- Fine indices geometrically contained in one coarse tube. -/
def restrictedContainedFineIndices
    {delta rho A : ℝ}
    {fine : TubeFamily delta} {coarse : TubeFamily rho}
    (j : Fin coarse.card) : Finset (Fin fine.card) := by
  classical
  exact Finset.univ.filter fun i =>
    (fine.tube i).carrier ⊆
      dilatedTubeCarrier A (coarse.tube j)

@[simp]
lemma mem_restrictedContainedFineIndices_iff
    {delta rho A : ℝ}
    {fine : TubeFamily delta} {coarse : TubeFamily rho}
    (j : Fin coarse.card) (i : Fin fine.card) :
    i ∈ restrictedContainedFineIndices
        (A := A) (fine := fine) (coarse := coarse) j ↔
      (fine.tube i).carrier ⊆
        dilatedTubeCarrier A (coarse.tube j) := by
  simp [restrictedContainedFineIndices]

/-- Fine indices geometrically contained in at least one selected parent. -/
def selectedContainedFineIndices
    {delta rho A : ℝ}
    {fine : TubeFamily delta} {coarse : TubeFamily rho}
    (selected : Finset (Fin coarse.card)) :
    Finset (Fin fine.card) := by
  classical
  exact Finset.univ.filter fun i =>
    ∃ j ∈ selected,
      (fine.tube i).carrier ⊆
        dilatedTubeCarrier A (coarse.tube j)

/-- Cardinality of one parent-map-free full geometric fiber. -/
def geometricFullContainmentFiberCount
    {delta rho A : ℝ}
    (fine : TubeFamily delta) (coarse : TubeFamily rho)
    (j : Fin coarse.card) : ENNReal :=
  ((restrictedContainedFineIndices
    (A := A) (fine := fine) (coarse := coarse) j).card : ENNReal)

/-- Frostman profile of one parent-map-free full geometric fiber. -/
def geometricFullContainmentFiberFrostmanConstant
    {delta rho A : ℝ}
    (fine : TubeFamily delta) (coarse : TubeFamily rho)
    (j : Fin coarse.card) : ENNReal :=
  (TubeSubfamily.fromFinset fine
      (restrictedContainedFineIndices
        (A := A) (fine := fine) (coarse := coarse) j)
    ).family.toBodyFamily.frostmanConstantIn
      (dilatedTubeCarrier A (coarse.tube j))

/-- Maximal-density profile of one parent-map-free full geometric fiber. -/
def geometricFullContainmentFiberDeltaMax
    {delta rho A : ℝ}
    (fine : TubeFamily delta) (coarse : TubeFamily rho)
    (j : Fin coarse.card) : ENNReal :=
  (TubeSubfamily.fromFinset fine
      (restrictedContainedFineIndices
        (A := A) (fine := fine) (coarse := coarse) j)
    ).family.toBodyFamily.deltaMax

/-- One geometric fine/coarse pair has uniform full-containment fibers. -/
def GeometricFullContainmentFibersAreCUniform
    {delta rho A : ℝ}
    (fine : TubeFamily delta) (coarse : TubeFamily rho)
    (C : ENNReal) : Prop :=
  1 ≤ C ∧
    ∀ j k,
      geometricFullContainmentFiberCount (A := A) fine coarse j ≤
        C * geometricFullContainmentFiberCount (A := A) fine coarse k

/-- Full geometric fibers have pairwise comparable Frostman profiles. -/
def GeometricFullContainmentFrostmanProfilesAreCUniform
    {delta rho A : ℝ}
    (fine : TubeFamily delta) (coarse : TubeFamily rho)
    (C : ENNReal) : Prop :=
  ∀ j k,
    ComparableBy C
      (geometricFullContainmentFiberFrostmanConstant
        (A := A) fine coarse j)
      (geometricFullContainmentFiberFrostmanConstant
        (A := A) fine coarse k)

/-- Full geometric fibers have pairwise comparable `deltaMax` profiles. -/
def GeometricFullContainmentDeltaMaxProfilesAreCUniform
    {delta rho A : ℝ}
    (fine : TubeFamily delta) (coarse : TubeFamily rho)
    (C : ENNReal) : Prop :=
  ∀ j k,
    ComparableBy C
      (geometricFullContainmentFiberDeltaMax
        (A := A) fine coarse j)
      (geometricFullContainmentFiberDeltaMax
        (A := A) fine coarse k)

/--
The cover-valued and parent-map-free full-fiber predicates are definitionally
the same once the fine and coarse tube families are fixed.
-/
lemma geometricFullContainmentFibersAreCUniform_iff_cover
    {delta rho A : ℝ}
    {fine : TubeFamily delta} {coarse : TubeFamily rho}
    (P : DilatedTubeCover A fine coarse) (C : ENNReal) :
    GeometricFullContainmentFibersAreCUniform
        (A := A) fine coarse C ↔
      P.FullContainmentFibersAreCUniform C := by
  rfl

/-- Full-fiber uniformity is monotone in its comparison constant. -/
lemma GeometricFullContainmentFibersAreCUniform.mono
    {delta rho A : ℝ}
    {fine : TubeFamily delta} {coarse : TubeFamily rho}
    {C D : ENNReal}
    (huniform :
      GeometricFullContainmentFibersAreCUniform
        (A := A) fine coarse C)
    (hCD : C ≤ D) :
    GeometricFullContainmentFibersAreCUniform
      (A := A) fine coarse D := by
  refine ⟨huniform.1.trans hCD, ?_⟩
  intro j k
  exact
    (huniform.2 j k).trans
      (mul_le_mul_right' hCD
        (geometricFullContainmentFiberCount
          (A := A) fine coarse k))

/-- The branching number represented by the largest geometric full fiber. -/
def geometricFullContainmentBranchingNumber
    {delta rho A : ℝ}
    (fine : TubeFamily delta) (coarse : TubeFamily rho) : ENNReal :=
  Finset.univ.sup fun j =>
    geometricFullContainmentFiberCount (A := A) fine coarse j

/-- A full-containment branching number never exceeds the fine cardinality. -/
lemma geometricFullContainmentBranchingNumber_le_enncard
    {delta rho A : ℝ}
    (fine : TubeFamily delta) (coarse : TubeFamily rho) :
    geometricFullContainmentBranchingNumber
        (A := A) fine coarse ≤
      fine.enncard := by
  classical
  apply Finset.sup_le
  intro j _
  dsimp only [geometricFullContainmentFiberCount, TubeFamily.enncard]
  have hcard :
      (restrictedContainedFineIndices
        (A := A) (fine := fine) (coarse := coarse) j).card ≤
        fine.card := by
    simpa using
      (Finset.card_le_univ
        (restrictedContainedFineIndices
          (A := A) (fine := fine) (coarse := coarse) j))
  exact_mod_cast hcard

/--
If every fine tube is assigned to a geometrically containing coarse tube,
then the parent-map-free branching number is at least one.
-/
lemma one_le_geometricFullContainmentBranchingNumber
    {delta rho A : ℝ}
    {fine : TubeFamily delta} {coarse : TubeFamily rho}
    (hfine : fine.Nonempty)
    (covered :
      ∀ i : Fin fine.card,
        ∃ j : Fin coarse.card,
          (fine.tube i).carrier ⊆
            dilatedTubeCarrier A (coarse.tube j)) :
    1 ≤ geometricFullContainmentBranchingNumber
      (A := A) fine coarse := by
  classical
  let i : Fin fine.card := ⟨0, hfine⟩
  rcases covered i with ⟨j, hj⟩
  have hi :
      i ∈ restrictedContainedFineIndices
        (A := A) (fine := fine) (coarse := coarse) j :=
    (mem_restrictedContainedFineIndices_iff j i).2 hj
  have hcard :
      1 ≤
        (restrictedContainedFineIndices
          (A := A) (fine := fine) (coarse := coarse) j).card := by
    exact Finset.one_le_card.mpr ⟨i, hi⟩
  have hcount :
      (1 : ENNReal) ≤
        geometricFullContainmentFiberCount
          (A := A) fine coarse j := by
    dsimp only [geometricFullContainmentFiberCount]
    exact_mod_cast hcard
  exact hcount.trans
    (Finset.le_sup
      (f := fun parent =>
        geometricFullContainmentFiberCount
          (A := A) fine coarse parent)
      (Finset.mem_univ j))

end Kakeya.Streamlined
