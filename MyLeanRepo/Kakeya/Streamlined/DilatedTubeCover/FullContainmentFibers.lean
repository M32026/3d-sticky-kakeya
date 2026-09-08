import MyLeanRepo.Kakeya.Streamlined.DilatedTubeCover.AssignedFiberProfiles

/-!
# Full geometric containment fibers of a dilated tube cover

The `parent` field of a `DilatedTubeCover` is an auxiliary surjective choice
used for disjoint bookkeeping.  The paper fiber over a coarse tube consists of
every fine tube geometrically contained in the prescribed dilation of that
coarse tube, independently of the chosen parent.

This module provides that canonical single-scale interface directly on
`DilatedTubeCover`.  Higher all-scale structures should reuse these definitions
rather than defining a second notion of full containment fiber.
-/

noncomputable section

namespace Kakeya.Streamlined

namespace DilatedTubeCover

/-- All fine indices geometrically contained in the dilation of one parent. -/
def fullContainmentFiberIndices
    {delta rho A : ℝ}
    {fine : TubeFamily delta} {coarse : TubeFamily rho}
    (P : DilatedTubeCover A fine coarse)
    (j : Fin coarse.card) : Finset (Fin fine.card) := by
  classical
  exact Finset.univ.filter fun i =>
    (fine.tube i).carrier ⊆ dilatedTubeCarrier A (coarse.tube j)

@[simp]
lemma mem_fullContainmentFiberIndices_iff
    {delta rho A : ℝ}
    {fine : TubeFamily delta} {coarse : TubeFamily rho}
    (P : DilatedTubeCover A fine coarse)
    (j : Fin coarse.card)
    (i : Fin fine.card) :
    i ∈ P.fullContainmentFiberIndices j ↔
      (fine.tube i).carrier ⊆ dilatedTubeCarrier A (coarse.tube j) := by
  simp [fullContainmentFiberIndices]

/-- The complete geometric containment fiber over one coarse parent. -/
def fullContainmentFiberSubfamily
    {delta rho A : ℝ}
    {fine : TubeFamily delta} {coarse : TubeFamily rho}
    (P : DilatedTubeCover A fine coarse)
    (j : Fin coarse.card) : TubeSubfamily fine :=
  TubeSubfamily.fromFinset fine (P.fullContainmentFiberIndices j)

/-- Cardinality of one complete geometric containment fiber. -/
def fullContainmentFiberCount
    {delta rho A : ℝ}
    {fine : TubeFamily delta} {coarse : TubeFamily rho}
    (P : DilatedTubeCover A fine coarse)
    (j : Fin coarse.card) : ENNReal :=
  (P.fullContainmentFiberIndices j).card

/-- Full geometric containment fibers have comparable cardinalities. -/
def FullContainmentFibersAreCUniform
    {delta rho A : ℝ}
    {fine : TubeFamily delta} {coarse : TubeFamily rho}
    (P : DilatedTubeCover A fine coarse)
    (C : ENNReal) : Prop :=
  1 ≤ C ∧
    ∀ first second,
      P.fullContainmentFiberCount first ≤
        C * P.fullContainmentFiberCount second

/--
Canonical paper-facing uniformity predicate for a dilated cover.

It depends only on complete geometric containment fibers and ignores the
auxiliary parent assignment.
-/
def IsCUniform
    {delta rho A : ℝ}
    {fine : TubeFamily delta} {coarse : TubeFamily rho}
    (P : DilatedTubeCover A fine coarse)
    (C : ENNReal) : Prop :=
  P.FullContainmentFibersAreCUniform C

/--
Assigned parents that own at least one fine tube in the full geometric fiber
of `j`.
-/
def fullContainmentOwnerParents
    {delta rho A : ℝ}
    {fine : TubeFamily delta} {coarse : TubeFamily rho}
    (P : DilatedTubeCover A fine coarse)
    (j : Fin coarse.card) : Finset (Fin coarse.card) :=
  (P.fullContainmentFiberIndices j).image P.parent

/-- Frostman profile of one complete geometric containment fiber. -/
def fullContainmentFiberFrostmanConstant
    {delta rho A : ℝ}
    {fine : TubeFamily delta} {coarse : TubeFamily rho}
    (P : DilatedTubeCover A fine coarse)
    (j : Fin coarse.card) : ENNReal :=
  (P.fullContainmentFiberSubfamily j).family.toBodyFamily.frostmanConstantIn
    (dilatedTubeCarrier A (coarse.tube j))

/-- Maximal-density profile of one complete geometric containment fiber. -/
def fullContainmentFiberDeltaMax
    {delta rho A : ℝ}
    {fine : TubeFamily delta} {coarse : TubeFamily rho}
    (P : DilatedTubeCover A fine coarse)
    (j : Fin coarse.card) : ENNReal :=
  (P.fullContainmentFiberSubfamily j).family.toBodyFamily.deltaMax

/-- The factoring fiber is contained in the paper full fiber. -/
lemma factoringFiberIndices_subset_fullContainmentFiberIndices
    {delta rho A : ℝ}
    {fine : TubeFamily delta} {coarse : TubeFamily rho}
    (P : DilatedTubeCover A fine coarse)
    (j : Fin coarse.card) :
    P.toFactoring.fiberIndices j ⊆ P.fullContainmentFiberIndices j := by
  change
    (Finset.univ.filter fun i : Fin fine.card => P.parent i = j) ⊆
      P.fullContainmentFiberIndices j
  intro i hi
  have hparent : P.parent i = j :=
    (Finset.mem_filter.mp hi).2
  rw [P.mem_fullContainmentFiberIndices_iff j i]
  simpa [hparent] using P.nested i

/-- The factoring-fiber cardinality is bounded by the paper full fiber. -/
lemma factoringFiberCount_le_fullContainmentFiberCount
    {delta rho A : ℝ}
    {fine : TubeFamily delta} {coarse : TubeFamily rho}
    (P : DilatedTubeCover A fine coarse)
    (j : Fin coarse.card) :
    P.toFactoring.fiberCount j ≤ P.fullContainmentFiberCount j := by
  change
    ((Finset.univ.filter fun i : Fin fine.card =>
      P.parent i = j).card : ENNReal) ≤
      ((P.fullContainmentFiberIndices j).card : ENNReal)
  exact_mod_cast
    Finset.card_le_card
      (P.factoringFiberIndices_subset_fullContainmentFiberIndices j)

/--
Every fine tube in a full geometric fiber lies in the assigned fiber of one
owner parent represented in `fullContainmentOwnerParents`.
-/
lemma fullContainmentFiberIndices_subset_ownerAssignedUnion
    {delta rho A : ℝ}
    {fine : TubeFamily delta} {coarse : TubeFamily rho}
    (P : DilatedTubeCover A fine coarse)
    (j : Fin coarse.card) :
    P.fullContainmentFiberIndices j ⊆
      (P.fullContainmentOwnerParents j).biUnion
        P.toFactoring.fiberIndices := by
  intro i hi
  refine Finset.mem_biUnion.mpr ⟨P.parent i, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, rfl⟩

/--
Assigned-fiber uniformity and a bound on the number of owner parents control
one full geometric fiber by every other full geometric fiber.
-/
lemma fullContainmentFiberCount_le_of_ownerCount
    {delta rho A : ℝ}
    {fine : TubeFamily delta} {coarse : TubeFamily rho}
    (P : DilatedTubeCover A fine coarse)
    {C M : ENNReal}
    (hUniform : P.toFactoring.FibersAreCUniform C)
    (hOwner :
      ∀ j, ((P.fullContainmentOwnerParents j).card : ENNReal) ≤ M)
    (first second : Fin coarse.card) :
    P.fullContainmentFiberCount first ≤
      M * C * P.fullContainmentFiberCount second := by
  have hSubset :=
    P.fullContainmentFiberIndices_subset_ownerAssignedUnion first
  have hCardSubset :
      P.fullContainmentFiberCount first ≤
        (((P.fullContainmentOwnerParents first).biUnion
          P.toFactoring.fiberIndices).card : ENNReal) := by
    unfold fullContainmentFiberCount
    exact_mod_cast Finset.card_le_card hSubset
  have hUnion :
      (((P.fullContainmentOwnerParents first).biUnion
          P.toFactoring.fiberIndices).card : ENNReal) ≤
        ∑ parent ∈ P.fullContainmentOwnerParents first,
          P.toFactoring.fiberCount parent := by
    change
      (((P.fullContainmentOwnerParents first).biUnion
          P.toFactoring.fiberIndices).card : ENNReal) ≤
        ∑ parent ∈ P.fullContainmentOwnerParents first,
          ((P.toFactoring.fiberIndices parent).card : ENNReal)
    exact_mod_cast Finset.card_biUnion_le
  have hFiber :
      ∀ parent ∈ P.fullContainmentOwnerParents first,
        P.toFactoring.fiberCount parent ≤
          C * P.toFactoring.fiberCount second := by
    intro parent _
    exact hUniform.2 parent second
  calc
    P.fullContainmentFiberCount first
        ≤ (((P.fullContainmentOwnerParents first).biUnion
            P.toFactoring.fiberIndices).card : ENNReal) := hCardSubset
    _ ≤ ∑ parent ∈ P.fullContainmentOwnerParents first,
          P.toFactoring.fiberCount parent := hUnion
    _ ≤ ∑ _parent ∈ P.fullContainmentOwnerParents first,
          C * P.toFactoring.fiberCount second :=
      Finset.sum_le_sum hFiber
    _ = ((P.fullContainmentOwnerParents first).card : ENNReal) *
          (C * P.toFactoring.fiberCount second) := by
      simp [nsmul_eq_mul]
    _ ≤ M * (C * P.toFactoring.fiberCount second) := by
      gcongr
      exact hOwner first
    _ ≤ M * (C * P.fullContainmentFiberCount second) := by
      gcongr
      exact P.factoringFiberCount_le_fullContainmentFiberCount second
    _ = M * C * P.fullContainmentFiberCount second := by ring

/--
Bounded owner-parent overlap upgrades assigned-fiber uniformity to genuine
full-containment branching uniformity.
-/
lemma fullContainmentFibersAreCUniform_of_ownerCount
    {delta rho A : ℝ}
    {fine : TubeFamily delta} {coarse : TubeFamily rho}
    (P : DilatedTubeCover A fine coarse)
    {C M : ENNReal}
    (hM : 1 ≤ M)
    (hUniform : P.toFactoring.FibersAreCUniform C)
    (hOwner :
      ∀ j, ((P.fullContainmentOwnerParents j).card : ENNReal) ≤ M) :
    P.FullContainmentFibersAreCUniform (M * C) := by
  refine ⟨by simpa using mul_le_mul' hM hUniform.1, ?_⟩
  exact P.fullContainmentFiberCount_le_of_ownerCount
    hUniform hOwner

/-- Every paper full fiber is nonempty because the parent map is surjective. -/
lemma fullContainmentFiberIndices_nonempty
    {delta rho A : ℝ}
    {fine : TubeFamily delta} {coarse : TubeFamily rho}
    (P : DilatedTubeCover A fine coarse)
    (j : Fin coarse.card) :
    (P.fullContainmentFiberIndices j).Nonempty := by
  rcases P.parent_surjective j with ⟨i, hi⟩
  have hassigned : i ∈ P.toFactoring.fiberIndices j := by
    change i ∈ Finset.univ.filter fun index : Fin fine.card =>
      P.parent index = j
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
  exact
    ⟨i, P.factoringFiberIndices_subset_fullContainmentFiberIndices j hassigned⟩

/-- Every finite nonempty fine family gives a canonical finite uniformity
bound for the full geometric fibres of any surjective dilated cover.  This is
the fallback used when a later same-source restriction is not itself a level
of the original all-real hierarchy. -/
lemma fullContainmentFibersAreCUniform_card
    {delta rho A : ℝ}
    {fine : TubeFamily delta} {coarse : TubeFamily rho}
    (P : DilatedTubeCover A fine coarse)
    (hfine : fine.Nonempty) :
    P.FullContainmentFibersAreCUniform fine.enncard := by
  have hone : (1 : ENNReal) ≤ fine.enncard := by
    change (1 : ENNReal) ≤ (fine.card : ENNReal)
    exact_mod_cast hfine
  refine ⟨hone, ?_⟩
  intro first second
  have hfirst : P.fullContainmentFiberCount first ≤ fine.enncard := by
    change ((P.fullContainmentFiberIndices first).card : ENNReal) ≤
      (fine.card : ENNReal)
    exact_mod_cast (show (P.fullContainmentFiberIndices first).card ≤ fine.card by
      simpa using Finset.card_le_univ (P.fullContainmentFiberIndices first))
  have hsecond : (1 : ENNReal) ≤
      P.fullContainmentFiberCount second := by
    change (1 : ENNReal) ≤
      ((P.fullContainmentFiberIndices second).card : ENNReal)
    exact_mod_cast
      (Finset.card_pos.mpr (P.fullContainmentFiberIndices_nonempty second))
  calc
    P.fullContainmentFiberCount first ≤ fine.enncard := hfirst
    _ = fine.enncard * 1 := by simp
    _ ≤ fine.enncard * P.fullContainmentFiberCount second := by gcongr

/-- Every paper full-fiber tube lies in its defining dilated parent. -/
lemma fullContainmentFiberSubfamily_all_contained
    {delta rho A : ℝ}
    {fine : TubeFamily delta} {coarse : TubeFamily rho}
    (P : DilatedTubeCover A fine coarse)
    (j : Fin coarse.card) :
    ∀ i,
      ((P.fullContainmentFiberSubfamily j).family.tube i).carrier ⊆
        dilatedTubeCarrier A (coarse.tube j) := by
  intro i
  rw [(P.fullContainmentFiberSubfamily j).tube_eq i]
  have hi :
      (P.fullContainmentFiberSubfamily j).embedding i ∈
        P.fullContainmentFiberIndices j :=
    Finset.orderEmbOfFin_mem (P.fullContainmentFiberIndices j) rfl i
  exact (P.mem_fullContainmentFiberIndices_iff j _).mp hi

/-- If the dilated carrier contains the unit ball and all fine tubes lie in the
unit ball, then the full-containment fiber is the entire fine family. -/
lemma fullContainmentFiberIndices_eq_univ_of_carrier_contains_unitBall
    {delta rho A : ℝ}
    {fine : TubeFamily delta} {coarse : TubeFamily rho}
    (P : DilatedTubeCover A fine coarse)
    (hF_ball : fine.IsInUnitBall)
    (j : Fin coarse.card)
    (h_carrier : Metric.closedBall (0 : Point3) 1 ⊆
      dilatedTubeCarrier A (coarse.tube j)) :
    P.fullContainmentFiberIndices j = Finset.univ := by
  ext i
  simp only [P.mem_fullContainmentFiberIndices_iff, Finset.mem_univ, iff_true]
  have h1 : (fine.tube i).carrier ⊆ Metric.closedBall (0 : Point3) 1 :=
    hF_ball i
  exact Set.Subset.trans h1 h_carrier

end DilatedTubeCover

end Kakeya.Streamlined

end
