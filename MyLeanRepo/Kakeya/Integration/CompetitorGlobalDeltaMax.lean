import MyLeanRepo.Kakeya.Integration.CompetitorHierarchyBridge
import MyLeanRepo.Kakeya.Streamlined.DividingScales.ConditionalRelationDeltaMaxSplitProduct.Helpers
import MyLeanRepo.Kakeya.Streamlined.FlatPrismFactoring.FromSection5AndPlankEstimates.UniformFiberOccupancyHelpers
import MyLeanRepo.Kakeya.Streamlined.FlatPrismFactoring.FromSection5AndPlankEstimates.FactoringComposition
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.TubeDimensions
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.DeterministicHelpers

/-!
# Global deltaMax from assigned-fiber Frostman control

This file aggregates Frostman inequalities over the disjoint assigned fibers
of one surjective parent map.  Assigned fibers are used only as a partition of
the source indices; they are not identified with complete geometric
containment fibers.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Streamlined

namespace TubeCover

/--
An assigned-fiber Frostman inequality forces every nonempty parent fiber to
carry enough fine-tube mass to account for the parent-tube volume.

This is the parentwise version of the usual Frostman cardinality lower bound.
It uses the assigned fiber selected by the parent map and makes no assertion
about the (generally larger) complete geometric containment fiber.
-/
theorem coarseVolume_le_assignedFrostman_mul_fiberCount_mul_fineVolume
    {delta rho : ℝ}
    (hdelta : 0 < delta)
    {fine : TubeFamily delta} {coarse : TubeFamily rho}
    (P : TubeCover fine coarse)
    {C : ENNReal}
    (hFrostman : P.AssignedFibersAreCFrostman C)
    (parent : Fin coarse.card) :
    Kakeya.deltaTubeVolume rho ≤
      C * P.toFactoring.fiberCount parent *
        Kakeya.deltaTubeVolume delta := by
  classical
  let index : Fin fine.toBodyFamily.card :=
    Classical.choose (P.toFactoring.parent_surjective parent)
  have hparent : P.toFactoring.parent index = parent :=
    Classical.choose_spec (P.toFactoring.parent_surjective parent)
  let test : Set Point3 :=
    (fine.toBodyFamily.body index).carrier
  have hindexFiber : index ∈ P.toFactoring.fiberIndices parent := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ index, hparent⟩
  have hindexContained : index ∈
      (P.toFactoring.fiberIndices parent).filter fun current =>
        (fine.toBodyFamily.body current).carrier ⊆ test := by
    exact Finset.mem_filter.mpr
      ⟨hindexFiber, Set.Subset.rfl⟩
  have hcontainedLower :
      Kakeya.deltaTubeVolume delta ≤
        P.toFactoring.fiberContainedMass parent test := by
    calc
      Kakeya.deltaTubeVolume delta =
          (fine.toBodyFamily.body index).volume := by
        exact
          (RandomTranslation.tube_volume_eq_deltaTubeVolume
            (fine.tube index)).symm
      _ ≤ P.toFactoring.fiberContainedMass parent test := by
        dsimp only [Factoring.fiberContainedMass]
        exact Finset.single_le_sum
          (s := (P.toFactoring.fiberIndices parent).filter fun current =>
            (fine.toBodyFamily.body current).carrier ⊆ test)
          (f := fun current => (fine.toBodyFamily.body current).volume)
          (fun current _ => by positivity) hindexContained
  have htestConvex : Convex ℝ test :=
    GeometricLemmas.tubeFamily_bodies_convex fine index
  have htestParent :
      test ⊆ (coarse.toBodyFamily.body parent).carrier := by
    simpa only [test, hparent] using P.toFactoring.contained index
  have hfrost := hFrostman parent test htestConvex htestParent
  have hcoarseVolume :
      (coarse.toBodyFamily.body parent).volume =
        Kakeya.deltaTubeVolume rho :=
    RandomTranslation.tube_volume_eq_deltaTubeVolume
      (coarse.tube parent)
  have hfiberMass :
      P.toFactoring.fiberMass parent =
        P.toFactoring.fiberCount parent *
          Kakeya.deltaTubeVolume delta := by
    dsimp only [Factoring.fiberMass, Factoring.fiberCount]
    calc
      (∑ current ∈ P.toFactoring.fiberIndices parent,
          (fine.toBodyFamily.body current).volume) =
          ∑ _current ∈ P.toFactoring.fiberIndices parent,
            Kakeya.deltaTubeVolume delta := by
        apply Finset.sum_congr rfl
        intro current _
        exact RandomTranslation.tube_volume_eq_deltaTubeVolume
          (fine.tube current)
      _ = ((P.toFactoring.fiberIndices parent).card : ENNReal) *
          Kakeya.deltaTubeVolume delta := by
        simp [Finset.sum_const, nsmul_eq_mul]
  have hproduct :
      Kakeya.deltaTubeVolume delta * Kakeya.deltaTubeVolume rho ≤
        (C * P.toFactoring.fiberCount parent *
          Kakeya.deltaTubeVolume delta) *
            Kakeya.deltaTubeVolume delta := by
    calc
      Kakeya.deltaTubeVolume delta * Kakeya.deltaTubeVolume rho
          ≤ P.toFactoring.fiberContainedMass parent test *
              Kakeya.deltaTubeVolume rho :=
        mul_le_mul_right' hcontainedLower _
      _ ≤ C * P.toFactoring.fiberMass parent * volume test := by
        simpa [hcoarseVolume] using hfrost
      _ = (C * P.toFactoring.fiberCount parent *
            Kakeya.deltaTubeVolume delta) *
          Kakeya.deltaTubeVolume delta := by
        rw [hfiberMass]
        rw [show volume test = Kakeya.deltaTubeVolume delta by
          exact RandomTranslation.tube_volume_eq_deltaTubeVolume
            (fine.tube index)]
        simp [mul_assoc]
  have hVzero : Kakeya.deltaTubeVolume delta ≠ 0 :=
    (RandomTranslation.deltaTubeVolume_pos hdelta).ne'
  have hVtop : Kakeya.deltaTubeVolume delta ≠ ⊤ :=
    RandomTranslation.deltaTubeVolume_ne_top
  have hproduct' :
      Kakeya.deltaTubeVolume delta * Kakeya.deltaTubeVolume rho ≤
        Kakeya.deltaTubeVolume delta *
          (C * P.toFactoring.fiberCount parent *
            Kakeya.deltaTubeVolume delta) := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using hproduct
  exact (ENNReal.mul_le_mul_iff_right hVzero hVtop).mp hproduct'

/--
If every assigned fiber is `C`-Frostman and all coarse parents have the same
positive finite volume `V`, then the fine family's global maximal density is
at most `C * fine.mass / V`.

For a convex test set `K`, the assigned fiber over `j` is tested only inside
`K ∩ coarse[j]`.  The assigned fibers then sum disjointly to the fine family.
-/
theorem deltaMax_le_assignedFrostman_mul_mass_div_commonVolume
    {delta rho : ℝ}
    {fine : TubeFamily delta} {coarse : TubeFamily rho}
    (P : TubeCover fine coarse)
    {C V : ENNReal}
    (hFrostman : P.AssignedFibersAreCFrostman C)
    (hvolume : ∀ parent : Fin coarse.toBodyFamily.card,
      (coarse.toBodyFamily.body parent).volume = V)
    (hVzero : V ≠ 0) (hVtop : V ≠ ⊤) :
    fine.toBodyFamily.deltaMax ≤ C * fine.toBodyFamily.mass / V := by
  classical
  apply
    ConditionalRelationDeltaMaxSplitProduct.deltaMax_le_of_containedMass_le
  intro K hK hKtop
  let localTest : Fin coarse.toBodyFamily.card → Set Point3 := fun parent =>
    K ∩ (coarse.toBodyFamily.body parent).carrier
  have hlocalConvex : ∀ parent, Convex ℝ (localTest parent) := by
    intro parent
    exact hK.inter
      (GeometricLemmas.tubeFamily_bodies_convex coarse parent)
  have hlocalSubset : ∀ parent,
      localTest parent ⊆ (coarse.toBodyFamily.body parent).carrier := by
    intro parent
    exact Set.inter_subset_right
  have hlocalVolume : ∀ parent, volume (localTest parent) ≤ volume K := by
    intro parent
    exact measure_mono Set.inter_subset_left
  let localIndices : Fin coarse.toBodyFamily.card →
      Finset (Fin fine.toBodyFamily.card) :=
    fun parent =>
      (P.toFactoring.fiberIndices parent).filter fun index =>
        (fine.toBodyFamily.body index).carrier ⊆ localTest parent
  have hlocalDisjoint : Set.Pairwise
      (Finset.univ : Finset (Fin coarse.toBodyFamily.card))
      (fun first second =>
        Disjoint (localIndices first) (localIndices second)) := by
    intro first _ second _ hne
    apply Disjoint.mono (Finset.filter_subset _ _)
      (Finset.filter_subset _ _)
    rw [Finset.disjoint_left]
    intro index hfirst hsecond
    have hfirstParent : P.toFactoring.parent index = first := by
      simpa [Factoring.fiberIndices] using hfirst
    have hsecondParent : P.toFactoring.parent index = second := by
      simpa [Factoring.fiberIndices] using hsecond
    exact hne (hfirstParent.symm.trans hsecondParent)
  have hcontainedIndices :
      fine.toBodyFamily.containedIndices K ⊆
        Finset.biUnion
          (Finset.univ : Finset (Fin coarse.toBodyFamily.card))
          localIndices := by
    intro index hindex
    have hindexK : (fine.toBodyFamily.body index).carrier ⊆ K :=
      BodyFamily.mem_containedIndices_iff.mp hindex
    let parent := P.toFactoring.parent index
    have hindexParent :
        (fine.toBodyFamily.body index).carrier ⊆
          (coarse.toBodyFamily.body parent).carrier :=
      P.toFactoring.contained index
    have hindexLocal :
        (fine.toBodyFamily.body index).carrier ⊆ localTest parent :=
      Set.subset_inter hindexK hindexParent
    apply Finset.mem_biUnion.mpr
    refine ⟨parent, Finset.mem_univ parent, ?_⟩
    exact Finset.mem_filter.mpr
      ⟨by simp [Factoring.fiberIndices, parent], hindexLocal⟩
  have hcontainedMass :
      fine.toBodyFamily.containedMass K ≤
        ∑ parent : Fin coarse.toBodyFamily.card,
          P.toFactoring.fiberContainedMass parent (localTest parent) := by
    dsimp only [BodyFamily.containedMass, Factoring.fiberContainedMass]
    have hsum :
        fine.toBodyFamily.containedMass K ≤
          ∑ index ∈ Finset.biUnion
              (Finset.univ : Finset (Fin coarse.toBodyFamily.card))
              localIndices,
            (fine.toBodyFamily.body index).volume :=
      Finset.sum_le_sum_of_subset_of_nonneg hcontainedIndices
        (fun _ _ _ => by positivity)
    rw [Finset.sum_biUnion hlocalDisjoint] at hsum
    exact hsum
  have hfiberFrostman : ∀ parent : Fin coarse.toBodyFamily.card,
      P.toFactoring.fiberContainedMass parent (localTest parent) * V ≤
        C * P.toFactoring.fiberMass parent *
          volume (localTest parent) := by
    intro parent
    have h := hFrostman parent (localTest parent)
      (hlocalConvex parent) (hlocalSubset parent)
    rwa [hvolume parent] at h
  have hproduct :
      fine.toBodyFamily.containedMass K * V ≤
        C * fine.toBodyFamily.mass * volume K := by
    calc
      fine.toBodyFamily.containedMass K * V
          ≤ (∑ parent : Fin coarse.toBodyFamily.card,
              P.toFactoring.fiberContainedMass parent (localTest parent)) * V :=
        mul_le_mul_right' hcontainedMass V
      _ = ∑ parent : Fin coarse.toBodyFamily.card,
          P.toFactoring.fiberContainedMass parent (localTest parent) * V := by
        rw [Finset.sum_mul]
      _ ≤ ∑ parent : Fin coarse.toBodyFamily.card,
          C * P.toFactoring.fiberMass parent *
            volume (localTest parent) := by
        exact Finset.sum_le_sum fun parent _ => hfiberFrostman parent
      _ ≤ ∑ parent : Fin coarse.toBodyFamily.card,
          C * P.toFactoring.fiberMass parent * volume K := by
        exact Finset.sum_le_sum fun parent _ =>
          mul_le_mul_left' (hlocalVolume parent)
            (C * P.toFactoring.fiberMass parent)
      _ = C * fine.toBodyFamily.mass * volume K := by
        rw [← Finset.sum_mul, ← Finset.mul_sum,
          factoring_mass_partition P.toFactoring]
  calc
    fine.toBodyFamily.containedMass K
        ≤ (C * fine.toBodyFamily.mass * volume K) / V :=
      (ENNReal.le_div_iff_mul_le (Or.inl hVzero) (Or.inl hVtop)).2
        hproduct
    _ = (C * fine.toBodyFamily.mass / V) * volume K := by
      simp [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]

end TubeCover

namespace Factoring

/--
Merge assigned Frostman fibers through a second surjective factoring.  The
first-level parent bodies have one common volume `Vmid`; the final parent
body has volume at most `Cvol * Vmid`.  Summing the first-level inequalities
inside one composite fiber cancels piece masses, so no bound on the number of
merged parents is needed.
-/
theorem compose_frostman_of_common_middle_volume
    {fine middle coarse : BodyFamily}
    (P₁ : Factoring fine middle) (P₂ : Factoring middle coarse)
    {C Cvol Vmid : ENNReal}
    (hFrostman : P₁.FibersAreCFrostman C)
    (hmiddleConvex : middle.IsConvex)
    (hVmid : ∀ parent, (middle.body parent).volume = Vmid)
    (hcoarseVolume : ∀ parent,
      (coarse.body parent).volume ≤ Cvol * Vmid) :
    (P₁.compose P₂).FibersAreCFrostman (Cvol * C) := by
  classical
  intro parent test htestConvex htestSubset
  let localTest : Fin middle.card → Set Point3 := fun middleParent =>
    test ∩ (middle.body middleParent).carrier
  have hrestrict : ∀ middleParent ∈ P₂.fiberIndices parent,
      P₁.fiberContainedMass middleParent test =
        P₁.fiberContainedMass middleParent (localTest middleParent) := by
    intro middleParent _
    dsimp only [Factoring.fiberContainedMass]
    congr 1
    apply Finset.filter_congr
    intro index hindex
    have hparentEq : P₁.parent index = middleParent :=
      (Finset.mem_filter.mp hindex).2
    have hmiddle :
        (fine.body index).carrier ⊆
          (middle.body middleParent).carrier := by
      simpa [hparentEq] using P₁.contained index
    exact ⟨fun h => Set.subset_inter h hmiddle,
      fun h => h.trans Set.inter_subset_left⟩
  have hpiece : ∀ middleParent ∈ P₂.fiberIndices parent,
      P₁.fiberContainedMass middleParent (localTest middleParent) * Vmid ≤
        C * P₁.fiberMass middleParent * volume test := by
    intro middleParent _
    calc
      P₁.fiberContainedMass middleParent (localTest middleParent) * Vmid
          = P₁.fiberContainedMass middleParent (localTest middleParent) *
              (middle.body middleParent).volume := by
        rw [hVmid]
      _ ≤ C * P₁.fiberMass middleParent *
            volume (localTest middleParent) :=
        hFrostman middleParent (localTest middleParent)
          (htestConvex.inter (hmiddleConvex middleParent))
          Set.inter_subset_right
      _ ≤ C * P₁.fiberMass middleParent * volume test := by
        exact mul_le_mul_left' (measure_mono Set.inter_subset_left) _
  have hsum :
      (P₁.compose P₂).fiberContainedMass parent test * Vmid ≤
        C * (P₁.compose P₂).fiberMass parent * volume test := by
    rw [compose_fiberContainedMass, compose_fiberMass]
    calc
      (∑ middleParent ∈ P₂.fiberIndices parent,
          P₁.fiberContainedMass middleParent test) * Vmid =
          ∑ middleParent ∈ P₂.fiberIndices parent,
            P₁.fiberContainedMass middleParent
              (localTest middleParent) * Vmid := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro middleParent hmiddleParent
        rw [hrestrict middleParent hmiddleParent]
      _ ≤ ∑ middleParent ∈ P₂.fiberIndices parent,
          C * P₁.fiberMass middleParent * volume test := by
        exact Finset.sum_le_sum fun middleParent hmiddleParent =>
          hpiece middleParent hmiddleParent
      _ = C * (∑ middleParent ∈ P₂.fiberIndices parent,
          P₁.fiberMass middleParent) * volume test := by
        rw [Finset.mul_sum, Finset.sum_mul]
  calc
    (P₁.compose P₂).fiberContainedMass parent test *
          (coarse.body parent).volume
        ≤ (P₁.compose P₂).fiberContainedMass parent test *
            (Cvol * Vmid) := by
      exact mul_le_mul_left' (hcoarseVolume parent) _
    _ = Cvol *
          ((P₁.compose P₂).fiberContainedMass parent test * Vmid) := by
      ring
    _ ≤ Cvol *
          (C * (P₁.compose P₂).fiberMass parent * volume test) := by
      gcongr
    _ = (Cvol * C) *
          (P₁.compose P₂).fiberMass parent * volume test := by
      ring

/--
Regroup assigned Frostman fibers through a second parent map without requiring
the intermediate parent bodies themselves to lie in the final parent body.

This is the mass-cancellation form needed when several honest hierarchy nodes
are merged into one supporting-line quotient parent.  Every fine body is still
contained in its original middle parent (through `P₁`) and in its final parent
(through `Q`), while `hparent` says that the final fibers are disjoint unions of
the middle fibers.  Consequently no bound on the number of merged middle
parents appears.
-/
theorem regroup_frostman_of_common_middle_volume
    {fine middle coarse : BodyFamily}
    (P₁ : Factoring fine middle) (Q : Factoring fine coarse)
    (group : Fin middle.card → Fin coarse.card)
    (hparent : ∀ index, Q.parent index = group (P₁.parent index))
    {C Cvol Vmid : ENNReal}
    (hFrostman : P₁.FibersAreCFrostman C)
    (hmiddleConvex : middle.IsConvex)
    (hVmid : ∀ parent, (middle.body parent).volume = Vmid)
    (hcoarseVolume : ∀ parent,
      (coarse.body parent).volume ≤ Cvol * Vmid) :
    Q.FibersAreCFrostman (Cvol * C) := by
  classical
  intro parent test htestConvex htestSubset
  let selectedMiddle : Finset (Fin middle.card) :=
    Finset.univ.filter fun middleParent => group middleParent = parent
  let localTest : Fin middle.card → Set Point3 := fun middleParent =>
    test ∩ (middle.body middleParent).carrier
  have hfiberIndices :
      Q.fiberIndices parent =
        selectedMiddle.biUnion fun middleParent =>
          P₁.fiberIndices middleParent := by
    ext index
    simp only [Factoring.fiberIndices, selectedMiddle,
      Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion]
    constructor
    · intro hindex
      refine ⟨P₁.parent index, ?_, rfl⟩
      rwa [hparent index] at hindex
    · rintro ⟨middleParent, hmiddleParent, hindex⟩
      rw [hparent index, hindex]
      exact hmiddleParent
  have hdisjoint :
      ∀ first ∈ selectedMiddle, ∀ second ∈ selectedMiddle,
        first ≠ second →
          Disjoint (P₁.fiberIndices first) (P₁.fiberIndices second) := by
    intro first _ second _ hne
    simp only [Factoring.fiberIndices, Finset.disjoint_left,
      Finset.mem_filter, Finset.mem_univ, true_and]
    intro index hfirst hsecond
    exact hne (hfirst.symm.trans hsecond)
  have hrestrict : ∀ middleParent ∈ selectedMiddle,
      P₁.fiberContainedMass middleParent test =
        P₁.fiberContainedMass middleParent (localTest middleParent) := by
    intro middleParent _
    dsimp only [Factoring.fiberContainedMass]
    congr 1
    apply Finset.filter_congr
    intro index hindex
    have hparentEq : P₁.parent index = middleParent :=
      (Finset.mem_filter.mp hindex).2
    have hmiddle :
        (fine.body index).carrier ⊆
          (middle.body middleParent).carrier := by
      simpa [hparentEq] using P₁.contained index
    exact ⟨fun h => Set.subset_inter h hmiddle,
      fun h => h.trans Set.inter_subset_left⟩
  have hpiece : ∀ middleParent ∈ selectedMiddle,
      P₁.fiberContainedMass middleParent (localTest middleParent) * Vmid ≤
        C * P₁.fiberMass middleParent * volume test := by
    intro middleParent _
    calc
      P₁.fiberContainedMass middleParent (localTest middleParent) * Vmid
          = P₁.fiberContainedMass middleParent (localTest middleParent) *
              (middle.body middleParent).volume := by
        rw [hVmid]
      _ ≤ C * P₁.fiberMass middleParent *
            volume (localTest middleParent) :=
        hFrostman middleParent (localTest middleParent)
          (htestConvex.inter (hmiddleConvex middleParent))
          Set.inter_subset_right
      _ ≤ C * P₁.fiberMass middleParent * volume test := by
        exact mul_le_mul_left' (measure_mono Set.inter_subset_left) _
  have hfiberContainedMass :
      Q.fiberContainedMass parent test =
        ∑ middleParent ∈ selectedMiddle,
          P₁.fiberContainedMass middleParent test := by
    have hfilterBiUnion :
        (selectedMiddle.biUnion fun middleParent =>
            P₁.fiberIndices middleParent).filter
              (fun index => (fine.body index).carrier ⊆ test) =
          selectedMiddle.biUnion fun middleParent =>
            (P₁.fiberIndices middleParent).filter
              (fun index => (fine.body index).carrier ⊆ test) := by
      ext index
      simp only [Finset.mem_filter, Finset.mem_biUnion]
      tauto
    dsimp only [Factoring.fiberContainedMass]
    rw [hfiberIndices, hfilterBiUnion]
    rw [Finset.sum_biUnion]
    intro first hfirst second hsecond hne
    exact (hdisjoint first hfirst second hsecond hne).mono
      (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have hfiberMass :
      Q.fiberMass parent =
        ∑ middleParent ∈ selectedMiddle, P₁.fiberMass middleParent := by
    dsimp only [Factoring.fiberMass]
    rw [hfiberIndices, Finset.sum_biUnion hdisjoint]
  have hsum :
      Q.fiberContainedMass parent test * Vmid ≤
        C * Q.fiberMass parent * volume test := by
    rw [hfiberContainedMass, hfiberMass]
    calc
      (∑ middleParent ∈ selectedMiddle,
          P₁.fiberContainedMass middleParent test) * Vmid =
          ∑ middleParent ∈ selectedMiddle,
            P₁.fiberContainedMass middleParent
              (localTest middleParent) * Vmid := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro middleParent hmiddleParent
        rw [hrestrict middleParent hmiddleParent]
      _ ≤ ∑ middleParent ∈ selectedMiddle,
          C * P₁.fiberMass middleParent * volume test := by
        exact Finset.sum_le_sum fun middleParent hmiddleParent =>
          hpiece middleParent hmiddleParent
      _ = C * (∑ middleParent ∈ selectedMiddle,
          P₁.fiberMass middleParent) * volume test := by
        rw [Finset.mul_sum, Finset.sum_mul]
  calc
    Q.fiberContainedMass parent test * (coarse.body parent).volume
        ≤ Q.fiberContainedMass parent test * (Cvol * Vmid) := by
      exact mul_le_mul_left' (hcoarseVolume parent) _
    _ = Cvol * (Q.fiberContainedMass parent test * Vmid) := by
      ring
    _ ≤ Cvol * (C * Q.fiberMass parent * volume test) := by
      gcongr
    _ = (Cvol * C) * Q.fiberMass parent * volume test := by
      ring

end Factoring

end Kakeya.Streamlined

namespace Kakeya.Integration

open Kakeya.Streamlined
open Kakeya.Streamlined.RandomTranslation

namespace CompetitorStickyInput

variable {delta : NNReal} {ι : Type*} {N : ℕ} {C : NNReal}
  {lambda frostmanConstant : ENNReal} {supportRadius : ℝ}

/--
Any one level of the original competitor hierarchy gives a global source
`deltaMax` bound.  This uses only the stored assigned-node Frostman partition.
-/
theorem source_deltaMax_le_nodeFrostman_mul_mass_div_levelVolume
    (input :
      CompetitorStickyInput delta ι N C lambda frostmanConstant supportRadius)
    (hdelta : 0 < delta) {k : ℕ} (hk : k ≤ N) :
    input.source.toBodyFamily.deltaMax ≤
      frostmanConstant * input.source.toBodyFamily.mass /
        Kakeya.deltaTubeVolume (Tube.gridScale delta N k : ℝ) := by
  apply TubeCover.deltaMax_le_assignedFrostman_mul_mass_div_commonVolume
    (input.levelStrictCover hk)
    (input.levelStrictCover_assignedFrostman hk)
  · intro parent
    change ((input.levelCoarse k).tube parent).volume =
      Kakeya.deltaTubeVolume (Tube.gridScale delta N k : ℝ)
    exact tube_volume_eq_deltaTubeVolume _
  · exact (deltaTubeVolume_pos (by
      exact_mod_cast Tube.gridScale_pos hdelta N k)).ne'
  · exact deltaTubeVolume_ne_top

end CompetitorStickyInput

end Kakeya.Integration
