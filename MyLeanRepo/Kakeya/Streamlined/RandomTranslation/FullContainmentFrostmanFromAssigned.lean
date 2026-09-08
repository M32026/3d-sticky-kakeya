import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.FullContainmentBranching
import MyLeanRepo.Kakeya.Streamlined.DividingScales.AllRealProfileFrostmanTransport.CarrierFacts
import MyLeanRepo.Kakeya.Streamlined.DividingScales.WeightedFiniteUnion
import MyLeanRepo.Kakeya.Streamlined.DividingScales.FrostmanInequalities
import MyLeanRepo.Kakeya.Streamlined.RhoTubeMultiplicity.DilatedVolumeProduct

/-!
# Complete-fiber Frostman control from assigned fibers

The assigned fibers form a partition, whereas a complete geometric fiber may
meet several assigned owners.  This module transfers a uniform assigned-fiber
Frostman estimate to the complete fibers by covering with those owner fibers,
using assigned-fiber uniformity to compare their masses, and bounding the
number of owners geometrically.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Streamlined.RandomTranslation

open Kakeya.Streamlined

/-- Assigned Frostman plus assigned uniformity and a finite owner bound imply
Frostman control of a complete geometric containment fiber. -/
theorem fullContainmentFiberFrostman_of_assigned
    {delta rho A : ℝ}
    (hdelta : 0 < delta) (hrho : 0 < rho) (hA : 1 ≤ A)
    {fine : TubeFamily delta} {coarse : TubeFamily rho}
    (P : DilatedTubeCover A fine coarse)
    {Cuniform Cfrostman M : ENNReal}
    (huniform : P.toFactoring.FibersAreCUniform Cuniform)
    (hfrostman : P.toFactoring.FibersAreCFrostman Cfrostman)
    (howner : ∀ parent,
      ((P.fullContainmentOwnerParents parent).card : ENNReal) ≤ M)
    (parent : Fin coarse.card) :
    P.fullContainmentFiberFrostmanConstant parent ≤
      M * Cuniform * Cfrostman := by
  classical
  let fullIndices := P.fullContainmentFiberIndices parent
  let owners := P.fullContainmentOwnerParents parent
  let assignedIndices := fun owner : Fin coarse.card =>
    P.toFactoring.fiberIndices owner
  let container := dilatedTubeCarrier A (coarse.tube parent)
  let fullFiber := P.fullContainmentFiberSubfamily parent
  have hfullContained :
      ∀ index, (fullFiber.family.toBodyFamily.body index).carrier ⊆
        container :=
    P.fullContainmentFiberSubfamily_all_contained parent
  have hfullMass := P.fullContainmentFiberMass_pos_and_top hdelta parent
  have hcontainerPos : 0 < volume container :=
    GeometricLemmas.dilatedTubeCarrier_volume_pos hrho hA
      (coarse.tube parent)
  have hcontainerTop : volume container ≠ ⊤ :=
    GeometricLemmas.dilatedTubeCarrier_volume_ne_top hrho hA
      (coarse.tube parent)
  have hfullContainedMass :
      fullFiber.family.toBodyFamily.containedMass container =
        fullFiber.family.toBodyFamily.mass :=
    P.fullContainmentFiberContainedMass_eq_mass parent
  apply fullFiber.family.toBodyFamily
    |>.frostmanConstantIn_le_of_containedMass_mul_volume_le
      hcontainerPos.ne' hcontainerTop
      (by simpa [hfullContainedMass] using hfullMass.1.ne')
      (by simpa [hfullContainedMass] using hfullMass.2)
  intro test htestConvex htestSubset
  have hfullMassTest :
      fullFiber.family.toBodyFamily.containedMass test =
        finsetContainedMass fullIndices test := by
    exact subfamily_containedMass_eq fullIndices test
  have hcover :
      fullIndices ⊆ owners.biUnion assignedIndices :=
    P.fullContainmentFiberIndices_subset_ownerAssignedUnion parent
  have hpiece : ∀ owner ∈ owners,
      finsetContainedMass (assignedIndices owner) test * volume container ≤
        Cfrostman * P.toFactoring.fiberMass owner * volume test := by
    intro owner _
    let ownerContainer :=
      dilatedTubeCarrier A (coarse.tube owner)
    let localTest := test ∩ ownerContainer
    have hcontainedMass :
        finsetContainedMass (assignedIndices owner) test =
          P.toFactoring.fiberContainedMass owner test := by rfl
    have hrestrict :
        P.toFactoring.fiberContainedMass owner test =
          P.toFactoring.fiberContainedMass owner localTest := by
      dsimp only [Factoring.fiberContainedMass]
      congr 1
      apply Finset.filter_congr
      intro index hindex
      have hparentEq : P.parent index = owner :=
        (Finset.mem_filter.mp hindex).2
      have hownerContainer :
          (fine.tube index).carrier ⊆ ownerContainer := by
        simpa [ownerContainer, hparentEq] using P.nested index
      exact ⟨fun h => Set.subset_inter h hownerContainer,
        fun h => h.trans Set.inter_subset_left⟩
    have hvolumeEq :
        volume container = volume ownerContainer :=
      P.fullContainmentFiberCarrier_volume_eq
        (ne_of_gt (zero_lt_one.trans_le hA)) parent owner
    rw [hcontainedMass, hrestrict, hvolumeEq]
    exact (hfrostman owner localTest
      (htestConvex.inter
        (GeometricLemmas.dilatedTubeCarrier_convex (coarse.tube owner)))
      Set.inter_subset_right).trans <| by
        have htestVolume : volume localTest ≤ volume test :=
          measure_mono Set.inter_subset_left
        gcongr
  have hsum :
      fullFiber.family.toBodyFamily.containedMass test * volume container ≤
        (∑ owner ∈ owners,
          Cfrostman * P.toFactoring.fiberMass owner) * volume test := by
    rw [hfullMassTest]
    calc
      finsetContainedMass fullIndices test * volume container ≤
          (∑ owner ∈ owners,
            finsetContainedMass (assignedIndices owner) test) *
              volume container := by
        gcongr
        exact finsetContainedMass_le_sum_of_subset_biUnion
          owners fullIndices assignedIndices hcover test
      _ = ∑ owner ∈ owners,
          finsetContainedMass (assignedIndices owner) test *
            volume container := by rw [Finset.sum_mul]
      _ ≤ ∑ owner ∈ owners,
          Cfrostman * P.toFactoring.fiberMass owner * volume test := by
        exact Finset.sum_le_sum hpiece
      _ = (∑ owner ∈ owners,
          Cfrostman * P.toFactoring.fiberMass owner) * volume test := by
        rw [Finset.sum_mul]
  have hownerMass :
      ∑ owner ∈ owners, Cfrostman * P.toFactoring.fiberMass owner ≤
        M * Cuniform * Cfrostman *
          P.toFactoring.fiberMass parent := by
    calc
      ∑ owner ∈ owners, Cfrostman * P.toFactoring.fiberMass owner ≤
          ∑ _owner ∈ owners,
            Cfrostman * (Cuniform * P.toFactoring.fiberMass parent) := by
        exact Finset.sum_le_sum fun owner _ => by
          gcongr
          rw [dilated_cover_fiberMass_eq P owner,
            dilated_cover_fiberMass_eq P parent]
          simpa [mul_assoc] using
            mul_le_mul_right' (huniform.2 owner parent)
              (Kakeya.deltaTubeVolume delta)
      _ = (owners.card : ENNReal) *
          (Cfrostman * (Cuniform * P.toFactoring.fiberMass parent)) := by
        simp [Finset.sum_const, nsmul_eq_mul]
      _ ≤ M *
          (Cfrostman * (Cuniform * P.toFactoring.fiberMass parent)) := by
        gcongr
        exact howner parent
      _ = M * Cuniform * Cfrostman *
          P.toFactoring.fiberMass parent := by ring
  have hassignedMassLe :
      P.toFactoring.fiberMass parent ≤ fullFiber.family.toBodyFamily.mass := by
    rw [dilated_cover_fiberMass_eq P parent,
      fullFiber.family.bodyMass_eq_nominalMass]
    exact mul_le_mul_right'
      (P.factoringFiberCount_le_fullContainmentFiberCount parent)
      (Kakeya.deltaTubeVolume delta)
  calc
    fullFiber.family.toBodyFamily.containedMass test * volume container
        ≤ (∑ owner ∈ owners,
          Cfrostman * P.toFactoring.fiberMass owner) * volume test := hsum
    _ ≤ (M * Cuniform * Cfrostman *
          P.toFactoring.fiberMass parent) * volume test := by
      gcongr
    _ ≤ (M * Cuniform * Cfrostman *
          fullFiber.family.toBodyFamily.mass) * volume test := by
      gcongr
    _ = (M * Cuniform * Cfrostman) *
          fullFiber.family.toBodyFamily.containedMass container *
            volume test := by
      rw [hfullContainedMass]

/-- Support-free owner packing upgrades assigned Frostman control to genuine
complete-fiber Frostman control. -/
theorem fullContainmentFiberFrostman_of_assigned_supportFree
    {delta rho A : ℝ}
    (hdelta : 0 < delta) (hrho : 0 < rho) (hrhoOne : rho ≤ 1)
    (hA : 1 ≤ A)
    {fine : TubeFamily delta} {coarse : TubeFamily rho}
    (hcoarseED : coarse.IsEssentiallyDistinct)
    (P : DilatedTubeCover A fine coarse)
    {Cuniform Cfrostman : ENNReal}
    (huniform : P.toFactoring.FibersAreCUniform Cuniform)
    (hfrostman : P.toFactoring.FibersAreCFrostman Cfrostman)
    (parent : Fin coarse.card) :
    P.fullContainmentFiberFrostmanConstant parent ≤
      fullContainmentBranchingLoss A hA * Cuniform * Cfrostman := by
  exact fullContainmentFiberFrostman_of_assigned
    hdelta hrho hA P huniform hfrostman
    (fun target => fullContainmentOwnerCount_le_branchingLoss
      A hA hrho hrhoOne hcoarseED P target) parent

/-- All-real version of the support-free assigned-to-complete transfer. -/
theorem AssignedDilatedUniformTubeStructure.fullContainmentFrostman_of_assigned
    {delta A : ℝ} {fine : TubeFamily delta}
    (hdelta : 0 < delta) (hA : 1 ≤ A)
    (U : AssignedDilatedUniformTubeStructure (A := A) fine)
    {Cfrostman : ENNReal}
    (hassigned :
      ∀ rho, (U.cover rho).toFactoring.FibersAreCFrostman Cfrostman) :
    U.toDilatedUniformTubeStructure.IsFrostmanAtEveryScale
      (fullContainmentBranchingLoss A hA *
        U.assignedUniformity * Cfrostman) := by
  intro rho parent
  exact fullContainmentFiberFrostman_of_assigned_supportFree
    hdelta (hdelta.trans_le rho.2.1) rho.2.2 hA
    (U.coarse_distinct rho) (U.cover rho)
    (U.assignedUniform rho) (hassigned rho) parent

end Kakeya.Streamlined.RandomTranslation

end
