/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceBudget

/-!
# Input exponents after the returned ambient ceilings

The actual finite preparation, estimator accuracies, and reserve precede
every finite collection of positive ambient input ceilings.
-/

@[expose] public section

namespace Kakeya.ML2Assembly

universe u

/-- All parent and raw middle preparation on the same chosen finite spine. -/
structure SourceLocalPreparation (beta varpi eps1 : Real)
    (rawGain rawDens : Real -> Real) : Prop where
  parent : forall m : Nat, m < ML2Spine.spineCount varpi eps1 ->
    SourceParentMinBounds beta
      (ML2Spine.spineNu beta varpi eps1
        (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens))
      (ML2Spine.spineDiv varpi eps1)
      (ML2Spine.spineRung beta varpi eps1
        (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) m)
      (ML2Spine.spineRung beta varpi eps1
        (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) (m + 1))
      (rawGain ((ML2Spine.spineRung beta varpi eps1
        (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) (m + 1)) / 16))
      (rawDens ((ML2Spine.spineRung beta varpi eps1
        (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) (m + 1)) / 16))
  middle : forall m : Nat, m < ML2Spine.spineCount varpi eps1 ->
    SourceMiddlePreparation.{u} beta varpi (ML2Spine.spineDiv varpi eps1)
      (ML2Spine.spineRung beta varpi eps1
        (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) (m + 1))
      (rawGain ((ML2Spine.spineRung beta varpi eps1
        (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) (m + 1)) / 16))
      (rawDens ((ML2Spine.spineRung beta varpi eps1
        (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) (m + 1)) / 16))

/-- Late input choices preserve every earlier factor accuracy and the reserve. -/
structure SourceLateInputBounds (beta varpi eps1 : Real)
    (rawGain rawDens : Real -> Real) (s : Real) (a : SourceLocalAccuracyData)
    (H : Finset Real) (etaL etaIn eta aL : Real) : Prop where
  input_pos : 0 < etaIn
  input_lt_loss : etaIn < etaL
  loss_le_accuracy : etaL <= s
  loss_le_ceilings : forall h : Real, h ∈ H -> etaL <= h
  shading_pos : 0 < eta
  shading_le_one : eta <= 1
  absorption_pos : 0 < aL
  site_ladder : eta + aL <= etaIn
  site_budget : eta + aL < ML2Spine.spineNu beta varpi eps1
    (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens)
  residual : forall m : Nat, m < ML2Spine.spineCount varpi eps1 ->
    a.kappaC + ML2Spine.spineRung beta varpi eps1
      (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) m <=
      2 * sourceParentMinimum (ML2Spine.spineDiv varpi eps1)
        (ML2Spine.spineRung beta varpi eps1
          (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) (m + 1))
        (rawGain ((ML2Spine.spineRung beta varpi eps1
          (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) (m + 1)) / 16))
        (rawDens ((ML2Spine.spineRung beta varpi eps1
          (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) (m + 1)) / 16))
  reserve_pos : 0 < a.reserve
  budget : forall m : Nat, m < ML2Spine.spineCount varpi eps1 ->
    6 * ML2Spine.spineNu beta varpi eps1
        (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) +
      a.theta2 + etaIn + a.epsf m + a.epsp m +
      (a.epsc m + ML2Spine.spineRung beta varpi eps1
        (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) m) +
      a.kappaPrime + a.reserve <=
      sourceMiddleNetGain (ML2Spine.spineDiv varpi eps1)
        (rawGain ((ML2Spine.spineRung beta varpi eps1
          (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) (m + 1)) / 16))

/-- Fix all preparations and accuracies before receiving any finite ambient ceilings. -/
theorem sourceSpine_localReserve_after_ceilings {beta varpi eps1 : Real}
    {rawGain rawDens : Real -> Real}
    (hbeta0 : 0 < beta) (hbeta1 : beta <= 1) (heps1 : 0 < eps1)
    (hp : Lemma91ParamsAt.{u} beta varpi rawGain rawDens) :
    exists s : Real, exists a : SourceLocalAccuracyData,
      SourceLocalPreparation.{u} beta varpi eps1 rawGain rawDens /\
      SourceLocalBudget beta varpi eps1 rawGain rawDens s a /\
      forall H : Finset Real, (forall h : Real, h ∈ H -> 0 < h) ->
        exists etaL etaIn eta aL : Real,
          SourceLateInputBounds beta varpi eps1 rawGain rawDens s a H etaL etaIn eta aL := by
  letI := Classical.decEq Real
  obtain ⟨s, a, hbudget⟩ := sourceSpine_exists_local_budget hbeta0 hbeta1 heps1 hp
  have hpreparation : SourceLocalPreparation.{u} beta varpi eps1 rawGain rawDens := {
    parent := sourceSpine_parent_min_bounds hbeta0 hbeta1 heps1 hp
    middle := sourceSpine_middle_preparation hbeta0 hbeta1 heps1 hp }
  refine ⟨s, a, hpreparation, hbudget, ?_⟩
  intro H hH
  let caps := insert s H
  have hcaps : caps.Nonempty := ⟨s, Finset.mem_insert_self _ _⟩
  let t := caps.min' hcaps
  have hcaps0 : forall x, x ∈ caps -> 0 < x := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hbudget.accuracy_pos
    · exact hH x hx
  have ht0 : 0 < t := hcaps0 _ (caps.min'_mem hcaps)
  have hts : t <= s := caps.min'_le _ (Finset.mem_insert_self _ _)
  have htH (h : Real) (hh : h ∈ H) : t <= h :=
    caps.min'_le _ (Finset.mem_insert_of_mem hh)
  have hinput0 : 0 < t / 4 := by positivity
  have hinput_s : t / 4 <= s := by linarith only [hts, ht0]
  refine ⟨t / 2, t / 4, t / 16, t / 16, {
    input_pos := hinput0
    input_lt_loss := by linarith only [ht0]
    loss_le_accuracy := by linarith only [hts, ht0]
    loss_le_ceilings := ?_
    shading_pos := by positivity
    shading_le_one := by linarith only [hts, hbudget.accuracy_le_one]
    absorption_pos := by positivity
    site_ladder := by linarith only [ht0]
    site_budget := by linarith only [hts, ht0, hbudget.accuracy_le_margin]
    residual := fun m hm => (hbudget.input_budget (t / 4) hinput0 hinput_s m hm).1
    reserve_pos := hbudget.reserve_pos
    budget := fun m hm => (hbudget.input_budget (t / 4) hinput0 hinput_s m hm).2.2 }⟩
  intro h hh
  linarith only [htH h hh, ht0]

end Kakeya.ML2Assembly
