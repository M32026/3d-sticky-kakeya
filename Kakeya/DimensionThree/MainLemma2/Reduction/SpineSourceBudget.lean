/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineSourceLocalReserve

/-!
# Common positive accuracies and local reserve

The common accuracy and all schedules are chosen before the input exponent.
Every parent charge retains its own canonical next-rung raw outputs.
-/

@[expose] public section

namespace Kakeya.ML2Assembly

universe u

/-- The fixed estimator accuracies, factor charges, and unspent reserve. -/
structure SourceLocalAccuracyData where
  epsf : Nat -> Real
  epsParent : Nat -> Real
  epsOuter : Nat -> Real
  epsp : Nat -> Real
  epsc : Nat -> Real
  kappaC : Real
  kappaPrime : Real
  theta2 : Real
  reserve : Real

/-- Exact common assignments and the complete budget on the actual chosen spine. -/
structure SourceLocalBudget (beta varpi eps1 : Real) (rawGain rawDens : Real -> Real)
    (s : Real) (a : SourceLocalAccuracyData) : Prop where
  accuracy_pos : 0 < s
  accuracy_le_one : s <= 1
  accuracy_le_margin : s <= ML2Spine.spineNu beta varpi eps1
    (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) / 100
  accuracy_le_parent : forall m : Nat, m < ML2Spine.spineCount varpi eps1 ->
    s <= sourceParentMinimum (ML2Spine.spineDiv varpi eps1)
      (ML2Spine.spineRung beta varpi eps1
        (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) (m + 1))
      (rawGain ((ML2Spine.spineRung beta varpi eps1
        (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) (m + 1)) / 16))
      (rawDens ((ML2Spine.spineRung beta varpi eps1
        (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) (m + 1)) / 16)) / 100
  accuracy_le_scaled_gain : forall m : Nat, m < ML2Spine.spineCount varpi eps1 ->
    s <= ML2Spine.spineDiv varpi eps1 *
      rawGain ((ML2Spine.spineRung beta varpi eps1
        (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) (m + 1)) / 16) / 1000
  fine_eq : forall m : Nat, a.epsf m = s
  parent_accuracy_eq : forall m : Nat, a.epsParent m = s
  outer_accuracy_eq : forall m : Nat, a.epsOuter m = s
  coarse_density_eq : a.kappaC = s
  splitting_eq : a.kappaPrime = s
  terminal_accuracy_eq : a.theta2 = s
  parent_charge_eq : forall m : Nat,
    a.epsp m = a.epsParent m + 2 * sourceParentMinimum (ML2Spine.spineDiv varpi eps1)
      (ML2Spine.spineRung beta varpi eps1
        (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) (m + 1))
      (rawGain ((ML2Spine.spineRung beta varpi eps1
        (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) (m + 1)) / 16))
      (rawDens ((ML2Spine.spineRung beta varpi eps1
        (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) (m + 1)) / 16))
  coarse_charge_eq : forall m : Nat, a.epsc m = a.epsOuter m + a.kappaC
  reserve_eq : a.reserve = s
  fine_pos : forall m : Nat, 0 < a.epsf m
  parent_accuracy_pos : forall m : Nat, 0 < a.epsParent m
  outer_accuracy_pos : forall m : Nat, 0 < a.epsOuter m
  coarse_density_pos : 0 < a.kappaC
  splitting_pos : 0 < a.kappaPrime
  terminal_accuracy_pos : 0 < a.theta2
  parent_charge_pos : forall m : Nat, m < ML2Spine.spineCount varpi eps1 -> 0 < a.epsp m
  coarse_charge_pos : forall m : Nat, 0 < a.epsc m
  reserve_pos : 0 < a.reserve
  input_budget : forall etaIn : Real, 0 < etaIn -> etaIn <= s ->
    forall m : Nat, m < ML2Spine.spineCount varpi eps1 ->
      And
        (a.kappaC + ML2Spine.spineRung beta varpi eps1
          (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) m <=
          2 * sourceParentMinimum (ML2Spine.spineDiv varpi eps1)
            (ML2Spine.spineRung beta varpi eps1
              (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) (m + 1))
            (rawGain ((ML2Spine.spineRung beta varpi eps1
              (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) (m + 1)) / 16))
            (rawDens ((ML2Spine.spineRung beta varpi eps1
              (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) (m + 1)) / 16)))
        (And (0 < a.reserve)
          (6 * ML2Spine.spineNu beta varpi eps1
              (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) +
            a.theta2 + etaIn + a.epsf m + a.epsp m +
            (a.epsc m + ML2Spine.spineRung beta varpi eps1
              (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) m) +
            a.kappaPrime + a.reserve <=
            sourceMiddleNetGain (ML2Spine.spineDiv varpi eps1)
              (rawGain ((ML2Spine.spineRung beta varpi eps1
                (sourceChoiceGain beta rawGain rawDens) (sourceChoiceDens beta rawDens) (m + 1)) / 16))))

/-- One positive accuracy and reserve work for every later admissible input exponent. -/
theorem sourceSpine_exists_local_budget {beta varpi eps1 : Real}
    {rawGain rawDens : Real -> Real}
    (hbeta0 : 0 < beta) (hbeta1 : beta <= 1) (heps1 : 0 < eps1)
    (hp : Lemma91ParamsAt.{u} beta varpi rawGain rawDens) :
    exists s : Real, exists a : SourceLocalAccuracyData,
      SourceLocalBudget beta varpi eps1 rawGain rawDens s a := by
  letI := Classical.decEq Real
  let G := sourceChoiceGain beta rawGain rawDens
  let D := sourceChoiceDens beta rawDens
  let N := ML2Spine.spineCount varpi eps1
  let e := ML2Spine.spineDiv varpi eps1
  let rung := ML2Spine.spineRung beta varpi eps1 G D
  let c := ML2Spine.spineNu beta varpi eps1 G D
  let v := fun m => rawGain (rung (m + 1) / 16)
  let d := fun m => rawDens (rung (m + 1) / 16)
  let P := fun m => sourceParentMinimum e (rung (m + 1)) (v m) (d m)
  let A := fun m => e * v m
  have hchoice := sourceParameterChoice hbeta0 hbeta1 hp
  have hc0 : 0 < c := ML2Spine.spineNu_pos hbeta0 hp.window_pos heps1
    hchoice.params.gain_pos hchoice.params.dens_pos
  have hparent (m : Nat) (hm : m < N) :
      SourceParentMinBounds beta c e (rung m) (rung (m + 1)) (v m) (d m) :=
    sourceSpine_parent_min_bounds hbeta0 hbeta1 heps1 hp m hm
  let caps : Finset Real := insert 1 (insert (c / 100)
    ((Finset.range N).image fun m => min (P m / 100) (A m / 1000)))
  have hcaps : caps.Nonempty := ⟨1, by simp [caps]⟩
  have hcaps0 : forall x, x ∈ caps -> 0 < x := by
    intro x hx
    simp only [caps, Finset.mem_insert, Finset.mem_image, Finset.mem_range] at hx
    rcases hx with rfl | rfl | ⟨m, hm, rfl⟩
    · norm_num
    · positivity
    · have hp0 : 0 < P m := (hparent m hm).parent_pos
      have hA0 : 0 < A m := (hparent m hm).scaled_gain_pos
      exact lt_min (by positivity) (by positivity)
  let s := caps.min' hcaps
  have hs0 : 0 < s := hcaps0 _ (caps.min'_mem hcaps)
  have hs1 : s <= 1 := caps.min'_le _ (by simp [caps])
  have hsc : s <= c / 100 := caps.min'_le _ (by simp [caps])
  have hsboth (m : Nat) (hm : m < N) :
      s <= min (P m / 100) (A m / 1000) := by
    apply caps.min'_le
    simp only [caps, Finset.mem_insert, Finset.mem_image, Finset.mem_range]
    exact Or.inr (Or.inr ⟨m, hm, rfl⟩)
  have hsP (m : Nat) (hm : m < N) : s <= P m / 100 :=
    (hsboth m hm).trans (min_le_left _ _)
  have hsA (m : Nat) (hm : m < N) : s <= A m / 1000 :=
    (hsboth m hm).trans (min_le_right _ _)
  let a : SourceLocalAccuracyData := {
    epsf := fun _ => s
    epsParent := fun _ => s
    epsOuter := fun _ => s
    epsp := fun m => s + 2 * P m
    epsc := fun _ => s + s
    kappaC := s
    kappaPrime := s
    theta2 := s
    reserve := s }
  refine ⟨s, a, {
    accuracy_pos := hs0
    accuracy_le_one := hs1
    accuracy_le_margin := hsc
    accuracy_le_parent := hsP
    accuracy_le_scaled_gain := hsA
    fine_eq := fun _ => rfl
    parent_accuracy_eq := fun _ => rfl
    outer_accuracy_eq := fun _ => rfl
    coarse_density_eq := rfl
    splitting_eq := rfl
    terminal_accuracy_eq := rfl
    parent_charge_eq := fun _ => rfl
    coarse_charge_eq := fun _ => rfl
    reserve_eq := rfl
    fine_pos := fun _ => hs0
    parent_accuracy_pos := fun _ => hs0
    outer_accuracy_pos := fun _ => hs0
    coarse_density_pos := hs0
    splitting_pos := hs0
    terminal_accuracy_pos := hs0
    parent_charge_pos := ?_
    coarse_charge_pos := fun _ => add_pos hs0 hs0
    reserve_pos := hs0
    input_budget := ?_ }⟩
  · intro m hm
    change 0 < s + 2 * P m
    have hp0 : 0 < P m := (hparent m hm).parent_pos
    positivity
  · intro etaIn _ hetaIn m hm
    change s + rung m <= 2 * P m ∧ 0 < s ∧
      6 * c + s + etaIn + s + (s + 2 * P m) + (s + s + rung m) + s + s <=
        sourceMiddleNetGain e (v m)
    have hp0 : 0 < P m := (hparent m hm).parent_pos
    have hqP : rung m <= beta * P m / 100 := (hparent m hm).rung_le_beta_parent
    have hbetaP : beta * P m <= P m := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hbeta1 hp0.le
    have hfixed : 6 * c + 2 * P m + rung m <= A m / 100 :=
      (hparent m hm).fixed_cost
    have hA0 : 0 < A m := (hparent m hm).scaled_gain_pos
    have hnet : sourceMiddleNetGain e (v m) = A m / 4 :=
      (sourceSpine_middle_preparation hbeta0 hbeta1 heps1 hp m hm).net_gain_eq
    refine ⟨?_, hs0, ?_⟩
    · linarith only [hsP m hm, hqP, hbetaP, hp0]
    · linarith only [hfixed, hsA m hm, hetaIn, hnet, hA0]

end Kakeya.ML2Assembly
