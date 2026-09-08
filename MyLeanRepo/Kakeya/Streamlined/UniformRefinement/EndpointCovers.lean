import MyLeanRepo.Kakeya.Streamlined.UniformScaleGrid

/-!
# Endpoint covers for the paper scale grid

The coarsest paper scale is exactly `1`, where one fixed tube covers the unit
ball. The finest paper scale is exactly `delta`, where the identity cover is
available.
-/

noncomputable section

open Metric

namespace Kakeya.Streamlined

/-- The first distinguished paper scale is the unit scale. -/
@[simp] lemma uniformScale_zero (delta : ℝ) (hdelta_le_one : delta ≤ 1) :
    (uniformScale delta hdelta_le_one
      (⟨0, Nat.succ_pos _⟩ : UniformScaleIndex delta)).1 = 1 := by
  simp [uniformScale, hdelta_le_one]

/-- The last distinguished paper scale is the original fine scale. -/
@[simp] lemma uniformScale_last (delta : ℝ) (hdelta_le_one : delta ≤ 1) :
    (uniformScale delta hdelta_le_one
      (Fin.last (uniformScaleSteps delta))).1 = delta := by
  have hM_pos : 0 < uniformScaleSteps delta := by
    simp [uniformScaleSteps]
  have hM_ne : (uniformScaleSteps delta : ℝ) ≠ 0 := by
    exact_mod_cast hM_pos.ne'
  simp [uniformScale, hM_ne, hdelta_le_one]

/--
The distinguished paper scales decrease with their index.
-/
lemma uniformScale_antitone {delta : ℝ} (hdelta_pos : 0 < delta)
    (hdelta_le_one : delta ≤ 1)
    {k l : UniformScaleIndex delta} (hkl : k ≤ l) :
    (uniformScale delta hdelta_le_one l).1 ≤
      (uniformScale delta hdelta_le_one k).1 := by
  have hM_pos : (0 : ℝ) < uniformScaleSteps delta := by
    exact_mod_cast (show 0 < uniformScaleSteps delta by
      simp [uniformScaleSteps])
  have h_exp :
      (k : ℝ) / (uniformScaleSteps delta : ℝ) ≤
        (l : ℝ) / (uniformScaleSteps delta : ℝ) := by
    gcongr
    exact_mod_cast hkl
  have h_rpow :
      delta ^ ((l : ℝ) / (uniformScaleSteps delta : ℝ)) ≤
        delta ^ ((k : ℝ) / (uniformScaleSteps delta : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hdelta_pos hdelta_le_one h_exp
  simp only [uniformScale]
  gcongr

/-- The identity cover of an indexed tube family. -/
def identityTubeCover {delta : ℝ} (F : TubeFamily delta) : TubeCover F F where
  parent := id
  parent_surjective := Function.surjective_id
  nested := fun _ => Set.Subset.rfl

/-- Every fiber of the identity cover has cardinality one. -/
lemma identityTubeCover_uniform {delta : ℝ} (F : TubeFamily delta) :
    (identityTubeCover F).toFactoring.FibersAreCUniform 1 := by
  constructor
  · norm_num
  · intro j k
    have hfilter (l : Fin F.card) :
        (Finset.univ.filter fun i : Fin F.card =>
          (identityTubeCover F).parent i = l) = {l} := by
      ext i
      simp [identityTubeCover]
    change
      ((Finset.univ.filter fun i : Fin F.card =>
        (identityTubeCover F).parent i = j).card : ENNReal) ≤
        1 * ((Finset.univ.filter fun i : Fin F.card =>
          (identityTubeCover F).parent i = k).card : ENNReal)
    rw [hfilter j, hfilter k]
    norm_num

private def endpointDirection : Point3 :=
  EuclideanSpace.single (0 : Fin 3) 1

private lemma endpointDirection_norm : ‖endpointDirection‖ = 1 := by
  simp [endpointDirection]

/-- A fixed unit-radius tube whose carrier contains the closed unit ball. -/
def unitScaleTube : Kakeya.DeltaTube 1 where
  base := 0
  direction := endpointDirection
  direction_unit := endpointDirection_norm

lemma unitBall_subset_unitScaleTube :
    Kakeya.DeltaTube.unitBall ⊆ unitScaleTube.carrier := by
  intro x hx
  have hzero : (0 : Point3) ∈
      Kakeya.unitSegment unitScaleTube.base unitScaleTube.direction := by
    exact ⟨0, by norm_num, by simp [unitScaleTube]⟩
  have hdist : dist x (0 : Point3) ≤ 1 := by
    simpa [Kakeya.DeltaTube.unitBall, Metric.mem_closedBall] using hx
  exact Metric.mem_cthickening_of_dist_le x 0 1
    (Kakeya.unitSegment unitScaleTube.base unitScaleTube.direction) hzero hdist

/-- The one-member unit-scale family used at the coarsest grid scale. -/
def unitScaleTubeFamily : TubeFamily 1 where
  card := 1
  tube := fun _ => unitScaleTube

private lemma unitScaleIndex_eq
    (i j : Fin unitScaleTubeFamily.card) : i = j := by
  apply Fin.ext
  have hi : i.val < 1 := by
    simpa [unitScaleTubeFamily] using i.isLt
  have hj : j.val < 1 := by
    simpa [unitScaleTubeFamily] using j.isLt
  omega

lemma unitScaleTubeFamily_distinct :
    unitScaleTubeFamily.IsEssentiallyDistinct := by
  intro i j hij
  exact (hij (unitScaleIndex_eq i j)).elim

/-- Every nonempty fine family in the unit ball is covered at scale `1`. -/
def unitScaleTubeCover {delta : ℝ} (F : TubeFamily delta)
    (hF_nonempty : F.Nonempty) (hF_ball : F.IsInUnitBall) :
    TubeCover F unitScaleTubeFamily where
  parent := fun _ => ⟨0, by simp [unitScaleTubeFamily]⟩
  parent_surjective := by
    intro j
    refine ⟨⟨0, hF_nonempty⟩, ?_⟩
    exact unitScaleIndex_eq _ _
  nested := fun i => (hF_ball i).trans unitBall_subset_unitScaleTube

lemma unitScaleTubeCover_uniform {delta : ℝ} (F : TubeFamily delta)
    (hF_nonempty : F.Nonempty) (hF_ball : F.IsInUnitBall) :
    (unitScaleTubeCover F hF_nonempty hF_ball
      ).toFactoring.FibersAreCUniform 1 := by
  constructor
  · norm_num
  · intro j k
    rw [unitScaleIndex_eq j k]
    simp

end Kakeya.Streamlined
