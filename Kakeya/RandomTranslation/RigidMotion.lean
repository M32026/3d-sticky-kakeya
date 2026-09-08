/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.RandomTranslation.RotationDirection
public import Kakeya.RandomTranslation.TranslationProb

/-!
# Random rigid motions

GWZ Lemma 3.8 randomises a family of `δ`-tubes by applying `J` independent **rigid motions**, a
random rotation composed with a random translation of size `≤ 1`. The repository previously had only
the translational half; this file assembles the full model.

## The model

There is no class: the sample space is a concrete product,

`Ω := unitary (E →L[ℝ] E) × E`,  `rigidMeasure := rotHaar.prod (uniformBallMeasure E)`,

so independence of the rotational and translational components is not an axiom but the definition of
`MeasureTheory.Measure.prod`, and Fubini/Tonelli applies verbatim. Both factors are probability
measures, hence so is the product.

The action is `rigidMap u v x = u x + v`, an isometry of `E` (`Kakeya.isometry_rigidMap`), and it
carries `δ`-tubes to `δ`-tubes (`Tube.rigidMove`), rotating the axis and translating the centre.

## What this feeds

* the rotational factor `≲ δ^(n-1)` of GWZ (106) comes from `Kakeya.rotHaar_projectiveCap_le`
  applied to `Tube.rigidMove_direction`;
* the translational factor `≲ δ^(n-1)` comes from the existing
  `Kakeya.prob_tube_translate_subset_le`;
* their product is (106), obtained by integrating the translational bound over the rotation variable
  against the rotational bound.
-/

@[expose] public section

open MeasureTheory Metric Set

namespace Kakeya

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The rigid motion determined by a rotation `u` and a translation vector `v`. -/
def rigidMap (u : unitary (E →L[ℝ] E)) (v : E) : E → E :=
  fun x => (u : E →L[ℝ] E) x + v

omit [MeasurableSpace E] [BorelSpace E] in
@[simp]
theorem rigidMap_apply (u : unitary (E →L[ℝ] E)) (v x : E) :
    rigidMap u v x = (u : E →L[ℝ] E) x + v := rfl

omit [MeasurableSpace E] [BorelSpace E] in
/-- A rigid motion is an isometry of `E`. -/
theorem isometry_rigidMap (u : unitary (E →L[ℝ] E)) (v : E) :
    Isometry (rigidMap u v) := by
  rw [isometry_iff_dist_eq]
  intro x y
  calc
    dist (rigidMap u v x) (rigidMap u v y) =
        ‖(u : E →L[ℝ] E) x + v - ((u : E →L[ℝ] E) y + v)‖ := by
      rw [rigidMap_apply, rigidMap_apply, dist_eq_norm]
    _ = ‖(u : E →L[ℝ] E) x - (u : E →L[ℝ] E) y‖ := by
      rw [add_sub_add_right_eq_sub]
    _ = ‖(u : E →L[ℝ] E) (x - y)‖ := by
      rw [map_sub]
    _ = ‖x - y‖ := by
      rw [norm_apply_of_mem_unitary (u := (u : E →L[ℝ] E)) u.property (x - y)]
    _ = dist x y := by
      rw [dist_eq_norm]

omit [MeasurableSpace E] [BorelSpace E] in
omit [MeasurableSpace E] [BorelSpace E] in
theorem rigidMap_image_closedBall (u : unitary (E →L[ℝ] E)) (v c : E) (ρ : ℝ) :
    rigidMap u v '' closedBall c ρ = closedBall (rigidMap u v c) ρ := by
  change (fun x : E => (u : E →L[ℝ] E) x + v) '' closedBall c ρ =
      closedBall ((u : E →L[ℝ] E) c + v) ρ
  rw [show (fun x : E => (u : E →L[ℝ] E) x + v) =
      (fun s : E => s + v) ∘ (u : E →L[ℝ] E) by funext x; rfl]
  rw [Set.image_comp]
  have hortho : (u : E →L[ℝ] E) '' closedBall c ρ =
      closedBall ((u : E →L[ℝ] E) c) ρ := by
    rw [← Unitary.coe_linearIsometryEquiv_apply u]
    exact (Unitary.linearIsometryEquiv u).image_closedBall c ρ
  rw [hortho]
  simp [add_comm]

omit [MeasurableSpace E] [BorelSpace E] in
omit [MeasurableSpace E] [BorelSpace E] in
theorem rigidMap_image_segment (u : unitary (E →L[ℝ] E)) (v a b : E) :
    rigidMap u v '' segment ℝ a b = segment ℝ (rigidMap u v a) (rigidMap u v b) := by
  let Φ : E →ᵃ[ℝ] E :=
    { toFun := rigidMap u v
      linear := (u : E →L[ℝ] E)
      map_vadd' := by
        intro p w
        simp [rigidMap, map_add, add_assoc] }
  have hΦ : rigidMap u v = (Φ : E → E) := by
    funext x
    rfl
  rw [hΦ]
  exact image_segment ℝ Φ a b

/-- **The probability space of random rigid motions**: a random rotation, distributed according to
Haar measure on the compact rotation group, together with an independent translation vector drawn
uniformly from the closed unit ball. Independence is not assumed — it is the definition of
`MeasureTheory.Measure.prod`. -/
def rigidMeasure (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] :
    Measure (unitary (E →L[ℝ] E) × E) :=
  (rotHaar (E := E)).prod (uniformBallMeasure E)

instance instIsProbabilityMeasureRigidMeasure :
    IsProbabilityMeasure (rigidMeasure E) := by
  rw [rigidMeasure]
  infer_instance

end

end Kakeya

namespace Tube

open Metric Set MeasureTheory Kakeya

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {δ : NNReal}

/-- **A rigid motion carries a `δ`-tube to a `δ`-tube.** -/
noncomputable def rigidMove (T : Tube δ E) (u : unitary (E →L[ℝ] E)) (v : E) : Tube δ E :=
  Tube.mk' δ (x := Kakeya.rigidMap u v T.x) (y := Kakeya.rigidMap u v T.y) (by
    rw [(Kakeya.isometry_rigidMap u v).dist_eq, T.dist_eq_one])

@[simp]
theorem rigidMove_x (T : Tube δ E) (u : unitary (E →L[ℝ] E)) (v : E) :
    (T.rigidMove u v).x = Kakeya.rigidMap u v T.x := rfl

@[simp]
theorem rigidMove_y (T : Tube δ E) (u : unitary (E →L[ℝ] E)) (v : E) :
    (T.rigidMove u v).y = Kakeya.rigidMap u v T.y := rfl

/-- The carrier of the moved tube is the image of the carrier. -/
theorem rigidMove_carrier (T : Tube δ E) (u : unitary (E →L[ℝ] E)) (v : E) :
    (T.rigidMove u v).carrier = Kakeya.rigidMap u v '' T.carrier := by
  simp only [Tube.carrier_eq, rigidMove_x, rigidMove_y, Set.image_iUnion₂,
    Kakeya.rigidMap_image_closedBall, ← Kakeya.rigidMap_image_segment, Set.biUnion_image]

/-- A rigid motion rotates the axis of a tube. -/
theorem rigidMove_direction (T : Tube δ E) (u : unitary (E →L[ℝ] E)) (v : E) :
    (T.rigidMove u v).direction = (u : E →L[ℝ] E) T.direction := by
  dsimp [Tube.direction]
  rw [map_sub]
  simp

end Tube

end
