import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.TubeContainment

/-!
# Changing a tube radius

Several cross-scale arguments compare the same oriented unit segment with
different neighborhood radii.  This module packages that operation and its
carrier monotonicity.
-/

namespace Kakeya.Streamlined.GeometricLemmas

/-- Reuse a tube's oriented axis with a new radius. -/
def withRadius {δ : ℝ} (rho : ℝ) (T : Kakeya.DeltaTube δ) :
    Kakeya.DeltaTube rho where
  base := T.base
  direction := T.direction
  direction_unit := T.direction_unit

@[simp] lemma withRadius_base
    {δ rho : ℝ} (T : Kakeya.DeltaTube δ) :
    (withRadius rho T).base = T.base := rfl

@[simp] lemma withRadius_direction
    {δ rho : ℝ} (T : Kakeya.DeltaTube δ) :
    (withRadius rho T).direction = T.direction := rfl

@[simp] lemma withRadius_midpoint
    {δ rho : ℝ} (T : Kakeya.DeltaTube δ) :
    tubeMidpoint (withRadius rho T) = tubeMidpoint T := rfl

@[simp] lemma withRadius_withRadius
    {δ rho sigma : ℝ} (T : Kakeya.DeltaTube δ) :
    withRadius sigma (withRadius rho T) = withRadius sigma T := by
  rfl

@[simp] lemma withRadius_same
    {δ : ℝ} (T : Kakeya.DeltaTube δ) :
    withRadius δ T = T := by
  cases T
  rfl

lemma withRadius_carrier
    {δ rho : ℝ} (T : Kakeya.DeltaTube δ) :
    (withRadius rho T).carrier =
      Metric.cthickening rho
        (Kakeya.unitSegment T.base T.direction) := rfl

/-- Enlarging the radius preserves carrier containment. -/
lemma carrier_subset_withRadius
    {δ rho : ℝ} (h : δ ≤ rho) (T : Kakeya.DeltaTube δ) :
    T.carrier ⊆ (withRadius rho T).carrier := by
  rw [Kakeya.DeltaTube.carrier, withRadius_carrier]
  exact Metric.cthickening_mono h _

/-- The new-radius carrier is monotone in the radius. -/
lemma withRadius_carrier_mono
    {δ rho sigma : ℝ} (h : rho ≤ sigma)
    (T : Kakeya.DeltaTube δ) :
    (withRadius rho T).carrier ⊆
      (withRadius sigma T).carrier := by
  rw [withRadius_carrier, withRadius_carrier]
  exact Metric.cthickening_mono h _

end Kakeya.Streamlined.GeometricLemmas
