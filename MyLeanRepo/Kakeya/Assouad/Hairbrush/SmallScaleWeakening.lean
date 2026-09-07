import MyLeanRepo.Kakeya.Assouad.Subunit.HairbrushSelfContainedLeaves

/-!
# Helper lemma: weaken HairbrushFiberTarget scale from confinementScale to theta

If theta ≤ confinementScale, then a target proved at confinementScale implies
one at theta, since sqrt is monotone and the LHS is monotone in the scale.
-/

noncomputable section

open MeasureTheory Metric Set Finset Real

attribute [local instance] Classical.propDecidable

namespace Kakeya.Assouad

/-- Weaken `HairbrushFiberTarget` from a larger scale to a smaller one. -/
lemma weaken_fiber_target_scale
    {δ theta confinementScale loss : ℝ}
    {F : Kakeya.TubeFamily δ}
    {Y : Kakeya.Shading F}
    (htheta_le_conf : theta ≤ confinementScale)
    (h : HairbrushFiberTarget (theta := confinementScale) (loss := loss) Y) :
    HairbrushFiberTarget (theta := theta) (loss := loss) Y := by
  have h_sqrt_nonneg : 0 ≤ Real.sqrt theta := Real.sqrt_nonneg _
  have h_sqrt_le : Real.sqrt theta ≤ Real.sqrt confinementScale :=
    Real.sqrt_le_sqrt (by linarith)
  have h9 : ENNReal.ofReal (Real.sqrt theta) ≤ ENNReal.ofReal (Real.sqrt confinementScale) :=
    ENNReal.ofReal_le_ofReal h_sqrt_le
  let a : ENNReal := Kakeya.realRpowENN δ (3 / 2 + loss)
  let b_conf : ENNReal := ENNReal.ofReal (Real.sqrt confinementScale)
  let b_theta : ENNReal := ENNReal.ofReal (Real.sqrt theta)
  let c : ENNReal := ENNReal.rpow F.enncard (1 / 2)
  have h11 : a * b_theta ≤ a * b_conf :=
    mul_le_mul (le_refl a) h9 (by simp) (by simp)
  have h10 : a * b_theta * c ≤ a * b_conf * c :=
    mul_le_mul h11 (le_refl c) (by simp) (by simp)
  have h_goal : a * b_conf * c ≤ volume Y.union := h
  exact h10.trans h_goal

end Kakeya.Assouad
