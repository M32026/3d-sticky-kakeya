/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.Factorization

/-!
# The eccentricity regime of GWZ Proposition 6.6(B), pinned

`Kakeya.tubeMultiplicityOfGlobalPlankFactorisation`
(`Kakeya/DimensionThree/Plank/Factorization.lean`) constrains the plank half-widths only by
`a ≤ b ≤ 1` together with `δ ^ (1 - ε₂) ≤ ρ ≤ a`.  Its eccentricity `b / a` is therefore bounded
only by `δ ^ (-(1 - ε₂))`, a *polynomial* power of the scale, and the whole of that range is inside
the statement's domain.

This file pins that, because it is the boundary at which a whole family of candidate cores fails to
apply.  A Part-(B) core proved under a **bounded-eccentricity** antecedent of the shape

`b * δ ^ ηecc ≤ a`  with  `ηecc < η`

covers only eccentricities up to `δ ^ (-ηecc)`.  In every such core `η` is the fullness exponent
produced existentially by `Kakeya.PlankEstimateAtMasterScaleWithDensity`, hence arbitrarily small
and *not* under the caller's control, so `ηecc` is arbitrarily small too.
`Kakeya.Prop66BEccentricity.exists_outside_boundedEccentricity` exhibits, for every `ε₂ < 1` and
every `δ ∈ (0, 1)`, a triple `(ρ, a, b)` satisfying every scale binder of Proposition 6.6(B) and
falsifying the antecedent for **every** `ηecc < 1 - ε₂` at once.

Consequently such a core cannot discharge `Kakeya.tubeMultiplicityOfGlobalPlankFactorisation`: it
proves the proposition on a proper sub-regime of its own domain, and the excluded part is the
eccentric one, which is the part carrying the `(a / b) ^ β` gain that the proposition exists to
assert.

The witness is the extreme point of the scale binders, `ρ = a = δ ^ (1 - ε₂)` and `b = 1`: the
coarse scale sits exactly at the floor the coarse-scale narrowing
(`Kakeya/DimensionThree/Plank/Prop66BCoarseScale.lean`) imposes, and the plank is as wide as the
unit-ball window allows.  It is not a pathological configuration — it is the configuration
`Kakeya.ML2Reduction.plankScale` produces.
-/

@[expose] public section

open scoped NNReal ENNReal

noncomputable section

namespace Kakeya

namespace Prop66BEccentricity

/-- **The scale binders of GWZ Proposition 6.6(B) allow eccentricity `δ ^ (-(1 - ε₂))`.**

For every `ε₂ ∈ (0, 1)` and every `δ ∈ (0, 1)` there are `ρ, a, b` with `a ≤ b ≤ 1`,
`δ ^ (1 - ε₂) ≤ ρ` and `ρ ≤ a` — every scale hypothesis Proposition 6.6(B) imposes — for which the
bounded-eccentricity antecedent `b * δ ^ ηecc ≤ a` is **false for every** `ηecc < 1 - ε₂`.

Since a core whose fullness exponent `η` is supplied by
`Kakeya.PlankEstimateAtMasterScaleWithDensity` may have `η` arbitrarily small, and its antecedent
requires `ηecc < η`, this exhibits a point of Proposition 6.6(B)'s domain outside every such
core's. -/
theorem exists_outside_boundedEccentricity
    {ε₂ : ℝ} (hε₂0 : 0 < ε₂) (hε₂1 : ε₂ < 1) {δ : ℝ≥0} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ ρ a b : ℝ≥0, a ≤ b ∧ b ≤ 1 ∧ (δ : ℝ≥0) ^ (1 - ε₂) ≤ ρ ∧ ρ ≤ a ∧
      ∀ ηecc : ℝ, ηecc < 1 - ε₂ → ¬ (b * (δ : ℝ≥0) ^ ηecc ≤ a) := by
  have hexp : (0 : ℝ) < 1 - ε₂ := by linarith
  refine ⟨δ ^ (1 - ε₂), δ ^ (1 - ε₂), 1, ?_, le_rfl, le_rfl, le_rfl, ?_⟩
  · exact NNReal.rpow_le_one hδ1.le hexp.le
  · intro ηecc hηecc hcon
    rw [one_mul] at hcon
    exact absurd hcon
      (not_le.2 (NNReal.rpow_lt_rpow_of_exponent_gt hδ0 hδ1 hηecc))

/-- **The same statement, read as the eccentricity ratio.**  At the witness the plank is as
eccentric as the coarse-scale floor permits: `b / a = δ ^ (-(1 - ε₂))`. -/
theorem eccentricity_at_witness {ε₂ : ℝ} (hε₂1 : ε₂ < 1) {δ : ℝ≥0} (hδ0 : 0 < δ) :
    (1 : ℝ≥0) / (δ ^ (1 - ε₂)) = δ ^ (-(1 - ε₂)) := by
  rw [NNReal.rpow_neg, one_div]

end Prop66BEccentricity

end Kakeya

end

end
