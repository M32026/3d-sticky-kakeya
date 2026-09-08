/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Tube.Basic

/-!
# The core-segment parameter of a point of a tube

`Tube.exists_param_of_mem_carrier` unpacks `Tube.carrier_eq`: a point of a `δ`-tube lies within
`δ` of the point of the core segment at some signed distance `t ∈ [-1/2, 1/2]` from the
midpoint. This is the only fact about membership in a tube that the bush bound
(`Kakeya/Tube/CommonPoint.lean` and `Kakeya/DimensionThree/BushCount.lean`) uses.
-/

@[expose] public section

namespace Tube

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [ProperSpace E]

/-- Signed parameter of a point of a `δ`-tube along its core segment: every `p ∈ T.carrier`
lies within `δ` of the point of the core segment at signed distance `t` from the midpoint,
for some `|t| ≤ 1 / 2`. -/
lemma exists_param_of_mem_carrier {δ : NNReal} (T : Tube δ E) {p : E} (hp : p ∈ T.carrier) :
    ∃ t : ℝ, |t| ≤ 1 / 2 ∧ ‖p - T.midpoint - t • T.direction‖ ≤ (δ : ℝ) := by
  rw [T.carrier_eq] at hp
  obtain ⟨z, hz_seg, hpz⟩ := Set.mem_iUnion₂.mp hp
  obtain ⟨a, b, ha, hb, hab, hz_eq⟩ := hz_seg
  set t := b - 1/2 with ht_def
  refine ⟨t, ?_, ?_⟩
  · have hb_le_one : b ≤ 1 := by
      have ha_nonneg : 0 ≤ a := ha
      linarith
    have h_low : -(1 / 2 : ℝ) ≤ t := by dsimp [t]; linarith
    have h_high : t ≤ 1 / 2 := by dsimp [t]; linarith
    exact abs_le.mpr ⟨h_low, h_high⟩
  · have h_pz : ‖p - z‖ ≤ (δ : ℝ) := by
      rw [Metric.mem_closedBall, dist_eq_norm] at hpz
      exact hpz
    have h_eq : p - T.midpoint - t • T.direction = p - z := by
      have ha_eq : a = 1 - b := by linarith
      have h_sub : p - T.midpoint - t • T.direction - (p - z) = 0 := by
        dsimp [t, Tube.midpoint, Tube.direction]
        rw [← hz_eq, ha_eq]
        module
      calc
        p - T.midpoint - t • T.direction
            = (p - T.midpoint - t • T.direction - (p - z)) + (p - z) := by abel
        _ = 0 + (p - z) := by rw [h_sub]
        _ = p - z := by simp
    rw [h_eq]
    exact h_pz

end Tube
