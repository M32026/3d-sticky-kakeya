import MyLeanRepo.Kakeya.Cinematic.Section5.DyadicFineAssignmentData
import MyLeanRepo.Kakeya.Cinematic.Section5.SingletonFiberScaleAbsorption

/-!
# Apply singleton-fiber absorption to dyadic assignment data

This wrapper connects the pure scale theorem to the exact representative
scales and safe uniform fiber count produced by the Section 5 dyadic
assignment.
-/

namespace Kakeya.Cinematic

lemma singleton_fiber_budget_of_uniform_q_one
    (K metricExponent tangencyExponent targetExponent : ℝ)
    (hK : 1 ≤ K)
    (hmetricExponent : 0 < metricExponent)
    (htangencyExponent : 0 < tangencyExponent)
    (hmargin :
      (3 / 2 : ℝ) * (metricExponent + tangencyExponent) <
        targetExponent) :
    ∃ delta₀ : ℝ,
      0 < delta₀ ∧
      delta₀ ≤ 1 ∧
      ∀ {family : Set C2Function} {E : Set (ℝ × ℝ)}
        {delta diameter tRep DeltaRep C_R : ℝ},
        0 < delta →
        delta ≤ delta₀ →
        diameter = K →
        ∀ (data : DyadicFineAssignmentData
            family E K delta diameter metricExponent tangencyExponent
              tRep DeltaRep C_R),
          E.Nonempty →
          ∀ q : ℕ,
            q = 1 →
            Real.rpow (tRep / (8 * diameter)) metricExponent *
                  Real.rpow (DeltaRep / (2 * tRep)) tangencyExponent *
                  (data.mu : ℝ) <
                4 * ((q : ℝ) + 1) →
            1 ≤
              Real.rpow delta (-targetExponent) *
                Real.rpow (data.mu : ℝ) (-3 / 2 : ℝ) := by
  rcases singleton_fiber_scale_absorption
      K metricExponent tangencyExponent targetExponent hK
      hmetricExponent htangencyExponent hmargin with
    ⟨delta₀, hdelta₀_pos, hdelta₀_one, hmain⟩
  refine ⟨delta₀, hdelta₀_pos, hdelta₀_one, ?_⟩
  intro family E delta diameter tRep DeltaRep C_R
    hdelta hdelta₀ hdiameter data hE q hq hlower
  obtain ⟨point, hpoint⟩ := hE
  let p : E := ⟨point, hpoint⟩
  have htRep_le : tRep ≤ 8 * K := by
    rw [← hdiameter]
    exact data.tRep_le_eight_diameter hdelta p
  have hlower_eight :
      Real.rpow (tRep / (8 * K)) metricExponent *
            Real.rpow (DeltaRep / (2 * tRep)) tangencyExponent *
            (data.mu : ℝ) <
          8 := by
    subst diameter
    subst q
    norm_num at hlower ⊢
    exact hlower
  exact hmain hdelta hdelta₀ data.delta_le_DeltaRep
    data.DeltaRep_le_tRep htRep_le data.mu_pos hlower_eight

end Kakeya.Cinematic
