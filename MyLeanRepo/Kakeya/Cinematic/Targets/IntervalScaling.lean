import MyLeanRepo.Kakeya.Cinematic.Statements

/-!
# Centered interval scaling API

Low-risk infrastructure for PYZ Lemmas 18 and 22. This target verifies that
the centered interval representation has the expected monotonicity, identity,
and diameter behavior.
-/

namespace Kakeya.Cinematic

theorem interval_scaling_api : IntervalScalingStatement := by
  have h_mono : ∀ (I : ParameterInterval) (q r : ℝ),
      0 ≤ q → q ≤ r → I.centeredCarrier q ⊆ I.centeredCarrier r := by
    intro I q r hq hqr x hx
    have h3 : q * I.length / 2 ≤ r * I.length / 2 := by
      have hlen : 0 ≤ I.length := I.length_nonneg
      gcongr
    exact hx.trans h3
  have h_id : ∀ (I : ParameterInterval), I.centeredCarrier 1 = I.carrier := by
    exact ParameterInterval.centeredCarrier_one
  have h_diam : ∀ (I : ParameterInterval) (q : ℝ), 0 ≤ q →
      ∀ x ∈ I.centeredCarrier q, ∀ y ∈ I.centeredCarrier q,
        |(x : ℝ) - y| ≤ q * I.length := by
    intro I q hq x hx y hy
    have h1 : |(x : ℝ) - I.midpoint| ≤ q * I.length / 2 := hx
    have h2 : |(y : ℝ) - I.midpoint| ≤ q * I.length / 2 := hy
    have h3 : |(x : ℝ) - y| ≤ |(x : ℝ) - I.midpoint| + |(y : ℝ) - I.midpoint| := by
      calc
        |(x : ℝ) - y|
          = |((x : ℝ) - I.midpoint) - ((y : ℝ) - I.midpoint)| := by ring_nf
        _ ≤ |(x : ℝ) - I.midpoint| + |(y : ℝ) - I.midpoint| := by
          exact abs_sub _ _
    linarith
  exact ⟨h_mono, h_id, h_diam⟩

end Kakeya.Cinematic
