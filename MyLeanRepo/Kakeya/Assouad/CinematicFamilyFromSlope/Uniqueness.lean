import MyLeanRepo.Kakeya.Assouad.CinematicFamilyFromSlope.LowerBound

/-!
# Uniqueness of slope curve representation

If the same C2Function represents two parameter triples, the triples must be equal.
-/

noncomputable section

namespace Kakeya.Assouad

/-- The parameter triple representing a slope curve is unique. -/
theorem slopeCurve_rep_unique (f : SlopeFunction)
    (h_ns : f.IsNonsingular) (h0 : f 0 = 0)
    (g : Kakeya.Cinematic.C2Function)
    (a₁ b₁ d₁ a₂ b₂ d₂ : ℝ)
    (h₁ : RepresentsSlopeCurve g f a₁ b₁ d₁)
    (h₂ : RepresentsSlopeCurve g f a₂ b₂ d₂) :
    a₁ = a₂ ∧ b₁ = b₂ ∧ d₁ = d₂ := by
  let zero : Kakeya.Cinematic.UnitPoint := ⟨0, by simp [Kakeya.Cinematic.unitInterval]⟩
  have h0' : (zero : ℝ) = 0 := by rfl
  have h_f0_in : (0 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by norm_num
  have h_fp0_ne : deriv f 0 ≠ 0 := by
    have h : 1 ≤ |deriv f 0| := (h_ns 0 h_f0_in).1
    have h' : 0 < |deriv f 0| := by linarith
    exact abs_pos.mp h'
  have h_val1 : g zero = a₁ := by
    have h := (h₁ zero).1
    simpa [h0', slopeCurveFunction, h0] using h
  have h_val2 : g zero = a₂ := by
    have h := (h₂ zero).1
    simpa [h0', slopeCurveFunction, h0] using h
  have ha : a₁ = a₂ := by
    linarith
  have h_der1 : g.firstDeriv zero = b₁ * deriv f 0 := by
    have h := (h₁ zero).2.1
    rw [h, deriv_slopeCurveFunction f a₁ b₁ d₁ 0]
    <;> simp [h0] <;> ring
  have h_der2 : g.firstDeriv zero = b₂ * deriv f 0 := by
    have h := (h₂ zero).2.1
    rw [h, deriv_slopeCurveFunction f a₂ b₂ d₂ 0]
    <;> simp [h0] <;> ring
  have hb : b₁ = b₂ := by
    have h_eq : b₁ * deriv f 0 = b₂ * deriv f 0 := by
      rw [←h_der1, h_der2]
    apply mul_left_cancel₀ h_fp0_ne
    linarith
  have h_der3 : g.secondDeriv zero =
      b₁ * deriv (deriv f) 0 + 2 * d₁ * deriv f 0 := by
    have h := (h₁ zero).2.2
    rw [h, deriv2_slopeCurveFunction f a₁ b₁ d₁ 0]
    <;> simp [h0] <;> ring
  have h_der4 : g.secondDeriv zero =
      b₂ * deriv (deriv f) 0 + 2 * d₂ * deriv f 0 := by
    have h := (h₂ zero).2.2
    rw [h, deriv2_slopeCurveFunction f a₂ b₂ d₂ 0]
    <;> simp [h0] <;> ring
  have h_eq2 : b₁ * deriv (deriv f) 0 + 2 * d₁ * deriv f 0 =
      b₂ * deriv (deriv f) 0 + 2 * d₂ * deriv f 0 := by
    rw [←h_der3, h_der4]
  have hd : d₁ = d₂ := by
    rw [hb] at h_eq2
    have h : 2 * d₁ * deriv f 0 = 2 * d₂ * deriv f 0 := by linarith
    have h' : d₁ * deriv f 0 = d₂ * deriv f 0 := by linarith
    apply mul_left_cancel₀ h_fp0_ne
    linarith
  exact ⟨ha, hb, hd⟩

end Kakeya.Assouad
