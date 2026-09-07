import MyLeanRepo.Kakeya.Assouad.Statements
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
WZ2 Section 7: normalize the negative vertical half-window by reflecting the
slope and the cinematic vertical parameter.
-/

namespace Kakeya.Assouad

theorem reflected_slope_cinematic :
    ReflectedSlopeCinematicStatement := by
  intro f hf
  let g : ℝ → ℝ := fun z => f (-z)
  have hg_eq : g = f.reflected := by
    funext z
    rfl
  have hcd : ContDiff ℝ 2 f := f.contDiff
  have hdiff : Differentiable ℝ f :=
    ContDiff.differentiable hcd (by norm_num)
  have hdiff2 : Differentiable ℝ (deriv f) :=
    ContDiff.differentiable_deriv_two hcd

  have h1 : ∀ z : ℝ, deriv g z = -deriv f (-z) := by
    intro z
    have hfa : HasDerivAt f (deriv f (-z)) (-z) :=
      hdiff.differentiableAt.hasDerivAt
    have hneg : HasDerivAt (fun x : ℝ => -x) (-1 : ℝ) z :=
      hasDerivAt_neg z
    have h : HasDerivAt g ((deriv f (-z)) * (-1 : ℝ)) z :=
      hfa.comp z hneg
    simpa [g, mul_neg_one] using h.deriv

  have h_deriv_g : deriv g = fun x : ℝ => -deriv f (-x) := by
    funext x
    exact h1 x

  have h2 : ∀ z : ℝ, deriv (deriv g) z = deriv (deriv f) (-z) := by
    intro z
    have hfa2 : HasDerivAt (deriv f) (deriv (deriv f) (-z)) (-z) :=
      hdiff2.differentiableAt.hasDerivAt
    have hneg : HasDerivAt (fun x : ℝ => -x) (-1 : ℝ) z :=
      hasDerivAt_neg z
    have h3 : HasDerivAt (fun x : ℝ => deriv f (-x))
        ((deriv (deriv f) (-z)) * (-1 : ℝ)) z :=
      hfa2.comp z hneg
    have h4 : HasDerivAt (fun x : ℝ => -deriv f (-x))
        (-((deriv (deriv f) (-z)) * (-1 : ℝ))) z :=
      h3.neg
    have h5 :
        deriv (deriv g) z =
          deriv (fun x : ℝ => -deriv f (-x)) z := by
      rw [h_deriv_g]
    rw [h5]
    have h6 := h4.deriv
    rw [h6]
    ring

  constructor
  · intro z hz
    have hneg_z : -z ∈ Set.Icc (-1 : ℝ) 1 := by
      simp only [Set.mem_Icc] at hz ⊢
      constructor <;> linarith
    rcases hf (-z) hneg_z with ⟨h61, h62, h63⟩
    have h71 : 1 ≤ |deriv f.reflected z| := by
      have h : deriv f.reflected z = -deriv f (-z) := by
        simpa [hg_eq] using h1 z
      rw [h, abs_neg]
      exact h61
    have h72 : |deriv f.reflected z| ≤ 2 := by
      have h : deriv f.reflected z = -deriv f (-z) := by
        simpa [hg_eq] using h1 z
      rw [h, abs_neg]
      exact h62
    have h73 : |deriv (deriv f.reflected) z| ≤ 1 / 100 := by
      have h :
          deriv (deriv f.reflected) z = deriv (deriv f) (-z) := by
        simpa [hg_eq, h_deriv_g] using h2 z
      rw [h]
      exact h63
    exact ⟨h71, h72, h73⟩
  · intro a b d z
    simp [cinematicEval, SlopeFunction.reflected]

end Kakeya.Assouad
