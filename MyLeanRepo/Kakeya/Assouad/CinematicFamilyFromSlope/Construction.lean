import MyLeanRepo.Kakeya.Assouad.CinematicFamilyFromSlope.LowerBound
import MyLeanRepo.Kakeya.Assouad.CinematicBridge
import MyLeanRepo.Kakeya.Cinematic.Definitions
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-!
# Construction of C2Function for slope curves

Defines `slopeCurve f a b d` packaging `t ↦ a + b*f(t) + d*t*f(t)` as a
`C2Function`, and proves it satisfies `RepresentsSlopeCurve`.

Whiteprint node: `slope_curve_construction`.
-/

noncomputable section

open Kakeya.Cinematic Kakeya.Assouad

namespace Kakeya.Assouad

/-- Packages the slope curve as a `C2Function` on the unit interval. -/
def slopeCurve (f : SlopeFunction) (a b d : ℝ) : C2Function :=
  let h := slopeCurveFunction f a b d
  let h1 := fun t : ℝ => b * deriv f t + d * (f t + t * deriv f t)
  let h2 := fun t : ℝ => b * deriv (deriv f) t + d * (2 * deriv f t + t * deriv (deriv f) t)
  have h_cd2 : ContDiff ℝ 2 h := by
    have hf : ContDiff ℝ 2 f := f.contDiff
    have h_id : ContDiff ℝ 2 (fun x : ℝ => x) := contDiff_id
    have h_prod : ContDiff ℝ 2 (fun x : ℝ => x * f x) := h_id.mul hf
    have h_b : ContDiff ℝ 2 (fun x : ℝ => b * f x) := contDiff_const.mul hf
    have h_d : ContDiff ℝ 2 (fun x : ℝ => d * (x * f x)) := contDiff_const.mul h_prod
    have h_sum : ContDiff ℝ 2 (fun x : ℝ => a + b * f x + d * (x * f x)) :=
      (contDiff_const.add h_b).add h_d
    have h_eq : (fun x : ℝ => a + b * f x + d * (x * f x)) = h := by
      funext x
      dsimp only [h, slopeCurveFunction]
      <;> ring
    rw [h_eq] at h_sum
    exact h_sum
  have h1_cd1 : ContDiff ℝ 1 h1 := by
    have hf : ContDiff ℝ 2 f := f.contDiff
    have hf1 : ContDiff ℝ 1 (deriv f) := hf.deriv'
    have h_id : ContDiff ℝ 1 (fun x : ℝ => x) := contDiff_id
    have h_f : ContDiff ℝ 1 f := hf.of_le (by norm_num)
    have h_prod : ContDiff ℝ 1 (fun x : ℝ => x * deriv f x) := h_id.mul hf1
    have h_sum : ContDiff ℝ 1 (fun x : ℝ => f x + x * deriv f x) := h_f.add h_prod
    have h_b : ContDiff ℝ 1 (fun x : ℝ => b * deriv f x) := contDiff_const.mul hf1
    have h_d : ContDiff ℝ 1 (fun x : ℝ => d * (f x + x * deriv f x)) := contDiff_const.mul h_sum
    have h_total : ContDiff ℝ 1 (fun x : ℝ => b * deriv f x + d * (f x + x * deriv f x)) :=
      h_b.add h_d
    have h_eq : (fun x : ℝ => b * deriv f x + d * (f x + x * deriv f x)) = h1 := by
      funext x; rfl
    rw [h_eq] at h_total
    exact h_total
  have h2_cd0 : ContDiff ℝ 0 h2 := by
    have hf : ContDiff ℝ 2 f := f.contDiff
    have hf1 : ContDiff ℝ 1 (deriv f) := hf.deriv'
    have hf2 : ContDiff ℝ 0 (deriv (deriv f)) := hf1.deriv'
    have h_id : ContDiff ℝ 0 (fun x : ℝ => x) := contDiff_id
    have h_f1 : ContDiff ℝ 0 (deriv f) := hf1.of_le (by norm_num)
    have h_prod : ContDiff ℝ 0 (fun x : ℝ => x * deriv (deriv f) x) := h_id.mul hf2
    have h_sum : ContDiff ℝ 0 (fun x : ℝ => 2 * deriv f x + x * deriv (deriv f) x) :=
      (contDiff_const.mul h_f1).add h_prod
    have h_b : ContDiff ℝ 0 (fun x : ℝ => b * deriv (deriv f) x) := contDiff_const.mul hf2
    have h_d : ContDiff ℝ 0 (fun x : ℝ => d * (2 * deriv f x + x * deriv (deriv f) x)) :=
      contDiff_const.mul h_sum
    have h_total : ContDiff ℝ 0 (fun x : ℝ => b * deriv (deriv f) x + d * (2 * deriv f x + x * deriv (deriv f) x)) :=
      h_b.add h_d
    have h_eq : (fun x : ℝ => b * deriv (deriv f) x + d * (2 * deriv f x + x * deriv (deriv f) x)) = h2 := by
      funext x; rfl
    rw [h_eq] at h_total
    exact h_total
  {
    value := ⟨fun x : UnitPoint => h x, h_cd2.continuous.comp continuous_subtype_val⟩
    firstDeriv := ⟨fun x : UnitPoint => h1 x, h1_cd1.continuous.comp continuous_subtype_val⟩
    secondDeriv := ⟨fun x : UnitPoint => h2 x, h2_cd0.continuous.comp continuous_subtype_val⟩
    hasExtension := by
      refine' ⟨h, h_cd2, _⟩
      constructor
      · intro x; rfl
      constructor
      · intro x
        exact deriv_slopeCurveFunction f a b d x
      · intro x
        exact deriv2_slopeCurveFunction f a b d x
  }

/-- `slopeCurve` satisfies `RepresentsSlopeCurve`. -/
theorem slopeCurve_represents (f : SlopeFunction) (a b d : ℝ) :
    RepresentsSlopeCurve (slopeCurve f a b d) f a b d := by
  intro x
  constructor
  · rfl
  constructor
  · exact (deriv_slopeCurveFunction f a b d x).symm
  · exact (deriv2_slopeCurveFunction f a b d x).symm

@[simp]
theorem slopeCurve_value (f : SlopeFunction) (a b d : ℝ) (x : UnitPoint) :
    (slopeCurve f a b d) x = a + b * f x + d * (x : ℝ) * f x := by
  simpa [slopeCurve, slopeCurveFunction] using rfl

@[simp]
theorem slopeCurve_firstDeriv (f : SlopeFunction) (a b d : ℝ) (x : UnitPoint) :
    (slopeCurve f a b d).firstDeriv x =
    b * deriv f x + d * (f x + (x : ℝ) * deriv f x) := by
  simpa [slopeCurve] using rfl

@[simp]
theorem slopeCurve_secondDeriv (f : SlopeFunction) (a b d : ℝ) (x : UnitPoint) :
    (slopeCurve f a b d).secondDeriv x =
    b * deriv (deriv f) x + d * (2 * deriv f x + (x : ℝ) * deriv (deriv f) x) := by
  simpa [slopeCurve] using rfl

end Kakeya.Assouad
