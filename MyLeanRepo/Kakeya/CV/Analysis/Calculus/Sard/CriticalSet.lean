/-
Copyright (c) 2026 SeedProver. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SeedProver
-/
module

public import MyLeanRepo.Kakeya.CV.Analysis.Calculus.Sard.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Tactic

@[expose] public section

namespace ForMathlib.Analysis.Calculus.Sard

open MeasureTheory
open scoped ContDiff

/-- The set `C k` is the set of points where all iterated derivatives of `f`
of order from `1` to `k` vanish (we do NOT require `f x = 0`). -/
def C {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (k : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∀ j, 1 ≤ j → j ≤ k → iteratedFDeriv ℝ j f x = 0}

variable {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}

/-- Given `x ∈ C f k \ C f (k + 1)`, there exists a smooth function `h : E → ℝ` such that:
1. `h` is `ContDiff ℝ ∞`
2. `fderiv ℝ h x ≠ 0`
3. `∀ y ∈ C f k, h y = 0` -/
lemma exists_helper_function (k : ℕ) (hk_pos : 1 ≤ k) (x : EuclideanSpace ℝ (Fin n))
    (hx1 : x ∈ C f k) (hx2 : x ∉ C f (k + 1)) (hf : ContDiff ℝ ∞ f) :
    ∃ (h : EuclideanSpace ℝ (Fin n) → ℝ),
      ContDiff ℝ ∞ h ∧
      fderiv ℝ h x ≠ 0 ∧
      ∀ y ∈ C f k, h y = 0 := by
  have h1 : ∀ j, 1 ≤ j → j ≤ k → iteratedFDeriv ℝ j f x = 0 := hx1
  have h2 : ¬ (∀ j, 1 ≤ j → j ≤ k + 1 → iteratedFDeriv ℝ j f x = 0) := by simpa [C] using hx2
  have h3 : iteratedFDeriv ℝ (k + 1) f x ≠ 0 := by
    by_contra h4
    have h5 : ∀ j, 1 ≤ j → j ≤ k + 1 → iteratedFDeriv ℝ j f x = 0 := by
      intro j hj1 hj2
      by_cases h6 : j ≤ k
      · exact h1 j hj1 h6
      · have h7 : j = k + 1 := by omega
        rw [h7]
        exact h4
    exact h2 h5
  let E := EuclideanSpace ℝ (Fin n)
  let M : Fin (k + 1) → Type := fun _ => E
  let φ := continuousMultilinearCurryLeftEquiv ℝ M ℝ
  have h4 : φ (iteratedFDeriv ℝ (k + 1) f x) ≠ 0 := by
    intro h_cont
    have h5 : iteratedFDeriv ℝ (k + 1) f x = 0 := by
      exact φ.toLinearEquiv.map_eq_zero_iff.mp h_cont
    exact h3 h5
  have h5 : ∃ (m : E), (φ (iteratedFDeriv ℝ (k + 1) f x)) m ≠ 0 := by
    by_contra h5
    push Not at h5
    have h6 : φ (iteratedFDeriv ℝ (k + 1) f x) = 0 := by
      exact ContinuousLinearMap.ext h5
    exact h4 h6
  rcases h5 with ⟨m, hm⟩
  have h6 : ∃ (u : Fin k → E), ((φ (iteratedFDeriv ℝ (k + 1) f x)) m) u ≠ 0 := by
    by_contra h6
    push Not at h6
    have h7 : (φ (iteratedFDeriv ℝ (k + 1) f x)) m = 0 := by
      exact ContinuousMultilinearMap.ext h6
    exact hm h7
  rcases h6 with ⟨u, hu⟩
  let h : E → ℝ := fun y => (iteratedFDeriv ℝ k f y) u
  have h1_diff : ContDiff ℝ ∞ (iteratedFDeriv ℝ k f) := by
    rw [contDiff_infty]
    intro m
    have hle : (m + k : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by
      exact right_eq_inf.mp rfl

    have hfm : ContDiff ℝ (m + k) f := hf.of_le hle
    exact hfm.iteratedFDeriv_right (le_refl _)
  let F := ContinuousMultilinearMap ℝ (fun (_ : Fin k) => E) ℝ
  let eval_u : F →L[ℝ] ℝ :=
    { toFun := fun c => c u
      map_add' := by intro c1 c2; exact ContinuousMultilinearMap.add_apply c1 c2 u
      map_smul' := by
        intro r c
        have h : (r • c) u = r * (c u) := by
          rw [ContinuousMultilinearMap.smul_apply c r u]
          simp
        exact h }
  have h_h_diff : ContDiff ℝ ∞ h := eval_u.contDiff.comp h1_diff
  have h_diff_iterated : Differentiable ℝ (iteratedFDeriv ℝ k f) := by
    have h1 : ContDiff ℝ 1 (iteratedFDeriv ℝ k f) := h1_diff.of_le (by simp)
    exact h1.differentiable (by norm_num)
  have h_fderiv_h : ∀ (m' : E), (fderiv ℝ h x) m' = (fderiv ℝ (iteratedFDeriv ℝ k f) x) m' u := by
    intro m'
    exact fderiv_continuousMultilinear_apply_const_apply h_diff_iterated.differentiableAt u m'
  have h_eq_fderiv : fderiv ℝ (iteratedFDeriv ℝ k f) x = φ (iteratedFDeriv ℝ (k + 1) f x) := by
    have h_eq1 : fderiv ℝ (iteratedFDeriv ℝ k f) = φ ∘ iteratedFDeriv ℝ (k + 1) f := by
      exact fderiv_iteratedFDeriv
    rw [h_eq1]
    rfl
  have h_main : (fderiv ℝ h x) m ≠ 0 := by
    rw [h_fderiv_h m, h_eq_fderiv]
    exact hu
  have h_fderiv_ne_zero : fderiv ℝ h x ≠ 0 := by
    intro h_cont
    have h7 : (fderiv ℝ h x) m = 0 := by
      rw [h_cont]
      simp
    exact h_main h7
  have h_zero_on_C : ∀ y ∈ C f k, h y = 0 := by
    intro y hy
    have h5 : iteratedFDeriv ℝ k f y = 0 := by
      exact hy k hk_pos (by linarith)
    simp [h, h5]
  exact ⟨h, h_h_diff, h_fderiv_ne_zero, h_zero_on_C⟩


end ForMathlib.Analysis.Calculus.Sard
