/-
Copyright (c) 2026 SeedProver. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SeedProver
-/
module

public import MyLeanRepo.Kakeya.CV.Analysis.Calculus.Sard.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Tactic

@[expose] public section

namespace ForMathlib.Analysis.Calculus.Sard

open MeasureTheory
open scoped ContDiff

/-- Base case m = 0: the image of the critical set has measure zero. -/
lemma critical_image_null_m0 (f : EuclideanSpace ℝ (Fin 0) → ℝ)
    (_hf : ContDiff ℝ ∞ f) :
    (volume : Measure ℝ) (f '' {x | fderiv ℝ f x = 0}) = 0 := by
  have h_subsingleton : Subsingleton (EuclideanSpace ℝ (Fin 0)) := by infer_instance
  let x0 : EuclideanSpace ℝ (Fin 0) := 0
  have h_set : {x : EuclideanSpace ℝ (Fin 0) | fderiv ℝ f x = 0} = ∅ ∨ {x : EuclideanSpace ℝ (Fin 0) | fderiv ℝ f x = 0} = {x0} := by
    by_cases h2 : fderiv ℝ f x0 = 0
    · right
      ext x
      have hx : x = x0 := Subsingleton.elim x x0
      simp [hx, h2]
    · left
      ext x
      have hx : x = x0 := Subsingleton.elim x x0
      simp [hx, h2]
  rcases h_set with (h_set | h_set)
  · rw [h_set]
    simp
  · rw [h_set]
    simp

/-- Evaluation at 0 gives a linear equivalence between `Fin 1 → ℝ` and `ℝ`. -/
def fin1_equiv : (Fin 1 → ℝ) ≃L[ℝ] ℝ :=
  { toFun := fun f => f 0,
    invFun := fun x => fun (_ : Fin 1) => x,
    left_inv := by
      intro f
      ext i
      fin_cases i
      rfl,
    right_inv := by
      intro x
      simp,
    map_add' := by
      intro f g
      rfl,
    map_smul' := by
      intro c f
      rfl }

/-- Base case m = 1: the image of the critical set has measure zero. -/
lemma critical_image_null_m1 (f : EuclideanSpace ℝ (Fin 1) → ℝ)
    (hf : ContDiff ℝ ∞ f) :
    (volume : Measure ℝ) (f '' {x | fderiv ℝ f x = 0}) = 0 := by
  let e1 : EuclideanSpace ℝ (Fin 1) ≃L[ℝ] (Fin 1 → ℝ) := EuclideanSpace.equiv (Fin 1) ℝ
  let e2 : (Fin 1 → ℝ) ≃L[ℝ] ℝ := fin1_equiv
  let e : EuclideanSpace ℝ (Fin 1) ≃L[ℝ] ℝ := e1.trans e2
  let f' : ℝ → ℝ := f ∘ e.symm
  have hf'_diff : ContDiff ℝ ∞ f' := hf.comp e.symm.contDiff
  let C : Set (EuclideanSpace ℝ (Fin 1)) := {x | fderiv ℝ f x = 0}
  let C' : Set ℝ := {x | fderiv ℝ f' x = 0}
  have h_fderiv_compat : ∀ (x : EuclideanSpace ℝ (Fin 1)),
      fderiv ℝ f x = 0 ↔ fderiv ℝ f' (e x) = 0 := by
    intro x
    have h_e_symm_diff : DifferentiableAt ℝ e.symm (e x) := e.symm.differentiableAt
    have h_f_diff : DifferentiableAt ℝ f x := (hf.differentiable (by simp)) x
    have h1 : fderiv ℝ f' (e x) = (fderiv ℝ f x).comp (e.symm : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1)) := by
      have h_fderiv_esymm : fderiv ℝ e.symm (e x) = (e.symm : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1)) := by
        exact e.symm.fderiv
      have h_esymm_apply : e.symm (e x) = x := e.symm_apply_apply x
      have h_f_diff' : DifferentiableAt ℝ f (e.symm (e x)) := by
        rw [h_esymm_apply]
        exact h_f_diff
      have h_comp : fderiv ℝ (f ∘ e.symm) (e x) = (fderiv ℝ f (e.symm (e x))).comp (fderiv ℝ e.symm (e x)) := by
        exact fderiv_comp (e x) h_f_diff' h_e_symm_diff
      rw [h_comp, h_esymm_apply, h_fderiv_esymm]
    rw [h1]
    constructor
    · intro h
      rw [h]
      simp
    · intro h
      have h2 : (fderiv ℝ f x).comp (e.symm : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1)) = 0 := h
      have h_surj : Function.Surjective (e.symm : ℝ → EuclideanSpace ℝ (Fin 1)) := e.symm.surjective
      have h3 : fderiv ℝ f x = 0 := by
        ext v
        rcases h_surj v with ⟨w, rfl⟩
        have h4 : ((fderiv ℝ f x).comp (e.symm : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1))) w = 0 := by
          rw [h2]
          simp
        simpa using h4
      exact h3
  have h1 : e '' C = C' := by
    ext z
    simp only [Set.mem_image, C, C', Set.mem_setOf_eq]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (h_fderiv_compat x).mp hx
    · intro hz
      refine ⟨e.symm z, ?_, by simp⟩
      have h4 : fderiv ℝ f' z = 0 := hz
      have h5 : fderiv ℝ f (e.symm z) = 0 := by
        have h6 := (h_fderiv_compat (e.symm z)).mpr
        simpa using h6 h4
      exact h5
  have h_main : volume (f' '' C') = 0 := by
    have h2 : ∀ x ∈ C', (fderiv ℝ f' x).det = 0 := by
      intro x hx
      simp only [C', Set.mem_setOf_eq] at hx
      have h3 : fderiv ℝ f' x = 0 := hx
      have h4 : (fderiv ℝ f' x).det = 0 := by
        rw [h3]
        simp
      exact h4
    have h_diff : ∀ (x : ℝ), x ∈ C' → HasFDerivWithinAt f' (fderiv ℝ f' x) C' x := by
      intro x _
      exact ((hf'_diff.differentiable (by simp)) x).hasFDerivAt.hasFDerivWithinAt
    exact MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume h_diff h2
  have h3 : f '' C = f' '' C' := by
    ext y
    simp only [Set.mem_image, f']
    constructor
    · rintro ⟨x, hx, rfl⟩
      have h4 : e x ∈ C' := (h_fderiv_compat x).mp hx
      have h5 : (f ∘ e.symm) (e x) = f x := by
        simp
      exact ⟨e x, h4, h5⟩
    · rintro ⟨z, hz, rfl⟩
      have h4 : z ∈ e '' C := by
        rw [h1]
        exact hz
      rcases h4 with ⟨x, hx, h_eq⟩
      have h5 : f x = f' z := by
        have h6 : f' z = f (e.symm z) := by rfl
        have h7 : e.symm z = x := by
          exact e.symm_apply_apply x ▸ congr_arg e.symm (Eq.symm h_eq)
        rw [h6, h7]
      exact ⟨x, hx, h5⟩
  rw [h3]
  exact h_main


end ForMathlib.Analysis.Calculus.Sard
