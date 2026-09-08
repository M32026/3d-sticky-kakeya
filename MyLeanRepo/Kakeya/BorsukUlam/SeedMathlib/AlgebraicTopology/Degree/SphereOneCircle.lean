/-
Copyright (c) 2026 SeedProver. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SeedProver
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import MyLeanRepo.Kakeya.BorsukUlam.SeedMathlib.AlgebraicTopology.Degree.Homology

@[expose] public section

/-!
# The One-Sphere and the Complex Unit Circle

This file gives the standard homeomorphism between the Euclidean `1`-sphere
used by the degree-theory development and `Circle`, the complex unit circle.
-/

open Metric Complex

noncomputable section

namespace SeedMathlib.AlgebraicTopology.Degree

/-- The standard real-linear isometry equivalence between `ℂ` and `ℝ²`. -/
def complexToEuclideanLinearIsometryEquiv : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) := by
  let b : OrthonormalBasis (Fin (Module.finrank ℝ ℂ)) ℝ ℂ := stdOrthonormalBasis ℝ ℂ
  let e : Fin (Module.finrank ℝ ℂ) ≃ Fin 2 := finCongr finrank_real_complex
  let b' : OrthonormalBasis (Fin 2) ℝ ℂ := b.reindex e
  exact b'.repr

/-- The Euclidean `1`-sphere is homeomorphic to the complex unit circle. -/
def sphereOneCircleHomeomorph : Sphere 1 ≃ₜ Circle := by
  let e : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] ℂ := complexToEuclideanLinearIsometryEquiv.symm
  have h_norm : ∀ x : EuclideanSpace ℝ (Fin 2), ‖e x‖ = ‖x‖ := by
    intro x
    exact e.norm_map x
  have h1 : ∀ x : EuclideanSpace ℝ (Fin 2), ‖x‖ = 1 → ‖e x‖ = 1 := by
    intro x hx
    rw [h_norm x, hx]
  have h2 : ∀ y : ℂ, ‖y‖ = 1 → ‖e.symm y‖ = 1 := by
    intro y hy
    have h : ‖e.symm y‖ = ‖y‖ := e.symm.norm_map y
    rw [h, hy]
  refine
    { toFun := fun x : Sphere 1 =>
        (⟨e x, by
          have hx : ‖(x : EuclideanSpace ℝ (Fin 2))‖ = 1 :=
            mem_sphere_zero_iff_norm.mp x.property
          exact mem_sphere_zero_iff_norm.mpr (h1 x.val hx)⟩ : Circle)
      invFun := fun y : Circle =>
        (⟨e.symm y, by
          have hy : ‖(y : ℂ)‖ = 1 := mem_sphere_zero_iff_norm.mp y.property
          exact mem_sphere_zero_iff_norm.mpr (h2 y.val hy)⟩ : Sphere 1)
      left_inv := by
        intro x
        apply Subtype.ext
        simp
      right_inv := by
        intro y
        apply Subtype.ext
        simp
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }

end SeedMathlib.AlgebraicTopology.Degree
