/-
Copyright (c) 2026 SeedProver. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SeedProver
-/
module

public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Tactic

@[expose] public section

universe u v w

noncomputable section

open Metric

namespace HomotopySphere

/--
The k-sphere minus any point is homeomorphic to Euclidean space of dimension k,
and hence is a contractible space.

Given a point `v` on the sphere `S^k`, the subtype `{x : S^k // x ≠ v}`
(i.e., the sphere with point `v` removed) is a `ContractibleSpace`.
-/

theorem sphere_minus_point_contractible {k : ℕ} (v : sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) :
    ContractibleSpace {x : sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1 // x ≠ v} := by
  have h_finrank : Module.finrank ℝ (EuclideanSpace ℝ (Fin (k + 1))) = k + 1 := by
    simp
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (k + 1))) = k + 1) :=
    ⟨h_finrank⟩
  let e1 : {x : sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1 // x ∈ (stereographic' k v).source} ≃ₜ
          {y : EuclideanSpace ℝ (Fin k) // y ∈ (stereographic' k v).target} :=
    (stereographic' k v).toHomeomorphSourceTarget
  have h_source : (stereographic' k v).source = {v}ᶜ := by simp
  have h_target : (stereographic' k v).target = Set.univ := by simp
  let e2 : {x : sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1 // x ≠ v} ≃ₜ
          {x : sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1 // x ∈ (stereographic' k v).source} := by
    refine' {
      toFun := fun x => ⟨x.val, by simp⟩,
      invFun := fun x => ⟨x.val, by simpa [h_source] using x.property⟩,
      left_inv := by intro x; simp,
      right_inv := by intro x; simp,
      continuous_toFun := by fun_prop,
      continuous_invFun := by fun_prop
    }
  let e3 : {y : EuclideanSpace ℝ (Fin k) // y ∈ (stereographic' k v).target} ≃ₜ
          EuclideanSpace ℝ (Fin k) := by
    refine' {
      toFun := fun y => y.val,
      invFun := fun y => ⟨y, by simp⟩,
      left_inv := by intro y; simp,
      right_inv := by intro y; simp,
      continuous_toFun := by fun_prop,
      continuous_invFun := by fun_prop
    }
  let e : {x : sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1 // x ≠ v} ≃ₜ
          EuclideanSpace ℝ (Fin k) :=
    e2.trans (e1.trans e3)
  exact e.contractibleSpace

end HomotopySphere
