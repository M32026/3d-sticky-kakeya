module

public import Mathlib.Topology.Homotopy.Affine
public import Mathlib.Topology.Homotopy.HomotopyGroup
public import MyLeanRepo.Kakeya.BorsukUlam.Vendored.Topology.Homotopy.HomotopyGroupSphereSubsingletonOfLt.SphereMinusPointContractible

@[expose] public section

universe u v w

noncomputable section

open Metric Topology.Homotopy

open scoped unitInterval Topology

namespace HomotopySphere

/--
Helper lemma: The sphere minus a point is homeomorphic to Euclidean space of one lower dimension.
-/

def sphere_minus_point_homeo {k : ℕ} (p : sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) :
    {y : sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1 // y ≠ p} ≃ₜ
    EuclideanSpace ℝ (Fin k) := by
  have h_finrank : Module.finrank ℝ (EuclideanSpace ℝ (Fin (k + 1))) = k + 1 := by simp
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (k + 1))) = k + 1) := ⟨h_finrank⟩
  let e1 : {x : sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1 // x ∈ (stereographic' k p).source} ≃ₜ
          {y : EuclideanSpace ℝ (Fin k) // y ∈ (stereographic' k p).target} :=
    (stereographic' k p).toHomeomorphSourceTarget
  have h_source : (stereographic' k p).source = {p}ᶜ := by simp
  have h_target : (stereographic' k p).target = Set.univ := by simp
  let e2 : {x : sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1 // x ≠ p} ≃ₜ
          {x : sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1 // x ∈ (stereographic' k p).source} := by
    refine' {
      toFun := fun x => ⟨x.val, by simp⟩,
      invFun := fun x => ⟨x.val, by simpa [h_source] using x.property⟩,
      left_inv := by intro x; simp,
      right_inv := by intro x; simp,
      continuous_toFun := by fun_prop,
      continuous_invFun := by fun_prop
    }
  let e3 : {y : EuclideanSpace ℝ (Fin k) // y ∈ (stereographic' k p).target} ≃ₜ
          EuclideanSpace ℝ (Fin k) := by
    refine' {
      toFun := fun y => y.val,
      invFun := fun y => ⟨y, by simp⟩,
      left_inv := by intro y; simp,
      right_inv := by intro y; simp,
      continuous_toFun := by fun_prop,
      continuous_invFun := by fun_prop
    }
  exact e2.trans (e1.trans e3)

/--
If a generalized loop `f : GenLoop N S^k x` misses some point `p : S^k` (i.e., `p` is not in
the range of `f`), and the basepoint `x` is also not equal to `p`, then `f` is homotopic
(relative to the boundary) to the constant loop at `x`.

Proof idea: The map `f` factors through the subspace `S^k \ {p}`, which is homeomorphic
to Euclidean space via stereographic projection. In Euclidean space, we can use the
straight-line (affine) homotopy to the constant map, which fixes points that are already
at the target value (such as the boundary points, which all map to `x`).
-/

theorem map_misses_point_nullHomotopic
    {N : Type*} [DecidableEq N] {k : ℕ}
    {x : sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1}
    (f : GenLoop N (sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1) x)
    (p : sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1)
    (h1 : p ∉ Set.range (f : C(I^N, sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1)))
    (h2 : x ≠ p) :
    GenLoop.Homotopic f (GenLoop.const) := by
  let S := sphere (0 : EuclideanSpace ℝ (Fin (k + 1))) 1
  let Y := {y : S // y ≠ p}
  let e : Y ≃ₜ EuclideanSpace ℝ (Fin k) := sphere_minus_point_homeo p
  -- Lift f to a map into Y
  let f' : C(I^N, Y) := ⟨
    fun z => ⟨f z, fun h => h1 ⟨z, h⟩⟩,
    by fun_prop
  ⟩
  let x' : Y := ⟨x, h2⟩
  -- Map into Euclidean space
  let e_cont : C(Y, EuclideanSpace ℝ (Fin k)) := ⟨e, e.continuous⟩
  let g : C(I^N, EuclideanSpace ℝ (Fin k)) := e_cont.comp f'
  let c : C(I^N, EuclideanSpace ℝ (Fin k)) := ContinuousMap.const _ (e x')
  -- g and c agree on the boundary
  have h_boundary : ∀ z ∈ Cube.boundary N, g z = c z := by
    intro z hz
    have h_fz : f z = x := f.2 z hz
    have h_f'z : f' z = x' := by
      apply Subtype.ext
      exact h_fz
    have h1 : g z = e_cont (f' z) := by rfl
    have h2 : e_cont (f' z) = e_cont x' := by rw [h_f'z]
    have h3 : e_cont x' = e x' := by rfl
    have h4 : c z = e x' := by rfl
    rw [h1, h2, h3, h4]
  -- Affine homotopy in Euclidean space
  let H : g.Homotopy c := ContinuousMap.Homotopy.affine g c
  -- This homotopy is constant on the boundary
  have H_rel : ∀ (t : I) z, z ∈ Cube.boundary N → H (t, z) = g z := by
    intro t z hz
    have h : g z = c z := h_boundary z hz
    simp [H, h]
  -- Now we have HomotopicRel in Euclidean space
  have h_euclid : g.HomotopicRel c (Cube.boundary N) :=
    ⟨⟨H, H_rel⟩⟩
  -- Push forward along e.symm
  let e_symm_cont : C(EuclideanSpace ℝ (Fin k), Y) := ⟨e.symm, e.symm.continuous⟩
  have h_Y : (e_symm_cont.comp g).HomotopicRel (e_symm_cont.comp c) (Cube.boundary N) :=
    h_euclid.comp_continuousMap e_symm_cont
  -- Push forward along the inclusion i : Y → S
  let i : C(Y, S) := ⟨Subtype.val, continuous_subtype_val⟩
  have h_S : (i.comp (e_symm_cont.comp g)).HomotopicRel
              (i.comp (e_symm_cont.comp c)) (Cube.boundary N) :=
    h_Y.comp_continuousMap i
  -- Simplify the maps
  have h1_eq : i.comp (e_symm_cont.comp g) = (f : C(I^N, S)) := by
    apply ContinuousMap.ext
    intro z
    have h1 : e_symm_cont (g z) = f' z := by
      simp [e_symm_cont, g, e_cont]
    have h2 : i (e_symm_cont (g z)) = f z := by
      rw [h1]
      rfl
    exact h2
  have h2_eq : i.comp (e_symm_cont.comp c) = ContinuousMap.const (I^N) x := by
    apply ContinuousMap.ext
    intro z
    have h1 : e_symm_cont (c z) = x' := by
      simp [e_symm_cont, c, x']
    have h2 : i (e_symm_cont (c z)) = x := by
      rw [h1]
      rfl
    simpa using h2
  rw [h1_eq, h2_eq] at h_S
  exact h_S

end HomotopySphere
