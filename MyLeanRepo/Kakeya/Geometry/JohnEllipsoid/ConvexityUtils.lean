/-
# Convexity utilities for the John ellipsoid theorem

This module provides basic convexity lemmas used in the proof of the
Löwner–John ellipsoid theorem.
-/

import MyLeanRepo.Kakeya.Geometry.JohnEllipsoid.Basic
import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.Separation

noncomputable section

open scoped Pointwise Real

namespace JohnEllipsoid

section General

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- Convexity is preserved under linear maps. -/
lemma convex_image_linearMap {s : Set E} (hs : Convex ℝ s) (f : E →ₗ[ℝ] F) :
    Convex ℝ (f '' s) := by
  intro y1 hy1 y2 hy2 a b ha hb hab
  rcases hy1 with ⟨x1, hx1, rfl⟩
  rcases hy2 with ⟨x2, hx2, rfl⟩
  have h : a • x1 + b • x2 ∈ s := hs hx1 hx2 ha hb hab
  refine' ⟨a • x1 + b • x2, h, _⟩
  simp [map_smul, map_add]
  <;> rfl

/-- Arbitrary intersection of convex sets is convex. -/
lemma convex_intersection {ι : Sort*} {s : ι → Set E}
    (h : ∀ i, Convex ℝ (s i)) : Convex ℝ (⋂ i, s i) :=
  convex_iInter h

/-- If `K` is convex and symmetric about `z` (`∀ x ∈ K, z + (z - x) ∈ K`),
and `K` is nonempty, then `z ∈ K`. -/
lemma symmetric_convex_contains_zero {K : Set E} {z : E}
    (hK : Convex ℝ K) (hsym : ∀ x ∈ K, z + (z - x) ∈ K) (hne : K.Nonempty) : z ∈ K := by
  rcases hne with ⟨x, hx⟩
  have h1 : z + (z - x) ∈ K := hsym x hx
  have h2 : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • (z + (z - x)) ∈ K :=
    hK hx h1 (by norm_num) (by norm_num) (by norm_num)
  have h3 : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • (z + (z - x)) = z := by
    calc
      (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • (z + (z - x))
        = (1 / 2 : ℝ) • x + ((1 / 2 : ℝ) • z + (1 / 2 : ℝ) • (z - x)) := by rw [smul_add]
      _ = (1 / 2 : ℝ) • x + ((1 / 2 : ℝ) • z + ((1 / 2 : ℝ) • z - (1 / 2 : ℝ) • x)) := by rw [smul_sub]
      _ = (1 / 2 : ℝ) • z + (1 / 2 : ℝ) • z := by abel
      _ = ((1 / 2 : ℝ) + (1 / 2 : ℝ)) • z := by rw [← add_smul]
      _ = (1 : ℝ) • z := by norm_num
      _ = z := by simp
  rw [h3] at h2
  exact h2

/-- If `K` is symmetric about `0` and convex, then for any `x ∈ K` and `t ∈ [-1, 1]`,
`t • x ∈ K`. -/
lemma symmetric_convex_abs {K : Set E}
    (hK : Convex ℝ K) (hsym : ∀ x ∈ K, -x ∈ K) {x : E} (hx : x ∈ K)
    {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) : t • x ∈ K := by
  have h0 : (0 : E) ∈ K :=
    symmetric_convex_contains_zero hK (fun x hx => by simpa using hsym x hx) ⟨x, hx⟩
  rcases ht with ⟨ht1, ht2⟩
  by_cases h : 0 ≤ t
  · exact hK.smul_mem_of_zero_mem h0 hx ⟨h, ht2⟩
  · have hneg : -x ∈ K := hsym x hx
    have hpos : 0 ≤ -t := by linarith
    have hle : -t ≤ 1 := by linarith
    have h3 : (-t) • (-x) ∈ K := hK.smul_mem_of_zero_mem h0 hneg ⟨hpos, hle⟩
    have h4 : (-t) • (-x) = t • x := by
      simp [smul_neg]
      <;> ring
    rw [h4] at h3
    exact h3

/-- Finite convex combination: if `K` is convex, `u_i ∈ K`, `a_i ≥ 0`, `Σ a_i = 1`,
then `Σ a_i • u_i ∈ K`. -/
lemma convex_combination {ι : Type*} {t : Finset ι} {w : ι → ℝ} {z : ι → E} {K : Set E}
    (hK : Convex ℝ K) (h₀ : ∀ i ∈ t, 0 ≤ w i) (h₁ : ∑ i ∈ t, w i = 1)
    (hz : ∀ i ∈ t, z i ∈ K) : ∑ i ∈ t, w i • z i ∈ K :=
  hK.sum_mem h₀ h₁ hz

end General

section Euclidean

variable {n : ℕ} {K : Set (E n)} {x : E n}

/-- If `K` is closed, convex, symmetric about `0`, and `x ∉ K`, then there exists `w`
such that `|inner w y| ≤ 1` for all `y ∈ K` and `inner w x > 1`. -/
lemma symmetric_separation
    (hK : Convex ℝ K) (hclosed : IsClosed K) (hsym : ∀ y ∈ K, -y ∈ K)
    (hne : K.Nonempty) (hx : x ∉ K) :
    ∃ (w : E n), (∀ y ∈ K, |inner ℝ w y| ≤ 1) ∧ inner ℝ w x > 1 := by
  have h_main : ∃ (f : StrongDual ℝ (E n)) (u : ℝ),
      (∀ a ∈ K, f a < u) ∧ u < f x :=
    geometric_hahn_banach_closed_point hK hclosed hx
  rcases h_main with ⟨f, u, h1, h2⟩
  have h3 : ∀ y ∈ K, |f y| < u := by
    intro y hy
    have h4 : f y < u := h1 y hy
    have h5 : -y ∈ K := hsym y hy
    have h6 : f (-y) < u := h1 (-y) h5
    have h7 : -f y < u := by simpa [map_neg] using h6
    exact abs_lt.mpr ⟨by linarith, h4⟩
  have h0 : (0 : E n) ∈ K :=
    symmetric_convex_contains_zero hK (fun x hx => by simpa using hsym x hx) hne
  have h_u_pos : 0 < u := by
    have h8 : |f 0| < u := h3 0 h0
    simpa using h8
  let g : StrongDual ℝ (E n) := (u⁻¹ : ℝ) • f
  have hg1 : ∀ y ∈ K, |g y| < 1 := by
    intro y hy
    have h9 : |f y| < u := h3 y hy
    have h10 : g y = u⁻¹ * f y := by
      simp [g, smul_eq_mul] <;> ring
    rw [h10]
    have h11 : |u⁻¹ * f y| = |u⁻¹| * |f y| := by rw [abs_mul]
    rw [h11]
    have h12 : |u⁻¹| = u⁻¹ := by
      rw [abs_inv, abs_of_pos h_u_pos]
    rw [h12]
    have h13 : u⁻¹ * |f y| < 1 := by
      have h14 : |f y| < u := h9
      have h15 : u⁻¹ * |f y| < u⁻¹ * u := mul_lt_mul_of_pos_left h14 (by positivity)
      have h16 : u⁻¹ * u = 1 := by
        field_simp [h_u_pos.ne'] <;> ring
      rw [h16] at h15
      exact h15
    exact h13
  have hg2 : g x > 1 := by
    have h10 : f x > u := h2
    have h11 : g x = u⁻¹ * f x := by
      simp [g, smul_eq_mul] <;> ring
    rw [h11]
    have h12 : u⁻¹ * f x > u⁻¹ * u := mul_lt_mul_of_pos_left h10 (by positivity)
    have h13 : u⁻¹ * u = 1 := by
      field_simp [h_u_pos.ne'] <;> ring
    rw [h13] at h12
    exact h12
  let w : E n := (InnerProductSpace.toDual ℝ (E n)).symm g
  have h_w_y : ∀ (y : E n), inner ℝ w y = g y := by
    intro y
    simpa [w, InnerProductSpace.toDual_apply_apply] using rfl
  refine' ⟨w, _ , _⟩
  · intro y hy
    have h11 : |inner ℝ w y| < 1 := by
      rw [h_w_y y]
      exact hg1 y hy
    exact le_of_lt h11
  · rw [h_w_y x]
    exact hg2

/-- At any boundary point `p` of a compact convex set `K` with nonempty interior,
there exists a supporting hyperplane: a nonzero `w` such that `inner w y ≤ inner w p`
for all `y ∈ K`. -/
lemma supporting_hyperplane_at_boundary {p : E n}
    (hK : Convex ℝ K) (hcompact : IsCompact K) (hinterior : (interior K).Nonempty)
    (hp : p ∈ frontier K) :
    ∃ (w : E n), w ≠ 0 ∧ ∀ y ∈ K, inner ℝ w y ≤ inner ℝ w p := by
  have hclosed : IsClosed K := hcompact.isClosed
  have hp' : p ∈ closure K ∧ p ∉ interior K := hp
  have hpK : p ∈ K := by
    have hcl : closure K = K := hclosed.closure_eq
    rw [hcl] at hp'
    exact hp'.1
  have hpi : p ∉ interior K := hp'.2
  have h_interior_convex : Convex ℝ (interior K) := hK.interior
  have h_interior_open : IsOpen (interior K) := isOpen_interior
  have h_main : ∃ (f : StrongDual ℝ (E n)), ∀ a ∈ interior K, f a < f p :=
    geometric_hahn_banach_open_point h_interior_convex h_interior_open hpi
  rcases h_main with ⟨f, hf⟩
  have h_closure : closure (interior K) = K := by
    have h1 : closure (interior K) = closure K :=
      hK.closure_interior_eq_closure_of_nonempty_interior hinterior
    have h2 : closure K = K := hclosed.closure_eq
    rw [h2] at h1
    exact h1
  let S : Set (E n) := {y | f y ≤ f p}
  have hS_eq : S = f ⁻¹' (Set.Iic (f p)) := by
    ext y
    simp [S]
    <;> rfl
  have hS_closed : IsClosed S := by
    rw [hS_eq]
    exact isClosed_Iic.preimage f.continuous
  have hS_contains : interior K ⊆ S := by
    intro a ha
    have h : f a < f p := hf a ha
    exact le_of_lt h
  have h_closure_subset : closure (interior K) ⊆ S := closure_minimal hS_contains hS_closed
  have h_support : ∀ y ∈ K, f y ≤ f p := by
    intro y hy
    have h_y_closure : y ∈ closure (interior K) := by
      rw [h_closure] <;> exact hy
    exact h_closure_subset h_y_closure
  let w : E n := (InnerProductSpace.toDual ℝ (E n)).symm f
  have h_w_y : ∀ (y : E n), inner ℝ w y = f y := by
    intro y
    simpa [w, InnerProductSpace.toDual_apply_apply] using rfl
  have hwnonzero : w ≠ 0 := by
    intro h
    have h1 : (InnerProductSpace.toDual ℝ (E n)) w = f := by
      simp [w]
    have h2 : (InnerProductSpace.toDual ℝ (E n)) w = 0 := by
      rw [h] <;> simp
    have h_f0 : f = 0 := by
      rw [← h1, h2]
    rw [h_f0] at hf
    rcases hinterior with ⟨a, ha⟩
    have h_contra : (0 : ℝ) < (0 : ℝ) := hf a ha
    linarith
  exact ⟨w, hwnonzero, fun y hy => by
    rw [h_w_y y, h_w_y p]
    exact h_support y hy⟩

/-- Given a point `x` in the scaled unit ball `‖x‖ ≤ 1/√n` that is outside a closed
convex symmetric set `K`, symmetric separation yields a vector `w` with `|inner w y| ≤ 1`
for all `y ∈ K` and `‖w‖² > n`. This is the key input to the deformation contradiction. -/
lemma symmetric_separation_norm_bound (hn : 0 < n)
    (hK : Convex ℝ K) (hclosed : IsClosed K) (hsym : ∀ y ∈ K, -y ∈ K)
    (hne : K.Nonempty) (hx : x ∉ K) (hx_norm : ‖x‖ ≤ (Real.sqrt (n : ℝ))⁻¹) :
    ∃ (w : E n), (∀ y ∈ K, |inner ℝ w y| ≤ 1) ∧ (n : ℝ) < ‖w‖^2 := by
  obtain ⟨w, h1, h2⟩ := symmetric_separation hK hclosed hsym hne hx
  have h_cs : inner ℝ w x ≤ ‖w‖ * ‖x‖ := real_inner_le_norm w x
  have h_pos : 0 < inner ℝ w x := by linarith
  have h3 : 1 < ‖w‖ * ‖x‖ := by linarith
  have h4 : 1 < ‖w‖ * (Real.sqrt (n : ℝ))⁻¹ := by
    calc 1 < ‖w‖ * ‖x‖ := h3
      _ ≤ ‖w‖ * (Real.sqrt (n : ℝ))⁻¹ := by gcongr
  have h5 : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by positivity)
  have h6 : (n : ℝ) < ‖w‖^2 := by
    have h7 : 1 < ‖w‖ * (Real.sqrt (n : ℝ))⁻¹ := h4
    have h8 : Real.sqrt (n : ℝ) < ‖w‖ := by
      field_simp [h5.ne'] at h7 <;> nlinarith
    nlinarith [Real.sq_sqrt (show 0 ≤ (n : ℝ) from by positivity)]
  exact ⟨w, h1, h6⟩

end Euclidean

end JohnEllipsoid
