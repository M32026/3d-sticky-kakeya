/-
# Euclidean Space Utilities

Utility lemmas for Euclidean space used in the John ellipsoid proof:
- Linear equiv ↔ invertible matrix equivalence
- Riesz representation theorem
- Outer product matrix and trace
- Hahn-Banach separation theorems
-/

import MyLeanRepo.Kakeya.Geometry.JohnEllipsoid.Basic
import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.LocallyConvex.Separation

noncomputable section

open scoped InnerProductSpace

namespace JohnEllipsoid

variable {n : ℕ}

/-- Equivalence between linear equivs on `E n` and invertible matrices. -/
def linearEquiv_toMatrix :
    (E n ≃ₗ[ℝ] E n) ≃* Matrix.GeneralLinearGroup (Fin n) ℝ :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (R := ℝ) (M := E n)).symm.trans
    (Matrix.GeneralLinearGroup.toLin' (EuclideanSpace.basisFun (Fin n) ℝ).toBasis).symm

/-- Riesz representation: every continuous linear functional on `E n` is
given by inner product with a unique vector, and the norms agree. -/
theorem inner_product_dual (f : E n →L[ℝ] ℝ) :
    ∃! (w : E n), (∀ (x : E n), f x = inner ℝ w x) ∧ ‖w‖ = ‖f‖ := by
  let w : E n := (InnerProductSpace.toDual ℝ (E n)).symm f
  have hfw : (InnerProductSpace.toDual ℝ (E n)) w = f :=
    (InnerProductSpace.toDual ℝ (E n)).apply_symm_apply f
  have h1 : ∀ (x : E n), f x = inner ℝ w x := by
    intro x
    exact (InnerProductSpace.toDual_symm_apply (x := x) (y := f)).symm
  have h2 : ‖w‖ = ‖f‖ := by
    have h : ‖(InnerProductSpace.toDual ℝ (E n)) w‖ = ‖w‖ :=
      (InnerProductSpace.toDual ℝ (E n)).norm_map w
    rw [hfw] at h
    exact h.symm
  refine' ⟨w, ⟨h1, h2⟩, _⟩
  intro w' hw'
  have h3 : ∀ x, inner ℝ w x = inner ℝ w' x := by
    intro x
    rw [← h1 x, hw'.1 x]
  have h4 : w = w' := by
    exact innerSL_inj.mp (ContinuousLinearMap.ext h3)
  exact h4.symm

/-- The matrix of the rank-one map `x ↦ (inner w x) • w` with respect to the
standard basis is the outer product matrix `w ⊗ w`. -/
theorem outer_product_matrix (w : E n) :
    LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
      (InnerProductSpace.rankOne ℝ w w : E n →ₗ[ℝ] E n)
    = Matrix.vecMulVec w w := by
  rw [InnerProductSpace.toMatrix_rankOne w w
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin n) ℝ)]
  simp [Matrix.vecMulVec_apply]
  <;> rfl

/-- The trace of the rank-one map `x ↦ (inner w x) • w` equals `‖w‖²`. -/
theorem norm_sq_eq_trace_outer (w : E n) :
    (InnerProductSpace.rankOne ℝ w w : E n →ₗ[ℝ] E n).trace ℝ (E n) = ‖w‖ ^ 2 := by
  rw [InnerProductSpace.trace_rankOne w w]
  simp [real_inner_self_eq_norm_sq]

/-- Strict separation of a point from a closed convex set:
there exists a nonzero `w` and a real `c` such that `inner w x > c` and
`inner w y < c` for all `y ∈ K`. -/
theorem separation_point_from_closed_convex'
    {K : Set (E n)} (hK_nonempty : K.Nonempty)
    (hK_conv : Convex ℝ K) (hK_closed : IsClosed K)
    {x : E n} (hx : x ∉ K) :
    ∃ (w : E n) (c : ℝ), w ≠ 0 ∧
      inner ℝ w x > c ∧ ∀ y ∈ K, inner ℝ w y < c := by
  have hhb : ∃ (f : StrongDual ℝ (E n)) (u : ℝ),
      (∀ a ∈ K, f a < u) ∧ u < f x :=
    geometric_hahn_banach_closed_point hK_conv hK_closed hx
  rcases hhb with ⟨f, c, h1, h2⟩
  let w : E n := (InnerProductSpace.toDual ℝ (E n)).symm f
  have hfw : ∀ (z : E n), f z = inner ℝ w z := by
    intro z
    exact (InnerProductSpace.toDual_symm_apply (x := z) (y := f)).symm
  have h3 : inner ℝ w x > c := by
    rw [← hfw x]
    exact h2
  have h4 : ∀ y ∈ K, inner ℝ w y < c := by
    intro y hy
    rw [← hfw y]
    exact h1 y hy
  rcases hK_nonempty with ⟨y0, hy0⟩
  have hw_ne_zero : w ≠ 0 := by
    by_contra h
    have h5 : inner ℝ w y0 < c := h4 y0 hy0
    rw [h] at h3 h5
    simp at h3 h5 <;> linarith
  exact ⟨w, c, hw_ne_zero, h3, h4⟩

/-- Separation of a point from a closed convex set containing the origin:
there exists `w ≠ 0` such that `inner w x > 1` and `inner w y ≤ 1` for all `y ∈ K`. -/
theorem separation_point_from_closed_convex
    {K : Set (E n)} (hK_nonempty : K.Nonempty)
    (hK_conv : Convex ℝ K) (hK_closed : IsClosed K)
    (h0 : (0 : E n) ∈ K) {x : E n} (hx : x ∉ K) :
    ∃ (w : E n), w ≠ 0 ∧
      inner ℝ w x > 1 ∧ ∀ y ∈ K, inner ℝ w y ≤ 1 := by
  have hsep := separation_point_from_closed_convex' hK_nonempty hK_conv hK_closed hx
  rcases hsep with ⟨w, c, hw_ne_zero, hx_gt, hK_lt⟩
  have hc_pos : 0 < c := by
    have h0' : inner ℝ w (0 : E n) < c := hK_lt 0 h0
    simpa using h0'
  have hc_ne_zero : c ≠ 0 := hc_pos.ne'
  let w' := c⁻¹ • w
  have h5 : inner ℝ w' x > 1 := by
    have h_eq : inner ℝ w' x = (inner ℝ w x) / c := by
      simp [w', inner_smul_left] <;> ring
    rw [h_eq]
    have h' : (inner ℝ w x) / c > 1 := by
      have h_pos : 0 < c := hc_pos
      have h : (inner ℝ w x) > c := hx_gt
      calc
        (inner ℝ w x) / c > c / c := by gcongr
        _ = 1 := by
          field_simp [h_pos.ne'] <;> ring
    exact h'
  have h6 : ∀ y ∈ K, inner ℝ w' y ≤ 1 := by
    intro y hy
    have h7 : inner ℝ w y < c := hK_lt y hy
    have h_eq : inner ℝ w' y = (inner ℝ w y) / c := by
      simp [w', inner_smul_left] <;> ring
    rw [h_eq]
    have h' : (inner ℝ w y) / c < 1 := by
      have h_pos : 0 < c := hc_pos
      have h : (inner ℝ w y) < c := h7
      calc
        (inner ℝ w y) / c < c / c := by gcongr
        _ = 1 := by
          field_simp [h_pos.ne'] <;> ring
    exact h'.le
  have hw'_ne_zero : w' ≠ 0 := by
    intro h
    have h9 : c⁻¹ • w = 0 := h
    have h10 : w = 0 := by
      simpa [smul_eq_zero, hc_ne_zero] using h9
    exact hw_ne_zero h10
  exact ⟨w', hw'_ne_zero, h5, h6⟩

/-- Strict separation of a point from a compact convex set:
there exists `w ≠ 0`, `c : ℝ`, and `ε > 0` such that
`inner w x > c + ε` and `inner w y < c` for all `y ∈ C`. -/
theorem strict_separation_compact_convex
    {C : Set (E n)} (hC_nonempty : C.Nonempty)
    (hC_conv : Convex ℝ C) (hC_compact : IsCompact C)
    {x : E n} (hx : x ∉ C) :
    ∃ (w : E n) (c ε : ℝ), w ≠ 0 ∧ ε > 0 ∧
      inner ℝ w x > c + ε ∧ ∀ y ∈ C, inner ℝ w y < c := by
  have hC_closed : IsClosed C := hC_compact.isClosed
  have hhb : ∃ (f : StrongDual ℝ (E n)) (u : ℝ),
      (∀ a ∈ C, f a < u) ∧ u < f x :=
    geometric_hahn_banach_closed_point hC_conv hC_closed hx
  rcases hhb with ⟨f, u, h1, h2⟩
  let w : E n := (InnerProductSpace.toDual ℝ (E n)).symm f
  have hfw : ∀ (z : E n), f z = inner ℝ w z := by
    intro z
    exact (InnerProductSpace.toDual_symm_apply (x := z) (y := f)).symm
  have h3 : inner ℝ w x > u := by
    rw [← hfw x]; exact h2
  have h4 : ∀ y ∈ C, inner ℝ w y < u := by
    intro y hy
    rw [← hfw y]; exact h1 y hy
  rcases hC_nonempty with ⟨y0, hy0⟩
  have hw_ne_zero : w ≠ 0 := by
    by_contra h
    have h5 : inner ℝ w y0 < u := h4 y0 hy0
    rw [h] at h3 h5
    simp at h3 h5 <;> linarith
  let ε : ℝ := (inner ℝ w x - u) / 2
  have hε_pos : 0 < ε := by
    dsimp only [ε]
    linarith
  have h5 : inner ℝ w x > u + ε := by
    dsimp only [ε]
    linarith
  exact ⟨w, u, ε, hw_ne_zero, hε_pos, h5, h4⟩

end JohnEllipsoid
