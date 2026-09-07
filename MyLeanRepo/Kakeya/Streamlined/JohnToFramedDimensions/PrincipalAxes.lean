import MyLeanRepo.Kakeya.Geometry.OuterJohnEllipsoid
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Principal axes (SVD) for a 3D linear equivalence
-/

noncomputable section

open JohnEllipsoid

namespace Kakeya.Streamlined

/--
Given a linear equivalence `A` on `E 3`, there exist positive singular values
`σ` (antitone) and orthonormal bases `v`, `u` such that `A (v i) = σ i • u i`.
-/
lemma principalAxesSvd (A : E 3 ≃ₗ[ℝ] E 3) :
    ∃ (σ : Fin 3 → ℝ) (v u : OrthonormalBasis (Fin 3) ℝ (E 3)),
      (∀ i, 0 < σ i) ∧
      Antitone σ ∧
      (∀ i, A (v i) = σ i • u i) := by
  set T : E 3 →ₗ[ℝ] E 3 := A.toLinearMap with hT
  set B : E 3 →ₗ[ℝ] E 3 := T.adjoint.comp T with hB_def
  have hB : B.IsSymmetric := T.isSymmetric_adjoint_comp_self
  have hn : Module.finrank ℝ (E 3) = 3 := by simp
  set v : OrthonormalBasis (Fin 3) ℝ (E 3) := hB.eigenvectorBasis hn with hv_def
  set lam : Fin 3 → ℝ := hB.eigenvalues hn with hlam_def
  have hlam_anti : Antitone lam := hB.eigenvalues_antitone hn
  have h_eigen : ∀ i, B (v i) = lam i • v i :=
    fun i => hB.apply_eigenvectorBasis hn i
  have hadj : ∀ (x y : E 3), inner ℝ x (T.adjoint y) = inner ℝ (T x) y :=
    fun x y => LinearMap.adjoint_inner_right T x y
  have hv_orth : Pairwise (fun (i j : Fin 3) => inner ℝ (v i) (v j) = 0) :=
    v.orthonormal.2
  have hv_norm : ∀ i, ‖v i‖ = 1 := v.orthonormal.1
  have hlam_pos : ∀ i, 0 < lam i := by
    intro i
    have hvi_ne_zero : v i ≠ 0 := by
      have h : ‖v i‖ = 1 := hv_norm i
      intro h2
      rw [h2] at h
      simp at h <;> linarith
    have hAvi_ne_zero : A (v i) ≠ 0 := by
      intro h
      exact hvi_ne_zero (A.injective (by simpa using h))
    have h_pos : 0 < ‖A (v i)‖ ^ 2 := by positivity
    have hB1 : B (v i) = T.adjoint (T (v i)) := by
      simp [hB_def]
      <;> rfl
    have h1 : inner ℝ (v i) (B (v i)) = ‖A (v i)‖ ^ 2 := by
      rw [hB1]
      have h2 : inner ℝ (v i) (T.adjoint (T (v i))) = inner ℝ (T (v i)) (T (v i)) := hadj (v i) (T (v i))
      rw [h2]
      have h3 : inner ℝ (T (v i)) (T (v i)) = ‖T (v i)‖ ^ 2 := by
        simp [real_inner_self_eq_norm_sq]
      rw [h3] <;> rfl
    have h4 : inner ℝ (v i) (B (v i)) = lam i * ‖v i‖ ^ 2 := by
      rw [h_eigen i, inner_smul_right]
      have h5 : inner ℝ (v i) (v i) = ‖v i‖ ^ 2 := by simp [real_inner_self_eq_norm_sq]
      rw [h5] <;> ring
    rw [h4] at h1
    have h7 : ‖v i‖ ^ 2 > 0 := by
      rw [hv_norm i] <;> norm_num
    nlinarith
  set σ : Fin 3 → ℝ := fun i => Real.sqrt (lam i) with hσ_def
  have hσ_pos : ∀ i, 0 < σ i := by
    intro i
    exact Real.sqrt_pos.mpr (hlam_pos i)
  have hσ_sq : ∀ i, σ i ^ 2 = lam i := by
    intro i
    rw [hσ_def, Real.sq_sqrt (le_of_lt (hlam_pos i))]
  have hσ_anti : Antitone σ := by
    intro i j h
    have h1 : lam i ≥ lam j := hlam_anti h
    exact Real.sqrt_le_sqrt h1
  let u_vec : Fin 3 → E 3 := fun i => (σ i)⁻¹ • A (v i)
  have hAu : ∀ i, A (v i) = σ i • u_vec i := by
    intro i
    dsimp only [u_vec]
    have h9 : σ i * (σ i)⁻¹ = 1 := by
      have h10 : σ i ≠ 0 := (hσ_pos i).ne'
      field_simp [h10]
    calc
      A (v i) = (σ i * (σ i)⁻¹) • A (v i) := by rw [h9] <;> simp
      _ = σ i • ((σ i)⁻¹ • A (v i)) := by rw [smul_smul] <;> ring
  have h_orth : ∀ (i j : Fin 3), i ≠ j → inner ℝ (u_vec i) (u_vec j) = 0 := by
    intro i j hne
    dsimp only [u_vec]
    have hB1 : B (v j) = T.adjoint (T (v j)) := by simp [hB_def] <;> rfl
    have h1 : inner ℝ (A (v i)) (A (v j)) = inner ℝ (v i) (B (v j)) := by
      rw [hB1]
      exact (hadj (v i) (T (v j))).symm
    have hvi_vj : inner ℝ (v i) (v j) = 0 := hv_orth hne
    have h2 : inner ℝ (v i) (B (v j)) = 0 := by
      rw [h_eigen j, inner_smul_right, hvi_vj] <;> ring
    have h4 : inner ℝ (A (v i)) (A (v j)) = 0 := by
      rw [h1, h2]
    have h5 : inner ℝ ((σ i)⁻¹ • A (v i)) ((σ j)⁻¹ • A (v j)) = 0 := by
      rw [inner_smul_left, inner_smul_right, h4] <;> ring
    exact h5
  have h_norm : ∀ i, ‖u_vec i‖ = 1 := by
    intro i
    dsimp only [u_vec]
    have hB1 : B (v i) = T.adjoint (T (v i)) := by simp [hB_def] <;> rfl
    have h2 : inner ℝ (A (v i)) (A (v i)) = lam i := by
      have h3 : inner ℝ (A (v i)) (A (v i)) = inner ℝ (v i) (B (v i)) := by
        rw [hB1]
        exact (hadj (v i) (T (v i))).symm
      rw [h3, h_eigen i, inner_smul_right]
      have h4 : inner ℝ (v i) (v i) = 1 := by
        have h5 : inner ℝ (v i) (v i) = ‖v i‖ ^ 2 := by simp [real_inner_self_eq_norm_sq]
        rw [h5, hv_norm i] <;> norm_num
      rw [h4] <;> ring
    have h6 : ‖A (v i)‖ ^ 2 = lam i := by
      have h7 : inner ℝ (A (v i)) (A (v i)) = ‖A (v i)‖ ^ 2 := by
        simp [real_inner_self_eq_norm_sq]
      linarith
    have h7 : ‖(σ i)⁻¹ • A (v i)‖ = |(σ i)⁻¹| * ‖A (v i)‖ := norm_smul _ _
    rw [h7]
    have h8 : 0 < (σ i)⁻¹ := inv_pos.mpr (hσ_pos i)
    have h9 : |(σ i)⁻¹| = (σ i)⁻¹ := abs_of_pos h8
    rw [h9]
    have h10 : ‖A (v i)‖ = σ i := by
      have h11 : ‖A (v i)‖ ^ 2 = σ i ^ 2 := by rw [h6, hσ_sq i]
      have h12 : Real.sqrt (‖A (v i)‖ ^ 2) = Real.sqrt (σ i ^ 2) := by rw [h11]
      have h13 : Real.sqrt (‖A (v i)‖ ^ 2) = ‖A (v i)‖ := by
        rw [Real.sqrt_sq] <;> positivity
      have h14 : Real.sqrt (σ i ^ 2) = σ i := by
        rw [Real.sqrt_sq] <;> positivity
      linarith
    rw [h10]
    have h13 : (σ i)⁻¹ * σ i = 1 := by
      have h14 : σ i ≠ 0 := (hσ_pos i).ne'
      field_simp [h14]
    rw [h13]
  have h_u_orth : Orthonormal ℝ u_vec := ⟨h_norm, h_orth⟩
  let u_basis : Module.Basis (Fin 3) ℝ (E 3) :=
    basisOfOrthonormalOfCardEqFinrank h_u_orth (by simp)
  have h_coe : ⇑u_basis = u_vec := coe_basisOfOrthonormalOfCardEqFinrank h_u_orth (by simp)
  have hsp : (⊤ : Submodule ℝ (E 3)) ≤ Submodule.span ℝ (Set.range u_vec) := by
    have h : Submodule.span ℝ (Set.range u_vec) = ⊤ := by
      rw [← h_coe]
      exact u_basis.span_eq
    rw [h]
  let u : OrthonormalBasis (Fin 3) ℝ (E 3) :=
    OrthonormalBasis.mk h_u_orth hsp
  have h_u_coe : ⇑u = u_vec := by
    exact OrthonormalBasis.coe_mk h_u_orth hsp
  have hAu' : ∀ i, A (v i) = σ i • u i := by
    intro i
    have h15 : u i = u_vec i := by
      rw [← h_u_coe] <;> rfl
    rw [h15]
    exact hAu i
  exact ⟨σ, v, u, hσ_pos, hσ_anti, hAu'⟩

end Kakeya.Streamlined
