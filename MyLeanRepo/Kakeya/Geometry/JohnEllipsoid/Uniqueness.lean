/-
# Uniqueness of the outer John ellipsoid

Proof using general Fritz John contact conditions and AM-GM on singular values.
-/

import MyLeanRepo.Kakeya.Geometry.JohnEllipsoid.Basic
import MyLeanRepo.Kakeya.Geometry.JohnEllipsoid.EllipsoidProps
import MyLeanRepo.Kakeya.Geometry.JohnEllipsoid.VolumeUtils
import MyLeanRepo.Kakeya.Geometry.JohnEllipsoid.GeneralFritzJohn
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Tactic

noncomputable section

open MeasureTheory
open scoped Pointwise Real

namespace JohnEllipsoid

variable {n : ℕ}

section Helpers

lemma adjoint_comp_symmetric (T : E n →ₗ[ℝ] E n) :
    (T.adjoint.comp T).IsSymmetric := by
  intro x y
  dsimp only [LinearMap.comp_apply]
  have h1 : inner ℝ x (T.adjoint (T y)) = inner ℝ (T x) (T y) := by
    exact LinearMap.adjoint_inner_right T x (T y)
  have h2 : inner ℝ (T.adjoint (T x)) y = inner ℝ (T x) (T y) := by
    exact LinearMap.adjoint_inner_left T y (T x)
  rw [h1, h2]

lemma adjoint_comp_pos (T : E n →ₗ[ℝ] E n) :
    ∀ (x : E n), 0 ≤ inner ℝ x ((T.adjoint.comp T) x) := by
  intro x
  dsimp only [LinearMap.comp_apply]
  have h : inner ℝ x (T.adjoint (T x)) = inner ℝ (T x) (T x) := by
    exact LinearMap.adjoint_inner_right T x (T x)
  rw [h]
  exact real_inner_self_nonneg

lemma inner_S_self_eq_norm_sq (T : E n →ₗ[ℝ] E n) (u : E n) :
    inner ℝ ((T.adjoint.comp T) u) u = ‖T u‖ ^ 2 := by
  dsimp only [LinearMap.comp_apply]
  have h : inner ℝ (T.adjoint (T u)) u = inner ℝ (T u) (T u) := by
    exact LinearMap.adjoint_inner_left T u (T u)
  rw [h]
  have h2 : inner ℝ (T u) (T u) = ‖T u‖ ^ 2 := by
    exact real_inner_self_eq_norm_sq (T u)
  exact h2

lemma det_adjoint_eq_det (f : E n →ₗ[ℝ] E n) :
    LinearMap.det f.adjoint = LinearMap.det f := by
  let b : OrthonormalBasis (Fin n) ℝ (E n) := by
    exact EuclideanSpace.basisFun (Fin n) ℝ
  let b' := b.toBasis
  have h1 : (LinearMap.toMatrix b' b') f.adjoint =
      ((LinearMap.toMatrix b' b') f).transpose := by
    have h2 := LinearMap.toMatrix_adjoint b b f
    have h3 : ((LinearMap.toMatrix b' b') f).conjTranspose = ((LinearMap.toMatrix b' b') f).transpose := by
      ext i j; simp [Matrix.conjTranspose]
    rw [h2, h3]
  have h3 : LinearMap.det f.adjoint = ((LinearMap.toMatrix b' b') f.adjoint).det :=
    (LinearMap.det_toMatrix b' f.adjoint).symm
  have h4 : LinearMap.det f = ((LinearMap.toMatrix b' b') f).det :=
    (LinearMap.det_toMatrix b' f).symm
  rw [h3, h1, Matrix.det_transpose, ←h4]

lemma posSemidef_trace_nonneg {S : E n →ₗ[ℝ] E n}
    (hS_pos : ∀ (x : E n), 0 ≤ inner ℝ x (S x)) :
    0 ≤ S.trace ℝ (E n) := by
  let b : OrthonormalBasis (Fin n) ℝ (E n) := by
    exact EuclideanSpace.basisFun (Fin n) ℝ
  have h : S.trace ℝ (E n) = ∑ j : Fin n, inner ℝ (b j) (S (b j)) :=
    LinearMap.trace_eq_sum_inner S b
  rw [h]
  apply Finset.sum_nonneg
  intro j _
  exact hS_pos (b j)

end Helpers

section TraceIdentity

lemma fritz_john_trace_identity
    {m : ℕ} {u : Fin m → E n} {c : Fin m → ℝ}
    (h_outer : ∀ (x : E n), ∑ i : Fin m, (c i * inner ℝ (u i) x) • u i = x)
    (T : E n →ₗ[ℝ] E n) :
    LinearMap.trace ℝ (E n) (T.adjoint.comp T) =
      ∑ i : Fin m, c i * ‖T (u i)‖ ^ 2 := by
  let S : E n →ₗ[ℝ] E n := T.adjoint.comp T
  have hS_symm : S.IsSymmetric := adjoint_comp_symmetric T
  let b : OrthonormalBasis (Fin n) ℝ (E n) := by
    exact EuclideanSpace.basisFun (Fin n) ℝ
  have h_trace : S.trace ℝ (E n) = ∑ j : Fin n, inner ℝ (b j) (S (b j)) :=
    LinearMap.trace_eq_sum_inner S b
  have h_expand : ∀ (x : E n), x = ∑ i : Fin m, (c i * inner ℝ (u i) x) • u i := by
    intro x; exact (h_outer x).symm
  have h_basis_expand : ∀ (x : E n), x = ∑ j : Fin n, inner ℝ (b j) x • b j := by
    intro x
    have h : (∑ j : Fin n, b.repr x j • b j) = x := b.sum_repr x
    have h2 : ∀ j, b.repr x j = inner ℝ (b j) x := by
      intro j; exact OrthonormalBasis.repr_apply_apply b x j
    have h3 : (∑ j : Fin n, b.repr x j • b j) = ∑ j : Fin n, inner ℝ (b j) x • b j := by
      apply Finset.sum_congr rfl; intro j _; rw [h2 j]
    rw [h3] at h; exact h.symm
  have h_inner_expand : ∀ (x y : E n), inner ℝ y x =
      ∑ i : Fin m, c i * inner ℝ (u i) x * inner ℝ y (u i) := by
    intro x y
    have h_exp : x = ∑ i : Fin m, (c i * inner ℝ (u i) x) • u i := h_expand x
    have h_goal : inner ℝ y x = inner ℝ y (∑ i : Fin m, (c i * inner ℝ (u i) x) • u i) :=
      congr_arg (fun z => inner ℝ y z) h_exp
    rw [h_goal]
    have h_sum : inner ℝ y (∑ i : Fin m, (c i * inner ℝ (u i) x) • u i) =
        ∑ i : Fin m, inner ℝ y ((c i * inner ℝ (u i) x) • u i) := by
      rw [inner_sum]
    rw [h_sum]
    have h_smul : ∑ i : Fin m, inner ℝ y ((c i * inner ℝ (u i) x) • u i) =
        ∑ i : Fin m, (c i * inner ℝ (u i) x) * inner ℝ y (u i) := by
      apply Finset.sum_congr rfl; intro i _
      rw [inner_smul_right]
    rw [h_smul]
    <;> rfl
  have h_main : ∑ j : Fin n, inner ℝ (b j) (S (b j)) =
      ∑ i : Fin m, c i * inner ℝ (S (u i)) (u i) := by
    calc
      ∑ j : Fin n, inner ℝ (b j) (S (b j))
        = ∑ j : Fin n, ∑ i : Fin m, c i * inner ℝ (u i) (S (b j)) * inner ℝ (b j) (u i) := by
          apply Finset.sum_congr rfl; intro j _
          exact h_inner_expand (S (b j)) (b j)
      _ = ∑ i : Fin m, ∑ j : Fin n, c i * inner ℝ (u i) (S (b j)) * inner ℝ (b j) (u i) := by
          rw [Finset.sum_comm]
      _ = ∑ i : Fin m, c i * (∑ j : Fin n, inner ℝ (u i) (S (b j)) * inner ℝ (b j) (u i)) := by
          apply Finset.sum_congr rfl; intro i _
          have h_step : ∑ j : Fin n, c i * inner ℝ (u i) (S (b j)) * inner ℝ (b j) (u i) =
              c i * ∑ j : Fin n, inner ℝ (u i) (S (b j)) * inner ℝ (b j) (u i) := by
            have h4 : ∑ j : Fin n, c i * (inner ℝ (u i) (S (b j)) * inner ℝ (b j) (u i)) =
                c i * ∑ j : Fin n, inner ℝ (u i) (S (b j)) * inner ℝ (b j) (u i) := by
              rw [Finset.mul_sum]
            have h5 : ∑ j : Fin n, c i * inner ℝ (u i) (S (b j)) * inner ℝ (b j) (u i) =
                ∑ j : Fin n, c i * (inner ℝ (u i) (S (b j)) * inner ℝ (b j) (u i)) := by
              apply Finset.sum_congr rfl; intro j _; ring
            rw [h5, h4]
          exact h_step
      _ = ∑ i : Fin m, c i * (∑ j : Fin n, inner ℝ (S (u i)) (b j) * inner ℝ (b j) (u i)) := by
          apply Finset.sum_congr rfl; intro i _
          congr 1
          apply Finset.sum_congr rfl; intro j _
          have h_sym : inner ℝ (S (u i)) (b j) = inner ℝ (u i) (S (b j)) := hS_symm (u i) (b j)
          rw [←h_sym] <;> ring
      _ = ∑ i : Fin m, c i * inner ℝ (S (u i)) (u i) := by
          apply Finset.sum_congr rfl; intro i _
          have h_basis_sum : inner ℝ (S (u i)) (u i) =
              ∑ j : Fin n, inner ℝ (S (u i)) (b j) * inner ℝ (b j) (u i) := by
            have h_u_expand : u i = ∑ j : Fin n, inner ℝ (b j) (u i) • b j := h_basis_expand (u i)
            have h : inner ℝ (S (u i)) (u i) =
                inner ℝ (S (u i)) (∑ j : Fin n, inner ℝ (b j) (u i) • b j) :=
              congr_arg (fun z => inner ℝ (S (u i)) z) h_u_expand
            rw [h]
            have h2 : inner ℝ (S (u i)) (∑ j : Fin n, inner ℝ (b j) (u i) • b j) =
                ∑ j : Fin n, inner ℝ (S (u i)) (inner ℝ (b j) (u i) • b j) := by
              rw [inner_sum]
            rw [h2]
            apply Finset.sum_congr rfl; intro j _
            have h3 : inner ℝ (S (u i)) (inner ℝ (b j) (u i) • b j) =
                inner ℝ (b j) (u i) * inner ℝ (S (u i)) (b j) := by
              rw [inner_smul_right] <;> ring
            rw [h3] <;> ring
          rw [h_basis_sum]
  rw [h_trace, h_main]
  apply Finset.sum_congr rfl
  intro i _
  have h6 : inner ℝ (S (u i)) (u i) = ‖T (u i)‖ ^ 2 :=
    inner_S_self_eq_norm_sq T (u i)
  rw [h6] <;> ring

end TraceIdentity

section DetTraceAMGM

lemma posSemidef_det_le_trace_pow
    {S : E n →ₗ[ℝ] E n} (hS_symm : S.IsSymmetric)
    (hS_pos : ∀ (x : E n), 0 ≤ inner ℝ x (S x))
    (hn : 0 < n) :
    S.det ≤ (S.trace ℝ (E n) / (n : ℝ)) ^ n := by
  let hn' : Module.finrank ℝ (E n) = n := by simp
  let eigval : Fin n → ℝ := hS_symm.eigenvalues hn'
  let b := hS_symm.eigenvectorBasis hn'
  have h_eig_nonneg : ∀ (i : Fin n), 0 ≤ eigval i := by
    intro i
    have h_eig : S (b i) = eigval i • b i := hS_symm.apply_eigenvectorBasis hn' i
    have h5 : 0 ≤ inner ℝ (b i) (S (b i)) := hS_pos _
    rw [h_eig] at h5
    have h6 : inner ℝ (b i) (eigval i • b i) = eigval i * ‖b i‖ ^ 2 := by
      simp [inner_smul_right, inner_self_eq_norm_sq_to_K] <;> ring
    rw [h6] at h5
    have h7 : ‖b i‖ = 1 := by
      have h8 : ‖b i‖₊ = 1 := OrthonormalBasis.nnnorm_eq_one b i
      simpa using h8
    rw [h7] at h5 <;> norm_num at h5 ⊢ <;> linarith
  have hdet : S.det = ∏ i : Fin n, eigval i := by
    have h : S.det = ∏ i : Fin n, (hS_symm.eigenvalues hn' i : ℝ) :=
      hS_symm.det_eq_prod_eigenvalues hn'
    have h2 : (∏ i : Fin n, (hS_symm.eigenvalues hn' i : ℝ)) = ∏ i : Fin n, eigval i := by rfl
    rw [h, h2]
  have htrace : S.trace ℝ (E n) = ∑ i : Fin n, eigval i :=
    hS_symm.trace_eq_sum_eigenvalues hn'
  rw [hdet, htrace]
  let w : Fin n → ℝ := fun _ => (n : ℝ)⁻¹
  have hw_sum : ∑ i : Fin n, w i = 1 := by
    simp [w, Finset.sum_const, Finset.card_fin] <;> field_simp [hn.ne'] <;> ring
  have h_amgm : ∏ i : Fin n, (eigval i) ^ (w i) ≤ ∑ i : Fin n, w i * eigval i :=
    Real.geom_mean_le_arith_mean_weighted (s := Finset.univ) w eigval
      (fun i _ => by positivity) hw_sum (fun i _ => h_eig_nonneg i)
  have h_prod_rpow : ∏ i : Fin n, (eigval i) ^ (w i) = (∏ i : Fin n, eigval i) ^ ((n : ℝ)⁻¹) := by
    have h10 : ∀ (i : Fin n), (eigval i) ^ (w i) = (eigval i) ^ ((n : ℝ)⁻¹) := by
      intro i; rfl
    have h11 : ∏ i : Fin n, (eigval i) ^ (w i) = ∏ i : Fin n, (eigval i) ^ ((n : ℝ)⁻¹) := by
      apply Finset.prod_congr rfl; intro i _; exact h10 i
    rw [h11]
    have h12 : ∀ (s : Finset (Fin n)), ∏ i ∈ s, (eigval i) ^ ((n : ℝ)⁻¹) = (∏ i ∈ s, eigval i) ^ ((n : ℝ)⁻¹) := by
      intro s
      induction s using Finset.induction with
      | empty => simp
      | @insert a s ha ih =>
        rw [Finset.prod_insert ha, Finset.prod_insert ha]
        rw [ih]
        have h_nonneg_a : 0 ≤ eigval a := h_eig_nonneg a
        have h_nonneg_prod : 0 ≤ ∏ i ∈ s, eigval i := by
          apply Finset.prod_nonneg; intro i _; exact h_eig_nonneg i
        rw [← Real.mul_rpow h_nonneg_a h_nonneg_prod] <;> ring
    exact h12 Finset.univ
  have h_sum_nonneg : 0 ≤ ∑ i : Fin n, eigval i := by
    apply Finset.sum_nonneg; intro i _; exact h_eig_nonneg i
  have h11 : ∑ i : Fin n, w i * eigval i = (n : ℝ)⁻¹ * ∑ i : Fin n, eigval i := by
    rw [Finset.mul_sum] <;> rfl
  rw [h_prod_rpow, h11] at h_amgm
  have h13 : 0 ≤ ∏ i : Fin n, eigval i := by
    apply Finset.prod_nonneg; intro i _; exact h_eig_nonneg i
  have h15 : (((∏ i : Fin n, eigval i) ^ ((n : ℝ)⁻¹)) ^ n) = ∏ i : Fin n, eigval i := by
    have h16 : (((∏ i : Fin n, eigval i) ^ ((n : ℝ)⁻¹)) ^ n) =
        (((∏ i : Fin n, eigval i) ^ ((n : ℝ)⁻¹)) ^ (n : ℝ)) := by
      rw [← Real.rpow_natCast] <;> positivity
    rw [h16]
    have h17 : (((∏ i : Fin n, eigval i) ^ ((n : ℝ)⁻¹)) ^ (n : ℝ)) =
        (∏ i : Fin n, eigval i) ^ (((n : ℝ)⁻¹) * (n : ℝ)) := by
      rw [← Real.rpow_mul h13] <;> ring
    rw [h17]
    have h18 : (n : ℝ)⁻¹ * (n : ℝ) = 1 := by field_simp [hn.ne'] <;> ring
    rw [h18] <;> simp
  have h19 : 0 ≤ (n : ℝ)⁻¹ * ∑ i : Fin n, eigval i := by positivity
  have h20 : ((∏ i : Fin n, eigval i) ^ ((n : ℝ)⁻¹)) ^ n ≤ (((n : ℝ)⁻¹ * ∑ i : Fin n, eigval i) ^ n) := by
    gcongr
  rw [h15] at h20
  have h21 : ((n : ℝ)⁻¹ * ∑ i : Fin n, eigval i) = (∑ i : Fin n, eigval i) / (n : ℝ) := by ring
  rw [h21] at h20
  exact h20

lemma eq_am_gm_implies_id
    {S : E n →ₗ[ℝ] E n} (hS_symm : S.IsSymmetric)
    (hS_pos : ∀ (x : E n), 0 ≤ inner ℝ x (S x))
    (hn : 0 < n) (hdet : S.det = 1) (htrace : S.trace ℝ (E n) = (n : ℝ)) :
    S = (1 : E n →ₗ[ℝ] E n) := by
  let hn' : Module.finrank ℝ (E n) = n := by simp
  let eigval : Fin n → ℝ := hS_symm.eigenvalues hn'
  let b := hS_symm.eigenvectorBasis hn'
  have h_eig_nonneg : ∀ (i : Fin n), 0 ≤ eigval i := by
    intro i
    have h_eig : S (b i) = eigval i • b i := hS_symm.apply_eigenvectorBasis hn' i
    have h5 : 0 ≤ inner ℝ (b i) (S (b i)) := hS_pos _
    rw [h_eig] at h5
    have h6 : inner ℝ (b i) (eigval i • b i) = eigval i * ‖b i‖ ^ 2 := by
      simp [inner_smul_right, inner_self_eq_norm_sq_to_K] <;> ring
    rw [h6] at h5
    have h7 : ‖b i‖ = 1 := by
      have h8 : ‖b i‖₊ = 1 := OrthonormalBasis.nnnorm_eq_one b i
      simpa using h8
    rw [h7] at h5 <;> norm_num at h5 ⊢ <;> linarith
  have hdet' : ∏ i : Fin n, eigval i = 1 := by
    have h : S.det = ∏ i : Fin n, eigval i := by
      have h2 : S.det = ∏ i : Fin n, (hS_symm.eigenvalues hn' i : ℝ) :=
        hS_symm.det_eq_prod_eigenvalues hn'
      have h3 : (∏ i : Fin n, (hS_symm.eigenvalues hn' i : ℝ)) = ∏ i : Fin n, eigval i := by rfl
      rw [h2, h3]
    rw [h] at hdet; exact hdet
  have htrace' : ∑ i : Fin n, eigval i = (n : ℝ) := by
    have h : S.trace ℝ (E n) = ∑ i : Fin n, eigval i :=
      hS_symm.trace_eq_sum_eigenvalues hn'
    rw [h] at htrace; exact htrace
  have h_eig_pos : ∀ (i : Fin n), 0 < eigval i := by
    intro i
    by_contra h
    have h0 : eigval i = 0 := by linarith [h_eig_nonneg i]
    have h_prod_zero : ∏ j : Fin n, eigval j = 0 := by
      rw [Finset.prod_eq_zero (Finset.mem_univ i)]; exact h0
    rw [h_prod_zero] at hdet'; norm_num at hdet'
  have h_sum_log : ∑ i : Fin n, Real.log (eigval i) = 0 := by
    have h : ∑ i : Fin n, Real.log (eigval i) = Real.log (∏ i : Fin n, eigval i) := by
      rw [← Real.log_prod] <;> intro i _; exact (h_eig_pos i).ne'
    rw [h, hdet'] <;> norm_num
  have h_sum_sub : ∑ i : Fin n, (eigval i - 1) = 0 := by
    have h : ∑ i : Fin n, (eigval i - 1) = (∑ i : Fin n, eigval i) - ∑ i : Fin n, (1 : ℝ) := by
      rw [Finset.sum_sub_distrib] <;> rfl
    rw [h, htrace']
    simp [Finset.sum_const, Finset.card_fin] <;> ring
  have h_nonpos : ∀ (j : Fin n), Real.log (eigval j) - (eigval j - 1) ≤ 0 := by
    intro j
    have h9 : Real.log (eigval j) ≤ eigval j - 1 := Real.log_le_sub_one_of_pos (h_eig_pos j)
    linarith
  have h_sum_zero : ∑ i : Fin n, (Real.log (eigval i) - (eigval i - 1)) = 0 := by
    have h10 : ∑ i : Fin n, (Real.log (eigval i) - (eigval i - 1)) =
        (∑ i : Fin n, Real.log (eigval i)) - ∑ i : Fin n, (eigval i - 1) := by
      rw [Finset.sum_sub_distrib] <;> rfl
    rw [h10, h_sum_log, h_sum_sub] <;> ring
  have h_all_zero : ∀ (j : Fin n), Real.log (eigval j) - (eigval j - 1) = 0 := by
    intro j
    have h11 : ∀ i ∈ Finset.univ, Real.log (eigval i) - (eigval i - 1) ≤ 0 := by
      intro i _; exact h_nonpos i
    exact Finset.sum_eq_zero_iff_of_nonpos h11 |>.mp h_sum_zero j (Finset.mem_univ j)
  have h_all_one : ∀ (i : Fin n), eigval i = 1 := by
    intro i
    have h_eq2 : Real.log (eigval i) = eigval i - 1 := by linarith [h_all_zero i]
    have h_pos : 0 < eigval i := h_eig_pos i
    have h_exp : Real.exp (Real.log (eigval i)) = eigval i := Real.exp_log h_pos
    have h_eq4 : Real.exp (eigval i - 1) = eigval i := by
      calc
        Real.exp (eigval i - 1) = Real.exp (Real.log (eigval i)) := by rw [h_eq2]
        _ = eigval i := h_exp
    have h_strict : ∀ (y : ℝ), y ≠ 0 → 1 + y < Real.exp y := by
      intro y hy
      by_cases hpos : 0 < y
      · have h1 : 0 < y / 2 := by linarith
        have h2 : 1 + y / 2 ≤ Real.exp (y / 2) := by linarith [Real.add_one_le_exp (y / 2)]
        have h3 : Real.exp (y / 2) > 1 := by
          have h4 : Real.exp (y / 2) > Real.exp 0 := Real.exp_strictMono h1
          simpa using h4
        have h5 : Real.exp y = (Real.exp (y / 2)) ^ 2 := by
          have h6 : y = y / 2 + y / 2 := by ring
          rw [h6, Real.exp_add] <;> ring_nf
        rw [h5]; nlinarith
      · have hneg : y < 0 := by
          exact lt_of_le_of_ne (le_of_not_gt hpos) hy
        by_cases h2 : y ≤ -2
        · have h3 : 1 + y ≤ 0 := by linarith
          have h4 : 0 < Real.exp y := Real.exp_pos y
          linarith
        · have h3 : -2 < y := by linarith
          have h4 : 0 < 1 + y / 2 := by linarith
          have h5 : 1 + y / 2 ≤ Real.exp (y / 2) := by linarith [Real.add_one_le_exp (y / 2)]
          have h6 : Real.exp y = (Real.exp (y / 2)) ^ 2 := by
            have h7 : y = y / 2 + y / 2 := by ring
            rw [h7, Real.exp_add] <;> ring_nf
          rw [h6]
          nlinarith [sq_pos_of_neg hneg]
    by_cases h5 : eigval i - 1 = 0
    · linarith
    · have h6 := h_strict (eigval i - 1) h5
      rw [h_eq4] at h6
      <;> linarith
  have h_S_b : ∀ (i : Fin n), S (b i) = (b i) := by
    intro i
    have h_eig : S (b i) = eigval i • b i := hS_symm.apply_eigenvectorBasis hn' i
    rw [h_eig, h_all_one i] <;> simp
  have h_basis_expand : ∀ (x : E n), x = ∑ j : Fin n, inner ℝ (b j) x • b j := by
    intro x
    have h : (∑ j : Fin n, b.repr x j • b j) = x := b.sum_repr x
    have h2 : ∀ j, b.repr x j = inner ℝ (b j) x := by
      intro j; exact OrthonormalBasis.repr_apply_apply b x j
    have h3 : (∑ j : Fin n, b.repr x j • b j) = ∑ j : Fin n, inner ℝ (b j) x • b j := by
      apply Finset.sum_congr rfl; intro j _; rw [h2 j]
    rw [h3] at h; exact h.symm
  apply LinearMap.ext
  intro x
  have h_expand : x = ∑ j : Fin n, inner ℝ (b j) x • b j := h_basis_expand x
  have h4 : S x = ∑ j : Fin n, inner ℝ (b j) x • S (b j) := by
    calc
      S x = S (∑ j : Fin n, inner ℝ (b j) x • b j) := by exact congr_arg S h_expand
      _ = ∑ j : Fin n, S (inner ℝ (b j) x • b j) := by rw [map_sum S]
      _ = ∑ j : Fin n, inner ℝ (b j) x • S (b j) := by
          apply Finset.sum_congr rfl; intro j _
          exact S.map_smul (inner ℝ (b j) x) (b j)
  rw [h4]
  have h5 : ∑ j : Fin n, inner ℝ (b j) x • S (b j) = ∑ j : Fin n, inner ℝ (b j) x • b j := by
    apply Finset.sum_congr rfl; intro j _; rw [h_S_b j]
  rw [h5]
  exact h_expand.symm

end DetTraceAMGM

section IsometryConsequences

lemma norm_eq_of_adjoint_comp_eq_one
    (T : E n ≃ₗ[ℝ] E n)
    (hT : (T : E n →ₗ[ℝ] E n).adjoint.comp
        (T : E n →ₗ[ℝ] E n) = (1 : E n →ₗ[ℝ] E n)) :
    ∀ x : E n, ‖T x‖ = ‖x‖ := by
  intro x
  have hnorm_sq :
      ‖T x‖ ^ 2 = ‖x‖ ^ 2 := by
    have hinner :
        inner ℝ (((T : E n →ₗ[ℝ] E n).adjoint.comp
          (T : E n →ₗ[ℝ] E n)) x) x = ‖T x‖ ^ 2 :=
      inner_S_self_eq_norm_sq (T : E n →ₗ[ℝ] E n) x
    rw [hT] at hinner
    have hself : inner ℝ x x = ‖x‖ ^ 2 :=
      real_inner_self_eq_norm_sq x
    simpa [hself] using hinner.symm
  nlinarith [norm_nonneg (T x), norm_nonneg x]

lemma image_unit_closedBall_eq_of_adjoint_comp_eq_one
    (T : E n ≃ₗ[ℝ] E n)
    (hT : (T : E n →ₗ[ℝ] E n).adjoint.comp
        (T : E n →ₗ[ℝ] E n) = (1 : E n →ₗ[ℝ] E n)) :
    (T : E n →ₗ[ℝ] E n) '' Metric.closedBall (0 : E n) 1 =
      Metric.closedBall (0 : E n) 1 := by
  have hnorm := norm_eq_of_adjoint_comp_eq_one T hT
  apply Set.Subset.antisymm
  · intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have hx_norm : ‖x‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hx
    have hTx_norm : ‖T x‖ ≤ 1 := by
      rw [hnorm x]
      exact hx_norm
    simpa [Metric.mem_closedBall, dist_zero_right] using hTx_norm
  · intro y hy
    have hy_norm : ‖y‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hy
    refine ⟨T.symm y, ?_, T.apply_symm_apply y⟩
    have hsymm_norm : ‖T.symm y‖ = ‖y‖ := by
      have h := hnorm (T.symm y)
      rw [T.apply_symm_apply] at h
      exact h.symm
    have hpreimage_norm : ‖T.symm y‖ ≤ 1 := by
      rw [hsymm_norm]
      exact hy_norm
    simpa [Metric.mem_closedBall, dist_zero_right] using hpreimage_norm

end IsometryConsequences

section MainUniqueness

theorem outerJohnEllipsoid_unique_main (n : ℕ) {K : Set (E n)} (hK : IsConvexBody K)
    (c1 c2 : E n) (A1 A2 : E n ≃ₗ[ℝ] E n)
    (h1 : IsOuterJohnEllipsoid K c1 A1)
    (h2 : IsOuterJohnEllipsoid K c2 A2) :
    ellipsoid c1 A1 = ellipsoid c2 A2 := by
  by_cases hn : 0 < n
  · -- Case n > 0
    have h_vol12 : volume (ellipsoid c1 A1) ≤ volume (ellipsoid c2 A2) :=
      h1.2 c2 A2 h2.1
    have h_vol21 : volume (ellipsoid c2 A2) ≤ volume (ellipsoid c1 A1) :=
      h2.2 c1 A1 h1.1
    have h_det_eq : |LinearMap.det (A1 : E n →ₗ[ℝ] E n)| =
        |LinearMap.det (A2 : E n →ₗ[ℝ] E n)| := by
      have h_le1 := (volume_ellipsoid_le_iff c1 A1 c2 A2).mp h_vol12
      have h_le2 := (volume_ellipsoid_le_iff c2 A2 c1 A1).mp h_vol21
      linarith
    let K' : Set (E n) := A1.symm '' ((-c1) +ᵥ K)
    have hK'_eq : K' = A1.symm (-c1) +ᵥ A1.symm '' K := by
      have h : A1.symm '' ((-c1) +ᵥ K) = A1.symm (-c1) +ᵥ A1.symm '' K := by
        ext z
        simp only [Set.mem_image, Set.mem_vadd_set]
        constructor
        · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
          refine ⟨A1.symm x, ⟨x, hx, rfl⟩, ?_⟩
          simp [vadd_eq_add, A1.symm.map_add] <;> abel
        · rintro ⟨w, ⟨x, hx, rfl⟩, rfl⟩
          refine ⟨(-c1) +ᵥ x, ⟨x, hx, rfl⟩, ?_⟩
          simp [vadd_eq_add, A1.symm.map_add] <;> abel
      exact h
    have hK'_sub : K' ⊆ Metric.closedBall (0 : E n) 1 := by
      intro y hy
      rcases hy with ⟨z, hz, rfl⟩
      rcases hz with ⟨x, hx, rfl⟩
      have h_norm : ‖A1.symm (x - c1)‖ ≤ 1 := by
        simpa [ellipsoid_mem_iff] using h1.1 hx
      have h_eq : A1.symm ((-c1) +ᵥ x) = A1.symm (x - c1) := by
        have h : (-c1) +ᵥ x = x - c1 := by simp [vadd_eq_add] <;> abel
        rw [h]
      rw [h_eq]
      simpa [dist_zero_right] using h_norm
    have hK'_convex : Convex ℝ K' := by
      rw [hK'_eq]
      exact (hK.1.linear_image (A1.symm : E n →ₗ[ℝ] E n)).vadd (A1.symm (-c1))
    have hK'_compact : IsCompact K' := by
      rw [hK'_eq]
      exact (hK.2.1.image (A1.symm : E n →ₗ[ℝ] E n).continuous_of_finiteDimensional).vadd (A1.symm (-c1))
    let h_homeo : E n ≃ₜ E n :=
      { toFun := A1.symm,
        invFun := A1,
        left_inv := A1.symm.left_inv,
        right_inv := A1.symm.right_inv,
        continuous_toFun := A1.symm.continuous_of_finiteDimensional,
        continuous_invFun := A1.continuous_of_finiteDimensional }
    have h_interior_image : interior (A1.symm '' K) = A1.symm '' interior K := by
      have h := h_homeo.image_interior K
      exact h.symm
    have hK'_interior : (interior K').Nonempty := by
      rw [hK'_eq, interior_vadd, h_interior_image]
      rcases hK.2.2 with ⟨x, hx⟩
      refine ⟨A1.symm (-c1) +ᵥ A1.symm x, ?_⟩
      exact Set.mem_vadd_set.mpr ⟨A1.symm x, ⟨x, hx, rfl⟩, rfl⟩
    let hK'_body : IsConvexBody K' := ⟨hK'_convex, hK'_compact, hK'_interior⟩
    have hK'_min : ∀ (c : E n) (A : E n ≃ₗ[ℝ] E n),
        K' ⊆ ellipsoid c A →
        volume (ellipsoid (0 : E n) (1 : E n ≃ₗ[ℝ] E n)) ≤ volume (ellipsoid c A) := by
      intro c A h_sub
      have hK_sub : K ⊆ ellipsoid (c1 + A1 c) (A.trans A1) := by
        intro x hx
        set y : E n := A1.symm (x - c1) with hy_def
        have hy_in_K' : y ∈ K' := by
          have h1 : (-c1) +ᵥ x ∈ (-c1) +ᵥ K := Set.mem_vadd_set.mpr ⟨x, hx, rfl⟩
          exact ⟨(-c1) +ᵥ x, h1, by simp [hy_def, vadd_eq_add] <;> abel⟩
        have h_ellip : y ∈ ellipsoid c A := h_sub hy_in_K'
        have h_norm : ‖A.symm (y - c)‖ ≤ 1 := by
          simpa [ellipsoid_mem_iff] using h_ellip
        set z : E n := A.symm (y - c) with hz_def
        have hz_norm : ‖z‖ ≤ 1 := h_norm
        have h1 : A z = y - c := A.apply_symm_apply (y - c)
        have h_goal : ‖(A.trans A1).symm (x - (c1 + A1 c))‖ ≤ 1 := by
          have h_eq1 : (A.trans A1).symm (x - (c1 + A1 c)) = z := by
            have h2 : (A.trans A1).symm (x - (c1 + A1 c)) =
                A.symm (A1.symm (x - (c1 + A1 c))) := by rfl
            rw [h2]
            have h3 : x - (c1 + A1 c) = (x - c1) - A1 c := by abel
            rw [h3]
            have h4 : A1.symm ((x - c1) - A1 c) = A1.symm (x - c1) - A1.symm (A1 c) := by
              exact A1.symm.map_sub (x - c1) (A1 c)
            have h5 : A1.symm (A1 c) = c := A1.symm_apply_apply c
            rw [h4, h5] <;> rfl
          rw [h_eq1]; exact hz_norm
        simpa [ellipsoid_mem_iff] using h_goal
      have h_min := h1.2 (c1 + A1 c) (A.trans A1) hK_sub
      have h_det_le : |LinearMap.det (A1 : E n →ₗ[ℝ] E n)| ≤
          |LinearMap.det ((A.trans A1) : E n →ₗ[ℝ] E n)| :=
        (volume_ellipsoid_le_iff c1 A1 (c1 + A1 c) (A.trans A1)).mp h_min
      have h_det_comp : LinearMap.det ((A.trans A1) : E n →ₗ[ℝ] E n) =
          LinearMap.det (A1 : E n →ₗ[ℝ] E n) * LinearMap.det (A : E n →ₗ[ℝ] E n) := by
        have h_eq : (A.trans A1 : E n →ₗ[ℝ] E n) = (A1 : E n →ₗ[ℝ] E n).comp (A : E n →ₗ[ℝ] E n) := by
          ext z; rfl
        rw [h_eq]
        exact LinearMap.det_comp (A1 : E n →ₗ[ℝ] E n) (A : E n →ₗ[ℝ] E n)
      have h_abs : |LinearMap.det ((A.trans A1) : E n →ₗ[ℝ] E n)| =
          |LinearMap.det (A1 : E n →ₗ[ℝ] E n)| * |LinearMap.det (A : E n →ₗ[ℝ] E n)| := by
        rw [h_det_comp, abs_mul]
      rw [h_abs] at h_det_le
      have h_det1_pos : 0 < |LinearMap.det (A1 : E n →ₗ[ℝ] E n)| :=
        abs_pos.mpr (LinearEquiv.isUnit_det' A1).ne_zero
      have h_one_le : (1 : ℝ) ≤ |LinearMap.det (A : E n →ₗ[ℝ] E n)| := by nlinarith
      have h_iff := volume_ellipsoid_le_iff (0 : E n) (1 : E n ≃ₗ[ℝ] E n) c A
      have h_final : |LinearMap.det ((1 : E n ≃ₗ[ℝ] E n) : E n →ₗ[ℝ] E n)| ≤
          |LinearMap.det (A : E n →ₗ[ℝ] E n)| := by simpa using h_one_le
      exact h_iff.mpr h_final
    rcases general_fritz_john_conditions hn hK'_body hK'_sub hK'_min with
      ⟨m, u, c, h_contact, hc_nonneg, hc_sum, hc_center, hc_outer⟩
    let T : E n ≃ₗ[ℝ] E n := A1.trans A2.symm
    let d : E n := A2.symm (c1 - c2)
    let T_lin : E n →ₗ[ℝ] E n := (T : E n →ₗ[ℝ] E n)
    have hdet_abs : |LinearMap.det T_lin| = 1 := by
      have h1 : LinearMap.det T_lin =
          LinearMap.det (A2.symm : E n →ₗ[ℝ] E n) * LinearMap.det (A1 : E n →ₗ[ℝ] E n) := by
        have h_eq : T_lin = (A2.symm : E n →ₗ[ℝ] E n).comp (A1 : E n →ₗ[ℝ] E n) := by
          ext z; rfl
        rw [h_eq]
        exact LinearMap.det_comp (A2.symm : E n →ₗ[ℝ] E n) (A1 : E n →ₗ[ℝ] E n)
      rw [h1]
      have h2 : LinearMap.det (A2.symm : E n →ₗ[ℝ] E n) =
          (LinearMap.det (A2 : E n →ₗ[ℝ] E n))⁻¹ := by
        exact LinearEquiv.det_coe_symm A2
      rw [h2, abs_mul, abs_inv, h_det_eq]
      <;> field_simp [(LinearEquiv.isUnit_det' A2).ne_zero] <;> ring
    have h_bound : ∀ (i : Fin m), ‖T_lin (u i) + d‖ ≤ 1 := by
      intro i
      have h_ui_in_K' : u i ∈ K' := (h_contact i).1
      have h_x_in_K : A1 (u i) + c1 ∈ K := by
        rcases h_ui_in_K' with ⟨z, hz, h_eq⟩
        have hz2 : z = A1 (u i) := by
          have h3 : A1 (A1.symm z) = z := A1.apply_symm_apply z
          rw [h_eq] at h3; exact h3.symm
        rcases hz with ⟨x, hx, hz_eq⟩
        have h4 : (-c1) +ᵥ x = z := hz_eq
        have h5 : x - c1 = A1 (u i) := by
          have h6 : (-c1) +ᵥ x = x - c1 := by simp [vadd_eq_add] <;> abel
          rw [h6] at h4
          rw [hz2] at h4
          exact h4
        have h7 : x = A1 (u i) + c1 := by
          have h8 : x - c1 = A1 (u i) := h5
          exact sub_eq_iff_eq_add.mp h8
        rw [h7] at hx; exact hx
      have h7 : A1 (u i) + c1 ∈ ellipsoid c2 A2 := h2.1 h_x_in_K
      have h8 : ‖A2.symm ((A1 (u i) + c1) - c2)‖ ≤ 1 := by
        simpa [ellipsoid_mem_iff] using h7
      have h9 : A2.symm ((A1 (u i) + c1) - c2) = T_lin (u i) + d := by
        simp [T_lin, T, d, A2.symm.map_add, A2.symm.map_sub] <;> abel
      rw [h9] at h8; exact h8
    have h_sum_ineq : ∑ i : Fin m, c i * (‖T_lin (u i) + d‖ ^ 2) ≤ (n : ℝ) := by
      have h_le : ∀ i ∈ Finset.univ, c i * (‖T_lin (u i) + d‖ ^ 2) ≤ c i * 1 := by
        intro i _
        have h10 : ‖T_lin (u i) + d‖ ^ 2 ≤ 1 := by
          have h11 : ‖T_lin (u i) + d‖ ≤ 1 := h_bound i
          have h12 : 0 ≤ ‖T_lin (u i) + d‖ := by positivity
          nlinarith
        have h13 : 0 ≤ c i := hc_nonneg i
        exact mul_le_mul_of_nonneg_left h10 h13
      calc
        ∑ i : Fin m, c i * (‖T_lin (u i) + d‖ ^ 2)
          ≤ ∑ i : Fin m, c i * 1 := Finset.sum_le_sum h_le
        _ = ∑ i : Fin m, c i := by simp [Finset.mul_sum]
        _ = (n : ℝ) := hc_sum
    let S : E n →ₗ[ℝ] E n := T_lin.adjoint.comp T_lin
    have hS_symm : S.IsSymmetric := adjoint_comp_symmetric T_lin
    have hS_pos : ∀ (x : E n), 0 ≤ inner ℝ x (S x) := adjoint_comp_pos T_lin
    have h_expand : ∑ i : Fin m, c i * (‖T_lin (u i) + d‖ ^ 2) =
        (S.trace ℝ (E n)) + (n : ℝ) * ‖d‖ ^ 2 := by
      have h1 : ∀ (i : Fin m), ‖T_lin (u i) + d‖ ^ 2 =
          ‖T_lin (u i)‖ ^ 2 + 2 * inner ℝ (T_lin (u i)) d + ‖d‖ ^ 2 := by
        intro i
        have h : ‖T_lin (u i) + d‖ ^ 2 = ‖T_lin (u i)‖ ^ 2 + 2 * inner ℝ (T_lin (u i)) d + ‖d‖ ^ 2 := by
          simp [norm_add_sq_real] <;> ring
        exact h
      have h_center2 : T_lin (∑ i : Fin m, c i • u i) = 0 := by
        rw [hc_center] <;> simp
      have h_sum1 : ∑ i : Fin m, c i * (‖T_lin (u i) + d‖ ^ 2) =
          ∑ i : Fin m, c i * ‖T_lin (u i)‖ ^ 2 +
          2 * ∑ i : Fin m, c i * inner ℝ (T_lin (u i)) d +
          (∑ i : Fin m, c i) * ‖d‖ ^ 2 := by
        have h_apply : ∑ i : Fin m, c i * (‖T_lin (u i) + d‖ ^ 2) =
            ∑ i : Fin m, c i * (‖T_lin (u i)‖ ^ 2 + 2 * inner ℝ (T_lin (u i)) d + ‖d‖ ^ 2) := by
          apply Finset.sum_congr rfl; intro i _; rw [h1 i]
        rw [h_apply]
        have h_dist : ∑ i : Fin m, c i * (‖T_lin (u i)‖ ^ 2 + 2 * inner ℝ (T_lin (u i)) d + ‖d‖ ^ 2) =
            ∑ i : Fin m, (c i * ‖T_lin (u i)‖ ^ 2 + c i * (2 * inner ℝ (T_lin (u i)) d) + c i * ‖d‖ ^ 2) := by
          apply Finset.sum_congr rfl; intro i _; ring
        rw [h_dist]
        have h_final : ∑ i : Fin m, (c i * ‖T_lin (u i)‖ ^ 2 + c i * (2 * inner ℝ (T_lin (u i)) d) + c i * ‖d‖ ^ 2) =
            (∑ i : Fin m, c i * ‖T_lin (u i)‖ ^ 2) +
            2 * (∑ i : Fin m, c i * inner ℝ (T_lin (u i)) d) +
            (∑ i : Fin m, c i) * ‖d‖ ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
          have h4 : ∑ i : Fin m, c i * (2 * inner ℝ (T_lin (u i)) d) =
              2 * ∑ i : Fin m, c i * inner ℝ (T_lin (u i)) d := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro i _; ring
          have h5 : ∑ i : Fin m, c i * ‖d‖ ^ 2 = (∑ i : Fin m, c i) * ‖d‖ ^ 2 := by
            rw [Finset.sum_mul]
          rw [h4, h5] <;> ring
        exact h_final
      have h_sum2 : ∑ i : Fin m, c i * inner ℝ (T_lin (u i)) d =
          inner ℝ (∑ i : Fin m, c i • T_lin (u i)) d := by
        have h3 : ∑ i : Fin m, c i * inner ℝ (T_lin (u i)) d =
            ∑ i : Fin m, inner ℝ (c i • T_lin (u i)) d := by
          apply Finset.sum_congr rfl; intro i _
          have h4 : inner ℝ (c i • T_lin (u i)) d = c i * inner ℝ (T_lin (u i)) d := by
            rw [inner_smul_left] <;> simp
          exact h4.symm
        rw [h3]
        have h5 : inner ℝ (∑ i : Fin m, c i • T_lin (u i)) d =
            ∑ i : Fin m, inner ℝ (c i • T_lin (u i)) d := by
          have h_sym : inner ℝ (∑ i : Fin m, c i • T_lin (u i)) d =
              inner ℝ d (∑ i : Fin m, c i • T_lin (u i)) := by
            exact real_inner_comm d (∑ i, c i • T_lin (u i))
          rw [h_sym, inner_sum]
          apply Finset.sum_congr rfl
          intro i _
          exact real_inner_comm (c i • T_lin (u i)) d
        exact h5.symm
      have h_sum3 : ∑ i : Fin m, c i • T_lin (u i) = T_lin (∑ i : Fin m, c i • u i) := by
        have h : T_lin (∑ i : Fin m, c i • u i) = ∑ i : Fin m, T_lin (c i • u i) := by
          rw [map_sum T_lin]
        have h2 : ∑ i : Fin m, T_lin (c i • u i) = ∑ i : Fin m, c i • T_lin (u i) := by
          apply Finset.sum_congr rfl; intro i _
          rw [T_lin.map_smul]
        have h3 : T_lin (∑ i : Fin m, c i • u i) = ∑ i : Fin m, c i • T_lin (u i) := by
          rw [h, h2]
        exact h3.symm
      rw [h_sum1, h_sum2, h_sum3, h_center2, hc_sum]
      have h_trace_id : S.trace ℝ (E n) = ∑ i : Fin m, c i * ‖T_lin (u i)‖ ^ 2 :=
        fritz_john_trace_identity hc_outer T_lin
      rw [h_trace_id] <;> simp <;> ring
    rw [h_expand] at h_sum_ineq
    have h_amgm : S.det ≤ (S.trace ℝ (E n) / (n : ℝ)) ^ n :=
      posSemidef_det_le_trace_pow hS_symm hS_pos hn
    have h_det_adj : LinearMap.det T_lin.adjoint = LinearMap.det T_lin :=
      det_adjoint_eq_det T_lin
    have hS_det : S.det = (LinearMap.det T_lin) ^ 2 := by
      have h : S.det = LinearMap.det T_lin.adjoint * LinearMap.det T_lin := by
        simpa [S, LinearMap.det_comp] using rfl
      rw [h, h_det_adj] <;> ring
    have hS_det_pos : 0 < S.det := by
      rw [hS_det]
      have h : 0 ≤ (LinearMap.det T_lin) ^ 2 := by positivity
      have h2 : (LinearMap.det T_lin) ^ 2 ≠ 0 := by
        have h3 : LinearMap.det T_lin ≠ 0 := (LinearEquiv.isUnit_det' T).ne_zero
        exact pow_ne_zero 2 h3
      exact lt_of_le_of_ne h (Ne.symm h2)
    have hS_det_one : S.det = 1 := by
      have h_abs : |S.det| = 1 := by
        rw [hS_det, abs_pow, hdet_abs] <;> norm_num
      have h : |S.det| = S.det := abs_of_pos hS_det_pos
      rw [h] at h_abs; exact h_abs
    have h_trace_nonneg : 0 ≤ S.trace ℝ (E n) :=
      posSemidef_trace_nonneg hS_pos
    have h_trace_ge_n : (n : ℝ) ≤ S.trace ℝ (E n) := by
      rw [hS_det_one] at h_amgm
      by_contra h3
      have h4 : S.trace ℝ (E n) / (n : ℝ) < 1 := by
        have h5 : (n : ℝ) > 0 := Nat.cast_pos.mpr hn
        have h6 : S.trace ℝ (E n) < (n : ℝ) := by linarith
        exact (div_lt_one h5).mpr h6
      have h6 : 0 ≤ S.trace ℝ (E n) / (n : ℝ) := by
        apply div_nonneg h_trace_nonneg
        exact Nat.cast_nonneg n
      have h7 : (S.trace ℝ (E n) / (n : ℝ)) ^ n < 1 := by
        have h8 : ∀ (x : ℝ), 0 ≤ x → x < 1 → ∀ (k : ℕ), 0 < k → x ^ k < 1 := by
          intro x hx hx2 k hk
          induction k with
          | zero => contradiction
          | succ k' ih =>
            by_cases h_k : k' = 0
            · rw [h_k]; simpa using hx2
            · have h_ih' : x ^ k' < 1 := ih (Nat.pos_of_ne_zero h_k)
              have h_nonneg : 0 ≤ x ^ k' := by positivity
              have h_mul : x * x ^ k' < 1 := by
                calc
                  x * x ^ k' ≤ 1 * x ^ k' := by gcongr <;> linarith
                  _ = x ^ k' := by ring
                  _ < 1 := h_ih'
              simpa [pow_succ] using by
                have h_mul' : x ^ k' * x < 1 := by
                  rw [mul_comm]; exact h_mul
                exact h_mul'
        exact h8 (S.trace ℝ (E n) / (n : ℝ)) h6 h4 n hn
      linarith
    have h_d_zero : d = 0 := by
      have h_ineq1 : (S.trace ℝ (E n)) + (n : ℝ) * ‖d‖ ^ 2 ≤ (n : ℝ) := h_sum_ineq
      have h_ineq2 : (n : ℝ) ≤ S.trace ℝ (E n) := h_trace_ge_n
      have h : (n : ℝ) * ‖d‖ ^ 2 ≤ 0 := by linarith
      have h' : ‖d‖ ^ 2 ≤ 0 := by
        have hpos : (n : ℝ) > 0 := Nat.cast_pos.mpr hn
        nlinarith
      have h'' : ‖d‖ = 0 := by nlinarith [norm_nonneg d]
      simpa [norm_eq_zero] using h''
    have h_trace_eq_n : S.trace ℝ (E n) = (n : ℝ) := by
      have h_ineq1 : (S.trace ℝ (E n)) + (n : ℝ) * ‖d‖ ^ 2 ≤ (n : ℝ) := h_sum_ineq
      have h_ineq2 : (n : ℝ) ≤ S.trace ℝ (E n) := h_trace_ge_n
      have h_d0 : ‖d‖ ^ 2 = 0 := by
        have h : ‖d‖ = 0 := by simpa [norm_eq_zero] using h_d_zero
        rw [h] <;> norm_num
      rw [h_d0] at h_ineq1
      linarith
    have h_c1_eq_c2 : c1 = c2 := by
      have h : A2.symm (c1 - c2) = 0 := h_d_zero
      have h2 : c1 - c2 = 0 := by
        have h3 := A2.apply_symm_apply (c1 - c2)
        rw [h] at h3
        simpa using h3.symm
      simpa [sub_eq_zero] using h2
    have h_S_id : S = (1 : E n →ₗ[ℝ] E n) :=
      eq_am_gm_implies_id hS_symm hS_pos hn hS_det_one h_trace_eq_n
    have hT_ball :
        T_lin '' Metric.closedBall (0 : E n) 1 =
          Metric.closedBall (0 : E n) 1 := by
      simpa only [T_lin] using
        image_unit_closedBall_eq_of_adjoint_comp_eq_one T h_S_id
    have h_eq1 : (A1 : E n →ₗ[ℝ] E n) = (A2 : E n →ₗ[ℝ] E n).comp T_lin := by
      ext x; simp [T_lin, T] <;> rfl
    have h_A1_image : (A1 : E n →ₗ[ℝ] E n) '' Metric.closedBall (0 : E n) 1 =
        (A2 : E n →ₗ[ℝ] E n) '' Metric.closedBall (0 : E n) 1 := by
      rw [h_eq1]
      have h_image : ((A2 : E n →ₗ[ℝ] E n).comp T_lin) '' Metric.closedBall (0 : E n) 1 =
          (A2 : E n →ₗ[ℝ] E n) '' (T_lin '' Metric.closedBall (0 : E n) 1) := by
        exact Set.image_comp (A2 : E n →ₗ[ℝ] E n) T_lin (Metric.closedBall (0 : E n) 1)
      rw [h_image, hT_ball]
    have h_final : ellipsoid c1 A1 = ellipsoid c2 A2 := by
      have hc : c1 = c2 := h_c1_eq_c2
      rw [hc]
      dsimp only [ellipsoid]
      exact congr_arg (fun s => c2 +ᵥ s) h_A1_image
    exact h_final
  · -- Case n = 0
    have hn0 : n = 0 := by omega
    haveI : Subsingleton (E n) := by rw [hn0] <;> infer_instance
    have h_c_eq : c1 = c2 := by
      exact Subsingleton.elim c1 c2
    have h_ellip_eq : ellipsoid c1 A1 = ellipsoid c2 A2 := by
      rw [h_c_eq]
      have h_univ1 : ellipsoid c2 A1 = Set.univ := by
        have hne : (ellipsoid c2 A1).Nonempty := ellipsoid_nonempty c2 A1
        exact Subsingleton.eq_univ_of_nonempty hne
      have h_univ2 : ellipsoid c2 A2 = Set.univ := by
        have hne : (ellipsoid c2 A2).Nonempty := ellipsoid_nonempty c2 A2
        exact Subsingleton.eq_univ_of_nonempty hne
      rw [h_univ1, h_univ2]
    exact h_ellip_eq

end MainUniqueness

end JohnEllipsoid
