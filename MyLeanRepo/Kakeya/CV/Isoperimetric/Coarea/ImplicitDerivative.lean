import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.GraphArea
import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Tactic

/-!
# Implicit Function Derivative Lemma for Coarea Formula

For a local diffeomorphism Φ(y) = projHCL(y) + f(y)·eLast with inverse Ψ,
define g_t(v) = last coordinate of Ψ(unsplit(v,t)). Then:

  ‖fderiv f y‖ / |fderiv f y eLast| = √(1 + ‖fderiv g_t v‖²)

where y = Ψ(unsplit(v,t)).

This supplies the implicit-derivative identity used in the Fubini step.
-/

open MeasureTheory Metric Set ENNReal LinearMap Filter
open scoped MeasureTheory

namespace Geometry

variable {m : ℕ} [Nonempty (Fin m)]

-- ============================================================================
-- Infrastructure
-- ============================================================================

/-- Last standard basis vector in E(m+1). -/
noncomputable def eLast : E (m + 1) :=
  EuclideanSpace.single (Fin.last m) 1

lemma norm_eLast : ‖(eLast : E (m + 1))‖ = 1 := by
  simp [eLast, EuclideanSpace.norm_single]

/-- Last coordinate as continuous linear functional. -/
noncomputable def coordECL : E (m + 1) →L[ℝ] ℝ :=
  { toFun := fun y => y (Fin.last m)
    map_add' := by intro y z; rfl
    map_smul' := by intro c y; rfl
    cont := by fun_prop }

lemma coordECL_eLast : coordECL (eLast : E (m + 1)) = 1 := by
  simp [coordECL, eLast, EuclideanSpace.single_apply] <;> aesop

/-- Orthogonal projection onto eLastᗮ. -/
noncomputable def projHCL : E (m + 1) →L[ℝ] E (m + 1) :=
  ContinuousLinearMap.id ℝ (E (m + 1)) - coordECL.smulRight (eLast : E (m + 1))

lemma coordECL_projHCL (w : E (m + 1)) : coordECL (projHCL w) = 0 := by
  simp [projHCL, coordECL_eLast] <;> ring

/-- Scaling by eLast: ℝ → E(m+1). -/
noncomputable def scaleE : ℝ →L[ℝ] E (m + 1) :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight (eLast : E (m + 1))

/-- Inclusion E(m) → E(m+1) as last-coordinate-zero subspace. -/
noncomputable def inclEm : E m →L[ℝ] E (m + 1) :=
  (GraphAreaFormula.F_lin (0 : E m →L[ℝ] ℝ)).toContinuousLinearMap

lemma inclEm_isometry (v : E m) : ‖inclEm v‖ = ‖v‖ := by
  have h : inner ℝ (inclEm v) (inclEm v) = inner ℝ v v + (0 : ℝ) * (0 : ℝ) :=
    GraphAreaFormula.inner_F_lin (0 : E m →L[ℝ] ℝ) v v
  have h2 : ‖inclEm v‖ ^ 2 = ‖v‖ ^ 2 := by
    simpa [inner_self_eq_norm_sq_to_K] using h
  have h3 : 0 ≤ ‖inclEm v‖ := by positivity
  have h4 : 0 ≤ ‖v‖ := by positivity
  nlinarith

/-- Unsplit E(m) × ℝ → E(m+1). -/
noncomputable def unsplit (v : E m) (t : ℝ) : E (m + 1) :=
  GraphAreaFormula.graphMap (fun _ => t) v

lemma unsplit_eq (t : ℝ) (w : E m) :
    unsplit w t = inclEm w + scaleE t := by
  ext i
  by_cases h : i.val < m
  · let j : Fin m := ⟨i.val, h⟩
    have hi : i = Fin.castSucc j := by apply Fin.ext; simp [j] <;> omega
    have h1 : (unsplit w t) i = w j := by
      rw [hi]; exact GraphAreaFormula.graphMap_apply_castSucc (fun _ => t) w j
    have h21 : (inclEm w) i = w j := by
      rw [hi]; exact GraphAreaFormula.F_lin_apply_castSucc (0 : E m →L[ℝ] ℝ) w j
    have h22 : (scaleE t) i = 0 := by
      rw [hi]
      have h_eLast : (eLast : E (m + 1)) (Fin.castSucc j) = 0 := by
        simp [eLast, EuclideanSpace.single_apply] <;> omega
      simp [scaleE, h_eLast] <;> ring
    have h_sum : ((inclEm w + scaleE t) : E (m + 1)) i = (inclEm w) i + (scaleE t) i := by rfl
    rw [h_sum, h21, h22, h1] <;> ring
  · have hlast : i = Fin.last m := by apply Fin.ext; simp [h] <;> omega
    have h1 : (unsplit w t) i = t := by
      rw [hlast]; exact GraphAreaFormula.graphMap_apply_last (fun _ => t) w
    have h21 : (inclEm w) i = 0 := by
      rw [hlast]; exact GraphAreaFormula.F_lin_apply_last (0 : E m →L[ℝ] ℝ) w
    have h22 : (scaleE t) i = t := by
      rw [hlast]
      have h_eLast : (eLast : E (m + 1)) (Fin.last m) = 1 := by
        simp [eLast, EuclideanSpace.single_apply] <;> omega
      simp [scaleE, h_eLast] <;> ring
    have h_sum : ((inclEm w + scaleE t) : E (m + 1)) i = (inclEm w) i + (scaleE t) i := by rfl
    rw [h_sum, h21, h22, h1] <;> ring

lemma unsplit_deriv (t : ℝ) (v : E m) :
    HasStrictFDerivAt (fun w : E m => unsplit w t) inclEm v := by
  have h_eq : (fun w : E m => unsplit w t) = fun w => inclEm w + scaleE t := by
    funext w; exact unsplit_eq t w
  rw [h_eq]
  have h_a : HasStrictFDerivAt inclEm inclEm v := inclEm.hasStrictFDerivAt
  have h_b : HasStrictFDerivAt (fun (_ : E m) => scaleE t) (0 : E m →L[ℝ] E (m + 1)) v := by
    exact hasStrictFDerivAt_const (scaleE t : E (m + 1)) v
  have h_sum : HasStrictFDerivAt (fun w : E m => inclEm w + scaleE t)
      (inclEm + (0 : E m →L[ℝ] E (m + 1))) v := h_a.add h_b
  have h_zero : inclEm + (0 : E m →L[ℝ] E (m + 1)) = inclEm := by simp
  rw [h_zero] at h_sum
  exact h_sum

/-- HOrth = kernel of coordECL. -/
noncomputable def HOrth : Submodule ℝ (E (m + 1)) := coordECL.ker

lemma hOrth_iff (x : E (m + 1)) : x ∈ HOrth ↔ coordECL x = 0 := by
  simp [HOrth]

lemma inner_eq_coordECL (x : E (m + 1)) :
    inner ℝ x (eLast : E (m + 1)) = coordECL x := by
  have h1 : inner ℝ x (eLast : E (m + 1)) = ∑ i : Fin (m + 1), x i * (eLast : E (m + 1)) i := by
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro i _
    simp <;> ring
  rw [h1]
  have h2 : ∑ i : Fin (m + 1), x i * (eLast : E (m + 1)) i = x (Fin.last m) := by
    rw [Fin.sum_univ_castSucc]
    have h3 : ∑ j : Fin m, x (Fin.castSucc j) * (eLast : E (m + 1)) (Fin.castSucc j) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      simp [eLast, EuclideanSpace.single_apply] <;> aesop
    have h4 : x (Fin.last m) * (eLast : E (m + 1)) (Fin.last m) = x (Fin.last m) := by
      simp [eLast, EuclideanSpace.single_apply] <;> ring
    rw [h3, h4] <;> ring
  rw [h2]
  <;> rfl

/-- Derivative of Φ(y) = projHCL(y) + f(y)·eLast. -/
noncomputable def coareaPhiFDeriv (f' : E (m + 1) →L[ℝ] ℝ) :
    E (m + 1) →L[ℝ] E (m + 1) :=
  projHCL + scaleE.comp f'

/-- Determinant of coareaPhiFDeriv equals f'(eLast). -/
lemma det_coareaPhiFDeriv (f' : E (m + 1) →L[ℝ] ℝ) :
    (coareaPhiFDeriv f').det = f' (eLast : E (m + 1)) := by
  let b : OrthonormalBasis (Fin (m + 1)) ℝ (E (m + 1)) :=
    EuclideanSpace.basisFun (Fin (m + 1)) ℝ
  let D := coareaPhiFDeriv f'
  let v : E (m + 1) →L[ℝ] ℝ := f' - coordECL
  let u : E (m + 1) := eLast
  have hD : D = ContinuousLinearMap.id ℝ (E (m + 1)) + v.smulRight u := by
    apply ContinuousLinearMap.ext
    intro y
    have h1 : D y = projHCL y + scaleE (f' y) := by rfl
    have h2 : projHCL y = y - coordECL y • u := by rfl
    have h3 : scaleE (f' y) = f' y • u := by rfl
    rw [h1, h2, h3]
    <;> simp [v, sub_smul] <;> abel
  let bB := b.toBasis
  let uVec : Fin (m + 1) → ℝ := fun i => inner ℝ (b i) u
  let vVec : Fin (m + 1) → ℝ := fun j => v (b j)
  let M := LinearMap.toMatrix bB bB D.toLinearMap
  let oneMat : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ := 1
  have hMatrix : M = oneMat + Matrix.replicateCol (Fin 1) uVec * Matrix.replicateRow (Fin 1) vVec := by
    ext i j
    have hMij : M i j = bB.repr (D (bB j)) i := LinearMap.toMatrix_apply bB bB D.toLinearMap i j
    rw [hMij, hD]
    have h2 : bB.repr ((ContinuousLinearMap.id ℝ (E (m + 1)) + v.smulRight u) (bB j)) i =
        bB.repr (bB j) i + v (bB j) * bB.repr u i := by
      simp [map_add, map_smul, ContinuousLinearMap.smulRight_apply] <;> ring
    rw [h2]
    have h3 : bB.repr (bB j) i = if i = j then (1 : ℝ) else 0 := by
      have h31 := bB.repr_self j
      rw [h31]
      simp [Finsupp.single_apply] <;> split_ifs <;> tauto
    have h4 : bB.repr u i = inner ℝ (b i) u :=
      OrthonormalBasis.repr_apply_apply b u i
    rw [h3, h4]
    have h_mat : (Matrix.replicateCol (Fin 1) uVec * Matrix.replicateRow (Fin 1) vVec) i j = uVec i * vVec j := by
      have h_univ : (Finset.univ : Finset (Fin 1)) = {(0 : Fin 1)} := by ext x; simp
      rw [Matrix.mul_apply, h_univ, Finset.sum_singleton]
      <;> simp [Matrix.replicateCol, Matrix.replicateRow] <;> ring
    have h_one : oneMat i j = if i = j then (1 : ℝ) else 0 := by
      simp [oneMat, Matrix.one_apply] <;> aesop
    have h_bBj : bB j = b j := by rfl
    have h5 : (if i = j then (1 : ℝ) else 0) + v (bB j) * inner ℝ (b i) u =
        (oneMat + Matrix.replicateCol (Fin 1) uVec * Matrix.replicateRow (Fin 1) vVec) i j := by
      have h_add : (oneMat + Matrix.replicateCol (Fin 1) uVec * Matrix.replicateRow (Fin 1) vVec) i j =
          oneMat i j + (Matrix.replicateCol (Fin 1) uVec * Matrix.replicateRow (Fin 1) vVec) i j := by
        exact Matrix.add_apply oneMat _ i j
      rw [h_add, h_one, h_mat]
      have h_alg : v (bB j) * inner ℝ (b i) u = uVec i * vVec j := by
        simp [uVec, vVec, h_bBj, mul_comm] <;> ring
      rw [h_alg] <;> ring
    exact h5
  have h_main : M.det = 1 + vVec ⬝ᵥ uVec := by
    rw [hMatrix]
    exact Matrix.det_one_add_replicateCol_mul_replicateRow uVec vVec
  have h_dot : vVec ⬝ᵥ uVec = v u := by
    have h_dot1 : vVec ⬝ᵥ uVec = ∑ i : Fin (m + 1), vVec i * uVec i := by rfl
    rw [h_dot1]
    have h_expand : u = ∑ i : Fin (m + 1), inner ℝ (b i) u • b i := by
      have h_sum : (∑ i : Fin (m + 1), bB.repr u i • bB i) = u := bB.sum_repr u
      have h_eq : ∑ i : Fin (m + 1), bB.repr u i • bB i = ∑ i : Fin (m + 1), inner ℝ (b i) u • b i := by
        apply Finset.sum_congr rfl
        intro i _
        have h6 : bB.repr u i = inner ℝ (b i) u := OrthonormalBasis.repr_apply_apply b u i
        rw [h6] <;> rfl
      exact h_sum.symm.trans h_eq
    have h_ind : ∀ (s : Finset (Fin (m + 1))), v (∑ i ∈ s, inner ℝ (b i) u • b i) = ∑ i ∈ s, v (inner ℝ (b i) u • b i) := by
      intro s
      induction s using Finset.induction with
      | empty => simp
      | @insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, v.map_add] <;> rw [ih]
    calc
      vVec ⬝ᵥ uVec
        = ∑ i : Fin (m + 1), v (b i) * inner ℝ (b i) u := by rfl
      _ = ∑ i : Fin (m + 1), v (inner ℝ (b i) u • b i) := by
          apply Finset.sum_congr rfl
          intro i _
          have h : v (inner ℝ (b i) u • b i) = inner ℝ (b i) u * v (b i) := by
            rw [v.map_smul] <;> ring
          rw [h] <;> ring
      _ = v (∑ i : Fin (m + 1), inner ℝ (b i) u • b i) := (h_ind Finset.univ).symm
      _ = v u := by rw [← h_expand]
  have h_vu : v u = f' (eLast : E (m + 1)) - 1 := by
    have h_coord : coordECL (eLast : E (m + 1)) = 1 := coordECL_eLast
    simp [v, u, h_coord] <;> ring
  have h_det : D.det = M.det := (LinearMap.det_toMatrix bB D.toLinearMap).symm
  rw [h_det, h_main, h_dot, h_vu] <;> ring

-- ============================================================================
-- Algebraic identity (short proof)
-- ============================================================================

/-- Algebraic identity: if f'(h) + f'(e)·g'(h) = 0 for h ∈ H = eᗮ,
  then ‖f'‖ / |f'(e)| = √(1 + ‖g'‖²). -/
lemma algebraic_identity
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    (e : V) (he : ‖e‖ = 1)
    (H : Submodule ℝ V) (hH : ∀ v, v ∈ H ↔ inner ℝ v e = 0)
    (f' : V →L[ℝ] ℝ) (hne : f' e ≠ 0)
    (g' : H →L[ℝ] ℝ)
    (h2 : ∀ (h : H), f' (h : V) + f' e * g' h = 0) :
    ‖f'‖ / |f' e| = Real.sqrt (1 + ‖g'‖ ^ 2) := by
  let u_f : V := (InnerProductSpace.toDual ℝ V).symm f'
  have h1 : ∀ x, inner ℝ u_f x = f' x := by
    intro x; exact InnerProductSpace.toDual_symm_apply
  have h_norm_f : ‖u_f‖ = ‖f'‖ :=
    (InnerProductSpace.toDual ℝ V).symm.norm_map f'
  let α : ℝ := f' e
  have hα_ne : α ≠ 0 := hne
  let v_H : V := u_f - α • e
  have h_orth : inner ℝ v_H e = 0 := by
    simp [v_H, inner_sub_left, inner_smul_left, h1, he, inner_self_eq_norm_sq_to_K] <;> nlinarith
  have h_vH_in_H : v_H ∈ H := (hH v_H).mpr h_orth
  let v_H' : H := ⟨v_H, h_vH_in_H⟩

  have h_decomp : u_f = v_H + α • e := by simp [v_H] <;> abel
  have h_pyth : ‖u_f‖ ^ 2 = ‖v_H‖ ^ 2 + ‖α • e‖ ^ 2 := by
    rw [h_decomp]
    have h_orth2 : inner ℝ v_H (α • e) = 0 := by
      simp [inner_smul_right, h_orth] <;> ring
    have h : ‖v_H + α • e‖ ^ 2 = ‖v_H‖ ^ 2 + ‖α • e‖ ^ 2 := by
      simpa [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_real (h := h_orth2)
    exact h
  have h_c1 : ‖α • e‖ ^ 2 = α ^ 2 := by
    simp [norm_smul, he] <;> ring

  -- g' is represented by -v_H/α
  have h_g'_eq : ∀ (h : H), g' h = -inner ℝ v_H (h : V) / α := by
    intro h
    have h_eq : f' (h : V) + α * g' h = 0 := h2 h
    have h3 : f' (h : V) = inner ℝ u_f (h : V) := (h1 (h : V)).symm
    rw [h3] at h_eq
    have h4 : inner ℝ u_f (h : V) = inner ℝ v_H (h : V) := by
      rw [h_decomp]
      have h5 : inner ℝ (v_H + α • e) (h : V) = inner ℝ v_H (h : V) + inner ℝ (α • e) (h : V) := by
        rw [inner_add_left]
      rw [h5]
      have h6 : inner ℝ (α • e) (h : V) = α * inner ℝ e (h : V) := by
        simp [inner_smul_left] <;> ring
      rw [h6]
      have h7 : inner ℝ e (h : V) = 0 := by
        have h8 : inner ℝ (h : V) e = 0 := (hH (h : V)).mp h.prop
        have h9 : inner ℝ e (h : V) = inner ℝ (h : V) e := real_inner_comm (h : V) e
        rw [h9]; exact h8
      rw [h7] <;> ring
    rw [h4] at h_eq
    field_simp [hα_ne] at h_eq ⊢ <;> linarith

  have h_absα_pos : 0 < |α| := abs_pos.mpr hα_ne

  have h_norm_g' : ‖g'‖ = ‖v_H‖ / |α| := by
    have h_norm_abs : ∀ (x : ℝ), ‖x‖ = abs x := by
      intro x; simp
    have h_le : ‖g'‖ ≤ ‖v_H‖ / |α| := by
      apply g'.opNorm_le_bound (by positivity)
      intro h
      have h_val : g' h = -inner ℝ v_H (h : V) / α := h_g'_eq h
      rw [h_norm_abs (g' h), h_val]
      have h6 : abs (-inner ℝ v_H (h : V) / α) = abs (inner ℝ v_H (h : V)) / |α| := by
        rw [abs_div, abs_neg] <;> rfl
      rw [h6]
      have h5 : abs (inner ℝ v_H (h : V)) ≤ ‖v_H‖ * ‖(h : V)‖ :=
        abs_real_inner_le_norm v_H (h : V)
      have h_div : abs (inner ℝ v_H (h : V)) / |α| ≤ ‖v_H‖ * ‖(h : V)‖ / |α| :=
        div_le_div_of_nonneg_right h5 (abs_nonneg α)
      have h_comm : ‖v_H‖ * ‖(h : V)‖ / |α| = ‖v_H‖ / |α| * ‖(h : V)‖ := by ring
      rw [h_comm] at h_div
      exact h_div
    have h_ge : ‖v_H‖ / |α| ≤ ‖g'‖ := by
      by_cases h_vH0 : ‖v_H‖ = 0
      · have h_goal : ‖v_H‖ / |α| = 0 := by
          rw [h_vH0] <;> simp
        rw [h_goal]
        exact norm_nonneg g'
      · have h_pos : 0 < ‖v_H‖ := by
          exact lt_of_le_of_ne (by positivity) (Ne.symm h_vH0)
        have h7 : inner ℝ v_H (v_H' : V) = ‖v_H‖ ^ 2 := by
          have h71 : (v_H' : V) = v_H := by rfl
          rw [h71]
          have h72 : inner ℝ v_H v_H = ‖v_H‖ ^ 2 := by
            simpa [inner_self_eq_norm_sq_to_K] using rfl
          exact h72
        have h_eval : g' v_H' = -‖v_H‖ ^ 2 / α := by
          rw [h_g'_eq v_H', h7] <;> ring
        have h_bound : ‖g' v_H'‖ ≤ ‖g'‖ * ‖v_H'‖ := g'.le_opNorm v_H'
        have h' : ‖v_H'‖ = ‖v_H‖ := by rfl
        rw [h'] at h_bound
        rw [h_norm_abs (g' v_H'), h_eval] at h_bound
        have h8 : abs (-‖v_H‖ ^ 2 / α) = ‖v_H‖ ^ 2 / |α| := by
          rw [abs_div, abs_neg, abs_of_nonneg (show 0 ≤ ‖v_H‖ ^ 2 by positivity)] <;> ring
        rw [h8] at h_bound
        have h9 : ‖v_H‖ ^ 2 / |α| ≤ ‖g'‖ * ‖v_H‖ := h_bound
        have h10 : 0 < |α| := by positivity
        have h11 : ‖v_H‖ / |α| ≤ ‖g'‖ := by
          calc
            ‖v_H‖ / |α|
              = (‖v_H‖ ^ 2 / |α|) / ‖v_H‖ := by
                field_simp [h_pos.ne', h10.ne'] <;> ring
            _ ≤ (‖g'‖ * ‖v_H‖) / ‖v_H‖ := by gcongr
            _ = ‖g'‖ := by
              field_simp [h_pos.ne'] <;> ring
        exact h11
    exact le_antisymm h_le h_ge

  have h_main : ‖f'‖ ^ 2 = α ^ 2 * (1 + ‖g'‖ ^ 2) := by
    rw [←h_norm_f, h_pyth, h_c1, h_norm_g']
    have h_abs_sq : |α| ^ 2 = α ^ 2 := by
      simp [sq_abs] <;> ring
    have h_expand : (‖v_H‖ / |α|) ^ 2 = ‖v_H‖ ^ 2 / α ^ 2 := by
      rw [div_pow, h_abs_sq] <;> ring
    rw [h_expand] <;> field_simp [hα_ne] <;> ring
  have h_sqrt_eq : Real.sqrt (‖f'‖ ^ 2) = Real.sqrt (α ^ 2 * (1 + ‖g'‖ ^ 2)) := by
    rw [h_main]
  have h_sqrt1 : Real.sqrt (‖f'‖ ^ 2) = ‖f'‖ := by
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (show 0 ≤ ‖f'‖ by positivity)]
  have h_sqrt2 : Real.sqrt (α ^ 2 * (1 + ‖g'‖ ^ 2)) = |α| * Real.sqrt (1 + ‖g'‖ ^ 2) := by
    have h_nonneg : 0 ≤ α ^ 2 := by positivity
    rw [Real.sqrt_mul h_nonneg, Real.sqrt_sq_eq_abs] <;> ring
  have h_final : ‖f'‖ = |α| * Real.sqrt (1 + ‖g'‖ ^ 2) := by
    rw [h_sqrt1, h_sqrt2] at h_sqrt_eq
    exact h_sqrt_eq
  rw [h_final]
  field_simp [hα_ne] <;> ring

-- ============================================================================
-- Main lemma
-- ============================================================================

/-- **Implicit derivative identity for coarea formula.**
Given Φ(y) = projHCL(y) + f(y)·eLast is a local diffeomorphism via φ,
and g_t(v) = coordECL(φ.symm(unsplit(v,t))), then
  ‖fderiv f y‖ / |fderiv f y eLast| = √(1 + ‖fderiv g_t v‖²)
where y = φ.symm(unsplit(v,t)). -/
lemma implicit_derivative_identity
    (f : E (m + 1) → ℝ)
    (hf : ContDiff ℝ 1 f)
    (φ : OpenPartialHomeomorph (E (m + 1)) (E (m + 1)))
    (hφ_coe : (φ : E (m + 1) → E (m + 1)) = fun y => projHCL y + f y • (eLast : E (m + 1)))
    {V : Set (E (m + 1))}
    (hV_source : V ⊆ φ.source)
    (hV_reg : ∀ y ∈ V, (fderiv ℝ f y) (eLast : E (m + 1)) ≠ 0)
    (t : ℝ) (v : E m)
    (hvt : unsplit v t ∈ φ.target)
    (hyV : φ.symm (unsplit v t) ∈ V) :
    let y := φ.symm (unsplit v t)
    let g_t : E m → ℝ := fun w => coordECL (φ.symm (unsplit w t))
    ENNReal.ofReal (‖fderiv ℝ f y‖ / |(fderiv ℝ f y) (eLast : E (m + 1))|) =
    ENNReal.ofReal (Real.sqrt (1 + ‖fderiv ℝ g_t v‖ ^ 2)) := by
  set y : E (m + 1) := φ.symm (unsplit v t) with hy_def
  set z : E (m + 1) := unsplit v t with hz_def
  set f' : E (m + 1) →L[ℝ] ℝ := fderiv ℝ f y with hf'_def
  have h_reg : f' (eLast : E (m + 1)) ≠ 0 := hV_reg y hyV

  let DΦ_y : E (m + 1) →L[ℝ] E (m + 1) := coareaPhiFDeriv f'

  have h_c1 : ContDiff ℝ 1 f := hf
  have h_diff : Differentiable ℝ f := (contDiff_one_iff_fderiv.mp h_c1).1
  have h_cont : Continuous (fderiv ℝ f) := (contDiff_one_iff_fderiv.mp h_c1).2
  have h_der : ∀ᶠ w in nhds y, HasFDerivAt f (fderiv ℝ f w) w := by
    filter_upwards with w
    exact h_diff.differentiableAt.hasFDerivAt
  have h_fderiv_strict : HasStrictFDerivAt f f' y :=
    hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt h_der h_cont.continuousAt

  have hΦ_strict : HasStrictFDerivAt (φ : E (m + 1) → E (m + 1)) DΦ_y y := by
    have h_a : HasStrictFDerivAt (fun y => projHCL y) projHCL y := projHCL.hasStrictFDerivAt
    have h_b : HasStrictFDerivAt (fun y : E (m + 1) => f y • (eLast : E (m + 1)))
        (scaleE.comp f') y := by
      have h_smul : HasStrictFDerivAt (fun y : E (m + 1) => f y • (eLast : E (m + 1)))
          (f'.smulRight (eLast : E (m + 1))) y :=
        h_fderiv_strict.smul_const (eLast : E (m + 1))
      have h_eq : f'.smulRight (eLast : E (m + 1)) = scaleE.comp f' := by
        ext x <;> rfl
      rw [h_eq] at h_smul
      exact h_smul
    have h1 : HasStrictFDerivAt (fun y : E (m + 1) => projHCL y + f y • (eLast : E (m + 1))) DΦ_y y :=
      h_a.add h_b
    convert h1 using 1
    <;> funext x <;> rw [hφ_coe] <;> rfl

  have hdet : DΦ_y.det = f' (eLast : E (m + 1)) := det_coareaPhiFDeriv f'
  have hdet_ne : DΦ_y.det ≠ 0 := by rw [hdet] <;> exact h_reg
  let DΦ_equiv : E (m + 1) ≃L[ℝ] E (m + 1) :=
    DΦ_y.toContinuousLinearEquivOfDetNeZero hdet_ne
  let DΨ : E (m + 1) →L[ℝ] E (m + 1) := (DΦ_equiv.symm : E (m + 1) →L[ℝ] E (m + 1))

  have h_symm_deriv : HasStrictFDerivAt φ.symm DΨ z :=
    φ.hasStrictFDerivAt_symm hvt hΦ_strict

  let g_t : E m → ℝ := fun w => coordECL (φ.symm (unsplit w t))
  let g'_full : E m →L[ℝ] ℝ := coordECL.comp (DΨ.comp inclEm)

  have h_g_deriv : HasFDerivAt g_t g'_full v := by
    have h1 : HasFDerivAt φ.symm DΨ z := h_symm_deriv.hasFDerivAt
    have h2 : HasStrictFDerivAt (fun w : E m => unsplit w t) inclEm v := unsplit_deriv t v
    have h_inner : HasStrictFDerivAt (φ.symm ∘ fun w : E m => unsplit w t) (DΨ.comp inclEm) v :=
      h_symm_deriv.comp v h2
    have h_coord_at : HasStrictFDerivAt coordECL coordECL y := coordECL.hasStrictFDerivAt
    have h3 : HasFDerivAt (coordECL ∘ φ.symm ∘ fun w : E m => unsplit w t)
        (coordECL.comp (DΨ.comp inclEm)) v :=
      (h_coord_at.comp v h_inner).hasFDerivAt
    have h4 : HasFDerivAt g_t g'_full v := by
      convert h3
      <;> funext x <;> rfl
    exact h4
  have h_fderiv_eq : fderiv ℝ g_t v = g'_full := h_g_deriv.fderiv

  let H := HOrth (m := m)
  let g'_H : H →L[ℝ] ℝ :=
    { toFun := fun h : H => coordECL (DΨ (h : E (m + 1)))
      map_add' := by intro h1 h2; simp [map_add] <;> rfl
      map_smul' := by intro c h; simp [map_smul] <;> ring
      cont := by fun_prop }

  -- Key: DΨ(h) = h + g'_H(h)·eLast for h ∈ H
  have h_decomp : ∀ (h : H), DΨ (h : E (m + 1)) = (h : E (m + 1)) + g'_H h • (eLast : E (m + 1)) := by
    intro h
    set w : E (m + 1) := DΨ (h : E (m + 1)) with hw_def
    have h4 : DΦ_y w = (h : E (m + 1)) := DΦ_equiv.apply_symm_apply (h : E (m + 1))
    have h5 : projHCL w + f' w • (eLast : E (m + 1)) = (h : E (m + 1)) := h4
    have h6 : coordECL w = g'_H h := by rfl
    have h7 : f' w = 0 := by
      have h8 : coordECL (projHCL w + f' w • (eLast : E (m + 1))) = coordECL (h : E (m + 1)) := by rw [h5]
      have h9 : coordECL (h : E (m + 1)) = 0 := h.prop
      have h10 : coordECL (projHCL w + f' w • (eLast : E (m + 1))) = f' w := by
        simp [coordECL_projHCL, map_add, map_smul, coordECL_eLast] <;> ring
      rw [h10] at h8
      exact h8.trans h9
    have h11 : projHCL w = (h : E (m + 1)) := by
      rw [h7] at h5
      simpa using h5
    have h12 : w = projHCL w + coordECL w • (eLast : E (m + 1)) := by
      simp [projHCL] <;> abel
    rw [h12, h11, h6] <;> rfl

  -- Orthogonal relation: f'(h) + f'(eLast) * g'_H(h) = 0
  have h_orth_rel : ∀ (h : H), f' (h : E (m + 1)) + f' (eLast : E (m + 1)) * g'_H h = 0 := by
    intro h
    set w : E (m + 1) := DΨ (h : E (m + 1)) with hw_def
    have h4 : DΦ_y w = (h : E (m + 1)) := DΦ_equiv.apply_symm_apply (h : E (m + 1))
    have h5 : projHCL w + f' w • (eLast : E (m + 1)) = (h : E (m + 1)) := h4
    have h7 : f' w = 0 := by
      have h8 : coordECL (projHCL w + f' w • (eLast : E (m + 1))) = coordECL (h : E (m + 1)) := by rw [h5]
      have h9 : coordECL (h : E (m + 1)) = 0 := h.prop
      have h10 : coordECL (projHCL w + f' w • (eLast : E (m + 1))) = f' w := by
        simp [coordECL_projHCL, map_add, map_smul, coordECL_eLast] <;> ring
      rw [h10] at h8
      exact h8.trans h9
    have h10 : w = (h : E (m + 1)) + g'_H h • (eLast : E (m + 1)) := h_decomp h
    rw [h10] at h7
    have h11 : f' ((h : E (m + 1)) + g'_H h • (eLast : E (m + 1))) = 0 := h7
    have h12 : f' ((h : E (m + 1)) + g'_H h • (eLast : E (m + 1))) =
        f' (h : E (m + 1)) + f' (eLast : E (m + 1)) * g'_H h := by
      simp [map_add, map_smul] <;> ring
    rw [h12] at h11
    exact h11

  -- Operator norm equality: ‖g'_full‖ = ‖g'_H‖
  have h_norm_eq : ‖g'_full‖ = ‖g'_H‖ := by
    have h_le1 : ‖g'_full‖ ≤ ‖g'_H‖ := by
      apply g'_full.opNorm_le_bound (by positivity)
      intro v
      let h : H := ⟨inclEm v, by
        have h_in : coordECL (inclEm v) = 0 := by
          simp [HOrth, coordECL, inclEm, GraphAreaFormula.F_lin_apply_last] <;> norm_num
        exact h_in⟩
      have h1 : g'_full v = g'_H h := by rfl
      rw [h1]
      have h2 : ‖g'_H h‖ ≤ ‖g'_H‖ * ‖(h : E (m + 1))‖ := g'_H.le_opNorm h
      have h3 : ‖(h : E (m + 1))‖ = ‖v‖ := inclEm_isometry v
      rw [h3] at h2
      exact h2
    have h_le2 : ‖g'_H‖ ≤ ‖g'_full‖ := by
      apply g'_H.opNorm_le_bound (by positivity)
      intro h
      let v : E m := GraphAreaFormula.proj (h : E (m + 1))
      have hv : inclEm v = (h : E (m + 1)) := by
        ext i
        by_cases h2 : i.val < m
        · let j : Fin m := ⟨i.val, h2⟩
          have hj : i = Fin.castSucc j := by apply Fin.ext; simp [j, h2] <;> omega
          rw [hj]
          have h6 : (inclEm v) (Fin.castSucc j) = v j :=
            GraphAreaFormula.F_lin_apply_castSucc (0 : E m →L[ℝ] ℝ) v j
          have h7 : v j = (h : E (m + 1)) (Fin.castSucc j) :=
            GraphAreaFormula.proj_apply (h : E (m + 1)) j
          exact Eq.trans h6 h7
        · have hlast : i = Fin.last m := by apply Fin.ext; simp [h2] <;> omega
          rw [hlast]
          have h4 : coordECL (h : E (m + 1)) = 0 := h.prop
          have h5 : (inclEm v) (Fin.last m) = 0 :=
            GraphAreaFormula.F_lin_apply_last (0 : E m →L[ℝ] ℝ) v
          have h6 : (h : E (m + 1)) (Fin.last m) = coordECL (h : E (m + 1)) := by
            rfl
          rw [h5, h6, h4]
      have h1 : g'_H h = g'_full v := by
        simpa [g'_full, g'_H, hv] using rfl
      rw [h1]
      have h2 : ‖g'_full v‖ ≤ ‖g'_full‖ * ‖v‖ := g'_full.le_opNorm v
      have h3 : ‖v‖ = ‖(h : E (m + 1))‖ := by
        have h4 : ‖inclEm v‖ = ‖v‖ := inclEm_isometry v
        have h5 : ‖inclEm v‖ = ‖(h : E (m + 1))‖ := by rw [hv]
        rw [h5] at h4
        exact h4.symm
      rw [h3] at h2
      exact h2
    exact le_antisymm h_le1 h_le2

  have hH_iff : ∀ (x : E (m + 1)), x ∈ H ↔ inner ℝ x (eLast : E (m + 1)) = 0 := by
    intro x
    have h1 : x ∈ H ↔ coordECL x = 0 := by simp [H, HOrth]
    rw [h1]
    have h2 : inner ℝ x (eLast : E (m + 1)) = coordECL x := inner_eq_coordECL x
    rw [h2]

  have h_alg : ‖f'‖ / |f' (eLast : E (m + 1))| = Real.sqrt (1 + ‖g'_H‖ ^ 2) :=
    algebraic_identity (eLast : E (m + 1)) norm_eLast H hH_iff f' h_reg g'_H h_orth_rel

  dsimp only
  rw [h_fderiv_eq, h_norm_eq]
  exact congr_arg (fun x : ℝ => ENNReal.ofReal x) h_alg

end Geometry
