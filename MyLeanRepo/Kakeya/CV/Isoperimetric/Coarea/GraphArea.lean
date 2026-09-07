import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Tactic

/-!
# Graph Area Formula — Affine Case and General Graph Infrastructure

This module provides:

## Definitions
- `proj p`: projection from `E(m+1)` to `E(m)` dropping the last coordinate.
- `graph g`: subset `{p ∈ E(m+1) | p_{last} = g(proj p)}`.
- `cylinder A`: subset `{p ∈ E(m+1) | proj p ∈ A}`.
- `graphMap g y`: the point `(y, g(y)) ∈ E(m+1)`.

## Main theorems
For `a : E(m) →L[ℝ] ℝ`, `b : ℝ`, and measurable `A : Set E(m)`:
- `graph_area_linear`: `μHE[m](graph(a·) ∩ cylinder A) = √(1 + ‖a‖²) · volume A`
- `graph_area_affine`: `μHE[m](graph(a· + b) ∩ cylinder A) = √(1 + ‖a‖²) · volume A`

## Supporting infrastructure for smooth extension
- `graph_cylinder_eq_image`: `graph g ∩ cylinder A = graphMap g '' A`
- `graphMap_norm_sq`: `‖graphMap g y - graphMap g z‖² = ‖y-z‖² + (g y - g z)²`
- `graphMap_injective`, `graphMap_proj`, `graphMap_apply_castSucc`, `graphMap_apply_last`

## Proof route for the affine formula
1. Embed `E(m)` as a graph subspace `H` of `E(m+1)` via `F_lin`.
2. Construct an isometry `L_iso` between `E(m)` and `H` (using ONB).
3. The change-of-basis map `T = F_equiv ∘ L_iso.symm` satisfies `T*T = I + uu^T`,
   so `|det T| = √(1 + ‖a‖²)` by the matrix determinant lemma.
4. Transfer `μHE[m]` on the graph to `volume` on `E(m)` via the isometry,
   then apply the linear equiv volume scaling formula.

All work is in `EuclideanSpace ℝ (Fin (m+1))` with true L2 norm.
-/

open MeasureTheory Metric Set ENNReal LinearMap
open scoped MeasureTheory

namespace GraphAreaFormula

variable {m : ℕ} [Nonempty (Fin m)]

-- ============================================================================
-- Riesz vector
-- ============================================================================

section Riesz

variable (a : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ)

noncomputable def rieszVector : EuclideanSpace ℝ (Fin m) :=
  (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin m))).symm a

lemma riesz_eq (v : EuclideanSpace ℝ (Fin m)) :
    a v = inner ℝ (rieszVector a) v := by
  have h : inner ℝ (rieszVector a) v = a v :=
    InnerProductSpace.toDual_symm_apply (x := v) (y := a)
  exact h.symm

lemma riesz_norm : ‖rieszVector a‖ = ‖a‖ := by
  exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin m))).symm.norm_map a

end Riesz

-- ============================================================================
-- Determinant lemma
-- ============================================================================

section Determinant

variable (a : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ)

noncomputable def rankOneMap :
    (EuclideanSpace ℝ (Fin m)) →ₗ[ℝ] (EuclideanSpace ℝ (Fin m)) :=
  { toFun := fun v => a v • rieszVector a
    map_add' := by
      intro v w
      have h : a (v + w) = a v + a w := a.map_add v w
      rw [h, add_smul]
    map_smul' := by
      intro c v
      have h : a (c • v) = c • a v := a.map_smul c v
      rw [h]
      have h2 : (c • a v) • rieszVector a = c • (a v • rieszVector a) := by
        have h3 : c • a v = c * a v := by simp
        rw [h3, smul_smul]
      exact h2 }

lemma rankOneMap_apply (v : EuclideanSpace ℝ (Fin m)) :
    rankOneMap a v = inner ℝ (rieszVector a) v • rieszVector a := by
  have h_def : rankOneMap a v = a v • rieszVector a := by rfl
  have h : a v = inner ℝ (rieszVector a) v := riesz_eq a v
  rw [h_def, h]

lemma det_rank_one_update :
    LinearMap.det ((LinearMap.id : (EuclideanSpace ℝ (Fin m)) →ₗ[ℝ] (EuclideanSpace ℝ (Fin m))) + rankOneMap a) =
      1 + ‖rieszVector a‖ ^ 2 := by
  let b := EuclideanSpace.basisFun (Fin m) ℝ
  let bb := b.toBasis
  let u := rieszVector a
  let u' : Fin m → ℝ := fun i => u i
  have h_mat : ∀ (i j : Fin m),
      (LinearMap.toMatrix bb bb (rankOneMap a)) i j = u i * u j := by
    intro i j
    have h1 : (LinearMap.toMatrix bb bb (rankOneMap a)) i j =
        (bb.repr (rankOneMap a (bb j))) i := by
      simp [LinearMap.toMatrix_apply] <;> rfl
    rw [h1]
    have h2 : rankOneMap a (bb j) = a (bb j) • u := by rfl
    rw [h2]
    have h3 : (bb.repr (a (bb j) • u)) i = a (bb j) * (bb.repr u) i := by
      simp [map_smul] <;> rfl
    rw [h3]
    have h4 : (bb.repr u) i = u i := EuclideanSpace.basisFun_repr (Fin m) ℝ u i
    rw [h4]
    have h5 : a (bb j) = inner ℝ u (bb j) := riesz_eq a (bb j)
    rw [h5]
    have h6 : inner ℝ u (bb j) = inner ℝ (bb j) u := by
      exact (real_inner_comm u (bb j)).symm
    rw [h6]
    have h7 : inner ℝ (bb j) u = u j := EuclideanSpace.basisFun_inner (Fin m) ℝ u j
    rw [h7] <;> ring
  have h1 : (LinearMap.toMatrix bb bb (rankOneMap a)) =
      Matrix.replicateCol (ι := Fin 1) u' * Matrix.replicateRow (ι := Fin 1) u' := by
    ext i j
    have h_rep : (Matrix.replicateCol (ι := Fin 1) u' * Matrix.replicateRow (ι := Fin 1) u') i j = u i * u j := by
      simp [Matrix.replicateCol, Matrix.replicateRow, Matrix.mul_apply] <;> ring
    rw [h_rep]
    exact h_mat i j
  have h_add : LinearMap.toMatrix bb bb ((LinearMap.id : (EuclideanSpace ℝ (Fin m)) →ₗ[ℝ] (EuclideanSpace ℝ (Fin m))) + rankOneMap a) =
      LinearMap.toMatrix bb bb (LinearMap.id : (EuclideanSpace ℝ (Fin m)) →ₗ[ℝ] (EuclideanSpace ℝ (Fin m))) + LinearMap.toMatrix bb bb (rankOneMap a) := by
    simp
  have h_id : LinearMap.toMatrix bb bb (LinearMap.id : (EuclideanSpace ℝ (Fin m)) →ₗ[ℝ] (EuclideanSpace ℝ (Fin m))) = (1 : Matrix (Fin m) (Fin m) ℝ) := by
    exact LinearMap.toMatrix_id _
  have h_mat2 : LinearMap.toMatrix bb bb ((LinearMap.id : (EuclideanSpace ℝ (Fin m)) →ₗ[ℝ] (EuclideanSpace ℝ (Fin m))) + rankOneMap a) =
      (1 : Matrix (Fin m) (Fin m) ℝ) + Matrix.replicateCol (ι := Fin 1) u' * Matrix.replicateRow (ι := Fin 1) u' := by
    rw [h_add, h_id, h1]
  have h_main : LinearMap.det ((LinearMap.id : (EuclideanSpace ℝ (Fin m)) →ₗ[ℝ] (EuclideanSpace ℝ (Fin m))) + rankOneMap a) =
      (LinearMap.toMatrix bb bb ((LinearMap.id : (EuclideanSpace ℝ (Fin m)) →ₗ[ℝ] (EuclideanSpace ℝ (Fin m))) + rankOneMap a)).det := by
    rw [← LinearMap.det_toMatrix bb]
  rw [h_main, h_mat2]
  have h_det : (1 + Matrix.replicateCol (ι := Fin 1) u' * Matrix.replicateRow (ι := Fin 1) u').det = 1 + u' ⬝ᵥ u' :=
    Matrix.det_one_add_replicateCol_mul_replicateRow (ι := Fin 1) (u := u') (v := u')
  rw [h_det]
  have h7 : inner ℝ u u = ∑ i : Fin m, u i * u i := by
    rw [PiLp.inner_apply]
    have h_inner : ∑ i : Fin m, inner ℝ (u i) (u i) = ∑ i : Fin m, (u i) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      have h : inner ℝ (u i) (u i) = (u i) * (u i) := by
        simp [inner_self_eq_norm_sq_to_K] <;> ring
      rw [h] <;> ring
    rw [h_inner]
    have h_eq : ∑ i : Fin m, (u i) ^ 2 = ∑ i : Fin m, u i * u i := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [h_eq]
  have h8 : inner ℝ u u = ‖u‖ ^ 2 := by
    exact inner_self_eq_norm_sq_to_K u
  have h_norm2 : ‖u‖ ^ 2 = ∑ i : Fin m, u i * u i := by
    exact Eq.trans h8.symm h7
  have h_dot : (u' ⬝ᵥ u') = ∑ i : Fin m, u' i * u' i := by
    rfl
  have h9 : ∑ i : Fin m, u' i * u' i = ∑ i : Fin m, u i * u i := by
    apply Finset.sum_congr rfl
    intro i _
    <;> rfl
  have h_goal : 1 + (u' ⬝ᵥ u') = 1 + ‖u‖ ^ 2 := by
    rw [h_dot, h9, ←h_norm2]
  exact h_goal

lemma det_adjoint_eq_det {T : (EuclideanSpace ℝ (Fin m)) →ₗ[ℝ] (EuclideanSpace ℝ (Fin m))} :
    LinearMap.det T.adjoint = LinearMap.det T := by
  let b := EuclideanSpace.basisFun (Fin m) ℝ
  let bb := b.toBasis
  let A := LinearMap.toMatrix bb bb T
  have h_real : A.conjTranspose = A.transpose := by
    ext i j <;> simp [Matrix.conjTranspose_apply] <;> rfl
  have h_orig : (Matrix.toLin bb bb A.conjTranspose) = (Matrix.toLin bb bb A).adjoint :=
    Matrix.toLin_conjTranspose b b A
  have h' : (Matrix.toLin bb bb A).adjoint = Matrix.toLin bb bb A.transpose := by
    rw [h_real] at h_orig
    exact h_orig.symm
  have hT : T = Matrix.toLin bb bb A := by
    exact (Matrix.toLin_toMatrix bb bb T).symm
  have h_eq : T.adjoint = Matrix.toLin bb bb A.transpose := by
    rw [hT]
    exact h'
  have h2 : LinearMap.toMatrix bb bb T.adjoint = A.transpose := by
    rw [h_eq, LinearMap.toMatrix_toLin]
  rw [← LinearMap.det_toMatrix bb, h2, Matrix.det_transpose]
  <;> rw [← LinearMap.det_toMatrix bb T]

lemma det_squared_of_starStar {T : (EuclideanSpace ℝ (Fin m)) ≃L[ℝ] (EuclideanSpace ℝ (Fin m))}
    (h : T.toLinearMap.adjoint.comp T.toLinearMap =
        (LinearMap.id : (EuclideanSpace ℝ (Fin m)) →ₗ[ℝ] (EuclideanSpace ℝ (Fin m))) + rankOneMap a) :
    (LinearMap.det T.toLinearMap) ^ 2 = 1 + ‖rieszVector a‖ ^ 2 := by
  have h1 : LinearMap.det (T.toLinearMap.adjoint.comp T.toLinearMap) =
      LinearMap.det T.toLinearMap.adjoint * LinearMap.det T.toLinearMap := by
    rw [LinearMap.det_comp]
  have h_adj_det : LinearMap.det T.toLinearMap.adjoint = LinearMap.det T.toLinearMap :=
    det_adjoint_eq_det
  have h2 : LinearMap.det (T.toLinearMap.adjoint.comp T.toLinearMap) =
      (LinearMap.det T.toLinearMap) ^ 2 := by
    rw [h1, h_adj_det] <;> ring
  have h3 : LinearMap.det (T.toLinearMap.adjoint.comp T.toLinearMap) =
      LinearMap.det ((LinearMap.id : (EuclideanSpace ℝ (Fin m)) →ₗ[ℝ] (EuclideanSpace ℝ (Fin m))) + rankOneMap a) := by
    rw [h]
  have h4 : LinearMap.det ((LinearMap.id : (EuclideanSpace ℝ (Fin m)) →ₗ[ℝ] (EuclideanSpace ℝ (Fin m))) + rankOneMap a) =
      1 + ‖rieszVector a‖ ^ 2 := det_rank_one_update a
  have h5 : (LinearMap.det T.toLinearMap) ^ 2 =
      LinearMap.det (T.toLinearMap.adjoint.comp T.toLinearMap) := h2.symm
  rw [h5, h3, h4]

end Determinant

-- ============================================================================
-- Graph embedding
-- ============================================================================

section Graph

variable (a : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ)
variable (b : ℝ)

/-- Direct graph embedding v ↦ (v, a(v)) in E(m+1). -/
noncomputable def F_lin :
    (EuclideanSpace ℝ (Fin m)) →ₗ[ℝ] (EuclideanSpace ℝ (Fin (m + 1))) :=
  { toFun := fun v =>
      (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
        (fun i : Fin (m + 1) => if h : i.val < m then v ⟨i.val, h⟩ else a v)
    map_add' := by
      intro v w
      ext i
      by_cases h : i.val < m
      · simp [EuclideanSpace.equiv, h] <;> rfl
      · simp [EuclideanSpace.equiv, h, a.map_add] <;> ring
    map_smul' := by
      intro c v
      ext i
      by_cases h : i.val < m
      · simp [EuclideanSpace.equiv, h] <;> rfl
      · simp [EuclideanSpace.equiv, h, a.map_smul] <;> ring }

noncomputable def proj (p : EuclideanSpace ℝ (Fin (m + 1))) : EuclideanSpace ℝ (Fin m) :=
  (EuclideanSpace.equiv (Fin m) ℝ).symm (fun i : Fin m => p (Fin.castSucc i))

lemma proj_apply (p : EuclideanSpace ℝ (Fin (m + 1))) (i : Fin m) :
    (proj p) i = p (Fin.castSucc i) := by
  simp [proj, EuclideanSpace.equiv] <;> rfl

lemma continuous_proj :
    Continuous (proj : EuclideanSpace ℝ (Fin (m + 1)) → EuclideanSpace ℝ (Fin m)) := by
  have h1 : Continuous (fun (p : EuclideanSpace ℝ (Fin (m + 1))) =>
      (fun i : Fin m => p (Fin.castSucc i))) := by fun_prop
  exact (EuclideanSpace.equiv (Fin m) ℝ).symm.continuous.comp h1

lemma F_lin_apply_castSucc (v : EuclideanSpace ℝ (Fin m)) (i : Fin m) :
    (F_lin a v) (Fin.castSucc i) = v i := by
  simp [F_lin, EuclideanSpace.equiv]
  <;> split_ifs <;> omega

lemma proj_F_lin (v : EuclideanSpace ℝ (Fin m)) : proj (F_lin a v) = v := by
  ext i
  rw [proj_apply, F_lin_apply_castSucc]

lemma F_lin_apply_last (v : EuclideanSpace ℝ (Fin m)) :
    (F_lin a v) (Fin.last m) = a v := by
  simp [F_lin, EuclideanSpace.equiv]
  <;> split_ifs <;> omega

lemma F_lin_injective : Function.Injective (F_lin a) := by
  intro v w h
  have h' : ∀ (i : Fin m), v i = w i := by
    intro i
    have h1 : (F_lin a v) (Fin.castSucc i) = (F_lin a w) (Fin.castSucc i) := by rw [h]
    rw [F_lin_apply_castSucc a v i, F_lin_apply_castSucc a w i] at h1
    exact h1
  ext i
  exact h' i

noncomputable def graphSubspace : Submodule ℝ (EuclideanSpace ℝ (Fin (m + 1))) :=
  (F_lin a).range

noncomputable def F_equiv :
    (EuclideanSpace ℝ (Fin m)) ≃ₗ[ℝ] (graphSubspace a) :=
  { toFun := fun v => ⟨F_lin a v, by exact ⟨v, rfl⟩⟩
    invFun := fun p => proj (p : EuclideanSpace ℝ (Fin (m + 1)))
    left_inv := by
      intro v
      exact proj_F_lin a v
    right_inv := by
      intro p
      have h_range : ∃ (v : EuclideanSpace ℝ (Fin m)), F_lin a v = (p : EuclideanSpace ℝ (Fin (m + 1))) := p.prop
      rcases h_range with ⟨v, hv⟩
      have h_v : proj (p : EuclideanSpace ℝ (Fin (m + 1))) = v := by
        rw [← hv]
        exact proj_F_lin a v
      apply Subtype.ext
      calc (F_lin a (proj (p : EuclideanSpace ℝ (Fin (m + 1)))))
          = F_lin a v := by rw [h_v]
        _ = (p : EuclideanSpace ℝ (Fin (m + 1))) := hv
    map_add' := by
      intro v w
      apply Subtype.ext
      exact (F_lin a).map_add v w
    map_smul' := by
      intro c v
      apply Subtype.ext
      exact (F_lin a).map_smul c v }

lemma finrank_H : Module.finrank ℝ (graphSubspace a) = m := by
  have h : Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) = Module.finrank ℝ (graphSubspace a) :=
    (F_equiv a).finrank_eq
  have h' : Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) = m := by simp
  have h'' : Module.finrank ℝ (graphSubspace a) = Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) := h.symm
  rw [h'', h']

noncomputable def L_iso :
    (EuclideanSpace ℝ (Fin m)) ≃ₗᵢ[ℝ] (graphSubspace a) := by
  let bE := EuclideanSpace.basisFun (Fin m) ℝ
  let bH := stdOrthonormalBasis ℝ (graphSubspace a)
  have hfr : Module.finrank ℝ (graphSubspace a) = m := finrank_H a
  let idx_equiv : Fin m ≃ Fin (Module.finrank ℝ (graphSubspace a)) := by
    rw [hfr] <;> exact Equiv.refl _
  exact bE.equiv bH idx_equiv

noncomputable def T :
    (EuclideanSpace ℝ (Fin m)) ≃L[ℝ] (EuclideanSpace ℝ (Fin m)) :=
  (F_equiv a).toContinuousLinearEquiv.trans (L_iso a).symm.toContinuousLinearEquiv

lemma inner_F_lin (v w : EuclideanSpace ℝ (Fin m)) :
    inner ℝ (F_lin a v) (F_lin a w) = inner ℝ v w + a v * a w := by
  have h_sum1 : inner ℝ (F_lin a v) (F_lin a w) =
      ∑ i : Fin (m + 1), (F_lin a v i) * (F_lin a w i) := by
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro i _
    have h_real : inner ℝ ((F_lin a v) i) ((F_lin a w) i) = (F_lin a v i) * (F_lin a w i) := by
      simp <;> ring
    exact h_real
  rw [h_sum1]
  have h_split : ∑ i : Fin (m + 1), (F_lin a v i) * (F_lin a w i) =
      (∑ j : Fin m, (v j) * (w j)) + a v * a w := by
    rw [Fin.sum_univ_castSucc]
    have h1 : ∀ (j : Fin m), (F_lin a v (Fin.castSucc j)) * (F_lin a w (Fin.castSucc j)) =
        (v j) * (w j) := by
      intro j
      rw [F_lin_apply_castSucc a v j, F_lin_apply_castSucc a w j]
    have h2 : (F_lin a v (Fin.last m)) * (F_lin a w (Fin.last m)) = a v * a w := by
      rw [F_lin_apply_last a v, F_lin_apply_last a w]
    rw [h2]
    apply congr_arg (fun x => x + a v * a w)
    apply Finset.sum_congr rfl
    intro j _
    exact h1 j
  rw [h_split]
  have h_inner : inner ℝ v w = ∑ j : Fin m, (v j) * (w j) := by
    rw [PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro j _
    have h_real : inner ℝ (v j) (w j) = (v j) * (w j) := by
      simp <;> ring
    exact h_real
  rw [h_inner] <;> ring

lemma inner_T (v w : EuclideanSpace ℝ (Fin m)) :
    inner ℝ ((T a) v) ((T a) w) = inner ℝ v w + a v * a w := by
  have h_isom : ∀ (x y : graphSubspace a),
      inner ℝ ((L_iso a).symm x) ((L_iso a).symm y) = inner ℝ x y := by
    intro x y
    exact (L_iso a).symm.inner_map_map x y
  have h1 : inner ℝ ((T a) v) ((T a) w) =
      inner ℝ ((F_equiv a) v) ((F_equiv a) w) := by
    exact h_isom _ _
  rw [h1]
  have h2 : inner ℝ ((F_equiv a) v) ((F_equiv a) w) =
      inner ℝ (F_lin a v) (F_lin a w) := by rfl
  rw [h2, inner_F_lin a]

lemma T_star_T :
    (T a).toLinearMap.adjoint.comp (T a).toLinearMap =
      (LinearMap.id : (EuclideanSpace ℝ (Fin m)) →ₗ[ℝ] (EuclideanSpace ℝ (Fin m))) + rankOneMap a := by
  set X := (T a).toLinearMap.adjoint.comp (T a).toLinearMap with hX
  set Y := (LinearMap.id : (EuclideanSpace ℝ (Fin m)) →ₗ[ℝ] (EuclideanSpace ℝ (Fin m))) + rankOneMap a with hY
  have h_main : ∀ (v w : EuclideanSpace ℝ (Fin m)),
      inner ℝ (X v) w = inner ℝ (Y v) w := by
    intro v w
    have h_left : inner ℝ (X v) w = inner ℝ v w + a v * a w := by
      have h5 : inner ℝ (X v) w = inner ℝ ((T a) v) ((T a) w) := by
        simpa [hX, LinearMap.comp_apply, LinearMap.adjoint_inner_left] using rfl
      rw [h5, inner_T a]
    have h_right : inner ℝ (Y v) w = inner ℝ v w + a v * a w := by
      have h_rank : Y v = v + (inner ℝ (rieszVector a) v) • (rieszVector a) := by
        simpa [hY, rankOneMap_apply] using rfl
      rw [h_rank]
      have h_calc : inner ℝ (v + (inner ℝ (rieszVector a) v) • (rieszVector a)) w =
          inner ℝ v w + (inner ℝ (rieszVector a) v) * (inner ℝ (rieszVector a) w) := by
        have h1 : inner ℝ (v + (inner ℝ (rieszVector a) v) • (rieszVector a)) w =
            inner ℝ v w + inner ℝ ((inner ℝ (rieszVector a) v) • (rieszVector a)) w := by
            exact inner_add_left _ _ _
        rw [h1]
        have h2 : inner ℝ ((inner ℝ (rieszVector a) v) • (rieszVector a)) w =
            (inner ℝ (rieszVector a) v) * inner ℝ (rieszVector a) w := by
            exact inner_smul_left _ _ _
        rw [h2] <;> ring
      rw [h_calc]
      have h6 : inner ℝ (rieszVector a) v = a v := (riesz_eq a v).symm
      have h7 : inner ℝ (rieszVector a) w = a w := (riesz_eq a w).symm
      rw [h6, h7] <;> ring
    rw [h_left, h_right]
  apply LinearMap.ext
  intro v
  have h8 : ∀ (w : EuclideanSpace ℝ (Fin m)), inner ℝ (X v) w = inner ℝ (Y v) w := h_main v
  have h9 : ∀ (w : EuclideanSpace ℝ (Fin m)), inner ℝ w (X v) = inner ℝ w (Y v) := by
    intro w
    have h10 : inner ℝ (X v) w = inner ℝ (Y v) w := h8 w
    have h11 : inner ℝ w (X v) = inner ℝ (X v) w := by
      exact (real_inner_comm w (X v)).symm
    have h12 : inner ℝ w (Y v) = inner ℝ (Y v) w := by
      exact (real_inner_comm w (Y v)).symm
    rw [h11, h12, h10]
  have h_iff : X v = Y v ↔ ∀ (w : EuclideanSpace ℝ (Fin m)), inner ℝ w (X v) = inner ℝ w (Y v) :=
    ext_iff_inner_left (𝕜 := ℝ)
  exact h_iff.mpr h9

lemma abs_det_T :
    |LinearMap.det (T a).toLinearMap| = Real.sqrt (1 + ‖a‖ ^ 2) := by
  have h1 : (LinearMap.det (T a).toLinearMap) ^ 2 = 1 + ‖rieszVector a‖ ^ 2 :=
    det_squared_of_starStar (a := a) (T_star_T a)
  have h2 : ‖rieszVector a‖ = ‖a‖ := riesz_norm a
  rw [h2] at h1
  have h4 : |LinearMap.det (T a).toLinearMap| =
      Real.sqrt ((LinearMap.det (T a).toLinearMap) ^ 2) := by
    rw [Real.sqrt_sq_eq_abs]
  rw [h4, h1]
  <;> rw [Real.sqrt_eq_cases] <;> norm_num <;> linarith

def graph (g : (EuclideanSpace ℝ (Fin m)) → ℝ) : Set (EuclideanSpace ℝ (Fin (m + 1))) :=
  {p : EuclideanSpace ℝ (Fin (m + 1)) | p (Fin.last m) = g (proj p)}

def cylinder (A : Set (EuclideanSpace ℝ (Fin m))) : Set (EuclideanSpace ℝ (Fin (m + 1))) :=
  {p : EuclideanSpace ℝ (Fin (m + 1)) | proj p ∈ A}

/-- General graph map: sends `y ∈ E(m)` to the point `(y, g(y)) ∈ E(m+1)`. -/
noncomputable def graphMap (g : (EuclideanSpace ℝ (Fin m)) → ℝ)
    (y : EuclideanSpace ℝ (Fin m)) : EuclideanSpace ℝ (Fin (m + 1)) :=
  (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
    fun i : Fin (m + 1) => if h : i.val < m then y ⟨i.val, h⟩ else g y

lemma graphMap_apply_castSucc (g : (EuclideanSpace ℝ (Fin m)) → ℝ)
    (y : EuclideanSpace ℝ (Fin m)) (i : Fin m) :
    (graphMap g y) (Fin.castSucc i) = y i := by
  simp [graphMap, EuclideanSpace.equiv] <;> split_ifs <;> omega

lemma graphMap_apply_last (g : (EuclideanSpace ℝ (Fin m)) → ℝ)
    (y : EuclideanSpace ℝ (Fin m)) :
    (graphMap g y) (Fin.last m) = g y := by
  simp [graphMap, EuclideanSpace.equiv] <;> split_ifs <;> omega

lemma graphMap_proj (g : (EuclideanSpace ℝ (Fin m)) → ℝ)
    (y : EuclideanSpace ℝ (Fin m)) :
    proj (graphMap g y) = y := by
  ext i
  rw [proj_apply, graphMap_apply_castSucc]

lemma graphMap_injective (g : (EuclideanSpace ℝ (Fin m)) → ℝ) :
    Function.Injective (graphMap g) := by
  intro y z h
  have h3 : proj (graphMap g y) = proj (graphMap g z) := by rw [h]
  rw [graphMap_proj g y, graphMap_proj g z] at h3
  exact h3

/-- Norm squared identity for graph map differences. -/
lemma graphMap_norm_sq (g : (EuclideanSpace ℝ (Fin m)) → ℝ)
    (y z : EuclideanSpace ℝ (Fin m)) :
    ‖graphMap g y - graphMap g z‖ ^ 2 = ‖y - z‖ ^ 2 + (g y - g z) ^ 2 := by
  have h1 : ‖graphMap g y - graphMap g z‖ ^ 2 =
      ∑ i : Fin (m + 1), ((graphMap g y - graphMap g z) i) ^ 2 :=
    EuclideanSpace.real_norm_sq_eq (graphMap g y - graphMap g z)
  rw [h1]
  have h2 : ∑ i : Fin (m + 1), ((graphMap g y - graphMap g z) i) ^ 2 =
      (∑ j : Fin m, (y j - z j) ^ 2) + (g y - g z) ^ 2 := by
    rw [Fin.sum_univ_castSucc]
    have h3 : ∀ (j : Fin m), j ∈ Finset.univ →
        (graphMap g y - graphMap g z) (Fin.castSucc j) ^ 2 = (y j - z j) ^ 2 := by
      intro j _
      have h31 : (graphMap g y - graphMap g z) (Fin.castSucc j) = y j - z j := by
        simp [graphMap_apply_castSucc]
      rw [h31]
    have h4 : (graphMap g y - graphMap g z) (Fin.last m) ^ 2 = (g y - g z) ^ 2 := by
      have h41 : (graphMap g y - graphMap g z) (Fin.last m) = g y - g z := by
        simp [graphMap_apply_last]
      rw [h41]
    rw [Finset.sum_congr rfl h3, h4]
  rw [h2]
  have h5 : ‖y - z‖ ^ 2 = ∑ j : Fin m, (y j - z j) ^ 2 :=
    EuclideanSpace.real_norm_sq_eq (y - z)
  rw [h5] <;> ring

/-- The intersection `graph g ∩ cylinder A` equals the image of `A` under `graphMap g`. -/
lemma graph_cylinder_eq_image (g : (EuclideanSpace ℝ (Fin m)) → ℝ)
    (A : Set (EuclideanSpace ℝ (Fin m))) :
    graph g ∩ cylinder A = graphMap g '' A := by
  ext z
  simp only [graph, cylinder, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨proj z, h2, ?_⟩
    ext j
    by_cases h : j.val < m
    · let i : Fin m := ⟨j.val, h⟩
      have hj : j = Fin.castSucc i := by
        apply Fin.ext <;> simp [i, Fin.castSucc]
      rw [hj]
      rw [graphMap_apply_castSucc, proj_apply]
    · have hlast : j = Fin.last m := by
        apply Fin.ext
        have h' : j.val = m := by omega
        exact h'
      rw [hlast]
      rw [graphMap_apply_last]
      exact h1.symm
  · rintro ⟨y, hy, rfl⟩
    constructor
    · rw [graphMap_apply_last, graphMap_proj]
    · rw [graphMap_proj] <;> exact hy

theorem graph_area_linear (A : Set (EuclideanSpace ℝ (Fin m))) (hA : MeasurableSet A) :
    μHE[m] (graph (fun x : EuclideanSpace ℝ (Fin m) => a x) ∩ cylinder A) =
      ENNReal.ofReal (Real.sqrt (1 + ‖a‖ ^ 2)) * volume A := by
  let H := graphSubspace a
  let F_eq := F_equiv a
  let L := L_iso a
  let T_map := T a

  have h_set1 : graph (fun x : EuclideanSpace ℝ (Fin m) => a x) ∩ cylinder A = (F_lin a) '' A := by
    ext z
    simp only [graph, cylinder, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨proj z, h2, ?_⟩
      ext j
      by_cases h : j.val < m
      · let i : Fin m := ⟨j.val, h⟩
        have hj : j = Fin.castSucc i := by
          apply Fin.ext <;> simp [i, Fin.castSucc]
        rw [hj]
        rw [F_lin_apply_castSucc, proj_apply]
      · have hlast : j = Fin.last m := by
          apply Fin.ext
          have h' : j.val = m := by omega
          exact h'
        rw [hlast]
        rw [F_lin_apply_last]
        exact h1.symm
    · rintro ⟨v, hv, rfl⟩
      constructor
      · rw [F_lin_apply_last, proj_F_lin]
      · rw [proj_F_lin] <;> exact hv
  rw [h_set1]

  have h_set2 : (F_lin a) '' A = Subtype.val '' (F_eq '' A) := by
    ext z
    simp only [Set.mem_image]
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact ⟨F_eq v, ⟨v, hv, rfl⟩, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      rcases hy with ⟨v, hv, rfl⟩
      exact ⟨v, hv, rfl⟩
  rw [h_set2]

  have h3 : ∀ (S : Set H), μHE[m] (Subtype.val '' S) = μHE[m] S := by
    intro S
    exact AffineSubspace.euclideanHausdorffMeasure_coe_image m (H : AffineSubspace ℝ (EuclideanSpace ℝ (Fin (m + 1)))) S
  rw [h3 (F_eq '' A)]

  have hfr : Module.finrank ℝ H = m := finrank_H a
  have h5 : (μHE[m] : Measure H) = volume := by
    have h : (μHE[Module.finrank ℝ H] : Measure H) = volume :=
      InnerProductSpace.euclideanHausdorffMeasure_eq_volume
    rw [hfr] at * <;> exact h
  rw [h5]

  have h_comp : ∀ (x : EuclideanSpace ℝ (Fin m)), L (T_map x) = F_eq x := by
    intro x
    have h2 : T_map x = (L_iso a).symm ((F_equiv a) x) := by
      simp [T_map, ContinuousLinearEquiv.trans_apply] <;> rfl
    rw [h2]
    have h3 : (L_iso a) ((L_iso a).symm ((F_equiv a) x)) = (F_equiv a) x := by
      exact (L_iso a).apply_symm_apply _
    exact h3
  have h7 : F_eq '' A = L '' (T_map '' A) := by
    calc F_eq '' A
      = (fun x => F_eq x) '' A := by rfl
    _ = (fun x => L (T_map x)) '' A := by
      apply congr_arg (fun f => f '' A)
      funext x
      exact (h_comp x).symm
    _ = L '' (T_map '' A) := by rw [Set.image_image]
  rw [h7]

  have h8 : MeasurePreserving (L : (EuclideanSpace ℝ (Fin m)) → H) volume volume := by
    have h9 : MeasurePreserving (L : (EuclideanSpace ℝ (Fin m)) → H) (μHE[m]) (μHE[m]) :=
      (L : (EuclideanSpace ℝ (Fin m)) ≃ₗᵢ[ℝ] H).toIsometryEquiv.measurePreserving_euclideanHausdorffMeasure m
    have h10 : (μHE[m] : Measure (EuclideanSpace ℝ (Fin m))) = volume :=
      EuclideanSpace.euclideanHausdorffMeasure_eq_volume m
    have h11 : (μHE[m] : Measure H) = volume := by
      have hfr2 : Module.finrank ℝ H = m := finrank_H a
      have h : (μHE[Module.finrank ℝ H] : Measure H) = volume :=
        InnerProductSpace.euclideanHausdorffMeasure_eq_volume
      rw [hfr2] at * <;> exact h
    simpa [h10, h11] using h9
  have h8_symm : MeasurePreserving (L.symm : H → (EuclideanSpace ℝ (Fin m))) volume volume := by
    have h9 : MeasurePreserving (L.symm : H → (EuclideanSpace ℝ (Fin m))) (μHE[m]) (μHE[m]) :=
      (L.symm : H ≃ₗᵢ[ℝ] (EuclideanSpace ℝ (Fin m))).toIsometryEquiv.measurePreserving_euclideanHausdorffMeasure m
    have h10 : (μHE[m] : Measure (EuclideanSpace ℝ (Fin m))) = volume :=
      EuclideanSpace.euclideanHausdorffMeasure_eq_volume m
    have h11 : (μHE[m] : Measure H) = volume := by
      have hfr2 : Module.finrank ℝ H = m := finrank_H a
      have h : (μHE[Module.finrank ℝ H] : Measure H) = volume :=
        InnerProductSpace.euclideanHausdorffMeasure_eq_volume
      rw [hfr2] at * <;> exact h
    simpa [h10, h11] using h9
  have h_img_preimg : T_map '' A = T_map.symm ⁻¹' A := by
    ext y
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro h
      refine ⟨T_map.symm y, h, ?_⟩
      simp
  have h_meas : MeasurableSet (T_map '' A) := by
    rw [h_img_preimg]
    exact T_map.symm.continuous.measurable hA
  have h12 : volume (L '' (T_map '' A)) = volume (T_map '' A) := by
    have h_eq_set : L '' (T_map '' A) = (L.symm : H → (EuclideanSpace ℝ (Fin m))) ⁻¹' (T_map '' A) := by
      ext y
      simp only [Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨x, hx, h_eq⟩
        have h4 : L.symm y = x := by
          apply L.injective
          rw [h_eq]
          <;> simp
        rw [h4] <;> exact hx
      · intro h
        refine ⟨L.symm y, h, ?_⟩
        simp
    rw [h_eq_set]
    exact h8_symm.measure_preimage (h_meas.nullMeasurableSet)
  rw [h12]

  have h13 : volume (T_map '' A) =
      ENNReal.ofReal |LinearMap.det T_map.toLinearMap| * volume A :=
    MeasureTheory.Measure.addHaar_image_continuousLinearEquiv volume T_map A
  rw [h13, abs_det_T a]

theorem graph_area_affine (A : Set (EuclideanSpace ℝ (Fin m))) (hA : MeasurableSet A) :
    μHE[m] (graph (fun x : EuclideanSpace ℝ (Fin m) => a x + b) ∩ cylinder A) =
      ENNReal.ofReal (Real.sqrt (1 + ‖a‖ ^ 2)) * volume A := by
  let v : EuclideanSpace ℝ (Fin (m + 1)) :=
    (EuclideanSpace.equiv (Fin (m + 1)) ℝ).symm
      (fun i : Fin (m + 1) => if h : i.val < m then (0 : ℝ) else b)
  let τ : (EuclideanSpace ℝ (Fin (m + 1))) → (EuclideanSpace ℝ (Fin (m + 1))) := fun p => p + v
  have hτ : Isometry τ := by exact isometry_add_right _
  have hv1 : ∀ (i : Fin m), v (Fin.castSucc i) = 0 := by
    intro i
    simp [v, EuclideanSpace.equiv]
    <;> split_ifs <;> omega
  have hv2 : v (Fin.last m) = b := by
    simp [v, EuclideanSpace.equiv]
    <;> split_ifs <;> omega
  have hproj_add : ∀ (p : EuclideanSpace ℝ (Fin (m + 1))), proj (p + v) = proj p := by
    intro p
    ext i
    rw [proj_apply, proj_apply]
    have h_add : (p + v) (Fin.castSucc i) = p (Fin.castSucc i) + v (Fin.castSucc i) := by rfl
    rw [h_add, hv1, add_zero]
  have hlast_add : ∀ (p : EuclideanSpace ℝ (Fin (m + 1))), (p + v) (Fin.last m) = p (Fin.last m) + b := by
    intro p
    have h_add : (p + v) (Fin.last m) = p (Fin.last m) + v (Fin.last m) := by rfl
    rw [h_add, hv2]
  have hproj_sub : ∀ (z : EuclideanSpace ℝ (Fin (m + 1))), proj (z - v) = proj z := by
    intro z
    have h : proj ((z - v) + v) = proj (z - v) := hproj_add (z - v)
    have h2 : (z - v) + v = z := by simp
    rw [h2] at h
    exact h.symm
  have hlast_sub : ∀ (z : EuclideanSpace ℝ (Fin (m + 1))), (z - v) (Fin.last m) = z (Fin.last m) - b := by
    intro z
    have h : (z - v) + v = z := by simp
    have h3 : ((z - v) + v) (Fin.last m) = z (Fin.last m) := by rw [h]
    have h4 : ((z - v) + v) (Fin.last m) = (z - v) (Fin.last m) + v (Fin.last m) := by rfl
    rw [h4, hv2] at h3
    linarith
  have h_set2 : graph (fun x : EuclideanSpace ℝ (Fin m) => a x + b) ∩ cylinder A =
      τ '' (graph (fun x : EuclideanSpace ℝ (Fin m) => a x) ∩ cylinder A) := by
    ext z
    simp only [graph, cylinder, Set.mem_image, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2⟩
      let p := z - v
      have hpz : p + v = z := by simp [p]
      have hproj_p : proj p = proj z := hproj_sub z
      have hlast_p : p (Fin.last m) = z (Fin.last m) - b := hlast_sub z
      refine ⟨p, ⟨?_, ?_⟩, hpz⟩
      · rw [hlast_p, hproj_p]
        linarith [h1]
      · rw [hproj_p] <;> exact h2
    · rintro ⟨p, ⟨hp1, hp2⟩, rfl⟩
      constructor
      · have h_proj : proj (p + v) = proj p := hproj_add p
        rw [h_proj, hlast_add, hp1] <;> ring
      · have h_proj2 : proj (p + v) = proj p := hproj_add p
        rw [h_proj2] <;> exact hp2
  rw [h_set2]
  rw [hτ.euclideanHausdorffMeasure_image]
  exact graph_area_linear a A hA

end Graph

end GraphAreaFormula
