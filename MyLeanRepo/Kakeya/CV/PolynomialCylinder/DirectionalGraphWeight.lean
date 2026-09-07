import MyLeanRepo.Kakeya.CV.PolynomialCylinder.GraphAreaFderiv
import MyLeanRepo.Kakeya.CV.PolynomialCylinder.DirectionCovers

/-!
# Directional graph weight identities

This module proves the pointwise graph-weight identities for graphs solved in
the first and second coordinate directions.
-/

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal Real

namespace Kakeya.CV

variable {p : MvPolynomial (Fin 3) ℝ} {g : R2 → ℝ} {y : R2} {u : R3}

/-- The derivative of an x-direction graph map. -/
def xGraphMapFderiv (g : R2 → ℝ) (y : R2) : R2 →L[ℝ] R3 :=
  { toFun := fun v : R2 =>
      (EuclideanSpace.equiv (Fin 3) ℝ).symm
        ![fderiv ℝ g y v, v 1, v 0]
    map_add' := by
      intro v w
      ext i
      fin_cases i <;> simp
    map_smul' := by
      intro c v
      ext i
      fin_cases i <;> simp [smul_eq_mul] }

lemma xGraphMap_fderiv
    (g : R2 → ℝ) (y : R2) (h_diff : DifferentiableAt ℝ g y) :
    HasFDerivAt (xGraphMap g) (xGraphMapFderiv g y) y := by
  let proj0 : R2 →L[ℝ] ℝ :=
    { toFun := fun x => x 0
      map_add' := by intro v w; rfl
      map_smul' := by intro c v; rfl }
  let proj1 : R2 →L[ℝ] ℝ :=
    { toFun := fun x => x 1
      map_add' := by intro v w; rfl
      map_smul' := by intro c v; rfl }
  have h0 : HasFDerivAt (fun x : R2 => x 0) proj0 y :=
    proj0.hasFDerivAt
  have h1 : HasFDerivAt (fun x : R2 => x 1) proj1 y :=
    proj1.hasFDerivAt
  have hg : HasFDerivAt g (fderiv ℝ g y) y :=
    h_diff.hasFDerivAt
  let e : (Fin 3 → ℝ) ≃L[ℝ] R3 :=
    (EuclideanSpace.equiv (Fin 3) ℝ).symm
  let F : R2 → (Fin 3 → ℝ) := fun x => ![g x, x 1, x 0]
  let φ' : Fin 3 → (R2 →L[ℝ] ℝ) := fun i =>
    if i = 0 then fderiv ℝ g y else if i = 1 then proj1 else proj0
  let F' : R2 →L[ℝ] (Fin 3 → ℝ) :=
    ContinuousLinearMap.pi φ'
  have hF : HasFDerivAt F F' y := by
    rw [hasFDerivAt_pi]
    intro i
    fin_cases i <;> simp [φ', h0, h1, hg]
  have hmain :
      HasFDerivAt (e ∘ F) (e.toContinuousLinearMap.comp F') y :=
    e.toContinuousLinearMap.hasFDerivAt.comp y hF
  have hfun : e ∘ F = xGraphMap g := by
    funext x
    simp [xGraphMap, F, e, graphMap, swapCoords]
    <;> ext i <;> fin_cases i <;> simp <;> rfl
  have hderiv :
      e.toContinuousLinearMap.comp F' = xGraphMapFderiv g y := by
    ext v i
    simp [xGraphMapFderiv, F', φ',
      ContinuousLinearMap.pi_apply]
    <;> fin_cases i <;> simp <;> rfl
  rw [hfun, hderiv] at hmain
  exact hmain

/-- On an x-direction graph, the directional normal weight times the graph
Jacobian is the corresponding gradient weight divided by the nonzero first
gradient component. -/
lemma graph_weight_identity_x
    (_h_zero : polynomialValue p (xGraphMap g y) = 0)
    (h_zero_local :
      ∀ᶠ w : R2 in nhds y,
        polynomialValue p (xGraphMap g w) = 0)
    (h_reg : (polynomialGradient p (xGraphMap g y)) 0 ≠ 0)
    (hg_diff : DifferentiableAt ℝ g y) :
    ‖inner ℝ u (polynomialUnitNormal p (xGraphMap g y))‖ *
        Real.sqrt (1 + ‖fderiv ℝ g y‖ ^ 2) =
      ‖inner ℝ u (polynomialGradient p (xGraphMap g y))‖ /
        |(polynomialGradient p (xGraphMap g y)) 0| := by
  set z : R3 := xGraphMap g y with hz
  set grad : R3 := polynomialGradient p z with hgrad
  have hgrad0 : grad 0 ≠ 0 := h_reg
  have hgrad_ne : grad ≠ 0 := by
    intro h
    apply hgrad0
    rw [h]
    simp
  have hnorm_pos : 0 < ‖grad‖ :=
    norm_pos_iff.mpr hgrad_ne
  have hlocal :
      (fun w : R2 => polynomialValue p (xGraphMap g w)) =ᶠ[nhds y]
        (0 : R2 → ℝ) :=
    h_zero_local
  have hzero_deriv :
      HasFDerivAt
        (fun w : R2 => polynomialValue p (xGraphMap g w))
        (0 : R2 →L[ℝ] ℝ) y := by
    exact
      (hasFDerivAt_const (c := (0 : ℝ)) (x := y)).congr_of_eventuallyEq
        hlocal
  have hp_deriv :
      HasFDerivAt (fun v : R3 => polynomialValue p v)
        (gradientCLM p (xGraphMap g y)) (xGraphMap g y) :=
    polynomialValue_fderiv p (xGraphMap g y)
  have hgraph_deriv :
      HasFDerivAt (xGraphMap g) (xGraphMapFderiv g y) y :=
    xGraphMap_fderiv g y hg_diff
  have hchain :
      HasFDerivAt
        (fun w : R2 => polynomialValue p (xGraphMap g w))
        ((gradientCLM p z).comp (xGraphMapFderiv g y)) y := by
    have heq :
        gradientCLM p (xGraphMap g y) = gradientCLM p z := by
      simp [hz]
    have h := hp_deriv.comp y hgraph_deriv
    rw [heq] at h
    exact h
  have hkey :
      (gradientCLM p z).comp (xGraphMapFderiv g y) =
        (0 : R2 →L[ℝ] ℝ) :=
    hchain.unique hzero_deriv
  have hderiv0 :
      fderiv ℝ g y e02 = -grad 2 / grad 0 := by
    have hzero :
        (gradientCLM p z).comp (xGraphMapFderiv g y) e02 = 0 := by
      rw [hkey]
      simp
    have happly :
        (gradientCLM p z).comp (xGraphMapFderiv g y) e02 =
          gradientCLM p z (xGraphMapFderiv g y e02) := rfl
    have hcalc :
        gradientCLM p z (xGraphMapFderiv g y e02) =
          grad 0 * fderiv ℝ g y e02 + grad 2 := by
      rw [gradientCLM_apply]
      have hcomponent :
          ∀ i : Fin 3,
            polynomialValue (MvPolynomial.pderiv i p) z = grad i := by
        intro i
        simp [hgrad, polynomialGradient]
      rw [Fin.sum_univ_three, hcomponent 0, hcomponent 1,
        hcomponent 2]
      simp [xGraphMapFderiv, e02]
    have heq : grad 0 * fderiv ℝ g y e02 + grad 2 = 0 := by
      rw [← hcalc, ← happly, hzero]
    field_simp [hgrad0] at heq ⊢
    linarith
  have hderiv1 :
      fderiv ℝ g y e12 = -grad 1 / grad 0 := by
    have hzero :
        (gradientCLM p z).comp (xGraphMapFderiv g y) e12 = 0 := by
      rw [hkey]
      simp
    have happly :
        (gradientCLM p z).comp (xGraphMapFderiv g y) e12 =
          gradientCLM p z (xGraphMapFderiv g y e12) := rfl
    have hcalc :
        gradientCLM p z (xGraphMapFderiv g y e12) =
          grad 0 * fderiv ℝ g y e12 + grad 1 := by
      rw [gradientCLM_apply]
      have hcomponent :
          ∀ i : Fin 3,
            polynomialValue (MvPolynomial.pderiv i p) z = grad i := by
        intro i
        simp [hgrad, polynomialGradient]
      rw [Fin.sum_univ_three, hcomponent 0, hcomponent 1,
        hcomponent 2]
      simp [xGraphMapFderiv, e12]
    have heq : grad 0 * fderiv ℝ g y e12 + grad 1 = 0 := by
      rw [← hcalc, ← happly, hzero]
    field_simp [hgrad0] at heq ⊢
    linarith
  have hnorm_fderiv :
      ‖fderiv ℝ g y‖ ^ 2 =
        ((grad 1) ^ 2 + (grad 2) ^ 2) / (grad 0) ^ 2 := by
    let v : R2 :=
      (InnerProductSpace.toDual ℝ R2).symm (fderiv ℝ g y)
    have hev :
        (InnerProductSpace.toDual ℝ R2) v = fderiv ℝ g y :=
      (InnerProductSpace.toDual ℝ R2).apply_symm_apply
        (fderiv ℝ g y)
    have hfun : (fderiv ℝ g y : R2 → ℝ) = inner ℝ v := by
      have h :
          ((InnerProductSpace.toDual ℝ R2) v : R2 → ℝ) =
            (fderiv ℝ g y : R2 → ℝ) :=
        congr_arg (fun L : R2 →L[ℝ] ℝ => (L : R2 → ℝ)) hev
      exact h.symm
    have hvnorm : ‖fderiv ℝ g y‖ = ‖v‖ := by
      have h := (InnerProductSpace.toDual ℝ R2).norm_map v
      rw [hev] at h
      exact h
    have h0 : fderiv ℝ g y e02 = v 0 := by
      rw [hfun]
      simp [e02, PiLp.inner_apply]
    have h1 : fderiv ℝ g y e12 = v 1 := by
      rw [hfun]
      simp [e12, PiLp.inner_apply]
    have hv_sq : ‖v‖ ^ 2 = (v 0) ^ 2 + (v 1) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    have hfd_sq :
        ‖fderiv ℝ g y‖ ^ 2 =
          (fderiv ℝ g y e02) ^ 2 +
            (fderiv ℝ g y e12) ^ 2 := by
      rw [hvnorm, hv_sq, h0, h1]
    rw [hfd_sq, hderiv0, hderiv1]
    field_simp [hgrad0]
    ring
  have hnorm_ratio :
      1 + ‖fderiv ℝ g y‖ ^ 2 =
        ‖grad‖ ^ 2 / (grad 0) ^ 2 := by
    have hgrad_sq :
        ‖grad‖ ^ 2 =
          (grad 0) ^ 2 + (grad 1) ^ 2 + (grad 2) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
    rw [hnorm_fderiv, hgrad_sq]
    field_simp [hgrad0]
    ring
  have hsqrt :
      Real.sqrt (1 + ‖fderiv ℝ g y‖ ^ 2) =
        ‖grad‖ / |grad 0| := by
    rw [hnorm_ratio, Real.sqrt_div (by positivity),
      Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg grad),
      Real.sqrt_sq_eq_abs]
  have hunit :
      polynomialUnitNormal p z = ‖grad‖⁻¹ • grad := by
    rw [polynomialUnitNormal, dif_neg hnorm_pos.ne']
  have hinner :
      ‖inner ℝ u (polynomialUnitNormal p z)‖ =
        ‖inner ℝ u grad‖ / ‖grad‖ := by
    rw [hunit, inner_smul_right]
    have habs :
        ‖(‖grad‖⁻¹ * inner ℝ u grad : ℝ)‖ =
          |‖grad‖⁻¹| * ‖inner ℝ u grad‖ := by
      simp only [Real.norm_eq_abs, abs_mul]
    rw [habs, abs_inv, abs_of_nonneg (norm_nonneg grad)]
    ring
  rw [hinner, hsqrt]
  field_simp [hgrad0, hnorm_pos.ne']

/-- The derivative of a y-direction graph map. -/
def yGraphMapFderiv (g : R2 → ℝ) (y : R2) : R2 →L[ℝ] R3 :=
  { toFun := fun v : R2 =>
      (EuclideanSpace.equiv (Fin 3) ℝ).symm
        ![v 0, fderiv ℝ g y v, v 1]
    map_add' := by
      intro v w
      ext i
      fin_cases i <;> simp
    map_smul' := by
      intro c v
      ext i
      fin_cases i <;> simp [smul_eq_mul] }

lemma yGraphMap_fderiv
    (g : R2 → ℝ) (y : R2) (h_diff : DifferentiableAt ℝ g y) :
    HasFDerivAt (yGraphMap g) (yGraphMapFderiv g y) y := by
  let proj0 : R2 →L[ℝ] ℝ :=
    { toFun := fun x => x 0
      map_add' := by intro v w; rfl
      map_smul' := by intro c v; rfl }
  let proj1 : R2 →L[ℝ] ℝ :=
    { toFun := fun x => x 1
      map_add' := by intro v w; rfl
      map_smul' := by intro c v; rfl }
  have h0 : HasFDerivAt (fun x : R2 => x 0) proj0 y :=
    proj0.hasFDerivAt
  have h1 : HasFDerivAt (fun x : R2 => x 1) proj1 y :=
    proj1.hasFDerivAt
  have hg : HasFDerivAt g (fderiv ℝ g y) y :=
    h_diff.hasFDerivAt
  let e : (Fin 3 → ℝ) ≃L[ℝ] R3 :=
    (EuclideanSpace.equiv (Fin 3) ℝ).symm
  let F : R2 → (Fin 3 → ℝ) := fun x => ![x 0, g x, x 1]
  let φ' : Fin 3 → (R2 →L[ℝ] ℝ) := fun i =>
    if i = 0 then proj0 else if i = 1 then fderiv ℝ g y else proj1
  let F' : R2 →L[ℝ] (Fin 3 → ℝ) :=
    ContinuousLinearMap.pi φ'
  have hF : HasFDerivAt F F' y := by
    rw [hasFDerivAt_pi]
    intro i
    fin_cases i <;> simp [φ', h0, h1, hg]
  have hmain :
      HasFDerivAt (e ∘ F) (e.toContinuousLinearMap.comp F') y :=
    e.toContinuousLinearMap.hasFDerivAt.comp y hF
  have hfun : e ∘ F = yGraphMap g := by
    funext x
    simp [yGraphMap, F, e, graphMap, swapCoords]
    <;> ext i <;> fin_cases i <;> simp <;> rfl
  have hderiv :
      e.toContinuousLinearMap.comp F' = yGraphMapFderiv g y := by
    ext v i
    simp [yGraphMapFderiv, F', φ',
      ContinuousLinearMap.pi_apply]
    <;> fin_cases i <;> simp <;> rfl
  rw [hfun, hderiv] at hmain
  exact hmain

/-- On a y-direction graph, the directional normal weight times the graph
Jacobian is the corresponding gradient weight divided by the nonzero second
gradient component. -/
lemma graph_weight_identity_y
    (_h_zero : polynomialValue p (yGraphMap g y) = 0)
    (h_zero_local :
      ∀ᶠ w : R2 in nhds y,
        polynomialValue p (yGraphMap g w) = 0)
    (h_reg : (polynomialGradient p (yGraphMap g y)) 1 ≠ 0)
    (hg_diff : DifferentiableAt ℝ g y) :
    ‖inner ℝ u (polynomialUnitNormal p (yGraphMap g y))‖ *
        Real.sqrt (1 + ‖fderiv ℝ g y‖ ^ 2) =
      ‖inner ℝ u (polynomialGradient p (yGraphMap g y))‖ /
        |(polynomialGradient p (yGraphMap g y)) 1| := by
  set z : R3 := yGraphMap g y with hz
  set grad : R3 := polynomialGradient p z with hgrad
  have hgrad1 : grad 1 ≠ 0 := h_reg
  have hgrad_ne : grad ≠ 0 := by
    intro h
    apply hgrad1
    rw [h]
    simp
  have hnorm_pos : 0 < ‖grad‖ :=
    norm_pos_iff.mpr hgrad_ne
  have hlocal :
      (fun w : R2 => polynomialValue p (yGraphMap g w)) =ᶠ[nhds y]
        (0 : R2 → ℝ) :=
    h_zero_local
  have hzero_deriv :
      HasFDerivAt
        (fun w : R2 => polynomialValue p (yGraphMap g w))
        (0 : R2 →L[ℝ] ℝ) y := by
    exact
      (hasFDerivAt_const (c := (0 : ℝ)) (x := y)).congr_of_eventuallyEq
        hlocal
  have hp_deriv :
      HasFDerivAt (fun v : R3 => polynomialValue p v)
        (gradientCLM p (yGraphMap g y)) (yGraphMap g y) :=
    polynomialValue_fderiv p (yGraphMap g y)
  have hgraph_deriv :
      HasFDerivAt (yGraphMap g) (yGraphMapFderiv g y) y :=
    yGraphMap_fderiv g y hg_diff
  have hchain :
      HasFDerivAt
        (fun w : R2 => polynomialValue p (yGraphMap g w))
        ((gradientCLM p z).comp (yGraphMapFderiv g y)) y := by
    have heq :
        gradientCLM p (yGraphMap g y) = gradientCLM p z := by
      simp [hz]
    have h := hp_deriv.comp y hgraph_deriv
    rw [heq] at h
    exact h
  have hkey :
      (gradientCLM p z).comp (yGraphMapFderiv g y) =
        (0 : R2 →L[ℝ] ℝ) :=
    hchain.unique hzero_deriv
  have hderiv0 :
      fderiv ℝ g y e02 = -grad 0 / grad 1 := by
    have hzero :
        (gradientCLM p z).comp (yGraphMapFderiv g y) e02 = 0 := by
      rw [hkey]
      simp
    have happly :
        (gradientCLM p z).comp (yGraphMapFderiv g y) e02 =
          gradientCLM p z (yGraphMapFderiv g y e02) := rfl
    have hcalc :
        gradientCLM p z (yGraphMapFderiv g y e02) =
          grad 0 + grad 1 * fderiv ℝ g y e02 := by
      rw [gradientCLM_apply]
      have hcomponent :
          ∀ i : Fin 3,
            polynomialValue (MvPolynomial.pderiv i p) z = grad i := by
        intro i
        simp [hgrad, polynomialGradient]
      rw [Fin.sum_univ_three, hcomponent 0, hcomponent 1,
        hcomponent 2]
      simp [yGraphMapFderiv, e02]
    have heq : grad 0 + grad 1 * fderiv ℝ g y e02 = 0 := by
      rw [← hcalc, ← happly, hzero]
    field_simp [hgrad1] at heq ⊢
    linarith
  have hderiv1 :
      fderiv ℝ g y e12 = -grad 2 / grad 1 := by
    have hzero :
        (gradientCLM p z).comp (yGraphMapFderiv g y) e12 = 0 := by
      rw [hkey]
      simp
    have happly :
        (gradientCLM p z).comp (yGraphMapFderiv g y) e12 =
          gradientCLM p z (yGraphMapFderiv g y e12) := rfl
    have hcalc :
        gradientCLM p z (yGraphMapFderiv g y e12) =
          grad 1 * fderiv ℝ g y e12 + grad 2 := by
      rw [gradientCLM_apply]
      have hcomponent :
          ∀ i : Fin 3,
            polynomialValue (MvPolynomial.pderiv i p) z = grad i := by
        intro i
        simp [hgrad, polynomialGradient]
      rw [Fin.sum_univ_three, hcomponent 0, hcomponent 1,
        hcomponent 2]
      simp [yGraphMapFderiv, e12]
    have heq : grad 1 * fderiv ℝ g y e12 + grad 2 = 0 := by
      rw [← hcalc, ← happly, hzero]
    field_simp [hgrad1] at heq ⊢
    linarith
  have hnorm_fderiv :
      ‖fderiv ℝ g y‖ ^ 2 =
        ((grad 0) ^ 2 + (grad 2) ^ 2) / (grad 1) ^ 2 := by
    let v : R2 :=
      (InnerProductSpace.toDual ℝ R2).symm (fderiv ℝ g y)
    have hev :
        (InnerProductSpace.toDual ℝ R2) v = fderiv ℝ g y :=
      (InnerProductSpace.toDual ℝ R2).apply_symm_apply
        (fderiv ℝ g y)
    have hfun : (fderiv ℝ g y : R2 → ℝ) = inner ℝ v := by
      have h :
          ((InnerProductSpace.toDual ℝ R2) v : R2 → ℝ) =
            (fderiv ℝ g y : R2 → ℝ) :=
        congr_arg (fun L : R2 →L[ℝ] ℝ => (L : R2 → ℝ)) hev
      exact h.symm
    have hvnorm : ‖fderiv ℝ g y‖ = ‖v‖ := by
      have h := (InnerProductSpace.toDual ℝ R2).norm_map v
      rw [hev] at h
      exact h
    have h0 : fderiv ℝ g y e02 = v 0 := by
      rw [hfun]
      simp [e02, PiLp.inner_apply]
    have h1 : fderiv ℝ g y e12 = v 1 := by
      rw [hfun]
      simp [e12, PiLp.inner_apply]
    have hv_sq : ‖v‖ ^ 2 = (v 0) ^ 2 + (v 1) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    have hfd_sq :
        ‖fderiv ℝ g y‖ ^ 2 =
          (fderiv ℝ g y e02) ^ 2 +
            (fderiv ℝ g y e12) ^ 2 := by
      rw [hvnorm, hv_sq, h0, h1]
    rw [hfd_sq, hderiv0, hderiv1]
    field_simp [hgrad1]
  have hnorm_ratio :
      1 + ‖fderiv ℝ g y‖ ^ 2 =
        ‖grad‖ ^ 2 / (grad 1) ^ 2 := by
    have hgrad_sq :
        ‖grad‖ ^ 2 =
          (grad 0) ^ 2 + (grad 1) ^ 2 + (grad 2) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
    rw [hnorm_fderiv, hgrad_sq]
    field_simp [hgrad1]
    ring
  have hsqrt :
      Real.sqrt (1 + ‖fderiv ℝ g y‖ ^ 2) =
        ‖grad‖ / |grad 1| := by
    rw [hnorm_ratio, Real.sqrt_div (by positivity),
      Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg grad),
      Real.sqrt_sq_eq_abs]
  have hunit :
      polynomialUnitNormal p z = ‖grad‖⁻¹ • grad := by
    rw [polynomialUnitNormal, dif_neg hnorm_pos.ne']
  have hinner :
      ‖inner ℝ u (polynomialUnitNormal p z)‖ =
        ‖inner ℝ u grad‖ / ‖grad‖ := by
    rw [hunit, inner_smul_right]
    have habs :
        ‖(‖grad‖⁻¹ * inner ℝ u grad : ℝ)‖ =
          |‖grad‖⁻¹| * ‖inner ℝ u grad‖ := by
      simp only [Real.norm_eq_abs, abs_mul]
    rw [habs, abs_inv, abs_of_nonneg (norm_nonneg grad)]
    ring
  rw [hinner, hsqrt]
  field_simp [hgrad1, hnorm_pos.ne']

/-- On a z-direction graph, the directional normal weight times the graph
Jacobian is the corresponding gradient weight divided by the nonzero third
gradient component. -/
lemma graph_weight_identity_z
    (_h_zero : polynomialValue p (graphMap g y) = 0)
    (h_zero_local :
      ∀ᶠ w : R2 in nhds y,
        polynomialValue p (graphMap g w) = 0)
    (h_reg : (polynomialGradient p (graphMap g y)) 2 ≠ 0)
    (hg_diff : DifferentiableAt ℝ g y) :
    ‖inner ℝ u (polynomialUnitNormal p (graphMap g y))‖ *
        Real.sqrt (1 + ‖fderiv ℝ g y‖ ^ 2) =
      ‖inner ℝ u (polynomialGradient p (graphMap g y))‖ /
        |(polynomialGradient p (graphMap g y)) 2| := by
  set z : R3 := graphMap g y with hz
  set grad : R3 := polynomialGradient p z with hgrad
  have hgrad2 : grad 2 ≠ 0 := h_reg
  have hgrad_ne : grad ≠ 0 := by
    intro h; apply hgrad2; rw [h]; simp
  have hnorm_pos : 0 < ‖grad‖ := norm_pos_iff.mpr hgrad_ne
  have hlocal : (fun w : R2 => polynomialValue p (graphMap g w)) =ᶠ[nhds y] (0 : R2 → ℝ) := h_zero_local
  have hzero_deriv : HasFDerivAt (fun w : R2 => polynomialValue p (graphMap g w)) (0 : R2 →L[ℝ] ℝ) y :=
    (hasFDerivAt_const (c := (0 : ℝ)) (x := y)).congr_of_eventuallyEq hlocal
  have hp_deriv : HasFDerivAt (fun v : R3 => polynomialValue p v) (gradientCLM p z) z :=
    polynomialValue_fderiv p z
  have hgraph_deriv : HasFDerivAt (graphMap g) (graphMapFderiv g y) y :=
    graphMap_fderiv g y hg_diff
  have hchain : HasFDerivAt (fun w : R2 => polynomialValue p (graphMap g w))
      ((gradientCLM p z).comp (graphMapFderiv g y)) y := by
    have heq : gradientCLM p (graphMap g y) = gradientCLM p z := by simp [hz]
    have h := hp_deriv.comp y hgraph_deriv
    rw [heq] at h; exact h
  have hkey : (gradientCLM p z).comp (graphMapFderiv g y) = (0 : R2 →L[ℝ] ℝ) :=
    hchain.unique hzero_deriv
  have hderiv0 : fderiv ℝ g y e02 = -grad 0 / grad 2 := by
    have hzero : (gradientCLM p z).comp (graphMapFderiv g y) e02 = 0 := by rw [hkey]; simp
    have happly : (gradientCLM p z).comp (graphMapFderiv g y) e02 = gradientCLM p z (graphMapFderiv g y e02) := rfl
    have hcalc : gradientCLM p z (graphMapFderiv g y e02) = grad 0 + grad 2 * fderiv ℝ g y e02 := by
      rw [gradientCLM_apply]
      have hcomponent : ∀ i : Fin 3, polynomialValue (MvPolynomial.pderiv i p) z = grad i := by
        intro i; simp [hgrad, polynomialGradient]
      rw [Fin.sum_univ_three, hcomponent 0, hcomponent 1, hcomponent 2]
      simp [graphMapFderiv, e02]
    have heq : grad 0 + grad 2 * fderiv ℝ g y e02 = 0 := by
      rw [← hcalc, ← happly, hzero]
    field_simp [hgrad2] at heq ⊢; linarith
  have hderiv1 : fderiv ℝ g y e12 = -grad 1 / grad 2 := by
    have hzero : (gradientCLM p z).comp (graphMapFderiv g y) e12 = 0 := by rw [hkey]; simp
    have happly : (gradientCLM p z).comp (graphMapFderiv g y) e12 = gradientCLM p z (graphMapFderiv g y e12) := rfl
    have hcalc : gradientCLM p z (graphMapFderiv g y e12) = grad 1 + grad 2 * fderiv ℝ g y e12 := by
      rw [gradientCLM_apply]
      have hcomponent : ∀ i : Fin 3, polynomialValue (MvPolynomial.pderiv i p) z = grad i := by
        intro i; simp [hgrad, polynomialGradient]
      rw [Fin.sum_univ_three, hcomponent 0, hcomponent 1, hcomponent 2]
      simp [graphMapFderiv, e12]
    have heq : grad 1 + grad 2 * fderiv ℝ g y e12 = 0 := by
      rw [← hcalc, ← happly, hzero]
    field_simp [hgrad2] at heq ⊢; linarith
  have hnorm_fderiv : ‖fderiv ℝ g y‖ ^ 2 = ((grad 0) ^ 2 + (grad 1) ^ 2) / (grad 2) ^ 2 := by
    let v : R2 := (InnerProductSpace.toDual ℝ R2).symm (fderiv ℝ g y)
    have hfun : (fderiv ℝ g y : R2 → ℝ) = inner ℝ v := by
      have h := ((InnerProductSpace.toDual ℝ R2).apply_symm_apply (fderiv ℝ g y))
      exact congr_arg (fun L : R2 →L[ℝ] ℝ => (L : R2 → ℝ)) h |>.symm
    have hvnorm : ‖fderiv ℝ g y‖ = ‖v‖ := by
      have h := (InnerProductSpace.toDual ℝ R2).norm_map v
      rw [((InnerProductSpace.toDual ℝ R2).apply_symm_apply (fderiv ℝ g y))] at h; exact h
    have h0 : fderiv ℝ g y e02 = v 0 := by rw [hfun]; simp [e02, PiLp.inner_apply]
    have h1 : fderiv ℝ g y e12 = v 1 := by rw [hfun]; simp [e12, PiLp.inner_apply]
    have hv_sq : ‖v‖ ^ 2 = (v 0) ^ 2 + (v 1) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    have hfd_sq : ‖fderiv ℝ g y‖ ^ 2 = (fderiv ℝ g y e02) ^ 2 + (fderiv ℝ g y e12) ^ 2 := by
      rw [hvnorm, hv_sq, h0, h1]
    rw [hfd_sq, hderiv0, hderiv1]
    <;> field_simp [hgrad2] <;> ring
  have hnorm_ratio : 1 + ‖fderiv ℝ g y‖ ^ 2 = ‖grad‖ ^ 2 / (grad 2) ^ 2 := by
    have hgrad_sq : ‖grad‖ ^ 2 = (grad 0) ^ 2 + (grad 1) ^ 2 + (grad 2) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
    rw [hnorm_fderiv, hgrad_sq]; field_simp [hgrad2]; ring
  have hsqrt : Real.sqrt (1 + ‖fderiv ℝ g y‖ ^ 2) = ‖grad‖ / |grad 2| := by
    rw [hnorm_ratio, Real.sqrt_div (by positivity), Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg grad), Real.sqrt_sq_eq_abs]
  have hunit : polynomialUnitNormal p z = ‖grad‖⁻¹ • grad := by
    rw [polynomialUnitNormal, dif_neg hnorm_pos.ne']
  have hinner : ‖inner ℝ u (polynomialUnitNormal p z)‖ = ‖inner ℝ u grad‖ / ‖grad‖ := by
    rw [hunit, inner_smul_right]
    have habs : ‖(‖grad‖⁻¹ * inner ℝ u grad : ℝ)‖ = |‖grad‖⁻¹| * ‖inner ℝ u grad‖ := by
      simp only [Real.norm_eq_abs, abs_mul]
    rw [habs, abs_inv, abs_of_nonneg (norm_nonneg grad)]; ring
  rw [hinner, hsqrt]
  field_simp [hgrad2, hnorm_pos.ne']

end Kakeya.CV
