import MyLeanRepo.Kakeya.CV.PrincipalAxes.DirectionalGraphProjectionMeasurable
import MyLeanRepo.Kakeya.CV.PrincipalAxes.AffineBaseImageMeasurable
import MyLeanRepo.Kakeya.CV.PolynomialCylinder.AffinePullback
import MyLeanRepo.Kakeya.CV.Geometry
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.MeasureTheory.Measure.Hausdorff

/-!
# Projection area of a diagonally transformed graph

A positive diagonal affine map sends a regular coordinate graph to another
regular coordinate graph. Its directional surface area in the graph direction
is the standard plane constant times the determinant-scaled base volume.
-/

noncomputable section

open MeasureTheory Metric Set
open scoped ENNReal Real

namespace Kakeya.CV

/-- Projection-area formulas before and after a positive diagonal affine
transformation of a regular measurable graph patch. -/
lemma diagonal_transformed_graph_projection
    (p' q : MvPolynomial (Fin 3) ℝ)
    (D' : Point 3 ≃ₗ[ℝ] Point 3)
    (d0 d1 d2 : ℝ) (hd0 : 0 < d0) (hd1 : 0 < d1)
    (hD'0 : D' (eBasis 0) = d0 • eBasis 0)
    (hD'1 : D' (eBasis 1) = d1 • eBasis 1)
    (hD'2 : D' (eBasis 2) = d2 • eBasis 2)
    (c : Point 3)
    (hpq' : ∀ x, polynomialValue p' (c + D' x) = polynomialValue q x)
    {U : Set R2} {g : R2 → ℝ} {B : Set R2}
    (hU : IsOpen U) (hg : ContDiffOn ℝ 1 g U)
    (hB : MeasurableSet B) (hB_sub : B ⊆ U)
    (h_zero : ∀ u ∈ U, polynomialValue q (graphMap g u) = 0)
    (h_reg : ∀ u ∈ U, (polynomialGradient q (graphMap g u)) 2 ≠ 0) :
    directionalSurfaceArea (eBasis 2) p'
        ((fun y : Point 3 => c + D' y) '' (graphMap g '' B)) =
      planeConstant * (ENNReal.ofReal (d0 * d1) * volume B) ∧
    directionalSurfaceArea (eBasis 2) q (graphMap g '' B) =
      planeConstant * volume B := by
  let eqv2 := EuclideanSpace.equiv (Fin 2) ℝ
  let M : R2 ≃ₗ[ℝ] R2 :=
    { toFun := fun x : R2 => eqv2.symm ![d0 * x 0, d1 * x 1]
      invFun := fun y : R2 => eqv2.symm ![d0⁻¹ * y 0, d1⁻¹ * y 1]
      left_inv := by
        intro x
        apply eqv2.injective
        ext i
        fin_cases i <;> simp [eqv2, hd0.ne', hd1.ne']
      right_inv := by
        intro y
        apply eqv2.injective
        ext i
        fin_cases i <;> simp [eqv2, hd0.ne', hd1.ne']
      map_add' := by
        intro x y
        apply eqv2.injective
        ext i
        fin_cases i <;> simp [eqv2] <;> ring
      map_smul' := by
        intro r x
        apply eqv2.injective
        ext i
        fin_cases i <;> simp [eqv2] <;> ring }
  let c' : R2 := eqv2.symm ![c 0, c 1]
  let L : R2 → R2 := fun u => c' + M u
  let U' : Set R2 := L '' U
  let h : R2 → ℝ := fun s => c 2 + d2 * g (M.symm (s - c'))
  let B' : Set R2 := L '' B
  let F : Point 3 → Point 3 := fun y => c + D' y

  have h_eqv2_symm : ∀ (v : Fin 2 → ℝ) (j : Fin 2), (eqv2.symm v) j = v j := by
    intro v j
    have h1 : eqv2 (eqv2.symm v) = v := eqv2.right_inv v
    have h2 : (eqv2 (eqv2.symm v)) j = v j := by rw [h1]
    have h3 : (eqv2 (eqv2.symm v)) j = (eqv2.symm v) j := by rfl
    rw [h3] at h2
    exact h2

  have hM_comp : ∀ u : R2, (M u) 0 = d0 * u 0 ∧ (M u) 1 = d1 * u 1 := by
    intro u
    constructor <;> simp [M, h_eqv2_symm]

  have hc' : c' 0 = c 0 ∧ c' 1 = c 1 := by
    constructor <;> simp [c', h_eqv2_symm]

  have hD'_comp : ∀ x : Point 3,
      (D' x) 0 = d0 * x 0 ∧ (D' x) 1 = d1 * x 1 ∧ (D' x) 2 = d2 * x 2 := by
    intro x
    have h_basis : x = x 0 • eBasis 0 + x 1 • eBasis 1 + x 2 • eBasis 2 := by
      ext j
      fin_cases j <;> simp [eBasis, EuclideanSpace.single]
    rw [h_basis]
    have h : D' (x 0 • eBasis 0 + x 1 • eBasis 1 + x 2 • eBasis 2) =
        x 0 • D' (eBasis 0) + x 1 • D' (eBasis 1) + x 2 • D' (eBasis 2) := by
      rw [map_add, map_add, map_smul, map_smul, map_smul]
    rw [h, hD'0, hD'1, hD'2]
    constructor
    · simp [eBasis, EuclideanSpace.single, smul_eq_mul] <;> ring
    · constructor
      · simp [eBasis, EuclideanSpace.single, smul_eq_mul] <;> ring
      · simp [eBasis, EuclideanSpace.single, smul_eq_mul] <;> ring

  let Mcl : R2 ≃L[ℝ] R2 := M.toContinuousLinearEquiv
  let hL_homeo : Homeomorph R2 R2 :=
    { toFun := L
      invFun := fun y => M.symm (y - c')
      left_inv := by
        intro x
        simp [L]
      right_inv := by
        intro y
        simp [L]
      continuous_toFun := continuous_const.add Mcl.continuous
      continuous_invFun :=
        Mcl.symm.continuous.comp (continuous_id.sub continuous_const) }

  have hU'_open : IsOpen U' := by
    have h_open : IsOpen (hL_homeo '' U) := hL_homeo.isOpenMap U hU
    have h_eq : hL_homeo '' U = U' := by
      ext y
      simp only [Set.mem_image, U']
      constructor <;> intro hy <;> exact hy
    rwa [h_eq] at h_open

  have h_affine := affineBaseImage_measurable_volume hB c' M
  have hB'_meas : MeasurableSet B' := by
    have h1 : B' = (fun u : R2 => c' + M u) '' B := by rfl
    rw [h1]
    exact h_affine.1

  have hB'_sub : B' ⊆ U' := by
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact ⟨x, hB_sub hx, rfl⟩

  have hdetM : LinearMap.det (M : R2 →ₗ[ℝ] R2) = d0 * d1 := by
    let b2 := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
    have h00 : (M (b2 0)) 0 = d0 := by
      simp [M, b2, EuclideanSpace.basisFun_apply, h_eqv2_symm]
    have h01 : (M (b2 0)) 1 = 0 := by
      simp [M, b2, EuclideanSpace.basisFun_apply, h_eqv2_symm]
    have h10 : (M (b2 1)) 0 = 0 := by
      simp [M, b2, EuclideanSpace.basisFun_apply, h_eqv2_symm]
    have h11 : (M (b2 1)) 1 = d1 := by
      simp [M, b2, EuclideanSpace.basisFun_apply, h_eqv2_symm]
    have h_mat :
        LinearMap.toMatrix b2 b2 (M : R2 →ₗ[ℝ] R2) = Matrix.diagonal ![d0, d1] := by
      ext i j
      simp only [LinearMap.toMatrix_apply, Matrix.diagonal_apply]
      fin_cases i <;> fin_cases j <;>
        simp [h00, h01, h10, h11] <;> norm_num <;> tauto
    have h_det : LinearMap.det (M : R2 →ₗ[ℝ] R2) =
        Matrix.det (LinearMap.toMatrix b2 b2 (M : R2 →ₗ[ℝ] R2)) := by
      exact Eq.symm (LinearMap.det_toMatrix b2 (M : R2 →ₗ[ℝ] R2))
    rw [h_det, h_mat, Matrix.det_diagonal]
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
    simp

  have h_vol : volume B' = ENNReal.ofReal (d0 * d1) * volume B := by
    have h1 : B' = (fun u : R2 => c' + M u) '' B := by rfl
    rw [h1, h_affine.2, hdetM]
    exact congrArg (fun r => ENNReal.ofReal r * volume B)
      (abs_of_nonneg (mul_nonneg hd0.le hd1.le))

  have hM_symm_diff : ContDiff ℝ 1 (M.symm : R2 → R2) :=
    M.symm.toContinuousLinearMap.contDiff
  have h_sub_diff : ContDiff ℝ 1 (fun s : R2 => s - c') :=
    contDiff_id.sub contDiff_const
  have h_comp_diff : ContDiff ℝ 1 (fun s : R2 => M.symm (s - c')) :=
    hM_symm_diff.comp h_sub_diff
  have hh_diff : ContDiffOn ℝ 1 h U' := by
    have h1 : ContDiffOn ℝ 1 g U := hg
    have h2 : ContDiffOn ℝ 1 (fun s : R2 => M.symm (s - c')) U' :=
      h_comp_diff.contDiffOn
    have h3 : ContDiffOn ℝ 1 (g ∘ fun s : R2 => M.symm (s - c')) U' := by
      refine h1.comp h2 ?_
      intro s hs
      rcases hs with ⟨u, hu, rfl⟩
      simpa [L] using hu
    have h4 : ContDiffOn ℝ 1 (fun s : R2 => c 2 + d2 * g (M.symm (s - c'))) U' :=
      contDiffOn_const.add (contDiffOn_const.mul h3)
    simpa [h] using h4

  have hgm0 : ∀ (f : R2 → ℝ) (x : R2), (graphMap f x) 0 = x 0 := by
    intro f x
    simp [graphMap]
  have hgm1 : ∀ (f : R2 → ℝ) (x : R2), (graphMap f x) 1 = x 1 := by
    intro f x
    simp [graphMap]
  have hgm2 : ∀ (f : R2 → ℝ) (x : R2), (graphMap f x) 2 = f x := by
    intro f x
    simp [graphMap]

  have h_graph_eq : ∀ u, F (graphMap g u) = graphMap h (L u) := by
    intro u
    have hF0 : (F (graphMap g u)) 0 = c 0 + d0 * u 0 := by
      have h : (F (graphMap g u)) 0 = c 0 + (D' (graphMap g u)) 0 := by
        simp [F]
      rw [h, (hD'_comp (graphMap g u)).1, hgm0 g u]
    have hF1 : (F (graphMap g u)) 1 = c 1 + d1 * u 1 := by
      have h : (F (graphMap g u)) 1 = c 1 + (D' (graphMap g u)) 1 := by
        simp [F]
      rw [h, (hD'_comp (graphMap g u)).2.1, hgm1 g u]
    have hF2 : (F (graphMap g u)) 2 = c 2 + d2 * g u := by
      have h : (F (graphMap g u)) 2 = c 2 + (D' (graphMap g u)) 2 := by
        simp [F]
      rw [h, (hD'_comp (graphMap g u)).2.2, hgm2 g u]
    have hL0 : (L u) 0 = c 0 + d0 * u 0 := by
      change (c' + M u) 0 = _
      rw [show (c' + M u) 0 = c' 0 + (M u) 0 by rfl, hc'.1, (hM_comp u).1]
    have hL1 : (L u) 1 = c 1 + d1 * u 1 := by
      change (c' + M u) 1 = _
      rw [show (c' + M u) 1 = c' 1 + (M u) 1 by rfl, hc'.2, (hM_comp u).2]
    have hL2 : h (L u) = c 2 + d2 * g u := by
      have h5 : L u - c' = M u := by
        dsimp only [L]
        abel
      have h4 : M.symm (L u - c') = u := by
        rw [h5]
        exact M.left_inv u
      change c 2 + d2 * g (M.symm (L u - c')) = _
      rw [h4]
    have h0 : (F (graphMap g u)) 0 = (graphMap h (L u)) 0 := by
      rw [hF0, hgm0, hL0]
    have h1 : (F (graphMap g u)) 1 = (graphMap h (L u)) 1 := by
      rw [hF1, hgm1, hL1]
    have h2 : (F (graphMap g u)) 2 = (graphMap h (L u)) 2 := by
      rw [hF2, hgm2, hL2]
    have h_ext :
        ∀ i : Fin 3, (F (graphMap g u)) i = (graphMap h (L u)) i := by
      intro i
      have h_cases : i = 0 ∨ i = 1 ∨ i = 2 := by
        have h_v : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
        rcases h_v with (h_v | h_v | h_v)
        · left
          apply Fin.ext
          simpa using h_v
        · right
          left
          apply Fin.ext
          simpa using h_v
        · right
          right
          apply Fin.ext
          simpa using h_v
      rcases h_cases with (rfl | rfl | rfl)
      · exact h0
      · exact h1
      · exact h2
    exact (WithLp.equiv 2 (Fin 3 → ℝ)).injective (funext h_ext)

  have h_image_eq : F '' (graphMap g '' B) = graphMap h '' B' := by
    ext y
    simp only [Set.mem_image]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨L x, ⟨x, hx, rfl⟩, (h_graph_eq x).symm⟩
    · rintro ⟨s, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨graphMap g u, ⟨u, hu, rfl⟩, h_graph_eq u⟩

  have h_zero' : ∀ s ∈ U', polynomialValue p' (graphMap h s) = 0 := by
    intro s hs
    rcases hs with ⟨u, hu, rfl⟩
    rw [← h_graph_eq u, hpq', h_zero u hu]

  have hD'_adj2 :
      ∀ y : Point 3, ((D' : Point 3 →ₗ[ℝ] Point 3).adjoint y) 2 = d2 * y 2 := by
    intro y
    have h4 : inner ℝ (eBasis 2) ((D' : Point 3 →ₗ[ℝ] Point 3).adjoint y) =
        inner ℝ (D' (eBasis 2)) y :=
      LinearMap.adjoint_inner_right (D' : Point 3 →ₗ[ℝ] Point 3) (eBasis 2) y
    have h5 : ((D' : Point 3 →ₗ[ℝ] Point 3).adjoint y) 2 =
        inner ℝ (eBasis 2) ((D' : Point 3 →ₗ[ℝ] Point 3).adjoint y) := by
      simp [eBasis, PiLp.inner_apply]
    rw [h5, h4, hD'2]
    simp [eBasis, PiLp.inner_apply, smul_eq_mul] <;> ring

  have h_reg' : ∀ s ∈ U', (polynomialGradient p' (graphMap h s)) 2 ≠ 0 := by
    intro s hs
    rcases hs with ⟨u, hu, rfl⟩
    rw [← h_graph_eq u]
    have hq_eq : q = pullbackPolynomial p' c 1 D' := by
      let eqv3' : Point 3 ≃ (Fin 3 → ℝ) := WithLp.equiv _ _
      apply MvPolynomial.funext
      intro y
      let x : Point 3 := eqv3'.symm y
      have h1 : polynomialValue (pullbackPolynomial p' c 1 D') x =
          polynomialValue p' (c + D' x) := by
        rw [pullbackPolynomial_eval p' c 1 D' x]
        simp
      have h2 : polynomialValue (pullbackPolynomial p' c 1 D') x =
          polynomialValue q x := by
        rw [h1]
        exact hpq' x
      have h3 : (fun i : Fin 3 => x i) = y := by
        funext i
        simp [x, eqv3']
      simpa [polynomialValue, h3] using h2.symm
    have h_pullback : polynomialGradient q (graphMap g u) =
        (1 : ℝ) • (D' : Point 3 →ₗ[ℝ] Point 3).adjoint
          (polynomialGradient p' (F (graphMap g u))) := by
      rw [hq_eq]
      have hpb := pullbackGradient p' c 1 D' (graphMap g u)
      have hF : c + (1 : ℝ) • D' (graphMap g u) = F (graphMap g u) := by
        simp [F]
      rw [hF] at hpb
      exact hpb
    have h7 : (polynomialGradient q (graphMap g u)) 2 =
        d2 * (polynomialGradient p' (F (graphMap g u))) 2 := by
      rw [h_pullback]
      simp [hD'_adj2]
    have h10 : (polynomialGradient q (graphMap g u)) 2 ≠ 0 := h_reg u hu
    intro h_contra
    apply h10
    rw [h7, h_contra]
    simp

  have h_q_proj : directionalSurfaceArea (eBasis 2) q (graphMap g '' B) =
      planeConstant * volume B :=
    directionalSurfaceArea_zGraph_projection_meas hU hg hB hB_sub h_zero h_reg

  have h_p'_proj : directionalSurfaceArea (eBasis 2) p' (graphMap h '' B') =
      planeConstant * volume B' :=
    directionalSurfaceArea_zGraph_projection_meas
      hU'_open hh_diff hB'_meas hB'_sub h_zero' h_reg'

  have h_lhs : directionalSurfaceArea (eBasis 2) p' (F '' (graphMap g '' B)) =
      planeConstant * (ENNReal.ofReal (d0 * d1) * volume B) := by
    rw [h_image_eq, h_p'_proj, h_vol]

  exact ⟨h_lhs, h_q_proj⟩

end Kakeya.CV
