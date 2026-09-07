import MyLeanRepo.Kakeya.CV.Statements
import MyLeanRepo.Kakeya.CV.PrincipalAxes.DirectionalRegularAffineIdentityOn
import MyLeanRepo.Kakeya.CV.PrincipalAxes.DirectionalSurfaceAreaVanishing
import MyLeanRepo.Kakeya.CV.PrincipalAxes.CoordinateDirectionalAreaLowerBound
import MyLeanRepo.Kakeya.CV.PrincipalAxes.DeterminantProduct
import MyLeanRepo.Kakeya.CV.PrincipalAxes.CuttingBall
import MyLeanRepo.Kakeya.CV.PrincipalAxes.SingularSetPullback
import MyLeanRepo.Kakeya.CV.Geometry

/-!
# Single-ellipsoid weighted lower bound

Given a polynomial that cuts a scaled ellipsoid at least 40/40, the weighted
sum of directional surface areas in the principal directions is bounded below
by the isoperimetric constant times the ellipsoid volume factor.

This is the single-ellipsoid case of Carbery--Valdimarsson Section 8, Lemma 9.
-/

noncomputable section

open MeasureTheory Metric Set Finset
open scoped ENNReal Real BigOperators

namespace Kakeya.CV

lemma single_ellipsoid_weighted_lower_bound
    (hIso : PolynomialRegionIsoperimetricStatement)
    (p : MvPolynomial (Fin 3) ℝ)
    (A : Point 3 ≃ₗ[ℝ] Point 3) (η : ℝ) (z : Point 3)
    (b : OrthonormalBasis (Fin 3) ℝ (Point 3))
    (ℓ : Fin 3 → ℝ)
    (_hp : p ≠ 0) (hsing : HasNegligibleSingularSet p)
    (hη : 0 < η)
    (hℓ : ∀ i, 0 < ℓ i)
    (hA : ∀ i, A (eBasis i) = ℓ i • b i)
    (hCut : PolynomialCutsAtLeast p (scaledEllipsoid A η z)
      (2 / 5 : ℝ≥0∞)) :
    ENNReal.ofReal cutsBallConstant *
        ENNReal.ofReal (η ^ 2 * ∏ i, ℓ i) *
        codimensionOneMeasure 3 (unitSphere 3) ≤
      ∑ i : Fin 3, ENNReal.ofReal (ℓ i) *
        directionalSurfaceArea (b i) p
          (polynomialZeroSet p ∩ scaledEllipsoid A η z) := by
  let q := pullbackPolynomial p z η A
  let f : Point 3 → Point 3 := fun y => z + η • A y
  let Z : Set (Point 3) := polynomialZeroSet q ∩ unitBall 3

  have hpq : ∀ x, polynomialValue p (f x) = polynomialValue q x := by
    intro x
    exact (pullbackPolynomial_eval p z η A x).symm

  -- Step 2: pullback the cut condition
  have hCut_q : PolynomialCutsAtLeast q (unitBall 3) (2 / 5 : ℝ≥0∞) :=
    cutsAtLeast_pullback p z η hη A (2 / 5) hCut

  -- Step 3: cuts-ball lemma
  have hArea : codimensionOneMeasure 3 Z ≥
      ENNReal.ofReal cutsBallConstant * codimensionOneMeasure 3 (unitSphere 3) :=
    cutsAtLeastBallLemma hIso q hCut_q

  -- Step 4: singular set transfer
  have hsing_q : HasNegligibleSingularSet q :=
    hasNegligibleSingularSet_pullback p z η hη A hsing

  -- Step 5: measurability of Z
  have hZ_meas : MeasurableSet Z := by
    have h1 : MeasurableSet (polynomialZeroSet q) := by
      have h_cont : Continuous (fun x : Point 3 => polynomialValue q x) := by
        have h1 : Continuous (EuclideanSpace.equiv (Fin 3) ℝ) :=
          (EuclideanSpace.equiv (Fin 3) ℝ).toLinearMap.continuous_of_finiteDimensional
        have h2 : Continuous (fun f : Fin 3 → ℝ => MvPolynomial.eval f q) :=
          MvPolynomial.continuous_eval q
        exact h2.comp h1
      exact (isClosed_eq h_cont continuous_const).measurableSet
    have h2 : MeasurableSet (unitBall 3) := Metric.isClosed_closedBall.measurableSet
    exact h1.inter h2

  -- Step 5: coordinate directional area lower bound
  have h_coord : codimensionOneMeasure 3 Z ≤
      ∑ i : Fin 3, directionalSurfaceArea (eBasis i) q Z :=
    coordinate_directional_area_controls_surface q Z hZ_meas
      (fun x hx => hx.1) hsing_q

  -- Combine hArea and h_coord
  have h_trans : ENNReal.ofReal cutsBallConstant *
      codimensionOneMeasure 3 (unitSphere 3) ≤
      ∑ i : Fin 3, directionalSurfaceArea (eBasis i) q Z :=
    le_trans hArea h_coord

  -- Step 6: for each i, define R_i and D_i
  let R : Fin 3 → Set (Point 3) := fun i =>
    unitBall 3 ∩ {x | polynomialValue q x = 0 ∧ (polynomialGradient q x) i ≠ 0}
  let D : Fin 3 → Set (Point 3) := fun i => Z \ R i

  have hR_meas : ∀ i, MeasurableSet (R i) := by
    intro i
    have h1 : MeasurableSet (unitBall 3) := Metric.isClosed_closedBall.measurableSet
    have h_cont : Continuous (fun x : Point 3 => polynomialValue q x) := by
      have h1 : Continuous (EuclideanSpace.equiv (Fin 3) ℝ) :=
        (EuclideanSpace.equiv (Fin 3) ℝ).toLinearMap.continuous_of_finiteDimensional
      have h2 : Continuous (fun f : Fin 3 → ℝ => MvPolynomial.eval f q) :=
        MvPolynomial.continuous_eval q
      exact h2.comp h1
    have hgrad_cont : Continuous (fun x : Point 3 => (polynomialGradient q x) i) := by
      have h : Continuous (polynomialGradient q) := polynomialGradient_continuous q
      have hproj : Continuous (fun v : Point 3 => v i) := PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i
      exact hproj.comp h
    have h3 : MeasurableSet {x | polynomialValue q x = 0 ∧ (polynomialGradient q x) i ≠ 0} :=
      (isClosed_eq h_cont continuous_const).measurableSet.inter
        (isOpen_ne.preimage hgrad_cont).measurableSet
    exact h1.inter h3

  have hD_meas : ∀ i, MeasurableSet (D i) := by
    intro i
    exact hZ_meas.diff (hR_meas i)

  have hRD_disj : ∀ i, Disjoint (R i) (D i) := by
    intro i
    rw [Set.disjoint_left]
    intro x hxR hxD
    exact hxD.2 hxR

  have hZ_union : ∀ i, R i ∪ D i = Z := by
    intro i
    have h1 : R i ⊆ Z := by
      intro x hx
      have h2 : x ∈ unitBall 3 := hx.1
      have h3 : polynomialValue q x = 0 := hx.2.1
      exact ⟨h3, h2⟩
    rw [Set.union_sdiff_cancel h1]

  have hD_vanish : ∀ i, ∀ x ∈ D i, (polynomialGradient q x) i = 0 := by
    intro i x hx
    have h1 : x ∈ Z := hx.1
    have h2 : x ∉ R i := hx.2
    have h3 : x ∈ unitBall 3 := h1.2
    have h4 : polynomialValue q x = 0 := h1.1
    by_cases h5 : (polynomialGradient q x) i = 0
    · exact h5
    · exfalso
      exact h2 ⟨h3, h4, h5⟩

  -- Step 7: vanishing on D_i
  have h_vanish : ∀ i,
      directionalSurfaceArea (eBasis i) q (D i) = 0 ∧
      directionalSurfaceArea (b i) p (f '' (D i)) = 0 := by
    intro i
    exact directionalSurfaceArea_vanish_on_isingular
      p q A η z hη b ℓ hℓ hA hpq i (D i) (hD_meas i) (hD_vanish i)

  -- Step 8: affine identity on R_i
  have h_affine : ∀ i,
      ENNReal.ofReal (ℓ i) *
        directionalSurfaceArea (b i) p (f '' (R i)) =
      ENNReal.ofReal (η ^ 2 * |LinearMap.det (A : Point 3 →ₗ[ℝ] Point 3)|) *
        directionalSurfaceArea (eBasis i) q (R i) := by
    intro i
    exact direction_i_regular_affine_identity_on
      p q A η z hη b ℓ hℓ hA hpq i (unitBall 3) Metric.isClosed_closedBall.measurableSet

  -- Step 9: additivity to extend to full Z
  have h_q_add : ∀ i, directionalSurfaceArea (eBasis i) q Z =
      directionalSurfaceArea (eBasis i) q (R i) := by
    intro i
    have h_union : R i ∪ D i = Z := hZ_union i
    have h : directionalSurfaceArea (eBasis i) q (R i ∪ D i) =
        directionalSurfaceArea (eBasis i) q (R i) +
        directionalSurfaceArea (eBasis i) q (D i) :=
      lintegral_union (hD_meas i) (hRD_disj i)
    rw [h_union] at *
    rw [h, (h_vanish i).1, add_zero]

  have h_p_add : ∀ i, directionalSurfaceArea (b i) p (f '' Z) =
      directionalSurfaceArea (b i) p (f '' (R i)) := by
    intro i
    have h_inj : Function.Injective f := by
      intro x y h
      simp only [f] at h
      have h1 : η • A x = η • A y := by simpa using h
      have h2 : A x = A y := by
        simpa [smul_eq_zero, hη.ne'] using h1
      exact A.injective h2
    have h_disj : Disjoint (f '' (R i)) (f '' (D i)) :=
      (hRD_disj i).image (fun x _ y _ h => h_inj h) (subset_univ _) (subset_univ _)
    have h_image_union : f '' (R i) ∪ f '' (D i) = f '' Z := by
      rw [← Set.image_union, hZ_union i]
    have hfD_meas : MeasurableSet (f '' (D i)) := by
      let g : Point 3 → Point 3 := fun x => η⁻¹ • A.symm (x - z)
      have hgf : ∀ x, g (f x) = x := by
        intro x
        simp [g, f, map_smul, hη.ne']
      have hfg : ∀ y, f (g y) = y := by
        intro y
        simp [g, f, map_smul, hη.ne']
      have h1 : f '' (D i) = g ⁻¹' (D i) := by
        ext y
        simp only [Set.mem_image, Set.mem_preimage]
        constructor
        · rintro ⟨x, hx, rfl⟩
          have h2 : g (f x) = x := hgf x
          rw [h2]
          exact hx
        · intro hy
          exact ⟨g y, hy, hfg y⟩
      rw [h1]
      have h_cont : Continuous g := by
        have h1 : Continuous (fun x : Point 3 => x - z) := continuous_id.sub continuous_const
        have h3 : Continuous (A.symm : Point 3 → Point 3) :=
          A.symm.toContinuousLinearEquiv.continuous
        have h4 : Continuous (fun x : Point 3 => A.symm (x - z)) := h3.comp h1
        have h5 : Continuous (fun x : Point 3 => η⁻¹ • A.symm (x - z)) := h4.const_smul η⁻¹
        have h_eq : (fun x : Point 3 => η⁻¹ • A.symm (x - z)) = g := by
          funext x; rfl
        rw [h_eq] at h5
        exact h5
      exact (hD_meas i).preimage h_cont.measurable
    have h : directionalSurfaceArea (b i) p (f '' (R i) ∪ f '' (D i)) =
        directionalSurfaceArea (b i) p (f '' (R i)) +
        directionalSurfaceArea (b i) p (f '' (D i)) :=
      lintegral_union hfD_meas h_disj
    rw [h_image_union] at *
    rw [h, (h_vanish i).2, add_zero]

  -- Per-direction equality on full Z
  have h_per_i : ∀ i,
      ENNReal.ofReal (ℓ i) * directionalSurfaceArea (b i) p (f '' Z) =
      ENNReal.ofReal (η ^ 2 * |LinearMap.det (A : Point 3 →ₗ[ℝ] Point 3)|) *
        directionalSurfaceArea (eBasis i) q Z := by
    intro i
    rw [h_p_add i, h_q_add i]
    exact h_affine i

  -- Sum over i
  have h_sum :
      ∑ i : Fin 3, ENNReal.ofReal (ℓ i) * directionalSurfaceArea (b i) p (f '' Z) =
      ENNReal.ofReal (η ^ 2 * |LinearMap.det (A : Point 3 →ₗ[ℝ] Point 3)|) *
        ∑ i : Fin 3, directionalSurfaceArea (eBasis i) q Z := by
    calc
      ∑ i : Fin 3, ENNReal.ofReal (ℓ i) * directionalSurfaceArea (b i) p (f '' Z)
        = ∑ i : Fin 3, ENNReal.ofReal (η ^ 2 * |LinearMap.det (A : Point 3 →ₗ[ℝ] Point 3)|) *
            directionalSurfaceArea (eBasis i) q Z := by
          apply Finset.sum_congr rfl
          intro i _
          exact h_per_i i
      _ = ENNReal.ofReal (η ^ 2 * |LinearMap.det (A : Point 3 →ₗ[ℝ] Point 3)|) *
            ∑ i : Fin 3, directionalSurfaceArea (eBasis i) q Z := by
          rw [Finset.mul_sum]

  -- Step 10: image equality
  have h_image_eq : f '' Z = polynomialZeroSet p ∩ scaledEllipsoid A η z := by
    ext y
    simp only [Set.mem_image, Set.mem_inter_iff]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hx1 : polynomialValue q x = 0 := hx.1
      have hx2 : x ∈ unitBall 3 := hx.2
      have hval : polynomialValue p (f x) = 0 := by
        rw [hpq x, hx1]
      have hellip : f x ∈ scaledEllipsoid A η z := by
        have h_ball : ‖x‖ ≤ 1 := by simpa [unitBall, Metric.mem_closedBall] using hx2
        let v := η • x
        have hv1 : ‖v‖ ≤ η := by
          rw [show v = η • x from rfl, norm_smul, Real.norm_eq_abs, abs_of_pos hη]
          calc η * ‖x‖ ≤ η * 1 := by gcongr
            _ = η := by ring
        have hv2 : v ∈ Metric.closedBall (0 : Point 3) η := by
          simpa [Metric.mem_closedBall] using hv1
        have h3 : A v = η • A x := by
          simp [v, map_smul]
        have h4 : η • A x ∈ A '' Metric.closedBall (0 : Point 3) η := ⟨v, hv2, h3⟩
        have h5 : f x ∈ scaledEllipsoid A η z := by
          have h6 : f x = z +ᵥ (η • A x) := by simp [f]
          rw [h6]
          exact ⟨η • A x, h4, rfl⟩
        exact h5
      exact ⟨hval, hellip⟩
    · rintro ⟨hval, hellip⟩
      have h_scaled_inv : ∃ (x : Point 3), x ∈ unitBall 3 ∧ f x = y := by
        simp only [scaledEllipsoid, Set.mem_vadd_set] at hellip
        rcases hellip with ⟨w, hw, h_eq1⟩
        rcases hw with ⟨v, hv, h_eq2⟩
        have h_ball : ‖v‖ ≤ η := by simpa [Metric.mem_closedBall] using hv
        let x := η⁻¹ • v
        have h_inv_pos : 0 < η⁻¹ := by positivity
        have hy1 : ‖x‖ ≤ 1 := by
          rw [show x = η⁻¹ • v from rfl, norm_smul, Real.norm_eq_abs, abs_of_pos h_inv_pos]
          calc η⁻¹ * ‖v‖ ≤ η⁻¹ * η := by gcongr
            _ = 1 := by field_simp [hη.ne']
        have hy2 : x ∈ unitBall 3 := by simpa [unitBall, Metric.mem_closedBall] using hy1
        have h2 : η • A x = A v := by
          have h : η • A x = η • A (η⁻¹ • v) := by rfl
          rw [h]
          have h' : A (η⁻¹ • v) = η⁻¹ • A v := by rw [map_smul]
          rw [h']
          have h'' : η • (η⁻¹ • A v) = A v := by
            simp [smul_smul, hη.ne']
          exact h''
        have hfy : f x = y := by
          have h1 : f x = z + η • A x := by simp [f]
          rw [h1, h2]
          have h4 : z + A v = z +ᵥ A v := by rfl
          rw [h4, h_eq2, h_eq1]
        exact ⟨x, hy2, hfy⟩
      rcases h_scaled_inv with ⟨x, hx_ball, rfl⟩
      have hq_val : polynomialValue q x = 0 := by
        rw [← hpq x]
        exact hval
      exact ⟨x, ⟨hq_val, hx_ball⟩, rfl⟩

  -- Step 11: determinant product
  have h_det : |LinearMap.det (A : Point 3 →ₗ[ℝ] Point 3)| = ∏ i : Fin 3, ℓ i :=
    abs_det_eq_product A b ℓ hℓ hA

  have h_prod_pos : 0 < ∏ i : Fin 3, ℓ i := by
    apply Finset.prod_pos
    intro i _
    exact hℓ i
  have h_pos2 : 0 ≤ η ^ 2 * ∏ i : Fin 3, ℓ i := by
    exact mul_nonneg (sq_nonneg η) h_prod_pos.le

  -- Final calc
  calc
    ENNReal.ofReal cutsBallConstant *
        ENNReal.ofReal (η ^ 2 * ∏ i, ℓ i) *
        codimensionOneMeasure 3 (unitSphere 3)
      = ENNReal.ofReal (η ^ 2 * ∏ i, ℓ i) *
          (ENNReal.ofReal cutsBallConstant * codimensionOneMeasure 3 (unitSphere 3)) := by
        ring
    _ = ENNReal.ofReal (η ^ 2 * |LinearMap.det (A : Point 3 →ₗ[ℝ] Point 3)|) *
          (ENNReal.ofReal cutsBallConstant * codimensionOneMeasure 3 (unitSphere 3)) := by
        rw [h_det]
    _ ≤ ENNReal.ofReal (η ^ 2 * |LinearMap.det (A : Point 3 →ₗ[ℝ] Point 3)|) *
          ∑ i : Fin 3, directionalSurfaceArea (eBasis i) q Z := by
        exact (mul_le_mul_right h_trans) _
    _ = ∑ i : Fin 3, ENNReal.ofReal (ℓ i) *
          directionalSurfaceArea (b i) p (f '' Z) := h_sum.symm
    _ = ∑ i : Fin 3, ENNReal.ofReal (ℓ i) *
          directionalSurfaceArea (b i) p
            (polynomialZeroSet p ∩ scaledEllipsoid A η z) := by
        rw [h_image_eq]

end Kakeya.CV
