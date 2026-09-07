import MyLeanRepo.Kakeya.CV.PolynomialCylinder.AffinePullback
import Mathlib.Topology.MetricSpace.Antilipschitz
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.Module.LinearMap.Polynomial
import Mathlib.Analysis.InnerProductSpace.PiL2


/-!
# Affine tools for the ManyBisections proof
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Kakeya.CV

/-- Construct an AntilipschitzWith bound from a norm lower bound on a linear map. -/
lemma antilipschitz_of_lower_bound (m : ℝ) (hm : 0 < m)
    (A : Point 3 ≃ₗ[ℝ] Point 3) (hA : ∀ x, m * ‖x‖ ≤ ‖A x‖) :
    AntilipschitzWith (⟨m⁻¹, by positivity⟩ : ℝ≥0) (A : Point 3 → Point 3) := by
  let K : ℝ≥0 := ⟨m⁻¹, by positivity⟩
  have hK : (K : ℝ) = m⁻¹ := by
    unfold K; exact rfl
  have h : ∀ (x y : Point 3), dist x y ≤ (K : ℝ) * dist (A x) (A y) := by
    intro x y
    have h₁ : dist x y = ‖x - y‖ := by simp [dist_eq_norm]
    have h₂ : dist (A x) (A y) = ‖A (x - y)‖ := by
      simp [dist_eq_norm, map_sub]
    rw [h₁, h₂, hK]
    have h₃ : m * ‖x - y‖ ≤ ‖A (x - y)‖ := hA (x - y)
    calc
      ‖x - y‖ = m⁻¹ * (m * ‖x - y‖) := by field_simp [hm.ne'] <;> ring
      _ ≤ m⁻¹ * ‖A (x - y)‖ := by gcongr
  exact AntilipschitzWith.of_le_mul_dist h

/-- Hausdorff measure lower bound under an affine map y ↦ z + η • A y. -/
lemma hausdorff_affine_lower_bound (m η : ℝ) (hm : 0 < m) (hη : 0 < η)
    (A : Point 3 ≃ₗ[ℝ] Point 3) (hA : ∀ x, m * ‖x‖ ≤ ‖A x‖)
    (z : Point 3) (s : Set (Point 3)) :
    ENNReal.ofReal ((η * m) ^ 2) * codimensionOneMeasure 3 s ≤
      codimensionOneMeasure 3 ((fun y : Point 3 => z + η • A y) '' s) := by
  let f : Point 3 → Point 3 := fun y => z + η • A y
  let c : ℝ := η * m
  have hc_pos : 0 < c := mul_pos hη hm
  let K : ℝ≥0 := ⟨c⁻¹, by positivity⟩
  have hK : (K : ℝ) = c⁻¹ := by
    exact Subtype.coe_mk c⁻¹ (by positivity)
  have h_antilipschitz : AntilipschitzWith K f := by
    refine' AntilipschitzWith.of_le_mul_dist _
    intro x y
    have h_dist : c * dist x y ≤ dist (f x) (f y) := by
      have h1 : f x - f y = η • A (x - y) := by
        simp [f, map_sub, smul_sub] <;> abel
      have h2 : dist (f x) (f y) = η * ‖A (x - y)‖ := by
        rw [dist_eq_norm, h1, norm_smul, Real.norm_eq_abs, abs_of_pos hη] <;> ring
      rw [h2, dist_eq_norm]
      have h2 : m * ‖x - y‖ ≤ ‖A (x - y)‖ := hA (x - y)
      calc η * ‖A (x - y)‖
        ≥ η * (m * ‖x - y‖) := by exact mul_le_mul_of_nonneg_left h2 (by linarith)
      _ = c * ‖x - y‖ := by ring
    have h_goal : dist x y ≤ c⁻¹ * dist (f x) (f y) := by
      calc dist x y
        = c⁻¹ * (c * dist x y) := by field_simp [hc_pos.ne'] <;> ring
      _ ≤ c⁻¹ * dist (f x) (f y) := by exact mul_le_mul_of_nonneg_left h_dist (by positivity)
    rw [hK]
    exact h_goal
  let d : ℝ := (3 : ℝ) - 1
  have hd_nonneg : 0 ≤ d := by norm_num
  have h_main2 : codimensionOneMeasure 3 s ≤ (K : ℝ≥0∞) ^ d * codimensionOneMeasure 3 (f '' s) := by
    simpa [codimensionOneMeasure] using h_antilipschitz.le_hausdorffMeasure_image hd_nonneg s
  have hK2 : (K : ℝ≥0∞) ^ d = ENNReal.ofReal (c⁻¹ ^ 2) := by
    have hd : d = (2 : ℝ) := by norm_num
    rw [hd]
    have h1 : (K : ℝ≥0∞) = ENNReal.ofReal (K : ℝ) := ENNReal.coe_nnreal_eq K
    rw [h1, hK]
    have h_rpow_nat : ENNReal.ofReal c⁻¹ ^ (2 : ℝ) = (ENNReal.ofReal c⁻¹) ^ 2 :=
      ENNReal.rpow_natCast (ENNReal.ofReal c⁻¹) 2
    rw [h_rpow_nat]
    have h2 : (ENNReal.ofReal c⁻¹) ^ 2 = ENNReal.ofReal (c⁻¹ ^ 2) := by
      rw [← ENNReal.ofReal_pow (by positivity)] <;> rfl
    exact h2
  rw [hK2] at h_main2
  have h_c2_nonneg : 0 ≤ c ^ 2 := by positivity
  have h_mul_cancel : ENNReal.ofReal (c ^ 2) * ENNReal.ofReal (c⁻¹ ^ 2) = 1 := by
    have h1 : c ^ 2 * c⁻¹ ^ 2 = (1 : ℝ) := by
      field_simp [hc_pos.ne'] <;> ring
    have h2 : ENNReal.ofReal (c ^ 2) * ENNReal.ofReal (c⁻¹ ^ 2) = ENNReal.ofReal (c ^ 2 * c⁻¹ ^ 2) := by
      rw [ENNReal.ofReal_mul h_c2_nonneg]
    rw [h2, h1] <;> simp
  have h_final : ENNReal.ofReal (c ^ 2) * codimensionOneMeasure 3 s ≤ codimensionOneMeasure 3 (f '' s) := by
    have h9 : ENNReal.ofReal (c ^ 2) * codimensionOneMeasure 3 s ≤
        ENNReal.ofReal (c ^ 2) * (ENNReal.ofReal (c⁻¹ ^ 2) * codimensionOneMeasure 3 (f '' s)) :=
      mul_le_mul_left' h_main2 _
    have h10 : ENNReal.ofReal (c ^ 2) * (ENNReal.ofReal (c⁻¹ ^ 2) * codimensionOneMeasure 3 (f '' s)) =
        (ENNReal.ofReal (c ^ 2) * ENNReal.ofReal (c⁻¹ ^ 2)) * codimensionOneMeasure 3 (f '' s) := by
      rw [mul_assoc]
    rw [h10] at h9
    rw [h_mul_cancel] at h9
    simpa using h9
  have h_c2 : ENNReal.ofReal ((η * m) ^ 2) = ENNReal.ofReal (c ^ 2) := by
    have h : (η * m) ^ 2 = c ^ 2 := by dsimp only [c] <;> ring
    rw [h]
  rw [h_c2]
  exact h_final

/-- Volume of a scaled ellipsoid. -/
lemma volume_affine_ball (A : Point 3 ≃ₗ[ℝ] Point 3) (η : ℝ) (hη : 0 < η)
    (z : Point 3) :
    volume (scaledEllipsoid A η z) =
      ENNReal.ofReal (η ^ 3 * |LinearMap.det (A : Point 3 →ₗ[ℝ] Point 3)|) * volume (unitBall 3) := by
  let A' := A.toContinuousLinearEquiv
  let ηunit : ℝˣ := Units.mk0 η hη.ne'
  let smulMap : Point 3 ≃L[ℝ] Point 3 := ContinuousLinearEquiv.smulLeft ηunit
  have hsmul_apply : ∀ (x : Point 3), (smulMap : Point 3 → Point 3) x = η • x := by
    intro x
    change (ηunit : ℝ) • x = η • x
    <;> rfl
  have hdet_smul : LinearMap.det (smulMap : Point 3 →ₗ[ℝ] Point 3) = η ^ 3 := by
    have h : (smulMap : Point 3 →ₗ[ℝ] Point 3) = η • LinearMap.id := by
      apply LinearMap.ext
      intro x
      have h1 : (smulMap : Point 3 →ₗ[ℝ] Point 3) x = (smulMap : Point 3 → Point 3) x := by rfl
      rw [h1, hsmul_apply x] <;> rfl
    rw [h, LinearMap.det_smul, LinearMap.det_id]
    <;> simp <;> ring
  have h1 : Metric.closedBall (0 : Point 3) η = smulMap '' unitBall 3 := by
    ext x
    simp only [Metric.mem_closedBall, unitBall, Set.mem_image, dist_zero_right]
    constructor
    · intro hx
      let y := η⁻¹ • x
      have h_inv_pos : 0 < η⁻¹ := by positivity
      have hynorm : ‖y‖ ≤ 1 := by
        rw [show y = η⁻¹ • x from rfl, norm_smul, Real.norm_eq_abs, abs_of_pos h_inv_pos]
        calc η⁻¹ * ‖x‖ ≤ η⁻¹ * η := by gcongr
          _ = 1 := by field_simp [hη.ne'] <;> ring
      have h3 : smulMap y = x := by
        rw [hsmul_apply y]
        simp [y, hη.ne'] <;> abel
      exact ⟨y, hynorm, h3⟩
    · rintro ⟨y, hy, rfl⟩
      rw [hsmul_apply y, norm_smul, Real.norm_eq_abs, abs_of_pos hη]
      calc η * ‖y‖ ≤ η * 1 := by gcongr
        _ = η := by ring
  have h_translate : ∀ (s : Set (Point 3)), MeasurableSet s → volume ((fun x => z + x) '' s) = volume s := by
    intro s hs
    let t : Point 3 → Point 3 := fun x => z + x
    let t_inv : Point 3 → Point 3 := fun x => -z + x
    have hmp : MeasurePreserving t_inv := measurePreserving_add_left volume (-z)
    have h2 : t '' s = t_inv ⁻¹' s := by
      ext y
      simp only [Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨x, hx, rfl⟩
        have h4 : t_inv (t x) = x := by
          simp [t, t_inv] <;> abel
        rw [h4]
        exact hx
      · intro hy
        have h3 : t (t_inv y) = y := by
          simp [t, t_inv] <;> abel
        exact ⟨t_inv y, hy, h3⟩
    rw [h2]
    exact hmp.measure_preimage hs.nullMeasurableSet
  have h_comm : ∀ (y : Point 3), smulMap (A y) = A (smulMap y) := by
    intro y
    rw [hsmul_apply (A y), hsmul_apply y, map_smul] <;> rfl
  have h_image_comp : A '' (smulMap '' unitBall 3) = smulMap '' (A '' unitBall 3) := by
    ext x
    simp only [Set.mem_image]
    constructor
    · rintro ⟨w, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨A y, ⟨y, hy, rfl⟩, h_comm y⟩
    · rintro ⟨v, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨smulMap y, ⟨y, hy, rfl⟩, (h_comm y).symm⟩
  have h5 : volume (smulMap '' (A '' unitBall 3)) =
      ENNReal.ofReal (η ^ 3) * volume (A '' unitBall 3) := by
    have h : volume (smulMap '' (A '' unitBall 3)) =
        ENNReal.ofReal |LinearMap.det (smulMap : Point 3 →ₗ[ℝ] Point 3)| * volume (A '' unitBall 3) :=
      MeasureTheory.Measure.addHaar_image_continuousLinearEquiv volume smulMap (A '' unitBall 3)
    rw [h, hdet_smul]
    have h_abs : |η ^ 3| = η ^ 3 := by rw [abs_of_pos (pow_pos hη 3)]
    rw [h_abs] <;> ring
  have h6 : volume (A '' unitBall 3) =
      ENNReal.ofReal |LinearMap.det (A : Point 3 →ₗ[ℝ] Point 3)| * volume (unitBall 3) :=
    MeasureTheory.Measure.addHaar_image_continuousLinearEquiv volume A' (unitBall 3)
  have h7 : ENNReal.ofReal (η ^ 3) * ENNReal.ofReal |LinearMap.det (A : Point 3 →ₗ[ℝ] Point 3)| =
      ENNReal.ofReal (η ^ 3 * |LinearMap.det (A : Point 3 →ₗ[ℝ] Point 3)|) := by
    rw [← ENNReal.ofReal_mul] <;> positivity
  have h_set_eq : (fun x : Point 3 => z + x) '' (A '' Metric.closedBall (0 : Point 3) η) =
      scaledEllipsoid A η z := by
    ext w
    simp [scaledEllipsoid, Set.mem_vadd_set]
    <;> aesop
  calc
    volume (scaledEllipsoid A η z)
      = volume ((fun x => z + x) '' (A '' Metric.closedBall (0 : Point 3) η)) := by
        rw [h_set_eq]
    _ = volume (A '' Metric.closedBall (0 : Point 3) η) := h_translate _ ((isCompact_closedBall (0 : Point 3) η).image A'.continuous).measurableSet
    _ = volume (A '' (smulMap '' unitBall 3)) := by rw [h1]
    _ = volume (smulMap '' (A '' unitBall 3)) := by rw [h_image_comp]
    _ = ENNReal.ofReal (η ^ 3) * volume (A '' unitBall 3) := h5
    _ = ENNReal.ofReal (η ^ 3) * (ENNReal.ofReal |LinearMap.det (A : Point 3 →ₗ[ℝ] Point 3)| * volume (unitBall 3)) := by rw [h6]
    _ = ENNReal.ofReal (η ^ 3 * |LinearMap.det (A : Point 3 →ₗ[ℝ] Point 3)|) * volume (unitBall 3) := by
        have h8 : ENNReal.ofReal (η ^ 3) * (ENNReal.ofReal |LinearMap.det (A : Point 3 →ₗ[ℝ] Point 3)| * volume (unitBall 3)) =
            (ENNReal.ofReal (η ^ 3) * ENNReal.ofReal |LinearMap.det (A : Point 3 →ₗ[ℝ] Point 3)|) * volume (unitBall 3) := by
          rw [mul_assoc]
        rw [h8, h7]

/-- Bisection is preserved under affine pullback. -/
lemma bisection_pullback (p : MvPolynomial (Fin 3) ℝ) (z : Point 3) (η : ℝ) (hη : 0 < η)
    (A : Point 3 ≃ₗ[ℝ] Point 3)
    (hBisect : PolynomialBisects p (scaledEllipsoid A η z)) :
    volume (unitBall 3 ∩ {y | polynomialValue (pullbackPolynomial p z η A) y < 0}) =
    volume (unitBall 3 ∩ {y | 0 < polynomialValue (pullbackPolynomial p z η A) y}) := by
  let q := pullbackPolynomial p z η A
  let g : Point 3 → Point 3 := fun y => η • A y
  let f : Point 3 → Point 3 := fun y => z + g y
  let g' : Point 3 ≃L[ℝ] Point 3 :=
    { toFun := g
      invFun := fun x => η⁻¹ • A.symm x
      left_inv := by intro x; simp [g, hη.ne'] <;> abel
      right_inv := by intro x; simp [g, hη.ne'] <;> abel
      map_add' := by intro x y; simp [g, add_smul] <;> abel
      map_smul' := by
        intro c x
        dsimp only [g]
        rw [map_smul]
        exact smul_comm η c (A x)
      continuous_toFun := by
        have hA_cont : Continuous A := A.toLinearMap.continuous_of_finiteDimensional
        exact hA_cont.const_smul _
      continuous_invFun := by
        have hA_symm_cont : Continuous A.symm := A.symm.toLinearMap.continuous_of_finiteDimensional
        exact hA_symm_cont.const_smul _ }
  have h_eval : ∀ y, polynomialValue q y = polynomialValue p (f y) := by
    intro y
    exact pullbackPolynomial_eval p z η A y
  have h_scaled_mem : ∀ (y : Point 3), y ∈ unitBall 3 → f y ∈ scaledEllipsoid A η z := by
    intro y hy
    have h_ball : ‖y‖ ≤ 1 := by simpa [unitBall, Metric.mem_closedBall] using hy
    let v := η • y
    have hv1 : ‖v‖ ≤ η := by
      rw [show v = η • y from rfl, norm_smul, Real.norm_eq_abs, abs_of_pos hη]
      calc η * ‖y‖ ≤ η * 1 := by gcongr
        _ = η := by ring
    have hv2 : v ∈ Metric.closedBall (0 : Point 3) η := by
      simpa [Metric.mem_closedBall] using hv1
    have h3 : A v = g y := by
      simp [v, g, map_smul] <;> ring
    have h4 : g y ∈ A '' Metric.closedBall (0 : Point 3) η := ⟨v, hv2, h3⟩
    have h5 : f y ∈ scaledEllipsoid A η z := by
      have h6 : f y = z +ᵥ g y := by
        simp [f] <;> abel
      rw [h6]
      exact ⟨g y, h4, rfl⟩
    exact h5
  have h_scaled_inv : ∀ (x : Point 3), x ∈ scaledEllipsoid A η z →
      ∃ (y : Point 3), y ∈ unitBall 3 ∧ f y = x := by
    intro x hx
    simp only [scaledEllipsoid, Set.mem_vadd_set] at hx
    rcases hx with ⟨w, hw, h_eq1⟩
    rcases hw with ⟨v, hv, h_eq2⟩
    have h_ball : ‖v‖ ≤ η := by simpa [Metric.mem_closedBall] using hv
    let y := η⁻¹ • v
    have h_inv_pos : 0 < η⁻¹ := by positivity
    have hy1 : ‖y‖ ≤ 1 := by
      rw [show y = η⁻¹ • v from rfl, norm_smul, Real.norm_eq_abs, abs_of_pos h_inv_pos]
      calc η⁻¹ * ‖v‖ ≤ η⁻¹ * η := by gcongr
        _ = 1 := by field_simp [hη.ne'] <;> ring
    have hy2 : y ∈ unitBall 3 := by
      simpa [unitBall, Metric.mem_closedBall] using hy1
    have h2 : g y = A v := by
      have h : g y = η • A (η⁻¹ • v) := by simp [g, y]
      rw [h]
      have h' : A (η⁻¹ • v) = η⁻¹ • A v := by rw [map_smul] <;> rfl
      rw [h']
      have h'' : η • (η⁻¹ • A v) = A v := by
        simp [smul_smul, hη.ne'] <;> ring
      exact h''
    have hfy : f y = x := by
      have h1 : f y = z + g y := by simp [f] <;> abel
      rw [h1, h2]
      have h4 : z + A v = z +ᵥ A v := by rfl
      rw [h4, h_eq2, h_eq1]
    exact ⟨y, hy2, hfy⟩
  let S_neg := unitBall 3 ∩ {y | polynomialValue q y < 0}
  let S_pos := unitBall 3 ∩ {y | 0 < polynomialValue q y}
  have hcont_q : Continuous (fun y => polynomialValue q y) := by
    have h1 : Continuous (fun y : Point 3 => (fun i : Fin 3 => y i)) :=
      PiLp.continuous_ofLp 2 fun x => ℝ
    have h2 : Continuous (fun x : Fin 3 → ℝ => MvPolynomial.eval x q) := MvPolynomial.continuous_eval q
    exact h2.comp h1
  have h_ball_closed : IsClosed (unitBall 3) := Metric.isClosed_closedBall
  have hS_neg_meas : MeasurableSet S_neg :=
    h_ball_closed.measurableSet.inter (measurableSet_lt hcont_q.measurable measurable_const)
  have hS_pos_meas : MeasurableSet S_pos :=
    h_ball_closed.measurableSet.inter (measurableSet_lt measurable_const hcont_q.measurable)
  have h_image_preimage : ∀ (s : Set (Point 3)), g '' s = g'.symm ⁻¹' s := by
    intro s
    ext y
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have h_eq1 : g' x = g x := by rfl
      have h : g'.symm (g x) = x := by
        rw [← h_eq1]
        exact g'.left_inv x
      rw [h]
      exact hx
    · intro hy
      refine ⟨g'.symm y, hy, ?_⟩
      have h_eq : g (g'.symm y) = g' (g'.symm y) := by rfl
      rw [h_eq]
      exact g'.right_inv y
  have hgS_neg_meas : MeasurableSet (g '' S_neg) := by
    rw [h_image_preimage S_neg]
    exact hS_neg_meas.preimage g'.symm.continuous.measurable
  have hgS_pos_meas : MeasurableSet (g '' S_pos) := by
    rw [h_image_preimage S_pos]
    exact hS_pos_meas.preimage g'.symm.continuous.measurable
  have h_image_neg : f '' S_neg = scaledEllipsoid A η z ∩ {x | polynomialValue p x < 0} := by
    ext x
    simp only [S_neg, Set.mem_image, Set.mem_inter_iff]
    constructor
    · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
      have hfy : f y ∈ scaledEllipsoid A η z := h_scaled_mem y hy1
      have hsign : polynomialValue p (f y) < 0 := by rw [← h_eval y] <;> exact hy2
      exact ⟨hfy, hsign⟩
    · rintro ⟨h1, h2⟩
      rcases h_scaled_inv x h1 with ⟨y, hy1, rfl⟩
      have h4 : polynomialValue q y < 0 := by rw [h_eval y] <;> exact h2
      exact ⟨y, ⟨hy1, h4⟩, rfl⟩
  have h_image_pos : f '' S_pos = scaledEllipsoid A η z ∩ {x | 0 < polynomialValue p x} := by
    ext x
    simp only [S_pos, Set.mem_image, Set.mem_inter_iff]
    constructor
    · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
      have hfy : f y ∈ scaledEllipsoid A η z := h_scaled_mem y hy1
      have hsign : 0 < polynomialValue p (f y) := by rw [← h_eval y] <;> exact hy2
      exact ⟨hfy, hsign⟩
    · rintro ⟨h1, h2⟩
      rcases h_scaled_inv x h1 with ⟨y, hy1, rfl⟩
      have h4 : 0 < polynomialValue q y := by rw [h_eval y] <;> exact h2
      exact ⟨y, ⟨hy1, h4⟩, rfl⟩
  let detFactor := ENNReal.ofReal (η ^ 3 * |LinearMap.det (A : Point 3 →ₗ[ℝ] Point 3)|)
  have hdet_A_ne_zero : LinearMap.det (A : Point 3 →ₗ[ℝ] Point 3) ≠ 0 := by
    have h : IsUnit (LinearMap.det (A : Point 3 →ₗ[ℝ] Point 3)) :=
      LinearEquiv.isUnit_det' A
    exact h.ne_zero
  have hdet_abs_pos : 0 < |LinearMap.det (A : Point 3 →ₗ[ℝ] Point 3)| := abs_pos.mpr hdet_A_ne_zero
  have hdet_pos : 0 < detFactor := by
    apply ENNReal.ofReal_pos.mpr
    exact mul_pos (pow_pos hη 3) hdet_abs_pos
  have h_translate : ∀ (s : Set (Point 3)), MeasurableSet s → volume ((fun x => z + x) '' s) = volume s := by
    intro s hs
    let t : Point 3 → Point 3 := fun x => z + x
    let t_inv : Point 3 → Point 3 := fun x => -z + x
    have hmp : MeasurePreserving t_inv := measurePreserving_add_left volume (-z)
    have h2 : t '' s = t_inv ⁻¹' s := by
      ext y
      simp only [Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨x, hx, rfl⟩
        have h4 : t_inv (t x) = x := by
          simp [t, t_inv] <;> abel
        rw [h4]
        exact hx
      · intro hy
        have h3 : t (t_inv y) = y := by
          simp [t, t_inv] <;> abel
        exact ⟨t_inv y, hy, h3⟩
    rw [h2]
    exact hmp.measure_preimage hs.nullMeasurableSet
  have h_f_image : ∀ (s : Set (Point 3)), f '' s = (fun x => z + x) '' (g '' s) := by
    intro s
    ext x
    simp only [f, Set.mem_image, Function.comp_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨g y, ⟨y, hy, rfl⟩, rfl⟩
    · rintro ⟨w, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨y, hy, rfl⟩
  have hdet_g : LinearMap.det (g' : Point 3 →ₗ[ℝ] Point 3) =
      η ^ 3 * LinearMap.det (A : Point 3 →ₗ[ℝ] Point 3) := by
    let smulMap2 : Point 3 ≃L[ℝ] Point 3 := ContinuousLinearEquiv.smulLeft (Units.mk0 η hη.ne')
    have hsmul : ∀ (x : Point 3), (smulMap2 : Point 3 → Point 3) x = η • x := by
      intro x; change (Units.mk0 η hη.ne' : ℝ) • x = η • x <;> rfl
    have hdet_smul2 : LinearMap.det (smulMap2 : Point 3 →ₗ[ℝ] Point 3) = η ^ 3 := by
      have h : (smulMap2 : Point 3 →ₗ[ℝ] Point 3) = η • LinearMap.id := by
        apply LinearMap.ext; intro x
        have h1 : (smulMap2 : Point 3 →ₗ[ℝ] Point 3) x = (smulMap2 : Point 3 → Point 3) x := by rfl
        rw [h1, hsmul x] <;> rfl
      rw [h, LinearMap.det_smul, LinearMap.det_id] <;> simp <;> ring
    have h_comp : (g' : Point 3 →ₗ[ℝ] Point 3) = (smulMap2 : Point 3 →ₗ[ℝ] Point 3).comp (A : Point 3 →ₗ[ℝ] Point 3) := by
      apply LinearMap.ext
      intro x
      have h1 : (g' : Point 3 → Point 3) x = η • A x := by
        change g x = η • A x; simp [g]
      have h2 : ((smulMap2 : Point 3 →ₗ[ℝ] Point 3).comp (A : Point 3 →ₗ[ℝ] Point 3)) x = η • A x := by
        simp [hsmul] <;> rfl
      exact h1.trans h2.symm
    rw [h_comp, LinearMap.det_comp, hdet_smul2] <;> ring
  have h_abs : |η ^ 3 * LinearMap.det (A : Point 3 →ₗ[ℝ] Point 3)| =
      η ^ 3 * |LinearMap.det (A : Point 3 →ₗ[ℝ] Point 3)| := by
    rw [abs_mul, abs_pow, abs_of_pos hη] <;> ring
  have hvol_g_neg : volume (g '' S_neg) = detFactor * volume S_neg := by
    have h : volume (g '' S_neg) =
        ENNReal.ofReal |LinearMap.det (g' : Point 3 →ₗ[ℝ] Point 3)| * volume S_neg :=
      MeasureTheory.Measure.addHaar_image_continuousLinearEquiv volume g' S_neg
    rw [h, hdet_g, h_abs] <;> rfl
  have hvol_g_pos : volume (g '' S_pos) = detFactor * volume S_pos := by
    have h : volume (g '' S_pos) =
        ENNReal.ofReal |LinearMap.det (g' : Point 3 →ₗ[ℝ] Point 3)| * volume S_pos :=
      MeasureTheory.Measure.addHaar_image_continuousLinearEquiv volume g' S_pos
    rw [h, hdet_g, h_abs] <;> rfl
  have hvol_neg : volume (f '' S_neg) = detFactor * volume S_neg := by
    rw [h_f_image S_neg, h_translate (g '' S_neg) hgS_neg_meas, hvol_g_neg]
  have hvol_pos : volume (f '' S_pos) = detFactor * volume S_pos := by
    rw [h_f_image S_pos, h_translate (g '' S_pos) hgS_pos_meas, hvol_g_pos]
  have hBisect' : volume (scaledEllipsoid A η z ∩ {x | polynomialValue p x < 0}) =
      volume (scaledEllipsoid A η z ∩ {x | 0 < polynomialValue p x}) := by
    simpa [PolynomialBisects] using hBisect
  rw [← h_image_neg, ← h_image_pos] at hBisect'
  rw [hvol_neg, hvol_pos] at hBisect'
  have hdet_finite : detFactor ≠ ⊤ := ENNReal.ofReal_lt_top.ne
  exact (ENNReal.mul_right_inj hdet_pos.ne' hdet_finite).mp hBisect'

end Kakeya.CV
