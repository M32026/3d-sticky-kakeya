import MyLeanRepo.Kakeya.Assouad.WZ1.SmoothedMeasure
import MyLeanRepo.Kakeya.Assouad.WZ1.NonConcentrationToThinTubes

/-!
# Smoothed measures satisfy measure thin tubes

If G₂ has uniform strip non-concentration for widths r ≥ δ, then the
smoothed measure of G₂ (convolution with a uniform ball of radius δ)
satisfies `HasMeasureThinTubes` for all r > 0.
-/

noncomputable section

open MeasureTheory Set Metric

open scoped ENNReal NNReal

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/--
Volume bound for intersection of a ball and a strip.

For any unit vector n and offset t,
`volume(B(0,ρ) ∩ {y | |inner y n - t| ≤ r}) ≤ 4 * ρ * r`.
-/
lemma ball_strip_volume_bound
    {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r)
    (n : Point2) (hn : ‖n‖ = 1) (t : ℝ) :
    volume (Metric.ball (0 : Point2) ρ ∩ {y : Point2 | |inner ℝ y n - t| ≤ r}) ≤
      ENNReal.ofReal (4 * ρ * r) := by
  let a : ℝ := n 0
  let b : ℝ := n 1
  have h_inner_form : ∀ (x y : Point2), inner ℝ x y = x 0 * y 0 + x 1 * y 1 := by
    intro x y
    have h : inner ℝ x y = ∑ i : Fin 2, x i * y i := by
      rw [PiLp.inner_apply] <;> simp [mul_comm]
    rw [h]
    have h2 : (∑ i : Fin 2, x i * y i) = x 0 * y 0 + x 1 * y 1 := by
      simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] <;> ring
    exact h2
  have h_norm_self : ∀ (x : Point2), inner ℝ x x = ‖x‖ ^ 2 := by
    intro x
    simpa using inner_self_eq_norm_sq_to_K
  have h_norm2 : ‖n‖ ^ 2 = a^2 + b^2 := by
    have h1 : inner ℝ n n = ‖n‖ ^ 2 := h_norm_self n
    have h2 : inner ℝ n n = a^2 + b^2 := by
      have h3 : inner ℝ n n = n 0 * n 0 + n 1 * n 1 := h_inner_form n n
      have h4 : n 0 * n 0 + n 1 * n 1 = a^2 + b^2 := by
        dsimp only [a, b] <;> ring
      rw [h3, h4]
    linarith
  have hab : a^2 + b^2 = 1 := by
    have h4 : (‖n‖ ^ 2 : ℝ) = 1 := by rw [hn] <;> norm_num
    linarith [h_norm2]
  let e0 : Point2 := EuclideanSpace.single 0 1
  let e1 : Point2 := EuclideanSpace.single 1 1
  let e : Point2 → Point2 := fun z =>
    (a * z 0 + b * z 1) • e0 + (b * z 0 - a * z 1) • e1
  have h_e_comp0 : ∀ z : Point2, e z 0 = a * z 0 + b * z 1 := by
    intro z; simp [e, e0, e1, EuclideanSpace.single_apply] <;> ring
  have h_e_comp1 : ∀ z : Point2, e z 1 = b * z 0 - a * z 1 := by
    intro z; simp [e, e0, e1, EuclideanSpace.single_apply] <;> ring
  have h_e_add : ∀ (x y : Point2), e (x + y) = e x + e y := by
    intro x y; ext i; fin_cases i <;> simp [h_e_comp0, h_e_comp1, Pi.add_apply] <;> ring
  have h_e_smul : ∀ (c : ℝ) (x : Point2), e (c • x) = c • e x := by
    intro c x; ext i; fin_cases i <;> simp [h_e_comp0, h_e_comp1, Pi.smul_apply] <;> ring
  let e_lm : Point2 →ₗ[ℝ] Point2 :=
    { toFun := e, map_add' := h_e_add, map_smul' := h_e_smul }
  have h_preserves_inner : ∀ (x y : Point2), inner ℝ (e_lm x) (e_lm y) = inner ℝ x y := by
    intro x y
    rw [h_inner_form (e_lm x) (e_lm y), h_inner_form x y]
    have h9 : e_lm x 0 = a * x 0 + b * x 1 := h_e_comp0 x
    have h10 : e_lm x 1 = b * x 0 - a * x 1 := h_e_comp1 x
    have h11 : e_lm y 0 = a * y 0 + b * y 1 := h_e_comp0 y
    have h12 : e_lm y 1 = b * y 0 - a * y 1 := h_e_comp1 y
    rw [h9, h10, h11, h12]
    have h_alg : (a * x 0 + b * x 1) * (a * y 0 + b * y 1) +
        (b * x 0 - a * x 1) * (b * y 0 - a * y 1) =
        (a^2 + b^2) * (x 0 * y 0 + x 1 * y 1) := by ring
    rw [h_alg, hab] <;> ring
  let e_li : Point2 →ₗᵢ[ℝ] Point2 :=
    LinearMap.isometryOfInner e_lm h_preserves_inner
  have h_e_invol : ∀ (z : Point2), e_li (e_li z) = z := by
    intro z
    ext i
    fin_cases i
    · have h : e_li (e_li z) 0 = z 0 := by
        have h1 : e_li (e_li z) 0 = a * (e_li z) 0 + b * (e_li z) 1 := h_e_comp0 (e_li z)
        rw [h1]
        have h2 : (e_li z) 0 = a * z 0 + b * z 1 := h_e_comp0 z
        have h3 : (e_li z) 1 = b * z 0 - a * z 1 := h_e_comp1 z
        rw [h2, h3]
        have h4 : a * (a * z 0 + b * z 1) + b * (b * z 0 - a * z 1) = (a^2 + b^2) * z 0 := by ring
        rw [h4, hab] <;> ring
      exact h
    · have h : e_li (e_li z) 1 = z 1 := by
        have h1 : e_li (e_li z) 1 = b * (e_li z) 0 - a * (e_li z) 1 := h_e_comp1 (e_li z)
        rw [h1]
        have h2 : (e_li z) 0 = a * z 0 + b * z 1 := h_e_comp0 z
        have h3 : (e_li z) 1 = b * z 0 - a * z 1 := h_e_comp1 z
        rw [h2, h3]
        have h4 : b * (a * z 0 + b * z 1) - a * (b * z 0 - a * z 1) = (a^2 + b^2) * z 1 := by ring
        rw [h4, hab] <;> ring
      exact h
  let e_equiv : Point2 ≃ₗᵢ[ℝ] Point2 :=
    { e_li with
      invFun := e_li
      left_inv := h_e_invol
      right_inv := h_e_invol }
  have h_e_comp0_inner : ∀ (z : Point2), e_li z 0 = inner ℝ z n := by
    intro z
    have h1 : e_li z 0 = a * z 0 + b * z 1 := h_e_comp0 z
    have h2 : inner ℝ z n = z 0 * a + z 1 * b := h_inner_form z n
    rw [h1, h2] <;> ring
  have h_inner_rot : ∀ (z : Point2), inner ℝ (e_li z) n = z 0 := by
    intro z
    rw [h_inner_form (e_li z) n]
    have h9 : e_li z 0 = a * z 0 + b * z 1 := h_e_comp0 z
    have h10 : e_li z 1 = b * z 0 - a * z 1 := h_e_comp1 z
    rw [h9, h10]
    have h11 : n 0 = a := by rfl
    have h12 : n 1 = b := by rfl
    rw [h11, h12]
    have h_alg : (a * z 0 + b * z 1) * a + (b * z 0 - a * z 1) * b = z 0 := by
      have h : (a * z 0 + b * z 1) * a + (b * z 0 - a * z 1) * b = (a^2 + b^2) * z 0 := by ring
      rw [h, hab] <;> ring
    exact h_alg
  have h_ball : e_li '' (Metric.ball (0 : Point2) ρ) = Metric.ball (0 : Point2) ρ := by
    ext y
    simp only [Set.mem_image, Metric.mem_ball]
    constructor
    · rintro ⟨z, hz, rfl⟩
      have h_e0 : e_li 0 = 0 := e_li.map_zero
      have h_dist : dist (e_li z) (e_li 0) = dist z 0 := e_li.isometry.dist_eq z 0
      rw [h_e0] at h_dist
      rw [h_dist]; exact hz
    · intro hy
      refine ⟨e_li y, ?_, h_e_invol y⟩
      have h_e0 : e_li 0 = 0 := e_li.map_zero
      have h_dist : dist (e_li y) (e_li 0) = dist y 0 := e_li.isometry.dist_eq y 0
      rw [h_e0] at h_dist
      rw [h_dist]; exact hy
  have h_strip : e_li '' {z : Point2 | |inner ℝ z n - t| ≤ r} = {y : Point2 | |y 0 - t| ≤ r} := by
    ext y
    simp only [Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨z, hz, rfl⟩
      have h_eq : e_li z 0 = inner ℝ z n := h_e_comp0_inner z
      rw [h_eq]; exact hz
    · intro hy
      have h : |inner ℝ (e_li y) n - t| ≤ r := by
        have h2 : inner ℝ (e_li y) n = y 0 := h_inner_rot y
        rw [h2] <;> exact hy
      exact ⟨e_li y, h, h_e_invol y⟩
  have h_e_inj : Function.Injective e_li := e_li.injective
  let S_orig : Set Point2 := Metric.ball (0 : Point2) ρ ∩ {z : Point2 | |inner ℝ z n - t| ≤ r}
  let S_rot : Set Point2 := Metric.ball (0 : Point2) ρ ∩ {y : Point2 | |y 0 - t| ≤ r}
  have h4 : e_li '' S_orig = S_rot := by
    rw [Set.image_inter h_e_inj, h_ball, h_strip]
  let e_mequiv : Point2 ≃ᵐ Point2 := e_equiv.toMeasurableEquiv
  have hmp : MeasurePreserving e_mequiv volume volume :=
    LinearIsometryEquiv.measurePreserving e_equiv
  have h5 : volume S_orig = volume S_rot := by
    have h6 : e_mequiv ⁻¹' (e_mequiv '' S_orig) = S_orig := by
      rw [e_mequiv.preimage_image]
    have h7 : volume (e_mequiv ⁻¹' (e_mequiv '' S_orig)) = volume (e_mequiv '' S_orig) :=
      hmp.measure_preimage_equiv (e_mequiv '' S_orig)
    rw [h6] at h7
    have h8 : e_mequiv '' S_orig = S_rot := by
      simpa [e_mequiv, e_equiv] using h4
    rw [h7, h8]
  rw [h5]
  let s : Fin 2 → Set ℝ := fun i =>
    if i = 0 then Set.Icc (t - r) (t + r) else Set.Icc (-ρ) ρ
  let rectangle : Set Point2 := {y | y 0 ∈ s 0 ∧ y 1 ∈ s 1}
  have h7 : S_rot ⊆ rectangle := by
    intro y hy
    have h8 : y ∈ Metric.ball (0 : Point2) ρ := hy.1
    have h9 : |y 0 - t| ≤ r := hy.2
    have h_normy : ‖y‖ < ρ := by
      simpa [Metric.mem_ball, dist_zero_right] using h8
    have h_norm2 : ‖y‖ ^ 2 = (y 0)^2 + (y 1)^2 := by
      have h1 : inner ℝ y y = ‖y‖ ^ 2 := h_norm_self y
      have h2 : inner ℝ y y = (y 0)^2 + (y 1)^2 := by
        rw [h_inner_form y y] <;> ring
      linarith
    have h10 : (y 1)^2 ≤ ρ^2 := by
      have h11 : (y 1)^2 ≤ ‖y‖ ^ 2 := by
        rw [h_norm2] <;> nlinarith [sq_nonneg (y 0)]
      have h12 : ‖y‖ ^ 2 < ρ^2 := by nlinarith [h_normy, norm_nonneg y]
      exact h11.trans h12.le
    have h13 : |y 1| ≤ ρ := by
      rw [abs_le] <;> constructor <;> nlinarith [sq_nonneg (y 1)]
    have h14 : y 0 ∈ s 0 := by
      simp only [s]
      have h141 : t - r ≤ y 0 := by linarith [abs_le.mp h9]
      have h142 : y 0 ≤ t + r := by linarith [abs_le.mp h9]
      exact ⟨h141, h142⟩
    have h15 : y 1 ∈ s 1 := by
      simp only [s]
      have h151 : -ρ ≤ y 1 := by linarith [abs_le.mp h13]
      have h152 : y 1 ≤ ρ := by linarith [abs_le.mp h13]
      exact ⟨h151, h152⟩
    exact ⟨h14, h15⟩
  let e_ofLp : Point2 ≃ᵐ (Fin 2 → ℝ) :=
    (EuclideanSpace.equiv (Fin 2) ℝ).toHomeomorph.toMeasurableEquiv
  have hpres_ofLp : MeasurePreserving e_ofLp volume volume :=
    PiLp.volume_preserving_ofLp (ι := Fin 2)
  have h_rect_img : e_ofLp '' rectangle = Set.univ.pi s := by
    ext f
    simp only [Set.mem_image, Set.mem_setOf_eq, rectangle, Set.mem_univ_pi]
    constructor
    · rintro ⟨y, ⟨h14, h15⟩, rfl⟩
      have h_eq : e_ofLp y = y := by rfl
      intro i
      fin_cases i
      · rw [h_eq]; exact h14
      · rw [h_eq]; exact h15
    · intro h
      refine ⟨e_ofLp.symm f, ?_, e_ofLp.apply_symm_apply f⟩
      have h14 : (e_ofLp.symm f) 0 ∈ s 0 := by
        have h15 : (e_ofLp.symm f) 0 = f 0 := by rfl
        rw [h15]; exact h 0
      have h16 : (e_ofLp.symm f) 1 ∈ s 1 := by
        have h17 : (e_ofLp.symm f) 1 = f 1 := by rfl
        rw [h17]; exact h 1
      exact ⟨h14, h16⟩
  have h16 : volume rectangle = ENNReal.ofReal (4 * ρ * r) := by
    have h17 : e_ofLp ⁻¹' (e_ofLp '' rectangle) = rectangle := by
      rw [e_ofLp.preimage_image]
    have h18 : volume (e_ofLp ⁻¹' (e_ofLp '' rectangle)) = volume (e_ofLp '' rectangle) :=
      hpres_ofLp.measure_preimage_equiv (e_ofLp '' rectangle)
    rw [h17] at h18
    have h19 : volume rectangle = volume (e_ofLp '' rectangle) := h18
    rw [h19, h_rect_img]
    rw [MeasureTheory.volume_pi_pi s]
    have h20 : ∏ i : Fin 2, volume (s i) = volume (s 0) * volume (s 1) := by
      simp [Fin.prod_univ_succ]
    rw [h20]
    have h_s0 : s 0 = Set.Icc (t - r) (t + r) := by simp [s]
    have h_s1 : s 1 = Set.Icc (-ρ) ρ := by simp [s]
    rw [h_s0, h_s1]
    have h_vol0 : volume (Set.Icc (t - r) (t + r)) = ENNReal.ofReal (2 * r) := by
      rw [Real.volume_Icc] <;> ring
    have h_vol1 : volume (Set.Icc (-ρ) ρ) = ENNReal.ofReal (2 * ρ) := by
      rw [Real.volume_Icc] <;> ring
    rw [h_vol0, h_vol1]
    have h21 : ENNReal.ofReal (2 * r) * ENNReal.ofReal (2 * ρ) = ENNReal.ofReal (4 * ρ * r) := by
      have h22 : 0 ≤ 2 * r := by linarith
      have h23 : ENNReal.ofReal (2 * r) * ENNReal.ofReal (2 * ρ) = ENNReal.ofReal ((2 * r) * (2 * ρ)) := by
        rw [← ENNReal.ofReal_mul h22]
      rw [h23]
      have h24 : (2 * r) * (2 * ρ) = 4 * ρ * r := by ring
      rw [h24]
    exact h21
  calc
    volume S_rot
      ≤ volume rectangle := measure_mono h7
    _ = ENNReal.ofReal (4 * ρ * r) := h16

/--
The uniform ball measure of a strip of half-width r is at most `4 * r / (π * ρ)`.
-/
lemma ballUniformMeasure_strip_bound
    {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r)
    (n : Point2) (hn : ‖n‖ = 1) (t : ℝ) :
    (ballUniformMeasure ρ hρ : Measure Point2) {y : Point2 | |inner ℝ y n - t| ≤ r} ≤
      ENNReal.ofReal (4 * r / (Real.pi * ρ)) := by
  let ball := Metric.ball (0 : Point2) ρ
  let strip : Set Point2 := {y | |inner ℝ y n - t| ≤ r}
  have h_strip_meas : MeasurableSet strip := by
    have h_cont : Measurable (fun y : Point2 => inner ℝ y n - t) := by fun_prop
    have h_Icc : MeasurableSet (Set.Icc (-r) r : Set ℝ) := by exact measurableSet_Icc
    have h_eq : strip = (fun y : Point2 => inner ℝ y n - t) ⁻¹' (Set.Icc (-r) r) := by
      ext y; simp [strip, abs_le] <;> ring_nf
    rw [h_eq]; exact h_Icc.preimage h_cont
  have h2 : volume.restrict ball strip = volume (ball ∩ strip) := by
    rw [Measure.restrict_apply h_strip_meas, Set.inter_comm]
  have h1 : (ballUniformMeasure ρ hρ : Measure Point2) strip =
      (volume ball)⁻¹ * volume (ball ∩ strip) := by
    have h_def : (ballUniformMeasure ρ hρ : Measure Point2) = (volume ball)⁻¹ • volume.restrict ball := by rfl
    rw [h_def]
    have h_smul : ((volume ball)⁻¹ • volume.restrict ball) strip = (volume ball)⁻¹ * volume.restrict ball strip := by
      rfl
    rw [h_smul, h2]
  rw [h1]
  have h3 : volume (ball ∩ strip) ≤ ENNReal.ofReal (4 * ρ * r) :=
    ball_strip_volume_bound hρ hr n hn t
  have h4 : (volume ball)⁻¹ * volume (ball ∩ strip) ≤ (volume ball)⁻¹ * ENNReal.ofReal (4 * ρ * r) := by gcongr
  have h_pos1 : 0 < ρ := hρ
  have h_pos2 : 0 < Real.pi := Real.pi_pos
  have h_eq1 : ENNReal.ofReal ρ ^ 2 * ENNReal.ofReal Real.pi = ENNReal.ofReal (ρ ^ 2 * Real.pi) := by
    have h1 : ENNReal.ofReal ρ ^ 2 = ENNReal.ofReal (ρ ^ 2) := by
      rw [← ENNReal.ofReal_pow (by linarith)] <;> rfl
    rw [h1, ← ENNReal.ofReal_mul (by positivity)] <;> rfl
  have h_pos3 : 0 < ρ ^ 2 * Real.pi := by positivity
  have h_inv : (ENNReal.ofReal (ρ ^ 2 * Real.pi))⁻¹ = ENNReal.ofReal ((ρ ^ 2 * Real.pi)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos h_pos3]
  have h_eq2 : ENNReal.ofReal ((ρ ^ 2 * Real.pi)⁻¹) * ENNReal.ofReal (4 * ρ * r) =
      ENNReal.ofReal (((ρ ^ 2 * Real.pi)⁻¹) * (4 * ρ * r)) := by
    rw [← ENNReal.ofReal_mul (by positivity)] <;> rfl
  have h_eq3 : ((ρ ^ 2 * Real.pi)⁻¹) * (4 * ρ * r) = 4 * r / (Real.pi * ρ) := by
    field_simp [h_pos1.ne', h_pos2.ne'] <;> ring
  have h_vol : volume ball = ENNReal.ofReal ρ ^ 2 * ENNReal.ofReal Real.pi :=
    EuclideanSpace.volume_ball_fin_two (0 : Point2) ρ
  have h5 : (volume ball)⁻¹ * ENNReal.ofReal (4 * ρ * r) = ENNReal.ofReal (4 * r / (Real.pi * ρ)) := by
    rw [h_vol, h_eq1, h_inv, h_eq2, h_eq3]
  calc
    (volume ball)⁻¹ * volume (ball ∩ strip)
      ≤ (volume ball)⁻¹ * ENNReal.ofReal (4 * ρ * r) := h4
    _ = ENNReal.ofReal (4 * r / (Real.pi * ρ)) := h5

/--
Smoothed measure strip bound for all scales, assuming discrete non-concentration
only for r ≥ δ.

Case r ≥ δ: Fubini + discrete non-concentration gives `K * r^β`.
Case r < δ: geometric bound gives `(4/π) * δ^{-β} * r^β`.

The output constant is `max(K, (4/π) * δ^{-β})`.
-/
lemma smoothedMeasure_strip_bound_all_scales
    {G₂ : DiscreteSet 2} (h2 : G₂.Nonempty)
    {δ : ℝ} (hδ : 0 < δ)
    {β K : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (hK : 1 ≤ K)
    (h_nonconc : ∀ (n : Point2), ‖n‖ = 1 → ∀ (t r : ℝ), δ ≤ r → 0 < r →
      ((G₂.filter fun y => |inner ℝ y n - t| ≤ r).card : ENNReal) ≤
        ENNReal.ofReal (K * r ^ β) * (G₂.card : ENNReal))
    {ℓ : AffineSubspace ℝ Point2} (p : Point2) (hp : p ∈ ℓ)
    (hfin : Module.finrank ℝ ℓ.direction = 1)
    {r : ℝ} (hr : 0 < r) :
    (smoothMeasure G₂ h2 δ hδ : Measure Point2) (Metric.thickening r (ℓ : Set Point2)) ≤
      ENNReal.ofReal (max K (4 / Real.pi * δ ^ (-β)) * r ^ β) := by
  let K' : ℝ := max K (4 / Real.pi * δ ^ (-β))
  by_cases h : δ ≤ r
  · -- Case r ≥ δ: use Fubini + discrete non-concentration
    let σ := ballUniformMeasure δ hδ
    let ν₂ := smoothMeasure G₂ h2 δ hδ
    let S : Set Point2 := Metric.thickening r (ℓ : Set Point2)
    have hS : MeasurableSet S := Metric.isOpen_thickening.measurableSet
    have h1 : (ν₂ : Measure Point2) S =
        (G₂.card : ENNReal)⁻¹ * ∑ a ∈ G₂, (σ : Measure Point2) {y : Point2 | a + y ∈ S} :=
      smoothMeasure_apply hS
    rw [h1]
    have h2' : ∑ a ∈ G₂, (σ : Measure Point2) {y : Point2 | a + y ∈ S} =
        ∫⁻ y : Point2, ((G₂.filter fun a : Point2 => a + y ∈ S).card : ENNReal) ∂(σ : Measure Point2) := by
      let f : Point2 → Point2 → ENNReal := fun a y =>
        Set.indicator {y : Point2 | a + y ∈ S} (fun _ : Point2 => (1 : ENNReal)) y
      have hf_meas : ∀ (a : Point2), a ∈ G₂ → Measurable (f a) := by
        intro a _
        have h_set_meas : MeasurableSet {y : Point2 | a + y ∈ S} := by
          have h_open : IsOpen S := Metric.isOpen_thickening
          exact (h_open.preimage (continuous_const.add continuous_id)).measurableSet
        have h : Measurable (Set.indicator {y : Point2 | a + y ∈ S} (fun _ : Point2 => (1 : ENNReal))) :=
          measurable_const.indicator h_set_meas
        have h_f_eq : f a = Set.indicator {y : Point2 | a + y ∈ S} (fun _ : Point2 => (1 : ENNReal)) := by
          funext y
          simp [f]
          <;> rfl
        rw [h_f_eq]
        exact h
      have h3 : ∀ a ∈ G₂, (σ : Measure Point2) {y : Point2 | a + y ∈ S} = ∫⁻ y, f a y ∂(σ : Measure Point2) := by
        intro a ha
        have h_set_meas : MeasurableSet {y : Point2 | a + y ∈ S} := by
          have h_open : IsOpen S := Metric.isOpen_thickening
          exact (h_open.preimage (continuous_const.add continuous_id)).measurableSet
        have h_eq : ∫⁻ y, f a y ∂(σ : Measure Point2) = (σ : Measure Point2) {y : Point2 | a + y ∈ S} := by
          rw [MeasureTheory.lintegral_indicator h_set_meas (fun _ => (1 : ENNReal))]
          <;> simp [f]
        exact h_eq.symm
      calc
        ∑ a ∈ G₂, (σ : Measure Point2) {y : Point2 | a + y ∈ S}
          = ∑ a ∈ G₂, ∫⁻ y, f a y ∂(σ : Measure Point2) := by
            apply Finset.sum_congr rfl; intro a ha; exact h3 a ha
        _ = ∫⁻ y, ∑ a ∈ G₂, f a y ∂(σ : Measure Point2) := by
            rw [← MeasureTheory.lintegral_finsetSum G₂ hf_meas]
        _ = ∫⁻ y, ((G₂.filter fun a : Point2 => a + y ∈ S).card : ENNReal) ∂(σ : Measure Point2) := by
            apply lintegral_congr
            intro y
            have h_sum : ∑ a ∈ G₂, f a y = ((G₂.filter fun a : Point2 => a + y ∈ S).card : ENNReal) := by
              simp [f, Set.indicator_apply, Finset.sum_ite]
              <;> norm_cast
            exact h_sum
    rw [h2']
    have h4 : ∀ (y : Point2), ((G₂.filter fun a : Point2 => a + y ∈ S).card : ENNReal) ≤
        ENNReal.ofReal (K * r ^ β) * (G₂.card : ENNReal) := by
      intro y
      obtain ⟨n, hn, hn_orth⟩ := exists_unit_normal_of_finrank_one hfin
      let t : ℝ := inner ℝ p n
      have h_strip : S ⊆ {z : Point2 | |inner ℝ z n - t| ≤ r} :=
        thickening_subset_strip hfin n hn hn_orth p hp r hr
      let t' : ℝ := t - inner ℝ y n
      have h_imp : ∀ (a : Point2), a + y ∈ S → |inner ℝ a n - t'| ≤ r := by
        intro a ha
        have h7 : |inner ℝ (a + y) n - t| ≤ r := h_strip ha
        have h8 : inner ℝ (a + y) n = inner ℝ a n + inner ℝ y n := by rw [inner_add_left]
        rw [h8] at h7
        have h9 : inner ℝ a n + inner ℝ y n - t = inner ℝ a n - t' := by
          simp [t'] <;> ring
        rw [h9] at h7
        exact h7
      have h_filter_sub : (G₂.filter fun a : Point2 => a + y ∈ S) ⊆
          G₂.filter fun z : Point2 => |inner ℝ z n - t'| ≤ r := by
        intro a ha
        have h5 : a ∈ G₂ := (Finset.mem_filter.mp ha).1
        have h6 : a + y ∈ S := (Finset.mem_filter.mp ha).2
        exact Finset.mem_filter.mpr ⟨h5, h_imp a h6⟩
      have h9 : ((G₂.filter fun a : Point2 => a + y ∈ S).card : ENNReal) ≤
          ((G₂.filter fun z : Point2 => |inner ℝ z n - t'| ≤ r).card : ENNReal) := by
        exact_mod_cast Finset.card_le_card h_filter_sub
      have h10 := h_nonconc n hn t' r h hr
      exact h9.trans h10
    have h5 : ∫⁻ y : Point2, ((G₂.filter fun a : Point2 => a + y ∈ S).card : ENNReal) ∂(σ : Measure Point2) ≤
        ∫⁻ y : Point2, ENNReal.ofReal (K * r ^ β) * (G₂.card : ENNReal) ∂(σ : Measure Point2) := by
      exact lintegral_mono h4
    have h6 : ∫⁻ y : Point2, ENNReal.ofReal (K * r ^ β) * (G₂.card : ENNReal) ∂(σ : Measure Point2) =
        ENNReal.ofReal (K * r ^ β) * (G₂.card : ENNReal) := by
      have h7 : (σ : Measure Point2) Set.univ = 1 := by
        simpa [σ] using ProbabilityMeasure.measure_univ σ
      rw [lintegral_const, h7] <;> simp
    rw [h6] at h5
    have hpos : (G₂.card : ENNReal) ≠ 0 := by
      have h : 0 < G₂.card := Finset.card_pos.mpr h2
      exact_mod_cast h.ne'
    have htop : (G₂.card : ENNReal) ≠ ⊤ := by simp
    have h7 : (G₂.card : ENNReal)⁻¹ * (ENNReal.ofReal (K * r ^ β) * (G₂.card : ENNReal)) =
        ENNReal.ofReal (K * r ^ β) := by
      rw [mul_comm (ENNReal.ofReal (K * r ^ β)), ← mul_assoc, ENNReal.inv_mul_cancel hpos htop, one_mul]
    have h8 : ENNReal.ofReal (K * r ^ β) ≤ ENNReal.ofReal (K' * r ^ β) := by
      have h9 : 0 ≤ r ^ β := by positivity
      exact ENNReal.ofReal_le_ofReal (by gcongr <;> exact le_max_left _ _)
    calc
      (G₂.card : ENNReal)⁻¹ * ∫⁻ y, ((G₂.filter fun a => a + y ∈ S).card : ENNReal) ∂(σ : Measure Point2)
        ≤ (G₂.card : ENNReal)⁻¹ * (ENNReal.ofReal (K * r ^ β) * (G₂.card : ENNReal)) := by gcongr
      _ = ENNReal.ofReal (K * r ^ β) := h7
      _ ≤ ENNReal.ofReal (K' * r ^ β) := h8
  · -- Case r < δ: use geometric bound
    have h' : r < δ := by linarith
    let σ := ballUniformMeasure δ hδ
    let ν₂ := smoothMeasure G₂ h2 δ hδ
    let S : Set Point2 := Metric.thickening r (ℓ : Set Point2)
    have hS : MeasurableSet S := Metric.isOpen_thickening.measurableSet
    obtain ⟨n, hn, hn_orth⟩ := exists_unit_normal_of_finrank_one hfin
    let t : ℝ := inner ℝ p n
    have h_sub : S ⊆ {y : Point2 | |inner ℝ y n - t| ≤ r} :=
      thickening_subset_strip hfin n hn hn_orth p hp r hr
    have h1 : (ν₂ : Measure Point2) S =
        (G₂.card : ENNReal)⁻¹ * ∑ a ∈ G₂, (σ : Measure Point2) {y : Point2 | a + y ∈ S} :=
      smoothMeasure_apply hS
    rw [h1]
    have h2_bound : ∀ a ∈ G₂, (σ : Measure Point2) {y : Point2 | a + y ∈ S} ≤
        ENNReal.ofReal (4 * r / (Real.pi * δ)) := by
      intro a _
      have h3 : {y : Point2 | a + y ∈ S} ⊆ {y : Point2 | |inner ℝ y n - (t - inner ℝ a n)| ≤ r} := by
        intro y hy
        have h4 : a + y ∈ S := hy
        have h5 : |inner ℝ (a + y) n - t| ≤ r := h_sub h4
        have h6 : inner ℝ (a + y) n = inner ℝ a n + inner ℝ y n := by rw [inner_add_left]
        have h7 : |inner ℝ y n - (t - inner ℝ a n)| ≤ r := by
          have h8 : inner ℝ (a + y) n - t = inner ℝ y n - (t - inner ℝ a n) := by
            rw [h6] <;> ring
          rw [h8] at h5
          exact h5
        exact h7
      have h6 : (σ : Measure Point2) {y : Point2 | a + y ∈ S} ≤
          (σ : Measure Point2) {y : Point2 | |inner ℝ y n - (t - inner ℝ a n)| ≤ r} :=
        measure_mono h3
      exact h6.trans (ballUniformMeasure_strip_bound hδ hr n hn (t - inner ℝ a n))
    have h3 : ∑ a ∈ G₂, (σ : Measure Point2) {y : Point2 | a + y ∈ S} ≤
        ∑ a ∈ G₂, ENNReal.ofReal (4 * r / (Real.pi * δ)) := by
      apply Finset.sum_le_sum
      intro a ha
      exact h2_bound a ha
    have h4 : ∑ a ∈ G₂, ENNReal.ofReal (4 * r / (Real.pi * δ)) =
        (G₂.card : ENNReal) * ENNReal.ofReal (4 * r / (Real.pi * δ)) := by
      simp [Finset.sum_const] <;> ring
    rw [h4] at h3
    have hpos : (G₂.card : ENNReal) ≠ 0 := by
      have h : 0 < G₂.card := Finset.card_pos.mpr h2
      exact_mod_cast h.ne'
    have htop : (G₂.card : ENNReal) ≠ ⊤ := by simp
    have h5 : (G₂.card : ENNReal)⁻¹ * ((G₂.card : ENNReal) * ENNReal.ofReal (4 * r / (Real.pi * δ))) =
        ENNReal.ofReal (4 * r / (Real.pi * δ)) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hpos htop, one_mul]
    have h6 : (G₂.card : ENNReal)⁻¹ * ∑ a ∈ G₂, (σ : Measure Point2) {y : Point2 | a + y ∈ S} ≤
        ENNReal.ofReal (4 * r / (Real.pi * δ)) := by
      calc
        (G₂.card : ENNReal)⁻¹ * ∑ a ∈ G₂, (σ : Measure Point2) {y : Point2 | a + y ∈ S}
          ≤ (G₂.card : ENNReal)⁻¹ * ((G₂.card : ENNReal) * ENNReal.ofReal (4 * r / (Real.pi * δ))) := by gcongr
        _ = ENNReal.ofReal (4 * r / (Real.pi * δ)) := h5
    have h7 : 4 * r / (Real.pi * δ) ≤ K' * r ^ β := by
      have h8 : 0 < δ := hδ
      have h9 : 0 ≤ r := by linarith
      have h10 : 0 ≤ r / δ := by positivity
      have h11 : r / δ ≤ 1 := by
        apply (div_le_one (by positivity)).mpr
        linarith
      have h12 : r / δ ≤ (r / δ) ^ β := by
        by_cases h0 : r / δ = 0
        · rw [h0]; positivity
        · have hx_pos : 0 < r / δ := by positivity
          have h_log_nonpos : Real.log (r / δ) ≤ 0 := Real.log_nonpos hx_pos.le h11
          have h_ineq : Real.log (r / δ) ≤ β * Real.log (r / δ) := by nlinarith
          have h_log_rpow : Real.log ((r / δ) ^ β) = β * Real.log (r / δ) := by
            rw [Real.log_rpow (by positivity)]
          have h4 : Real.log (r / δ) ≤ Real.log ((r / δ) ^ β) := by
            rw [h_log_rpow] <;> exact h_ineq
          exact (Real.log_le_log_iff hx_pos (by positivity)).mp h4
      have h13 : 0 < 4 / Real.pi := by positivity
      have h14 : (4 / Real.pi) * (r / δ) ≤ (4 / Real.pi) * (r / δ) ^ β := by gcongr
      have h15 : (4 / Real.pi) * (r / δ) ^ β = (4 / Real.pi * δ ^ (-β)) * r ^ β := by
        have h16 : (r / δ) ^ β = r ^ β / δ ^ β := by
          rw [Real.div_rpow (by positivity) (by positivity)]
        rw [h16]
        have h17 : δ ^ (-β) = 1 / δ ^ β := by
          rw [Real.rpow_neg (by positivity)] <;> ring
        rw [h17] <;> ring
      calc
        4 * r / (Real.pi * δ)
          = (4 / Real.pi) * (r / δ) := by ring
        _ ≤ (4 / Real.pi) * (r / δ) ^ β := h14
        _ = (4 / Real.pi * δ ^ (-β)) * r ^ β := h15
        _ ≤ K' * r ^ β := by
          have h18 : 0 ≤ r ^ β := by positivity
          gcongr <;> exact le_max_right _ _
    have h19 : 0 ≤ K' * r ^ β := by positivity
    have h20 : ENNReal.ofReal (4 * r / (Real.pi * δ)) ≤ ENNReal.ofReal (K' * r ^ β) :=
      ENNReal.ofReal_le_ofReal h7
    exact h6.trans h20

/--
Strip non-concentration on G₂ for scales ≥ δ implies `HasMeasureThinTubes`
for the smoothed measures (smoothing radius δ), with any exceptional fraction c.

The output constant is `max(K, (4/π) * δ^{-β})`.
-/
lemma smoothedMeasure_thinTubes_all_scales
    {G₁ G₂ : DiscreteSet 2} (h1 : G₁.Nonempty) (h2 : G₂.Nonempty)
    {δ : ℝ} (hδ : 0 < δ)
    {β K c : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (hK : 1 ≤ K) (hc : 0 ≤ c) (hc1 : c < 1)
    (h_nonconc : ∀ (n : Point2), ‖n‖ = 1 → ∀ (t r : ℝ), δ ≤ r → 0 < r →
      ((G₂.filter fun y => |inner ℝ y n - t| ≤ r).card : ENNReal) ≤
        ENNReal.ofReal (K * r ^ β) * (G₂.card : ENNReal)) :
    HasMeasureThinTubes β (max K (4 / Real.pi * δ ^ (-β))) c
      (smoothMeasure G₁ h1 δ hδ)
      (smoothMeasure G₂ h2 δ hδ) := by
  let K' : ℝ := max K (4 / Real.pi * δ ^ (-β))
  have hK'_one : 1 ≤ K' := by
    have h1 : 1 ≤ K := hK
    exact le_trans h1 (le_max_left _ _)
  let μ1 : Measure Point2 := smoothMeasure G₁ h1 δ hδ
  let μ2 : Measure Point2 := smoothMeasure G₂ h2 δ hδ
  let E : Set (Point2 × Point2) := μ1.support ×ˢ μ2.support
  have hE_meas : MeasurableSet E := by
    have h1 : IsClosed μ1.support := Measure.isClosed_support
    have h2 : IsClosed μ2.support := Measure.isClosed_support
    exact (h1.prod h2).measurableSet
  have hE_sub : E ⊆ μ1.support ×ˢ μ2.support := by
    exact Set.Subset.refl _
  have h_meas_support1 : MeasurableSet μ1.support := Measure.isClosed_support.measurableSet
  have h_meas_support1c : MeasurableSet μ1.supportᶜ := h_meas_support1.compl
  have h_meas_support2 : MeasurableSet μ2.support := Measure.isClosed_support.measurableSet
  have h_meas_support2c : MeasurableSet μ2.supportᶜ := h_meas_support2.compl
  have h_support1 : μ1 μ1.support = 1 := by
    have h1 : μ1 (μ1.supportᶜ) = 0 := MeasureTheory.Measure.measure_compl_support (μ := μ1)
    have h2 : μ1 Set.univ = 1 := by
      simp [μ1]
    have h3 : Set.univ = μ1.support ∪ μ1.supportᶜ := by ext x; simp
    have h4 : Disjoint μ1.support μ1.supportᶜ := by simp [Set.disjoint_left]
    have h5 : μ1 Set.univ = μ1 μ1.support + μ1 (μ1.supportᶜ) := by
      rw [h3, measure_union h4 h_meas_support1c]
    rw [h5, h1] at h2
    simpa using h2
  have h_support2 : μ2 μ2.support = 1 := by
    have h1 : μ2 (μ2.supportᶜ) = 0 := MeasureTheory.Measure.measure_compl_support (μ := μ2)
    have h2 : μ2 Set.univ = 1 := by
      simp [μ2]
    have h3 : Set.univ = μ2.support ∪ μ2.supportᶜ := by ext x; simp
    have h4 : Disjoint μ2.support μ2.supportᶜ := by simp [Set.disjoint_left]
    have h5 : μ2 Set.univ = μ2 μ2.support + μ2 (μ2.supportᶜ) := by
      rw [h3, measure_union h4 h_meas_support2c]
    rw [h5, h1] at h2
    simpa using h2
  have hE_mass : (1 - ENNReal.ofReal c) ≤
      ((smoothMeasure G₁ h1 δ hδ).prod (smoothMeasure G₂ h2 δ hδ)) E := by
    have h_prod : ((smoothMeasure G₁ h1 δ hδ).prod (smoothMeasure G₂ h2 δ hδ)) E =
        μ1 μ1.support * μ2 μ2.support := by
      have h : ((smoothMeasure G₁ h1 δ hδ).prod (smoothMeasure G₂ h2 δ hδ) : Measure (Point2 × Point2)) (μ1.support ×ˢ μ2.support) =
          μ1 μ1.support * μ2 μ2.support := by
        exact Measure.prod_prod μ1.support μ2.support
      simpa [E] using h
    rw [h_prod, h_support1, h_support2]
    have h2 : ENNReal.ofReal c ≤ 1 := by
      exact ENNReal.ofReal_le_one.mpr (by linarith)
    simpa using h2
  refine' ⟨hβ, hK'_one, ⟨hc, hc1⟩, E, hE_meas, hE_sub, hE_mass, _⟩
  intro b₁ hb₁ ℓ hb₁_in_ℓ hfin r hr
  let S : Set Point2 := Metric.thickening r (ℓ : Set Point2)
  let T : Set Point2 := {b₂ | b₂ ∈ S ∧ (b₁, b₂) ∈ E}
  have hT_eq : T = S ∩ μ2.support := by
    ext b₂
    simp only [T, E, Set.mem_setOf_eq, Set.mem_inter_iff]
    constructor
    · intro h
      exact ⟨h.1, h.2.2⟩
    · intro h
      exact ⟨h.1, ⟨hb₁, h.2⟩⟩
  have h_measure : μ2 T = μ2 S := by
    rw [hT_eq]
    have h1 : μ2 (μ2.supportᶜ) = 0 := MeasureTheory.Measure.measure_compl_support (μ := μ2)
    have h_null : μ2 (S \ μ2.support) = 0 := measure_mono_null (show S \ μ2.support ⊆ μ2.supportᶜ from by simp [Set.diff_subset_iff]) h1
    have h_meas_S : MeasurableSet S := Metric.isOpen_thickening.measurableSet
    have h_meas_inter : MeasurableSet (S ∩ μ2.support) := h_meas_S.inter h_meas_support2
    have h_meas_diff : MeasurableSet (S \ μ2.support) := h_meas_S.diff h_meas_support2
    have h3 : (S ∩ μ2.support) ∪ (S \ μ2.support) = S := by
      rw [Set.union_comm, Set.diff_union_inter]
    have h4 : Disjoint (S ∩ μ2.support) (S \ μ2.support) := by
      apply Set.disjoint_iff_inter_eq_empty.mpr
      ext x
      simp only [Set.mem_inter_iff, Set.mem_diff, Set.mem_empty_iff_false]
      <;> aesop
    have h5 : μ2 ((S ∩ μ2.support) ∪ (S \ μ2.support)) = μ2 (S ∩ μ2.support) + μ2 (S \ μ2.support) :=
      measure_union h4 h_meas_diff
    have h6 : μ2 S = μ2 (S ∩ μ2.support) := by
      have h7 : μ2 S = μ2 ((S ∩ μ2.support) ∪ (S \ μ2.support)) := by
        congr 1
        exact h3.symm
      rw [h7, h5, h_null]
      <;> simp
    exact h6.symm
  have h_bound := smoothedMeasure_strip_bound_all_scales h2 hδ hβ hβ1 hK h_nonconc b₁ hb₁_in_ℓ hfin hr
  have h_nonneg : 0 ≤ K' * r ^ β := by positivity
  have h9 : μ2 T = μ2 S := h_measure
  have h10 : μ2 S ≤ ENNReal.ofReal (K' * r ^ β) := by simpa [μ2] using h_bound
  have h11 : μ2 T ≤ ENNReal.ofReal (K' * r ^ β) := by rw [h9] <;> exact h10
  have h12 : ENNReal.ofReal (K' * r ^ β) = ↑(Real.toNNReal (K' * r ^ β)) := by
    rw [ENNReal.ofReal_eq_coe_nnreal h_nonneg]
    <;> simp [Real.toNNReal_of_nonneg h_nonneg]
    <;> rfl
  have h13 : μ2 T ≤ ↑(Real.toNNReal (K' * r ^ β)) := by
    rw [h12] at h11
    exact h11
  have h14 : (↑((smoothMeasure G₂ h2 δ hδ) T) : ENNReal) = μ2 T := by
    simp [μ2]
  have h15 : (↑((smoothMeasure G₂ h2 δ hδ) T) : ENNReal) ≤ ↑(Real.toNNReal (K' * r ^ β)) := by
    rw [h14]
    exact h13
  have h16 : (smoothMeasure G₂ h2 δ hδ) T ≤ Real.toNNReal (K' * r ^ β) := by
    exact WithTop.coe_le_coe.mp h15
  exact h16

end Kakeya.Assouad
