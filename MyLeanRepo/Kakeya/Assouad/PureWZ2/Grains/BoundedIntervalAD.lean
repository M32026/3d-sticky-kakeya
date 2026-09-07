import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.TrivialCovering
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.ADBridge

/-!
# Bounded interval AD bound

A bounded subset of `ℝ` satisfies the paper-literal AD condition with a
sufficiently large constant, provided the loss exponent exceeds `sigma`.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

/-- Helper: `3 * (L/delta)^sigma ≤ delta^(-outputLoss)` from the smallness condition. -/
lemma bounded_interval_smallness_step
    {delta sigma outputLoss L : ℝ}
    (hdelta_pos : 0 < delta)
    (hL_pos : 0 < L)
    (hsigma_pos : 0 < sigma)
    (hloss_gt_sigma : sigma < outputLoss)
    (hsmall : 3 * L^sigma ≤ (1/delta)^(outputLoss-sigma)) :
    3 * (L / delta) ^ sigma ≤ delta ^ (-outputLoss) := by
  have h1 : 3 * (L / delta) ^ sigma = 3 * L ^ sigma * delta ^ (-sigma) := by
    have h11 : (L / delta) ^ sigma = L ^ sigma / delta ^ sigma :=
      Real.div_rpow hL_pos.le hdelta_pos.le sigma
    have h12 : (delta ^ sigma)⁻¹ = delta ^ (-sigma) := by
      rw [Real.rpow_neg hdelta_pos.le] <;> ring
    rw [h11]
    have h13 : L ^ sigma / delta ^ sigma = L ^ sigma * (delta ^ sigma)⁻¹ := by ring
    rw [h13, h12] <;> ring
  have h3 : (1 / delta) ^ (outputLoss - sigma) = delta ^ (sigma - outputLoss) := by
    have h31 : (1 / delta) ^ (outputLoss - sigma) = (delta ^ (outputLoss - sigma))⁻¹ := by
      rw [Real.div_rpow (by norm_num) hdelta_pos.le] <;> simp
    have h32 : delta ^ (sigma - outputLoss) = (delta ^ (outputLoss - sigma))⁻¹ := by
      have h33 : sigma - outputLoss = -(outputLoss - sigma) := by ring
      rw [h33, Real.rpow_neg hdelta_pos.le] <;> ring
    rw [h31, h32]
  have h4 : delta ^ (sigma - outputLoss) * delta ^ (-sigma) = delta ^ (-outputLoss) := by
    have h41 : delta ^ (sigma - outputLoss) * delta ^ (-sigma) =
        delta ^ ((sigma - outputLoss) + (-sigma)) := by
      rw [← Real.rpow_add hdelta_pos]
    rw [h41]
    have h42 : (sigma - outputLoss) + (-sigma) = -outputLoss := by ring
    rw [h42]
  calc 3 * (L / delta) ^ sigma
    = 3 * L ^ sigma * delta ^ (-sigma) := h1
  _ ≤ (1 / delta) ^ (outputLoss - sigma) * delta ^ (-sigma) := by gcongr
  _ = delta ^ (sigma - outputLoss) * delta ^ (-sigma) := by rw [h3]
  _ = delta ^ (-outputLoss) := h4

/-- Key real inequality: if `1 ≤ x ≤ L/delta` and the smallness condition holds,
then `3 * x ≤ delta^(-outputLoss) * x^(1-sigma)`. -/
lemma bounded_interval_key_ineq
    {delta sigma outputLoss L : ℝ}
    (hdelta_pos : 0 < delta)
    (hL_pos : 0 < L)
    (hsigma_pos : 0 < sigma)
    (hloss_gt_sigma : sigma < outputLoss)
    (hsmall : 3 * L^sigma ≤ (1/delta)^(outputLoss-sigma))
    {x : ℝ} (hx1 : 1 ≤ x) (hx2 : x ≤ L / delta) :
    3 * x ≤ (delta ^ (-outputLoss)) * (x ^ (1 - sigma)) := by
  have hx_pos : 0 < x := by linarith
  have h_step : 3 * (L / delta) ^ sigma ≤ delta ^ (-outputLoss) :=
    bounded_interval_smallness_step hdelta_pos hL_pos hsigma_pos hloss_gt_sigma hsmall
  have h4 : 3 * x ^ sigma ≤ delta ^ (-outputLoss) := by
    have h41 : x ^ sigma ≤ (L / delta) ^ sigma :=
      Real.rpow_le_rpow (by linarith) hx2 (by linarith)
    have h42 : 3 * x ^ sigma ≤ 3 * (L / delta) ^ sigma := by gcongr
    exact h42.trans h_step
  have h5 : (3 * x ^ sigma) * x ^ (1 - sigma) ≤
      (delta ^ (-outputLoss)) * x ^ (1 - sigma) :=
    mul_le_mul_of_nonneg_right h4 (by positivity)
  have h6 : x ^ sigma * x ^ (1 - sigma) = x := by
    have h7 : x ^ sigma * x ^ (1 - sigma) = x ^ (sigma + (1 - sigma)) := by
      rw [← Real.rpow_add hx_pos]
    rw [h7]
    have h8 : sigma + (1 - sigma) = 1 := by ring
    rw [h8]
    simp
  have h9 : (3 * x ^ sigma) * x ^ (1 - sigma) = 3 * x := by
    calc (3 * x ^ sigma) * x ^ (1 - sigma)
      = 3 * (x ^ sigma * x ^ (1 - sigma)) := by ring
    _ = 3 * x := by rw [h6]
  rw [h9] at h5
  exact h5

/-- A bounded subset of `ℝ` satisfies `PureWZ2PaperADSet1` when
`outputLoss > sigma` and `delta` is sufficiently small. -/
lemma bounded_interval_paper_ad1
    {delta sigma outputLoss L : ℝ}
    (hdelta_pos : 0 < delta)
    (hdelta_le_one : delta ≤ 1)
    (hsigma_pos : 0 < sigma)
    (hsigma_lt_one : sigma < 1)
    (hloss_gt_sigma : sigma < outputLoss)
    (hL_pos : 0 < L)
    (hsmall : 3 * L^sigma ≤ (1/delta)^(outputLoss-sigma))
    {S : Set ℝ}
    (hS : S ⊆ Set.Icc (-L/2) (L/2)) :
    PureWZ2PaperADSet1 S delta (1 - sigma) (Kakeya.realRpowENN delta (-outputLoss)) := by
  have halpha_pos : 0 < 1 - sigma := by linarith
  have halpha_le_one : 1 - sigma ≤ 1 := by linarith
  set C : ENNReal := Kakeya.realRpowENN delta (-outputLoss) with hC_def

  have hC_one : 1 ≤ C := by
    have h2 : 1 ≤ 1 / delta := by
      calc 1 = delta / delta := by field_simp [hdelta_pos.ne']
        _ ≤ 1 / delta := by gcongr
    have h3 : 1 ≤ (1 / delta) ^ outputLoss := Real.one_le_rpow h2 (by linarith)
    have h4 : (1 / delta) ^ outputLoss = Real.rpow delta (-outputLoss) := by
      have h1 : (1 / delta) ^ outputLoss = (delta ^ outputLoss)⁻¹ := by
        rw [Real.div_rpow (by norm_num) hdelta_pos.le] <;> simp
      have h2 : Real.rpow delta (-outputLoss) = (delta ^ outputLoss)⁻¹ :=
        Real.rpow_neg hdelta_pos.le outputLoss
      rw [h1, h2]
    have h5 : 1 ≤ Real.rpow delta (-outputLoss) := by
      rw [←h4]
      exact h3
    simp only [hC_def, Kakeya.realRpowENN]
    exact ENNReal.one_le_ofReal.mpr h5

  have hC_ne_top : C ≠ ⊤ := by
    simp [hC_def, Kakeya.realRpowENN, ENNReal.ofReal_ne_top]

  have h_ineq : ∀ (x : ℝ), 1 ≤ x → x ≤ L / delta →
      ENNReal.ofReal (3 * x) ≤ C * Kakeya.realRpowENN x (1 - sigma) := by
    intro x hx1 hx2
    have h_real : 3 * x ≤ (delta ^ (-outputLoss)) * (x ^ (1 - sigma)) :=
      bounded_interval_key_ineq hdelta_pos hL_pos hsigma_pos hloss_gt_sigma hsmall hx1 hx2
    have h_pos1 : 0 ≤ delta ^ (-outputLoss) := by positivity
    have h1 : C * Kakeya.realRpowENN x (1 - sigma) =
        ENNReal.ofReal ((delta ^ (-outputLoss)) * (x ^ (1 - sigma))) := by
      simp [hC_def, Kakeya.realRpowENN, ENNReal.ofReal_mul h_pos1] <;> rfl
    rw [h1]
    exact ENNReal.ofReal_le_ofReal h_real

  have h_main : ∀ (rho : ℝ), ∀ (hrho : 0 ≤ rho), delta ≤ rho →
      ∀ (left length : ℝ), rho ≤ length →
        (↑(Metric.externalCoveringNumber ⟨rho, hrho⟩ (S ∩ Set.Icc left (left + length))) : ENNReal) ≤
          C * Kakeya.realRpowENN (length / rho) (1 - sigma) := by
    intro rho hrho hdelta_le_rho left length hlength_ge_rho
    let T : Set ℝ := S ∩ Set.Icc left (left + length)
    have hT_sub2 : T ⊆ S := by intro x hx; exact hx.1
    have hrho_pos : 0 < rho := by linarith

    by_cases hL_le_rho : L ≤ rho
    · -- Case 1: L ≤ rho, one ball centered at 0 suffices
      have h_center0 : T ⊆ Metric.closedBall (0 : ℝ) rho := by
        intro y hy
        have h_y1 : -L/2 ≤ y := (hS (hT_sub2 hy)).1
        have h_y2 : y ≤ L/2 := (hS (hT_sub2 hy)).2
        have h : dist y 0 ≤ rho := by
          simp only [Real.dist_eq, abs_le]
          constructor <;> linarith
        simpa [Metric.mem_closedBall] using h
      let ε : NNReal := ⟨rho, hrho⟩
      have h_iscover : Metric.IsCover ε T ({0} : Set ℝ) := by
        intro z hz
        have h_dist : dist z 0 ≤ rho := by
          simpa [Metric.mem_closedBall] using h_center0 hz
        have h_edist : edist z 0 ≤ (ε : ENNReal) := by
          rw [edist_dist z 0]
          have h_coe : (↑ε : ENNReal) = ENNReal.ofReal (↑ε : ℝ) := by simp
          rw [h_coe]
          have h_eps : (↑ε : ℝ) = rho := by
            unfold ε
            exact Subtype.coe_mk rho hrho
          rw [h_eps]
          exact ENNReal.ofReal_le_ofReal h_dist
        exact ⟨0, by simp, h_edist⟩
      have h_le : (Metric.externalCoveringNumber ε T : ENNReal) ≤ 1 := by
        calc (Metric.externalCoveringNumber ε T : ENNReal)
          ≤ ({0} : Set ℝ).encard := by exact_mod_cast h_iscover.externalCoveringNumber_le_encard
        _ = 1 := by simp
      have h13 : (1 : ENNReal) ≤ Kakeya.realRpowENN (length / rho) (1 - sigma) := by
        simp only [Kakeya.realRpowENN]
        have h14 : 1 ≤ length / rho := by
          calc 1 = rho / rho := by field_simp [hrho_pos.ne']
            _ ≤ length / rho := by gcongr
        have h15 : 0 ≤ 1 - sigma := by linarith
        have h16 : 1 ≤ Real.rpow (length / rho) (1 - sigma) :=
          Real.one_le_rpow h14 h15
        exact ENNReal.one_le_ofReal.mpr h16
      have h11 : (1 : ENNReal) ≤ C * Kakeya.realRpowENN (length / rho) (1 - sigma) := by
        have h1 : (1 : ENNReal) ≤ C := hC_one
        have h2 : (1 : ENNReal) ≤ Kakeya.realRpowENN (length / rho) (1 - sigma) := h13
        have h3 : (1 : ENNReal) * (1 : ENNReal) ≤ C * Kakeya.realRpowENN (length / rho) (1 - sigma) := by
          gcongr
        simpa using h3
      exact h_le.trans h11

    · -- Case 2: L > rho
      have h_rho_lt_L : rho < L := by linarith
      by_cases hcase : length ≤ L
      · -- Case 2a: length ≤ L
        have hx1 : 1 ≤ length / rho := by
          calc 1 = rho / rho := by field_simp [hrho_pos.ne']
            _ ≤ length / rho := by gcongr
        have hx2 : length / rho ≤ L / delta := by
          have h4 : length / rho ≤ L / rho := by gcongr
          have h5 : L / rho ≤ L / delta := by gcongr
          exact h4.trans h5
        have hT_sub1 : T ⊆ Set.Icc left (left + length) := by intro x hx; exact hx.2
        have hcov : (↑(Metric.externalCoveringNumber ⟨rho, hrho⟩ T) : ENNReal) ≤
            ENNReal.ofReal (length / rho) + 2 :=
          externalCoveringNumber_subset_interval hrho_pos (by linarith) hT_sub1
        have h9 : length / rho + 2 ≤ 3 * (length / rho) := by linarith
        have h10 := h_ineq (length / rho) hx1 hx2
        have h_add : ENNReal.ofReal (length / rho) + 2 = ENNReal.ofReal (length / rho + 2) := by
          have h8 : 0 ≤ length / rho := by positivity
          rw [ENNReal.ofReal_add h8 (by norm_num)] <;> simp
        calc
          (↑(Metric.externalCoveringNumber ⟨rho, hrho⟩ T) : ENNReal)
            ≤ ENNReal.ofReal (length / rho) + 2 := hcov
          _ = ENNReal.ofReal (length / rho + 2) := h_add
          _ ≤ ENNReal.ofReal (3 * (length / rho)) := ENNReal.ofReal_le_ofReal h9
          _ ≤ C * Kakeya.realRpowENN (length / rho) (1 - sigma) := h10

      · -- Case 2b: length > L
        have hL_lt_length : L < length := by linarith
        have hy1 : 1 ≤ L / rho := by
          calc 1 = rho / rho := by field_simp [hrho_pos.ne']
            _ ≤ L / rho := by gcongr
        have hy2 : L / rho ≤ L / delta := by
          have h1 : delta ≤ rho := hdelta_le_rho
          gcongr
        have hT_subL : T ⊆ Set.Icc (-L/2) (L/2) := by
          intro x hx; exact hS (hT_sub2 hx)
        have hT_subL' : T ⊆ Set.Icc (-L / 2) (-L / 2 + L) := by
          have h_eq : (-L / 2 + L) = L / 2 := by ring
          rw [h_eq]
          exact hT_subL
        have hcov : (↑(Metric.externalCoveringNumber ⟨rho, hrho⟩ T) : ENNReal) ≤
            ENNReal.ofReal (L / rho) + 2 :=
          externalCoveringNumber_subset_interval
            (S := T) (left := -L / 2) (length := L) (ε := rho)
            hrho_pos hL_pos.le hT_subL'
        have h9 : L / rho + 2 ≤ 3 * (L / rho) := by linarith
        have h10 := h_ineq (L / rho) hy1 hy2
        have h11 : C * Kakeya.realRpowENN (L / rho) (1 - sigma) ≤
            C * Kakeya.realRpowENN (length / rho) (1 - sigma) := by
          have h12 : L / rho ≤ length / rho := by
            have h121 : L < length := hL_lt_length
            exact div_lt_div_of_pos_right h121 hrho_pos |>.le
          have h13 : 0 ≤ 1 - sigma := by linarith
          have h14 : Kakeya.realRpowENN (L / rho) (1 - sigma) ≤
              Kakeya.realRpowENN (length / rho) (1 - sigma) :=
            realRpowENN_mono (by positivity) h12 (1 - sigma) h13
          gcongr
        have h_add : ENNReal.ofReal (L / rho) + 2 = ENNReal.ofReal (L / rho + 2) := by
          have h8 : 0 ≤ L / rho := by positivity
          rw [ENNReal.ofReal_add h8 (by norm_num)] <;> simp
        calc
          (↑(Metric.externalCoveringNumber ⟨rho, hrho⟩ T) : ENNReal)
            ≤ ENNReal.ofReal (L / rho) + 2 := hcov
          _ = ENNReal.ofReal (L / rho + 2) := h_add
          _ ≤ ENNReal.ofReal (3 * (L / rho)) := ENNReal.ofReal_le_ofReal h9
          _ ≤ C * Kakeya.realRpowENN (L / rho) (1 - sigma) := h10
          _ ≤ C * Kakeya.realRpowENN (length / rho) (1 - sigma) := h11

  refine ⟨hdelta_pos, halpha_pos, halpha_le_one, hC_one, hC_ne_top, ?_⟩
  exact h_main

/-- Geometric bound: the scalar projection onto `(1,0,0)` of any horizontal
slice of a paper tube shading union is contained in `[-1, 1]`, because
`wz1PaperTubeCarrier` is cropped to `axisBox 2 2 2`. -/
lemma horizontal_slice_projection_bounded
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading family}
    (z : ℝ) :
    scalarProjection (globalGrainDirection (0 : ℝ))
      (horizontalSlice shading.union z)
      ⊆ Set.Icc (-(1 : ℝ)) (1 : ℝ) := by
  intro y hy
  rcases (mem_image _ _ _).mp hy with ⟨x, hx, rfl⟩
  have hx_in_union : x ∈ shading.union := hx.1
  rcases hx_in_union with ⟨i, hi⟩
  have h_sub : shading.carrier i ⊆ wz1PaperTubeCarrier (family.tube i) := by
    simpa [wz1PaperBodyFamily] using shading.subset_body i
  have hx_in_carrier : x ∈ wz1PaperTubeCarrier (family.tube i) := h_sub hi
  have hx_in_box : x ∈ Kakeya.Streamlined.axisBox 2 2 2 := hx_in_carrier.2
  have h_abs2 : |x (0 : Fin 3)| ≤ 2 / 2 := hx_in_box.1
  have h_abs : |x (0 : Fin 3)| ≤ 1 := by
    have h_eq : (2 / 2 : ℝ) = 1 := by norm_num
    rw [h_eq] at h_abs2
    exact h_abs2
  have h_dir : globalGrainDirection (0 : ℝ) = EuclideanSpace.single (0 : Fin 3) 1 := by
    simp [globalGrainDirection]
    <;> ext i <;> fin_cases i <;> simp
  have h_inner : inner ℝ x (globalGrainDirection (0 : ℝ)) = x (0 : Fin 3) := by
    rw [h_dir]
    have h : inner ℝ x (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) = (1 : ℝ) * x (0 : Fin 3) :=
      EuclideanSpace.inner_single_right (0 : Fin 3) (1 : ℝ) x
    rw [h]
    <;> simp
  rw [h_inner]
  exact ⟨by linarith [abs_le.mp h_abs], by linarith [abs_le.mp h_abs]⟩

/-- Key real inequality for the local AD trivial interval bound.

If `outputLoss > sigma/2` and `delta` is small enough that
`3 * 2^sigma ≤ (1/delta)^(outputLoss - sigma/2)`, then for any
`1 ≤ x ≤ 2/√rho` with `rho ≥ delta`, we have
`3 * x ≤ delta^(-outputLoss) * x^(1-sigma)`.

This is the local-AD analogue of `bounded_interval_key_ineq`, using the
tighter bound `2/√rho` (coming from `L/rho` where `L = 2√rho`) instead
of `L/delta`. -/
lemma local_ad_key_ineq
    {delta rho sigma outputLoss : ℝ}
    (hdelta_pos : 0 < delta)
    (hrho_pos : 0 < rho)
    (hdelta_le_rho : delta ≤ rho)
    (hsigma_pos : 0 < sigma)
    (h_half : sigma / 2 < outputLoss)
    (hsmall : 3 * (2 : ℝ)^sigma ≤ (1 / delta)^(outputLoss - sigma / 2))
    {x : ℝ} (hx1 : 1 ≤ x) (hx2 : x ≤ 2 / Real.sqrt rho) :
    3 * x ≤ (delta ^ (-outputLoss)) * (x ^ (1 - sigma)) := by
  have hx_pos : 0 < x := by linarith
  have hrho_sqrt_pos : 0 < Real.sqrt rho := Real.sqrt_pos.mpr hrho_pos
  have hdelta_sqrt_pos : 0 < Real.sqrt delta := Real.sqrt_pos.mpr hdelta_pos
  have h1 : 2 / Real.sqrt rho ≤ 2 / Real.sqrt delta := by
    gcongr
    <;> exact Real.sqrt_le_sqrt hdelta_le_rho
  have h2 : x ≤ 2 / Real.sqrt delta := hx2.trans h1
  have h3 : x ^ sigma ≤ (2 / Real.sqrt delta) ^ sigma :=
    Real.rpow_le_rpow (by linarith) h2 (by linarith)
  have h4 : (2 / Real.sqrt delta) ^ sigma = (2 : ℝ)^sigma * delta ^ (-sigma / 2) := by
    have hsqrt_pos : 0 < Real.sqrt delta := Real.sqrt_pos.mpr hdelta_pos
    have h41 : (2 / Real.sqrt delta) ^ sigma = (2 : ℝ)^sigma * (Real.sqrt delta)^(-sigma) := by
      have h : (2 / Real.sqrt delta) ^ sigma = (2 : ℝ)^sigma / (Real.sqrt delta)^sigma :=
        Real.div_rpow (by norm_num) (Real.sqrt_nonneg delta) sigma
      rw [h]
      have h2 : (2 : ℝ)^sigma / (Real.sqrt delta)^sigma = (2 : ℝ)^sigma * ((Real.sqrt delta)^sigma)⁻¹ := by
        field_simp
      rw [h2]
      have h3 : ((Real.sqrt delta)^sigma)⁻¹ = (Real.sqrt delta)^(-sigma) := by
        rw [Real.rpow_neg (Real.sqrt_nonneg delta)]
        <;> ring
      rw [h3] <;> ring
    rw [h41]
    have h42 : (Real.sqrt delta)^(-sigma) = delta ^ (-sigma / 2) := by
      have h43 : Real.sqrt delta = delta ^ (1 / 2 : ℝ) := by
        rw [Real.sqrt_eq_rpow]
      rw [h43]
      have h44 : (delta ^ (1 / 2 : ℝ))^(-sigma) = delta ^ ((1 / 2 : ℝ) * (-sigma)) := by
        rw [← Real.rpow_mul hdelta_pos.le]
      rw [h44]
      have h45 : (1 / 2 : ℝ) * (-sigma) = -sigma / 2 := by ring
      rw [h45]
    rw [h42] <;> ring
  have h5 : 3 * x ^ sigma ≤ 3 * (2 : ℝ)^sigma * delta ^ (-sigma / 2) := by
    calc 3 * x ^ sigma
      ≤ 3 * (2 / Real.sqrt delta) ^ sigma := by gcongr
    _ = 3 * (2 : ℝ)^sigma * delta ^ (-sigma / 2) := by rw [h4] <;> ring
  have h6 : (1 / delta)^(outputLoss - sigma / 2) = delta ^ (sigma / 2 - outputLoss) := by
    have h61 : (1 / delta)^(outputLoss - sigma / 2) = (delta ^ (outputLoss - sigma / 2))⁻¹ := by
      rw [Real.div_rpow (by norm_num) hdelta_pos.le] <;> simp
    have h62 : sigma / 2 - outputLoss = -(outputLoss - sigma / 2) := by ring
    rw [h62, Real.rpow_neg hdelta_pos.le]
    <;> rw [h61] <;> ring
  have h7 : 3 * (2 : ℝ)^sigma * delta ^ (-sigma / 2) ≤ delta ^ (-outputLoss) := by
    calc 3 * (2 : ℝ)^sigma * delta ^ (-sigma / 2)
      ≤ (1 / delta)^(outputLoss - sigma / 2) * delta ^ (-sigma / 2) := by gcongr
    _ = delta ^ (sigma / 2 - outputLoss) * delta ^ (-sigma / 2) := by rw [h6]
    _ = delta ^ (-outputLoss) := by
      have h_exp : delta ^ (sigma / 2 - outputLoss) * delta ^ (-sigma / 2) =
          delta ^ ((sigma / 2 - outputLoss) + (-sigma / 2)) := by
        rw [← Real.rpow_add hdelta_pos]
      rw [h_exp]
      have h_sum : (sigma / 2 - outputLoss) + (-sigma / 2) = -outputLoss := by ring
      rw [h_sum]
  have h8 : 3 * x ^ sigma ≤ delta ^ (-outputLoss) := h5.trans h7
  have h9 : (3 * x ^ sigma) * x ^ (1 - sigma) ≤
      (delta ^ (-outputLoss)) * x ^ (1 - sigma) :=
    mul_le_mul_of_nonneg_right h8 (by positivity)
  have h10 : x ^ sigma * x ^ (1 - sigma) = x := by
    have h11 : x ^ sigma * x ^ (1 - sigma) = x ^ (sigma + (1 - sigma)) := by
      rw [← Real.rpow_add hx_pos]
    rw [h11]
    have h12 : sigma + (1 - sigma) = 1 := by ring
    rw [h12]
    simp
  have h13 : (3 * x ^ sigma) * x ^ (1 - sigma) = 3 * x := by
    calc (3 * x ^ sigma) * x ^ (1 - sigma)
      = 3 * (x ^ sigma * x ^ (1 - sigma)) := by ring
    _ = 3 * x := by rw [h10]
  rw [h13] at h9
  exact h9

/-- Global AD transport for the easy case `outputLoss > sigma`.

Uses constant slope `0` (trivially Lip 1) and `bounded_interval_paper_ad1`.
Horizontal slice projections onto the x-direction are contained in `[-1, 1]`,
so the bounded interval AD bound applies.

For sufficiently small `delta`, the constant `3 * 2^sigma * delta^{-sigma}`
is bounded by `delta^{-outputLoss}` when `outputLoss > sigma`.

This proves the `PureWZ2GlobalADTransportStatement` for the case
`outputLoss > sigma`. The case `outputLoss ≤ sigma` requires the anchored
transport with local AD. -/
lemma global_ad_transport_easy_case
    {sigma outputLoss : ℝ}
    (hsigma_pos : 0 < sigma) (hsigma_one : sigma < 1)
    (hloss_gt_sigma : sigma < outputLoss)
    (hloss_pos : 0 < outputLoss) :
    ∃ (delta₀ : ℝ), 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ (delta : ℝ), 0 < delta → delta ≤ delta₀ →
        ∀ (family : Kakeya.Streamlined.TubeFamily delta)
          (shading : WZ1PaperTubeShading family),
          WZ1PaperIsLineClass family →
          WZ1PaperIsCubicalShading shading →
          Nonempty (PureWZ2LipschitzGlobalGrainData shading sigma
            (Kakeya.realRpowENN delta (-outputLoss))) := by
  let exponent := outputLoss - sigma
  have hexp_pos : 0 < exponent := by linarith
  let threshold : ℝ := (3 * (2 : ℝ)^sigma)^(-1 / exponent)
  have hthreshold_pos : 0 < threshold := by positivity
  let delta₀ : ℝ := min 1 threshold
  have hdelta₀_pos : 0 < delta₀ := by positivity
  have hdelta₀_le_one : delta₀ ≤ 1 := min_le_left _ _
  have hdelta₀_le_threshold : delta₀ ≤ threshold := min_le_right _ _
  refine ⟨delta₀, hdelta₀_pos, hdelta₀_le_one, ?_⟩
  intro delta hdelta_pos hdelta_le_delta₀ family shading hline_class hcubical
  have hsmall : 3 * (2 : ℝ)^sigma ≤ (1 / delta)^(outputLoss - sigma) := by
    have h1 : delta ≤ threshold := hdelta_le_delta₀.trans hdelta₀_le_threshold
    have h2 : 1 / threshold ≤ 1 / delta := by
      apply one_div_le_one_div_of_le <;> linarith
    have h3 : (1 / threshold)^exponent ≤ (1 / delta)^exponent := by
      gcongr <;> linarith
    have h_pos : 0 < 3 * (2 : ℝ)^sigma := by positivity
    have h_nonneg : 0 ≤ 3 * (2 : ℝ)^sigma := by positivity
    have h41 : 1 / threshold = (3 * (2 : ℝ)^sigma)^(1 / exponent) := by
      have h2 : (3 * (2 : ℝ)^sigma)^(-1 / exponent) = ((3 * (2 : ℝ)^sigma)^(1 / exponent))⁻¹ := by
        have h21 : (-1 / exponent : ℝ) = -(1 / exponent) := by ring
        rw [h21]
        exact Real.rpow_neg h_nonneg (1 / exponent)
      have h4 : 1 / ((3 * (2 : ℝ)^sigma)^(-1 / exponent)) = (3 * (2 : ℝ)^sigma)^(1 / exponent) := by
        rw [h2]
        field_simp
      simpa [threshold] using h4
    have h4 : (1 / threshold)^exponent = 3 * (2 : ℝ)^sigma := by
      rw [h41]
      have h5 : ((3 * (2 : ℝ)^sigma)^(1 / exponent))^exponent = (3 * (2 : ℝ)^sigma)^((1 / exponent) * exponent) := by
        rw [Real.rpow_mul h_nonneg]
        <;> ring
      rw [h5]
      have h6 : (1 / exponent) * exponent = 1 := by
        field_simp [hexp_pos.ne'] <;> ring
      rw [h6]
      simp
    rw [h4] at h3
    exact h3
  let slope : ℝ → ℝ := fun _ => 0
  have hslope_lip : LipschitzOnWith 1 slope (Set.Icc (-1 : ℝ) 1) := by
    intro x _ y _
    simp [slope, dist_eq_norm] <;> norm_num
  have hglobal_ad : ∀ (z : ℝ), z ∈ Set.Icc (-1 : ℝ) 1 →
      PureWZ2PaperADSet1
        (scalarProjection (globalGrainDirection (slope z))
          (horizontalSlice shading.union z))
        delta (1 - sigma) (Kakeya.realRpowENN delta (-outputLoss)) := by
    intro z hz
    have h_dir : globalGrainDirection (slope z) = globalGrainDirection (0 : ℝ) := by
      simp [slope]
    rw [h_dir]
    have h_proj_bounded : scalarProjection (globalGrainDirection (0 : ℝ))
        (horizontalSlice shading.union z) ⊆ Set.Icc (-(1 : ℝ)) (1 : ℝ) :=
      horizontal_slice_projection_bounded z
    have h_interval_eq : Set.Icc (-(2 : ℝ) / 2) (2 / 2) = Set.Icc (-(1 : ℝ)) (1 : ℝ) := by
      norm_num
    have h_proj_bounded' : scalarProjection (globalGrainDirection (0 : ℝ))
        (horizontalSlice shading.union z) ⊆ Set.Icc (-(2 : ℝ) / 2) (2 / 2) := by
      rw [h_interval_eq]
      exact h_proj_bounded
    exact bounded_interval_paper_ad1
      hdelta_pos (by linarith) hsigma_pos hsigma_one hloss_gt_sigma
      (by norm_num) hsmall h_proj_bounded'
  exact ⟨PureWZ2LipschitzGlobalGrainData.ofRealFunction
    slope hslope_lip hglobal_ad⟩

/-- Direct construction of global grain data when outputLoss > sigma,
given the smallness condition `3 * 2^sigma ≤ (1/epsilon)^(outputLoss - sigma)`.

Uses constant slope 0 (Lip 1) and `bounded_interval_paper_ad1`. -/
def global_grain_data_direct
    {sigma outputLoss epsilon : ℝ}
    {family : Kakeya.Streamlined.TubeFamily epsilon}
    {shading : WZ1PaperTubeShading family}
    (hsigma_pos : 0 < sigma)
    (hsigma_lt_one : sigma < 1)
    (hloss_gt_sigma : sigma < outputLoss)
    (hepsilon_pos : 0 < epsilon)
    (hepsilon_le_one : epsilon ≤ 1)
    (hsmall : 3 * (2 : ℝ)^sigma ≤ (1 / epsilon)^(outputLoss - sigma)) :
    PureWZ2LipschitzGlobalGrainData shading sigma
      (Kakeya.realRpowENN epsilon (-outputLoss)) := by
  let slope : ℝ → ℝ := fun _ => 0
  have hslope_lip : LipschitzOnWith 1 slope (Set.Icc (-1 : ℝ) 1) := by
    intro x _ y _
    simp [slope]
  have hglobal_ad : ∀ (z : ℝ), z ∈ Set.Icc (-1 : ℝ) 1 →
      PureWZ2PaperADSet1
        (scalarProjection (globalGrainDirection (slope z))
          (horizontalSlice shading.union z))
        epsilon (1 - sigma) (Kakeya.realRpowENN epsilon (-outputLoss)) := by
    intro z _
    have h_dir : globalGrainDirection (slope z) = globalGrainDirection (0 : ℝ) := by
      simp [slope]
    rw [h_dir]
    have h_proj_bounded : scalarProjection (globalGrainDirection (0 : ℝ))
        (horizontalSlice shading.union z) ⊆ Set.Icc (-(1 : ℝ)) (1 : ℝ) :=
      horizontal_slice_projection_bounded z
    have h_interval_eq : Set.Icc (-(2 : ℝ) / 2) (2 / 2) = Set.Icc (-(1 : ℝ)) (1 : ℝ) := by
      norm_num
    have h_proj_bounded' : scalarProjection (globalGrainDirection (0 : ℝ))
        (horizontalSlice shading.union z) ⊆ Set.Icc (-(2 : ℝ) / 2) (2 / 2) := by
      rw [h_interval_eq]
      exact h_proj_bounded
    exact bounded_interval_paper_ad1
      hepsilon_pos (by linarith) hsigma_pos hsigma_lt_one hloss_gt_sigma
      (by norm_num) hsmall h_proj_bounded'
  exact PureWZ2LipschitzGlobalGrainData.ofRealFunction
    slope hslope_lip hglobal_ad

/-- Convert `epsilon ≤ (3 * 2^sigma)^(-1/(outputLoss - sigma))` to
`3 * 2^sigma ≤ (1/epsilon)^(outputLoss - sigma)`. -/
lemma threshold_to_small_condition
    {sigma outputLoss epsilon : ℝ}
    (hloss_gt_sigma : sigma < outputLoss)
    (hepsilon_pos : 0 < epsilon)
    (hthreshold : epsilon ≤ (3 * (2 : ℝ)^sigma)^(-1 / (outputLoss - sigma))) :
    3 * (2 : ℝ)^sigma ≤ (1 / epsilon)^(outputLoss - sigma) := by
  set threshold : ℝ := (3 * (2 : ℝ)^sigma)^(-1 / (outputLoss - sigma)) with hthreshold_def
  have hexp_pos : 0 < outputLoss - sigma := by linarith
  have hthreshold_pos : 0 < threshold := by positivity
  have h1 : 1 / threshold ≤ 1 / epsilon :=
    one_div_le_one_div_of_le hepsilon_pos hthreshold
  have h2 : (1 / threshold)^(outputLoss - sigma) ≤ (1 / epsilon)^(outputLoss - sigma) := by
    gcongr
  have h3 : 1 / threshold = (3 * (2 : ℝ)^sigma)^(1 / (outputLoss - sigma)) := by
    have h4 : threshold = ((3 * (2 : ℝ)^sigma)^(1 / (outputLoss - sigma)))⁻¹ := by
      rw [hthreshold_def]
      have h5 : (-1 / (outputLoss - sigma) : ℝ) = -(1 / (outputLoss - sigma)) := by ring
      rw [h5]
      rw [Real.rpow_neg (by positivity)]
    rw [h4]
    field_simp
  have h4 : (1 / threshold)^(outputLoss - sigma) = 3 * (2 : ℝ)^sigma := by
    rw [h3]
    have h5 : ((3 * (2 : ℝ)^sigma)^(1 / (outputLoss - sigma)))^(outputLoss - sigma) =
        (3 * (2 : ℝ)^sigma)^((1 / (outputLoss - sigma)) * (outputLoss - sigma)) := by
      rw [Real.rpow_mul (by positivity)]
    rw [h5]
    have h6 : (1 / (outputLoss - sigma)) * (outputLoss - sigma) = 1 := by
      field_simp [hexp_pos.ne']
    rw [h6]
    simp
  rw [h4] at h2
  exact h2

end Kakeya.Assouad

end
