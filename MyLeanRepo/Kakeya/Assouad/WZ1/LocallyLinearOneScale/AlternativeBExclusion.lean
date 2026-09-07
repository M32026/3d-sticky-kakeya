import MyLeanRepo.Kakeya.Assouad.WZ1.Definitions
import MyLeanRepo.Kakeya.Assouad.WZ1.IntervalADHelpers
import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers
import Mathlib.Data.Real.ENatENNReal
import Mathlib.Tactic

/-!
# Rule out Alternative B of the projection dichotomy using AD

Abstract lemma: if a bounded set `dotDiff` is AD at scale `deltaGraph` with
exponent `1-sigma`, then Alternative B's covering lower bound of exponent
`1-epsilon` (with `epsilon < sigma`) leads to a contradiction when the AD
constant satisfies `C' * 100 * deltaGraph^(eta*(sigma-epsilon)) < 1`.
-/

namespace Kakeya.Assouad

open Metric Set

/-- Cover `[-4,4]` by 4 unit balls centered at -3, -1, 1, 3. -/
private lemma icc_four_four_cover_by_four :
    Set.Icc (-4 : ℝ) 4 ⊆
      ⋃ c ∈ ({-3, -1, 1, 3} : Finset ℝ), Metric.closedBall c 1 := by
  intro x hx
  have h1 : -4 ≤ x := hx.1
  have h2 : x ≤ 4 := hx.2
  by_cases h3 : x ≤ -2
  · have h4 : dist x (-3 : ℝ) ≤ 1 := by
      simp [Real.dist_eq, abs_le] <;> constructor <;> linarith
    exact Set.mem_iUnion₂.mpr ⟨-3, by simp, h4⟩
  · by_cases h4 : x ≤ 0
    · have h5 : dist x (-1 : ℝ) ≤ 1 := by
        simp [Real.dist_eq, abs_le] <;> constructor <;> linarith
      exact Set.mem_iUnion₂.mpr ⟨-1, by simp, h5⟩
    · by_cases h5 : x ≤ 2
      · have h6 : dist x (1 : ℝ) ≤ 1 := by
          simp [Real.dist_eq, abs_le] <;> constructor <;> linarith
        exact Set.mem_iUnion₂.mpr ⟨1, by simp, h6⟩
      · have h7 : dist x (3 : ℝ) ≤ 1 := by
          simp [Real.dist_eq, abs_le] <;> constructor <;> linarith
        exact Set.mem_iUnion₂.mpr ⟨3, by simp, h7⟩

/-- If `A ⊆ closedBall x ε`, then `externalCoveringNumber ε A ≤ 1`. -/
private lemma externalCoveringNumber_le_one {A : Set ℝ} {x : ℝ} {ε : NNReal}
    (h : A ⊆ Metric.closedBall x ε) :
    (Metric.externalCoveringNumber ε A : ENNReal) ≤ 1 := by
  have h_cover : Metric.IsCover ε A ({x} : Set ℝ) := by
    intro y hy
    refine ⟨x, by simp, ?_⟩
    simpa [Set.mem_setOf_eq] using dist_le_coe.mp (h hy)
  have h1 : Metric.externalCoveringNumber ε A ≤ 1 := by
    have h2 := h_cover.externalCoveringNumber_le_encard
    simpa using h2
  have h3 : (Metric.externalCoveringNumber ε A : ENNReal) ≤ (1 : ENNReal) := by
    have h4 : (Metric.externalCoveringNumber ε A : ENNReal) ≤ ↑(1 : ℕ∞) :=
      ENat.toENNReal_le.mpr h1
    simpa using h4
  exact h3

/--
Pure real-arithmetic contradiction.
-/
private lemma real_contradiction
    {deltaGraph sigma epsilon eta C K x : ℝ}
    (hdeltaGraph_pos : 0 < deltaGraph)
    (hdeltaGraph_one : deltaGraph < 1)
    (hsigma_one : sigma < 1)
    (hepsilon_lt_sigma : epsilon < sigma)
    (heta_pos : 0 < eta)
    (hx_pos : 0 < x)
    (hx_lower : Real.rpow deltaGraph (-eta) ≤ x)
    (hC_nonneg : 0 ≤ C)
    (hK_nonneg : 0 ≤ K)
    (hK_le : K ≤ 100)
    (h_main : Real.rpow x (sigma - epsilon) * Real.rpow 2 (1 - sigma) ≤ K * C)
    (h_absorb : C * 100 * Real.rpow deltaGraph (eta * (sigma - epsilon)) < 1) :
    False := by
  set a : ℝ := sigma - epsilon with ha_def
  set b : ℝ := eta * a with hb_def
  have ha_pos : 0 < a := by linarith
  have hb_pos : 0 < b := by positivity
  have h1 : 0 < Real.rpow deltaGraph (-eta) := Real.rpow_pos_of_pos hdeltaGraph_pos (-eta)
  have h2 : Real.rpow (Real.rpow deltaGraph (-eta)) a ≤ Real.rpow x a :=
    Real.rpow_le_rpow h1.le hx_lower ha_pos.le
  have h31 : (Real.rpow deltaGraph (-eta)) ^ a = Real.rpow deltaGraph ((-eta) * a) :=
    (Real.rpow_mul hdeltaGraph_pos.le (-eta) a).symm
  have h32 : (-eta) * a = -b := by
    simp [hb_def, ha_def] <;> ring
  have h3 : Real.rpow (Real.rpow deltaGraph (-eta)) a = Real.rpow deltaGraph (-b) := by
    have h33 : Real.rpow (Real.rpow deltaGraph (-eta)) a = (Real.rpow deltaGraph (-eta)) ^ a := by rfl
    rw [h33, h31, h32]
  have h4 : Real.rpow deltaGraph (-b) ≤ Real.rpow x a := by
    rw [← h3]; exact h2
  have h_rpow2_nonneg : 0 ≤ Real.rpow 2 (1 - sigma) := Real.rpow_nonneg (by norm_num) _
  have h6 : Real.rpow deltaGraph (-b) * Real.rpow 2 (1 - sigma) ≤ K * C := by
    calc
      _ ≤ Real.rpow x a * Real.rpow 2 (1 - sigma) := by
        exact mul_le_mul_of_nonneg_right h4 h_rpow2_nonneg
      _ ≤ K * C := h_main
  have h7 : Real.rpow deltaGraph (-b) * Real.rpow deltaGraph b = 1 := by
    have h71 : Real.rpow deltaGraph (-b) * Real.rpow deltaGraph b =
        Real.rpow deltaGraph ((-b) + b) := (Real.rpow_add hdeltaGraph_pos (-b) b).symm
    have h72 : (-b) + b = 0 := by ring
    rw [h71, h72]; simp
  have h8 : 0 < Real.rpow deltaGraph b := Real.rpow_pos_of_pos hdeltaGraph_pos b
  have h9 : Real.rpow 2 (1 - sigma) ≤ K * C * Real.rpow deltaGraph b := by
    calc
      Real.rpow 2 (1 - sigma)
        = (Real.rpow deltaGraph (-b) * Real.rpow deltaGraph b) * Real.rpow 2 (1 - sigma) := by
          rw [h7] <;> ring
      _ = Real.rpow deltaGraph (-b) * Real.rpow 2 (1 - sigma) * Real.rpow deltaGraph b := by ring
      _ ≤ K * C * Real.rpow deltaGraph b := by gcongr
  have h10 : 1 ≤ Real.rpow 2 (1 - sigma) := by
    apply Real.one_le_rpow <;> linarith
  have h11 : K * C * Real.rpow deltaGraph b ≤ 100 * C * Real.rpow deltaGraph b := by
    have h111 : 0 ≤ C * Real.rpow deltaGraph b := by positivity
    nlinarith
  have h13 : K * C * Real.rpow deltaGraph b < 1 := by
    calc
      K * C * Real.rpow deltaGraph b
        ≤ 100 * C * Real.rpow deltaGraph b := h11
      _ = C * 100 * Real.rpow deltaGraph b := by ring
      _ < 1 := by simpa [hb_def, ha_def] using h_absorb
  linarith

/-- Convert `realRpowENN x a ≤ C' * realRpowENN y b` to real inequality. -/
private lemma ennreal_mul_le_to_real {x y a b : ℝ} {C' : ENNReal}
    (hC_top : C' ≠ ⊤) (hx_pos : 0 ≤ x) (hy_pos : 0 ≤ y)
    (h : Kakeya.realRpowENN x a ≤ C' * Kakeya.realRpowENN y b) :
    Real.rpow x a ≤ C'.toReal * Real.rpow y b := by
  have h1 : (Kakeya.realRpowENN x a).toReal ≤ (C' * Kakeya.realRpowENN y b).toReal :=
    (ENNReal.toReal_le_toReal (by simp [Kakeya.realRpowENN])
      (ENNReal.mul_ne_top hC_top (by simp [Kakeya.realRpowENN]))).mpr h
  have h2 : (Kakeya.realRpowENN x a).toReal = Real.rpow x a := by
    rw [Kakeya.realRpowENN, ENNReal.toReal_ofReal] <;> exact Real.rpow_nonneg hx_pos _
  have h3 : (C' * Kakeya.realRpowENN y b).toReal = C'.toReal * Real.rpow y b := by
    rw [ENNReal.toReal_mul, Kakeya.realRpowENN, ENNReal.toReal_ofReal] <;> exact Real.rpow_nonneg hy_pos _
  rw [h2, h3] at h1
  exact h1

/--
Abstract Alternative B exclusion lemma.
-/
lemma alternative_b_exclusion
    {dotDiff : Set ℝ}
    {deltaGraph sigma epsilon eta δ_AD : ℝ}
    {C' : ENNReal}
    (hdeltaGraph_pos : 0 < deltaGraph)
    (hdeltaGraph_one : deltaGraph < 1)
    (hsigma_pos : 0 < sigma)
    (hsigma_one : sigma < 1)
    (hepsilon_pos : 0 < epsilon)
    (hepsilon_lt_sigma : epsilon < sigma)
    (heta_pos : 0 < eta)
    (hC_top : C' ≠ ⊤)
    (hAD : IsADSet1 dotDiff δ_AD (1 - sigma) C')
    (rho_B center radius : ℝ)
    (hδ_AD_le_rhoB : δ_AD ≤ rho_B)
    (hrho_B_one : rho_B ≤ 1)
    (hradius_pos : 0 < radius)
    (hradius_lower : Real.rpow deltaGraph (-eta) * rho_B ≤ 2 * radius)
    (hcover_lower :
      Kakeya.realRpowENN (2 * radius / rho_B) (1 - epsilon) ≤
      (↑(Metric.externalCoveringNumber
        (Real.toNNReal rho_B)
          (dotDiff ∩ Metric.closedBall center radius)) : ENNReal))
    (hconstant_absorb :
      C' * (100 : ENNReal) *
        Kakeya.realRpowENN deltaGraph (eta * (sigma - epsilon)) < 1) :
    False := by
  have hsigma_epsilon_pos : 0 < sigma - epsilon := by linarith
  set x : ℝ := 2 * radius / rho_B with hx_def
  have hδ_AD_pos : 0 < δ_AD := hAD.1
  have hrhoB_pos : 0 < rho_B := hδ_AD_pos.trans_le hδ_AD_le_rhoB
  have hrhoB_nonneg : 0 ≤ rho_B := by linarith
  have hx_pos : 0 < x := by positivity
  have hx_lower : Real.rpow deltaGraph (-eta) ≤ x := by
    have h2 : Real.rpow deltaGraph (-eta) ≤ (2 * radius) / rho_B := by
      calc
        Real.rpow deltaGraph (-eta)
          = (Real.rpow deltaGraph (-eta) * rho_B) / rho_B := by
            field_simp [hrhoB_pos.ne'] <;> ring
        _ ≤ (2 * radius) / rho_B := by gcongr
    simpa [hx_def] using h2
  have hx_gt_one : 1 < x := by
    have h1_pos : 0 < Real.rpow deltaGraph eta := Real.rpow_pos_of_pos hdeltaGraph_pos eta
    have h1_lt : Real.rpow deltaGraph eta < 1 :=
      Real.rpow_lt_one hdeltaGraph_pos.le hdeltaGraph_one heta_pos
    have h_inv : Real.rpow deltaGraph (-eta) = (Real.rpow deltaGraph eta)⁻¹ :=
      Real.rpow_neg hdeltaGraph_pos.le eta
    have h_gt : 1 < (Real.rpow deltaGraph eta)⁻¹ := by
      calc (Real.rpow deltaGraph eta)⁻¹
        = 1 / (Real.rpow deltaGraph eta) := by simp
      _ > 1 / 1 := by gcongr
      _ = 1 := by norm_num
    have h_lower2 : (Real.rpow deltaGraph eta)⁻¹ ≤ x := by
      rw [← h_inv]; exact hx_lower
    linarith
  rcases hAD with ⟨_, _, _, _, hE_bounded, hcover⟩
  let eps_nn : NNReal := ⟨rho_B, hrhoB_nonneg⟩
  have h_eps_coe : (eps_nn : ℝ) = rho_B := by
    exact Subtype.coe_mk rho_B hrhoB_nonneg
  have h_eps_eq : eps_nn = Real.toNNReal rho_B := by
    apply NNReal.coe_injective
    simp [eps_nn, Real.toNNReal, hrhoB_nonneg] <;> rfl
  set C_real : ℝ := C'.toReal with hC_real_def
  have hC_real_nonneg : 0 ≤ C_real := ENNReal.toReal_nonneg

  -- Absorption condition in real
  set A_enr : ENNReal := C' * (100 : ENNReal) *
      Kakeya.realRpowENN deltaGraph (eta * (sigma - epsilon)) with hA_enr
  have hA_ne_top : A_enr ≠ ⊤ := ne_top_of_lt hconstant_absorb
  have h_rpow_nonneg : 0 ≤ Real.rpow deltaGraph (eta * (sigma - epsilon)) :=
    Real.rpow_nonneg hdeltaGraph_pos.le _
  have h_absorb_real : C_real * 100 *
      Real.rpow deltaGraph (eta * (sigma - epsilon)) < 1 := by
    have h2 : A_enr.toReal < 1 :=
      (ENNReal.toReal_lt_toReal hA_ne_top (by simp)).mpr hconstant_absorb
    have h_rpow_real : (Kakeya.realRpowENN deltaGraph (eta * (sigma - epsilon))).toReal =
        Real.rpow deltaGraph (eta * (sigma - epsilon)) := by
      rw [Kakeya.realRpowENN, ENNReal.toReal_ofReal] <;> exact h_rpow_nonneg
    have h100 : ((100 : ENNReal).toReal) = 100 := by simp
    have h3 : A_enr.toReal = C_real * 100 *
        Real.rpow deltaGraph (eta * (sigma - epsilon)) := by
      simp only [hA_enr]
      rw [ENNReal.toReal_mul, ENNReal.toReal_mul, hC_real_def, h100, h_rpow_real] <;> ring
    rw [h3] at h2
    exact h2

  by_cases hradius_le_rhoB : radius ≤ rho_B
  · -- Case 1: radius ≤ rho_B, one ball covers
    have h_sub : dotDiff ∩ Metric.closedBall center radius ⊆
        Metric.closedBall center eps_nn := by
      intro y hy
      have h_dist : dist y center ≤ radius := hy.2
      have h_dist' : dist y center ≤ rho_B := h_dist.trans hradius_le_rhoB
      have h_eps : (eps_nn : ℝ) = rho_B := h_eps_coe
      rw [h_eps]
      exact h_dist'
    have h_cover_upper : (Metric.externalCoveringNumber eps_nn
          (dotDiff ∩ Metric.closedBall center radius) : ENNReal) ≤ 1 :=
      externalCoveringNumber_le_one h_sub
    have h_cover_upper' : (Metric.externalCoveringNumber (Real.toNNReal rho_B)
          (dotDiff ∩ Metric.closedBall center radius) : ENNReal) ≤ 1 := by
      rw [← h_eps_eq]; exact h_cover_upper
    have h_lower_gt_one : (1 : ENNReal) <
        Kakeya.realRpowENN x (1 - epsilon) := by
      have h3 : (1 : ℝ) < Real.rpow x (1 - epsilon) := by
        apply Real.one_lt_rpow <;> linarith
      have h4 : (1 : ENNReal) < ENNReal.ofReal (Real.rpow x (1 - epsilon)) := by
        exact ENNReal.one_lt_ofReal.mpr h3
      simpa [Kakeya.realRpowENN] using h4
    have h4 : Kakeya.realRpowENN x (1 - epsilon) ≤
        (Metric.externalCoveringNumber (Real.toNNReal rho_B)
          (dotDiff ∩ Metric.closedBall center radius) : ENNReal) := by
      simpa [hx_def] using hcover_lower
    have h6 : (1 : ENNReal) <
        (Metric.externalCoveringNumber (Real.toNNReal rho_B)
          (dotDiff ∩ Metric.closedBall center radius) : ENNReal) :=
      h_lower_gt_one.trans_le h4
    have h7 : ¬ ((Metric.externalCoveringNumber (Real.toNNReal rho_B)
          (dotDiff ∩ Metric.closedBall center radius) : ENNReal) ≤ 1) := by
      intro h
      exact lt_irrefl (1 : ENNReal) (h6.trans_le h)
    exact h7 h_cover_upper'
  · -- radius > rho_B
    have hradius_gt_rhoB : rho_B < radius := by linarith
    by_cases hradius_one : radius ≤ 1
    · -- Case 2: rho_B < radius ≤ 1, direct AD bound
      have hcover_upper_raw :
          (Metric.externalCoveringNumber eps_nn
            (dotDiff ∩ Metric.closedBall center radius) : ENNReal) ≤
          C' * Kakeya.realRpowENN (radius / rho_B) (1 - sigma) := by
        have h := hcover rho_B hrhoB_nonneg hδ_AD_le_rhoB hrho_B_one center radius
          (by linarith) (by linarith)
        simpa [eps_nn] using h
      have hcover_upper :
          (Metric.externalCoveringNumber (Real.toNNReal rho_B)
            (dotDiff ∩ Metric.closedBall center radius) : ENNReal) ≤
          C' * Kakeya.realRpowENN (radius / rho_B) (1 - sigma) := by
        rw [← h_eps_eq]; exact hcover_upper_raw
      have h_radius_div : radius / rho_B = x / 2 := by
        rw [hx_def] <;> ring
      have h1 : Kakeya.realRpowENN x (1 - epsilon) ≤
          C' * Kakeya.realRpowENN (x / 2) (1 - sigma) := by
        calc
          Kakeya.realRpowENN x (1 - epsilon)
            = Kakeya.realRpowENN (2 * radius / rho_B) (1 - epsilon) := by rfl
          _ ≤ _ := hcover_lower
          _ ≤ C' * Kakeya.realRpowENN (radius / rho_B) (1 - sigma) := hcover_upper
          _ = C' * Kakeya.realRpowENN (x / 2) (1 - sigma) := by rw [h_radius_div]
      have h_x2_pos : 0 < x / 2 := by linarith
      have h1_real : Real.rpow x (1 - epsilon) ≤
          C_real * Real.rpow (x / 2) (1 - sigma) :=
        ennreal_mul_le_to_real hC_top hx_pos.le (by linarith) h1
      have h2 : Real.rpow x (1 - epsilon) =
          Real.rpow x (sigma - epsilon) * Real.rpow x (1 - sigma) := by
        have h_add : Real.rpow x (sigma - epsilon) * Real.rpow x (1 - sigma) =
            Real.rpow x ((sigma - epsilon) + (1 - sigma)) :=
          (Real.rpow_add hx_pos (sigma - epsilon) (1 - sigma)).symm
        have h_sum : (sigma - epsilon) + (1 - sigma) = 1 - epsilon := by ring
        rw [h_add, h_sum]
      have h3 : Real.rpow (x / 2) (1 - sigma) * Real.rpow 2 (1 - sigma) =
          Real.rpow x (1 - sigma) := by
        have h4 : 0 ≤ x / 2 := by linarith
        have h5 : 0 ≤ (2 : ℝ) := by norm_num
        have h6 : (x / 2 * (2 : ℝ)) ^ (1 - sigma) = (x / 2) ^ (1 - sigma) * (2 : ℝ) ^ (1 - sigma) :=
          Real.mul_rpow h4 h5
        have h7 : x / 2 * (2 : ℝ) = x := by ring
        rw [h7] at h6
        exact h6.symm
      have hpos_x2 : 0 < Real.rpow (x / 2) (1 - sigma) := Real.rpow_pos_of_pos h_x2_pos _
      have h_main_real : Real.rpow x (sigma - epsilon) * Real.rpow 2 (1 - sigma) ≤ C_real := by
        rw [h2] at h1_real
        set y := Real.rpow x (1 - sigma) with hy_def
        set z := Real.rpow (x / 2) (1 - sigma) with hz_def
        set w := Real.rpow 2 (1 - sigma) with hw_def
        have hz_pos : 0 < z := hpos_x2
        have h_eq : y = z * w := by
          simp only [hy_def, hz_def, hw_def]
          exact h3.symm
        have h_ineq : Real.rpow x (sigma - epsilon) * y ≤ C_real * z := h1_real
        rw [h_eq] at h_ineq
        have h : Real.rpow x (sigma - epsilon) * (z * w) ≤ C_real * z := h_ineq
        have h' : Real.rpow x (sigma - epsilon) * w ≤ C_real := by
          calc
            Real.rpow x (sigma - epsilon) * w
              = (Real.rpow x (sigma - epsilon) * (z * w)) / z := by
                field_simp [hz_pos.ne'] <;> ring
            _ ≤ (C_real * z) / z := by gcongr
            _ = C_real := by field_simp [hz_pos.ne'] <;> ring
        simpa [hw_def] using h'
      have h_main_real' : Real.rpow x (sigma - epsilon) * Real.rpow 2 (1 - sigma) ≤ (1 : ℝ) * C_real := by
        rw [one_mul]; exact h_main_real
      have hK_nonneg : (0 : ℝ) ≤ 1 := by norm_num
      have hK_le : (1 : ℝ) ≤ 100 := by norm_num
      exact real_contradiction (K := (1 : ℝ)) (C := C_real) hdeltaGraph_pos hdeltaGraph_one hsigma_one
        hepsilon_lt_sigma heta_pos hx_pos hx_lower hC_real_nonneg
        hK_nonneg hK_le h_main_real' h_absorb_real
    · -- Case 3: radius > 1, global 4-ball cover
      have hradius_gt_one : 1 < radius := by linarith
      let centers : Finset ℝ := {-3, -1, 1, 3}
      have h1 : dotDiff ⊆ ⋃ c ∈ centers, dotDiff ∩ Metric.closedBall c 1 := by
        intro y hy
        have h2 : y ∈ Set.Icc (-4 : ℝ) 4 := hE_bounded hy
        have h3 : y ∈ (⋃ c ∈ centers, Metric.closedBall c 1) :=
          icc_four_four_cover_by_four h2
        rcases Set.mem_iUnion₂.mp h3 with ⟨c, hc, h4⟩
        exact Set.mem_iUnion₂.mpr ⟨c, hc, ⟨hy, h4⟩⟩
      have h_each : ∀ c ∈ centers,
          (Metric.externalCoveringNumber eps_nn
            (dotDiff ∩ Metric.closedBall c 1) : ENNReal) ≤
          C' * Kakeya.realRpowENN (1 / rho_B) (1 - sigma) := by
        intro c _
        have h := hcover rho_B hrhoB_nonneg hδ_AD_le_rhoB hrho_B_one c 1
          (by linarith) (by norm_num)
        simpa [eps_nn] using h
      let B3_enr : ENNReal := (4 : ENNReal) * C' * Kakeya.realRpowENN (1 / rho_B) (1 - sigma)
      have hB3_top : B3_enr ≠ ⊤ := by
        dsimp only [B3_enr]
        have h1 : ((4 : ENNReal) * C') ≠ ⊤ := ENNReal.mul_ne_top (by simp) hC_top
        exact ENNReal.mul_ne_top h1 (by simp [Kakeya.realRpowENN])
      have h_mono_nat : Metric.externalCoveringNumber eps_nn dotDiff ≤
          Metric.externalCoveringNumber eps_nn (⋃ c ∈ centers, dotDiff ∩ Metric.closedBall c 1) :=
        Metric.externalCoveringNumber_mono_set h1
      have h_mono : (Metric.externalCoveringNumber eps_nn dotDiff : ENNReal) ≤
          (Metric.externalCoveringNumber eps_nn
            (⋃ c ∈ centers, dotDiff ∩ Metric.closedBall c 1) : ENNReal) :=
        ENat.toENNReal_le.mpr h_mono_nat
      have h4 := externalCoveringNumber_biUnion_le_card h_each
      have h_card : centers.card = 4 := by simp [centers] <;> norm_num
      have h_global : (Metric.externalCoveringNumber eps_nn dotDiff : ENNReal) ≤ B3_enr := by
        dsimp only [B3_enr]
        calc
          _ ≤ (Metric.externalCoveringNumber eps_nn
              (⋃ c ∈ centers, dotDiff ∩ Metric.closedBall c 1) : ENNReal) := h_mono
          _ ≤ (centers.card : ENNReal) * (C' * Kakeya.realRpowENN (1 / rho_B) (1 - sigma)) := h4
          _ = (4 : ENNReal) * (C' * Kakeya.realRpowENN (1 / rho_B) (1 - sigma)) := by
              rw [h_card] <;> norm_num
          _ = (4 : ENNReal) * C' * Kakeya.realRpowENN (1 / rho_B) (1 - sigma) := by ring
      have h_sub2 : dotDiff ∩ Metric.closedBall center radius ⊆ dotDiff := by
        exact Set.inter_subset_left
      have h_mono2_nat : Metric.externalCoveringNumber eps_nn
            (dotDiff ∩ Metric.closedBall center radius) ≤
          Metric.externalCoveringNumber eps_nn dotDiff :=
        Metric.externalCoveringNumber_mono_set h_sub2
      have h_mono2_nat' : Metric.externalCoveringNumber eps_nn
            (dotDiff ∩ Metric.closedBall center radius) ≤
          Metric.externalCoveringNumber eps_nn dotDiff :=
        Metric.externalCoveringNumber_mono_set h_sub2
      have h_mono2 : (Metric.externalCoveringNumber eps_nn
            (dotDiff ∩ Metric.closedBall center radius) : ENNReal) ≤
          (Metric.externalCoveringNumber eps_nn dotDiff : ENNReal) := by
        exact_mod_cast h_mono2_nat'
      have hcover_upper :
          (Metric.externalCoveringNumber (Real.toNNReal rho_B)
            (dotDiff ∩ Metric.closedBall center radius) : ENNReal) ≤ B3_enr := by
        rw [← h_eps_eq]
        exact h_mono2.trans h_global
      have h_inv_rho : Real.rpow (1 / rho_B) (1 - sigma) =
          Real.rpow rho_B (-(1 - sigma)) := by
        have h5 : (1 / rho_B) = rho_B⁻¹ := by ring
        rw [h5]
        have h6 : (rho_B⁻¹) ^ (1 - sigma) = (rho_B ^ (1 - sigma))⁻¹ :=
          Real.inv_rpow hrhoB_pos.le (1 - sigma)
        have h7 : Real.rpow rho_B (-(1 - sigma)) = (rho_B ^ (1 - sigma))⁻¹ :=
          Real.rpow_neg hrhoB_pos.le (1 - sigma)
        exact Eq.trans h6 h7.symm
      have h_inv_rho_enn : Kakeya.realRpowENN (1 / rho_B) (1 - sigma) =
          Kakeya.realRpowENN rho_B (-(1 - sigma)) := by
        simp only [Kakeya.realRpowENN]
        exact congr_arg ENNReal.ofReal h_inv_rho
      let B3'_enr : ENNReal := (4 : ENNReal) * C' * Kakeya.realRpowENN rho_B (-(1 - sigma))
      have hB3'_top : B3'_enr ≠ ⊤ := by
        dsimp only [B3'_enr]
        have h1 : ((4 : ENNReal) * C') ≠ ⊤ := ENNReal.mul_ne_top (by simp) hC_top
        exact ENNReal.mul_ne_top h1 (by simp [Kakeya.realRpowENN])
      have h1_enn : Kakeya.realRpowENN x (1 - epsilon) ≤ B3'_enr := by
        dsimp only [B3'_enr]
        calc
          Kakeya.realRpowENN (2 * radius / rho_B) (1 - epsilon)
            = Kakeya.realRpowENN x (1 - epsilon) := by rfl
          _ ≤ _ := hcover_lower
          _ ≤ B3_enr := hcover_upper
          _ = (4 : ENNReal) * C' * Kakeya.realRpowENN rho_B (-(1 - sigma)) := by
            dsimp only [B3_enr]
            rw [h_inv_rho_enn] <;> ring
      let D' : ENNReal := (4 : ENNReal) * C'
      have hD'_top : D' ≠ ⊤ := ENNReal.mul_ne_top (by simp) hC_top
      have h1_real : Real.rpow x (1 - epsilon) ≤
          D'.toReal * Real.rpow rho_B (-(1 - sigma)) :=
        ennreal_mul_le_to_real hD'_top hx_pos.le hrhoB_pos.le h1_enn
      have hD'_real : D'.toReal = 4 * C_real := by
        dsimp only [D']
        rw [ENNReal.toReal_mul, hC_real_def] <;> norm_num
      have h1_real' : Real.rpow x (1 - epsilon) ≤
          (4 : ℝ) * C_real * Real.rpow rho_B (-(1 - sigma)) := by
        rw [hD'_real] at h1_real
        exact h1_real
      have h_x_ge_two_rho : 2 / rho_B ≤ x := by
        rw [hx_def]
        have h : 2 ≤ 2 * radius := by linarith
        have hpos : 0 < rho_B := hrhoB_pos
        have h' : 2 / rho_B ≤ (2 * radius) / rho_B := by
          apply div_le_div_of_nonneg_right h hpos.le
        exact h'
      have h_x_rpow_ge : Real.rpow (2 / rho_B) (1 - sigma) ≤
          Real.rpow x (1 - sigma) := by
        have hpos : 0 ≤ 2 / rho_B := by positivity
        exact Real.rpow_le_rpow hpos h_x_ge_two_rho (by linarith)
      have h_mul2_rho : Real.rpow (2 / rho_B) (1 - sigma) =
          Real.rpow 2 (1 - sigma) * Real.rpow rho_B (-(1 - sigma)) := by
        have h4 : 0 ≤ (2 : ℝ) := by norm_num
        have h5 : (2 / rho_B) = (2 : ℝ) * rho_B⁻¹ := by ring
        rw [h5]
        have hrhoB_inv_nonneg : 0 ≤ rho_B⁻¹ := by positivity
        have h6 : Real.rpow ((2 : ℝ) * rho_B⁻¹) (1 - sigma) =
            Real.rpow 2 (1 - sigma) * Real.rpow rho_B⁻¹ (1 - sigma) := by
          have h_raw : ((2 : ℝ) * rho_B⁻¹) ^ (1 - sigma) =
              (2 : ℝ) ^ (1 - sigma) * (rho_B⁻¹) ^ (1 - sigma) :=
            Real.mul_rpow h4 hrhoB_inv_nonneg
          exact h_raw
        have h71 : (rho_B⁻¹) ^ (1 - sigma) = (rho_B ^ (1 - sigma))⁻¹ :=
          Real.inv_rpow hrhoB_pos.le (1 - sigma)
        have h72 : Real.rpow rho_B (-(1 - sigma)) = (rho_B ^ (1 - sigma))⁻¹ :=
          Real.rpow_neg hrhoB_pos.le (1 - sigma)
        have h7 : Real.rpow rho_B⁻¹ (1 - sigma) = Real.rpow rho_B (-(1 - sigma)) := by
          have h73 : Real.rpow rho_B⁻¹ (1 - sigma) = (rho_B ^ (1 - sigma))⁻¹ := by
            exact h71
          exact h73.trans h72.symm
        have h_goal : Real.rpow 2 (1 - sigma) * Real.rpow rho_B⁻¹ (1 - sigma) =
            Real.rpow 2 (1 - sigma) * Real.rpow rho_B (-(1 - sigma)) := by
          exact congr_arg (fun t : ℝ => Real.rpow 2 (1 - sigma) * t) h7
        rw [h6]
        exact h_goal
      have h_rhoB_inv_pos : 0 < Real.rpow rho_B (-(1 - sigma)) :=
        Real.rpow_pos_of_pos hrhoB_pos _
      have h2 : Real.rpow x (1 - epsilon) =
          Real.rpow x (sigma - epsilon) * Real.rpow x (1 - sigma) := by
        have h_add : Real.rpow x (sigma - epsilon) * Real.rpow x (1 - sigma) =
            Real.rpow x ((sigma - epsilon) + (1 - sigma)) :=
          (Real.rpow_add hx_pos (sigma - epsilon) (1 - sigma)).symm
        have h_sum : (sigma - epsilon) + (1 - sigma) = 1 - epsilon := by ring
        rw [h_add, h_sum]
      have h_main_real : Real.rpow x (sigma - epsilon) * Real.rpow 2 (1 - sigma) ≤
          (4 : ℝ) * C_real := by
        rw [h2] at h1_real
        set y := Real.rpow x (1 - sigma) with hy_def
        set z := Real.rpow rho_B (-(1 - sigma)) with hz_def
        set w := Real.rpow 2 (1 - sigma) with hw_def
        have hz_pos : 0 < z := h_rhoB_inv_pos
        have h_eq1 : w * z ≤ y := by
          simp only [hy_def, hz_def, hw_def]
          rw [← h_mul2_rho]
          exact h_x_rpow_ge
        have h_ineq : Real.rpow x (sigma - epsilon) * y ≤ (4 : ℝ) * C_real * z := by
          rw [h2] at h1_real'
          exact h1_real'
        have h5 : Real.rpow x (sigma - epsilon) * (w * z) ≤
            Real.rpow x (sigma - epsilon) * y := by
          exact mul_le_mul_of_nonneg_left h_eq1 (Real.rpow_nonneg hx_pos.le _)
        have h6 : Real.rpow x (sigma - epsilon) * w * z ≤
            (4 : ℝ) * C_real * z := by
          calc
            Real.rpow x (sigma - epsilon) * w * z
              = Real.rpow x (sigma - epsilon) * (w * z) := by ring
            _ ≤ Real.rpow x (sigma - epsilon) * y := h5
            _ ≤ (4 : ℝ) * C_real * z := h_ineq
        have h7 : Real.rpow x (sigma - epsilon) * w ≤ (4 : ℝ) * C_real := by
          calc
            Real.rpow x (sigma - epsilon) * w
              = (Real.rpow x (sigma - epsilon) * w * z) / z := by field_simp [hz_pos.ne'] <;> ring
            _ ≤ ((4 : ℝ) * C_real * z) / z := by gcongr
            _ = (4 : ℝ) * C_real := by field_simp [hz_pos.ne'] <;> ring
        simpa [hw_def] using h7
      have hK_nonneg2 : (0 : ℝ) ≤ 4 := by norm_num
      have hK_le2 : (4 : ℝ) ≤ 100 := by norm_num
      exact real_contradiction (K := (4 : ℝ)) hdeltaGraph_pos hdeltaGraph_one hsigma_one
        hepsilon_lt_sigma heta_pos hx_pos hx_lower hC_real_nonneg
        hK_nonneg2 hK_le2 h_main_real h_absorb_real

end Kakeya.Assouad
