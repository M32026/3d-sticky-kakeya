import MyLeanRepo.Kakeya.Cinematic.Section5.LevelSetInputs

/-!
# Fine rectangles lie in centered coarse rectangles
-/

namespace Kakeya.Cinematic

theorem fine_to_coarse_containment :
    FineToCoarseContainmentStatement := by
  unfold FineToCoarseContainmentStatement
  intro K delta t Delta C_R hK hdelta hdelta_Delta hDelta_t ht_pos hC_R_pos
    hC_R_large I hI R hR_over
  have hK_pos : 0 < K := by linarith
  have hDelta_pos : 0 < Delta := by linarith
  have hCRt_pos : 0 < C_R * t := mul_pos hC_R_pos ht_pos
  set fine_len : ℝ := R.interval.length with hfine_def
  set coarse_len : ℝ := Real.sqrt (Delta / (C_R * t)) with hcoarse_def
  have hcoarse_nonneg : 0 ≤ coarse_len := Real.sqrt_nonneg _
  have hcoarse_pos : 0 < coarse_len := Real.sqrt_pos.mpr (by positivity)
  have h_prod_pos : 0 < C_R * t * Delta := by positivity
  have h_fine_len_simp : fine_len = delta / Real.sqrt (C_R * t * Delta) := by
    have h1 : fine_len = Real.sqrt (delta / (C_R * t * Delta / delta)) :=
      R.interval_length
    rw [h1]
    have h2 : delta / (C_R * t * Delta / delta) =
        delta ^ 2 / (C_R * t * Delta) := by
      field_simp [hdelta.ne'] <;> ring
    rw [h2]
    have h3 : Real.sqrt (delta ^ 2 / (C_R * t * Delta)) =
        delta / Real.sqrt (C_R * t * Delta) := by
      rw [Real.sqrt_div (by positivity)]
      have h4 : Real.sqrt (delta ^ 2) = delta := by
        rw [Real.sqrt_sq_eq_abs, abs_of_pos hdelta]
      rw [h4]
    exact h3
  have h_sq1 : (delta / Real.sqrt (C_R * t * Delta)) ^ 2 =
      delta ^ 2 / (C_R * t * Delta) := by
    have hsqrt_sq : (Real.sqrt (C_R * t * Delta)) ^ 2 = C_R * t * Delta :=
      Real.sq_sqrt (by positivity)
    have h : (delta / Real.sqrt (C_R * t * Delta)) ^ 2 =
        delta ^ 2 / (Real.sqrt (C_R * t * Delta)) ^ 2 := by
      field_simp <;> ring
    rw [h, hsqrt_sq]
  have h_sq2 : coarse_len ^ 2 = Delta / (C_R * t) := by
    rw [hcoarse_def, Real.sq_sqrt (by positivity)]
  have h_fine_le_coarse : fine_len ≤ coarse_len := by
    rw [h_fine_len_simp]
    have h_nonneg1 : 0 ≤ delta / Real.sqrt (C_R * t * Delta) := by positivity
    have h_nonneg2 : 0 ≤ coarse_len := hcoarse_nonneg
    have h : (delta / Real.sqrt (C_R * t * Delta)) ^ 2 ≤ coarse_len ^ 2 := by
      rw [h_sq1, h_sq2]
      have h6 : delta ^ 2 ≤ Delta ^ 2 := by nlinarith
      have h7 : 0 < C_R * t := hCRt_pos
      calc
        delta ^ 2 / (C_R * t * Delta) ≤ Delta ^ 2 / (C_R * t * Delta) := by
          gcongr
        _ = Delta / (C_R * t) := by
          field_simp [h7.ne', hDelta_pos.ne'] <;> ring
    nlinarith
  set mid : ℝ := R.interval.midpoint with hmid_def
  have h_mid_bounds : R.interval.left ≤ mid ∧ mid ≤ R.interval.right := by
    have h1 : mid = (R.interval.left + R.interval.right) / 2 := by
      simp [hmid_def, ParameterInterval.midpoint] <;> ring
    rw [h1]
    constructor <;> linarith [R.interval.left_le_right]
  have h_mid_in_01 : 0 ≤ mid ∧ mid ≤ 1 := by
    have h1 : 0 ≤ R.interval.left := R.interval.left_mem.1
    have h2 : R.interval.right ≤ 1 := R.interval.right_mem.2
    exact ⟨by linarith, by linarith⟩
  let mid' : UnitPoint := ⟨mid, h_mid_in_01⟩
  have h_mid'_in_carrier : mid' ∈ R.interval.carrier := by
    simp only [ParameterInterval.carrier, Set.mem_setOf_eq]
    exact h_mid_bounds
  have h_mid_centered : |mid - I.midpoint| ≤ I.length / 8 := by
    have h_raw : |(mid' : ℝ) - I.midpoint| ≤ (1 / 4 : ℝ) * I.length / 2 :=
      hR_over h_mid'_in_carrier
    have h_coerce : (mid' : ℝ) = mid := by simp [mid']
    rw [h_coerce] at h_raw
    have h_eq : (1 / 4 : ℝ) * I.length / 2 = I.length / 8 := by ring
    rw [h_eq] at h_raw
    exact h_raw
  have hI_len_lower : I.length ≥ 1 / (12 * K) := by
    have h := hI.1
    have h2 : (12 * K)⁻¹ = 1 / (12 * K) := by
      field_simp [hK_pos.ne'] <;> ring
    rw [h2] at h
    exact h
  have h_mid_lower : mid ≥ 1 / (32 * K) := by
    have h1 : mid ≥ I.midpoint - I.length / 8 := by
      have h2 : -(I.length / 8) ≤ mid - I.midpoint := (abs_le.mp h_mid_centered).1
      linarith
    have h3 : I.midpoint = I.left + I.length / 2 := by
      simp [ParameterInterval.midpoint, ParameterInterval.length] <;> ring
    have h4 : mid ≥ I.left + 3 * I.length / 8 := by
      linarith [h1, h3]
    have h5 : 0 ≤ I.left := I.left_mem.1
    have h6 : I.length ≥ 1 / (12 * K) := hI_len_lower
    have h7 : I.left + 3 * I.length / 8 ≥ 3 * (1 / (12 * K)) / 8 := by
      have h71 : 3 * I.length / 8 ≥ 3 * (1 / (12 * K)) / 8 := by gcongr
      linarith [h5]
    have h8 : 3 * (1 / (12 * K)) / 8 = 1 / (32 * K) := by
      field_simp [hK_pos.ne'] <;> ring
    linarith
  have h_mid_upper : mid ≤ 1 - 1 / (32 * K) := by
    have h1 : mid ≤ I.midpoint + I.length / 8 := by
      have h2 : mid - I.midpoint ≤ I.length / 8 := (abs_le.mp h_mid_centered).2
      linarith
    have h3 : I.midpoint = I.right - I.length / 2 := by
      simp [ParameterInterval.midpoint, ParameterInterval.length] <;> ring
    have h4 : mid ≤ I.right - 3 * I.length / 8 := by
      linarith [h1, h3]
    have h5 : I.right ≤ 1 := I.right_mem.2
    have h6 : I.length ≥ 1 / (12 * K) := hI_len_lower
    have h7 : I.right - 3 * I.length / 8 ≤ 1 - 3 * (1 / (12 * K)) / 8 := by
      have h71 : 3 * I.length / 8 ≥ 3 * (1 / (12 * K)) / 8 := by gcongr
      linarith [h5]
    have h8 : 1 - 3 * (1 / (12 * K)) / 8 = 1 - 1 / (32 * K) := by
      field_simp [hK_pos.ne'] <;> ring
    linarith
  set half : ℝ := coarse_len / 2 with hhalf_def
  have h_half_le : half ≤ 1 / (32 * K) := by
    have h1 : coarse_len ≤ Real.sqrt (1 / C_R) := by
      rw [hcoarse_def]
      have h2 : Delta / (C_R * t) ≤ 1 / C_R := by
        have h3 : Delta ≤ t := hDelta_t
        have h4 : Delta / (C_R * t) ≤ t / (C_R * t) := by gcongr
        have h5 : t / (C_R * t) = 1 / C_R := by
          field_simp [hC_R_pos.ne', ht_pos.ne'] <;> ring
        rw [h5] at h4
        exact h4
      exact Real.sqrt_le_sqrt h2
    have h4 : Real.sqrt (1 / C_R) = 1 / Real.sqrt C_R := by
      rw [Real.sqrt_div (by positivity)]
      <;> simp
    have h5 : Real.sqrt C_R ≥ 16 * K := by
      have h6 : (16 * K) ^ 2 ≤ C_R := by
        have h7 : (16 * K) ^ 2 = 256 * K ^ 2 := by ring
        rw [h7]
        exact hC_R_large
      have h8 : 0 ≤ 16 * K := by positivity
      exact Real.le_sqrt_of_sq_le h6
    have h9 : 0 < Real.sqrt C_R := by positivity
    calc
      half = coarse_len / 2 := rfl
      _ ≤ Real.sqrt (1 / C_R) / 2 := by
        exact div_le_div_of_nonneg_right h1 (by norm_num)
      _ = (1 / Real.sqrt C_R) / 2 := by rw [h4]
      _ = 1 / (2 * Real.sqrt C_R) := by ring
      _ ≤ 1 / (32 * K) := by
        apply one_div_le_one_div_of_le <;> linarith
  have h_left_nonneg : 0 ≤ mid - half := by
    have h10 : mid ≥ 1 / (32 * K) := h_mid_lower
    have h11 : half ≤ 1 / (32 * K) := h_half_le
    linarith
  have h_right_le_one : mid + half ≤ 1 := by
    have h10 : mid ≤ 1 - 1 / (32 * K) := h_mid_upper
    have h11 : half ≤ 1 / (32 * K) := h_half_le
    linarith
  let S_interval : ParameterInterval :=
    { left := mid - half
      right := mid + half
      left_mem := by
        exact ⟨h_left_nonneg, by linarith [h_right_le_one]⟩
      right_mem := by
        exact ⟨by linarith [h_left_nonneg], h_right_le_one⟩
      left_le_right := by
        simp [hhalf_def] <;> linarith [hcoarse_nonneg] }
  have h_S_len : S_interval.length = coarse_len := by
    simp [S_interval, ParameterInterval.length, hhalf_def] <;> ring
  have h_S_midpoint : S_interval.midpoint = mid := by
    simp [S_interval, ParameterInterval.midpoint] <;> ring
  let S : CurvilinearRectangle Delta (C_R * t) :=
    { function := R.function
      interval := S_interval
      interval_length := by
        rw [h_S_len, hcoarse_def] }
  have h_interval_contain : R.interval.carrier ⊆ S_interval.carrier := by
    intro x hx
    have h2 : R.interval.left ≤ (x : ℝ) := hx.1
    have h3 : (x : ℝ) ≤ R.interval.right := hx.2
    have h4 : |(x : ℝ) - mid| ≤ fine_len / 2 := by
      have h5 : (x : ℝ) - mid ≤ fine_len / 2 := by
        simp [hmid_def, ParameterInterval.midpoint, ParameterInterval.length] at *
        linarith
      have h6 : mid - (x : ℝ) ≤ fine_len / 2 := by
        simp [hmid_def, ParameterInterval.midpoint, ParameterInterval.length] at *
        linarith
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have h7 : |(x : ℝ) - mid| ≤ coarse_len / 2 := by
      calc
        |(x : ℝ) - mid| ≤ fine_len / 2 := h4
        _ ≤ coarse_len / 2 := by gcongr
    have h8 : mid - half ≤ (x : ℝ) := by
      have h9 : -(coarse_len / 2) ≤ (x : ℝ) - mid := (abs_le.mp h7).1
      simpa [hhalf_def] using h9
    have h10 : (x : ℝ) ≤ mid + half := by
      have h11 : (x : ℝ) - mid ≤ coarse_len / 2 := (abs_le.mp h7).2
      have h12 : (x : ℝ) ≤ mid + coarse_len / 2 := by linarith
      have h13 : mid + coarse_len / 2 = mid + half := by
        simp [hhalf_def] <;> ring
      rw [h13] at h12
      exact h12
    exact ⟨h8, h10⟩
  have h_carrier_contain : R.carrier ⊆ S.carrier := by
    intro p hp
    have h1 : p.1 ∈ R.interval.carrier := hp.1
    have h2 : p.1 ∈ S_interval.carrier := h_interval_contain h1
    have h3 : |p.2 - R.function p.1| ≤ delta := hp.2
    have h4 : |p.2 - R.function p.1| ≤ Delta := by
      calc
        |p.2 - R.function p.1| ≤ delta := h3
        _ ≤ Delta := hdelta_Delta
    exact ⟨h2, h4⟩
  refine ⟨S, rfl, ?_, h_carrier_contain⟩
  simp [S, h_S_midpoint]

end Kakeya.Cinematic
