import MyLeanRepo.Kakeya.Cinematic.Section5.CenteredRectangleEnlargementInputs

/-!
# Centered enlargement of a fine rectangle
-/

namespace Kakeya.Cinematic

theorem centered_rectangle_enlargement :
    CenteredRectangleEnlargementStatement := by
  intro family I delta t lambda hdelta ht hlambda R hf hcentral hbuffer
  let m : ℝ := R.interval.midpoint
  let L : ℝ := Real.sqrt (lambda * delta / t)
  have hL_nonneg : 0 ≤ L := Real.sqrt_nonneg _
  have hm0 : 0 ≤ m := by
    dsimp only [m, ParameterInterval.midpoint]
    linarith [R.interval.left_mem.1, R.interval.left_le_right]
  have hm1 : m ≤ 1 := by
    dsimp only [m, ParameterInterval.midpoint]
    linarith [R.interval.right_mem.2, R.interval.left_le_right]
  let midpoint : UnitPoint := ⟨m, hm0, hm1⟩
  have hmidpoint_mem : midpoint ∈ R.interval.carrier := by
    change R.interval.left ≤ m ∧ m ≤ R.interval.right
    dsimp only [m, ParameterInterval.midpoint]
    constructor <;> linarith [R.interval.left_le_right]
  have hm_central :
      |m - I.midpoint| ≤ I.length / 8 := by
    have h := hcentral hmidpoint_mem
    change |m - I.midpoint| ≤ (1 / 4 : ℝ) * I.length / 2 at h
    convert h using 1 <;> ring
  have hI_mid_lower : I.length / 2 ≤ I.midpoint := by
    dsimp only [ParameterInterval.length, ParameterInterval.midpoint]
    linarith [I.left_mem.1]
  have hI_mid_upper : I.midpoint ≤ 1 - I.length / 2 := by
    dsimp only [ParameterInterval.length, ParameterInterval.midpoint]
    linarith [I.right_mem.2]
  have hleft0 : 0 ≤ m - L / 2 := by
    have hm_lower := (abs_le.mp hm_central).1
    have hL : L ≤ I.length / 8 := hbuffer
    linarith [I.length_nonneg]
  have hleft1 : m - L / 2 ≤ 1 := by
    linarith
  have hright0 : 0 ≤ m + L / 2 := by
    linarith
  have hright1 : m + L / 2 ≤ 1 := by
    have hm_upper := (abs_le.mp hm_central).2
    have hL : L ≤ I.length / 8 := hbuffer
    linarith [I.length_nonneg]
  have hleft_right : m - L / 2 ≤ m + L / 2 := by
    linarith
  let J : ParameterInterval :=
    { left := m - L / 2
      right := m + L / 2
      left_mem := ⟨hleft0, hleft1⟩
      right_mem := ⟨hright0, hright1⟩
      left_le_right := hleft_right }
  have hJ_length : J.length = L := by
    simp [J, ParameterInterval.length]
  let U : CurvilinearRectangle (lambda * delta) t :=
    { function := R.function
      interval := J
      interval_length := by
        exact hJ_length }
  have hU_function : U.function = R.function := rfl
  have hU_midpoint :
      U.interval.midpoint = R.interval.midpoint := by
    simp [U, J, m, ParameterInterval.midpoint]
  have hR_length_le : R.interval.length ≤ L := by
    rw [R.interval_length]
    apply Real.sqrt_le_sqrt
    apply (div_le_div_iff_of_pos_right ht).2
    nlinarith
  have hR_left :
      R.interval.left = m - R.interval.length / 2 := by
    simp [m, ParameterInterval.midpoint, ParameterInterval.length]
    ring
  have hR_right :
      R.interval.right = m + R.interval.length / 2 := by
    simp [m, ParameterInterval.midpoint, ParameterInterval.length]
    ring
  have hinterval : R.interval.carrier ⊆ U.interval.carrier := by
    intro x hx
    have hx_left : R.interval.left ≤ (x : ℝ) := hx.1
    have hx_right : (x : ℝ) ≤ R.interval.right := hx.2
    rw [hR_left] at hx_left
    rw [hR_right] at hx_right
    change m - L / 2 ≤ (x : ℝ) ∧ (x : ℝ) ≤ m + L / 2
    constructor <;> linarith
  have hcarrier : R.carrier ⊆ U.carrier := by
    intro p hp
    refine ⟨hinterval hp.1, ?_⟩
    rw [hU_function]
    exact hp.2.trans (by nlinarith)
  exact ⟨U, hU_function, hU_midpoint, hcarrier, by simpa [hU_function]⟩

end Kakeya.Cinematic
