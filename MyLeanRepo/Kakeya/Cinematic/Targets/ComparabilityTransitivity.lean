import MyLeanRepo.Kakeya.Cinematic.Statements

/-!
# PYZ Corollary 21: comparability transitivity

The output constant is uniform in the rectangles and may depend only on the
cinematic constants and the two input comparability constants.
-/

namespace Kakeya.Cinematic

theorem comparability_transitivity
    (hComparable : ComparableRectanglesStatement) :
    ComparabilityTransitivityStatement := by
  intro K D hK hD lambda₁ lambda₂ hlambda₁ hlambda₂
  rcases hComparable K D hK hD with ⟨C, hC_pos, hComparable_prop⟩
  let B1 := (Real.sqrt lambda₁ + Real.sqrt lambda₂)^2
  let B2 := max (1 + C * lambda₁^3) (max (1 + C * lambda₂^3) (1 : ℝ))
  set lambda₃ : ℝ := max B1 B2 with hlambda₃_def
  have hlambda₃_one : 1 ≤ lambda₃ := by
    rw [hlambda₃_def]
    have h1 : (1 : ℝ) ≤ B2 := by
      simp [B2] <;> norm_num
    exact le_trans h1 (le_max_right B1 B2)
  refine' ⟨lambda₃, hlambda₃_one, _⟩
  intro family hFamily I hI delta t hdelta hdt hadmissible
  have hadm2 : lambda₃ * delta ≤ t := hadmissible.2
  have h_tpos : 0 < t := by linarith
  intro R₁ R₂ R₃ hR1fam hR2fam hR3fam hR1quarter hR2quarter hR3quarter hComp12 hComp23
  have h12 := hComparable_prop family hFamily I hI delta t lambda₁ hdelta hdt hlambda₁
                R₁ R₂ hR1fam hR2fam hR1quarter hR2quarter hComp12
  have h23 := hComparable_prop family hFamily I hI delta t lambda₂ hdelta hdt hlambda₂
                R₂ R₃ hR2fam hR3fam hR2quarter hR3quarter hComp23
  let a₁ := R₁.interval.left
  let b₁ := R₁.interval.right
  let a₂ := R₂.interval.left
  let b₂ := R₂.interval.right
  let a₃ := R₃.interval.left
  let b₃ := R₃.interval.right
  have h23_ab : a₂ ≤ b₂ := R₂.interval.left_le_right
  have hH12 : max b₁ b₂ - min a₁ a₂ ≤ Real.sqrt (lambda₁ * delta / t) := h12.1
  have hH23 : max b₂ b₃ - min a₂ a₃ ≤ Real.sqrt (lambda₂ * delta / t) := h23.1
  have hf12 : ∀ x ∈ R₁.intervalHullCarrier R₂,
      |R₁.function x - R₂.function x| ≤ C * Real.rpow lambda₁ 3 * delta := h12.2
  have hf23 : ∀ x ∈ R₂.intervalHullCarrier R₃,
      |R₂.function x - R₃.function x| ≤ C * Real.rpow lambda₂ 3 * delta := h23.2
  have hrpow1 : Real.rpow lambda₁ 3 = lambda₁^3 := by simp [Real.rpow_natCast]
  have hrpow2 : Real.rpow lambda₂ 3 = lambda₂^3 := by simp [Real.rpow_natCast]
  have h_max_b : max b₁ b₃ ≤ max b₁ b₂ + max b₂ b₃ - b₂ := by
    by_cases h : b₁ ≤ b₃
    · have h5 : max b₁ b₃ = b₃ := by rw [max_eq_right h]
      rw [h5]
      have h6 : max b₁ b₂ ≥ b₂ := le_max_right b₁ b₂
      have h7 : max b₂ b₃ ≥ b₃ := le_max_right b₂ b₃
      linarith
    · have h' : b₃ ≤ b₁ := by linarith
      have h5 : max b₁ b₃ = b₁ := by rw [max_eq_left h']
      rw [h5]
      have h6 : max b₁ b₂ ≥ b₁ := le_max_left b₁ b₂
      have h7 : max b₂ b₃ ≥ b₂ := le_max_left b₂ b₃
      linarith
  have h_min_a : min a₁ a₃ ≥ min a₁ a₂ + min a₂ a₃ - a₂ := by
    by_cases h : a₁ ≤ a₃
    · have h5 : min a₁ a₃ = a₁ := by rw [min_eq_left h]
      rw [h5]
      have h6 : min a₁ a₂ ≤ a₁ := min_le_left a₁ a₂
      have h7 : min a₂ a₃ ≤ a₂ := min_le_left a₂ a₃
      linarith
    · have h' : a₃ ≤ a₁ := by linarith
      have h5 : min a₁ a₃ = a₃ := by rw [min_eq_right h']
      rw [h5]
      have h6 : min a₁ a₂ ≤ a₂ := min_le_right a₁ a₂
      have h7 : min a₂ a₃ ≤ a₃ := min_le_right a₂ a₃
      linarith
  have hH13_le : max b₁ b₃ - min a₁ a₃ ≤
      (max b₁ b₂ - min a₁ a₂) + (max b₂ b₃ - min a₂ a₃) := by
    linarith [h_max_b, h_min_a, h23_ab]
  have hsqrt_lambda3 : Real.sqrt lambda₃ ≥ Real.sqrt lambda₁ + Real.sqrt lambda₂ := by
    have h1 : (Real.sqrt lambda₁ + Real.sqrt lambda₂)^2 ≤ lambda₃ := by
      rw [hlambda₃_def]; exact le_max_left B1 B2
    have h2 : 0 ≤ Real.sqrt lambda₁ + Real.sqrt lambda₂ := by positivity
    have h3 : Real.sqrt ((Real.sqrt lambda₁ + Real.sqrt lambda₂)^2) =
        Real.sqrt lambda₁ + Real.sqrt lambda₂ := by
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg h2]
    have h4 : Real.sqrt lambda₃ ≥ Real.sqrt ((Real.sqrt lambda₁ + Real.sqrt lambda₂)^2) :=
      Real.sqrt_le_sqrt h1
    rw [h3] at h4; exact h4
  have h_sqrt_eq : ∀ (l : ℝ), 0 ≤ l →
      Real.sqrt (l * delta / t) = Real.sqrt l * Real.sqrt (delta / t) := by
    intro l hl
    have h : l * delta / t = l * (delta / t) := by ring
    rw [h, Real.sqrt_mul hl]
  have hsqrt_sum : Real.sqrt (lambda₁ * delta / t) + Real.sqrt (lambda₂ * delta / t) ≤
      Real.sqrt (lambda₃ * delta / t) := by
    rw [h_sqrt_eq lambda₁ (by linarith), h_sqrt_eq lambda₂ (by linarith),
        h_sqrt_eq lambda₃ (by linarith)]
    have h : (Real.sqrt lambda₁ + Real.sqrt lambda₂) * Real.sqrt (delta / t) ≤
        Real.sqrt lambda₃ * Real.sqrt (delta / t) :=
      mul_le_mul_of_nonneg_right hsqrt_lambda3 (by positivity)
    have h5 : Real.sqrt lambda₁ * Real.sqrt (delta / t) +
              Real.sqrt lambda₂ * Real.sqrt (delta / t) =
            (Real.sqrt lambda₁ + Real.sqrt lambda₂) * Real.sqrt (delta / t) := by ring
    rw [h5]; exact h
  let L := Real.sqrt (lambda₃ * delta / t)
  have hL_nonneg : 0 ≤ L := Real.sqrt_nonneg _
  have hL_le_one : L ≤ 1 := by
    have h : lambda₃ * delta / t ≤ 1 := by
      rw [div_le_one h_tpos] <;> linarith
    have h5 : L ≤ Real.sqrt 1 := Real.sqrt_le_sqrt h
    rw [Real.sqrt_one] at h5; exact h5
  let a := min a₁ a₃
  let b := max b₁ b₃
  have ha1_nonneg : 0 ≤ a₁ := R₁.interval.left_mem.1
  have ha3_nonneg : 0 ≤ a₃ := R₃.interval.left_mem.1
  have ha_nonneg : 0 ≤ a := le_min ha1_nonneg ha3_nonneg
  have hb1_le_one : b₁ ≤ 1 := R₁.interval.right_mem.2
  have hb3_le_one : b₃ ≤ 1 := R₃.interval.right_mem.2
  have hb_le_one : b ≤ 1 := max_le hb1_le_one hb3_le_one
  have hba_le_L : b - a ≤ L := by
    calc
      b - a = max b₁ b₃ - min a₁ a₃ := by rfl
      _ ≤ (max b₁ b₂ - min a₁ a₂) + (max b₂ b₃ - min a₂ a₃) := hH13_le
      _ ≤ Real.sqrt (lambda₁ * delta / t) + Real.sqrt (lambda₂ * delta / t) := by linarith
      _ ≤ L := hsqrt_sum
  let c := max 0 (b - L)
  have hc_nonneg : 0 ≤ c := le_max_left 0 (b - L)
  have h_bminusL_le_a : b - L ≤ a := by linarith [hba_le_L]
  have hc_le_a : c ≤ a := max_le ha_nonneg h_bminusL_le_a
  have hcL_eq : c + L = max L b := by
    have h : max 0 (b - L) + L = max (0 + L) (b - L + L) := by
      rw [max_add_add_right]
    rw [h]
    have h2 : 0 + L = L := by ring
    have h3 : b - L + L = b := by ring
    rw [h2, h3]
  have hb_le_cL : b ≤ c + L := by
    rw [hcL_eq]; exact le_max_right L b
  have hcL_le_one : c + L ≤ 1 := by
    rw [hcL_eq]; exact max_le hL_le_one hb_le_one
  have hc_le_one : c ≤ 1 := by linarith
  let J : ParameterInterval :=
    { left := c
      right := c + L
      left_mem := ⟨hc_nonneg, hc_le_one⟩
      right_mem := ⟨by linarith, hcL_le_one⟩
      left_le_right := by linarith [hL_nonneg] }
  have hJ_length : J.length = L := by
    simp [J, ParameterInterval.length] <;> ring
  let U₁₃ : CurvilinearRectangle (lambda₃ * delta) t :=
    { function := R₂.function
      interval := J
      interval_length := by rw [hJ_length] <;> rfl }
  have hU13_fam : U₁₃.function ∈ family := hR2fam
  have hR1_in_hull12 : R₁.interval.carrier ⊆ R₁.intervalHullCarrier R₂ := by
    intro x hx
    have h1 : a₁ ≤ (x : ℝ) := hx.1
    have h2 : (x : ℝ) ≤ b₁ := hx.2
    have h3 : min a₁ a₂ ≤ (x : ℝ) := le_trans (min_le_left a₁ a₂) h1
    have h4 : (x : ℝ) ≤ max b₁ b₂ := le_trans h2 (le_max_left b₁ b₂)
    have h_goal : min a₁ a₂ ≤ (x : ℝ) ∧ (x : ℝ) ≤ max b₁ b₂ := ⟨h3, h4⟩
    have h_final : x ∈ R₁.intervalHullCarrier R₂ := by
      rw [CurvilinearRectangle.intervalHullCarrier]
      simpa [Set.mem_setOf_eq] using h_goal
    exact h_final
  have hR3_in_hull23 : R₃.interval.carrier ⊆ R₂.intervalHullCarrier R₃ := by
    intro x hx
    have h1 : a₃ ≤ (x : ℝ) := hx.1
    have h2 : (x : ℝ) ≤ b₃ := hx.2
    have h3 : min a₂ a₃ ≤ (x : ℝ) := le_trans (min_le_right a₂ a₃) h1
    have h4 : (x : ℝ) ≤ max b₂ b₃ := le_trans h2 (le_max_right b₂ b₃)
    have h_goal : min a₂ a₃ ≤ (x : ℝ) ∧ (x : ℝ) ≤ max b₂ b₃ := ⟨h3, h4⟩
    have h_final : x ∈ R₂.intervalHullCarrier R₃ := by
      rw [CurvilinearRectangle.intervalHullCarrier]
      simpa [Set.mem_setOf_eq] using h_goal
    exact h_final
  have hlambda₃_ge1 : lambda₃ ≥ 1 + C * lambda₁^3 := by
    rw [hlambda₃_def]
    have h : 1 + C * lambda₁^3 ≤ B2 := by
      simp [B2] <;> norm_num
    exact le_trans h (le_max_right B1 B2)
  have hlambda₃_ge2 : lambda₃ ≥ 1 + C * lambda₂^3 := by
    rw [hlambda₃_def]
    have h : 1 + C * lambda₂^3 ≤ B2 := by
      simp [B2] <;> norm_num
    exact le_trans h (le_max_right B1 B2)
  have hR1_sub : R₁.carrier ⊆ U₁₃.carrier := by
    intro p hp
    have hpin1 : p.1 ∈ R₁.interval.carrier := by
      simpa [CurvilinearRectangle.carrier, verticalNeighborhoodOn] using hp |>.1
    have hpin2 : |p.2 - R₁.function p.1| ≤ delta := by
      simpa [CurvilinearRectangle.carrier, verticalNeighborhoodOn] using hp |>.2
    have hpinJ : p.1 ∈ J.carrier := by
      have h1 : a₁ ≤ (p.1 : ℝ) := hpin1.1
      have h2 : (p.1 : ℝ) ≤ b₁ := hpin1.2
      have h3 : c ≤ (p.1 : ℝ) := by
        have h4 : a ≤ a₁ := min_le_left a₁ a₃
        linarith [hc_le_a]
      have h4 : (p.1 : ℝ) ≤ c + L := by
        have h5 : b₁ ≤ b := le_max_left b₁ b₃
        linarith [hb_le_cL]
      exact ⟨h3, h4⟩
    have h5 : p.1 ∈ R₁.intervalHullCarrier R₂ := hR1_in_hull12 hpin1
    have h6 : |R₁.function p.1 - R₂.function p.1| ≤ C * lambda₁^3 * delta := by
      rw [hrpow1] at hf12
      exact hf12 p.1 h5
    have h71 : |p.2 - R₂.function p.1| ≤
        |p.2 - R₁.function p.1| + |R₁.function p.1 - R₂.function p.1| := by
      have h8 : p.2 - R₂.function p.1 =
          (p.2 - R₁.function p.1) + (R₁.function p.1 - R₂.function p.1) := by ring
      rw [h8]; exact abs_add_le _ _
    have h72 : |p.2 - R₁.function p.1| + |R₁.function p.1 - R₂.function p.1| ≤
        delta + C * lambda₁^3 * delta := add_le_add hpin2 h6
    have h7 : |p.2 - R₂.function p.1| ≤ (1 + C * lambda₁^3) * delta := by
      calc
        |p.2 - R₂.function p.1|
          ≤ |p.2 - R₁.function p.1| + |R₁.function p.1 - R₂.function p.1| := h71
        _ ≤ delta + C * lambda₁^3 * delta := h72
        _ = (1 + C * lambda₁^3) * delta := by ring
    have hdelta_nonneg : 0 ≤ delta := by linarith
    have h8 : (1 + C * lambda₁^3) * delta ≤ lambda₃ * delta :=
      mul_le_mul_of_nonneg_right hlambda₃_ge1 hdelta_nonneg
    have h9 : |p.2 - R₂.function p.1| ≤ lambda₃ * delta := le_trans h7 h8
    have h_goal : p.1 ∈ J.carrier ∧ |p.2 - U₁₃.function p.1| ≤ lambda₃ * delta :=
      ⟨hpinJ, h9⟩
    have h_final : p ∈ U₁₃.carrier := by
      rw [CurvilinearRectangle.carrier]
      simpa [verticalNeighborhoodOn, Set.mem_setOf_eq] using h_goal
    exact h_final
  have hR3_sub : R₃.carrier ⊆ U₁₃.carrier := by
    intro p hp
    have hpin1 : p.1 ∈ R₃.interval.carrier := by
      simpa [CurvilinearRectangle.carrier, verticalNeighborhoodOn] using hp |>.1
    have hpin2 : |p.2 - R₃.function p.1| ≤ delta := by
      simpa [CurvilinearRectangle.carrier, verticalNeighborhoodOn] using hp |>.2
    have hpinJ : p.1 ∈ J.carrier := by
      have h1 : a₃ ≤ (p.1 : ℝ) := hpin1.1
      have h2 : (p.1 : ℝ) ≤ b₃ := hpin1.2
      have h3 : c ≤ (p.1 : ℝ) := by
        have h4 : a ≤ a₃ := min_le_right a₁ a₃
        linarith [hc_le_a]
      have h4 : (p.1 : ℝ) ≤ c + L := by
        have h5 : b₃ ≤ b := le_max_right b₁ b₃
        linarith [hb_le_cL]
      exact ⟨h3, h4⟩
    have h5 : p.1 ∈ R₂.intervalHullCarrier R₃ := hR3_in_hull23 hpin1
    have h6 : |R₂.function p.1 - R₃.function p.1| ≤ C * lambda₂^3 * delta := by
      rw [hrpow2] at hf23
      exact hf23 p.1 h5
    have h6' : |R₃.function p.1 - R₂.function p.1| ≤ C * lambda₂^3 * delta := by
      have h_comm : |R₃.function p.1 - R₂.function p.1| = |R₂.function p.1 - R₃.function p.1| := by
        rw [abs_sub_comm]
      rw [h_comm]; exact h6
    have h71 : |p.2 - R₂.function p.1| ≤
        |p.2 - R₃.function p.1| + |R₃.function p.1 - R₂.function p.1| := by
      have h8 : p.2 - R₂.function p.1 =
          (p.2 - R₃.function p.1) + (R₃.function p.1 - R₂.function p.1) := by ring
      rw [h8]; exact abs_add_le _ _
    have h72 : |p.2 - R₃.function p.1| + |R₃.function p.1 - R₂.function p.1| ≤
        delta + C * lambda₂^3 * delta := add_le_add hpin2 h6'
    have h7 : |p.2 - R₂.function p.1| ≤ (1 + C * lambda₂^3) * delta := by
      calc
        |p.2 - R₂.function p.1|
          ≤ |p.2 - R₃.function p.1| + |R₃.function p.1 - R₂.function p.1| := h71
        _ ≤ delta + C * lambda₂^3 * delta := h72
        _ = (1 + C * lambda₂^3) * delta := by ring
    have hdelta_nonneg : 0 ≤ delta := by linarith
    have h8 : (1 + C * lambda₂^3) * delta ≤ lambda₃ * delta :=
      mul_le_mul_of_nonneg_right hlambda₃_ge2 hdelta_nonneg
    have h9 : |p.2 - R₂.function p.1| ≤ lambda₃ * delta := le_trans h7 h8
    have h_goal : p.1 ∈ J.carrier ∧ |p.2 - U₁₃.function p.1| ≤ lambda₃ * delta :=
      ⟨hpinJ, h9⟩
    have h_final : p ∈ U₁₃.carrier := by
      rw [CurvilinearRectangle.carrier]
      simpa [verticalNeighborhoodOn, Set.mem_setOf_eq] using h_goal
    exact h_final
  have h_main : R₁.carrier ∪ R₃.carrier ⊆ U₁₃.carrier := by
    intro x hx
    cases hx with
    | inl h => exact hR1_sub h
    | inr h => exact hR3_sub h
  exact ⟨U₁₃, hU13_fam, h_main⟩

end Kakeya.Cinematic
