import MyLeanRepo.Kakeya.Assouad.ExtremalHelpers

/-!
WZ Lemma 30: compare the projection-cover lower bound with a local AD upper
bound carrying one explicit absolute constant.

Given `δ^ε * x ≤ 10000 * N` and `N ≤ K * δ^(-ε) * x^α` with `1 ≤ K`, deduce
`x^(1-α) ≤ 10000 * K * δ^(-2ε)`.

The proof converts the `ENNReal` inequalities to `ℝ` after showing `N ≠ ⊤`
and `K ≠ ⊤`, does the algebra there, and lifts back.
-/

namespace Kakeya.Assouad

theorem ad_covering_comparison_with_constant :
    ADCoveringComparisonWithConstantStatement := by
  intro delta epsilon alpha x N K hdelta _hdelta1 hepsilon halpha halpha1 hx hK h1 h2
  by_cases hx0 : x = 0
  · subst hx0
    have h_pos : 0 < 1 - alpha := by linarith
    have h3 : Real.rpow 0 (1 - alpha) = 0 := by
      have h_pos2 : (1 - alpha) ≠ 0 := by linarith
      exact Real.zero_rpow h_pos2
    have h4 : Kakeya.realRpowENN 0 (1 - alpha) = 0 := by
      simp only [Kakeya.realRpowENN, h3]
      norm_num
    rw [h4]
    simp
  · by_cases hK_top : K = ⊤
    · have hd2ne_pos : 0 < Real.rpow delta (-2 * epsilon) :=
          Real.rpow_pos_of_pos hdelta _
      have h_d2ne_ne_zero : Kakeya.realRpowENN delta (-2 * epsilon) ≠ 0 := by
        have h_eq : Kakeya.realRpowENN delta (-2 * epsilon) =
            ENNReal.ofReal (Real.rpow delta (-2 * epsilon)) := by
          rfl
        rw [h_eq]
        exact mt ENNReal.ofReal_eq_zero.mp (not_le.mpr hd2ne_pos)
      have h_rhs_top : (10000 : ENNReal) * K *
          Kakeya.realRpowENN delta (-2 * epsilon) = ⊤ := by
        rw [hK_top]
        have h : (10000 : ENNReal) * (⊤ : ENNReal) = ⊤ := by simp
        rw [h]
        exact ENNReal.top_mul h_d2ne_ne_zero
      rw [h_rhs_top]
      exact le_top
    · have hx_pos : 0 < x := by
        exact lt_of_le_of_ne hx (Ne.symm hx0)
      set de : ℝ := Real.rpow delta epsilon with hde_def
      set dne : ℝ := Real.rpow delta (-epsilon) with hdne_def
      set xa : ℝ := Real.rpow x alpha with hxa_def
      set x1a : ℝ := Real.rpow x (1 - alpha) with hx1a_def
      set d2ne : ℝ := Real.rpow delta (-2 * epsilon) with hd2ne_def
      set kr : ℝ := K.toReal with hkr_def
      have hde_pos : 0 < de := Real.rpow_pos_of_pos hdelta _
      have hdne_pos : 0 < dne := Real.rpow_pos_of_pos hdelta _
      have hxa_pos : 0 < xa := Real.rpow_pos_of_pos hx_pos _
      have hkr_nonneg : 0 ≤ kr := by
        simp only [hkr_def]
        exact ENNReal.toReal_nonneg
      have h_de_top : Kakeya.realRpowENN delta epsilon ≠ ⊤ := by
        simp [Kakeya.realRpowENN]
      have h_dne_top : Kakeya.realRpowENN delta (-epsilon) ≠ ⊤ := by
        simp [Kakeya.realRpowENN]
      have h_xa_top : Kakeya.realRpowENN x alpha ≠ ⊤ := by
        simp [Kakeya.realRpowENN]
      have h_x_top : ENNReal.ofReal x ≠ ⊤ := ENNReal.ofReal_ne_top
      have h10000_top : (10000 : ENNReal) ≠ ⊤ := by simp
      have hK_top' : K ≠ ⊤ := hK_top
      have h_rhs2_top : (K * Kakeya.realRpowENN delta (-epsilon) *
          Kakeya.realRpowENN x alpha) ≠ ⊤ := by
        apply ENNReal.mul_ne_top
        · apply ENNReal.mul_ne_top hK_top' h_dne_top
        · exact h_xa_top
      have hN_top : N ≠ ⊤ := by
        by_contra hN_eq_top
        rw [hN_eq_top] at h2
        have h_cont : (K * Kakeya.realRpowENN delta (-epsilon) *
            Kakeya.realRpowENN x alpha) = ⊤ := by
          simpa using h2
        exact h_rhs2_top h_cont
      have h_lhs1_top :
          (Kakeya.realRpowENN delta epsilon * ENNReal.ofReal x) ≠ ⊤ :=
        ENNReal.mul_ne_top h_de_top h_x_top
      have h_rhs1_top : ((10000 : ENNReal) * N) ≠ ⊤ :=
        ENNReal.mul_ne_top h10000_top hN_top
      have h1_real :
          (Kakeya.realRpowENN delta epsilon * ENNReal.ofReal x).toReal ≤
            ((10000 : ENNReal) * N).toReal :=
        (ENNReal.toReal_le_toReal h_lhs1_top h_rhs1_top).mpr h1
      have h2_real : N.toReal ≤
          (K * Kakeya.realRpowENN delta (-epsilon) *
              Kakeya.realRpowENN x alpha).toReal :=
        (ENNReal.toReal_le_toReal hN_top h_rhs2_top).mpr h2
      have h1_lhs_simp :
          (Kakeya.realRpowENN delta epsilon * ENNReal.ofReal x).toReal =
            de * x := by
        rw [ENNReal.toReal_mul]
        have h_a : (Kakeya.realRpowENN delta epsilon).toReal = de := by
          rw [Kakeya.realRpowENN, ENNReal.toReal_ofReal hde_pos.le]
        have h_b : (ENNReal.ofReal x).toReal = x := by
          rw [ENNReal.toReal_ofReal hx_pos.le]
        rw [h_a, h_b]
      have h1_rhs_simp : ((10000 : ENNReal) * N).toReal =
          10000 * N.toReal := by
        rw [ENNReal.toReal_mul]
        simp
      rw [h1_lhs_simp, h1_rhs_simp] at h1_real
      have h2_rhs_simp :
          (K * Kakeya.realRpowENN delta (-epsilon) *
              Kakeya.realRpowENN x alpha).toReal =
            kr * dne * xa := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_mul]
        have h_a : K.toReal = kr := by rfl
        have h_b : (Kakeya.realRpowENN delta (-epsilon)).toReal = dne := by
          rw [Kakeya.realRpowENN, ENNReal.toReal_ofReal hdne_pos.le]
        have h_c : (Kakeya.realRpowENN x alpha).toReal = xa := by
          rw [Kakeya.realRpowENN, ENNReal.toReal_ofReal hxa_pos.le]
        rw [h_a, h_b, h_c]
      rw [h2_rhs_simp] at h2_real
      have h_comb : de * x ≤ 10000 * (kr * dne * xa) :=
        calc
          de * x ≤ 10000 * N.toReal := h1_real
          _ ≤ 10000 * (kr * dne * xa) := by gcongr
      have h_div : x / xa ≤ 10000 * kr * dne / de := by
        calc
          x / xa = (de * x) / (de * xa) := by
            field_simp [hde_pos.ne', hxa_pos.ne']
          _ ≤ (10000 * (kr * dne * xa)) / (de * xa) := by
            gcongr
          _ = 10000 * kr * dne / de := by
            field_simp [hde_pos.ne', hxa_pos.ne']
      have h_x1a_eq : x1a = x / xa := by
        have h : Real.rpow x (1 - alpha) =
            Real.rpow x (1 : ℝ) / Real.rpow x alpha :=
          Real.rpow_sub hx_pos (1 : ℝ) alpha
        simpa [x1a, xa] using h
      have h_d2ne_eq : d2ne = dne / de := by
        have h : Real.rpow delta (-2 * epsilon) =
            Real.rpow delta (-epsilon) / Real.rpow delta epsilon := by
          have h2 : (-2 * epsilon) = (-epsilon) - epsilon := by ring
          rw [h2]
          exact Real.rpow_sub hdelta (-epsilon) epsilon
        simpa [d2ne, dne, de] using h
      have h_final : x1a ≤ 10000 * kr * d2ne := by
        have h5 : x / xa ≤ 10000 * kr * dne / de := h_div
        have h6 : x1a = x / xa := h_x1a_eq
        have h7 : 10000 * kr * d2ne = 10000 * kr * (dne / de) := by
          rw [h_d2ne_eq]
        rw [h6, h7]
        have h8 : 10000 * kr * (dne / de) =
            10000 * kr * dne / de := by ring
        rw [h8]
        exact h5
      have h10000_nonneg : (0 : ℝ) ≤ 10000 := by norm_num
      have h10000kr_nonneg : (0 : ℝ) ≤ 10000 * kr :=
        mul_nonneg h10000_nonneg hkr_nonneg
      have h_ofReal_prod : ENNReal.ofReal (10000 * kr * d2ne) =
          (10000 : ENNReal) * K *
            Kakeya.realRpowENN delta (-2 * epsilon) := by
        have h91 : ENNReal.ofReal (10000 * kr * d2ne) =
            ENNReal.ofReal (10000 * kr) * ENNReal.ofReal d2ne := by
          rw [ENNReal.ofReal_mul h10000kr_nonneg]
        have h92 : ENNReal.ofReal (10000 * kr) =
            ENNReal.ofReal (10000 : ℝ) * ENNReal.ofReal kr := by
          rw [ENNReal.ofReal_mul h10000_nonneg]
        have h10 : ENNReal.ofReal (10000 : ℝ) =
            (10000 : ENNReal) := by norm_cast
        have h11 : ENNReal.ofReal kr = K := by
          rw [hkr_def]
          exact ENNReal.ofReal_toReal hK_top'
        have h12 : ENNReal.ofReal d2ne =
            Kakeya.realRpowENN delta (-2 * epsilon) := by
          simp [Kakeya.realRpowENN, d2ne]
        rw [h91, h92, h10, h11, h12]
      have h : ENNReal.ofReal x1a ≤
          ENNReal.ofReal (10000 * kr * d2ne) :=
        ENNReal.ofReal_le_ofReal h_final
      rw [h_ofReal_prod] at h
      have h13 : ENNReal.ofReal x1a =
          Kakeya.realRpowENN x (1 - alpha) := by
        simp [Kakeya.realRpowENN, x1a]
      rw [h13] at h
      exact h

end Kakeya.Assouad
