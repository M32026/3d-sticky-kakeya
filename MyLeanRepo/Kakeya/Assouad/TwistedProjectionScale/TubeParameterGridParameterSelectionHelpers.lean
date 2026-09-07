import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberGridParameterSelectionHelpers
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameterGridParameterSelectionStatement
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Helper lemmas for tube-parameter grid parameter selection

Large-base estimate for the four-dimensional branching constant and the
active-cardinality logarithmic bound.
-/

noncomputable section

namespace Kakeya.Assouad

/-- There exists a base `≥ 3` such that the four-dimensional branching
constant `2 * (Nat.log 2 ((base + 1)^4) + 1)` is at most `base^eta`. -/
lemma exists_large_base4 (eta : ℝ) (heta : 0 < eta) :
    ∃ base : ℕ, 3 ≤ base ∧
      (2 * (Nat.log 2 ((base + 1) ^ 4) + 1) : ℝ) ≤
        (base : ℝ) ^ eta := by
  set c : ℝ := eta / 2 with hc_def
  have hc_pos : 0 < c := by linarith
  set C : ℝ := 8 / (Real.log 2 * c) with hC_def
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hC_pos : 0 < C := by positivity
  set C' : ℝ := C * (2 : ℝ) ^ c with hC'_def
  have hC'_pos : 0 < C' := by positivity
  set threshold : ℝ := C' + 2 with hthreshold_def
  have hthreshold_pos : 0 < threshold := by positivity
  have h1 : ∃ (y : ℝ), 1 ≤ y ∧ y ^ c ≥ threshold := by
    let y : ℝ := threshold ^ (1 / c)
    have hy_pos : 0 < y := by positivity
    have hy1 : 1 ≤ y := by
      have h4 : 1 ≤ threshold := by linarith
      have h5 : 0 < 1 / c := by positivity
      exact Real.one_le_rpow h4 (le_of_lt h5)
    have hy2 : y ^ c = threshold := by
      rw [← Real.rpow_mul (by linarith)]
      have h6 : (1 / c) * c = 1 := by
        field_simp [hc_pos.ne'] <;> ring
      rw [h6, Real.rpow_one]
    exact ⟨y, hy1, by rw [hy2]⟩
  obtain ⟨y, hy1, hy2⟩ := h1
  have h_exists_base :
      ∃ (base : ℕ), 3 ≤ base ∧ (base : ℝ) ≥ y := by
    let n : ℕ := Nat.ceil (max y 3)
    have hn1 : (max y 3 : ℝ) ≤ n := Nat.le_ceil _
    have hn2 : 3 ≤ n := by
      have h3 : (3 : ℝ) ≤ max y 3 := le_max_right _ _
      exact_mod_cast h3.trans hn1
    have hn3 : y ≤ (n : ℝ) := by
      have h4 : y ≤ max y 3 := le_max_left _ _
      exact h4.trans hn1
    exact ⟨n, hn2, hn3⟩
  obtain ⟨base, hbase3, hbase_y⟩ := h_exists_base
  have hbase_pos : (0 : ℝ) < (base : ℝ) := by positivity
  have hbase1 : (1 : ℝ) ≤ (base : ℝ) := by linarith
  have h1 : (base : ℝ) ^ c ≥ threshold := by
    calc
      (base : ℝ) ^ c ≥ y ^ c :=
        Real.rpow_le_rpow (by linarith) hbase_y (by linarith)
      _ ≥ threshold := hy2
  have h2 : (base : ℝ) ^ c ≥ C' + 2 := by
    simpa [hthreshold_def] using h1
  have h3 : (base : ℝ) ^ c ≥ 2 := by linarith
  have h4 :
      Real.log ((base : ℝ) + 1) ≤
        ((base : ℝ) + 1) ^ c / c :=
    Real.log_le_rpow_div (by linarith) hc_pos
  have h5 : (base : ℝ) + 1 ≤ 2 * (base : ℝ) := by linarith
  have h6 :
      ((base : ℝ) + 1) ^ c ≤ (2 * (base : ℝ)) ^ c :=
    Real.rpow_le_rpow (by linarith) h5 (by linarith)
  have h7 :
      (2 * (base : ℝ)) ^ c =
        (2 : ℝ) ^ c * (base : ℝ) ^ c := by
    rw [Real.mul_rpow (by norm_num) (by positivity)] <;> ring
  have h8 :
      Real.log ((base : ℝ) + 1) ≤
        (2 : ℝ) ^ c * (base : ℝ) ^ c / c := by
    have h81 :
        ((base : ℝ) + 1) ^ c ≤
          (2 : ℝ) ^ c * (base : ℝ) ^ c :=
      h6.trans_eq h7
    calc
      Real.log ((base : ℝ) + 1)
          ≤ ((base : ℝ) + 1) ^ c / c := h4
      _ ≤ ((2 : ℝ) ^ c * (base : ℝ) ^ c) / c := by
        gcongr <;> linarith
  have h9 :
      (Nat.log 2 ((base + 1) ^ 4) : ℝ) ≤
        4 * Real.log ((base : ℝ) + 1) / Real.log 2 := by
    have h91 : 0 < (base + 1) ^ 4 := by positivity
    have h92 :
        (Nat.log 2 ((base + 1) ^ 4) : ℝ) ≤
          Real.logb (2 : ℝ) (((base + 1) ^ 4 : ℕ) : ℝ) :=
      Real.natLog_le_logb ((base + 1) ^ 4) 2
    have h93 :
        Real.logb (2 : ℝ) (((base + 1) ^ 4 : ℕ) : ℝ) =
          Real.log (((base + 1) ^ 4 : ℕ) : ℝ) / Real.log 2 := by
      rw [Real.logb] <;> ring
    rw [h93] at h92
    have h94 :
        (((base + 1) ^ 4 : ℕ) : ℝ) = ((base : ℝ) + 1) ^ 4 := by
      simp [pow_succ] <;> ring
    rw [h94] at h92
    have h95 :
        Real.log (((base : ℝ) + 1) ^ 4) =
          4 * Real.log ((base : ℝ) + 1) := by
      rw [Real.log_pow] <;> ring
    rw [h95] at h92
    exact h92
  have h10 :
      (2 * (Nat.log 2 ((base + 1) ^ 4) + 1) : ℝ) ≤
        8 * Real.log ((base : ℝ) + 1) / Real.log 2 + 2 := by
    calc
      (2 * (Nat.log 2 ((base + 1) ^ 4) + 1) : ℝ)
          = 2 * (Nat.log 2 ((base + 1) ^ 4) : ℝ) + 2 := by
            simp [mul_add] <;> ring
      _ ≤ 2 * (4 * Real.log ((base : ℝ) + 1) / Real.log 2) + 2 := by
            gcongr <;> linarith
      _ = 8 * Real.log ((base : ℝ) + 1) / Real.log 2 + 2 := by ring
  have h11 :
      8 * Real.log ((base : ℝ) + 1) / Real.log 2 ≤
        C * (2 : ℝ) ^ c * (base : ℝ) ^ c := by
    calc
      8 * Real.log ((base : ℝ) + 1) / Real.log 2
          ≤ 8 * ((2 : ℝ) ^ c * (base : ℝ) ^ c / c) / Real.log 2 := by
            gcongr
      _ = C * (2 : ℝ) ^ c * (base : ℝ) ^ c := by
        simp [hC_def] <;> ring
  have h12 :
      (2 * (Nat.log 2 ((base + 1) ^ 4) + 1) : ℝ) ≤
        C' * (base : ℝ) ^ c + 2 := by
    calc
      (2 * (Nat.log 2 ((base + 1) ^ 4) + 1) : ℝ)
          ≤ 8 * Real.log ((base : ℝ) + 1) / Real.log 2 + 2 := h10
      _ ≤ C * (2 : ℝ) ^ c * (base : ℝ) ^ c + 2 := by gcongr
      _ = C' * (base : ℝ) ^ c + 2 := by
        simp [hC'_def] <;> ring
  have h13 :
      C' * (base : ℝ) ^ c + 2 ≤ (base : ℝ) ^ (2 * c) := by
    have h14 :
        C' * (base : ℝ) ^ c + 2 ≤
          (C' + 2) * (base : ℝ) ^ c := by
      have h15 : 2 ≤ (base : ℝ) ^ c := h3
      nlinarith [Real.rpow_nonneg (by linarith) c]
    have h16 :
        (C' + 2) * (base : ℝ) ^ c ≤
          (base : ℝ) ^ c * (base : ℝ) ^ c := by
      have h17 : C' + 2 ≤ (base : ℝ) ^ c := h2
      have h18 : 0 ≤ (base : ℝ) ^ c := Real.rpow_nonneg (by linarith) c
      nlinarith
    have h19 :
        (base : ℝ) ^ c * (base : ℝ) ^ c =
          (base : ℝ) ^ (2 * c) := by
      have hsum : c + c = 2 * c := by ring
      rw [← Real.rpow_add hbase_pos c c, hsum]
    calc
      C' * (base : ℝ) ^ c + 2
          ≤ (C' + 2) * (base : ℝ) ^ c := h14
      _ ≤ (base : ℝ) ^ c * (base : ℝ) ^ c := h16
      _ = (base : ℝ) ^ (2 * c) := h19
  have h20 : 2 * c = eta := by
    rw [hc_def] <;> ring
  have h21 :
      (base : ℝ) ^ (2 * c) = (base : ℝ) ^ eta := by
    rw [h20]
  exact ⟨base, hbase3, h12.trans (h13.trans_eq h21)⟩

/-- Bound the logarithm of the active cardinality under the extremal
cardinality assumption `activeCard ≤ delta^{-3}`. -/
lemma active_card_log_bound
    (activeCard : ℕ) (delta : ℝ) (hdelta : 0 < delta) (hdelta_le1 : delta ≤ 1)
    (h : (activeCard : ENNReal) ≤ Kakeya.realRpowENN delta (-3)) :
    (Nat.log 2 activeCard + 1 : ℝ) ≤
      (3 / Real.log 2 + 1) * (1 + Real.log delta⁻¹) := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogδ_nonneg : 0 ≤ Real.log delta⁻¹ := by
    have h6 : delta⁻¹ ≥ 1 := by
      have h7 : delta ≤ 1 := hdelta_le1
      have h8 : delta⁻¹ ≥ (1 : ℝ)⁻¹ := by gcongr
      have h9 : (1 : ℝ)⁻¹ = 1 := by norm_num
      linarith
    exact Real.log_nonneg h6
  have hK_pos : 0 < (3 / Real.log 2 + 1 : ℝ) := by
    have h : 0 < 3 / Real.log 2 := by positivity
    linarith
  by_cases h_ac : activeCard = 0
  · -- activeCard = 0
    rw [h_ac]
    have h : (Nat.log 2 0 + 1 : ℝ) = 1 := by simp
    rw [h]
    have h2 : 0 ≤ 1 + Real.log delta⁻¹ := by linarith
    have h3 : 0 < 3 / Real.log 2 := by positivity
    have h4 : 1 ≤ (3 / Real.log 2 + 1 : ℝ) := by linarith
    have h5 : 1 ≤ (3 / Real.log 2 + 1 : ℝ) * (1 + Real.log delta⁻¹) := by
      calc
        1 ≤ 1 + Real.log delta⁻¹ := by linarith
        _ ≤ (3 / Real.log 2 + 1 : ℝ) * (1 + Real.log delta⁻¹) := by
          exact le_mul_of_one_le_left h2 h4
    exact h5
  · -- activeCard > 0
    have h_ac_pos : 0 < activeCard := Nat.pos_of_ne_zero h_ac
    have h_ac_nonneg : 0 ≤ (activeCard : ℝ) := by positivity
    have h_rpow_nonneg : 0 ≤ Real.rpow delta (-3) := Real.rpow_nonneg hdelta.le (-3)
    have h_real : (activeCard : ℝ) ≤ Real.rpow delta (-3) := by
      have h1 : (activeCard : ENNReal) = ENNReal.ofReal (activeCard : ℝ) := by simp
      rw [h1] at h
      exact (ENNReal.ofReal_le_ofReal_iff h_rpow_nonneg).mp h
    have h_log_ac :
        Real.log (activeCard : ℝ) ≤ Real.log (Real.rpow delta (-3)) :=
      Real.log_le_log (by exact_mod_cast h_ac_pos) h_real
    have h_log_rpow :
        Real.log (Real.rpow delta (-3)) = 3 * Real.log delta⁻¹ := by
      have h1 : Real.log (Real.rpow delta (-3)) = (-3) * Real.log delta :=
        Real.log_rpow hdelta (-3)
      rw [h1]
      have h2 : Real.log delta⁻¹ = -Real.log delta := by
        rw [Real.log_inv] <;> ring
      rw [h2] <;> ring
    have h_natlog :
        (Nat.log 2 activeCard : ℝ) ≤
          Real.log (activeCard : ℝ) / Real.log 2 :=
      nat_log_le_real_log activeCard h_ac_pos
    have h_main :
        (Nat.log 2 activeCard : ℝ) ≤
          3 * Real.log delta⁻¹ / Real.log 2 := by
      calc
        (Nat.log 2 activeCard : ℝ)
            ≤ Real.log (activeCard : ℝ) / Real.log 2 := h_natlog
        _ ≤ Real.log (Real.rpow delta (-3)) / Real.log 2 := by gcongr
        _ = 3 * Real.log delta⁻¹ / Real.log 2 := by
            rw [h_log_rpow] <;> ring
    have h4 :
        (Nat.log 2 activeCard + 1 : ℝ) ≤
          3 * Real.log delta⁻¹ / Real.log 2 + 1 := by linarith
    have h5 :
        3 * Real.log delta⁻¹ / Real.log 2 + 1 ≤
          (3 / Real.log 2 + 1) * (1 + Real.log delta⁻¹) := by
      have h6 : 0 ≤ Real.log delta⁻¹ := hlogδ_nonneg
      have h7 : (3 / Real.log 2 + 1) * (1 + Real.log delta⁻¹) -
          (3 * Real.log delta⁻¹ / Real.log 2 + 1) =
        3 / Real.log 2 + Real.log delta⁻¹ := by
        field_simp [hlog2_pos.ne'] <;> ring
      have h8 : 0 ≤ 3 / Real.log 2 + Real.log delta⁻¹ := by positivity
      linarith
    exact h4.trans h5

end Kakeya.Assouad
