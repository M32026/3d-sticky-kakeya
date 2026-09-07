import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberGridParameterSelectionStatement
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.LogAbsorption
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Helper lemmas for projected-fiber grid parameter selection

Cardinality, logarithmic, mesh-selection, and large-base estimates used to
absorb atomization and local-child branching losses.
-/

noncomputable section

namespace Kakeya.Assouad

lemma boundedPlanarGridCenters_card_le
    (base levels : ℕ) (hbase : 3 ≤ base) :
    (boundedPlanarGridCenters base levels
      (section7GridIndexBound base levels)).card ≤
      (104 * base ^ levels + 3) ^ 2 := by
  let indexBound : ℕ := section7GridIndexBound base levels
  have h_indexBound : indexBound = 52 * base ^ levels + 1 := by
    rfl
  let s1 : Finset ℤ :=
    Finset.Icc (-(indexBound : ℤ)) (indexBound : ℤ)
  let s2 : Finset (ℤ × ℤ) := s1.product s1
  have h1 :
      boundedPlanarGridCenters base levels indexBound =
        s2.image (planarGridCenter base levels) := by
    rfl
  rw [h1]
  have h2 :
      (s2.image (planarGridCenter base levels)).card ≤ s2.card :=
    Finset.card_image_le
  have h3 : s2.card = s1.card * s1.card := by
    simp [s2, Finset.card_product] <;> ring
  have h41 :
      (-(indexBound : ℤ)) ≤ (indexBound : ℤ) + 1 := by
    have h : 0 ≤ (indexBound : ℤ) := by positivity
    linarith
  have h4 : (s1.card : ℤ) = 2 * (indexBound : ℤ) + 1 := by
    have h42 :
        (s1.card : ℤ) =
          (indexBound : ℤ) + 1 - (-(indexBound : ℤ)) :=
      Int.card_Icc_of_le
        (-(indexBound : ℤ)) (indexBound : ℤ) h41
    rw [h42] <;> ring
  have h4' : s1.card = 2 * indexBound + 1 := by
    exact_mod_cast h4
  have h5 : s2.card = (2 * indexBound + 1) ^ 2 := by
    rw [h3, h4'] <;> ring
  have h6 :
      (s2.image (planarGridCenter base levels)).card ≤
        (2 * indexBound + 1) ^ 2 := by
    calc
      (s2.image (planarGridCenter base levels)).card
          ≤ s2.card := h2
      _ = (2 * indexBound + 1) ^ 2 := h5
  have h7 :
      (2 * indexBound + 1) ^ 2 =
        (104 * base ^ levels + 3) ^ 2 := by
    rw [h_indexBound] <;> ring
  rw [h7] at h6
  exact h6

lemma nat_log_le_real_log (n : ℕ) (hn : 0 < n) :
    (Nat.log 2 n : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 := by
  have h :
      (Nat.log 2 n : ℝ) ≤ Real.logb (2 : ℝ) (n : ℝ) :=
    Real.natLog_le_logb n 2
  have h2 :
      Real.logb (2 : ℝ) (n : ℝ) =
        Real.log (n : ℝ) / Real.log 2 := by
    rw [Real.logb] <;> ring
  rw [h2] at h
  exact h

lemma exists_levels_mesh
    (base : ℕ) (hbase : 3 ≤ base)
    (delta : ℝ) (hdelta : 0 < delta) (hdelta1 : delta < 1) :
    ∃ levels : ℕ,
      delta ≤ ((base ^ levels : ℝ)⁻¹) ∧
        ((base ^ levels : ℝ)⁻¹) < (base : ℝ) * delta := by
  have hbase1 : (1 : ℝ) < (base : ℝ) := by
    exact_mod_cast (show 1 < base from by omega)
  have hlog_base_pos : 0 < Real.log (base : ℝ) :=
    Real.log_pos hbase1
  have hx_nonneg :
      0 ≤ Real.log (delta⁻¹) / Real.log (base : ℝ) := by
    have h1 : 0 ≤ Real.log (delta⁻¹) := by
      have h2 : delta⁻¹ ≥ 1 := by
        have h3 : delta ≤ 1 := by linarith
        have h4 : delta⁻¹ ≥ 1 := by
          calc
            delta⁻¹ ≥ 1⁻¹ := by gcongr
            _ = 1 := by norm_num
        exact h4
      exact Real.log_nonneg h2
    positivity
  set x : ℝ :=
    Real.log (delta⁻¹) / Real.log (base : ℝ) with hx_def
  set levels : ℕ := Nat.floor x with hlevels_def
  have h5 : (levels : ℝ) ≤ x := Nat.floor_le hx_nonneg
  have h6 : x < (levels : ℝ) + 1 := Nat.lt_floor_add_one x
  have h7 : (base : ℝ) ^ levels ≤ delta⁻¹ := by
    have h71 :
        (levels : ℝ) * Real.log (base : ℝ) ≤
          Real.log (delta⁻¹) := by
      calc
        (levels : ℝ) * Real.log (base : ℝ)
            ≤ x * Real.log (base : ℝ) := by gcongr
        _ = Real.log (delta⁻¹) := by
          rw [hx_def]
          field_simp [hlog_base_pos.ne'] <;> ring
    have h72 :
        Real.log ((base : ℝ) ^ levels) ≤
          Real.log (delta⁻¹) := by
      have h :
          Real.log ((base : ℝ) ^ levels) =
            (levels : ℝ) * Real.log (base : ℝ) := by
        rw [Real.log_pow] <;> ring
      rw [h]
      exact h71
    have h73 : 0 < (base : ℝ) ^ levels := by positivity
    have h74 : 0 < delta⁻¹ := by positivity
    exact (Real.log_le_log_iff h73 h74).mp h72
  have h8 : delta⁻¹ < (base : ℝ) ^ (levels + 1) := by
    have h81 :
        Real.log (delta⁻¹) <
          ((levels : ℝ) + 1) * Real.log (base : ℝ) := by
      calc
        Real.log (delta⁻¹)
            = x * Real.log (base : ℝ) := by
              rw [hx_def]
              field_simp [hlog_base_pos.ne'] <;> ring
        _ < ((levels : ℝ) + 1) * Real.log (base : ℝ) := by
          gcongr
    have h82 :
        Real.log (delta⁻¹) <
          Real.log ((base : ℝ) ^ (levels + 1)) := by
      have h :
          Real.log ((base : ℝ) ^ (levels + 1)) =
            ((levels : ℝ) + 1) * Real.log (base : ℝ) := by
        rw [Real.log_pow] <;> simp [Nat.cast_add] <;> ring
      rw [h]
      exact h81
    have h83 : 0 < delta⁻¹ := by positivity
    have h84 : 0 < (base : ℝ) ^ (levels + 1) := by positivity
    exact (Real.log_lt_log_iff h83 h84).mp h82
  have h9 : delta ≤ ((base ^ levels : ℝ)⁻¹) := by
    have h91 : (base ^ levels : ℝ) ≤ delta⁻¹ := h7
    have h92 : 0 < (base ^ levels : ℝ) := by positivity
    have h93 : 0 < delta := hdelta
    calc
      delta = (delta⁻¹)⁻¹ := by
        field_simp [h93.ne'] <;> ring
      _ ≤ ((base ^ levels : ℝ)⁻¹) := by gcongr
  have h10 :
      ((base ^ levels : ℝ)⁻¹) < (base : ℝ) * delta := by
    have h101 :
        delta⁻¹ < (base ^ (levels + 1) : ℝ) := h8
    have h102 : 0 < (base ^ (levels + 1) : ℝ) := by
      positivity
    have h103 : 0 < delta := hdelta
    have h :
        ((base ^ levels : ℝ)⁻¹) =
          (base : ℝ) * ((base ^ (levels + 1) : ℝ)⁻¹) := by
      field_simp [pow_succ] <;> ring
    rw [h]
    have h104 :
        ((base ^ (levels + 1) : ℝ)⁻¹) < delta := by
      calc
        ((base ^ (levels + 1) : ℝ)⁻¹)
            < (delta⁻¹)⁻¹ := by gcongr
        _ = delta := by
          field_simp [h103.ne'] <;> ring
    have h105 : 0 < (base : ℝ) := by positivity
    exact mul_lt_mul_of_pos_left h104 h105
  exact ⟨levels, h9, h10⟩

lemma exists_large_base (eta : ℝ) (heta : 0 < eta) :
    ∃ base : ℕ, 3 ≤ base ∧
      (2 * (Nat.log 2 ((base + 1) ^ 2) + 1) : ℝ) ≤
        (base : ℝ) ^ eta := by
  set c : ℝ := eta / 2 with hc_def
  have hc_pos : 0 < c := by linarith
  set C : ℝ := 4 / (Real.log 2 * c) with hC_def
  have hlog2_pos : 0 < Real.log 2 :=
    Real.log_pos (by norm_num)
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
  have h5 : (base : ℝ) + 1 ≤ 2 * (base : ℝ) := by
    linarith
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
      (Nat.log 2 ((base + 1) ^ 2) : ℝ) ≤
        2 * Real.log ((base : ℝ) + 1) / Real.log 2 := by
    have h91 : 0 < (base + 1) ^ 2 := by positivity
    have h92 :
        (Nat.log 2 ((base + 1) ^ 2) : ℝ) ≤
          Real.logb (2 : ℝ) (((base + 1) ^ 2 : ℕ) : ℝ) :=
      Real.natLog_le_logb ((base + 1) ^ 2) 2
    have h93 :
        Real.logb (2 : ℝ) (((base + 1) ^ 2 : ℕ) : ℝ) =
          Real.log (((base + 1) ^ 2 : ℕ) : ℝ) / Real.log 2 := by
      rw [Real.logb] <;> ring
    rw [h93] at h92
    have h94 :
        (((base + 1) ^ 2 : ℕ) : ℝ) =
          ((base : ℝ) + 1) ^ 2 := by
      simp [pow_two] <;> ring
    rw [h94] at h92
    have h95 :
        Real.log (((base : ℝ) + 1) ^ 2) =
          2 * Real.log ((base : ℝ) + 1) := by
      rw [Real.log_pow] <;> ring
    rw [h95] at h92
    exact h92
  have h10 :
      (2 * (Nat.log 2 ((base + 1) ^ 2) + 1) : ℝ) ≤
        4 * Real.log ((base : ℝ) + 1) / Real.log 2 + 2 := by
    calc
      (2 * (Nat.log 2 ((base + 1) ^ 2) + 1) : ℝ)
          = 2 * (Nat.log 2 ((base + 1) ^ 2) : ℝ) + 2 := by
            simp [mul_add] <;> ring
      _ ≤ 2 *
            (2 * Real.log ((base : ℝ) + 1) / Real.log 2) +
          2 := by
            gcongr <;> linarith
      _ = 4 * Real.log ((base : ℝ) + 1) / Real.log 2 + 2 := by
        ring
  have h11 :
      4 * Real.log ((base : ℝ) + 1) / Real.log 2 ≤
        C * (2 : ℝ) ^ c * (base : ℝ) ^ c := by
    calc
      4 * Real.log ((base : ℝ) + 1) / Real.log 2
          ≤ 4 * ((2 : ℝ) ^ c * (base : ℝ) ^ c / c) /
            Real.log 2 := by gcongr
      _ = C * (2 : ℝ) ^ c * (base : ℝ) ^ c := by
        simp [hC_def] <;> ring
  have h12 :
      (2 * (Nat.log 2 ((base + 1) ^ 2) + 1) : ℝ) ≤
        C' * (base : ℝ) ^ c + 2 := by
    calc
      (2 * (Nat.log 2 ((base + 1) ^ 2) + 1) : ℝ)
          ≤ 4 * Real.log ((base : ℝ) + 1) / Real.log 2 + 2 :=
        h10
      _ ≤ C * (2 : ℝ) ^ c * (base : ℝ) ^ c + 2 := by
        gcongr
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
      have h18 : 0 ≤ (base : ℝ) ^ c :=
        Real.rpow_nonneg (by linarith) c
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

end Kakeya.Assouad
