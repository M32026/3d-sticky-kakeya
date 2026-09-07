import MyLeanRepo.Kakeya.Assouad.PropStickyFiniteNearbyScheduleStatements

/-!
# Finite representative nearby-scale schedule

Choose a finite geometric schedule of requested scales and attach the
supplied nearby-scale witness at each representative.  Every admissible
requested scale is bounded by one representative actual scale, while two
applications of the ambient nearby-window constant fit inside the output
constant.
-/

noncomputable section

namespace Kakeya.Assouad

open Kakeya.Streamlined

theorem wz2_prop_sticky_finite_nearby_schedule :
    WZ2PropStickyFiniteNearbyScheduleStatement := by
  classical
  intro delta family C outputConstant N hdelta hdelta1 hC hCtop hpow hout hcwa
  set c : ℝ := C.toReal with hc_def
  have hC_eq : C = ENNReal.ofReal c := by
    rw [ENNReal.ofReal_toReal] <;> exact hCtop
  have h1 : (2 : ENNReal) < C := hC
  rw [hC_eq] at h1
  have h4 : ENNReal.ofReal (2 : ℝ) < ENNReal.ofReal c := by simpa using h1
  have hc_pos : 0 < c := by
    by_contra h
    have h' : c ≤ 0 := by linarith
    have h'' : ENNReal.ofReal c = 0 := by
      rw [ENNReal.ofReal_eq_zero.mpr] <;> linarith
    rw [h''] at h4
    simp at h4
  have hc2 : (2 : ℝ) < c :=
    (ENNReal.ofReal_lt_ofReal_iff hc_pos).mp h4
  have hc1 : 1 < c := by linarith
  have h_pow_eq : ∀ n : ℕ, C ^ n = ENNReal.ofReal (c ^ n) := by
    intro n
    induction n with
    | zero => simp [hC_eq]
    | succ n ih =>
      have h_mul : ENNReal.ofReal (c ^ n) * ENNReal.ofReal c =
          ENNReal.ofReal (c ^ (n + 1)) := by
        have h1 : ENNReal.ofReal (c ^ n) * ENNReal.ofReal c =
            ENNReal.ofReal ((c ^ n) * c) := by
          rw [← ENNReal.ofReal_mul (by positivity)] <;> rfl
        rw [h1]
        have h2 : (c ^ n) * c = c ^ (n + 1) := by ring
        rw [h2]
      rw [pow_succ, ih, hC_eq, h_mul]
  have hN : 1 ≤ delta * c ^ N := by
    have h2 : ENNReal.ofReal (1 / delta) ≤ C ^ N := hpow
    rw [h_pow_eq N] at h2
    have h3 : 1 / delta ≤ c ^ N :=
      (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h2
    have h4 : 0 < delta := hdelta
    have h5 : 1 ≤ delta * (1 / delta) := by
      field_simp [h4.ne'] <;> linarith
    calc
      1 ≤ delta * (1 / delta) := h5
      _ ≤ delta * c ^ N := by gcongr
  let p : ℕ → Prop := fun n => 1 ≤ delta * c ^ n
  have hp : ∃ n, p n := ⟨N, hN⟩
  set k : ℕ := Nat.find hp with hk_def
  have hk : p k := Nat.find_spec (H := hp)
  have hmin : ∀ m < k, delta * c ^ m < 1 := by
    intro m hm
    have h4 : ¬p m := Nat.find_min (H := hp) (m := m) hm
    simpa [p] using h4
  have hkle : k ≤ N := Nat.find_min' (H := hp) (m := N) hN
  let s : ℕ → ℝ := fun n => min (delta * c ^ n) 1
  have hs_k : s k = 1 := by
    have h : 1 ≤ delta * c ^ k := hk
    exact min_eq_right h
  have hs_lt : ∀ m < k, s m = delta * c ^ m := by
    intro m hm
    have h : delta * c ^ m < 1 := hmin m hm
    exact min_eq_left (by linarith)
  have hs0 : s 0 = delta := by
    have h : delta ≤ 1 := hdelta1
    have h2 : s 0 = min (delta * c ^ 0) 1 := by rfl
    rw [h2]
    have h3 : min (delta * c ^ 0) 1 = delta := by
      simp [h] <;> linarith
    exact h3
  have hs_delta : ∀ n, delta ≤ s n := by
    intro n
    have h11 : 1 ≤ c := by linarith
    have h12 : c ^ 0 ≤ c ^ n := pow_le_pow_right₀ h11 (by omega)
    have h1 : 1 ≤ c ^ n := by simpa using h12
    have h2 : delta ≤ delta * c ^ n := by
      have h3 : 0 ≤ delta := by linarith
      nlinarith
    exact le_min h2 hdelta1
  have hs_le1 : ∀ n, s n ≤ 1 := by
    intro n
    exact min_le_right _ _
  set scaleCount : ℕ := k + 1 with hscaleCount_def
  have hscaleCount_pos : 0 < scaleCount := by simp [scaleCount]
  have hscaleCount_le : scaleCount ≤ N + 1 := by
    simp [scaleCount, hkle] <;> omega
  set requested : Fin scaleCount → AdmissibleScale delta := fun i =>
    ⟨s i.val, hs_delta i.val, hs_le1 i.val⟩
    with hrequested_def
  have h_requested_val : ∀ i, (requested i).1 = s i.val := by
    intro i
    rfl
  set witness : ∀ i : Fin scaleCount,
      WZ2PaperNearbyScaleCoverData family (requested i) C :=
    fun i => Classical.choice (hcwa.2.2 (requested i))
    with hwitness_def
  set rho_actual : Fin scaleCount → ℝ :=
    fun i => (witness i).rho
    with hrho_actual_def
  have h_witness_le : ∀ i, (requested i).1 ≤ rho_actual i :=
    fun i => (witness i).requested_le
  have h_witness_lt_real : ∀ i, rho_actual i < c * (requested i).1 := by
    intro i
    have h : ENNReal.ofReal (rho_actual i) <
        C * ENNReal.ofReal (requested i).1 :=
      (witness i).within_factor
    have hpos : 0 < (requested i).1 := by
      have h2 : delta ≤ (requested i).1 := (requested i).2.1
      linarith
    have hC' : C * ENNReal.ofReal (requested i).1 =
        ENNReal.ofReal (c * (requested i).1) := by
      rw [hC_eq, ENNReal.ofReal_mul (by linarith)] <;> rfl
    rw [hC'] at h
    have hpos2 : 0 < c * (requested i).1 := by positivity
    exact (ENNReal.ofReal_lt_ofReal_iff hpos2).mp h
  let q (rho₀ : AdmissibleScale delta) : ℕ → Prop :=
    fun n => rho₀.1 ≤ s n
  have hqk : ∀ rho₀, q rho₀ k := by
    intro rho₀
    dsimp only [q]
    have h : rho₀.1 ≤ 1 := rho₀.2.2
    rw [hs_k]
    exact h
  let j_func : AdmissibleScale delta → ℕ := fun rho₀ =>
    Nat.find ⟨k, hqk rho₀⟩
  have hj_spec : ∀ rho₀, rho₀.1 ≤ s (j_func rho₀) := by
    intro rho₀
    let hq : ∃ n, q rho₀ n := ⟨k, hqk rho₀⟩
    exact Nat.find_spec (H := hq)
  have hj_min : ∀ rho₀ m, m < j_func rho₀ → s m < rho₀.1 := by
    intro rho₀ m hm
    let hq : ∃ n, q rho₀ n := ⟨k, hqk rho₀⟩
    have h : ¬q rho₀ m := Nat.find_min (H := hq) (m := m) hm
    simpa [q] using h
  have hj_le_k : ∀ rho₀, j_func rho₀ ≤ k := by
    intro rho₀
    let hq : ∃ n, q rho₀ n := ⟨k, hqk rho₀⟩
    exact Nat.find_min' (H := hq) (m := k) (hqk rho₀)
  have h_key_bound : ∀ rho₀, s (j_func rho₀) < c * rho₀.1 := by
    intro rho₀
    set j : ℕ := j_func rho₀ with hj_def
    have hj_le : j ≤ k := hj_le_k rho₀
    by_cases hj0 : j = 0
    · have h_rho_le : rho₀.1 ≤ s j := hj_spec rho₀
      have h_j0 : j = 0 := hj0
      rw [h_j0] at h_rho_le
      rw [hs0] at h_rho_le
      have h_rho_eq : rho₀.1 = delta := by
        have h6 : delta ≤ rho₀.1 := rho₀.2.1
        linarith
      rw [h_j0, hs0, h_rho_eq]
      have h7 : delta < c * delta := by
        have h8 : 0 < delta := hdelta
        nlinarith
      exact h7
    · have hj_pos : 0 < j := by omega
      have h_prev : s (j - 1) < rho₀.1 :=
        hj_min rho₀ (j - 1) (by omega)
      have h_j1_lt_k : j - 1 < k := by omega
      have h_s_prev : s (j - 1) = delta * c ^ (j - 1) :=
        hs_lt (j - 1) h_j1_lt_k
      rw [h_s_prev] at h_prev
      by_cases hjk : j < k
      · have h_s_j : s j = delta * c ^ j := hs_lt j hjk
        rw [h_s_j]
        have h9 : delta * c ^ j = c * (delta * c ^ (j - 1)) := by
          have h10 : j = (j - 1) + 1 := by omega
          rw [h10]
          simp [pow_succ] <;> ring
        rw [h9]
        exact mul_lt_mul_of_pos_left h_prev hc_pos
      · have h_j_eq_k : j = k := by omega
        have h_k_pos : 0 < k := by omega
        rw [h_j_eq_k, hs_k]
        have h_prev_k : delta * c ^ (k - 1) < rho₀.1 := by
          have h_eq : j - 1 = k - 1 := by omega
          rw [h_eq] at h_prev
          exact h_prev
        have h10 : c * (delta * c ^ (k - 1)) < c * rho₀.1 :=
          mul_lt_mul_of_pos_left h_prev_k hc_pos
        have h_k_succ : ∃ k', k = k' + 1 :=
          Nat.exists_eq_succ_of_ne_zero (by omega)
        rcases h_k_succ with ⟨k', hkeq⟩
        have h11 : c * (delta * c ^ (k - 1)) = delta * c ^ k := by
          rw [hkeq]
          simp [pow_succ] <;> ring
        rw [h11] at h10
        have h12 : (1 : ℝ) < c * rho₀.1 := by
          have h13 : 1 ≤ delta * c ^ k := hk
          linarith
        exact h12
  have hj_lt : ∀ rho₀, j_func rho₀ < scaleCount := by
    intro rho₀
    have h2 : j_func rho₀ ≤ k := hj_le_k rho₀
    simp [scaleCount] at * <;> omega
  let representative : AdmissibleScale delta → Fin scaleCount :=
    fun rho₀ => ⟨j_func rho₀, hj_lt rho₀⟩
  have h_rep_val : ∀ rho₀, (representative rho₀).val = j_func rho₀ := by
    intro rho₀
    rfl
  have h_requested_grid_le : ∀ rho₀,
      rho₀.1 ≤ (requested (representative rho₀)).1 := by
    intro rho₀
    have h := hj_spec rho₀
    simpa [requested, representative] using h
  have h_requested_grid_within_output : ∀ rho₀,
      ENNReal.ofReal (requested (representative rho₀)).1 <
        outputConstant * ENNReal.ofReal rho₀.1 := by
    intro rho₀
    have hreal :
        (requested (representative rho₀)).1 <
          c * rho₀.1 := by
      have h := h_key_bound rho₀
      simpa [requested, representative] using h
    have hrequestedPos : 0 < (requested (representative rho₀)).1 := by
      exact hdelta.trans_le
        (requested (representative rho₀)).2.1
    have hrhoPos : 0 < rho₀.1 := by
      exact hdelta.trans_le rho₀.2.1
    have hCOfReal :
        ENNReal.ofReal c = C := hC_eq.symm
    have hENN :
        ENNReal.ofReal (requested (representative rho₀)).1 <
          C * ENNReal.ofReal rho₀.1 := by
      have hright : 0 < c * rho₀.1 := by positivity
      have h :=
        (ENNReal.ofReal_lt_ofReal_iff hright).mpr hreal
      rw [ENNReal.ofReal_mul (by positivity), hCOfReal] at h
      exact h
    exact hENN.trans_le (by
      gcongr
      have hCone : (1 : ENNReal) ≤ C :=
        (show (1 : ENNReal) ≤ 2 by norm_num).trans
          (le_of_lt hC)
      have hCsquare : C ≤ C * C := by
        calc
          C = C * 1 := by simp
          _ ≤ C * C := by gcongr
      exact hCsquare.trans hout)
  have h_requested_le_proof : ∀ rho₀,
      rho₀.1 ≤ rho_actual (representative rho₀) := by
    intro rho₀
    set j : ℕ := j_func rho₀ with hj_def
    have h1 : rho₀.1 ≤ s j := hj_spec rho₀
    have h2 : s j = (requested (representative rho₀)).1 := by
      rw [h_requested_val, h_rep_val] <;> rfl
    have h3 : (requested (representative rho₀)).1 ≤
        rho_actual (representative rho₀) :=
      h_witness_le (representative rho₀)
    linarith [h1, h2, h3]
  have h_within_output_proof : ∀ rho₀,
      ENNReal.ofReal (rho_actual (representative rho₀)) <
        outputConstant * ENNReal.ofReal rho₀.1 := by
    intro rho₀
    set j : ℕ := j_func rho₀ with hj_def
    have h_key : s j < c * rho₀.1 := h_key_bound rho₀
    have h_req_eq : (requested (representative rho₀)).1 = s j := by
      rw [h_requested_val, h_rep_val] <;> rfl
    have h_lt1 : rho_actual (representative rho₀) < c * s j := by
      have h := h_witness_lt_real (representative rho₀)
      rw [h_req_eq] at h
      exact h
    have h_lt2 : c * s j < c * (c * rho₀.1) :=
      mul_lt_mul_of_pos_left h_key hc_pos
    have h_lt3 : rho_actual (representative rho₀) <
        c ^ 2 * rho₀.1 := by
      calc
        rho_actual (representative rho₀) < c * s j := h_lt1
        _ < c * (c * rho₀.1) := h_lt2
        _ = c ^ 2 * rho₀.1 := by ring
    have h_rho_pos : 0 < rho₀.1 := by
      have h5 : delta ≤ rho₀.1 := rho₀.2.1
      linarith
    have h_pos2 : 0 < c ^ 2 * rho₀.1 := by positivity
    have h_enn : ENNReal.ofReal (rho_actual (representative rho₀)) <
        ENNReal.ofReal (c ^ 2 * rho₀.1) := by
      exact (ENNReal.ofReal_lt_ofReal_iff h_pos2).mpr h_lt3
    have h_mul : ENNReal.ofReal (c ^ 2 * rho₀.1) =
        ENNReal.ofReal (c ^ 2) * ENNReal.ofReal rho₀.1 := by
      rw [ENNReal.ofReal_mul (by positivity)] <;> rfl
    rw [h_mul] at h_enn
    have h_C2 : ENNReal.ofReal (c ^ 2) = C * C := by
      have h5 : C = ENNReal.ofReal c := hC_eq
      calc
        ENNReal.ofReal (c ^ 2) =
            ENNReal.ofReal (c * c) := by ring_nf
        _ = ENNReal.ofReal c * ENNReal.ofReal c := by
          rw [ENNReal.ofReal_mul (by linarith)] <;> rfl
        _ = C * C := by rw [← h5] <;> rfl
    rw [h_C2] at h_enn
    have h7 : (C * C) * ENNReal.ofReal rho₀.1 ≤
        outputConstant * ENNReal.ofReal rho₀.1 := by
      gcongr
      <;> exact hout
    exact h_enn.trans_le h7
  refine
    ⟨scaleCount, hscaleCount_pos, hscaleCount_le,
      k, rfl, requested, ?_, hk, hmin,
      ?_, ?_, ?_,
      witness, representative,
      h_requested_grid_le, ?_, ?_, h_requested_grid_within_output,
      h_requested_le_proof, h_within_output_proof⟩
  intro coordinate
  rfl
  · intro index hindex
    have hindexLt : index < k := by omega
    have hnextLt : index + 1 < k := by omega
    have hcurrent :
        s index = delta * c ^ index :=
      hs_lt index hindexLt
    have hnext :
        s (index + 1) = delta * c ^ (index + 1) :=
      hs_lt (index + 1) hnextLt
    change 2 * s index ≤ s (index + 1)
    rw [hcurrent, hnext, pow_succ]
    calc
      2 * (delta * c ^ index) ≤
          c * (delta * c ^ index) := by
        exact mul_le_mul_of_nonneg_right hc2.le (by positivity)
      _ = delta * (c ^ index * c) := by ring
  · intro index hindex
    have hcurrent :
        s index = delta * c ^ index := by
      apply hs_lt
      omega
    by_cases hnextTop : index + 1 = k
    · have hnext :
          s (index + 1) = 1 := by
        rw [hnextTop, hs_k]
      change
        ENNReal.ofReal (s (index + 1)) ≤
          C * ENNReal.ofReal (s index)
      have hreach :
          1 ≤ c * (delta * c ^ index) := by
        have hpow :
            c * (delta * c ^ index) =
              delta * c ^ (index + 1) := by
          rw [pow_succ]
          ring
        rw [hpow, hnextTop]
        exact hk
      calc
        ENNReal.ofReal (s (index + 1)) =
            ENNReal.ofReal 1 := by rw [hnext]
        _ ≤ ENNReal.ofReal (c * (delta * c ^ index)) :=
          ENNReal.ofReal_mono hreach
        _ =
            ENNReal.ofReal c *
              ENNReal.ofReal (delta * c ^ index) := by
          exact ENNReal.ofReal_mul hc_pos.le
        _ = C * ENNReal.ofReal (s index) := by
          rw [hC_eq, hcurrent]
    · have hnextLt : index + 1 < k := by omega
      have hnext :
          s (index + 1) = delta * c ^ (index + 1) :=
        hs_lt (index + 1) hnextLt
      change
        ENNReal.ofReal (s (index + 1)) ≤
          C * ENNReal.ofReal (s index)
      calc
        ENNReal.ofReal (s (index + 1)) =
            ENNReal.ofReal
              (c * (delta * c ^ index)) := by
          rw [hnext, pow_succ]
          congr 1
          ring
        _ =
            ENNReal.ofReal c *
              ENNReal.ofReal (delta * c ^ index) := by
          exact ENNReal.ofReal_mul hc_pos.le
        _ = C * ENNReal.ofReal (s index) := by
          rw [hC_eq, hcurrent]
        _ ≤ C * ENNReal.ofReal (s index) := le_rfl
  · intro first second hfirstSecond
    rw [h_requested_val, h_requested_val]
    dsimp only [s]
    apply min_le_min_right
    gcongr
    exact hc1.le
  · intro rho₀ index hindex
    have h := hj_min rho₀ index (by
      simpa [representative] using hindex)
    simpa [requested, representative] using h
  intro rho₀
  have hreal :
      (requested (representative rho₀)).1 <
        c * rho₀.1 := by
    have h := h_key_bound rho₀
    simpa [requested, representative] using h
  have hright : 0 < c * rho₀.1 := by
    have hrhoPos : 0 < rho₀.1 :=
      hdelta.trans_le rho₀.2.1
    positivity
  have h :=
    (ENNReal.ofReal_lt_ofReal_iff hright).mpr hreal
  rw [ENNReal.ofReal_mul (by positivity), ← hC_eq] at h
  exact h

end Kakeya.Assouad

end
