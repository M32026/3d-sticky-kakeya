import MyLeanRepo.Kakeya.Cinematic.Targets.CenteredSixteenthIntervalCover.Helpers

/-!
# Centered-sixteenth logarithmic interval cover

This is the one-dimensional covering lemma used in the globalization
following PYZ Lemma 39.
-/

namespace Kakeya.Cinematic

open CenteredCoverHelpers ParameterInterval Set

theorem centered_sixteenth_interval_cover :
    CenteredSixteenthIntervalCoverStatement := by
  intro K hK
  let C_cover : ℝ := 2 / Real.log (17 / 15) + 96 * K + 4
  have h_log_pos : 0 < Real.log (17 / 15 : ℝ) := by
    apply Real.log_pos; norm_num
  have hC_pos : 0 < C_cover := by positivity
  refine' ⟨C_cover, hC_pos, _⟩
  intro rho hrho hrhoK

  set L_max : ℝ := (6 * K)⁻¹ with hL_max_def
  set l_max : ℝ := L_max / 16 with hl_max_def
  let a : ℕ → ℝ := fun n => geomLength rho n

  have hK_pos : 0 < K := by linarith
  have h6K_pos : 0 < 6 * K := by positivity
  have h_inv_pos : 0 < (6 * K)⁻¹ := by positivity
  have hL_max_pos : 0 < L_max := by positivity
  have hL_max_le : L_max ≤ 1 := by
    rw [hL_max_def]
    have h : 1 ≤ 6 * K := by linarith
    have h' : (6 * K)⁻¹ ≤ 1 := by
      calc
        (6 * K)⁻¹ = (6 * K)⁻¹ * 1 := by ring
        _ ≤ (6 * K)⁻¹ * (6 * K) := by
          exact mul_le_mul_of_nonneg_left h (by positivity)
        _ = 1 := by field_simp [h6K_pos.ne'] <;> ring
    exact h'
  have hL_max_lt_one : L_max < 1 := by
    rw [hL_max_def]
    have h : 1 < 6 * K := by linarith
    have h' : (6 * K)⁻¹ < 1 := by
      calc
        (6 * K)⁻¹ = (6 * K)⁻¹ * 1 := by ring
        _ < (6 * K)⁻¹ * (6 * K) := by
          exact mul_lt_mul_of_pos_left h h_inv_pos
        _ = 1 := by field_simp [h6K_pos.ne'] <;> ring
    exact h'
  have hrho_le24 : rho ≤ 1 / 24 := by
    have h : (24 * K)⁻¹ ≤ (24 : ℝ)⁻¹ := by
      gcongr <;> linarith
    have h2 : (24 : ℝ)⁻¹ = 1 / 24 := by norm_num
    calc
      rho ≤ (24 * K)⁻¹ := hrhoK
      _ ≤ (24 : ℝ)⁻¹ := h
      _ = 1 / 24 := h2
  have hl_max_pos : 0 < l_max := by positivity
  have h4rho_le : 4 * rho ≤ L_max := by
    rw [hL_max_def]
    have h : 4 * rho ≤ 4 * (24 * K)⁻¹ := by gcongr
    have h2 : 4 * (24 * K)⁻¹ = (6 * K)⁻¹ := by
      field_simp [hK_pos.ne'] <;> ring
    rw [h2] at h
    exact h

  have hN_exists : ∃ n : ℕ, a n > L_max := by
    have h4pos : 0 < 4 * rho := by positivity
    have h_arch :
        ∃ n : ℕ, (L_max / (4 * rho)) < (17 / 15 : ℝ) ^ n :=
      pow_unbounded_of_one_lt (L_max / (4 * rho)) (by norm_num)
    rcases h_arch with ⟨n, hn⟩
    have h6 : 4 * rho * (17 / 15 : ℝ) ^ n > L_max := by
      calc
        4 * rho * (17 / 15 : ℝ) ^ n
            > 4 * rho * (L_max / (4 * rho)) := by gcongr
        _ = L_max := by field_simp [h4pos.ne'] <;> ring
    refine' ⟨n, _⟩
    have h_an : a n = 4 * rho * (17 / 15 : ℝ) ^ n := by
      simp [a, geomLength] <;> ring
    rw [h_an]
    exact h6
  let N : ℕ := Nat.find hN_exists
  have hN : a N > L_max := Nat.find_spec hN_exists
  have hN_min : ∀ m < N, a m ≤ L_max := fun m hm =>
    le_of_not_gt (Nat.find_min hN_exists hm)
  have hN_pos : 0 < N := by
    by_contra h
    have h0 : N = 0 := by omega
    rw [h0] at hN
    have h_a0 : a 0 = 4 * rho := by
      simp [a, geomLength] <;> ring
    rw [h_a0] at hN
    linarith [h4rho_le]
  have hN_pred : a (N - 1) ≤ L_max :=
    hN_min (N - 1) (by omega)
  have h17_15 : 17 * a (N - 1) > 15 * L_max := by
    have h_sub : N - 1 + 1 = N := by omega
    have h2 :
        geomLength rho (N - 1 + 1) =
          (17 / 15 : ℝ) * geomLength rho (N - 1) :=
      geomLength_succ rho (N - 1)
    have h1 : a N = (17 / 15 : ℝ) * a (N - 1) := by
      have h3 : a N = geomLength rho N := by rfl
      have h4 : a (N - 1) = geomLength rho (N - 1) := by rfl
      rw [h3, h4]
      rw [h_sub] at h2
      exact h2
    rw [h1] at hN
    linarith

  have hM_exists :
      ∃ m : ℕ, (m : ℝ) * l_max ≥ 1 - L_max := by
    obtain ⟨m, hm⟩ := exists_nat_ge ((1 - L_max) / l_max)
    refine' ⟨m, _⟩
    calc
      (m : ℝ) * l_max
          ≥ ((1 - L_max) / l_max) * l_max := by gcongr
      _ = 1 - L_max := by
        field_simp [hl_max_pos.ne'] <;> ring
  let M : ℕ := Nat.find hM_exists
  have hM : (M : ℝ) * l_max ≥ 1 - L_max :=
    Nat.find_spec hM_exists
  have hM_min : ∀ m < M, (m : ℝ) * l_max < 1 - L_max :=
    fun m hm => lt_of_not_ge (Nat.find_min hM_exists hm)
  have hM_pos : 0 < M := by
    by_contra h
    have h0 : M = 0 := by omega
    rw [h0] at hM
    norm_num at hM
    exact False.elim (by linarith)
  have hM_pred :
      ((M - 1 : ℕ) : ℝ) * l_max < 1 - L_max :=
    hM_min (M - 1) (by omega)
  have hM_bound : (M : ℝ) < 96 * K + 1 := by
    have h1 : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by
      simp [hM_pos] <;> omega
    rw [h1] at hM_pred
    have h2 : ((M : ℝ) - 1) * l_max < 1 := by linarith
    rw [hl_max_def, hL_max_def] at h2
    have h3 : (M : ℝ) - 1 < 96 * K := by
      field_simp [hK_pos.ne'] at h2 <;> linarith
    linarith
  have h_j_in_bounds :
      ∀ (j : ℕ), j < M →
        (j : ℝ) * l_max + L_max ≤ 1 := by
    intro j hj
    have h4 : (j : ℝ) ≤ ((M - 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega)
    have h5 :
        (j : ℝ) * l_max ≤ ((M - 1 : ℕ) : ℝ) * l_max := by
      gcongr
    have h6 :
        ((M - 1 : ℕ) : ℝ) * l_max < 1 - L_max :=
      hM_pred
    linarith

  have ha_pos : ∀ n, 0 < a n := by
    intro n
    have h1 : 0 < 4 * rho := by positivity
    have h2 : 0 < (17 / 15 : ℝ) ^ n := by positivity
    have h3 : a n = 4 * rho * (17 / 15 : ℝ) ^ n := by
      simp [a, geomLength] <;> ring
    rw [h3]
    positivity
  have ha_le_Lmax : ∀ n, n < N → a n ≤ L_max := hN_min
  have h_pow_ge1 : ∀ n : ℕ, (17 / 15 : ℝ) ^ n ≥ 1 := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
      calc
        (17 / 15 : ℝ) ^ (n + 1)
            = (17 / 15 : ℝ) * (17 / 15 : ℝ) ^ n := by ring
        _ ≥ (17 / 15 : ℝ) * 1 := by gcongr
        _ ≥ 1 := by norm_num
  have ha_ge4rho : ∀ n, a n ≥ 4 * rho := by
    intro n
    have h1 : (17 / 15 : ℝ) ^ n ≥ 1 := h_pow_ge1 n
    have h3 : a n = 4 * rho * (17 / 15 : ℝ) ^ n := by
      simp [a, geomLength] <;> ring
    rw [h3]
    have h4pos : 0 ≤ 4 * rho := by positivity
    have h4 :
        4 * rho * 1 ≤ 4 * rho * (17 / 15 : ℝ) ^ n :=
      mul_le_mul_of_nonneg_left h1 h4pos
    simpa using h4

  let total : ℕ := 2 * N + M + 1
  have h_total_pos : 0 < total := by omega
  let intervalFn : Fin total → ParameterInterval := fun i =>
    if h1 : i.val < N then
      mkParameterInterval 0 (a i.val) (by norm_num)
        (ha_pos i.val).le
        (have h : a i.val ≤ L_max := ha_le_Lmax i.val h1
         have h' : a i.val ≤ 1 := by linarith [hL_max_le]
         h')
    else if h2 : i.val < N + M then
      let j := i.val - N
      mkParameterInterval ((j : ℝ) * l_max)
        ((j : ℝ) * l_max + L_max)
        (by positivity) (by linarith)
        (h_j_in_bounds j (by omega))
    else if h3 : i.val = N + M then
      mkParameterInterval (1 - L_max) 1
        (by linarith) (by linarith) (by norm_num)
    else
      let k := i.val - (N + M + 1)
      have h_k_lt_N : k < N := by omega
      have h_ale : a k ≤ L_max := ha_le_Lmax k h_k_lt_N
      have h_nonneg : 0 ≤ a k := (ha_pos k).le
      have h_lt1 : a k < 1 := by
        linarith [hL_max_lt_one, h_ale]
      have h_left0 : 0 ≤ 1 - a k := by linarith
      have h_le1 : 1 - a k ≤ 1 := by linarith
      mkParameterInterval (1 - a k) 1 h_left0 h_le1
        (by norm_num)
  let intervals : IntervalFamily :=
    { card := total, interval := intervalFn }
  have h_mk_len : ∀ (l r : ℝ) h0 h1 h2,
      (mkParameterInterval l r h0 h1 h2).length = r - l := by
    intro l r h0 h1 h2
    simp [ParameterInterval.length]
  have h_branch_prop : ∀ (i : Fin total),
      4 * rho ≤ (intervals.interval i).length ∧
        (intervals.interval i).IsShort K := by
    intro i
    by_cases h1 : i.val < N
    · have h_eq : intervals.interval i =
          mkParameterInterval 0 (a i.val) (by norm_num)
            (ha_pos i.val).le
            (by linarith [hL_max_le, ha_le_Lmax i.val h1]) := by
        simp [intervals, intervalFn, h1] <;> aesop
      have h_len : (intervals.interval i).length = a i.val := by
        rw [h_eq, h_mk_len] <;> ring
      have h_short : (intervals.interval i).IsShort K := by
        have h : (intervals.interval i).length ≤ L_max := by
          rw [h_len]
          exact ha_le_Lmax i.val h1
        simpa [ParameterInterval.IsShort, hL_max_def] using h
      exact ⟨by rw [h_len]; exact ha_ge4rho i.val, h_short⟩
    · by_cases h2 : i.val < N + M
      · let j := i.val - N
        have h_j_lt_M : j < M := by omega
        have h_eq : intervals.interval i =
            mkParameterInterval ((j : ℝ) * l_max)
              ((j : ℝ) * l_max + L_max)
              (by positivity) (by linarith)
              (h_j_in_bounds j h_j_lt_M) := by
          simp [intervals, intervalFn, h1, h2, j] <;> aesop
        have h_len : (intervals.interval i).length = L_max := by
          rw [h_eq, h_mk_len] <;> ring
        have h_short : (intervals.interval i).IsShort K := by
          have h :
              (intervals.interval i).length ≤ L_max :=
            le_of_eq h_len
          simpa [ParameterInterval.IsShort, hL_max_def] using h
        exact ⟨by rw [h_len]; linarith [h4rho_le], h_short⟩
      · by_cases h3 : i.val = N + M
        · have h_eq : intervals.interval i =
              mkParameterInterval (1 - L_max) 1
                (by linarith) (by linarith) (by norm_num) := by
            simp [intervals, intervalFn, h1, h2, h3] <;> aesop
          have h_len : (intervals.interval i).length = L_max := by
            rw [h_eq, h_mk_len] <;> ring
          have h_short : (intervals.interval i).IsShort K := by
            have h :
                (intervals.interval i).length ≤ L_max :=
              le_of_eq h_len
            simpa [ParameterInterval.IsShort, hL_max_def] using h
          exact ⟨by rw [h_len]; linarith [h4rho_le], h_short⟩
        · let k := i.val - (N + M + 1)
          have h_k_lt_N : k < N := by omega
          have h_ale : a k ≤ L_max :=
            ha_le_Lmax k h_k_lt_N
          have h_nonneg : 0 ≤ a k := (ha_pos k).le
          have h_lt1 : a k < 1 := by
            linarith [hL_max_lt_one, h_ale]
          have h_left0 : 0 ≤ 1 - a k := by linarith
          have h_le1 : 1 - a k ≤ 1 := by linarith
          have h_eq : intervals.interval i =
              mkParameterInterval (1 - a k) 1 h_left0 h_le1
                (by norm_num) := by
            simp [intervals, intervalFn, h1, h2, h3, k] <;> aesop
          have h_len : (intervals.interval i).length = a k := by
            rw [h_eq, h_mk_len] <;> ring
          have h_short : (intervals.interval i).IsShort K := by
            have h :
                (intervals.interval i).length ≤ L_max := by
              rw [h_len]
              exact h_ale
            simpa [ParameterInterval.IsShort, hL_max_def] using h
          exact ⟨by rw [h_len]; exact ha_ge4rho k, h_short⟩
  have hN_bound :
      (N : ℝ) ≤ 1 + |Real.log rho| / Real.log (17 / 15) :=
    geom_steps_log_bound rho L_max N hrho hrho_le24
      hL_max_pos hL_max_le hN_pred
  have h_card :
      (intervals.card : ℝ) ≤
        C_cover * (|Real.log rho| + 1) := by
    have h_card_eq :
        (intervals.card : ℝ) = (2 * N + M + 1 : ℝ) := by
      simp [intervals, total] <;> norm_cast
    rw [h_card_eq]
    set L : ℝ := |Real.log rho| with hL_def
    set R : ℝ := Real.log (17 / 15) with hR_def
    have hR_pos : 0 < R := h_log_pos
    have hL_nonneg : 0 ≤ L := by positivity
    have h_ineq1 :
        (2 * N + M + 1 : ℝ) ≤
          2 * (1 + L / R) + (96 * K + 1) + 1 := by
      have hN' : (N : ℝ) ≤ 1 + L / R := by
        simpa [hL_def, hR_def] using hN_bound
      have hM' : (M : ℝ) < 96 * K + 1 := hM_bound
      linarith
    have h_ineq2 :
        2 * (1 + L / R) + (96 * K + 1) + 1 ≤
          C_cover * (L + 1) := by
      dsimp only [C_cover]
      have h5 : 0 ≤ 96 * K * L := by positivity
      have h6 : 0 ≤ 4 * L := by positivity
      have h7 : 0 ≤ 2 / R := by positivity
      have h8 :
          2 * (1 + L / R) + (96 * K + 1) + 1 =
            2 * L / R + 96 * K + 4 := by
        field_simp [hR_pos.ne'] <;> ring
      rw [h8]
      have h9 :
          (2 / R + 96 * K + 4) * (L + 1) =
            2 * L / R + 2 / R + 96 * K * L +
              96 * K + 4 * L + 4 := by
        field_simp [hR_pos.ne'] <;> ring
      rw [h9]
      linarith
    linarith
  have h_left_six : ∀ (i : Fin total) (h : i.val < N),
      (intervals.interval i).realCenteredCarrier (1 / 16) =
        Set.Icc (15 * a i.val / 32)
          (17 * a i.val / 32) := by
    intro i h
    have h_eq : intervals.interval i =
        mkParameterInterval 0 (a i.val) (by norm_num)
          (ha_pos i.val).le
          (by linarith [hL_max_le, ha_le_Lmax i.val h]) := by
      simp [intervals, intervalFn, h] <;> aesop
    rw [h_eq]
    have h_a1 : a i.val ≤ 1 := by
      linarith [hL_max_le, ha_le_Lmax i.val h]
    exact left_interval_sixteenth
      (a i.val) (ha_pos i.val).le h_a1
  have h_mid_six : ∀ (i : Fin total)
      (h1 : ¬i.val < N) (h2 : i.val < N + M),
      (intervals.interval i).realCenteredCarrier (1 / 16) =
        Set.Icc
          (((i.val - N : ℕ) : ℝ) * l_max + 15 * L_max / 32)
          (((i.val - N : ℕ) : ℝ) * l_max + 17 * L_max / 32) := by
    intro i h1 h2
    let j := i.val - N
    have h_j_lt_M : j < M := by omega
    have h_eq : intervals.interval i =
        mkParameterInterval ((j : ℝ) * l_max)
          ((j : ℝ) * l_max + L_max)
          (by positivity) (by linarith)
          (h_j_in_bounds j h_j_lt_M) := by
      simp [intervals, intervalFn, h1, h2, j] <;> aesop
    rw [h_eq]
    exact middle_interval_sixteenth
      ((j : ℝ) * l_max) L_max (by positivity)
      (h_j_in_bounds j h_j_lt_M) (by positivity)
  have h_extra_six : ∀ (i : Fin total)
      (h1 : ¬i.val < N) (h2 : ¬i.val < N + M)
      (h3 : i.val = N + M),
      (intervals.interval i).realCenteredCarrier (1 / 16) =
        Set.Icc (1 - 17 * L_max / 32)
          (1 - 15 * L_max / 32) := by
    intro i h1 h2 h3
    have h_eq : intervals.interval i =
        mkParameterInterval (1 - L_max) 1
          (by linarith) (by linarith) (by norm_num) := by
      simp [intervals, intervalFn, h1, h2, h3] <;> aesop
    rw [h_eq]
    exact right_interval_sixteenth
      L_max (by positivity) hL_max_le
  have h_right_six : ∀ (i : Fin total)
      (h1 : ¬i.val < N) (h2 : ¬i.val < N + M)
      (h3 : ¬i.val = N + M),
      (intervals.interval i).realCenteredCarrier (1 / 16) =
        Set.Icc
          (1 - 17 * a (i.val - (N + M + 1)) / 32)
          (1 - 15 * a (i.val - (N + M + 1)) / 32) := by
    intro i h1 h2 h3
    let k := i.val - (N + M + 1)
    have h_k_lt_N : k < N := by omega
    have h_ale : a k ≤ L_max := ha_le_Lmax k h_k_lt_N
    have h_nonneg : 0 ≤ a k := (ha_pos k).le
    have h_lt1 : a k < 1 := by
      linarith [hL_max_lt_one, h_ale]
    have h_left0 : 0 ≤ 1 - a k := by linarith
    have h_le1 : 1 - a k ≤ 1 := by linarith
    have h_eq : intervals.interval i =
        mkParameterInterval (1 - a k) 1 h_left0 h_le1
          (by norm_num) := by
      simp [intervals, intervalFn, h1, h2, h3, k] <;> aesop
    rw [h_eq]
    have h_a1 : a k ≤ 1 := by
      linarith [hL_max_le, h_ale]
    exact right_interval_sixteenth
      (a k) (ha_pos k).le h_a1
  have h_left_idx : ∀ (k : Fin N), (k.val : ℕ) < total := by
    intro k
    omega
  have h_mid_idx :
      ∀ (j : Fin M), N + (j.val : ℕ) < total := by
    intro j
    omega
  have h_extra_idx : N + M < total := by omega
  have h_right_idx :
      ∀ (k : Fin N), N + M + 1 + (k.val : ℕ) < total := by
    intro k
    omega
  have h_coverage :
      Set.Icc (2 * rho) (1 - 2 * rho) ⊆
        ⋃ i, (intervals.interval i).realCenteredCarrier (1 / 16) := by
    intro x hx
    have h_x_ge : 15 * rho / 8 ≤ x := by linarith [hx.1]
    have h_x_le : x ≤ 1 - 15 * rho / 8 := by linarith [hx.2]
    have h_a0 : a 0 = 4 * rho := by
      simp [a, geomLength] <;> ring
    by_cases h_case1 : x ≤ 17 * a (N - 1) / 32
    · have h_in :
          x ∈ Set.Icc (15 * a 0 / 32)
            (17 * a (N - 1) / 32) := by
        have h_left_endpoint :
            15 * a 0 / 32 = 15 * rho / 8 := by
          rw [h_a0] <;> ring
        rw [h_left_endpoint]
        exact ⟨h_x_ge, h_case1⟩
      have h_cover :=
        geometric_left_cover_fin a N hN_pos
          (sixteenth_tiling rho)
      have h4 :
          x ∈ ⋃ k : Fin N,
            Set.Icc (15 * a k / 32) (17 * a k / 32) :=
        h_cover h_in
      rcases mem_iUnion.mp h4 with ⟨k, hk⟩
      let i : Fin total := ⟨k.val, h_left_idx k⟩
      have h_i_val : i.val = k.val := by rfl
      have h_i_lt_N : i.val < N := by
        rw [h_i_val]
        exact k.is_lt
      have h5 :
          x ∈ (intervals.interval i).realCenteredCarrier
            (1 / 16) := by
        rw [h_left_six i h_i_lt_N]
        exact hk
      exact mem_iUnion.mpr ⟨i, h5⟩
    · have h_gt1 : x > 17 * a (N - 1) / 32 := by linarith
      have h_overlap1 :
          17 * a (N - 1) / 32 > 15 * L_max / 32 := by
        linarith [h17_15]
      by_cases h_case2 : x ≤ 1 - 17 * L_max / 32
      · have h_mid_ge : 15 * L_max / 32 ≤ x := by linarith
        have h_in :
            x ∈ Set.Icc (15 * L_max / 32)
              (15 * L_max / 32 + (M : ℝ) * l_max) := by
          have h6 :
              15 * L_max / 32 + (M : ℝ) * l_max ≥
                1 - 17 * L_max / 32 := by
            have h7 : (M : ℝ) * l_max ≥ 1 - L_max := hM
            linarith
          exact ⟨h_mid_ge, by linarith⟩
        have h_cover :=
          union_tiling_cover
            (15 * L_max / 32) l_max M hM_pos (by positivity)
        have h4 :
            x ∈ ⋃ j : Fin M,
              Set.Icc
                (15 * L_max / 32 + (j : ℝ) * l_max)
                (15 * L_max / 32 + ((j : ℝ) + 1) * l_max) :=
          h_cover h_in
        rcases mem_iUnion.mp h4 with ⟨j, hj⟩
        let i : Fin total := ⟨N + j.val, h_mid_idx j⟩
        have h_i_val : i.val = N + j.val := by rfl
        have h_i_ge_N : ¬i.val < N := by
          rw [h_i_val]
          omega
        have h_i_lt_NM : i.val < N + M := by
          rw [h_i_val]
          omega
        have h5 :
            x ∈ (intervals.interval i).realCenteredCarrier
              (1 / 16) := by
          rw [h_mid_six i h_i_ge_N h_i_lt_NM]
          have h_j_eq : (i.val - N : ℕ) = j.val := by
            rw [h_i_val]
            omega
          rw [h_j_eq]
          have h_goal :
              x ∈ Set.Icc
                (((j.val : ℝ) * l_max + 15 * L_max / 32))
                (((j.val : ℝ) * l_max + 17 * L_max / 32)) := by
            have h_eq1 :
                (j.val : ℝ) * l_max + 15 * L_max / 32 =
                  15 * L_max / 32 + (j.val : ℝ) * l_max := by
              ring
            have h_eq2 :
                (j.val : ℝ) * l_max + 17 * L_max / 32 =
                  15 * L_max / 32 +
                    ((j.val : ℝ) + 1) * l_max := by
              rw [hl_max_def] <;> ring
            rw [h_eq1, h_eq2]
            exact hj
          exact h_goal
        exact mem_iUnion.mpr ⟨i, h5⟩
      · have h_gt2 : x > 1 - 17 * L_max / 32 := by linarith
        by_cases h_case3 : x ≤ 1 - 15 * L_max / 32
        · have h_in :
              x ∈ Set.Icc
                (1 - 17 * L_max / 32)
                (1 - 15 * L_max / 32) :=
            ⟨by linarith, h_case3⟩
          let i : Fin total := ⟨N + M, h_extra_idx⟩
          have h_i_val : i.val = N + M := by rfl
          have h_i_ge_N : ¬i.val < N := by
            rw [h_i_val]
            omega
          have h_i_ge_NM : ¬i.val < N + M := by
            rw [h_i_val]
            omega
          have h_i_eq : i.val = N + M := h_i_val
          have h5 :
              x ∈ (intervals.interval i).realCenteredCarrier
                (1 / 16) := by
            rw [h_extra_six i h_i_ge_N h_i_ge_NM h_i_eq]
            exact h_in
          exact mem_iUnion.mpr ⟨i, h5⟩
        · have h_gt3 : x > 1 - 15 * L_max / 32 := by linarith
          have h_right_ge :
              1 - 17 * a (N - 1) / 32 ≤ x := by
            linarith [h17_15]
          have h_in :
              x ∈ Set.Icc
                (1 - 17 * a (N - 1) / 32)
                (1 - 15 * a 0 / 32) := by
            have h_right_endpoint :
                15 * a 0 / 32 = 15 * rho / 8 := by
              rw [h_a0] <;> ring
            rw [h_right_endpoint]
            exact ⟨h_right_ge, h_x_le⟩
          have h_cover :=
            geometric_right_cover_fin a N hN_pos
              (sixteenth_tiling rho)
          have h4 :
              x ∈ ⋃ k : Fin N,
                Set.Icc
                  (1 - 17 * a k / 32)
                  (1 - 15 * a k / 32) :=
            h_cover h_in
          rcases mem_iUnion.mp h4 with ⟨k, hk⟩
          let i : Fin total :=
            ⟨N + M + 1 + k.val, h_right_idx k⟩
          have h_i_val :
              i.val = N + M + 1 + k.val := by rfl
          have h_i_ge_N : ¬i.val < N := by
            rw [h_i_val]
            omega
          have h_i_ge_NM : ¬i.val < N + M := by
            rw [h_i_val]
            omega
          have h_i_neq : ¬i.val = N + M := by
            rw [h_i_val]
            omega
          have h5 :
              x ∈ (intervals.interval i).realCenteredCarrier
                (1 / 16) := by
            rw [h_right_six i h_i_ge_N h_i_ge_NM h_i_neq]
            have h_k_eq :
                (i.val - (N + M + 1) : ℕ) = k.val := by
              rw [h_i_val]
              omega
            rw [h_k_eq]
            exact hk
          exact mem_iUnion.mpr ⟨i, h5⟩

  exact ⟨intervals, h_total_pos, h_branch_prop, h_card, h_coverage⟩

end Kakeya.Cinematic
