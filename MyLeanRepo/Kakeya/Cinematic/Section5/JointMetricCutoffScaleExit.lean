import MyLeanRepo.Kakeya.Cinematic.Section5.JointMetricCutoffScaleExitInputs

namespace Kakeya.Cinematic

theorem joint_metric_cutoff_scale_exit :
    JointMetricCutoffScaleExitStatement := by
  dsimp only [JointMetricCutoffScaleExitStatement]
  intro K B te e hK hB hte he heQ h8
  set C1 : ℝ := 96 * (960 * K) ^ e * 2 ^ (e ^ 2) with hC1_def
  set C2 : ℝ := 4 * (B + 1) * 2 ^ (e ^ 2) * (8 * K) ^ e with hC2_def
  set alpha : ℝ := e * (2 - e) / (1 - e) with halpha_def
  set gamma : ℝ := 2 * te / 3 - alpha with hgamma_def
  set C3 : ℝ := C2 * C1 ^ (1 / (e * (1 - e))) with hC3_def
  set delta₀ : ℝ := min 1 (C3 ^ (-1 / gamma)) with hdelta₀_def

  have h1me : 0 < 1 - e := by linarith
  have he1e : 0 < e * (1 - e) := by positivity
  have hC1_pos : 0 < C1 := by positivity
  have hC2_pos : 0 < C2 := by positivity

  have halpha_le : alpha ≤ 7 * e / 3 := by
    rw [halpha_def]
    have h_pos : 0 < 1 - e := h1me
    have h1 : 3 * (2 - e) ≤ 7 * (1 - e) := by linarith
    have h2 : (2 - e) / (1 - e) ≤ 7 / 3 := by
      calc
        (2 - e) / (1 - e)
          = (3 * (2 - e)) / (3 * (1 - e)) := by field_simp [h_pos.ne'] <;> ring
        _ ≤ (7 * (1 - e)) / (3 * (1 - e)) := by
          gcongr
          <;> linarith
        _ = 7 / 3 := by field_simp [h_pos.ne'] <;> ring
    have h3 : e * ((2 - e) / (1 - e)) ≤ e * (7 / 3 : ℝ) :=
      mul_le_mul_of_nonneg_left h2 (by linarith)
    have h4 : e * ((2 - e) / (1 - e)) = e * (2 - e) / (1 - e) := by ring
    rw [h4] at h3
    have h5 : e * (7 / 3 : ℝ) = 7 * e / 3 := by ring
    rw [h5] at h3
    exact h3

  have h16e3 : 16 * e / 3 ≤ 2 * te / 3 := by linarith
  have halpha_lt : alpha < 2 * te / 3 := by
    calc
      alpha ≤ 7 * e / 3 := halpha_le
      _ < 16 * e / 3 := by linarith
      _ ≤ 2 * te / 3 := h16e3

  have hgamma_pos : 0 < gamma := by
    rw [hgamma_def]
    linarith

  have hC3_pos : 0 < C3 := by positivity

  have hdelta₀_pos : 0 < delta₀ := by
    rw [hdelta₀_def]
    positivity

  have hdelta₀_one : delta₀ ≤ 1 := by
    rw [hdelta₀_def]
    exact min_le_left _ _

  refine ⟨delta₀, hdelta₀_pos, hdelta₀_one, ?_⟩
  intro delta t Delta H F tangencyExponent mu q
    hdelta hdelta₀' hdeltaDelta hDeltaT htK hmu htangency hH1 hH hF hq hret hmetric

  subst htangency

  set x : ℝ := t / delta with hx_def

  have ht_pos : 0 < t := by linarith
  have hD_pos : 0 < Delta := by linarith
  have hx_pos : 0 < x := by
    rw [hx_def]
    positivity
  have hx_one : 1 ≤ x := by
    rw [hx_def]
    have h : delta ≤ t := by linarith
    have h2 : 1 ≤ t / delta := by
      rw [one_le_div hdelta]
      <;> linarith
    exact h2

  -- ===== Step 1: Metric cutoff =====
  have hF_pos : 0 < F := by
    rw [hF]
    have hpos : 0 < 2 * t / Delta := by positivity
    have h : 0 < (2 * t / Delta) ^ (e ^ 2) := Real.rpow_pos_of_pos hpos _
    positivity
  have hH_pos : 0 < H := by linarith

  have h14 : (1 / (24 * H * F)) ^ (1 / e) < 960 * K / x := by
    have h : (1 / 2 : ℝ) * (1 / (24 * H * F)) ^ (1 / e) * t < 480 * K * delta := hmetric
    have h2 : (1 / (24 * H * F)) ^ (1 / e) * t < 960 * K * delta := by linarith
    have h3 : (1 / (24 * H * F)) ^ (1 / e) < 960 * K * delta / t := by
      calc
        (1 / (24 * H * F)) ^ (1 / e)
          = ((1 / (24 * H * F)) ^ (1 / e) * t) / t := by field_simp [ht_pos.ne'] <;> ring
        _ < (960 * K * delta) / t := by gcongr
    have h_eq : 960 * K * delta / t = 960 * K / x := by
      rw [hx_def]
      field_simp [hdelta.ne', ht_pos.ne'] <;> ring
    rw [h_eq] at h3
    exact h3

  have h15 : 1 / (24 * H * F) < (960 * K / x) ^ e := by
    set a : ℝ := 1 / (24 * H * F) with ha_def
    set b : ℝ := 960 * K / x with hb_def
    have ha_pos : 0 < a := by positivity
    have hb_pos : 0 < b := by positivity
    have h : a ^ (1 / e) < b := h14
    have h_pos_a : 0 ≤ a ^ (1 / e) := by positivity
    have h2 : (a ^ (1 / e)) ^ e < b ^ e := Real.rpow_lt_rpow h_pos_a h he
    have h3 : (a ^ (1 / e)) ^ e = a := by
      have h4 : (a ^ (1 / e)) ^ e = a ^ ((1 / e) * e) := by
        rw [← Real.rpow_mul ha_pos.le]
        <;> ring
      rw [h4]
      have h5 : (1 / e) * e = 1 := by field_simp [he.ne'] <;> ring
      rw [h5]
      simp
    rw [h3] at h2
    exact h2

  have h16 : x ^ e < 24 * H * F * (960 * K) ^ e := by
    have h_pos1 : 0 < 1 / (24 * H * F) := by positivity
    have h_pos3 : 0 < x ^ e := by positivity
    have h_pos4 : 0 < (960 * K) ^ e := by positivity
    have h_div : (960 * K / x) ^ e = (960 * K) ^ e / x ^ e := by
      rw [Real.div_rpow (by positivity) (by positivity)]
    rw [h_div] at h15
    have h : 1 / (24 * H * F) < (960 * K) ^ e / x ^ e := h15
    calc
      x ^ e
        = (1 / (24 * H * F)) * (24 * H * F) * x ^ e := by
          field_simp [h_pos1.ne'] <;> ring
      _ < ((960 * K) ^ e / x ^ e) * (24 * H * F) * x ^ e := by gcongr
      _ = 24 * H * F * (960 * K) ^ e := by
        field_simp [h_pos3.ne'] <;> ring

  have h17 : F ≤ 4 * (2 * x) ^ (e ^ 2) := by
    rw [hF]
    have h : 2 * t / Delta ≤ 2 * x := by
      rw [hx_def]
      have h' : 1 / Delta ≤ 1 / delta := by
        exact one_div_le_one_div_of_le (by linarith) hdeltaDelta
      calc
        2 * t / Delta = 2 * t * (1 / Delta) := by ring
        _ ≤ 2 * t * (1 / delta) := by gcongr
        _ = 2 * (t / delta) := by ring
        _ = 2 * x := by rw [hx_def]
    have hpos : 0 < 2 * t / Delta := by positivity
    have h' : (2 * t / Delta) ^ (e ^ 2) ≤ (2 * x) ^ (e ^ 2) :=
      Real.rpow_le_rpow hpos.le h (by positivity)
    gcongr
    exact h'

  have h18 : 24 * H * F ≤ 96 * delta ^ (-(e ^ 2)) * (2 * x) ^ (e ^ 2) := by
    have hH' : H ≤ delta ^ (-(e ^ 2)) := hH
    have hH24 : 24 * H ≤ 24 * delta ^ (-(e ^ 2)) := by gcongr
    calc
      24 * H * F
        ≤ (24 * delta ^ (-(e ^ 2))) * F := by
          exact mul_le_mul_of_nonneg_right hH24 (by positivity)
        _ ≤ (24 * delta ^ (-(e ^ 2))) * (4 * (2 * x) ^ (e ^ 2)) := by gcongr
        _ = 96 * delta ^ (-(e ^ 2)) * (2 * x) ^ (e ^ 2) := by ring

  have h19 : x ^ e < 96 * delta ^ (-(e ^ 2)) * (2 * x) ^ (e ^ 2) * (960 * K) ^ e := by
    calc
      x ^ e < 24 * H * F * (960 * K) ^ e := h16
      _ ≤ (96 * delta ^ (-(e ^ 2)) * (2 * x) ^ (e ^ 2)) * (960 * K) ^ e := by gcongr
      _ = 96 * delta ^ (-(e ^ 2)) * (2 * x) ^ (e ^ 2) * (960 * K) ^ e := by ring

  have h20 : (2 * x) ^ (e ^ 2) = 2 ^ (e ^ 2) * x ^ (e ^ 2) := by
    rw [Real.mul_rpow (by positivity) (by positivity)]

  have h_step1 : x ^ (e * (1 - e)) < C1 * delta ^ (-(e ^ 2)) := by
    rw [h20] at h19
    set y : ℝ := x ^ (e ^ 2) with hy_def
    have hy_pos : 0 < y := by positivity
    have h : x ^ e < 96 * delta ^ (-(e ^ 2)) * (2 ^ (e ^ 2) * y) * (960 * K) ^ e := h19
    have h' : x ^ e / y < 96 * delta ^ (-(e ^ 2)) * 2 ^ (e ^ 2) * (960 * K) ^ e := by
      calc
        x ^ e / y
          < (96 * delta ^ (-(e ^ 2)) * (2 ^ (e ^ 2) * y) * (960 * K) ^ e) / y := by gcongr
        _ = 96 * delta ^ (-(e ^ 2)) * 2 ^ (e ^ 2) * (960 * K) ^ e := by
          field_simp [hy_pos.ne'] <;> ring
    have h_div2 : x ^ e / y = x ^ (e - e ^ 2) := by
      have h_add : x ^ (e - e ^ 2) * y = x ^ e := by
        simp only [hy_def]
        rw [← Real.rpow_add hx_pos]
        <;> ring_nf
      have h : x ^ e / y = x ^ (e - e ^ 2) := by
        rw [← h_add]
        field_simp [hy_pos.ne'] <;> ring
      exact h
    rw [h_div2] at h'
    have h_eq : e - e ^ 2 = e * (1 - e) := by ring
    rw [h_eq] at h'
    have hC1_eq : C1 = 96 * (960 * K) ^ e * 2 ^ (e ^ 2) := by
      simp [hC1_def] <;> ring
    rw [hC1_eq]
    <;> linarith

  -- ===== Step 2: x bound =====
  set p : ℝ := 1 / (e * (1 - e)) with hp_def
  have hp_pos : 0 < p := by positivity

  have h_step2 : x < C1 ^ p * delta ^ (-e / (1 - e)) := by
    have h1 : (x ^ (e * (1 - e))) ^ p < (C1 * delta ^ (-(e ^ 2))) ^ p :=
      Real.rpow_lt_rpow (by positivity) h_step1 hp_pos
    have h2 : (x ^ (e * (1 - e))) ^ p = x := by
      have h21 : (x ^ (e * (1 - e))) ^ p = x ^ ((e * (1 - e)) * p) :=
        (Real.rpow_mul hx_pos.le (e * (1 - e)) p).symm
      rw [h21]
      have h3 : (e * (1 - e)) * p = 1 := by
        rw [hp_def]
        field_simp [he1e.ne'] <;> ring
      rw [h3]
      simp
    have h4 : (C1 * delta ^ (-(e ^ 2))) ^ p = C1 ^ p * (delta ^ (-(e ^ 2))) ^ p := by
      rw [Real.mul_rpow (by positivity) (by positivity)]
    have h5 : (delta ^ (-(e ^ 2))) ^ p = delta ^ (-e / (1 - e)) := by
      have h51 : (delta ^ (-(e ^ 2))) ^ p = delta ^ ((-(e ^ 2)) * p) :=
        (Real.rpow_mul hdelta.le (-(e ^ 2)) p).symm
      rw [h51]
      have h6 : (-(e ^ 2)) * p = -e / (1 - e) := by
        rw [hp_def]
        field_simp [he1e.ne'] <;> ring
      rw [h6]
    rw [h2, h4, h5] at h1
    exact h1

  -- ===== Step 3: Joint retention =====
  have h31 : Delta / (2 * t) ≥ 1 / (2 * x) := by
    rw [hx_def]
    have h : Delta / (2 * t) ≥ delta / (2 * t) := by gcongr
    have h2 : delta / (2 * t) = 1 / (2 * (t / delta)) := by
      field_simp [hdelta.ne', ht_pos.ne'] <;> ring
    rw [h2] at h
    exact h

  have h32 : (Delta / (2 * t)) ^ (e ^ 2) ≥ (1 / (2 * x)) ^ (e ^ 2) := by
    have hpos1 : 0 < Delta / (2 * t) := by positivity
    have hpos2 : 0 < 1 / (2 * x) := by positivity
    exact Real.rpow_le_rpow hpos2.le h31 (by positivity)

  have h33 : (t / (8 * K)) ^ e * (1 / (2 * x)) ^ (e ^ 2) * (mu : ℝ) < 4 * ((q : ℝ) + 1) := by
    have h : (t / (8 * K)) ^ e * (1 / (2 * x)) ^ (e ^ 2) * (mu : ℝ) ≤
             (t / (8 * K)) ^ e * (Delta / (2 * t)) ^ (e ^ 2) * (mu : ℝ) := by
      gcongr
      <;> positivity
    exact h.trans_lt hret

  have h_8Kt : (8 * K / t) ^ e = (8 * K) ^ e * x ^ (-e) * delta ^ (-e) := by
    have h_eq1 : 8 * K / t = (8 * K) * (x * delta)⁻¹ := by
      rw [hx_def]
      field_simp [hdelta.ne', ht_pos.ne'] <;> ring
    rw [h_eq1]
    have h : ((8 * K) * (x * delta)⁻¹) ^ e = (8 * K) ^ e * ((x * delta)⁻¹) ^ e := by
      rw [Real.mul_rpow (by positivity) (by positivity)]
    rw [h]
    have h2 : ((x * delta)⁻¹) ^ e = (x * delta) ^ (-e) := by
      have hpos : 0 ≤ x * delta := by positivity
      rw [Real.inv_rpow hpos e, Real.rpow_neg hpos]
    rw [h2]
    have h3 : (x * delta) ^ (-e) = x ^ (-e) * delta ^ (-e) := by
      rw [Real.mul_rpow (by positivity) (by positivity)]
    rw [h3] <;> ring

  have h_2x : (2 * x) ^ (e ^ 2) = 2 ^ (e ^ 2) * x ^ (e ^ 2) := by
    rw [Real.mul_rpow (by positivity) (by positivity)]

  have h_e_le_one : e ≤ 1 := by linarith
  have h_esq_le_e : e ^ 2 ≤ e := by
    calc
      e ^ 2 = e * e := by ring
      _ ≤ e * 1 := by gcongr <;> linarith
      _ = e := by ring
  have h_exp_nonpos : e ^ 2 - e ≤ 0 := by linarith
  have h_xpow : x ^ (e ^ 2 - e) ≤ 1 := by
    have h : x ^ (e ^ 2 - e) ≤ x ^ (0 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hx_one h_exp_nonpos
    have h0 : x ^ (0 : ℝ) = 1 := Real.rpow_zero x
    rw [h0] at h
    exact h

  have h_q : (q : ℝ) + 1 ≤ (B + 1) * x := by
    calc
      (q : ℝ) + 1 ≤ B * x + 1 := by linarith [hq]
      _ ≤ B * x + x := by gcongr <;> linarith
      _ = (B + 1) * x := by ring

  have h_step3 : (mu : ℝ) < C2 * x * delta ^ (-e) := by
    have hpos1 : 0 < (t / (8 * K)) ^ e := by positivity
    have hpos2 : 0 < (1 / (2 * x)) ^ (e ^ 2) := by positivity
    have hpos3 : 0 < (mu : ℝ) := by exact_mod_cast hmu
    have h_isolate : (mu : ℝ) < 4 * ((q : ℝ) + 1) * ((t / (8 * K)) ^ e)⁻¹ * ((1 / (2 * x)) ^ (e ^ 2))⁻¹ := by
      calc
        (mu : ℝ)
          = ((t / (8 * K)) ^ e * (1 / (2 * x)) ^ (e ^ 2))⁻¹ * (((t / (8 * K)) ^ e * (1 / (2 * x)) ^ (e ^ 2)) * (mu : ℝ)) := by
            field_simp [hpos1.ne', hpos2.ne'] <;> ring
        _ < ((t / (8 * K)) ^ e * (1 / (2 * x)) ^ (e ^ 2))⁻¹ * (4 * ((q : ℝ) + 1)) := by gcongr
        _ = 4 * ((q : ℝ) + 1) * ((t / (8 * K)) ^ e)⁻¹ * ((1 / (2 * x)) ^ (e ^ 2))⁻¹ := by ring
    have h_inv1 : ((t / (8 * K)) ^ e)⁻¹ = (8 * K / t) ^ e := by
      have hpos : 0 ≤ t / (8 * K) := by positivity
      have h : ((t / (8 * K)) ^ e)⁻¹ = (t / (8 * K))⁻¹ ^ e := (Real.inv_rpow hpos e).symm
      rw [h]
      have h2 : (t / (8 * K))⁻¹ = 8 * K / t := by
        field_simp [ht_pos.ne'] <;> ring
      rw [h2]
    have h_inv2 : ((1 / (2 * x)) ^ (e ^ 2))⁻¹ = (2 * x) ^ (e ^ 2) := by
      have hpos : 0 ≤ 1 / (2 * x) := by positivity
      have h : ((1 / (2 * x)) ^ (e ^ 2))⁻¹ = (1 / (2 * x))⁻¹ ^ (e ^ 2) := (Real.inv_rpow hpos (e ^ 2)).symm
      rw [h]
      have h2 : (1 / (2 * x))⁻¹ = 2 * x := by
        field_simp [hx_pos.ne'] <;> ring
      rw [h2]
    rw [h_inv1, h_inv2] at h_isolate
    rw [h_8Kt, h_2x] at h_isolate
    set P : ℝ := 2 ^ (e ^ 2) * (8 * K) ^ e * delta ^ (-e) with hP_def
    have hP_pos : 0 < P := by positivity
    have h_main : (mu : ℝ) < 4 * ((q : ℝ) + 1) * x ^ (e ^ 2 - e) * P := by
      have hc : x ^ (-e) * x ^ (e ^ 2) = x ^ (e ^ 2 - e) := by
        rw [← Real.rpow_add hx_pos] <;> ring_nf
      have h_expand : 4 * ((q : ℝ) + 1) * ((8 * K) ^ e * x ^ (-e) * delta ^ (-e)) * (2 ^ (e ^ 2) * x ^ (e ^ 2)) =
                        4 * ((q : ℝ) + 1) * (x ^ (-e) * x ^ (e ^ 2)) * P := by
        simp [hP_def] <;> ring
      rw [h_expand, hc] at h_isolate
      exact h_isolate
    have h_bound : 4 * ((q : ℝ) + 1) * x ^ (e ^ 2 - e) ≤ 4 * ((B + 1) * x) := by
      have h1 : x ^ (e ^ 2 - e) ≤ 1 := h_xpow
      have h2 : 0 ≤ 4 * ((q : ℝ) + 1) := by positivity
      have h3 : 4 * ((q : ℝ) + 1) * x ^ (e ^ 2 - e) ≤ 4 * ((q : ℝ) + 1) := by
        calc
          4 * ((q : ℝ) + 1) * x ^ (e ^ 2 - e) ≤ 4 * ((q : ℝ) + 1) * 1 := by gcongr
          _ = 4 * ((q : ℝ) + 1) := by ring
      have h4 : 4 * ((q : ℝ) + 1) ≤ 4 * ((B + 1) * x) := by
        gcongr
      exact h3.trans h4
    have h_final : (mu : ℝ) < 4 * ((B + 1) * x) * P := by
      calc
        (mu : ℝ) < 4 * ((q : ℝ) + 1) * x ^ (e ^ 2 - e) * P := h_main
        _ ≤ (4 * ((B + 1) * x)) * P := by
          gcongr
          <;> linarith
    have h_goal : 4 * ((B + 1) * x) * P = C2 * x * delta ^ (-e) := by
      simp [hP_def, hC2_def] <;> ring
    rw [h_goal] at h_final
    exact h_final

  -- ===== Step 4: Combine =====
  have h_step4 : (mu : ℝ) < C3 * delta ^ (-alpha) := by
    have h1 : (mu : ℝ) < C2 * (C1 ^ p * delta ^ (-e / (1 - e))) * delta ^ (-e) := by
      calc
        (mu : ℝ) < C2 * x * delta ^ (-e) := h_step3
        _ ≤ C2 * (C1 ^ p * delta ^ (-e / (1 - e))) * delta ^ (-e) := by gcongr
    have h_exp : delta ^ (-e / (1 - e)) * delta ^ (-e) = delta ^ (-alpha) := by
      rw [← Real.rpow_add hdelta]
      have h_eq : -e / (1 - e) + (-e) = -alpha := by
        rw [halpha_def]
        field_simp [h1me.ne'] <;> ring
      rw [h_eq]
    have h_final : C2 * (C1 ^ p * delta ^ (-e / (1 - e))) * delta ^ (-e) = C3 * delta ^ (-alpha) := by
      calc
        C2 * (C1 ^ p * delta ^ (-e / (1 - e))) * delta ^ (-e)
          = C2 * C1 ^ p * (delta ^ (-e / (1 - e)) * delta ^ (-e)) := by ring
        _ = C2 * C1 ^ p * delta ^ (-alpha) := by rw [h_exp]
        _ = C3 * delta ^ (-alpha) := by
          have hC3_eq : C3 = C2 * C1 ^ p := by
            simp [hC3_def, hp_def] <;> ring
          rw [hC3_eq] <;> ring
    rw [h_final] at h1
    exact h1

  -- ===== Step 5: delta₀ inequality =====
  have h51 : delta ≤ C3 ^ (-1 / gamma) := by
    have h : delta₀ ≤ C3 ^ (-1 / gamma) := by
      rw [hdelta₀_def]
      exact min_le_right _ _
    exact hdelta₀'.trans h

  have h_step5 : C3 * delta ^ (-alpha) ≤ delta ^ (-2 * te / 3) := by
    have h52 : delta ^ gamma ≤ (C3 ^ (-1 / gamma)) ^ gamma :=
      Real.rpow_le_rpow hdelta.le h51 hgamma_pos.le
    have h53 : (C3 ^ (-1 / gamma)) ^ gamma = C3 ^ (-1 : ℝ) := by
      have h531 : (C3 ^ (-1 / gamma)) ^ gamma = C3 ^ ((-1 / gamma) * gamma) :=
        (Real.rpow_mul hC3_pos.le (-1 / gamma) gamma).symm
      rw [h531]
      have h : (-1 / gamma) * gamma = -1 := by
        field_simp [hgamma_pos.ne'] <;> ring
      rw [h]
    have h54 : delta ^ gamma ≤ C3 ^ (-1 : ℝ) := by
      rw [h53] at h52
      exact h52
    have h_pos1 : 0 < delta ^ gamma := by positivity
    have h_pos2 : 0 < C3 ^ (-1 : ℝ) := by positivity
    have h55 : C3 ≤ delta ^ (-gamma) := by
      have h_nonneg : 0 ≤ delta ^ gamma := by positivity
      have h : (C3 ^ (-1 : ℝ))⁻¹ ≤ (delta ^ gamma)⁻¹ := by
        rw [inv_le_inv₀ h_pos2 h_pos1]
        exact h54
      have h6 : (delta ^ gamma)⁻¹ = delta ^ (-gamma) := by
        rw [Real.rpow_neg hdelta.le]
      have h71 : C3 ^ (-1 : ℝ) = C3⁻¹ := by
        rw [Real.rpow_neg hC3_pos.le, Real.rpow_one]
      have h7 : (C3 ^ (-1 : ℝ))⁻¹ = C3 := by
        rw [h71]
        field_simp [hC3_pos.ne']
      rw [h6, h7] at h
      exact h
    have h8 : C3 * delta ^ (-alpha) ≤ delta ^ (-gamma) * delta ^ (-alpha) := by
      gcongr <;> positivity
    have h9 : delta ^ (-gamma) * delta ^ (-alpha) = delta ^ (-2 * te / 3) := by
      rw [← Real.rpow_add hdelta]
      have h10 : -gamma + (-alpha) = -2 * te / 3 := by
        rw [hgamma_def] <;> ring
      rw [h10]
    rw [h9] at h8
    exact h8

  -- ===== Step 6 =====
  have h_step6 : (mu : ℝ) < delta ^ (-2 * te / 3) := by
    calc
      (mu : ℝ) < C3 * delta ^ (-alpha) := h_step4
      _ ≤ delta ^ (-2 * te / 3) := h_step5

  -- ===== Step 7: Final conclusion =====
  have hmu_real_pos : 0 < (mu : ℝ) := by exact_mod_cast hmu

  have h71 : (mu : ℝ) ^ (3 / 2 : ℝ) < (delta ^ (-2 * te / 3)) ^ (3 / 2 : ℝ) := by
    exact Real.rpow_lt_rpow hmu_real_pos.le h_step6 (by norm_num)

  have h72 : (delta ^ (-2 * te / 3)) ^ (3 / 2 : ℝ) = delta ^ (-te) := by
    have h721 : (delta ^ (-2 * te / 3)) ^ (3 / 2 : ℝ) = delta ^ ((-2 * te / 3) * (3 / 2 : ℝ)) :=
      (Real.rpow_mul hdelta.le (-2 * te / 3) (3 / 2 : ℝ)).symm
    rw [h721]
    have h : (-2 * te / 3) * (3 / 2 : ℝ) = -te := by ring
    rw [h]

  have h73 : (mu : ℝ) ^ (3 / 2 : ℝ) < delta ^ (-te) := by
    rw [h72] at h71
    exact h71

  have h74 : 0 < (mu : ℝ) ^ (3 / 2 : ℝ) := by positivity

  have h75 : 1 < delta ^ (-te) * (mu : ℝ) ^ (-3 / 2 : ℝ) := by
    have h_div : delta ^ (-te) / (mu : ℝ) ^ (3 / 2 : ℝ) = delta ^ (-te) * (mu : ℝ) ^ (-3 / 2 : ℝ) := by
      rw [div_eq_mul_inv]
      have h : ((mu : ℝ) ^ (3 / 2 : ℝ))⁻¹ = (mu : ℝ) ^ (-3 / 2 : ℝ) := by
        have h' : (mu : ℝ) ^ (-(3 / 2 : ℝ)) = ((mu : ℝ) ^ (3 / 2 : ℝ))⁻¹ :=
          Real.rpow_neg hmu_real_pos.le (3 / 2 : ℝ)
        have h_eq : (-(3 / 2 : ℝ)) = (-3 / 2 : ℝ) := by norm_num
        rw [h_eq] at h'
        exact h'.symm
      rw [h]
    have h : 1 < delta ^ (-te) / (mu : ℝ) ^ (3 / 2 : ℝ) := by
      calc
        1 = (mu : ℝ) ^ (3 / 2 : ℝ) / (mu : ℝ) ^ (3 / 2 : ℝ) := by
          field_simp [h74.ne'] <;> ring
        _ < delta ^ (-te) / (mu : ℝ) ^ (3 / 2 : ℝ) := by
          exact div_lt_div_of_pos_right h73 h74
    rw [h_div] at h
    exact h

  exact h75.le

end Kakeya.Cinematic
