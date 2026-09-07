import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ParameterWindowClusterCardinalityStatements
import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers

/-!
# Cardinality after a parameter window

The window density and parameter Frostman constant give the natural center
exponent `densityLoss + frostmanLoss - 1`. The positive gap to `targetLoss`
absorbs the logarithmic weighted-clustering regularization loss.
-/

namespace Kakeya.Assouad

/-- Product inverse in ENNReal for nonzero finite elements. -/
private lemma ennreal_inv_mul {a b : ENNReal}
    (ha0 : a ≠ 0) (hat : a ≠ ⊤) (_hb0 : b ≠ 0) (_hbt : b ≠ ⊤) :
    (a * b)⁻¹ = a⁻¹ * b⁻¹ :=
  ENNReal.mul_inv (Or.inl ha0) (Or.inl hat)

/-- Logarithmic bound on cluster regularization loss. -/
lemma cluster_regularization_loss_bound
    {delta densityLoss frostmanLoss : ℝ}
    (hdelta : 0 < delta) (hdelta_lt_one : delta < 1)
    (_hdensity_pos : 0 < densityLoss) (_hfrost_pos : 0 < frostmanLoss)
    (hsum_lt_one : densityLoss + frostmanLoss < 1)
    {C lambda R : ENNReal} {imbalance : ℕ}
    (_hR_one : 1 ≤ R) (hR_ne_top : R ≠ ⊤)
    (hC_pos : 0 < C) (hC_ne_top : C ≠ ⊤)
    (hlambda_pos : 0 < lambda) (hlambda_ne_top : lambda ≠ ⊤)
    (hC_le : C ≤ Kakeya.realRpowENN delta (-frostmanLoss))
    (hlambda_eq :
      lambda =
        ENNReal.ofReal (delta / 8) *
          Kakeya.realRpowENN delta densityLoss)
    (himbalance_pos : 0 < imbalance)
    (himbalance_bound : (imbalance : ENNReal) ≤
        1000000 * C * lambda⁻¹ *
          Kakeya.realRpowENN delta (-1) + 1)
    (hR_eq :
      R = 4 * (Nat.log 2 (2 * imbalance) + 1 : ENNReal)) :
    R ≤ ENNReal.ofReal (200 * (1 + Real.log delta⁻¹)) := by
  have hC_ne_zero : C ≠ 0 := hC_pos.ne'
  have hlambda_ne_zero : lambda ≠ 0 := hlambda_pos.ne'

  have h_rpow_pos :
      ∀ x : ℝ, 0 < Kakeya.realRpowENN delta x := by
    intro x
    simp only [Kakeya.realRpowENN, ENNReal.ofReal_pos]
    exact Real.rpow_pos_of_pos hdelta x
  have h_rpow_ne_top :
      ∀ x : ℝ, Kakeya.realRpowENN delta x ≠ ⊤ := by
    intro x
    exact ENNReal.ofReal_ne_top
  have h_rpow_inv :
      ∀ x : ℝ,
        (Kakeya.realRpowENN delta x)⁻¹ =
          Kakeya.realRpowENN delta (-x) := by
    intro x
    have h_pos : 0 < Real.rpow delta x :=
      Real.rpow_pos_of_pos hdelta x
    have h1 :
        (Kakeya.realRpowENN delta x)⁻¹ =
          ENNReal.ofReal ((Real.rpow delta x)⁻¹) := by
      simp only [Kakeya.realRpowENN]
      exact (ENNReal.ofReal_inv_of_pos h_pos).symm
    rw [h1]
    have h2 :
        (Real.rpow delta x)⁻¹ = Real.rpow delta (-x) :=
      (Real.rpow_neg hdelta.le x).symm
    rw [h2]
    rfl

  have hlambda_inv : lambda⁻¹ =
      ENNReal.ofReal (8 / delta) *
        Kakeya.realRpowENN delta (-densityLoss) := by
    rw [hlambda_eq]
    have h_pos1 : 0 < ENNReal.ofReal (delta / 8) := by
      apply ENNReal.ofReal_pos.mpr
      linarith
    have h1 :
        (ENNReal.ofReal (delta / 8) *
            Kakeya.realRpowENN delta densityLoss)⁻¹ =
          (ENNReal.ofReal (delta / 8))⁻¹ *
            (Kakeya.realRpowENN delta densityLoss)⁻¹ :=
      ENNReal.mul_inv
        (Or.inl h_pos1.ne') (Or.inl ENNReal.ofReal_ne_top)
    rw [h1]
    have h2 :
        (ENNReal.ofReal (delta / 8))⁻¹ =
          ENNReal.ofReal (8 / delta) := by
      have h_pos : 0 < delta / 8 := by linarith
      have h_inv :
          (ENNReal.ofReal (delta / 8))⁻¹ =
            ENNReal.ofReal ((delta / 8)⁻¹) :=
        (ENNReal.ofReal_inv_of_pos h_pos).symm
      rw [h_inv]
      have h_div : (delta / 8)⁻¹ = 8 / delta := by
        field_simp [hdelta.ne'] <;> ring
      rw [h_div]
    have h3 :
        (Kakeya.realRpowENN delta densityLoss)⁻¹ =
          Kakeya.realRpowENN delta (-densityLoss) :=
      h_rpow_inv densityLoss
    rw [h2, h3]

  have h_imb_ENNReal : (imbalance : ENNReal) ≤
      8000001 *
        Kakeya.realRpowENN delta
          (-2 - densityLoss - frostmanLoss) := by
    have h := himbalance_bound
    rw [hlambda_inv] at h
    have h4 :
        ENNReal.ofReal (8 / delta) =
          (8 : ENNReal) * Kakeya.realRpowENN delta (-1) := by
      simp only [Kakeya.realRpowENN]
      have h6 :
          (8 / delta : ℝ) = 8 * Real.rpow delta (-1) := by
        have h7 : Real.rpow delta (-1) = delta⁻¹ := by
          have h1 :
              Real.rpow delta (-1) =
                (Real.rpow delta 1)⁻¹ := by
            simpa using Real.rpow_neg hdelta.le (1 : ℝ)
          have h2 : Real.rpow delta 1 = delta :=
            Real.rpow_one delta
          rw [h1, h2]
        rw [h7]
        ring
      rw [h6, ENNReal.ofReal_mul (by norm_num)]
      norm_cast
    have h5 :
        1000000 * C *
              (ENNReal.ofReal (8 / delta) *
                Kakeya.realRpowENN delta (-densityLoss)) *
              Kakeya.realRpowENN delta (-1) ≤
          8000000 *
            Kakeya.realRpowENN delta
              (-2 - densityLoss - frostmanLoss) := by
      calc
        1000000 * C *
              (ENNReal.ofReal (8 / delta) *
                Kakeya.realRpowENN delta (-densityLoss)) *
              Kakeya.realRpowENN delta (-1)
            ≤
          1000000 *
              Kakeya.realRpowENN delta (-frostmanLoss) *
              (ENNReal.ofReal (8 / delta) *
                Kakeya.realRpowENN delta (-densityLoss)) *
              Kakeya.realRpowENN delta (-1) := by
                gcongr
        _ = 8000000 *
              Kakeya.realRpowENN delta
                (-2 - densityLoss - frostmanLoss) := by
          rw [h4]
          have h6 :=
            realRpowENN_add hdelta
              (-frostmanLoss) (-densityLoss)
          have h7 :=
            realRpowENN_add hdelta
              (-frostmanLoss - densityLoss) (-1)
          have h8 :=
            realRpowENN_add hdelta
              (-frostmanLoss - densityLoss - 1) (-1)
          ring_nf at *
          simp [h6, h7, h8]
          ring
    have h9 :
        (1 : ENNReal) ≤
          Kakeya.realRpowENN delta
            (-2 - densityLoss - frostmanLoss) := by
      have h10 : -2 - densityLoss - frostmanLoss < 0 := by
        linarith
      have h11 :
          Real.rpow delta
              (-2 - densityLoss - frostmanLoss) ≥ 1 := by
        have h12 :
            Real.rpow delta
                (-2 - densityLoss - frostmanLoss) ≥
              Real.rpow delta 0 :=
          Real.rpow_le_rpow_of_exponent_ge
            hdelta hdelta_lt_one.le (by linarith)
        simpa using h12
      have h13 : (1 : ENNReal) = ENNReal.ofReal 1 := by
        norm_cast
      rw [h13]
      simp only [Kakeya.realRpowENN]
      exact ENNReal.ofReal_mono h11
    calc
      (imbalance : ENNReal)
          ≤ 1000000 * C *
              (ENNReal.ofReal (8 / delta) *
                Kakeya.realRpowENN delta (-densityLoss)) *
              Kakeya.realRpowENN delta (-1) + 1 := h
      _ ≤ 8000000 *
              Kakeya.realRpowENN delta
                (-2 - densityLoss - frostmanLoss) + 1 := by
            gcongr
      _ ≤ 8000000 *
              Kakeya.realRpowENN delta
                (-2 - densityLoss - frostmanLoss) +
            Kakeya.realRpowENN delta
              (-2 - densityLoss - frostmanLoss) := by
            gcongr
      _ = 8000001 *
              Kakeya.realRpowENN delta
                (-2 - densityLoss - frostmanLoss) := by
            ring

  have h_imb_real : (imbalance : ℝ) ≤
      8000001 *
        Real.rpow delta
          (-2 - densityLoss - frostmanLoss) := by
    have h_ne_top1 : (imbalance : ENNReal) ≠ ⊤ := by
      simp
    have h_ne_top2 :
        (8000001 *
          Kakeya.realRpowENN delta
            (-2 - densityLoss - frostmanLoss)) ≠ ⊤ := by
      apply ENNReal.mul_ne_top
      · simp
      · exact ENNReal.ofReal_ne_top
    have h :
        (imbalance : ENNReal).toReal ≤
          (8000001 *
            Kakeya.realRpowENN delta
              (-2 - densityLoss - frostmanLoss)).toReal :=
      (ENNReal.toReal_le_toReal h_ne_top1 h_ne_top2).mpr
        h_imb_ENNReal
    have h' : (imbalance : ENNReal).toReal = (imbalance : ℝ) := by
      simp
    have h'' :
        (8000001 *
          Kakeya.realRpowENN delta
            (-2 - densityLoss - frostmanLoss)).toReal =
          8000001 *
            Real.rpow delta
              (-2 - densityLoss - frostmanLoss) := by
      rw [ENNReal.toReal_mul]
      have h_rpow :
          (Kakeya.realRpowENN delta
            (-2 - densityLoss - frostmanLoss)).toReal =
              Real.rpow delta
                (-2 - densityLoss - frostmanLoss) := by
        simp only [Kakeya.realRpowENN]
        exact ENNReal.toReal_ofReal
          (Real.rpow_nonneg hdelta.le _)
      rw [h_rpow]
      simp
    rw [h', h''] at h
    exact h

  have hlog2_pos : 0 < Real.log 2 :=
    Real.log_pos (by norm_num)
  have hlog2_half : 1 / 2 ≤ Real.log 2 := by
    have h1 :
        Real.log (1 / 2 : ℝ) ≤ (1 / 2 : ℝ) - 1 :=
      Real.log_le_sub_one_of_pos (by norm_num)
    have h2 : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
      rw [Real.log_div (by norm_num) (by norm_num)]
      simp
    rw [h2] at h1
    linarith

  set n := imbalance with hn_def
  have hn_pos' : 0 < n := himbalance_pos

  have h_nat_log3 :
      (Nat.log 2 (2 * n) : ℝ) * Real.log 2 ≤
        Real.log ((2 * n : ℕ) : ℝ) := by
    have h1 :
        (2 : ℕ) ^ Nat.log 2 (2 * n) ≤ 2 * n :=
      Nat.pow_log_le_self 2 (by positivity)
    have h2 :
        ((2 : ℝ) ^ Nat.log 2 (2 * n)) ≤
          ((2 * n : ℕ) : ℝ) := by
      exact_mod_cast h1
    have h3 :
        Real.log ((2 : ℝ) ^ Nat.log 2 (2 * n)) ≤
          Real.log ((2 * n : ℕ) : ℝ) :=
      Real.log_le_log (by positivity) h2
    have h4 :
        Real.log ((2 : ℝ) ^ Nat.log 2 (2 * n)) =
          (Nat.log 2 (2 * n) : ℝ) * Real.log 2 := by
      rw [Real.log_pow]
    rw [h4] at h3
    exact h3

  have h_2n_bound : ((2 * n : ℕ) : ℝ) ≤
      16000002 *
        Real.rpow delta
          (-2 - densityLoss - frostmanLoss) := by
    have h6 :
        ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by
      simp [Nat.cast_mul]
    rw [h6]
    have h7 :
        2 * (n : ℝ) ≤
          2 * (8000001 *
            Real.rpow delta
              (-2 - densityLoss - frostmanLoss)) := by
      gcongr
    linarith

  have h_log_delta_inv_pos : 0 < Real.log delta⁻¹ := by
    have h21 : 1 < delta⁻¹ := by
      have hpos : 0 < delta := hdelta
      have hlt : delta < 1 := hdelta_lt_one
      have h : 1 / delta > 1 / 1 :=
        one_div_lt_one_div_of_lt hpos hlt
      simpa using h
    exact Real.log_pos h21

  set L :=
    Real.rpow delta
      (-2 - densityLoss - frostmanLoss) with hL_def
  have hL_pos : 0 < L := Real.rpow_pos_of_pos hdelta _

  have h_log_2n :
      Real.log ((2 * n : ℕ) : ℝ) ≤
        Real.log 16000002 +
          (2 + densityLoss + frostmanLoss) *
            Real.log delta⁻¹ := by
    have h7 : 0 < (2 * n : ℕ) := by positivity
    have h8 :
        ((2 * n : ℕ) : ℝ) ≤ 16000002 * L :=
      h_2n_bound
    have h9 : 0 < 16000002 * L := by positivity
    have h10 :
        Real.log ((2 * n : ℕ) : ℝ) ≤
          Real.log (16000002 * L) :=
      Real.log_le_log (by exact_mod_cast h7) h8
    have h11 :
        Real.log (16000002 * L) =
          Real.log 16000002 + Real.log L :=
      Real.log_mul (by norm_num) hL_pos.ne'
    have h12 :
        Real.log L =
          (-2 - densityLoss - frostmanLoss) *
            Real.log delta := by
      simp only [hL_def]
      exact Real.log_rpow hdelta
        (-2 - densityLoss - frostmanLoss)
    rw [h11, h12] at h10
    have h13 : Real.log delta⁻¹ = -Real.log delta := by
      rw [Real.log_inv]
    rw [h13] at *
    linarith

  have h_log16000002 : Real.log 16000002 < 24 := by
    have h14 : (16000002 : ℝ) < (2 : ℝ) ^ 24 := by
      norm_num
    have h15 :
        Real.log 16000002 < Real.log ((2 : ℝ) ^ 24) :=
      Real.log_lt_log (by norm_num) h14
    have h16 :
        Real.log ((2 : ℝ) ^ 24) = 24 * Real.log 2 := by
      rw [Real.log_pow]
      ring
    rw [h16] at h15
    have h17 : Real.log 2 < 1 := by
      have h_exp1 : Real.exp 1 > (2 : ℝ) := by
        have h : (1 : ℝ) + 1 < Real.exp 1 :=
          Real.add_one_lt_exp
            (show (1 : ℝ) ≠ 0 by norm_num)
        have h' : (1 : ℝ) + 1 = (2 : ℝ) := by norm_num
        rw [h'] at h
        exact h
      have h_log :
          Real.log 2 < Real.log (Real.exp 1) :=
        Real.log_lt_log (by norm_num) h_exp1
      have h_eq : Real.log (Real.exp 1) = 1 := by simp
      rw [h_eq] at h_log
      exact h_log
    linarith

  have h_sum_lt3 :
      2 + densityLoss + frostmanLoss < 3 := by
    linarith

  have h_nat_log4 :
      (Nat.log 2 (2 * n) : ℝ) ≤
        48 + 6 * Real.log delta⁻¹ := by
    have h24 :
        (Nat.log 2 (2 * n) : ℝ) ≤
          Real.log ((2 * n : ℕ) : ℝ) / Real.log 2 := by
      calc
        (Nat.log 2 (2 * n) : ℝ)
            =
          ((Nat.log 2 (2 * n) : ℝ) * Real.log 2) /
            Real.log 2 := by
              field_simp [hlog2_pos.ne'] <;> ring
        _ ≤ Real.log ((2 * n : ℕ) : ℝ) / Real.log 2 := by
              gcongr
    have h25 :
        Real.log ((2 * n : ℕ) : ℝ) / Real.log 2 ≤
          2 * Real.log ((2 * n : ℕ) : ℝ) := by
      have h26 : 1 / Real.log 2 ≤ 2 := by
        have h27 : 1 ≤ 2 * Real.log 2 := by
          linarith [hlog2_half]
        calc
          1 / Real.log 2
              ≤ (2 * Real.log 2) / Real.log 2 := by
                gcongr
          _ = 2 := by
                field_simp [hlog2_pos.ne'] <;> ring
      calc
        Real.log ((2 * n : ℕ) : ℝ) / Real.log 2
            =
          (1 / Real.log 2) *
            Real.log ((2 * n : ℕ) : ℝ) := by ring
        _ ≤ 2 * Real.log ((2 * n : ℕ) : ℝ) := by
              gcongr
    have h29 :
        Real.log ((2 * n : ℕ) : ℝ) <
          24 + 3 * Real.log delta⁻¹ := by
      have h30 :
          Real.log ((2 * n : ℕ) : ℝ) ≤
            Real.log 16000002 +
              (2 + densityLoss + frostmanLoss) *
                Real.log delta⁻¹ :=
        h_log_2n
      have h31 :
          Real.log 16000002 +
              (2 + densityLoss + frostmanLoss) *
                Real.log delta⁻¹ <
            24 + 3 * Real.log delta⁻¹ := by
        have h32 : Real.log 16000002 < 24 :=
          h_log16000002
        have h33 :
            (2 + densityLoss + frostmanLoss) *
                Real.log delta⁻¹ <
              3 * Real.log delta⁻¹ := by
          have h34 : 0 < Real.log delta⁻¹ :=
            h_log_delta_inv_pos
          nlinarith
        nlinarith
      exact h30.trans_lt h31
    have h35 :
        (Nat.log 2 (2 * n) : ℝ) ≤
          2 * Real.log ((2 * n : ℕ) : ℝ) :=
      h24.trans h25
    have h36 :
        2 * Real.log ((2 * n : ℕ) : ℝ) ≤
          48 + 6 * Real.log delta⁻¹ := by
      linarith [h29]
    exact h35.trans h36

  have h_nat_log5 :
      (Nat.log 2 (2 * n) + 1 : ℝ) ≤
        49 + 6 * Real.log delta⁻¹ := by
    have h36 :
        (Nat.log 2 (2 * n) : ℝ) ≤
          48 + 6 * Real.log delta⁻¹ :=
      h_nat_log4
    simp at *
    linarith

  have h30 :
      R = 4 * (Nat.log 2 (2 * n) + 1 : ENNReal) :=
    hR_eq
  rw [h30]
  have h_val :
      (↑(Nat.log 2 (2 * n)) + 1 : ENNReal) =
        ENNReal.ofReal
          ((↑(Nat.log 2 (2 * n)) + 1 : ℝ)) := by
    have h37 :
        (↑(Nat.log 2 (2 * n)) + 1 : ENNReal) =
          (↑(Nat.log 2 (2 * n) + 1) : ENNReal) := by
      simp [Nat.cast_add]
    rw [h37]
    have h38 :
        (↑(Nat.log 2 (2 * n) + 1) : ℝ) =
          (↑(Nat.log 2 (2 * n)) : ℝ) + 1 := by
      simp [Nat.cast_add]
    have h39 :
        (↑(Nat.log 2 (2 * n) + 1) : ENNReal) =
          ENNReal.ofReal
            (↑(Nat.log 2 (2 * n) + 1) : ℝ) :=
      (ENNReal.ofReal_natCast
        (Nat.log 2 (2 * n) + 1)).symm
    rw [h38] at h39
    exact h39
  rw [h_val]
  have h32 :
      4 * ENNReal.ofReal
          ((Nat.log 2 (2 * n) + 1 : ℝ)) =
        ENNReal.ofReal
          (4 * (Nat.log 2 (2 * n) + 1 : ℝ)) := by
    rw [ENNReal.ofReal_mul (by norm_num)]
    norm_cast
  rw [h32]
  have h33 :
      4 * (Nat.log 2 (2 * n) + 1 : ℝ) ≤
        200 * (1 + Real.log delta⁻¹) := by
    have h34 :
        (Nat.log 2 (2 * n) + 1 : ℝ) ≤
          49 + 6 * Real.log delta⁻¹ :=
      h_nat_log5
    have h35 : 0 < Real.log delta⁻¹ :=
      h_log_delta_inv_pos
    linarith
  exact ENNReal.ofReal_mono h33

theorem parameter_window_cluster_cardinality :
    ParameterWindowClusterCardinalityStatement := by
  intro delta densityLoss frostmanLoss targetLoss gamma
    hdelta hdelta_lt_one hdensity_pos hfrost_pos hsum_lt_one
    hgamma_eq hgamma_pos F Y C lambda clustered hC_le hlambda_eq
    hlog_absorb

  set R := clustered.regularizationLoss with hR_def
  set P2 := Kakeya.realRpowENN delta 2 with hP2_def
  set X := clustered.points.enncard with hX_def

  have hR_one : 1 ≤ R := clustered.regularizationLoss_one
  have hR_ne_top : R ≠ ⊤ :=
    clustered.regularizationLoss_ne_top
  have hR_pos : 0 < R := zero_lt_one.trans_le hR_one
  have hR_ne_zero : R ≠ 0 := hR_pos.ne'

  have h_frost_const :
      1 ≤ 100000 * C * R * lambda⁻¹ := by
    simpa [tubeParameterClusterFrostmanConstant] using
      clustered.frostmanConstant_one
  have hC_pos : 0 < C := by
    by_contra h
    have hC0 : C = 0 := by simpa using h
    rw [hC0] at h_frost_const
    simp at h_frost_const
  have hC_ne_zero : C ≠ 0 := hC_pos.ne'
  have hC_ne_top : C ≠ ⊤ := by
    have h :
        C ≤ Kakeya.realRpowENN delta (-frostmanLoss) :=
      hC_le
    have h' :
        Kakeya.realRpowENN delta (-frostmanLoss) ≠ ⊤ :=
      ENNReal.ofReal_ne_top
    exact ne_top_of_le_ne_top h' h

  have hlambda_pos : 0 < lambda := by
    rw [hlambda_eq]
    have h1 : 0 < ENNReal.ofReal (delta / 8) := by
      apply ENNReal.ofReal_pos.mpr
      linarith
    have h2 :
        0 < Kakeya.realRpowENN delta densityLoss := by
      simp only [Kakeya.realRpowENN]
      apply ENNReal.ofReal_pos.mpr
      exact Real.rpow_pos_of_pos hdelta _
    positivity
  have hlambda_ne_zero : lambda ≠ 0 := hlambda_pos.ne'
  have hlambda_ne_top : lambda ≠ ⊤ := by
    rw [hlambda_eq]
    exact ENNReal.mul_ne_top
      ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top

  have hP2_pos : 0 < P2 := by
    simp only [hP2_def, Kakeya.realRpowENN]
    apply ENNReal.ofReal_pos.mpr
    exact Real.rpow_pos_of_pos hdelta _
  have hP2_ne_zero : P2 ≠ 0 := hP2_pos.ne'
  have hP2_ne_top : P2 ≠ ⊤ := by
    simp [hP2_def, Kakeya.realRpowENN,
      ENNReal.ofReal_ne_top]

  have h_rpow_pos :
      ∀ x : ℝ, 0 < Kakeya.realRpowENN delta x := by
    intro x
    simp only [Kakeya.realRpowENN, ENNReal.ofReal_pos]
    exact Real.rpow_pos_of_pos hdelta x
  have h_rpow_ne_top :
      ∀ x : ℝ, Kakeya.realRpowENN delta x ≠ ⊤ := by
    intro x
    exact ENNReal.ofReal_ne_top
  have h_rpow_inv :
      ∀ x : ℝ,
        (Kakeya.realRpowENN delta x)⁻¹ =
          Kakeya.realRpowENN delta (-x) := by
    intro x
    have h_pos : 0 < Real.rpow delta x :=
      Real.rpow_pos_of_pos hdelta x
    have h1 :
        (Kakeya.realRpowENN delta x)⁻¹ =
          ENNReal.ofReal ((Real.rpow delta x)⁻¹) := by
      simp only [Kakeya.realRpowENN]
      exact (ENNReal.ofReal_inv_of_pos h_pos).symm
    rw [h1]
    have h2 :
        (Real.rpow delta x)⁻¹ = Real.rpow delta (-x) :=
      (Real.rpow_neg hdelta.le x).symm
    rw [h2]
    rfl

  have h_R_bound :
      R ≤ ENNReal.ofReal
        (200 * (1 + Real.log delta⁻¹)) :=
    cluster_regularization_loss_bound
      hdelta hdelta_lt_one hdensity_pos hfrost_pos hsum_lt_one
      hR_one hR_ne_top hC_pos hC_ne_top
      hlambda_pos hlambda_ne_top hC_le hlambda_eq
      clustered.imbalance_pos clustered.imbalance_bound
      clustered.regularizationLoss_eq

  have h_log_delta_inv_pos : 0 < Real.log delta⁻¹ := by
    have h21 : 1 < delta⁻¹ := by
      have hpos : 0 < delta := hdelta
      have hlt : delta < 1 := hdelta_lt_one
      have h : 1 / delta > 1 / 1 :=
        one_div_lt_one_div_of_lt hpos hlt
      simpa using h
    exact Real.log_pos h21

  have h_absorb :
      200 * (1 + Real.log delta⁻¹) ≤
        (1 / 8 : ℝ) * Real.rpow delta (-gamma) := by
    have h34 :
        1600 * (1 + Real.log delta⁻¹) ≤
          Real.rpow delta (-gamma) :=
      hlog_absorb
    have h35 :
        200 * (1 + Real.log delta⁻¹) =
          (1 / 8 : ℝ) *
            (1600 * (1 + Real.log delta⁻¹)) := by
      ring
    rw [h35]
    have h36 : 0 ≤ Real.rpow delta (-gamma) :=
      Real.rpow_nonneg hdelta.le _
    gcongr

  have h_log_absorbed :
      8 * R ≤ Kakeya.realRpowENN delta (-gamma) := by
    have h_R_bound2 :
        R ≤ (1 / 8 : ENNReal) *
          Kakeya.realRpowENN delta (-gamma) := by
      calc
        R ≤ ENNReal.ofReal
              (200 * (1 + Real.log delta⁻¹)) := h_R_bound
        _ ≤ ENNReal.ofReal
              ((1 / 8 : ℝ) *
                Real.rpow delta (-gamma)) :=
          ENNReal.ofReal_mono h_absorb
        _ = (1 / 8 : ENNReal) *
              Kakeya.realRpowENN delta (-gamma) := by
          have h_mul :
              ENNReal.ofReal
                  ((1 / 8 : ℝ) *
                    Real.rpow delta (-gamma)) =
                ENNReal.ofReal (1 / 8 : ℝ) *
                  ENNReal.ofReal
                    (Real.rpow delta (-gamma)) :=
            ENNReal.ofReal_mul (by norm_num)
          rw [h_mul]
          have h1 :
              ENNReal.ofReal (1 / 8 : ℝ) =
                (1 / 8 : ENNReal) := by simp
          have h2 :
              ENNReal.ofReal (Real.rpow delta (-gamma)) =
                Kakeya.realRpowENN delta (-gamma) := by
            simp [Kakeya.realRpowENN]
          rw [h1, h2]
    have h :
        8 * R ≤
          8 * ((1 / 8 : ENNReal) *
            Kakeya.realRpowENN delta (-gamma)) := by
      gcongr
    have h3 : (8 : ENNReal) * (1 / 8 : ENNReal) = 1 := by
      have h31 :
          (1 / 8 : ENNReal) = (8 : ENNReal)⁻¹ := by
        simp [one_div]
      rw [h31]
      exact ENNReal.mul_inv_cancel (by simp) (by simp)
    have h2 :
        8 * ((1 / 8 : ENNReal) *
            Kakeya.realRpowENN delta (-gamma)) =
          Kakeya.realRpowENN delta (-gamma) := by
      rw [←mul_assoc, h3, one_mul]
    rw [h2] at h
    exact h

  have h_lambda_eq2 : lambda =
      (1 / 8 : ENNReal) *
        Kakeya.realRpowENN delta (1 + densityLoss) := by
    rw [hlambda_eq]
    have h1 :
        ENNReal.ofReal (delta / 8) =
          (1 / 8 : ENNReal) * ENNReal.ofReal delta := by
      have h2 :
          (delta / 8 : ℝ) = (1 / 8 : ℝ) * delta := by
        ring
      rw [h2]
      have h3 :
          ENNReal.ofReal ((1 / 8 : ℝ) * delta) =
            ENNReal.ofReal (1 / 8 : ℝ) *
              ENNReal.ofReal delta :=
        ENNReal.ofReal_mul (by positivity)
      rw [h3]
      have h4 :
          ENNReal.ofReal (1 / 8 : ℝ) =
            (1 / 8 : ENNReal) := by simp
      rw [h4]
    have h3 :
        Kakeya.realRpowENN delta 1 = ENNReal.ofReal delta := by
      simp [Kakeya.realRpowENN, Real.rpow_one]
    rw [h1, ←h3]
    have h4 :
        (1 + densityLoss : ℝ) = (1 : ℝ) + densityLoss := by
      ring
    rw [h4, realRpowENN_add hdelta 1 densityLoss]
    ring

  have h1 :
      (1 / 8 : ENNReal) *
          Kakeya.realRpowENN delta (1 + densityLoss) ≤
        100000 * R *
          (Kakeya.realRpowENN delta (-frostmanLoss) * P2) *
          X := by
    have h_card :
        lambda ≤ 100000 * R * (C * P2) * X :=
      clustered.points_card_lower
    rw [h_lambda_eq2] at h_card
    calc
      (1 / 8 : ENNReal) *
            Kakeya.realRpowENN delta (1 + densityLoss)
          ≤ 100000 * R * (C * P2) * X := h_card
      _ = 100000 * R * C * P2 * X := by ring
      _ ≤ 100000 * R *
            Kakeya.realRpowENN delta (-frostmanLoss) *
            P2 * X := by
              gcongr
      _ = 100000 * R *
            (Kakeya.realRpowENN delta (-frostmanLoss) * P2) *
            X := by ring

  set d2 :=
    Kakeya.realRpowENN delta (2 - frostmanLoss) with hd2_def
  have hd2_pos : 0 < d2 :=
    h_rpow_pos (2 - frostmanLoss)
  have hd2_ne_top : d2 ≠ ⊤ :=
    h_rpow_ne_top (2 - frostmanLoss)
  have hd2_ne_zero : d2 ≠ 0 := hd2_pos.ne'

  have h_pow_combine :
      Kakeya.realRpowENN delta (-frostmanLoss) * P2 = d2 := by
    simp only [hP2_def, hd2_def]
    have h :
        -frostmanLoss + (2 : ℝ) = 2 - frostmanLoss := by
      ring
    rw [←realRpowENN_add hdelta
      (-frostmanLoss) (2 : ℝ), h]

  have h1' :
      (1 / 8 : ENNReal) *
          Kakeya.realRpowENN delta (1 + densityLoss) ≤
        100000 * R * d2 * X := by
    rw [h_pow_combine] at h1
    exact h1

  have h_d2_inv_mul : d2 * d2⁻¹ = 1 :=
    ENNReal.mul_inv_cancel hd2_ne_zero hd2_ne_top

  have h4 :
      (1 / 8 : ENNReal) *
          Kakeya.realRpowENN delta
            (densityLoss + frostmanLoss - 1) ≤
        100000 * R * X := by
    have h41 :
        (1 / 8 : ENNReal) *
              Kakeya.realRpowENN delta (1 + densityLoss) *
              d2⁻¹ ≤
            (100000 * R * d2 * X) * d2⁻¹ := by
      gcongr
    have h42 :
        (100000 * R * d2 * X) * d2⁻¹ =
          100000 * R * X := by
      calc
        (100000 * R * d2 * X) * d2⁻¹
            = 100000 * R * (d2 * d2⁻¹) * X := by ring
        _ = 100000 * R * (1 : ENNReal) * X := by
              rw [h_d2_inv_mul]
        _ = 100000 * R * X := by ring
    have h43 :
        (1 / 8 : ENNReal) *
              Kakeya.realRpowENN delta (1 + densityLoss) *
              d2⁻¹ =
            (1 / 8 : ENNReal) *
              Kakeya.realRpowENN delta
                (densityLoss + frostmanLoss - 1) := by
      have h_inv :
          d2⁻¹ =
            Kakeya.realRpowENN delta
              (-(2 - frostmanLoss)) := by
        simpa [hd2_def] using
          h_rpow_inv (2 - frostmanLoss)
      rw [h_inv]
      have h_add :
          (1 + densityLoss) + (-(2 - frostmanLoss)) =
            densityLoss + frostmanLoss - 1 := by
        ring
      have h_mul :
          Kakeya.realRpowENN delta (1 + densityLoss) *
              Kakeya.realRpowENN delta
                (-(2 - frostmanLoss)) =
            Kakeya.realRpowENN delta
              (densityLoss + frostmanLoss - 1) := by
        rw [←realRpowENN_add hdelta
          (1 + densityLoss) (-(2 - frostmanLoss)), h_add]
      have h_goal :
          (1 / 8 : ENNReal) *
                Kakeya.realRpowENN delta (1 + densityLoss) *
                Kakeya.realRpowENN delta
                  (-(2 - frostmanLoss)) =
              (1 / 8 : ENNReal) *
                (Kakeya.realRpowENN delta (1 + densityLoss) *
                  Kakeya.realRpowENN delta
                    (-(2 - frostmanLoss))) := by
        ring
      rw [h_goal, h_mul]
    rw [h43] at h41
    rw [h42] at h41
    exact h41

  have h5 :
      Kakeya.realRpowENN delta gamma ≤ (8 * R)⁻¹ := by
    have h51 :
        (Kakeya.realRpowENN delta (-gamma))⁻¹ ≤
          (8 * R)⁻¹ :=
      ENNReal.inv_le_inv.mpr h_log_absorbed
    have h52 :
        (Kakeya.realRpowENN delta (-gamma))⁻¹ =
          Kakeya.realRpowENN delta gamma := by
      have h := h_rpow_inv (-gamma)
      have h_neg : -(-gamma) = gamma := by ring
      rw [h_neg] at h
      exact h
    rw [h52] at h51
    exact h51

  have h6 :
      Kakeya.realRpowENN delta (-1 + targetLoss) =
        Kakeya.realRpowENN delta
            (densityLoss + frostmanLoss - 1) *
          Kakeya.realRpowENN delta gamma := by
    have h_exp :
        -1 + targetLoss =
          (densityLoss + frostmanLoss - 1) + gamma := by
      linarith [hgamma_eq]
    rw [h_exp]
    exact realRpowENN_add hdelta
      (densityLoss + frostmanLoss - 1) gamma

  have h_reg_inv_mul : R * R⁻¹ = 1 :=
    ENNReal.mul_inv_cancel hR_ne_zero hR_ne_top

  have h7 :
      (1 / 8 : ENNReal) *
            Kakeya.realRpowENN delta
              (densityLoss + frostmanLoss - 1) *
            R⁻¹ ≤
          100000 * X := by
    have h71 :
        ((1 / 8 : ENNReal) *
              Kakeya.realRpowENN delta
                (densityLoss + frostmanLoss - 1)) *
              R⁻¹ ≤
            (100000 * R * X) * R⁻¹ := by
      gcongr
    have h72 :
        (100000 * R * X) * R⁻¹ = 100000 * X := by
      calc
        (100000 * R * X) * R⁻¹
            = 100000 * (R * R⁻¹) * X := by ring
        _ = 100000 * (1 : ENNReal) * X := by
              rw [h_reg_inv_mul]
        _ = 100000 * X := by ring
    rw [h72] at h71
    exact h71

  have h8_ne_zero : (8 : ENNReal) ≠ 0 := by simp
  have h8_ne_top : (8 : ENNReal) ≠ ⊤ := by simp
  have h8 :
      (8 * R)⁻¹ = (1 / 8 : ENNReal) * R⁻¹ := by
    have h81 :
        (8 * R)⁻¹ = (8 : ENNReal)⁻¹ * R⁻¹ :=
      ennreal_inv_mul
        h8_ne_zero h8_ne_top hR_ne_zero hR_ne_top
    have h82 :
        (8 : ENNReal)⁻¹ = (1 / 8 : ENNReal) := by
      simp [one_div]
    rw [h81, h82]

  calc
    Kakeya.realRpowENN delta (-1 + targetLoss)
        =
      Kakeya.realRpowENN delta
          (densityLoss + frostmanLoss - 1) *
        Kakeya.realRpowENN delta gamma := h6
    _ ≤ Kakeya.realRpowENN delta
          (densityLoss + frostmanLoss - 1) *
        (8 * R)⁻¹ := by
          gcongr
    _ = Kakeya.realRpowENN delta
          (densityLoss + frostmanLoss - 1) *
        ((1 / 8 : ENNReal) * R⁻¹) := by
          rw [h8]
    _ = (1 / 8 : ENNReal) *
        Kakeya.realRpowENN delta
          (densityLoss + frostmanLoss - 1) *
        R⁻¹ := by
          ring
    _ ≤ 100000 * X := h7

end Kakeya.Assouad
