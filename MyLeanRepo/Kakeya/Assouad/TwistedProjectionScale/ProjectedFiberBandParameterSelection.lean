import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.ProjectedFiberBandParameterSelectionStatement
import MyLeanRepo.Kakeya.Assouad.TubeVolumeScaling
import MyLeanRepo.Kakeya.Assouad.TubeVolumeLowerBound
import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Parameters for the projected-fiber multiplicity band

Choose a normalized threshold and a finite dyadic range whose logarithmic
band loss is absorbed by one power of `delta^(-eta)`.
-/

namespace Kakeya.Assouad

private lemma projected_fiber_levelCount_selection
    {eta : ℝ} (heta : 0 < eta) (C : ℝ) (hC : 0 ≤ C) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ < 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        ∃ levelCount : ℕ,
          C / delta ^ (eta + 1) ≤ (2 ^ levelCount : ℝ) ∧
          2 * (levelCount + 1 : ℝ) ≤ delta ^ (-eta) := by
  let eps : ℝ := eta / 2
  have heps : 0 < eps := by positivity
  have hlog2_pos : 0 < Real.log 2 :=
    Real.log_pos (by norm_num)
  let A : ℝ := 2 * Real.log (C + 1) / Real.log 2 + 4
  let B : ℝ := 4 * (eta + 1) / (eta * Real.log 2)
  let D : ℝ := A + B
  have hA_nonneg : 0 ≤ A := by
    have h1 : 0 ≤ Real.log (C + 1) :=
      Real.log_nonneg (by linarith)
    have h2 : 0 ≤ Real.log (C + 1) / Real.log 2 := by
      positivity
    positivity
  have hB_nonneg : 0 ≤ B := by positivity
  have hD_nonneg : 0 ≤ D := by positivity
  rcases exists_delta_realRpowENN_bound
      (ENNReal.ofReal D) ENNReal.ofReal_ne_top heps with
    ⟨delta₁, hdelta₁_pos, hdelta₁_one, hbound⟩
  let delta₀ : ℝ := min delta₁ (1 / 2)
  have hdelta₀_pos : 0 < delta₀ := by positivity
  have hdelta₀_lt_one : delta₀ < 1 := by
    have h : delta₀ ≤ 1 / 2 := min_le_right _ _
    linarith
  refine ⟨delta₀, hdelta₀_pos, hdelta₀_lt_one, ?_⟩
  intro delta hdelta_pos hdelta_le
  have hdelta_le₁ : delta ≤ delta₁ :=
    hdelta_le.trans (min_le_left _ _)
  set z : ℝ := (C + 1) / delta ^ (eta + 1) with hz_def
  have hz_pos : 0 < z := by positivity
  have hz_one : 1 ≤ z := by
    have h1 : delta ^ (eta + 1) ≤ 1 :=
      Real.rpow_le_one hdelta_pos.le (by linarith) (by linarith)
    have h2 : 1 ≤ C + 1 := by linarith
    exact (one_le_div (by positivity)).mpr (by linarith)
  set levelCount : ℕ :=
    Nat.ceil (Real.log z / Real.log 2) with hlc_def
  have hlog_z_nonneg : 0 ≤ Real.log z :=
    Real.log_nonneg hz_one
  have h1 :
      Real.log z / Real.log 2 ≤ (levelCount : ℝ) :=
    Nat.le_ceil (Real.log z / Real.log 2)
  have h2 :
      Real.log z ≤ (levelCount : ℝ) * Real.log 2 := by
    calc
      Real.log z =
          (Real.log z / Real.log 2) * Real.log 2 := by
            field_simp [hlog2_pos.ne'] <;> ring
      _ ≤ (levelCount : ℝ) * Real.log 2 := by gcongr
  have h3 : z ≤ (2 : ℝ) ^ levelCount := by
    have h4 :
        Real.exp (Real.log z) ≤
          Real.exp ((levelCount : ℝ) * Real.log 2) :=
      Real.exp_le_exp.mpr h2
    have h5 : Real.exp (Real.log z) = z :=
      Real.exp_log hz_pos
    have h6 :
        Real.exp ((levelCount : ℝ) * Real.log 2) =
          (2 : ℝ) ^ levelCount := by
      have h_comm :
          (levelCount : ℝ) * Real.log 2 =
            Real.log 2 * (levelCount : ℝ) := by
        ring
      rw [h_comm]
      have h61 :
          Real.exp (Real.log 2 * (levelCount : ℝ)) =
            (Real.exp (Real.log 2)) ^ (levelCount : ℝ) := by
        rw [Real.exp_mul]
      rw [h61]
      have h62 : Real.exp (Real.log 2) = (2 : ℝ) :=
        Real.exp_log (by norm_num)
      rw [h62]
      have h63 :
          (2 : ℝ) ^ (levelCount : ℝ) =
            (2 : ℝ) ^ levelCount := by
        rw [Real.rpow_natCast]
      rw [h63] <;> norm_cast
    rw [h5, h6] at h4
    exact h4
  have h_main1 :
      C / delta ^ (eta + 1) ≤ (2 ^ levelCount : ℝ) := by
    have h5 : C / delta ^ (eta + 1) ≤ z := by
      rw [hz_def]
      gcongr
      linarith
    simpa using h5.trans h3
  have h7 : -1 < Real.log z / Real.log 2 := by
    have h8 : 0 ≤ Real.log z / Real.log 2 := by positivity
    linarith
  have h8 :
      (levelCount : ℝ) <
        Real.log z / Real.log 2 + 1 :=
    Nat.ceil_lt_add_one_of_gt_neg_one h7
  have h9 :
      (levelCount : ℝ) ≤
        Real.log z / Real.log 2 + 1 := by
    linarith
  have h10 :
      Real.log z =
        Real.log (C + 1) +
          (eta + 1) * Real.log (1 / delta) := by
    have h11 :
        z = (C + 1) * (1 / delta) ^ (eta + 1) := by
      rw [hz_def]
      have h12 :
          (1 / delta) ^ (eta + 1) =
            1 / delta ^ (eta + 1) := by
        have h121 :
            (1 / delta) ^ (eta + 1) =
              (1 : ℝ) ^ (eta + 1) /
                delta ^ (eta + 1) := by
          rw [Real.div_rpow (by norm_num) hdelta_pos.le]
        rw [h121]
        simp
      rw [h12]
      ring
    rw [h11]
    rw [Real.log_mul (by linarith) (by positivity),
      Real.log_rpow (by positivity)] <;> ring
  have h11 :
      Real.log (1 / delta) ≤ (1 / delta) ^ eps / eps :=
    Real.log_le_rpow_div (by positivity) heps
  have h12 : (1 / delta) ^ eps = delta ^ (-eps) := by
    have h121 :
        (1 / delta) ^ eps =
          (1 : ℝ) ^ eps / delta ^ eps := by
      rw [Real.div_rpow (by norm_num) hdelta_pos.le]
    have h122 :
        delta ^ (-eps) = (delta ^ eps)⁻¹ :=
      Real.rpow_neg hdelta_pos.le eps
    rw [h121, h122]
    simp
  have h13 :
      2 * ((levelCount : ℝ) + 1) ≤
        A + B * delta ^ (-eps) := by
    calc
      2 * ((levelCount : ℝ) + 1)
          ≤ 2 * (Real.log z / Real.log 2 + 1 + 1) := by
            gcongr
      _ = 2 * Real.log z / Real.log 2 + 4 := by ring
      _ = 2 *
            (Real.log (C + 1) +
              (eta + 1) * Real.log (1 / delta)) /
            Real.log 2 + 4 := by
          rw [h10] <;> ring
      _ ≤ 2 *
            (Real.log (C + 1) +
              (eta + 1) * ((1 / delta) ^ eps / eps)) /
            Real.log 2 + 4 := by
          gcongr
      _ = A + B * delta ^ (-eps) := by
        have h_eq :
            2 *
                (Real.log (C + 1) +
                  (eta + 1) * ((1 / delta) ^ eps / eps)) /
                Real.log 2 + 4 =
              A + B * delta ^ (-eps) := by
          simp only [A, B, h12]
          have he : eps = eta / 2 := by rfl
          rw [he]
          field_simp [hlog2_pos.ne', heta.ne']
          ring
        exact h_eq
  have h14 : 1 ≤ delta ^ (-eps) := by
    have h15 : delta ≤ 1 := by
      linarith [hdelta_le₁.trans hdelta₁_one]
    have h16 : -eps ≤ 0 := by linarith
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos
      hdelta_pos h15 h16
  have h15 :
      A + B * delta ^ (-eps) ≤ D * delta ^ (-eps) := by
    have h16 : A ≤ A * delta ^ (-eps) := by
      have h :
          A * 1 ≤ A * delta ^ (-eps) :=
        mul_le_mul_of_nonneg_left h14 hA_nonneg
      simpa using h
    calc
      A + B * delta ^ (-eps)
          ≤ A * delta ^ (-eps) + B * delta ^ (-eps) := by
            gcongr
      _ = D * delta ^ (-eps) := by
        simp [D]
        ring
  have h16 :
      2 * ((levelCount : ℝ) + 1) ≤
        D * delta ^ (-eps) :=
    h13.trans h15
  have h17 :
      ENNReal.ofReal D ≤
        Kakeya.realRpowENN delta (-eps) :=
    hbound delta hdelta_pos hdelta_le₁
  have h18 : D ≤ delta ^ (-eps) := by
    simpa [Kakeya.realRpowENN,
      ENNReal.ofReal_le_ofReal_iff
        (Real.rpow_nonneg hdelta_pos.le _)] using h17
  have h19 :
      D * delta ^ (-eps) ≤ delta ^ (-eta) := by
    calc
      D * delta ^ (-eps)
          ≤ delta ^ (-eps) * delta ^ (-eps) := by
            gcongr
      _ = delta ^ (-eta) := by
        rw [← Real.rpow_add hdelta_pos]
        simp [eps]
        ring_nf
  have h20 :
      2 * ((levelCount : ℝ) + 1) ≤ delta ^ (-eta) :=
    h16.trans h19
  exact ⟨levelCount, h_main1, h20⟩

theorem projected_fiber_band_parameter_selection :
    ProjectedFiberBandParameterSelectionStatement := by
  intro eta heta
  let V : ENNReal :=
    MeasureTheory.volume section7ProjectionRectangle
  have hV_ne_top : V ≠ ⊤ := by
    have h1 :
        section7ProjectionRectangle ⊆
          Metric.closedBall (0 : Point2) 52 := by
      intro p hp
      have h2 : |p 0| ≤ 51 := hp.1
      have h3 : |p 1| ≤ 1 := hp.2
      have h4 : dist p (0 : Point2) ≤ 52 := by
        have h41 : dist p (0 : Point2) = ‖p‖ := by
          rw [dist_zero_right]
        rw [h41]
        have h5 :
            ‖p‖ ^ 2 = ∑ i : Fin 2, (p i) ^ 2 :=
          EuclideanSpace.real_norm_sq_eq p
        have h5' :
            ∑ i : Fin 2, (p i) ^ 2 =
              (p 0) ^ 2 + (p 1) ^ 2 := by
          rw [Fin.sum_univ_two] <;> ring
        have h6 :
            (p 0) ^ 2 + (p 1) ^ 2 ≤
              (|p 0| + |p 1|) ^ 2 := by
          have h7 : 0 ≤ 2 * |p 0| * |p 1| := by
            positivity
          nlinarith [sq_abs (p 0), sq_abs (p 1)]
        have h8 : |p 0| + |p 1| ≤ 52 := by linarith
        have h9 : ‖p‖ ^ 2 ≤ 52 ^ 2 := by
          calc
            ‖p‖ ^ 2 =
                (p 0) ^ 2 + (p 1) ^ 2 := by
                  rw [h5, h5']
            _ ≤ (|p 0| + |p 1|) ^ 2 := h6
            _ ≤ 52 ^ 2 := by gcongr
        have h10 : 0 ≤ ‖p‖ := by positivity
        nlinarith
      exact h4
    have h_bdd :
        Bornology.IsBounded section7ProjectionRectangle :=
      Metric.isBounded_closedBall.subset h1
    dsimp only [V]
    exact h_bdd.measure_lt_top.ne
  let C : ℝ := 12 * V.toReal
  have hC_nonneg : 0 ≤ C := by positivity
  rcases projected_fiber_levelCount_selection
      heta C hC_nonneg with
    ⟨delta₀, hdelta₀_pos, hdelta₀_lt_one, h_main⟩
  refine ⟨delta₀, hdelta₀_pos, hdelta₀_lt_one, ?_⟩
  intro delta hdelta_pos hdelta_le F hF_nonempty Y hY_dense
  have hdelta_le_one : delta ≤ 1 := by linarith
  have hF_mass_eq :
      F.toBodyFamily.mass =
        F.enncard * Kakeya.deltaTubeVolume delta :=
    tubeFamily_mass_eq_nominal F
  have hvol_pos : 0 < Kakeya.deltaTubeVolume delta :=
    (tube_volume_scaling.2.1 delta hdelta_pos hdelta_le_one).1
  have hvol_ne_top : Kakeya.deltaTubeVolume delta ≠ ⊤ :=
    (tube_volume_scaling.2.1 delta hdelta_pos hdelta_le_one).2
  have hF_enncard_pos : 0 < F.enncard := by
    have hF_card_pos : 0 < F.card := hF_nonempty
    simpa [Kakeya.Streamlined.TubeFamily.enncard] using
      hF_card_pos
  have hF_enncard_ne_top : F.enncard ≠ ⊤ := by
    simp [Kakeya.Streamlined.TubeFamily.enncard] <;>
      exact ENNReal.natCast_ne_top _
  have hF_mass_pos : 0 < F.toBodyFamily.mass := by
    rw [hF_mass_eq]
    exact ENNReal.mul_pos hF_enncard_pos.ne' hvol_pos.ne'
  have hF_mass_ne_top : F.toBodyFamily.mass ≠ ⊤ := by
    rw [hF_mass_eq]
    exact ENNReal.mul_ne_top hF_enncard_ne_top hvol_ne_top
  have hY_mass_pos : 0 < Y.mass := by
    have h1 :
        Kakeya.realRpowENN delta eta *
            F.toBodyFamily.mass ≤
          Y.mass :=
      hY_dense
    have h2 : 0 < Kakeya.realRpowENN delta eta := by
      simp [Kakeya.realRpowENN]
      positivity
    have h3 :
        0 < Kakeya.realRpowENN delta eta *
          F.toBodyFamily.mass :=
      ENNReal.mul_pos h2.ne' hF_mass_pos.ne'
    exact h3.trans_le h1
  have hY_mass_ne_zero : Y.mass ≠ 0 := hY_mass_pos.ne'
  have hY_mass_le_F : Y.mass ≤ F.toBodyFamily.mass := by
    simp only [Kakeya.Streamlined.Shading.mass,
      Kakeya.Streamlined.BodyFamily.mass]
    apply Finset.sum_le_sum
    intro i _
    exact MeasureTheory.measure_mono (Y.subset_body i)
  have hY_mass_ne_top : Y.mass ≠ ⊤ :=
    ne_top_of_le_ne_top hF_mass_ne_top hY_mass_le_F
  rcases h_main delta hdelta_pos hdelta_le with
    ⟨levelCount, h_lc1, h_lc2⟩
  let threshold : ENNReal :=
    ENNReal.ofReal (6 * delta) * F.enncard *
      (2 ^ levelCount : ENNReal)⁻¹
  have h_pow_ne_zero : (2 ^ levelCount : ENNReal) ≠ 0 := by
    have h : 0 < (2 ^ levelCount : ENNReal) := by positivity
    exact h.ne'
  have h_pow_ne_top : (2 ^ levelCount : ENNReal) ≠ ⊤ := by
    exact_mod_cast ENNReal.natCast_ne_top (2 ^ levelCount)
  have h_thresh_ne_zero : threshold ≠ 0 := by
    have h1 : 0 < ENNReal.ofReal (6 * delta) :=
      ENNReal.ofReal_pos.mpr (by linarith)
    have h1' : ENNReal.ofReal (6 * delta) ≠ 0 := h1.ne'
    have h2 : F.enncard ≠ 0 := hF_enncard_pos.ne'
    have h3 : (2 ^ levelCount : ENNReal)⁻¹ ≠ 0 :=
      ENNReal.inv_ne_zero.mpr h_pow_ne_top
    have h12 :
        ENNReal.ofReal (6 * delta) * F.enncard ≠ 0 :=
      mul_ne_zero h1' h2
    have h123 :
        (ENNReal.ofReal (6 * delta) * F.enncard) *
            (2 ^ levelCount : ENNReal)⁻¹ ≠
          0 :=
      mul_ne_zero h12 h3
    simpa [threshold] using h123
  have h_thresh_ne_top : threshold ≠ ⊤ := by
    apply ENNReal.mul_ne_top
    · apply ENNReal.mul_ne_top
      · exact ENNReal.ofReal_ne_top
      · exact hF_enncard_ne_top
    · exact ENNReal.inv_ne_top.mpr h_pow_ne_zero
  have h_cap :
      ENNReal.ofReal (6 * delta) * F.enncard ≤
        threshold * (2 ^ levelCount : ENNReal) := by
    have h4 :
        threshold * (2 ^ levelCount : ENNReal) =
          ENNReal.ofReal (6 * delta) * F.enncard := by
      simp only [threshold]
      have h5 :
          ((ENNReal.ofReal (6 * delta) * F.enncard) *
                (2 ^ levelCount : ENNReal)⁻¹) *
              (2 ^ levelCount : ENNReal) =
            (ENNReal.ofReal (6 * delta) * F.enncard) *
              ((2 ^ levelCount : ENNReal)⁻¹ *
                (2 ^ levelCount : ENNReal)) := by
        rw [mul_assoc]
      rw [h5]
      have h6 :
          (2 ^ levelCount : ENNReal)⁻¹ *
              (2 ^ levelCount : ENNReal) =
            1 :=
        ENNReal.inv_mul_cancel h_pow_ne_zero h_pow_ne_top
      rw [h6, mul_one]
    rw [h4]
  have h_vol_lower :
      ENNReal.ofReal (delta ^ 2) ≤
        Kakeya.deltaTubeVolume delta :=
    canonical_volume_lower hdelta_pos
  have hF_mass_lower :
      F.enncard * ENNReal.ofReal (delta ^ 2) ≤
        F.toBodyFamily.mass := by
    rw [hF_mass_eq]
    gcongr
  have h_rpow2 :
      Kakeya.realRpowENN delta 2 =
        ENNReal.ofReal (delta ^ 2) := by
    simp [Kakeya.realRpowENN] <;> norm_cast
  have h_rpow_add :
      Kakeya.realRpowENN delta (eta + 2) =
        Kakeya.realRpowENN delta eta *
          Kakeya.realRpowENN delta 2 :=
    realRpowENN_add hdelta_pos eta 2
  have hY_lower :
      F.enncard * Kakeya.realRpowENN delta (eta + 2) ≤
        Y.mass := by
    have h5 :
        F.enncard * Kakeya.realRpowENN delta (eta + 2) ≤
          F.toBodyFamily.mass *
            Kakeya.realRpowENN delta eta := by
      rw [h_rpow_add, h_rpow2]
      have h6 :
          F.enncard *
                (Kakeya.realRpowENN delta eta *
                  ENNReal.ofReal (delta ^ 2)) ≤
            F.toBodyFamily.mass *
              Kakeya.realRpowENN delta eta := by
        have h61 :
            F.enncard *
                  (Kakeya.realRpowENN delta eta *
                    ENNReal.ofReal (delta ^ 2)) =
                (F.enncard * ENNReal.ofReal (delta ^ 2)) *
                  Kakeya.realRpowENN delta eta := by
          ring
        rw [h61]
        exact mul_le_mul_right'
          hF_mass_lower (Kakeya.realRpowENN delta eta)
      simpa [mul_assoc] using h6
    have h7 :
        F.toBodyFamily.mass * Kakeya.realRpowENN delta eta ≤
          Y.mass := by
      have h8 :
          Kakeya.realRpowENN delta eta *
              F.toBodyFamily.mass ≤
            Y.mass :=
        hY_dense
      have h9 :
          Kakeya.realRpowENN delta eta *
              F.toBodyFamily.mass =
            F.toBodyFamily.mass *
              Kakeya.realRpowENN delta eta := by
        ring
      rw [h9] at h8
      exact h8
    exact h5.trans h7
  have hV_eq :
      V = ENNReal.ofReal V.toReal :=
    (ENNReal.ofReal_toReal hV_ne_top).symm
  have h10 :
      12 * ENNReal.ofReal delta * V *
            (2 ^ levelCount : ENNReal)⁻¹ ≤
        Kakeya.realRpowENN delta (eta + 2) := by
    rw [hV_eq]
    have h11 :
        (12 : ENNReal) * ENNReal.ofReal delta *
            ENNReal.ofReal V.toReal =
          ENNReal.ofReal (12 * delta * V.toReal) := by
      have h11a :
          (12 : ENNReal) * ENNReal.ofReal delta =
            ENNReal.ofReal (12 * delta) := by
        have h12 :
            (12 : ENNReal) = ENNReal.ofReal (12 : ℝ) := by
          norm_cast
        rw [h12]
        have h13 :
            ENNReal.ofReal (12 : ℝ) *
                ENNReal.ofReal delta =
              ENNReal.ofReal ((12 : ℝ) * delta) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
        rw [h13] <;> norm_cast
      rw [h11a]
      rw [← ENNReal.ofReal_mul (by positivity)] <;> ring
    have h12 :
        Kakeya.realRpowENN delta (eta + 2) *
              (2 ^ levelCount : ENNReal) =
            ENNReal.ofReal
              (delta ^ (eta + 2) * (2 : ℝ) ^ levelCount) := by
      have h13 :
          Kakeya.realRpowENN delta (eta + 2) =
            ENNReal.ofReal (delta ^ (eta + 2)) := by
        simp [Kakeya.realRpowENN]
      rw [h13]
      have h14 :
          (2 ^ levelCount : ENNReal) =
            ENNReal.ofReal ((2 : ℝ) ^ levelCount) := by
        norm_cast
      rw [h14, ← ENNReal.ofReal_mul (by positivity)] <;> ring
    have h15 :
        12 * delta * V.toReal ≤
          delta ^ (eta + 2) * (2 : ℝ) ^ levelCount := by
      have h16 :
          C / delta ^ (eta + 1) ≤
            (2 ^ levelCount : ℝ) :=
        h_lc1
      have h17 : C = 12 * V.toReal := by rfl
      rw [h17] at h16
      have h18 :
          12 * V.toReal ≤
            delta ^ (eta + 1) * (2 ^ levelCount : ℝ) := by
        calc
          12 * V.toReal =
              (12 * V.toReal / delta ^ (eta + 1)) *
                delta ^ (eta + 1) := by
                  field_simp [hdelta_pos.ne'] <;> ring
          _ ≤ (2 ^ levelCount : ℝ) *
                delta ^ (eta + 1) := by
              gcongr
          _ = delta ^ (eta + 1) *
                (2 ^ levelCount : ℝ) := by
              ring
      calc
        12 * delta * V.toReal =
            delta * (12 * V.toReal) := by ring
        _ ≤ delta *
              (delta ^ (eta + 1) *
                (2 ^ levelCount : ℝ)) := by
            gcongr
        _ = delta ^ (eta + 2) *
              (2 ^ levelCount : ℝ) := by
          have h19 :
              delta * delta ^ (eta + 1) =
                delta ^ (eta + 2) := by
            have h20 :
                delta ^ (1 : ℝ) * delta ^ (eta + 1) =
                  delta ^ ((1 : ℝ) + (eta + 1)) := by
              rw [← Real.rpow_add hdelta_pos]
            have h21 : delta ^ (1 : ℝ) = delta :=
              Real.rpow_one delta
            rw [h21] at h20
            have h22 : (1 : ℝ) + (eta + 1) = eta + 2 := by
              ring
            rw [h22] at h20
            exact h20
          have h23 :
              delta *
                  (delta ^ (eta + 1) *
                    (2 ^ levelCount : ℝ)) =
                (delta * delta ^ (eta + 1)) *
                  (2 ^ levelCount : ℝ) := by
            ring
          rw [h23, h19] <;> ring
    have h20 :
        ENNReal.ofReal (12 * delta * V.toReal) ≤
          Kakeya.realRpowENN delta (eta + 2) *
            (2 ^ levelCount : ENNReal) := by
      rw [h12]
      exact ENNReal.ofReal_mono h15
    have h21 :
        ENNReal.ofReal (12 * delta * V.toReal) *
              (2 ^ levelCount : ENNReal)⁻¹ ≤
            Kakeya.realRpowENN delta (eta + 2) := by
      calc
        ENNReal.ofReal (12 * delta * V.toReal) *
              (2 ^ levelCount : ENNReal)⁻¹
            ≤ (Kakeya.realRpowENN delta (eta + 2) *
                (2 ^ levelCount : ENNReal)) *
              (2 ^ levelCount : ENNReal)⁻¹ := by
                gcongr
        _ = Kakeya.realRpowENN delta (eta + 2) := by
          rw [mul_assoc,
            ENNReal.mul_inv_cancel h_pow_ne_zero h_pow_ne_top,
            mul_one]
    rw [← h11] at h21
    exact h21
  have h_low_tail : 2 * (threshold * V) ≤ Y.mass := by
    have h21 :
        2 * (threshold * V) =
          12 * ENNReal.ofReal delta * F.enncard * V *
            (2 ^ levelCount : ENNReal)⁻¹ := by
      simp only [threshold]
      have h22 :
          ENNReal.ofReal (6 * delta) =
            6 * ENNReal.ofReal delta := by
        rw [ENNReal.ofReal_mul (by linarith)]
        norm_cast
      rw [h22]
      ring
    rw [h21]
    have h23 :
        F.enncard *
              (12 * ENNReal.ofReal delta * V *
                (2 ^ levelCount : ENNReal)⁻¹) ≤
            F.enncard * Kakeya.realRpowENN delta (eta + 2) := by
      gcongr
    have h24 :
        F.enncard *
              (12 * ENNReal.ofReal delta * V *
                (2 ^ levelCount : ENNReal)⁻¹) =
            12 * ENNReal.ofReal delta * F.enncard * V *
              (2 ^ levelCount : ENNReal)⁻¹ := by
      ring
    rw [h24] at h23
    exact h23.trans hY_lower
  have h_loss :
      projectedFiberBandLoss levelCount ≤
        Kakeya.realRpowENN delta (-eta) := by
    have h25 :
        projectedFiberBandLoss levelCount =
          2 * (levelCount + 1 : ENNReal) := by
      simp [projectedFiberBandLoss] <;> norm_cast
    rw [h25]
    have h26 :
        2 * (levelCount + 1 : ENNReal) =
          ENNReal.ofReal (2 * ((levelCount : ℝ) + 1)) := by
      norm_cast
    rw [h26]
    have h27 :
        2 * ((levelCount : ℝ) + 1) ≤ delta ^ (-eta) :=
      h_lc2
    have h28 :
        ENNReal.ofReal (2 * ((levelCount : ℝ) + 1)) ≤
          ENNReal.ofReal (delta ^ (-eta)) :=
      ENNReal.ofReal_mono h27
    simpa [Kakeya.realRpowENN] using h28
  have h_final :
      threshold ≠ 0 ∧
        threshold ≠ ⊤ ∧
        Y.mass ≠ 0 ∧
        Y.mass ≠ ⊤ ∧
        2 *
              (threshold *
                MeasureTheory.volume section7ProjectionRectangle) ≤
            Y.mass ∧
        ENNReal.ofReal (6 * delta) * F.enncard ≤
            threshold * (2 ^ levelCount : ENNReal) ∧
        projectedFiberBandLoss levelCount ≤
          Kakeya.realRpowENN delta (-eta) := by
    exact
      ⟨h_thresh_ne_zero, h_thresh_ne_top,
        hY_mass_ne_zero, hY_mass_ne_top,
        h_low_tail, h_cap, h_loss⟩
  exact ⟨threshold, levelCount, h_final⟩

end Kakeya.Assouad
