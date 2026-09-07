import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedLargeBinMassThresholdInputs

/-!
# Cubic mass threshold for a large fixed ambient bin
-/

namespace Kakeya.Cinematic

lemma ambient_restricted_large_bin_mass_smallness
    (delta epsilon epsilon' logLoss D C_KT scale : ℝ)
    (hdelta : 0 < delta)
    (hscale : 0 < scale)
    (hepsilon' : 0 < epsilon')
    (hD : 0 ≤ D)
    (hC_KT : 0 ≤ C_KT)
    (hlogSmall :
      logLoss * Real.rpow scale epsilon' *
          Real.rpow delta epsilon' ≤
        1)
    (hfixedSmall :
      (D ^ 3 * Real.rpow C_KT (5 / 2 : ℝ) *
          Real.rpow scale (3 - epsilon')) *
          Real.rpow delta (1 / 2 + epsilon - epsilon') ≤
        1) :
    logLoss * D ^ 3 *
          Real.rpow C_KT (5 / 2 : ℝ) *
          scale ^ 3 *
          Real.rpow delta (1 / 2 + epsilon) ≤
      1 := by
  have hscalePower :
      Real.rpow scale epsilon' *
          Real.rpow scale (3 - epsilon') =
        scale ^ 3 := by
    calc
      Real.rpow scale epsilon' *
          Real.rpow scale (3 - epsilon') =
        Real.rpow scale (epsilon' + (3 - epsilon')) :=
          (Real.rpow_add hscale epsilon' (3 - epsilon')).symm
      _ = Real.rpow scale (3 : ℝ) := by
        congr 1
        ring
      _ = scale ^ 3 := Real.rpow_natCast scale 3
  have hdeltaPower :
      Real.rpow delta epsilon' *
          Real.rpow delta (1 / 2 + epsilon - epsilon') =
        Real.rpow delta (1 / 2 + epsilon) := by
    calc
      Real.rpow delta epsilon' *
          Real.rpow delta (1 / 2 + epsilon - epsilon') =
        Real.rpow delta
          (epsilon' + (1 / 2 + epsilon - epsilon')) := by
            exact
              (Real.rpow_add hdelta epsilon'
                (1 / 2 + epsilon - epsilon')).symm
      _ = Real.rpow delta (1 / 2 + epsilon) := by
        congr 1
        ring
  have hfixedNonneg :
      0 ≤
        (D ^ 3 * Real.rpow C_KT (5 / 2 : ℝ) *
          Real.rpow scale (3 - epsilon')) *
          Real.rpow delta (1 / 2 + epsilon - epsilon') := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (pow_nonneg hD 3)
          (Real.rpow_nonneg hC_KT _))
        (Real.rpow_nonneg hscale.le _))
      (Real.rpow_nonneg hdelta.le _)
  calc
    logLoss * D ^ 3 *
          Real.rpow C_KT (5 / 2 : ℝ) *
          scale ^ 3 *
          Real.rpow delta (1 / 2 + epsilon) =
        (logLoss * Real.rpow scale epsilon' *
            Real.rpow delta epsilon') *
          ((D ^ 3 * Real.rpow C_KT (5 / 2 : ℝ) *
              Real.rpow scale (3 - epsilon')) *
            Real.rpow delta
              (1 / 2 + epsilon - epsilon')) := by
      rw [← hscalePower, ← hdeltaPower]
      ring
    _ ≤
        1 *
          ((D ^ 3 * Real.rpow C_KT (5 / 2 : ℝ) *
              Real.rpow scale (3 - epsilon')) *
            Real.rpow delta
              (1 / 2 + epsilon - epsilon')) := by
      exact mul_le_mul_of_nonneg_right hlogSmall hfixedNonneg
    _ ≤ 1 * 1 := by
      exact mul_le_mul_of_nonneg_left hfixedSmall (by norm_num)
    _ = 1 := by ring

theorem ambient_restricted_large_bin_mass_threshold :
    AmbientRestrictedLargeBinMassThresholdStatement := by
  intro delta deltaVert epsilon mu logLoss D C_KT scale total
    hdelta hdeltaVert hmu hlogLoss hD hCKT hscale
    hdv hmu_bound hsmall hstrict
  set localTarget :=
    (delta ^ (-epsilon) * mu ^ (-3 / 2 : ℝ)) /
      (logLoss * (D ^ 3 * (C_KT / delta)))
    with hlocal_def
  set bound :=
    C_KT ^ (-5 / 2 : ℝ) *
      delta ^ (5 / 2 - epsilon) /
      (logLoss * D ^ 3)
    with hbound_def
  have h_pos1 : 0 < logLoss * D ^ 3 * C_KT := by positivity
  have h_pos2 : 0 < C_KT / delta := by positivity
  have h_bound_pos : 0 < bound := by positivity
  have h_rpow_add :
      ∀ (x y z : ℝ), 0 < x →
        x ^ y * x ^ z = x ^ (y + z) := by
    intro x y z hx
    exact (Real.rpow_add hx y z).symm
  have h_rpow_one : ∀ x : ℝ, x ^ (1 : ℝ) = x := by
    intro x
    have h1 : x ^ (1 : ℝ) = x ^ (1 : ℕ) := by
      norm_cast
    rw [h1]
    simp
  have h_anti :
      AntitoneOn (fun x : ℝ => x ^ (-3 / 2 : ℝ)) (Set.Ioi 0) :=
    Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by norm_num)
  have h21 :
      (C_KT / delta) ^ (-3 / 2 : ℝ) ≤
        mu ^ (-3 / 2 : ℝ) :=
    h_anti hmu h_pos2 hmu_bound
  have h_neg :
      delta ^ (-3 / 2 : ℝ) =
        (delta ^ (3 / 2 : ℝ))⁻¹ := by
    have h9 : (-3 / 2 : ℝ) = -(3 / 2 : ℝ) := by
      norm_num
    rw [h9]
    exact Real.rpow_neg hdelta.le (3 / 2 : ℝ)
  have h22 :
      (C_KT / delta) ^ (-3 / 2 : ℝ) =
        C_KT ^ (-3 / 2 : ℝ) *
          delta ^ (3 / 2 : ℝ) := by
    have h_div :
        (C_KT / delta) ^ (-3 / 2 : ℝ) =
          C_KT ^ (-3 / 2 : ℝ) /
            delta ^ (-3 / 2 : ℝ) :=
      Real.div_rpow (by positivity) (by positivity) _
    rw [h_div, h_neg]
    have h_pos3 : 0 < delta ^ (3 / 2 : ℝ) :=
      Real.rpow_pos_of_pos hdelta _
    field_simp [h_pos3.ne']
  have h_mu_lower :
      C_KT ^ (-3 / 2 : ℝ) *
          delta ^ (3 / 2 : ℝ) ≤
        mu ^ (-3 / 2 : ℝ) := by
    linarith [h21, h22]
  have h_mul1 :
      C_KT ^ (5 / 2 : ℝ) *
          C_KT ^ (-5 / 2 : ℝ) = 1 := by
    rw [h_rpow_add C_KT (5 / 2) (-5 / 2) hCKT]
    norm_num
  have h_mul2 :
      delta ^ (1 / 2 + epsilon) *
          delta ^ (5 / 2 - epsilon) =
        delta ^ (3 : ℝ) := by
    rw [h_rpow_add delta
      (1 / 2 + epsilon) (5 / 2 - epsilon) hdelta]
    ring_nf
  have h_rpow1 :
      delta ^ (-epsilon) * delta ^ (3 / 2 : ℝ) =
        delta ^ (3 / 2 - epsilon) := by
    rw [h_rpow_add delta (-epsilon) (3 / 2) hdelta]
    ring_nf
  have h_rpow2 :
      C_KT ^ (-3 / 2 : ℝ) / C_KT =
        C_KT ^ (-5 / 2 : ℝ) := by
    have h :
        C_KT ^ (-3 / 2 : ℝ) / C_KT =
          C_KT ^ (-3 / 2 : ℝ) * C_KT ^ (-1 : ℝ) := by
      simp [Real.rpow_neg hCKT.le]
      ring
    rw [h, h_rpow_add C_KT (-3 / 2) (-1) hCKT]
    norm_num
  have h_rpow3 :
      delta ^ (3 / 2 - epsilon) * delta =
        delta ^ (5 / 2 - epsilon) := by
    have h :
        delta ^ (3 / 2 - epsilon) * delta ^ (1 : ℝ) =
          delta ^ (5 / 2 - epsilon) := by
      rw [h_rpow_add delta
        (3 / 2 - epsilon) (1 : ℝ) hdelta]
      ring_nf
    rw [h_rpow_one delta] at h
    exact h
  have h_factor :
      (logLoss * D ^ 3 * C_KT ^ (5 / 2 : ℝ) *
          scale ^ 3 * delta ^ (1 / 2 + epsilon)) *
          (C_KT ^ (-5 / 2 : ℝ) *
            delta ^ (5 / 2 - epsilon) /
            (logLoss * D ^ 3)) =
        (C_KT ^ (5 / 2 : ℝ) *
            C_KT ^ (-5 / 2 : ℝ)) *
          (delta ^ (1 / 2 + epsilon) *
            delta ^ (5 / 2 - epsilon)) *
          scale ^ 3 := by
    field_simp [hlogLoss.ne', hD.ne']
  have h_claim1 : scale ^ 3 * delta ^ 3 ≤ bound := by
    have h :
        (logLoss * D ^ 3 * C_KT ^ (5 / 2 : ℝ) *
            scale ^ 3 * delta ^ (1 / 2 + epsilon)) *
            bound ≤
          bound := by
      have h' :=
        mul_le_mul_of_nonneg_right hsmall h_bound_pos.le
      simpa [one_mul] using h'
    have h_eq :
        (logLoss * D ^ 3 * C_KT ^ (5 / 2 : ℝ) *
            scale ^ 3 * delta ^ (1 / 2 + epsilon)) *
            bound =
          scale ^ 3 * delta ^ 3 := by
      simp only [hbound_def]
      rw [h_factor, h_mul1, h_mul2]
      have h5 : delta ^ (3 : ℝ) = delta ^ 3 := by
        norm_cast
      rw [h5]
      ring
    rw [h_eq] at h
    exact h
  have h_common :
      C_KT ^ (-3 / 2 : ℝ) *
            delta ^ (3 / 2 - epsilon) * delta /
            (logLoss * D ^ 3 * C_KT) =
        bound := by
    simp only [hbound_def]
    calc
      C_KT ^ (-3 / 2 : ℝ) *
            delta ^ (3 / 2 - epsilon) * delta /
            (logLoss * D ^ 3 * C_KT) =
          (C_KT ^ (-3 / 2 : ℝ) / C_KT) *
            (delta ^ (3 / 2 - epsilon) * delta) /
            (logLoss * D ^ 3) := by
        field_simp [hlogLoss.ne', hD.ne', hCKT.ne']
      _ =
          C_KT ^ (-5 / 2 : ℝ) *
            delta ^ (5 / 2 - epsilon) /
            (logLoss * D ^ 3) := by
        rw [h_rpow2, h_rpow3]
  have h_rhs :
      (delta ^ (-epsilon) *
          (C_KT ^ (-3 / 2 : ℝ) *
            delta ^ (3 / 2 : ℝ))) /
          (logLoss * (D ^ 3 * (C_KT / delta))) =
        C_KT ^ (-3 / 2 : ℝ) *
          delta ^ (3 / 2 - epsilon) * delta /
          (logLoss * D ^ 3 * C_KT) := by
    have h4 :
        logLoss * (D ^ 3 * (C_KT / delta)) =
          (logLoss * D ^ 3 * C_KT) / delta := by
      field_simp [hdelta.ne']
    rw [h4]
    have h5 :
        (delta ^ (-epsilon) *
            (C_KT ^ (-3 / 2 : ℝ) *
              delta ^ (3 / 2 : ℝ))) /
            ((logLoss * D ^ 3 * C_KT) / delta) =
          (delta ^ (-epsilon) *
              delta ^ (3 / 2 : ℝ) *
              C_KT ^ (-3 / 2 : ℝ) * delta) /
            (logLoss * D ^ 3 * C_KT) := by
      field_simp [h_pos1.ne', hdelta.ne']
    rw [h5, h_rpow1]
    ring
  have h_bound_eq :
      bound =
        (delta ^ (-epsilon) *
          (C_KT ^ (-3 / 2 : ℝ) *
            delta ^ (3 / 2 : ℝ))) /
          (logLoss * (D ^ 3 * (C_KT / delta))) := by
    calc
      bound =
          C_KT ^ (-3 / 2 : ℝ) *
            delta ^ (3 / 2 - epsilon) * delta /
            (logLoss * D ^ 3 * C_KT) :=
        h_common.symm
      _ =
          (delta ^ (-epsilon) *
            (C_KT ^ (-3 / 2 : ℝ) *
              delta ^ (3 / 2 : ℝ))) /
            (logLoss * (D ^ 3 * (C_KT / delta))) :=
        h_rhs.symm
  have h_claim2 : bound ≤ localTarget := by
    rw [h_bound_eq, hlocal_def]
    apply div_le_div_of_nonneg_right
    · have h_pos3 : 0 < delta ^ (-epsilon) :=
        Real.rpow_pos_of_pos hdelta _
      exact mul_le_mul_of_nonneg_left h_mu_lower h_pos3.le
    · positivity
  have h_dv3 :
      deltaVert ^ (3 : ℝ) =
        scale ^ 3 * delta ^ 3 := by
    rw [hdv]
    have h : (scale * delta) ^ (3 : ℝ) =
        (scale * delta) ^ 3 := by
      norm_cast
    rw [h]
    ring
  have h_main : deltaVert ^ (3 : ℝ) ≤ localTarget := by
    calc
      deltaVert ^ (3 : ℝ) =
          scale ^ 3 * delta ^ 3 := h_dv3
      _ ≤ bound := h_claim1
      _ ≤ localTarget := h_claim2
  have h7 :
      ENNReal.ofReal (deltaVert ^ (3 : ℝ)) ≤
        ENNReal.ofReal localTarget :=
    ENNReal.ofReal_mono h_main
  exact lt_of_le_of_lt h7 hstrict

end Kakeya.Cinematic
