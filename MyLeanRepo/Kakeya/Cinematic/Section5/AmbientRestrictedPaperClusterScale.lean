import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientRestrictedPaperClusterScaleInputs
import MyLeanRepo.Kakeya.Cinematic.Section5.SelectedIncidenceCanonicalCutoffsInputs
import Mathlib.Tactic

/-!
# Paper cluster radius and Proposition 26 parameter

Pure scale arithmetic behind the variable cluster radius in the
nonconcentration-to-Proposition-26 transition.
-/

namespace Kakeya.Cinematic

lemma ambientRestrictedPaperClusterRadius_metricCut
    (t epsilon logLoss fiberRatio : ℝ)
    (_ht : 0 < t)
    (_hepsilon : 0 < epsilon)
    (hlogLoss : 0 < logLoss)
    (hfiberRatio : 0 < fiberRatio) :
    11 *
        ambientRestrictedPaperClusterRadius
          t epsilon logLoss fiberRatio =
      selectedIncidenceMetricCut logLoss fiberRatio epsilon * t / 8 := by
  dsimp only [ambientRestrictedPaperClusterRadius,
    selectedIncidenceMetricCut]
  let x : ℝ := 24 * logLoss * fiberRatio
  have hx : 0 < x := by
    dsimp only [x]
    positivity
  have hpow :
      Real.rpow (1 / x) (1 / epsilon) =
        Real.rpow x (-1 / epsilon) := by
    calc
      Real.rpow (1 / x) (1 / epsilon) =
          Real.rpow x⁻¹ (1 / epsilon) := by rw [one_div]
      _ = (Real.rpow x (1 / epsilon))⁻¹ :=
        Real.inv_rpow hx.le (1 / epsilon)
      _ = Real.rpow x (-(1 / epsilon)) :=
        (Real.rpow_neg hx.le (1 / epsilon)).symm
      _ = Real.rpow x (-1 / epsilon) := by
        congr 1
        ring
  rw [show 24 * logLoss * fiberRatio = x by rfl, hpow]
  ring

lemma delta_lt_eleven_paperClusterRadius_of_metricCut
    (K delta t epsilon logLoss fiberRatio : ℝ)
    (hK : 1 ≤ K)
    (hdelta : 0 < delta)
    (ht : 0 < t)
    (hepsilon : 0 < epsilon)
    (hlogLoss : 0 < logLoss)
    (hfiberRatio : 0 < fiberRatio)
    (hmetric :
      480 * K * delta ≤
        selectedIncidenceMetricCut
          logLoss fiberRatio epsilon * t) :
    delta <
      11 *
        ambientRestrictedPaperClusterRadius
          t epsilon logLoss fiberRatio := by
  have hscaled :
      60 * K * delta ≤
        selectedIncidenceMetricCut
          logLoss fiberRatio epsilon * t / 8 := by
    linarith
  rw [ambientRestrictedPaperClusterRadius_metricCut
    t epsilon logLoss fiberRatio ht hepsilon hlogLoss hfiberRatio]
  have hKdelta : delta ≤ K * delta :=
    by
      simpa using mul_le_mul_of_nonneg_right hK hdelta.le
  nlinarith

lemma ambientRestrictedPaperClusterParameter_eq
    (C_R t epsilon logLoss fiberRatio : ℝ)
    (ht : 0 < t)
    (hepsilon : 0 < epsilon)
    (hlogLoss : 0 < logLoss)
    (hfiberRatio : 0 < fiberRatio) :
    ambientRestrictedPaperClusterParameter
        C_R t epsilon logLoss fiberRatio =
      C_R * 22 *
        Real.rpow
          (24 * logLoss * fiberRatio)
          (1 / epsilon) := by
  let x : ℝ := 24 * logLoss * fiberRatio
  have hx : 0 < x := by
    dsimp only [x]
    positivity
  have hradius :
      ambientRestrictedPaperClusterRadius
          t epsilon logLoss fiberRatio =
        t / 176 * Real.rpow x (-1 / epsilon) := by
    simp only [ambientRestrictedPaperClusterRadius, x]
  have hinverse :
      (Real.rpow x (-1 / epsilon))⁻¹ =
        Real.rpow x (1 / epsilon) := by
    have hneg :
        Real.rpow x (-1 / epsilon) =
          (Real.rpow x (1 / epsilon))⁻¹ := by
      have hexponent : -1 / epsilon = -(1 / epsilon) := by ring
      rw [hexponent]
      exact Real.rpow_neg hx.le (1 / epsilon)
    rw [hneg]
    exact inv_inv _
  rw [ambientRestrictedPaperClusterParameter, hradius]
  have hpow : Real.rpow x (-1 / epsilon) ≠ 0 :=
    (Real.rpow_pos_of_pos hx _).ne'
  have hdivision :
      C_R * t /
          (8 * (t / 176 * Real.rpow x (-1 / epsilon))) =
        C_R * 22 *
          (Real.rpow x (-1 / epsilon))⁻¹ := by
    field_simp [ht.ne', hpow]
    ring
  rw [hdivision, hinverse]

lemma ambientRestrictedPaperFiberCoefficient_eq_inv_six_logLoss
    (t epsilon logLoss fiberRatio : ℝ)
    (ht : 0 < t)
    (hepsilon : 0 < epsilon)
    (hlogLoss : 0 < logLoss)
    (hfiberRatio : 0 < fiberRatio) :
    ambientRestrictedPaperFiberCoefficient
        t epsilon logLoss fiberRatio =
      1 / (6 * logLoss) := by
  set x : ℝ := 24 * logLoss * fiberRatio with hx_def
  set y : ℝ := -1 / epsilon with hy_def
  have hx_pos : 0 < x := by
    dsimp only [x]
    positivity
  have hradius :
      ambientRestrictedPaperClusterRadius
          t epsilon logLoss fiberRatio =
        t / 176 * Real.rpow x y := by
    rw [ambientRestrictedPaperClusterRadius, hx_def, hy_def]
  have hscale :
      176 *
            ambientRestrictedPaperClusterRadius
              t epsilon logLoss fiberRatio /
          t =
        Real.rpow x y := by
    rw [hradius]
    field_simp [ht.ne']
  have hpow :
      Real.rpow (Real.rpow x y) epsilon = x⁻¹ := by
    have h1 :
        Real.rpow (Real.rpow x y) epsilon =
          Real.rpow x (y * epsilon) := by
      exact (Real.rpow_mul hx_pos.le y epsilon).symm
    rw [h1]
    have h2 : y * epsilon = -1 := by
      simp [hy_def]
      field_simp [hepsilon.ne']
    rw [h2]
    exact Real.rpow_neg_one x
  rw [ambientRestrictedPaperFiberCoefficient, hscale, hpow, hx_def]
  field_simp [hlogLoss.ne', hfiberRatio.ne']
  norm_num

theorem ambient_restricted_paper_cluster_scale :
    AmbientRestrictedPaperClusterScaleStatement := by
  intro C_R delta t Delta epsilon logLoss fiberRatio
    hCR hdelta ht hDelta hdelta_le_Delta hDelta_le_t hepsilon hlogLoss
    hfiberRatio
  set x : ℝ := 24 * logLoss * fiberRatio with hx_def
  set y : ℝ := -1 / epsilon with hy_def
  set radius : ℝ :=
    ambientRestrictedPaperClusterRadius t epsilon logLoss fiberRatio
      with hradius_def
  set A : ℝ :=
    ambientRestrictedPaperClusterParameter
      C_R t epsilon logLoss fiberRatio
      with hA_def
  set coefficient : ℝ :=
    ambientRestrictedPaperFiberCoefficient
      t epsilon logLoss fiberRatio
      with hcoeff_def

  have hx_pos : 0 < x := by positivity
  have hx_gt_one : 1 < x := by
    dsimp only [x]
    have h1 : 24 * logLoss * fiberRatio ≥ 24 := by
      have h2 : logLoss ≥ 1 := hlogLoss
      have h3 : fiberRatio ≥ 1 := hfiberRatio
      nlinarith
    nlinarith
  have hy_neg : y < 0 := by
    dsimp only [y]
    have h1 : -1 / epsilon < 0 := by
      apply div_neg_of_neg_of_pos
      · linarith
      · linarith
    exact h1
  have h_inv_eps_pos : 0 < 1 / epsilon := by positivity

  have hradius_eq : radius = t / 176 * x ^ y := by
    rw [hradius_def, ambientRestrictedPaperClusterRadius, hx_def, hy_def]
    <;> rfl

  have h1_radius_pos : 0 < radius := by
    rw [hradius_eq]
    have h1 : 0 < t / 176 := by positivity
    have h2 : 0 < x ^ y := Real.rpow_pos_of_pos hx_pos y
    positivity

  have h2_11radius : 11 * radius < t / 8 := by
    rw [hradius_eq]
    have h3 : x ^ y < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg hx_gt_one hy_neg
    have h4 : t / 176 * x ^ y < t / 176 := by
      have h5 : 0 < t / 176 := by positivity
      nlinarith
    have h6 : 11 * (t / 176 * x ^ y) < t / 8 := by
      nlinarith
    exact h6

  have h_inv_rpow : (x ^ y)⁻¹ = x ^ (1 / epsilon) := by
    have h7 : x ^ y = (x ^ (1 / epsilon))⁻¹ := by
      have h8 : y = -(1 / epsilon) := by
        simp [hy_def]
        field_simp
      rw [h8, Real.rpow_neg (by linarith)]
    rw [h7]
    have h9 : 0 < x ^ (1 / epsilon) :=
      Real.rpow_pos_of_pos hx_pos (1 / epsilon)
    field_simp [h9.ne']

  have hA_param : A = C_R * t / (8 * radius) := by
    rw [hA_def, ambientRestrictedPaperClusterParameter, ← hradius_def]

  have hA_eq : A = C_R * 22 * x ^ (1 / epsilon) := by
    rw [hA_param, hradius_eq]
    have h10 : 8 * (t / 176 * x ^ y) = t / 22 * x ^ y := by
      ring
    rw [h10]
    have h11 :
        C_R * t / (t / 22 * x ^ y) =
          C_R * 22 * (x ^ y)⁻¹ := by
      have h12 : t ≠ 0 := by linarith
      have h13 : x ^ y ≠ 0 :=
        (Real.rpow_pos_of_pos hx_pos y).ne'
      field_simp [h12, h13]
    rw [h11, h_inv_rpow]

  have h3_A_ge_one : 1 ≤ A := by
    rw [hA_eq]
    have h14 : 1 ≤ x ^ (1 / epsilon) :=
      Real.one_le_rpow (by linarith) (by positivity)
    nlinarith

  have h4 : C_R * t / A = 8 * radius := by
    rw [hA_param]
    have h15 : C_R * t ≠ 0 := by positivity
    have h16 : 8 * radius ≠ 0 := by positivity
    field_simp [h15, h16]

  have h5 : Delta ≤ A * (C_R * t) := by
    have h17 : 1 ≤ A * C_R := by
      have h18 : 1 ≤ A := h3_A_ge_one
      have h19 : 1 ≤ C_R := hCR
      nlinarith
    have h20 : A * (C_R * t) = (A * C_R) * t := by ring
    rw [h20]
    have h21 : (A * C_R) * t ≥ t := by
      have h22 : 0 < t := ht
      nlinarith
    linarith [hDelta_le_t]

  have hcoeff_param :
      coefficient =
        4 * (176 * radius / t) ^ epsilon * fiberRatio := by
    rw [hcoeff_def, ambientRestrictedPaperFiberCoefficient, ← hradius_def]
    <;> rfl

  have hcoeff_simp : coefficient = 1 / (6 * logLoss) := by
    rw [hcoeff_param]
    have h24 : 176 * radius / t = x ^ y := by
      rw [hradius_eq]
      have h25 : t ≠ 0 := by linarith
      field_simp [h25]
    rw [h24]
    have h26 : (x ^ y) ^ epsilon = x⁻¹ := by
      have h27 : (x ^ y) ^ epsilon = x ^ (y * epsilon) := by
        rw [← Real.rpow_mul (by linarith) y epsilon]
      rw [h27]
      have h28 : y * epsilon = -1 := by
        simp [hy_def]
        field_simp [hepsilon.ne']
      rw [h28, Real.rpow_neg_one]
    rw [h26]
    have h29 : x = 24 * logLoss * fiberRatio := by simp [hx_def]
    rw [h29]
    have h30 : fiberRatio ≠ 0 := by linarith
    have h31 : logLoss ≠ 0 := by linarith
    field_simp [h30, h31] <;> norm_num

  have h6 : 4 * logLoss * coefficient ≤ 1 := by
    rw [hcoeff_simp]
    have h32 : logLoss ≠ 0 := by linarith
    field_simp [h32] <;> norm_num

  exact ⟨h1_radius_pos, h2_11radius, h3_A_ge_one, h4, h5, h6⟩

end Kakeya.Cinematic
