import MyLeanRepo.Kakeya.Cinematic.Section5.SelectedIncidenceCanonicalCutoffsInputs

/-!
# Canonical good-pair cutoffs for selected incidence fibers
-/

namespace Kakeya.Cinematic

lemma pointwise_metricCut_of_representative_scale
    (K delta tRep exactT metricCut : ℝ)
    (hK : 1 ≤ K)
    (hdelta : 0 < delta)
    (htRep : 0 < tRep)
    (hexactT : 0 < exactT)
    (hrep : tRep ≤ 8 * exactT)
    (hscale : 480 * K * delta ≤ metricCut * tRep) :
    delta / exactT < metricCut := by
  have h8 : 8 * delta < metricCut * tRep := by
    apply lt_of_lt_of_le _ hscale
    nlinarith
  have hdiv : 8 * delta / tRep < metricCut := by
    apply (div_lt_iff₀ htRep).2
    simpa [mul_comm] using h8
  have hpoint : delta / exactT ≤ 8 * delta / tRep := by
    apply (div_le_div_iff₀ hexactT htRep).2
    nlinarith
  exact hpoint.trans_lt hdiv

lemma pointwise_tangencyCut_of_representative_scale
    (delta DeltaRep exactDelta tangencyCut : ℝ)
    (hexactDelta : 0 < exactDelta)
    (htangencyCut : 0 < tangencyCut)
    (hrep : DeltaRep ≤ 2 * exactDelta)
    (hscale : delta < tangencyCut * DeltaRep / 2) :
    delta / exactDelta < tangencyCut := by
  apply (div_lt_iff₀ hexactDelta).2
  calc
    delta < tangencyCut * DeltaRep / 2 := hscale
    _ ≤ tangencyCut * exactDelta := by
      have := mul_le_mul_of_nonneg_left hrep htangencyCut.le
      nlinarith

theorem selected_incidence_canonical_cutoffs :
    SelectedIncidenceCanonicalCutoffsStatement := by
  intro heavyLogLoss fiberRatio epsilon eta hH hF heps heta
  set Bm : ℝ := 1 / (24 * heavyLogLoss * fiberRatio) with hBm_def
  set Bt : ℝ := 1 / (24 * heavyLogLoss) with hBt_def
  have h_gt1 : 1 < 24 * heavyLogLoss * fiberRatio := by
    have h : 24 * heavyLogLoss * fiberRatio ≥ 24 := by nlinarith
    linarith
  have h_gt2 : 1 < 24 * heavyLogLoss := by
    have h : 24 * heavyLogLoss ≥ 24 := by nlinarith
    linarith
  have h_pos1 : 0 < 24 * heavyLogLoss * fiberRatio := by positivity
  have h_pos2 : 0 < 24 * heavyLogLoss := by positivity
  have hBm_pos : 0 < Bm := by positivity
  have hBt_pos : 0 < Bt := by positivity
  have hBm_nonneg : 0 ≤ Bm := by positivity
  have hBt_nonneg : 0 ≤ Bt := by positivity
  have hBm_lt_one : Bm < 1 := by
    rw [hBm_def]
    exact (div_lt_one (by positivity)).mpr h_gt1
  have hBt_lt_one : Bt < 1 := by
    rw [hBt_def]
    exact (div_lt_one (by positivity)).mpr h_gt2
  have h1 : 0 < 1 / epsilon := by positivity
  have h2 : 0 < 1 / eta := by positivity
  have h3 : (1 / epsilon) * epsilon = 1 := by
    field_simp [heps.ne']
  have h4 : (1 / eta) * eta = 1 := by
    field_simp [heta.ne']
  have h5 : 2 * selectedIncidenceMetricCut heavyLogLoss fiberRatio epsilon =
      Real.rpow Bm (1 / epsilon) := by
    simp [selectedIncidenceMetricCut, hBm_def]
  have h6 : selectedIncidenceTangencyCut heavyLogLoss eta =
      Real.rpow Bt (1 / eta) := by
    simp [selectedIncidenceTangencyCut, hBt_def]
  have hmetric2 :
      Real.rpow
          (2 * selectedIncidenceMetricCut
            heavyLogLoss fiberRatio epsilon) epsilon =
        Bm := by
    rw [h5]
    have h7 :
        Real.rpow Bm ((1 / epsilon) * epsilon) =
          Real.rpow (Real.rpow Bm (1 / epsilon)) epsilon :=
      Real.rpow_mul hBm_nonneg (1 / epsilon) epsilon
    have h8 :
        Real.rpow Bm ((1 / epsilon) * epsilon) =
          Real.rpow Bm 1 := by rw [h3]
    have h9 : Real.rpow Bm 1 = Bm := Real.rpow_one Bm
    rw [h8, h9] at h7
    exact h7.symm
  have htangency2 :
      Real.rpow
          (selectedIncidenceTangencyCut heavyLogLoss eta) eta =
        Bt := by
    rw [h6]
    have h7 :
        Real.rpow Bt ((1 / eta) * eta) =
          Real.rpow (Real.rpow Bt (1 / eta)) eta :=
      Real.rpow_mul hBt_nonneg (1 / eta) eta
    have h8 :
        Real.rpow Bt ((1 / eta) * eta) =
          Real.rpow Bt 1 := by rw [h4]
    have h9 : Real.rpow Bt 1 = Bt := Real.rpow_one Bt
    rw [h8, h9] at h7
    exact h7.symm
  have h7 : 0 < Real.rpow Bm (1 / epsilon) :=
    Real.rpow_pos_of_pos hBm_pos _
  have hmetric_pos :
      0 < selectedIncidenceMetricCut
        heavyLogLoss fiberRatio epsilon := by
    have h8 :
        selectedIncidenceMetricCut
            heavyLogLoss fiberRatio epsilon =
          (1 / 2 : ℝ) * Real.rpow Bm (1 / epsilon) := by
      simp [selectedIncidenceMetricCut, hBm_def]
    rw [h8]
    exact mul_pos (by norm_num) h7
  have hmetric_lt_one :
      selectedIncidenceMetricCut
          heavyLogLoss fiberRatio epsilon < 1 := by
    have h9 : Real.rpow Bm (1 / epsilon) < 1 :=
      Real.rpow_lt_one hBm_nonneg hBm_lt_one h1
    have h10 :
        selectedIncidenceMetricCut
            heavyLogLoss fiberRatio epsilon =
          (1 / 2 : ℝ) * Real.rpow Bm (1 / epsilon) := by
      simp [selectedIncidenceMetricCut, hBm_def]
    rw [h10]
    nlinarith
  have htangency_pos :
      0 < selectedIncidenceTangencyCut heavyLogLoss eta :=
    Real.rpow_pos_of_pos hBt_pos _
  have htangency_lt_one :
      selectedIncidenceTangencyCut heavyLogLoss eta < 1 :=
    Real.rpow_lt_one hBt_nonneg hBt_lt_one h2
  have hbudget1 :
      24 * heavyLogLoss *
            Real.rpow
              (2 * selectedIncidenceMetricCut
                heavyLogLoss fiberRatio epsilon) epsilon *
            fiberRatio =
          1 := by
    rw [hmetric2, hBm_def]
    field_simp [h_pos1.ne']
  have hbudget2 :
      24 * heavyLogLoss *
            Real.rpow
              (selectedIncidenceTangencyCut heavyLogLoss eta) eta =
          1 := by
    rw [htangency2, hBt_def]
    field_simp [h_pos2.ne']
  exact
    ⟨hmetric_pos, hmetric_lt_one, htangency_pos,
      htangency_lt_one, hbudget1, hbudget2⟩

end Kakeya.Cinematic
