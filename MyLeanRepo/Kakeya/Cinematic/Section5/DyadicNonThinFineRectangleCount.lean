import MyLeanRepo.Kakeya.Cinematic.Section5.AmbientBallRestriction
import MyLeanRepo.Kakeya.Cinematic.Section5.FaithfulScaleAbsorption
import MyLeanRepo.Kakeya.Cinematic.Section5.NonThinFineRectangleCount

/-!
# Non-thin counting for one dyadic ambient bin

The center-distance hypothesis of the non-thin packing theorem follows
directly from membership of every selected source point in one ambient bin.
-/

namespace Kakeya.Cinematic

lemma dyadic_non_thin_fine_rectangle_count
    {family : Set C2Function} {E : Set (ℝ × ℝ)}
    {K delta diameter epsilon eta tRep DeltaRep C_R : ℝ}
    (hK : 1 ≤ K)
    (hC_R_large : 9216 * K ^ 2 ≤ C_R)
    (hdelta : 0 < delta)
    (data : DyadicFineAssignmentData
      family E K delta diameter epsilon eta tRep DeltaRep C_R)
    (h_nonthin : tRep ≤ 16 * delta)
    (R : RectangleFamily
      delta (C_R * tRep * DeltaRep / delta))
    (source : Fin R.card → E)
    (hsource :
      ∀ i, R.rectangle i =
        data.assignment.rectangle (source i))
    (hcenters : R.CentersIn family)
    (hcentral : R.IsOverCentralQuarterOf data.interval)
    (hincomp : R.IsPairwiseIncomparable family 100)
    (center : C2Function)
    (hbin : ∀ i,
      ((source i : E) : ℝ × ℝ) ∈ data.ambientBin center tRep) :
    ∃ C_non_thin : ℝ,
      0 < C_non_thin ∧
        (R.card : ℝ) ≤ C_non_thin := by
  rcases non_thin_fine_rectangle_count K C_R hK hC_R_large with
    ⟨C_non_thin, hC_non_thin, hmain⟩
  have hcentral_assignment :
      R.IsOverCentralQuarterOf data.assignment.interval := by
    rw [data.assignment_interval]
    exact hcentral
  refine ⟨C_non_thin, hC_non_thin, ?_⟩
  apply hmain hdelta data.delta_le_DeltaRep data.DeltaRep_le_tRep
    h_nonthin data.assignment.intervalControlled R hcenters
    hcentral_assignment hincomp center
  intro i
  have hcenter :
      data.assignment.center (source i) ∈ c2Ball center tRep := by
    rcases hbin i with ⟨hsource_mem, hcenter⟩
    have hproof : hsource_mem = (source i).property := Subsingleton.elim _ _
    simpa [hproof] using hcenter
  have hdistance :
      c2Distance center (data.assignment.center (source i)) ≤ tRep := by
    have h :=
      (show c2Distance (data.assignment.center (source i)) center ≤ tRep by
        simpa only [mem_c2Ball] using hcenter)
    simpa [c2Distance_eq_dist, dist_comm] using h
  rw [hsource i, data.assignment.rectangle_function]
  exact hdistance.trans <| by
    have htRep_pos := data.tRep_pos
    linarith

lemma dyadic_non_thin_multiplicity_bound
    {family : Set C2Function} {E : Set (ℝ × ℝ)}
    {K delta diameter metricExponent tangencyExponent
      tRep DeltaRep C_R baseDelta C_KT lambda L : ℝ}
    (hK : 1 ≤ K)
    (hC_KT : 1 ≤ C_KT)
    (hlambda : 1 ≤ lambda)
    (hL : 0 ≤ L)
    (hmetric : 0 < metricExponent)
    (htangency : 0 < tangencyExponent)
    (hdelta : 0 < delta)
    (hdelta16 : delta ≤ 1 / 16)
    (hbaseDelta : 0 < baseDelta)
    (hdelta_eq :
      delta = (1 + L) * lambda * baseDelta)
    (data : DyadicFineAssignmentData
      family E K delta diameter metricExponent tangencyExponent
        tRep DeltaRep C_R)
    (hdiameter : diameter = K)
    (hKT :
      data.ambientSource.HasKatzTaoBound baseDelta C_KT)
    (hnonthin : tRep ≤ 16 * delta)
    (hE : E.Nonempty)
    {q : ℕ}
    (hq_lower :
      ∀ p : E, q ≤ (data.assignment.fiber p).card)
    (hretained :
      Real.rpow (tRep / (8 * diameter)) metricExponent *
          Real.rpow (DeltaRep / (2 * tRep)) tangencyExponent *
          (data.mu : ℝ) <
        4 * ((q : ℝ) + 1)) :
    Real.rpow delta metricExponent * (data.mu : ℝ) <
      4 * Real.rpow (8 * K) metricExponent *
        Real.rpow 32 tangencyExponent *
        (16 * C_KT * ((1 + L) * lambda) + 1) := by
  obtain ⟨point, hpoint⟩ := hE
  let p : E := ⟨point, hpoint⟩
  have hKpos : 0 < K := by
    linarith
  have hbase_le_delta : baseDelta ≤ delta := by
    rw [hdelta_eq]
    have hfactor : 1 ≤ (1 + L) * lambda := by
      have h1 : 1 ≤ 1 + L := by
        linarith
      nlinarith
    nlinarith
  have hbase_le_tRep : baseDelta ≤ tRep :=
    hbase_le_delta.trans data.delta_le_DeltaRep
      |>.trans data.DeltaRep_le_tRep
  have htRep_one : tRep ≤ 1 := by
    calc
      tRep ≤ 16 * delta := hnonthin
      _ ≤ 16 * (1 / 16) := by
        gcongr
      _ = 1 := by
        norm_num
  have hq_real :
      (q : ℝ) ≤ C_KT * (tRep / baseDelta) := by
    have h1 :
        (q : ℝ) ≤
          ((data.assignment.fiber p).card : ℝ) := by
      exact_mod_cast hq_lower p
    exact h1.trans
      (data.fiber_card_le_katz_tao
        hdelta hKT hbase_le_tRep htRep_one p)
  have htRep_base :
      tRep / baseDelta ≤
        16 * ((1 + L) * lambda) := by
    have h1 :
        tRep ≤
          16 * ((1 + L) * lambda * baseDelta) := by
      rw [← hdelta_eq]
      exact hnonthin
    apply (div_le_iff₀ hbaseDelta).2
    calc
      tRep ≤
          16 * ((1 + L) * lambda * baseDelta) := h1
      _ =
          (16 * ((1 + L) * lambda)) * baseDelta := by
        ring
  have hq_upper :
      (q : ℝ) ≤
        16 * C_KT * ((1 + L) * lambda) := by
    calc
      (q : ℝ) ≤ C_KT * (tRep / baseDelta) := hq_real
      _ ≤ C_KT * (16 * ((1 + L) * lambda)) := by
        gcongr
      _ = 16 * C_KT * ((1 + L) * lambda) := by
        ring
  have htRep_pos : 0 < tRep := data.tRep_pos
  have hdiameter_pos : 0 < diameter := by
    rw [hdiameter]
    exact hKpos
  have hDelta_pos : 0 < DeltaRep :=
    hdelta.trans_le data.delta_le_DeltaRep
  have hmetric_ratio :
      delta / (8 * K) ≤
        tRep / (8 * diameter) := by
    rw [hdiameter]
    apply
      (div_le_div_iff_of_pos_right
        (by positivity : 0 < 8 * K)).2
    exact
      data.delta_le_DeltaRep.trans
        data.DeltaRep_le_tRep
  have htangency_ratio :
      1 / 32 ≤ DeltaRep / (2 * tRep) := by
    apply
      (le_div_iff₀
        (by positivity : 0 < 2 * tRep)).2
    have hDelta_lower : tRep / 16 ≤ DeltaRep := by
      have h1 : tRep ≤ 16 * delta := hnonthin
      have h2 : delta ≤ DeltaRep := data.delta_le_DeltaRep
      linarith
    calc
      (1 / 32) * (2 * tRep) = tRep / 16 := by
        ring
      _ ≤ DeltaRep := hDelta_lower
  have hmetric_pow :
      Real.rpow (delta / (8 * K)) metricExponent ≤
        Real.rpow
          (tRep / (8 * diameter)) metricExponent :=
    Real.rpow_le_rpow
      (by positivity) hmetric_ratio hmetric.le
  have htangency_pow :
      Real.rpow (1 / 32) tangencyExponent ≤
        Real.rpow
          (DeltaRep / (2 * tRep)) tangencyExponent :=
    Real.rpow_le_rpow
      (by positivity) htangency_ratio htangency.le
  have hmetric_rep_ratio_nonneg :
      0 ≤ tRep / (8 * diameter) :=
    div_nonneg htRep_pos.le (by positivity)
  have hmetric_rep_nonneg :
      0 ≤
        Real.rpow
          (tRep / (8 * diameter)) metricExponent :=
    Real.rpow_nonneg hmetric_rep_ratio_nonneg _
  have htangency_nonneg :
      0 ≤ Real.rpow (1 / 32) tangencyExponent :=
    Real.rpow_nonneg (by norm_num) _
  have htangency_ratio_nonneg :
      0 ≤ DeltaRep / (2 * tRep) :=
    div_nonneg hDelta_pos.le (by positivity)
  have hfactor_product :
      Real.rpow (delta / (8 * K)) metricExponent *
          Real.rpow (1 / 32) tangencyExponent ≤
        Real.rpow
            (tRep / (8 * diameter)) metricExponent *
          Real.rpow
            (DeltaRep / (2 * tRep)) tangencyExponent :=
    mul_le_mul hmetric_pow htangency_pow
      htangency_nonneg hmetric_rep_nonneg
  have hfactor_lower :
      Real.rpow (delta / (8 * K)) metricExponent *
          Real.rpow (1 / 32) tangencyExponent *
          (data.mu : ℝ) <
        4 * ((q : ℝ) + 1) := by
    calc
      Real.rpow (delta / (8 * K)) metricExponent *
            Real.rpow (1 / 32) tangencyExponent *
            (data.mu : ℝ) ≤
          (Real.rpow
              (tRep / (8 * diameter)) metricExponent *
            Real.rpow
              (DeltaRep / (2 * tRep)) tangencyExponent) *
            (data.mu : ℝ) :=
        mul_le_mul_of_nonneg_right
          hfactor_product (by positivity)
      _ < 4 * ((q : ℝ) + 1) := hretained
  let fixed : ℝ :=
    Real.rpow (8 * K) metricExponent *
      Real.rpow 32 tangencyExponent
  have hfixed_pos : 0 < fixed := by
    dsimp only [fixed]
    exact mul_pos
      (Real.rpow_pos_of_pos
        (by positivity : 0 < 8 * K) _)
      (Real.rpow_pos_of_pos
        (by norm_num : (0 : ℝ) < 32) _)
  have hmetric_div :
      Real.rpow
          (delta / (8 * K)) metricExponent =
        Real.rpow delta metricExponent /
          Real.rpow (8 * K) metricExponent :=
    Real.div_rpow hdelta.le (by positivity) _
  have htangency_div :
      Real.rpow (1 / 32) tangencyExponent =
        1 / Real.rpow 32 tangencyExponent := by
    have h :=
      Real.div_rpow
        (show (0 : ℝ) ≤ 1 by norm_num)
        (show (0 : ℝ) ≤ 32 by norm_num)
        tangencyExponent
    simpa using h
  have hquotient :
      Real.rpow (delta / (8 * K)) metricExponent *
          Real.rpow (1 / 32) tangencyExponent *
          (data.mu : ℝ) =
        (Real.rpow delta metricExponent *
          (data.mu : ℝ)) / fixed := by
    rw [hmetric_div, htangency_div]
    dsimp only [fixed]
    have h8K : 0 < 8 * K := by
      positivity
    field_simp
      [ne_of_gt (Real.rpow_pos_of_pos h8K _),
        ne_of_gt
          (Real.rpow_pos_of_pos
            (by norm_num : (0 : ℝ) < 32) _)]
  rw [hquotient] at hfactor_lower
  have hscaled' :
      Real.rpow delta metricExponent *
          (data.mu : ℝ) <
        (4 * ((q : ℝ) + 1)) * fixed :=
    (div_lt_iff₀ hfixed_pos).mp hfactor_lower
  have hscaled :
      Real.rpow delta metricExponent *
          (data.mu : ℝ) <
        fixed * (4 * ((q : ℝ) + 1)) := by
    simpa [mul_comm] using hscaled'
  calc
    Real.rpow delta metricExponent * (data.mu : ℝ) <
        fixed * (4 * ((q : ℝ) + 1)) :=
      hscaled
    _ ≤ fixed *
          (4 *
            (16 * C_KT * ((1 + L) * lambda) + 1)) := by
      gcongr
    _ =
        4 * Real.rpow (8 * K) metricExponent *
          Real.rpow 32 tangencyExponent *
          (16 * C_KT * ((1 + L) * lambda) + 1) := by
      dsimp only [fixed]
      ring

lemma dyadic_non_thin_scale_exit
    (K C_KT lambda L metricExponent tangencyExponent
      targetExponent : ℝ)
    (hK : 1 ≤ K)
    (hC_KT : 1 ≤ C_KT)
    (hlambda : 1 ≤ lambda)
    (hL : 0 ≤ L)
    (hmetric : 0 < metricExponent)
    (htangency : 0 < tangencyExponent)
    (hmargin :
      (3 / 2 : ℝ) * metricExponent < targetExponent) :
    ∃ delta₀ : ℝ,
      0 < delta₀ ∧
      delta₀ ≤ 1 / 16 ∧
      ∀ {family : Set C2Function} {E : Set (ℝ × ℝ)}
        {delta diameter tRep DeltaRep C_R baseDelta : ℝ},
        0 < delta →
        delta ≤ delta₀ →
        0 < baseDelta →
        delta = (1 + L) * lambda * baseDelta →
        ∀ (data : DyadicFineAssignmentData
            family E K delta diameter metricExponent
              tangencyExponent tRep DeltaRep C_R),
          diameter = K →
          data.ambientSource.HasKatzTaoBound
            baseDelta C_KT →
          tRep ≤ 16 * delta →
          E.Nonempty →
          ∀ {q : ℕ},
            (∀ p : E,
              q ≤ (data.assignment.fiber p).card) →
            Real.rpow
                  (tRep / (8 * diameter)) metricExponent *
                Real.rpow
                  (DeltaRep / (2 * tRep)) tangencyExponent *
                (data.mu : ℝ) <
              4 * ((q : ℝ) + 1) →
            1 ≤
              Real.rpow delta (-targetExponent) *
                Real.rpow (data.mu : ℝ) (-3 / 2 : ℝ) := by
  let B : ℝ :=
    4 * Real.rpow (8 * K) metricExponent *
      Real.rpow 32 tangencyExponent *
      (16 * C_KT * ((1 + L) * lambda) + 1)
  have hfixed1 :
      0 < Real.rpow (8 * K) metricExponent :=
    Real.rpow_pos_of_pos (by positivity) _
  have hfixed2 :
      0 < Real.rpow 32 tangencyExponent :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hfactor :
      0 < 16 * C_KT * ((1 + L) * lambda) + 1 := by
    have hnonneg :
        0 ≤ 16 * C_KT * ((1 + L) * lambda) := by
      positivity
    linarith
  have hB : 0 < B := by
    dsimp only [B]
    positivity
  rcases bounded_multiplicity_scale_absorption
      metricExponent targetExponent B hB hmargin with
    ⟨rawDelta₀, hrawDelta₀, _, hmain⟩
  let delta₀ : ℝ := min rawDelta₀ (1 / 16)
  have hdelta₀ : 0 < delta₀ := by
    dsimp only [delta₀]
    positivity
  have hdelta₀_sixteenth : delta₀ ≤ 1 / 16 := by
    dsimp only [delta₀]
    exact min_le_right _ _
  have hdelta₀_raw : delta₀ ≤ rawDelta₀ := by
    dsimp only [delta₀]
    exact min_le_left _ _
  refine ⟨delta₀, hdelta₀, hdelta₀_sixteenth, ?_⟩
  intro family E delta diameter tRep DeltaRep C_R baseDelta
    hdelta hdelta_le hbaseDelta hdelta_eq data
    hdiameter hKT hnonthin hE q hq_lower hretained
  have hdelta_raw : delta ≤ rawDelta₀ :=
    hdelta_le.trans hdelta₀_raw
  have hdelta16 : delta ≤ 1 / 16 :=
    hdelta_le.trans hdelta₀_sixteenth
  apply hmain hdelta hdelta_raw data.mu_pos
  exact dyadic_non_thin_multiplicity_bound
    hK hC_KT hlambda hL hmetric htangency hdelta hdelta16
    hbaseDelta hdelta_eq data hdiameter hKT hnonthin hE
    hq_lower hretained

end Kakeya.Cinematic
