import MyLeanRepo.Kakeya.Assouad.PureWZ2.Theorem5_2
import MyLeanRepo.Kakeya.Assouad.PureWZ2.ParameterFrostmanLowerBound

/-!
# Pure WZ2 Node 8: Theorem 5.2

The Section 7 parameter-Frostman estimate is a closed proof dependency.
The proof compares its lower bound with the repaired Node 7 upper exponent
`sigma - analyticLoss`.
-/

namespace Kakeya.Assouad

theorem pure_wz2_node08_theorem5_2 :
    PureWZ2Theorem5_2AssemblyStatement := by
  intro hSubunit hCritical hPropSticky hGrains hC2 hLargeSlope hSmall
  by_contra h_not
  rcases hCritical hSubunit h_not with ⟨sigma, ⟨pkg⟩⟩
  have hsigma_pos : 0 < sigma := pkg.sigma_pos
  have hSmallConj :=
    hSmall hSubunit hCritical hPropSticky hGrains hC2 hLargeSlope
  have h_prep :
      PureWZ2ParameterFrostmanPreparationStatement :=
    hSmallConj.2
  set epsilon : ℝ := sigma / 4 with hepsilon_def
  have hepsilon_pos : 0 < epsilon := by linarith
  have hLower :
      TwistedProjectionParameterFrostmanEstimateStatement :=
    pure_wz2_twisted_projection_parameter_frostman_lower_bound
  rcases hLower epsilon hepsilon_pos with
    ⟨eta, delta₀, heta_pos, heta_le,
      hdelta₀_pos, hdelta₀_lt_one, h_est_concl⟩
  have heta_lt_sigma : eta < sigma := by linarith
  rcases h_prep sigma pkg eta delta₀
      heta_pos heta_lt_sigma hdelta₀_pos with
    ⟨delta, hdelta_pos, hdelta_le_d0,
      hdelta_lt_one, ⟨prep⟩⟩
  have h_volume_ge :
      MeasureTheory.volume
          (twistedUnion prep.shading prep.analysisSlope) ≥
        Kakeya.realRpowENN delta epsilon :=
    h_est_concl delta hdelta_pos hdelta_le_d0
      prep.family prep.family_nonempty prep.bounded_base
      prep.analytic_distinct prep.vertical_chart
      prep.tube_wolff prep.parameter_frostman
      prep.cardinality_upper prep.shading prep.dense
      prep.slope_window prep.analysisSlope
      prep.analysisSlope_nonsingular
      prep.analysisSlope_zero
  have h_exp_lt : epsilon < sigma - eta := by
    simp only [hepsilon_def]
    linarith
  have h_rpow_lt :
      Real.rpow delta (sigma - eta) <
        Real.rpow delta epsilon :=
    Real.rpow_lt_rpow_of_exponent_gt
      hdelta_pos hdelta_lt_one h_exp_lt
  have h_rpow_pos : 0 < Real.rpow delta epsilon :=
    Real.rpow_pos_of_pos hdelta_pos _
  have h_ennreal_lt :
      Kakeya.realRpowENN delta (sigma - eta) <
        Kakeya.realRpowENN delta epsilon := by
    simpa [Kakeya.realRpowENN] using
      (ENNReal.ofReal_lt_ofReal_iff h_rpow_pos).mpr h_rpow_lt
  have h_contra :
      Kakeya.realRpowENN delta epsilon ≤
        Kakeya.realRpowENN delta (sigma - eta) :=
    le_trans h_volume_ge prep.projection_upper
  exact not_le.mpr h_ennreal_lt h_contra

end Kakeya.Assouad
