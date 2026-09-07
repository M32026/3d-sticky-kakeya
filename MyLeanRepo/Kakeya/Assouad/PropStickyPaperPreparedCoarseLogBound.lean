import MyLeanRepo.Kakeya.Assouad.PropStickyPaperPreparedCoarseRegularizedMainlineV2Statements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLinePackingCardinality
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperBoundaryLogCoefficient

/-! # Physical-scale logarithmic bound for caller coarse parents -/

noncomputable section

namespace Kakeya.Assouad

theorem wz2_paper_prepared_coarse_log_bound
    {delta rho : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hdeltaRho : delta ≤ rho)
    (hrhoOne : rho ≤ 1)
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    (hLine : WZ1PaperIsLineClass coarse)
    (hDistinct : WZ1PaperIsEssentiallyDistinct coarse) :
    (Nat.log 2 (2 * coarse.card) + 1 : ENNReal) ≤
      ENNReal.ofReal
        (wz2PaperBoundaryLogCoefficient *
          (1 + Real.log delta⁻¹)) := by
  have hCard :
      coarse.card ≤
        (2 * Nat.ceil (80 / rho) + 1) ^ 5 :=
    paper_essentially_distinct_card_bound_nat
      hDistinct hLine hrho hrhoOne
  have hRaw :
      (Nat.log 2 (2 * coarse.card) + 1 : ℝ) ≤
        (5 / Real.log 2) * Real.log (1 / rho) +
          (5 * Real.log 163 / Real.log 2 + 2) :=
    explicit_card_log_bound hrho hrhoOne hCard
  have hDeltaOne : delta ≤ 1 := hdeltaRho.trans hrhoOne
  have hLogDelta : 0 ≤ Real.log delta⁻¹ := by
    apply Real.log_nonneg
    calc
      (1 : ℝ) = 1⁻¹ := by norm_num
      _ ≤ delta⁻¹ := by gcongr
  have hInverse :
      1 / rho ≤ 1 / delta :=
    one_div_le_one_div_of_le hdelta hdeltaRho
  have hLogRhoDelta :
      Real.log (1 / rho) ≤ Real.log (1 / delta) :=
    Real.log_le_log (by positivity) hInverse
  have hLogOne :
      Real.log (1 / delta) = Real.log delta⁻¹ := by
    congr 1
    field_simp [hdelta.ne']
  rw [hLogOne] at hLogRhoDelta
  have hCoefficientA :
      5 / Real.log 2 ≤ wz2PaperBoundaryLogCoefficient := by
    dsimp only [wz2PaperBoundaryLogCoefficient]
    exact le_max_right _ _
  have hCoefficientB :
      5 * Real.log 163 / Real.log 2 + 2 ≤
        wz2PaperBoundaryLogCoefficient := by
    dsimp only [wz2PaperBoundaryLogCoefficient]
    exact le_max_left _ _
  have hReal :
      (Nat.log 2 (2 * coarse.card) + 1 : ℝ) ≤
        wz2PaperBoundaryLogCoefficient *
          (1 + Real.log delta⁻¹) := by
    calc
      (Nat.log 2 (2 * coarse.card) + 1 : ℝ) ≤
          (5 / Real.log 2) * Real.log (1 / rho) +
            (5 * Real.log 163 / Real.log 2 + 2) :=
        hRaw
      _ ≤
          (5 / Real.log 2) * Real.log delta⁻¹ +
            (5 * Real.log 163 / Real.log 2 + 2) := by
        gcongr
      _ ≤
          wz2PaperBoundaryLogCoefficient * Real.log delta⁻¹ +
            wz2PaperBoundaryLogCoefficient := by
        gcongr
      _ =
          wz2PaperBoundaryLogCoefficient *
            (1 + Real.log delta⁻¹) := by ring
  have hCast :
      (Nat.log 2 (2 * coarse.card) + 1 : ENNReal) =
        ENNReal.ofReal
          (Nat.log 2 (2 * coarse.card) + 1 : ℝ) := by
    norm_cast
  rw [hCast]
  exact ENNReal.ofReal_mono hReal

end Kakeya.Assouad

end
