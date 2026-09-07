import MyLeanRepo.Kakeya.Cinematic.Section5.MetricGoodPairIncidence
import MyLeanRepo.Kakeya.Cinematic.Section5.RepresentativeMetricGoodPairSelection

/-!
# Tangency-automatic counting when the shading gate fails

If the representative tangency scale is smaller than the enlarged shading
thickness, tangency separation at threshold `delta` is automatic. The metric
good-pair incidence theorem then gives a fine-rectangle count whose remaining
square-root factor is uniform in the representative scales.
-/

namespace Kakeya.Cinematic

lemma tangency_auto_counting_of_shading_gate_failure
    (hProductScale : ProductScaleFixedPairIncidenceStatement)
    (hTangencyGeometry : TangencyGeometryCompletionStatement)
    (hFinePair : FinePairIncidenceBoundStatement)
    (hPairCounting : PairIncidenceCountingStatement)
    {K D delta diameter epsilon eta tRep DeltaRep C_R C_shading : ℝ}
    (hK : 1 ≤ K) (hD : 1 ≤ D)
    (hdelta : 0 < delta)
    (htRep : 0 < tRep)
    (hDeltaRep : 0 < DeltaRep)
    (hC_R : 0 < C_R)
    (hC_shading : 0 < C_shading)
    {family : Set C2Function}
    (hfamily : IsCinematicFamily family K D)
    {E : Set (ℝ × ℝ)}
    (data : DyadicFineAssignmentData
      family E K delta diameter epsilon eta tRep DeltaRep C_R)
    (R : RectangleFamily
      delta (C_R * tRep * DeltaRep / delta))
    (source : Fin R.card → E)
    (hsource : ∀ i,
      R.rectangle i = data.assignment.rectangle (source i))
    (hcentral : R.IsOverCentralQuarterOf data.interval)
    (hincomp : R.IsPairwiseIncomparable family 100)
    (F_B : FiniteFunctionFamily)
    (hF_B : F_B.carrier ⊆ family)
    (hfiber : ∀ i,
      (data.assignment.fiber (source i)).carrier ⊆ F_B.carrier)
    (q : ℕ) (hq : 0 < q)
    (hfiber_lower : ∀ i,
      q ≤ (data.assignment.fiber (source i)).card)
    (metricCut : ℝ)
    (hmetricCut : 0 < metricCut)
    (hmetricCut_one : metricCut < 1)
    (hmetricScale : ∀ p : E,
      delta / data.exactT p < metricCut)
    (hretention : ∀ p : E,
      24 * Real.rpow (2 * metricCut) epsilon ≤
        Real.rpow
          (data.exactDelta p / (4 * data.exactT p)) eta)
    (hmetricGeometry :
      10 * delta ≤ (metricCut * tRep / 8) / (6 * K))
    (hadmissible :
      100 * delta ≤ C_R * tRep * DeltaRep / delta)
    (hgate : DeltaRep < C_shading * delta) :
    ∃ C_inc : ℝ, 0 < C_inc ∧
      (R.card : ℝ) * (q : ℝ) ^ 2 ≤
        3 * (F_B.card : ℝ) ^ 2 *
          (C_inc *
              Real.sqrt
                (8 * C_R * C_shading / metricCut) +
            1) := by
  have hRepMetric : RepresentativeMetricGoodPairSelectionStatement :=
    representative_metric_good_pair_selection
  rcases metric_good_pair_incidence
      hRepMetric hProductScale hTangencyGeometry
      hFinePair hPairCounting K D hK hD with
    ⟨C_inc, hC_inc, hmain⟩
  refine ⟨C_inc, hC_inc, ?_⟩
  have hraw :=
    hmain hfamily hdelta hC_R hmetricCut hmetricCut_one
      hdelta le_rfl data hmetricScale hretention
      hmetricGeometry (by norm_num) hadmissible
      R source hsource hcentral hincomp F_B hF_B hfiber
      q hq hfiber_lower
  have hinside :
      delta * (C_R * tRep * DeltaRep / delta) /
          ((metricCut * tRep / 8) * delta) ≤
        8 * C_R * C_shading / metricCut := by
    have hdenominator : 0 < metricCut * tRep * delta := by
      positivity
    calc
      delta * (C_R * tRep * DeltaRep / delta) /
          ((metricCut * tRep / 8) * delta) =
          8 * C_R * DeltaRep / (metricCut * delta) := by
            field_simp [hdelta.ne', htRep.ne', hmetricCut.ne']
      _ ≤ 8 * C_R * (C_shading * delta) /
          (metricCut * delta) := by
            gcongr
      _ = 8 * C_R * C_shading / metricCut := by
            field_simp [hdelta.ne', hmetricCut.ne']
  have hsqrt :
      Real.sqrt
          (delta * (C_R * tRep * DeltaRep / delta) /
            ((metricCut * tRep / 8) * delta)) ≤
        Real.sqrt (8 * C_R * C_shading / metricCut) :=
    Real.sqrt_le_sqrt hinside
  calc
    (R.card : ℝ) * (q : ℝ) ^ 2 ≤
        3 * (F_B.card : ℝ) ^ 2 *
          (C_inc *
              Real.sqrt
                (delta * (C_R * tRep * DeltaRep / delta) /
                  ((metricCut * tRep / 8) * delta)) +
            1) := hraw
    _ ≤
        3 * (F_B.card : ℝ) ^ 2 *
          (C_inc *
              Real.sqrt
                (8 * C_R * C_shading / metricCut) +
            1) := by
      gcongr

end Kakeya.Cinematic
