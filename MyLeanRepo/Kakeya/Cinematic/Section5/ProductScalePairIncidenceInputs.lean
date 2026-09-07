import MyLeanRepo.Kakeya.Cinematic.Section5.LevelSetInputs

/-!
# Product-scale fixed-pair incidence

The PYZ Lemma 46 bound depends on the product of the metric and tangency
separation scales, not on metric separation relative to the fine rectangle's
second parameter. Its constant is uniform over all scales, curve pairs, and
rectangle families once the cinematic constants are fixed.
-/

namespace Kakeya.Cinematic

def ProductScaleFixedPairIncidenceStatement : Prop :=
  TangencyGeometryCompletionStatement →
    ∀ K D : ℝ,
      1 ≤ K →
      1 ≤ D →
      ∃ C_pair : ℝ, 0 < C_pair ∧
        ∀ {delta t metricLower tangencyLower Cc : ℝ},
          0 < delta →
          0 < t →
          0 < metricLower →
          0 < tangencyLower →
          10 * delta ≤ metricLower / (6 * K) →
          100 ≤ Cc →
          Cc * delta ≤ t →
          ∀ {family : Set C2Function},
            IsCinematicFamily family K D →
            ∀ {I : ParameterInterval},
              I.IsControlled K →
              ∀ {w b : C2Function},
                w ∈ family →
                b ∈ family →
                w ≠ b →
                metricLower ≤ c2Distance w b →
                tangencyLower ≤ tangencyParameterOn I w b + delta →
                ∀ {R : RectangleFamily delta t},
                  R.IsOverCentralQuarterOf I →
                  R.IsPairwiseIncomparable family Cc →
                  (∀ i,
                    (R.rectangle i).IsLambdaTangent w 5 ∧
                      (R.rectangle i).IsLambdaTangent b 5) →
                (R.card : ℝ) ≤
                  C_pair *
                    Real.sqrt
                      (delta * t / (metricLower * tangencyLower))

end Kakeya.Cinematic
