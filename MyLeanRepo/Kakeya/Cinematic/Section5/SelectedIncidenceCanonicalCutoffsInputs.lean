import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Canonical good-pair cutoffs for selected incidence fibers

The paper's Lemma 45 compares the metric-fiber scale `mu₁` with the retained
scale `mu₂`, and uses a logarithmic tangency cutoff.  These definitions solve
the resulting q-level bad-set budgets exactly.  Geometric lower-scale
admissibility is intentionally left to the final small-scale caller.
-/

namespace Kakeya.Cinematic

noncomputable def selectedIncidenceMetricCut
    (heavyLogLoss fiberRatio epsilon : ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    Real.rpow
      (1 / (24 * heavyLogLoss * fiberRatio))
      (1 / epsilon)

noncomputable def selectedIncidenceTangencyCut
    (heavyLogLoss eta : ℝ) : ℝ :=
  Real.rpow
    (1 / (24 * heavyLogLoss))
    (1 / eta)

def SelectedIncidenceCanonicalCutoffsStatement : Prop :=
  ∀ heavyLogLoss fiberRatio epsilon eta : ℝ,
    1 ≤ heavyLogLoss →
    1 ≤ fiberRatio →
    0 < epsilon →
    0 < eta →
    let metricCut :=
      selectedIncidenceMetricCut
        heavyLogLoss fiberRatio epsilon
    let tangencyCut :=
      selectedIncidenceTangencyCut heavyLogLoss eta
    0 < metricCut ∧
      metricCut < 1 ∧
      0 < tangencyCut ∧
      tangencyCut < 1 ∧
      24 * heavyLogLoss *
            Real.rpow (2 * metricCut) epsilon *
            fiberRatio =
          1 ∧
      24 * heavyLogLoss *
            Real.rpow tangencyCut eta =
          1

end Kakeya.Cinematic
