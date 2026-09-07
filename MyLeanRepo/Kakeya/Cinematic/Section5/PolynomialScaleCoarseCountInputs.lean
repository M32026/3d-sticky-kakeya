import MyLeanRepo.Kakeya.Cinematic.Statements

/-!
# Coarse rectangle count at polynomially large scale

The fine rectangles in PYZ Lemma 43 have second parameter
`C_R * t * Delta / delta`, which can be larger than one but is bounded by a
fixed multiple of `delta⁻¹`. The doubling and midpoint-packing proof of
Lemma 25 still gives a polynomial-in-`delta` cardinality bound in this
regime; the fixed upper-scale constant changes only the smallness threshold.
-/

namespace Kakeya.Cinematic

def PolynomialScaleCoarseRectangleCountStatement : Prop :=
  ∀ D : ℝ, 1 ≤ D →
    ∃ C : ℝ, 0 < C ∧
      ∀ K T : ℝ, 1 ≤ K → 1 ≤ T →
        ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
          ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
            ∀ t lambda : ℝ,
              delta ≤ t →
              t ≤ T / delta →
              100 ≤ lambda →
              IsAdmissibleComparisonScale delta t lambda →
              ∀ family : Set C2Function,
                IsCinematicFamily family K D →
                ∀ I : ParameterInterval, I.IsShort K →
                  ∀ R : RectangleFamily delta t,
                    R.CentersIn family →
                    R.IsOverCentralQuarterOf I →
                    R.IsPairwiseIncomparable family lambda →
                    (R.card : ℝ) ≤ Real.rpow delta (-C)

end Kakeya.Cinematic
