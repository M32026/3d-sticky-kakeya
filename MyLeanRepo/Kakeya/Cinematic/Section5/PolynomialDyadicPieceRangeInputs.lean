import MyLeanRepo.Kakeya.Cinematic.Section5.DyadicPieceVolumeRefinementInputs
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Polynomially controlled dyadic piece-volume range

This is the quantitative range input for the piece-volume pigeonhole in PYZ
Lemma 43.  A polynomial bound for the number of pieces, a polynomial lower
bound for the retained mass, and the canonical half-mass cutoff force all
non-tiny pieces into only logarithmically many dyadic layers.
-/

namespace Kakeya.Cinematic

def PolynomialDyadicPieceRangeStatement : Prop :=
  ∀ {delta countExponent massExponent : ℝ}
    {N : ℕ} {total lower upper : ENNReal},
    0 < delta →
    delta ≤ 1 / 2 →
    0 ≤ countExponent →
    0 ≤ massExponent →
    0 < N →
    (N : ℝ) ≤ Real.rpow delta (-countExponent) →
    ENNReal.ofReal (Real.rpow delta massExponent) < total →
    2 * ((N : ENNReal) * lower) = total →
    upper ≤ 1 →
    ∃ L : ℕ,
      0 < L ∧
      upper < (2 : ENNReal) ^ L * lower ∧
      (L : ℝ) ≤
        (countExponent + massExponent + 2) *
          (Real.logb 2 (1 / delta) + 1)

end Kakeya.Cinematic
