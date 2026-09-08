import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.WithShading.FixedDepthIncreasingGrid
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.WithShading.GridPiecewiseData

/-!
# Explicit K-ratio gate for the fixed-depth power grid

Every adjacent interval of the increasing power grid has the same ratio
`delta^(-1/N)`.  The final finite-grid assembly therefore uses one explicit
real K-parameter, namely the maximum of `2` and twice the corresponding
volume-growth constant.

This witness remains scale-dependent.  Later loss estimates must bound its
growth honestly; this module does not treat it as an absolute constant.
-/

noncomputable section

open Kakeya.Streamlined

namespace Kakeya.Streamlined.RandomTranslation.WithShading

/-- The explicit K used on every adjacent interval of one fixed power grid. -/
def fixedDepthPowerGridKRatio
    (delta : ℝ) (N : ℕ) : ℝ :=
  max 2
    (2 * cVol
      (Kakeya.realRpowENN delta (-(1 / (N : ℝ)))).toReal)

/--
The explicit power-grid K is at least two and dominates the exact volume
growth constant on every increasing adjacent interval.
-/
def FixedDepthPowerGridKRatioGateStatement : Prop :=
  ∀ {delta : ℝ} {N : ℕ},
    0 < delta →
    delta ≤ 1 →
    0 < N →
  ∀ (grid : FixedDepthPowerGrid delta N),
    2 ≤ fixedDepthPowerGridKRatio delta N ∧
    ENNReal.ofReal (fixedDepthPowerGridKRatio delta N) ≤
        ENNReal.ofReal
            (2 + Real.pi + 8 / 3 * Real.pi) *
          Kakeya.realRpowENN delta (-(3 / (N : ℝ))) ∧
      ∀ i : Fin N,
        2 * ENNReal.ofReal
            (cVol
              ((grid.increasingScale (Fin.succ i)).1 /
                (grid.increasingScale
                  (Fin.castSucc i)).1)) ≤
          ENNReal.ofReal (fixedDepthPowerGridKRatio delta N)

end Kakeya.Streamlined.RandomTranslation.WithShading

end
