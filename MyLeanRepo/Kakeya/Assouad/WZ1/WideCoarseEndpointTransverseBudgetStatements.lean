import MyLeanRepo.Kakeya.Assouad.WZ1.WideCoarseEndpointLineSplitStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.WideCoarseEndpointRawCounting
import MyLeanRepo.Kakeya.Assouad.WZ1.WideCoarseEndpointRawBudgetAssembly
import MyLeanRepo.Kakeya.Assouad.WZ1.WideCoarseEndpointPowerArithmetic
import MyLeanRepo.Kakeya.Assouad.WZ1.WideCoarseEndpointScaleAbsorption
import MyLeanRepo.Kakeya.Assouad.WZ1.WideCoarseEndpointSourceBudget
import MyLeanRepo.Kakeya.Assouad.WZ1.WideCoarseEndpointTransverseGeometry

/-!
# Source-strip budget leaf for the transverse endpoint regime

Exact affine pullback, enlargement from the exact source radius to `delta`,
and cancellation of the balanced fiber multiplicity are mechanical.  The
only remaining transverse leaf is the quantitative upper bound on that one
enlarged selected-source strip.
-/

namespace Kakeya.Assouad

open scoped ENNReal

/-- The exact selected-source strip budget needed after transverse pullback. -/
def WZ1WideCoarseEndpointTransverseSourceBudget
    {epsilon eta delta : ℝ}
    (parameters : WZ1Proposition8_9Parameters epsilon)
    {F G₁ G₂ ambient active : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    {data :
      WZ1Proposition8_9CommonStripData
        delta epsilon eta parameters F G₁ G₂ H}
    (input :
      WZ1WideCoarseEndpointLineInput
        (ambient := ambient) (active := active)
        parameters data)
    (normal : Point2) (level radius : ℝ) : Prop :=
  WZ1WideCoarseEndpointSourceBudget
    (ambient := ambient) (active := active)
    parameters input normal level radius

/--
The sole quantitative transverse leaf.

The supplied `rawWidth`, ambient/active retention, exact rescaling, and the
enlarged exact source strip are all fixed in the input.  No affine pullback
or balanced-fiber cancellation remains in this statement.
-/
def WZ1WideCoarseEndpointTransverseBudgetStatement : Prop :=
  ∀ epsilon : ℝ,
    ∀ parameters : WZ1Proposition8_9Parameters epsilon,
      0 < epsilon → epsilon < 1 →
        ∃ etaCap : ℝ, 0 < etaCap ∧
          ∀ eta : ℝ, 0 < eta → eta ≤ etaCap →
            ∃ delta₀ : ℝ,
              0 < delta₀ ∧ delta₀ ≤ 1 ∧
              ∀ {delta : ℝ}
                {F G₁ G₂ ambient active : DiscreteSet 2}
                {H : Finset (Point2 × Point2 × Point2)},
                0 < delta → delta ≤ delta₀ →
                ∀ data :
                  WZ1Proposition8_9CommonStripData
                    delta epsilon eta parameters F G₁ G₂ H,
                  ∀ input :
                    WZ1WideCoarseEndpointLineInput
                      (ambient := ambient) (active := active)
                      parameters data,
                    ∀ normal : Point2, ‖normal‖ = 1 →
                      1 / 2 ≤
                        |inner ℝ normal
                          (wz1Perp2 data.direction)| →
                      ∀ level radius : ℝ,
                        delta / data.width ≤ radius →
                        radius ≤ 1 →
                        WZ1WideCoarseEndpointTransverseSourceBudget
                          (ambient := ambient) (active := active)
                          parameters input normal level radius

/-- The source-strip budget implies the previous transverse endpoint leaf. -/
def WZ1WideCoarseEndpointTransverseBudgetAssemblyStatement : Prop :=
  WZ1WideCoarseEndpointTransverseBudgetStatement →
    WZ1WideCoarseEndpointTransverseStatement

end Kakeya.Assouad
