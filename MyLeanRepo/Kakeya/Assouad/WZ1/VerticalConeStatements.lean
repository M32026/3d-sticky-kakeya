import MyLeanRepo.Kakeya.Assouad.WZ1.RescaledFiberStatements

/-!
# Narrow vertical cones after anchored unit rescaling

The distinguished source tube in the Proposition 9 unit rescaling is sent to
the vertical axis.  Every retained source tube belongs to the same coarse
parent and is projectively close to the distinguished direction.  After the
transverse dilation by `1 / (100 * rho)`, every rediscretized target axis is
therefore contained in a fixed narrow cone about the vertical axis.

This is stronger than `IsInVerticalChart`, which only gives a lower bound
`|direction_z| >= 1/2`.  The narrow-cone estimate is the geometric input later
used to prove the Lemma 23 hypothesis `|planeMap_z| <= 1/2`.
-/

namespace Kakeya.Assouad

/-- Every tube direction is within `aperture` of one of the two vertical axes. -/
def IsInNarrowVerticalCone
    {delta : ℝ} (F : Kakeya.Streamlined.TubeFamily delta)
    (aperture : ℝ) : Prop :=
  ∀ i, ∃ sign : ℝ, (sign = 1 ∨ sign = -1) ∧
    ‖(F.tube i).direction - sign • e3‖ ≤ aperture

/--
The target family of one Property-(P) selected, anchored, unit-rescaled parent
fiber lies in the fixed `1/10` vertical cone at the small intermediate scales
used by Proposition 9.

The bound `rho ≤ 1/4` is the actual geometric range of the common-parent
direction estimate.  The downstream anchored global-grain producer chooses
the stronger threshold `rho ≤ 1/100`.
-/
def WZ1PropertyPRescaledFiberNarrowConeStatement : Prop :=
  ∀ {delta sigma inputLoss baseOutputLoss propertyOutputLoss : ℝ},
    ∀ {F : Kakeya.Streamlined.TubeFamily delta},
      ∀ {U : Kakeya.Streamlined.UniformTubeStructure F},
        ∀ {Y : Kakeya.Streamlined.TubeShading F},
          ∀ {rho : Kakeya.Streamlined.AdmissibleScale delta},
            ∀ {balanced :
                WZ1BalancedCoverData
                  (sigma := sigma) (epsilon := inputLoss) U Y rho},
              ∀ {parent : Fin (U.coarse rho).card},
                ∀ {hrho : 0 < rho.1},
                  ∀ (base :
                      WZ1UnitRescaledFiberData
                        (inputLoss := inputLoss)
                        (outputLoss := baseOutputLoss)
                        balanced parent hrho),
                    ∀ (selected :
                        WZ1PropertyPRescaledFiberData
                          (propertyOutputLoss := propertyOutputLoss)
                          base),
                      rho.1 ≤ 1 / 4 →
                        IsInNarrowVerticalCone
                          selected.fiber.targetFamily (1 / 10)

end Kakeya.Assouad
