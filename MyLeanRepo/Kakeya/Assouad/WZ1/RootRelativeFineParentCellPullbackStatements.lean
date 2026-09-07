import MyLeanRepo.Kakeya.Assouad.WZ1.RootRelativeBalancedCoverStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma17RefinementLeafStatements

/-!
# Root-relative fine parent-cell pullback

One coordinate of a root-relative Proposition 5 package exposes an ordinary
single-scale balanced-cover view. The already-closed fine parent-cell
pullback acts only on that view and does not inspect any transition map or
another schedule coordinate.
-/

namespace Kakeya.Assouad

/--
Apply the fine parent-cell pullback to one explicit root-relative schedule
coordinate.

The selected coarse shading and all quantitative assumptions remain explicit.
The output is on the original root family.
-/
def WZ1RootRelativeFineParentCellPullbackStatement : Prop :=
  ∀ epsilon₁ epsilon₂ : ℝ,
    0 < epsilon₁ →
    0 < epsilon₂ →
    epsilon₁ < epsilon₂ →
    epsilon₁ + epsilon₂ < 1 →
    ∃ rho₀ : ℝ,
      0 < rho₀ ∧ rho₀ ≤ 1 / 1000 ∧
      ∀ {delta sigma : ℝ},
        ∀ {F : Kakeya.Streamlined.TubeFamily delta},
          ∀ {U : Kakeya.Streamlined.UniformTubeStructure F},
            ∀ {Y : Kakeya.Streamlined.TubeShading F},
              ∀ {scaleCount depth : ℕ},
                ∀ {schedule :
                    Fin scaleCount →
                      Kakeya.Streamlined.AdmissibleScale delta},
                  ∀ cover :
                      WZ1RootRelativeBalancedCoverData
                        (sigma := sigma) (epsilon := epsilon₁)
                        U Y schedule depth,
                    ∀ coordinate : Fin scaleCount,
                      ∀ propertyThree :
                          Kakeya.Streamlined.TubeShading
                            (U.coarse (schedule coordinate)),
                        0 < sigma →
                        sigma < 1 →
                        0 < (schedule coordinate).1 →
                        (schedule coordinate).1 ≤ rho₀ →
                        wz1Lemma17FinePullbackAbsorptionConstant *
                            Kakeya.realRpowENN delta
                              (epsilon₂ - epsilon₁) ≤
                          Kakeya.realRpowENN
                            (schedule coordinate).1 epsilon₂ →
                        IsSubshading propertyThree
                          (cover.atScale coordinate).coarseShading →
                        WZ1ExtremalPair sigma epsilon₂
                          (U.coarse (schedule coordinate))
                          (cover.atScale coordinate).coarseUniform
                          propertyThree →
                          Nonempty
                            (WZ1Lemma17FineParentCellPullbackData
                              (epsilon₂ := epsilon₂)
                              (cover.toBalancedCoverData coordinate)
                              propertyThree)

end Kakeya.Assouad
