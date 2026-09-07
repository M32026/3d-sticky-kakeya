import MyLeanRepo.Kakeya.Assouad.WZ1.RootRelativeBalancedCoverStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.CordobaLogAbsorptionStatement
import MyLeanRepo.Kakeya.Assouad.WZ1.LocalGrainCubeCountStatements

/-!
# Root-relative Córdoba leaves for WZ1 Lemma 17

These interfaces isolate the part of the paper's Lemma 17 that is independent
of the still-open root-relative Proposition 5 producer.  They consume one
explicit rho-scale cover and the Property-(P) shadings used by the Córdoba
argument.  No recursive coarse uniform structure or cross-scale transition
map appears.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

/--
The exact root-relative data consumed by the Córdoba full-grain argument.

The fields follow the paper's two Property-(P) refinements with a
constant-multiplicity refinement between them.  The structure deliberately
omits the independent tau and robust covers: the Córdoba estimate only uses
their already-produced consequences recorded below.
-/
structure WZ1RootRelativeCordobaData
    {delta sigma epsilon₁ epsilon₃ : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {refined : Kakeya.Streamlined.TubeShading F}
    {rho tau : Kakeya.Streamlined.AdmissibleScale delta}
    (rhoCover : WZ1RootRelativeScaleCoverData
      (sigma := sigma) (epsilon := epsilon₁) U refined rho) where
  propertyOne : Kakeya.Streamlined.TubeShading (U.coarse rho)
  propertyOne_sub_coarse :
    IsSubshading propertyOne rhoCover.coarseShading
  constantShading : Kakeya.Streamlined.TubeShading (U.coarse rho)
  constant_subshading : IsSubshading constantShading propertyOne
  multiplicity : ℕ
  multiplicity_pos : 0 < multiplicity
  constant_multiplicity :
    constantShading.HasConstantMultiplicity
      multiplicity (2 * multiplicity)
  propertyThree : Kakeya.Streamlined.TubeShading (U.coarse rho)
  propertyThree_subshading :
    IsSubshading propertyThree constantShading
  propertyOne_full :
    ∀ j p, p ∈ propertyOne.carrier j →
      Kakeya.realRpowENN rho.1 (2 + 2 * epsilon₁) *
          ENNReal.ofReal tau.1 ≤
        volume
          (propertyOne.carrier j ∩ Metric.closedBall p tau.1)
  propertyThree_full :
    ∀ j p, p ∈ propertyThree.carrier j →
      Kakeya.realRpowENN rho.1 (2 + 2 * epsilon₁) *
          ENNReal.ofReal tau.1 ≤
        volume
          (propertyThree.carrier j ∩ Metric.closedBall p tau.1)
  transverse :
    ∀ p ∈ propertyThree.union,
      ∀ i, p ∈ propertyThree.carrier i →
        ∃ j,
          p ∈ propertyOne.carrier j ∧
          Real.rpow rho.1 epsilon₃ ≤
            ‖wz1Cross
              ((U.coarse rho).tube i).direction
              ((U.coarse rho).tube j).direction‖

/--
Direction control at the representative of the rho-cell containing `q`.

This is the only root-relative geometric input used by the Córdoba proof
beyond the explicit scale-cover and Property-(P) data.
-/
def WZ1RootRelativeDirectionBoundStatement : Prop :=
  ∀ {delta sigma epsilon : ℝ},
    ∀ {F : Kakeya.Streamlined.TubeFamily delta},
      ∀ {U : Kakeya.Streamlined.UniformTubeStructure F},
        ∀ {Y refined : Kakeya.Streamlined.TubeShading F},
          ∀ {rho : Kakeya.Streamlined.AdmissibleScale delta},
            ∀ (scale :
                WZ1RootRelativeScaleCoverData
                  (sigma := sigma) (epsilon := epsilon)
                  U refined rho),
              IsSubshading refined Y →
              ∀ (plane : WZ1PlaneMapData Y),
                0 < rho.1 →
                ∀ {j : Fin (U.coarse rho).card},
                  ∀ {p q : Point3},
                    p ∈ scale.coarseShading.carrier j →
                    q ∈ scale.coarseShading.union →
                      |inner ℝ ((U.coarse rho).tube j).direction
                          (plane.planeMap
                            (scale.representative (scale.cell q)))| ≤
                        10 * rho.1 +
                          (plane.lipschitzConstant : ℝ) *
                            (dist p q + 4 * rho.1)

/--
Root-relative WZ1 Lemma 17 Córdoba full-grain conclusion.

The exponent is the paper's `rho^(1+6 epsilon₁+epsilon₃)` lower bound with one
additional `rho^epsilon₁` absorbing the harmonic sum suppressed by
`gtrapprox_rho`.  The condition `tau^2 ≤ 4*rho` is the enlarged-radius scale
relation needed after the fine parent-cell pullback; it still absorbs
Lipschitz variation into a slab of width `O(L rho)`.
-/
def WZ1RootRelativeCordobaSlabLowerStatement : Prop :=
  ∀ epsilon₁ epsilon₂ epsilon₃ : ℝ,
    0 < epsilon₁ → 0 < epsilon₂ → 0 < epsilon₃ →
    epsilon₁ < epsilon₂ → epsilon₂ < epsilon₃ →
    epsilon₁ + epsilon₃ < 1 →
    ∃ rho₀ : ℝ, 0 < rho₀ ∧ rho₀ ≤ 1 / 1000 ∧
      ∀ {delta sigma : ℝ},
        ∀ {F : Kakeya.Streamlined.TubeFamily delta},
          ∀ {U : Kakeya.Streamlined.UniformTubeStructure F},
            ∀ {refined : Kakeya.Streamlined.TubeShading F},
              ∀ {rho tau : Kakeya.Streamlined.AdmissibleScale delta},
                ∀ (rhoCover :
                    WZ1RootRelativeScaleCoverData
                      (sigma := sigma) (epsilon := epsilon₁)
                      U refined rho),
                  ∀ (data :
                      WZ1RootRelativeCordobaData
                        (epsilon₃ := epsilon₃) rhoCover (tau := tau)),
                    0 < rho.1 → rho.1 ≤ rho₀ →
                    rho.1 ≤ tau.1 →
                    tau.1 ^ 2 ≤ 4 * rho.1 →
                    tau.1 ≤ 1 →
                    ∀ {Y : Kakeya.Streamlined.TubeShading F},
                      ∀ (plane : WZ1PlaneMapData Y),
                        IsSubshading refined Y →
                        ∀ q ∈ data.propertyThree.union,
                          ∀ t ∈
                              scalarProjection
                                (plane.planeMap
                                  (rhoCover.representative
                                    (rhoCover.cell q)))
                                (data.propertyThree.union ∩
                                  Metric.closedBall q tau.1),
                            Kakeya.realRpowENN rho.1
                                  (1 + 7 * epsilon₁ + epsilon₃) *
                                ENNReal.ofReal
                                  (tau.1 ^ 2 / 200) ≤
                              volume
                                (data.propertyOne.union ∩
                                  Metric.closedBall q (3 * tau.1) ∩
                                  {x |
                                    |inner ℝ x
                                          (plane.planeMap
                                            (rhoCover.representative
                                              (rhoCover.cell q))) -
                                        t| ≤
                                      20 *
                                        max 1
                                          (plane.lipschitzConstant : ℝ) *
                                        rho.1})

/--
Independent validation boundary for the Córdoba proof while the direction
leaf is still open.
-/
def WZ1RootRelativeCordobaSlabLowerFromDirectionStatement : Prop :=
  WZ1RootRelativeDirectionBoundStatement →
    WZ1RootRelativeCordobaSlabLowerStatement

end Kakeya.Assouad
