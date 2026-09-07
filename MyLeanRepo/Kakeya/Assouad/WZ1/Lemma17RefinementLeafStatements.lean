import MyLeanRepo.Kakeya.Assouad.WZ1.LocalGrainCubeCountStatements

/-!
# Paper leaves for the WZ1 Lemma 17 dependent refinement

The coarse Property-(P) refinement and the induced fine parent-cell pullback
are independent quantitative steps.  Keeping them separate prevents the
fine-density argument from being hidden inside the coarse pruning proof.
-/

namespace Kakeya.Assouad

structure WZ1Lemma17CoarseRefinementData
    {delta sigma epsilon₁ epsilon₂ epsilon₃ : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    (first :
      WZ1BalancedCoverData
        (sigma := sigma) (epsilon := epsilon₁) U Y rho)
    (tau : Kakeya.Streamlined.AdmissibleScale delta)
    (tauAtRho : Kakeya.Streamlined.AdmissibleScale rho.1)
    (tauCover :
      WZ1BalancedCoverData
        (sigma := sigma) (epsilon := epsilon₂)
        first.coarseUniform first.coarseShading tauAtRho)
    (robustScale : Kakeya.Streamlined.AdmissibleScale rho.1)
    (robustCover :
      WZ1BalancedCoverData
        (sigma := sigma) (epsilon := epsilon₁)
        first.coarseUniform tauCover.refined robustScale) where
  propertyOne :
    Kakeya.Streamlined.TubeShading (U.coarse rho)
  propertyOne_sub_robust :
    IsSubshading propertyOne robustCover.refined
  propertyOne_sub_tau :
    IsSubshading propertyOne tauCover.refined
  propertyOne_extremal :
    WZ1ExtremalPair sigma epsilon₂
      (U.coarse rho) first.coarseUniform propertyOne
  constantShading :
    Kakeya.Streamlined.TubeShading (U.coarse rho)
  constant_subshading :
    IsSubshading constantShading propertyOne
  multiplicity : ℕ
  multiplicity_pos : 0 < multiplicity
  constant_multiplicity :
    constantShading.HasConstantMultiplicity
      multiplicity (2 * multiplicity)
  multiplicity_lower :
    Kakeya.realRpowENN rho.1 (-sigma + epsilon₁) ≤
      (2 * multiplicity : ENNReal)
  propertyThree :
    Kakeya.Streamlined.TubeShading (U.coarse rho)
  propertyThree_subshading :
    IsSubshading propertyThree constantShading
  propertyThree_extremal :
    WZ1ExtremalPair sigma epsilon₂
      (U.coarse rho) first.coarseUniform propertyThree
  propertyOne_full :
    ∀ j p, p ∈ propertyOne.carrier j →
      Kakeya.realRpowENN rho.1 (2 + 2 * epsilon₁) *
          ENNReal.ofReal tau.1 ≤
        MeasureTheory.volume
          (propertyOne.carrier j ∩ Metric.closedBall p tau.1)
  propertyThree_full :
    ∀ j p, p ∈ propertyThree.carrier j →
      Kakeya.realRpowENN rho.1 (2 + 2 * epsilon₁) *
          ENNReal.ofReal tau.1 ≤
        MeasureTheory.volume
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

structure WZ1Lemma17FineParentCellPullbackData
    {delta sigma epsilon₁ epsilon₂ : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    (first :
      WZ1BalancedCoverData
        (sigma := sigma) (epsilon := epsilon₁) U Y rho)
    (propertyThree :
      Kakeya.Streamlined.TubeShading (U.coarse rho)) where
  fineShading : Kakeya.Streamlined.TubeShading F
  fine_subshading : IsSubshading fineShading first.refined
  fine_extremal :
    WZ1ExtremalPair sigma epsilon₂ F U fineShading
  fine_supported_on_propertyThree_cell :
    ∀ i p, p ∈ fineShading.carrier i →
      ∃ q,
        q ∈ propertyThree.carrier ((U.cover rho).parent i) ∧
          first.cell q = first.cell p

def WZ1Lemma17CoarseRefinementStatement : Prop :=
  ∀ epsilon₁ epsilon₂ epsilon₃ : ℝ,
    0 < epsilon₁ →
    0 < epsilon₂ →
    0 < epsilon₃ →
    epsilon₁ < epsilon₂ →
    epsilon₂ < epsilon₃ →
    epsilon₁ + epsilon₃ < 1 →
    ∃ rho₀ : ℝ, 0 < rho₀ ∧ rho₀ ≤ 1 / 1000 ∧
      ∀ {delta sigma : ℝ},
        ∀ {F : Kakeya.Streamlined.TubeFamily delta},
          ∀ {U : Kakeya.Streamlined.UniformTubeStructure F},
            ∀ {Y : Kakeya.Streamlined.TubeShading F},
              ∀ {rho : Kakeya.Streamlined.AdmissibleScale delta},
                ∀ (first :
                    WZ1BalancedCoverData
                      (sigma := sigma) (epsilon := epsilon₁)
                      U Y rho),
                  ∀ (tau : Kakeya.Streamlined.AdmissibleScale delta),
                    ∀ (tauAtRho :
                        Kakeya.Streamlined.AdmissibleScale rho.1),
                      ∀ (tauCover :
                          WZ1BalancedCoverData
                            (sigma := sigma) (epsilon := epsilon₂)
                            first.coarseUniform first.coarseShading
                              tauAtRho),
                        ∀ (robustScale :
                            Kakeya.Streamlined.AdmissibleScale rho.1),
                          ∀ (robustCover :
                              WZ1BalancedCoverData
                                (sigma := sigma) (epsilon := epsilon₁)
                                first.coarseUniform tauCover.refined
                                  robustScale),
                            0 < sigma → sigma < 1 →
                            0 < rho.1 → rho.1 ≤ rho₀ →
                            tauAtRho.1 = tau.1 →
                            robustScale.1 =
                              Real.rpow rho.1 epsilon₃ →
                            rho.1 ≤ tau.1 →
                            tau.1 ≤ 1 →
                            ∀ D : ℕ, 0 < D →
                              (∀ p ∈ robustCover.refined.union,
                                ∀ i,
                                  p ∈ robustCover.refined.carrier i →
                                    (wz1CloseDirectionCount
                                        robustCover.refined p i
                                          robustScale.1 : ENNReal) ≤
                                      (D : ENNReal) *
                                        Kakeya.realRpowENN
                                          (rho.1 / robustScale.1)
                                          (-sigma - epsilon₁)) →
                              2 * (D : ENNReal) *
                                  Kakeya.realRpowENN
                                    (rho.1 / robustScale.1)
                                    (-sigma - epsilon₁) <
                                Kakeya.realRpowENN
                                  rho.1 (-sigma + epsilon₁) →
                                Nonempty
                                  (WZ1Lemma17CoarseRefinementData
                                    (epsilon₃ := epsilon₃)
                                    first tau tauAtRho tauCover
                                      robustScale robustCover)

def WZ1Lemma17FineParentCellPullbackStatement : Prop :=
  ∀ epsilon₁ epsilon₂ : ℝ,
    0 < epsilon₁ →
    0 < epsilon₂ →
    epsilon₁ < epsilon₂ →
    epsilon₁ + epsilon₂ < 1 →
    ∃ rho₀ : ℝ, 0 < rho₀ ∧ rho₀ ≤ 1 / 1000 ∧
      ∀ {delta sigma : ℝ},
        ∀ {F : Kakeya.Streamlined.TubeFamily delta},
          ∀ {U : Kakeya.Streamlined.UniformTubeStructure F},
            ∀ {Y : Kakeya.Streamlined.TubeShading F},
              ∀ {rho : Kakeya.Streamlined.AdmissibleScale delta},
                ∀ (first :
                    WZ1BalancedCoverData
                      (sigma := sigma) (epsilon := epsilon₁)
                      U Y rho),
                  ∀ propertyThree :
                      Kakeya.Streamlined.TubeShading (U.coarse rho),
                    0 < sigma → sigma < 1 →
                    0 < rho.1 → rho.1 ≤ rho₀ →
                    wz1Lemma17FinePullbackAbsorptionConstant *
                        Kakeya.realRpowENN delta
                          (epsilon₂ - epsilon₁) ≤
                      Kakeya.realRpowENN rho.1 epsilon₂ →
                    IsSubshading propertyThree first.coarseShading →
                    WZ1ExtremalPair sigma epsilon₂
                      (U.coarse rho) first.coarseUniform propertyThree →
                      Nonempty
                        (WZ1Lemma17FineParentCellPullbackData
                          (epsilon₂ := epsilon₂)
                          first propertyThree)

def WZ1Lemma17SameConfigurationFromLeavesStatement : Prop :=
  WZ1Lemma17CoarseRefinementStatement →
    WZ1Lemma17FineParentCellPullbackStatement →
      WZ1Lemma17SameConfigurationRefinementStatement

end Kakeya.Assouad
