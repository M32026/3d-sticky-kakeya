import MyLeanRepo.Kakeya.Assouad.WZ1.PropertyPStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.PlaneMapVerticalBoundStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.ScaleChangedLipschitzStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.SuppliedWeakPlaneMapStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.VerticalConeStatements

/-!
# Anchored global-grain transport

This is the geometric core of WZ1 Proposition 9 after all dependent
configurations have been selected:

* `sourceLocal` supplies the every-scale local AD structure before unit
  rescaling;
* `selectedFiber` supplies the later Property-(P) refinement of the concrete
  unit-rescaled Proposition 5 fiber;
* `changed` is the same rescaled family after the second, prescribed scale
  change that creates the final tube radius and local Lipschitz plane map.

The remaining work is to use the discrete shaded-height witnesses, the
inverse-transpose normal transport, one fixed horizontal orientation interval,
and affine-thickening AD transport to construct the global Lipschitz slope on
the final family.  No independent existential configuration is permitted.
-/

noncomputable section

namespace Kakeya.Assouad

/--
The two horizontal coordinate charts used in the proof of WZ1 Proposition 9.

The vertical coordinate is fixed.  In the second chart the first two
coordinates are interchanged before the standard grain direction
`(1, slope, 0)` is used.
-/
inductive WZ1HorizontalChart where
  | first
  | second
  deriving DecidableEq

namespace WZ1HorizontalChart

/-- Apply the selected horizontal coordinate chart to a point. -/
def mapPoint : WZ1HorizontalChart → Point3 → Point3
  | first, p => p
  | second, p => Kakeya.Assouad.point3 (p 1) (p 0) (p 2)

/-- Grain direction in the original coordinates of the selected chart. -/
def direction : WZ1HorizontalChart → ℝ → Point3
  | first, slope => globalGrainDirection slope
  | second, slope => Kakeya.Assouad.point3 slope 1 0

end WZ1HorizontalChart

/-- Height-dependent scalar projection in a selected horizontal chart. -/
def wz1ChartedGlobalGrainProjection
    (chart : WZ1HorizontalChart) (slope : ℝ → ℝ)
    (E : Set Point3) : Set ℝ :=
  (fun p =>
    inner ℝ p
      (chart.direction (slope (p (2 : Fin 3))))) '' E

/-- Global slab AD control before normalizing the horizontal chart. -/
def HasChartedGlobalSlabAD {δ : ℝ}
    {F : Kakeya.Streamlined.TubeFamily δ}
    (chart : WZ1HorizontalChart)
    (Y : Kakeya.Streamlined.TubeShading F)
    (slope : ℝ → ℝ) (sigma : ℝ) (C : ENNReal) : Prop :=
  ∀ z ∈ Set.Icc (-1 : ℝ) 1,
    IsADSet1
      (wz1ChartedGlobalGrainProjection chart slope
        (globalGrainSlab Y.union z δ))
      δ (1 - sigma) C

/-- Lipschitz global grains before the horizontal chart is normalized. -/
structure WZ1ChartedLipschitzGlobalGrainData
    {delta : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (chart : WZ1HorizontalChart)
    (Y : Kakeya.Streamlined.TubeShading F)
    (sigma : ℝ) (C : ENNReal) where
  slope : ℝ → ℝ
  lipschitzConstant : NNReal
  lipschitz :
    LipschitzOnWith lipschitzConstant slope (Set.Icc (-1 : ℝ) 1)
  global_slab_ad :
    HasChartedGlobalSlabAD chart Y slope sigma C

/-- The final same-configuration output of the anchored transport step. -/
structure WZ1AnchoredGlobalGrainData
    {fineDelta sigma changedBalancedLoss transportInputLoss
      sourceIncidenceScale : ℝ}
    {F : Kakeya.Streamlined.TubeFamily fineDelta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    {targetScale : Kakeya.Streamlined.AdmissibleScale fineDelta}
    (changedBalanced :
      WZ1BalancedCoverData
        (sigma := sigma) (epsilon := changedBalancedLoss)
        U Y targetScale)
    (changedSourcePlaneMap :
      WZ1WeakPlaneMapData Y sourceIncidenceScale)
    (changed :
      WZ1ScaleChangedLipschitzPlaneMapData
        (sigma := sigma)
        (balancedLoss := changedBalancedLoss)
        (outputLoss := transportInputLoss)
        U Y targetScale changedBalanced changedSourcePlaneMap)
    (outputLoss : ℝ) where
  chart : WZ1HorizontalChart
  shading :
    Kakeya.Streamlined.TubeShading
      (U.coarse targetScale)
  subshading : IsSubshading shading changed.shading
  vertical_chart :
    IsInVerticalChart (U.coarse targetScale)
  extremal :
    WZ1ExtremalPair sigma outputLoss
      (U.coarse targetScale)
      changedBalanced.coarseUniform shading
  planeMap : WZ1PlaneMapData shading
  planeMap_eq :
    planeMap.planeMap = changed.planeMap.planeMap
  planeMap_lipschitzConstant_eq :
    planeMap.lipschitzConstant =
      changed.planeMap.lipschitzConstant
  globalGrains :
    WZ1ChartedLipschitzGlobalGrainData chart shading sigma
      (Kakeya.realRpowENN targetScale.1 (-outputLoss))
  slope_lipschitz_bound :
    (globalGrains.lipschitzConstant : ENNReal) ≤
      Kakeya.realRpowENN targetScale.1 (-outputLoss)
  slope_bound :
    ∀ z ∈ Set.Icc (-1 : ℝ) 1,
      |globalGrains.slope z| ≤ 3
  planeMap_vertical_bound :
    ∀ p ∈ shading.union,
      |planeMap.planeMap p (2 : Fin 3)| ≤ 1 / 2
  planeMap_lipschitz_bound :
    (planeMap.lipschitzConstant : ENNReal) ≤
      Kakeya.realRpowENN targetScale.1 (-outputLoss)

/--
Exact provenance for normalizing a charted global-grain configuration.

For the first chart this is the identity transport.  For the second chart it
is the simultaneous swap of coordinates `0` and `1` on every tube, shading,
coarse family, and plane-map normal.  The explicit index equivalences prevent
the normalization theorem from choosing an unrelated extremal family.
-/
structure WZ1HorizontalChartNormalizationData
    {fineDelta sigma changedBalancedLoss transportInputLoss outputLoss
      sourceIncidenceScale : ℝ}
    {F : Kakeya.Streamlined.TubeFamily fineDelta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    {targetScale : Kakeya.Streamlined.AdmissibleScale fineDelta}
    {changedBalanced :
      WZ1BalancedCoverData
        (sigma := sigma) (epsilon := changedBalancedLoss)
        U Y targetScale}
    {changedSourcePlaneMap :
      WZ1WeakPlaneMapData Y sourceIncidenceScale}
    {changed :
      WZ1ScaleChangedLipschitzPlaneMapData
        (sigma := sigma)
        (balancedLoss := changedBalancedLoss)
        (outputLoss := transportInputLoss)
        U Y targetScale changedBalanced changedSourcePlaneMap}
    (charted :
      WZ1AnchoredGlobalGrainData
        changedBalanced changedSourcePlaneMap changed outputLoss) where
  output :
    WZ1GlobalPlaninessData sigma outputLoss targetScale.1
  sourceIndex :
    Fin output.family.card ≃ Fin (U.coarse targetScale).card
  tube_base_eq :
    ∀ i,
      (output.family.tube i).base =
        charted.chart.mapPoint
          ((U.coarse targetScale).tube (sourceIndex i)).base
  tube_direction_eq :
    ∀ i,
      (output.family.tube i).direction =
        charted.chart.mapPoint
          ((U.coarse targetScale).tube (sourceIndex i)).direction
  shading_carrier_eq :
    ∀ i,
      output.shading.carrier i =
        charted.chart.mapPoint ''
          charted.shading.carrier (sourceIndex i)
  planeMap_eq :
    ∀ p ∈ charted.shading.union,
      output.planeMap.planeMap (charted.chart.mapPoint p) =
        charted.chart.mapPoint (charted.planeMap.planeMap p)
  slope_eq :
    output.global_grains.slope = charted.globalGrains.slope
  uniformity_eq :
    output.uniform.uniformity =
      changedBalanced.coarseUniform.uniformity
  coarseIndex :
    ∀ rho,
      Fin (output.uniform.coarse rho).card ≃
        Fin (changedBalanced.coarseUniform.coarse rho).card
  coarse_tube_base_eq :
    ∀ rho i,
      ((output.uniform.coarse rho).tube i).base =
        charted.chart.mapPoint
          ((changedBalanced.coarseUniform.coarse rho).tube
            (coarseIndex rho i)).base
  coarse_tube_direction_eq :
    ∀ rho i,
      ((output.uniform.coarse rho).tube i).direction =
        charted.chart.mapPoint
          ((changedBalanced.coarseUniform.coarse rho).tube
            (coarseIndex rho i)).direction
  parent_eq :
    ∀ rho i,
      coarseIndex rho ((output.uniform.cover rho).parent i) =
        (changedBalanced.coarseUniform.cover rho).parent
          (sourceIndex i)

/-- Normalize either horizontal chart to the downstream standard chart. -/
def WZ1HorizontalChartNormalizationStatement : Prop :=
  ∀ {fineDelta sigma changedBalancedLoss transportInputLoss outputLoss
      sourceIncidenceScale : ℝ},
    ∀ {F : Kakeya.Streamlined.TubeFamily fineDelta},
      ∀ {U : Kakeya.Streamlined.UniformTubeStructure F},
        ∀ {Y : Kakeya.Streamlined.TubeShading F},
          ∀ {targetScale :
              Kakeya.Streamlined.AdmissibleScale fineDelta},
            ∀ {changedBalanced :
                WZ1BalancedCoverData
                  (sigma := sigma)
                  (epsilon := changedBalancedLoss)
                  U Y targetScale},
              ∀ {changedSourcePlaneMap :
                  WZ1WeakPlaneMapData Y sourceIncidenceScale},
                ∀ {changed :
                    WZ1ScaleChangedLipschitzPlaneMapData
                      (sigma := sigma)
                      (balancedLoss := changedBalancedLoss)
                      (outputLoss := transportInputLoss)
                      U Y targetScale changedBalanced
                      changedSourcePlaneMap},
                  ∀ charted :
                      WZ1AnchoredGlobalGrainData
                        changedBalanced changedSourcePlaneMap
                        changed outputLoss,
                    Nonempty
                      (WZ1HorizontalChartNormalizationData charted)

/--
Transport the source local-grain AD structure through one anchored
unit-rescaled fiber and the dependent second scale change.

`rhoSquared` records the source local-AD scale whose square-root ball has
radius `rho`; `targetScale` is the final radius on the rescaled family.  The
two equalities are the literal scale identities used in the paper.  They are
kept explicit rather than inferred from unrelated admissible-scale witnesses.
-/
def WZ1AnchoredGlobalGrainTransportConclusion : Prop :=
  ∀ sigma outputLoss : ℝ,
    0 < sigma → sigma < 1 → 0 < outputLoss →
      ∃ transportInputLoss sourceDelta₀ : ℝ,
        0 < transportInputLoss ∧
        transportInputLoss < outputLoss ∧
        transportInputLoss < sigma / 2 ∧
        transportInputLoss <
          (sigma / (2 + sigma)) * outputLoss ∧
        0 < sourceDelta₀ ∧ sourceDelta₀ ≤ 1 ∧
        ∀ {sourceDelta localLoss balancedLoss scaleInputLoss
            weakLoss changedBalancedLoss : ℝ},
          ∀ {F : Kakeya.Streamlined.TubeFamily sourceDelta},
            ∀ {U : Kakeya.Streamlined.UniformTubeStructure F},
              ∀ {Y : Kakeya.Streamlined.TubeShading F},
                ∀ {plane : WZ1PlaneMapData Y},
                  ∀ (sourceLocal :
                      WZ1EveryScaleLocalGrainData
                        (sigma := sigma)
                        (outputLoss := localLoss)
                        U Y plane),
                    ∀ {rho :
                        Kakeya.Streamlined.AdmissibleScale sourceDelta},
                      ∀ (anchored :
                          WZ1BalancedCoverRescaledFiberData
                            (sigma := sigma)
                            (inputLoss := balancedLoss)
                            (outputLoss := scaleInputLoss)
                            U sourceLocal.shading rho),
                        ∀ (parent :
                            Fin (U.coarse rho).card),
                          ∀ {baseOutputLoss : ℝ},
                            ∀ (baseFiber :
                                WZ1UnitRescaledFiberData
                                  (inputLoss := balancedLoss)
                                  (outputLoss := baseOutputLoss)
                                  anchored.balanced parent
                                  (lt_of_lt_of_le
                                    anchored.balanced.refined_extremal.1
                                    rho.2.1)),
                              ∀ (selectedFiber :
                                  WZ1PropertyPRescaledFiberData
                                    (propertyOutputLoss := scaleInputLoss)
                                    baseFiber),
                              ∀ (suppliedWeak :
                                  WZ1SuppliedWeakPlaneMapData
                                    (sigma := sigma)
                                    (outputLoss := weakLoss)
                                    selectedFiber.fiber.targetUniform
                                    selectedFiber.fiber.targetShading),
                              ∀ (rhoSquared :
                                  Kakeya.Streamlined.AdmissibleScale
                                    sourceDelta),
                                ∀ (targetScale :
                                    Kakeya.Streamlined.AdmissibleScale
                                      (sourceDelta / rho.1)),
                                  ∀ (changedBalanced :
                                      WZ1BalancedCoverData
                                        (sigma := sigma)
                                        (epsilon := changedBalancedLoss)
                                        selectedFiber.fiber.targetUniform
                                        suppliedWeak.shading
                                        targetScale),
                                  ∀ (changed :
                                      WZ1ScaleChangedLipschitzPlaneMapData
                                        (sigma := sigma)
                                        (balancedLoss :=
                                          changedBalancedLoss)
                                        (outputLoss :=
                                          transportInputLoss)
                                        selectedFiber.fiber.targetUniform
                                        suppliedWeak.shading
                                        targetScale
                                        changedBalanced
                                        suppliedWeak.planeMap),
                                    localLoss ≤ transportInputLoss →
                                    balancedLoss < scaleInputLoss →
                                    scaleInputLoss <
                                      weakLoss →
                                    weakLoss <
                                      changedBalancedLoss →
                                    changedBalancedLoss <
                                      transportInputLoss →
                                    sourceDelta ≤ sourceDelta₀ →
                                    rho.1 =
                                      Real.rpow sourceDelta
                                        (sigma / (2 + sigma)) →
                                    rhoSquared.1 = rho.1 ^ 2 →
                                    targetScale.1 = rho.1 →
                                    Nonempty
                                      (WZ1AnchoredGlobalGrainData
                                        changedBalanced
                                        suppliedWeak.planeMap
                                        changed outputLoss)

/--
The narrow vertical-cone geometry supplies the missing direction input to the
anchored global-grain transport.
-/
def WZ1AnchoredGlobalGrainTransportStatement : Prop :=
  WZ1PropertyPRescaledFiberNarrowConeStatement →
    WZ1ScaleChangedPlaneMapVerticalBoundStatement →
      WZ1AnchoredGlobalGrainTransportConclusion

end Kakeya.Assouad
