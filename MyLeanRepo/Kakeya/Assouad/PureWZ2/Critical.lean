import MyLeanRepo.Kakeya.Assouad.PureWZ2.Core
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12OneScaleRescaling
import MyLeanRepo.Kakeya.AssertionD

/-!
# Pure WZ2 Subunit and critical-exponent statements

The completed hairbrush proof may be reused to prove the first statement, but
the outputs below are formulated only with literal WZ2 Definition 2.12.
-/

noncomputable section

namespace Kakeya.Assouad

/--
One strict-full-fiber localization and John-rescaling certificate to which
Assertion D applies.

The selected source indices come from one complete strict fiber of an actual
nearby-scale Definition 2.12 witness.  The last two fields record the exact
Jacobian/cardinality comparison needed to transfer Assertion D's lower bound
back to the original unbounded configuration.
-/
structure PureWZ2FullFiberAssertionDRefinementData
    {outputEpsilon assertionEpsilon kappa assertionEta delta : ℝ}
    {C : ENNReal}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (shading : Kakeya.Streamlined.TubeShading family) where
  requested : WZ2PaperRequestedScale delta
  nearby :
    WZ2PaperPureNearbyScaleCoverData family requested C
  parent : Fin nearby.scaleData.coarse.card
  strict_fiber_nonempty :
    (wz2PaperOrdinaryFullFiberIndices
      family nearby.scaleData.coarse parent).Nonempty
  johnFiber :
    WZ2PaperPureUnitRescaledFullFiberData
      (fine := family)
      (coarse := nearby.scaleData.coarse)
      parent C
  oneScale :
    WZ2PaperPureOneScaleRescalingBridge
      (fine := family)
      (coarse := nearby.scaleData.coarse)
      parent nearby.scaleData.rho_pos C
  rescaled_delta_pos :
    0 < delta / nearby.rho
  rescaled_delta_le_one :
    delta / nearby.rho ≤ 1
  publicShading :
    Kakeya.Streamlined.TubeShading
      oneScale.bridge.publicFamily
  public_shading_from_source :
    ∀ publicIndex,
      publicShading.carrier publicIndex ⊆
        oneScale.bridge.coordinateChange ''
          (johnFiber.normalization.map ''
            shading.carrier
              ((wz2PaperPureFullFiberSubfamily
                family nearby.scaleData.coarse parent).embedding
                (oneScale.bridge.publicSourceIndex publicIndex)))
  selected :
    Kakeya.Streamlined.TubeSubfamily
      oneScale.bridge.publicFamily
  selected_nonempty : selected.family.Nonempty
  selectedShading :
    Kakeya.Streamlined.TubeShading selected.family
  selected_subshading :
    ∀ index,
      selectedShading.carrier index ⊆
        publicShading.carrier (selected.embedding index)
  selected_cardinality_retention :
    Kakeya.realRpowENN
          (delta / nearby.rho) assertionEpsilon *
        oneScale.bridge.publicFamily.enncard ≤
      selected.family.enncard
  selected_mass_retention :
    Kakeya.realRpowENN
          (delta / nearby.rho) assertionEpsilon *
        publicShading.mass ≤
      selectedShading.mass
  targetFamily :
    Kakeya.TubeFamily (delta / nearby.rho)
  selectedIndex :
    ∀ tube : Kakeya.DeltaTube (delta / nearby.rho),
      tube ∈ targetFamily →
        Fin selected.family.card
  selectedIndex_bijective :
    Function.Bijective
      (fun member :
          {tube : Kakeya.DeltaTube (delta / nearby.rho) //
          tube ∈ targetFamily} =>
        selectedIndex member.1 member.2)
  target_tube_eq :
    ∀ tube : Kakeya.DeltaTube (delta / nearby.rho),
      ∀ membership : tube ∈ targetFamily,
        tube =
          selected.family.tube
            (selectedIndex tube membership)
  target_carrier_contains_common_image :
    ∀ tube : Kakeya.DeltaTube (delta / nearby.rho),
      ∀ membership : tube ∈ targetFamily,
        oneScale.bridge.coordinateChange ''
            (johnFiber.normalization.map ''
              (family.tube
                ((wz2PaperPureFullFiberSubfamily
                  family nearby.scaleData.coarse parent).embedding
                  (oneScale.bridge.publicSourceIndex
                    (selected.embedding
                      (selectedIndex tube membership))))).carrier) ⊆
          tube.carrier
  targetShading : Kakeya.Shading targetFamily
  target_shading_eq_selected :
    ∀ tube : Kakeya.DeltaTube (delta / nearby.rho),
      ∀ membership : tube ∈ targetFamily,
        targetShading.carrier tube =
          selectedShading.carrier
            (selectedIndex tube membership)
  target_union_subset_john_image :
    targetShading.union ⊆
      oneScale.bridge.coordinateChange ''
        (johnFiber.normalization.map '' shading.union)
  target_unit_ball : targetFamily.IsInUnitBall
  target_distinct : targetFamily.IsEssentiallyDistinct
  target_dense :
    targetShading.IsLambdaDense
      (Kakeya.realRpowENN
        (delta / nearby.rho) assertionEta)
  target_katz_tao :
    Kakeya.KatzTaoConvexWolffBound targetFamily
      (Real.rpow (delta / nearby.rho) (-assertionEta))
  target_frostman :
    Kakeya.FrostmanSlabWolffBound targetFamily
      (Real.rpow (delta / nearby.rho) (-assertionEta))
  target_cardinality :
    Kakeya.realRpowENN
        (delta / nearby.rho) (-2 + assertionEpsilon) ≤
      targetFamily.enncard
  pullbackFactor : ENNReal
  pullback_factor_pos : 0 < pullbackFactor
  pullback_factor_ne_top : pullbackFactor ≠ ⊤
  source_power_le_assertion_rhs :
    Kakeya.realRpowENN delta (1 / 2 + outputEpsilon) ≤
      pullbackFactor *
        (ENNReal.ofReal kappa *
          Kakeya.realRpowENN
            (delta / nearby.rho) assertionEpsilon *
          targetFamily.enncard *
          Kakeya.deltaTubeVolume
            (delta / nearby.rho) *
          ENNReal.rpow
            (targetFamily.enncard *
              ENNReal.rpow
                (Kakeya.deltaTubeVolume
                  (delta / nearby.rho)) (1 / 2))
            (-(1 / 2 : ℝ)))
  target_union_pullback :
    pullbackFactor *
        MeasureTheory.volume targetShading.union ≤
      MeasureTheory.volume shading.union

/--
The paper-internal localization needed before the completed hairbrush theorem
can be reused.

The actual nearby scale, complete strict fiber, and John normalization are
part of the output.  This statement must not be replaced by an assigned-fiber
or exact-requested-scale source.
-/
def PureWZ2FullFiberAssertionDRefinementStatement : Prop :=
  ∀ outputEpsilon assertionEpsilon kappa assertionEta : ℝ,
    0 < outputEpsilon →
    0 < assertionEpsilon →
    assertionEpsilon < outputEpsilon →
    0 < kappa →
    0 < assertionEta →
      ∃ inputEta delta₀ : ℝ,
        0 < inputEta ∧
        0 < delta₀ ∧ delta₀ ≤ 1 ∧
        ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
          ∀ family : Kakeya.Streamlined.TubeFamily delta,
            family.Nonempty →
            ∀ shading : Kakeya.Streamlined.TubeShading family,
              WZ2PaperPureCWAAtNearbyScales family
                  (Kakeya.realRpowENN delta (-inputEta)) →
              shading.IsLambdaDense
                  (Kakeya.realRpowENN delta inputEta) →
                Kakeya.realRpowENN delta
                    (1 / 2 + outputEpsilon) ≤
                    MeasureTheory.volume shading.union ∨
                  Nonempty
                    (PureWZ2FullFiberAssertionDRefinementData
                      (outputEpsilon := outputEpsilon)
                      (assertionEpsilon := assertionEpsilon)
                      (kappa := kappa)
                      (assertionEta := assertionEta)
                      (C := Kakeya.realRpowENN delta (-inputEta))
                      shading)

/-- Apply Assertion D to the strict-full-fiber refinement. -/
def PureWZ2WolffFloorFromAssertionDStatement : Prop :=
  Kakeya.AssertionD (1 / 2) 0 →
    PureWZ2FullFiberAssertionDRefinementStatement →
      PureWZ2WolffVolumeFloor

/-- The elementary strict-power argument placing admissibility below one. -/
def PureWZ2WolffFloorImpliesSubunitCeilingStatement : Prop :=
  PureWZ2WolffVolumeFloor →
    ∃ ceiling : ℝ,
      ceiling < 1 ∧
      ¬ PureWZ2Admissible ceiling

/--
Node 1: expose the dangerous model conversion and its two assembly steps,
then provide the pure Wolff floor and a concrete subunit ceiling.
-/
def PureWZ2SubunitPackageStatement : Prop :=
  PureWZ2FullFiberAssertionDRefinementStatement ∧
    PureWZ2WolffFloorFromAssertionDStatement ∧
    PureWZ2WolffFloorImpliesSubunitCeilingStatement ∧
    PureWZ2WolffVolumeFloor ∧
      ∃ ceiling : ℝ,
        ceiling < 1 ∧
        ¬ PureWZ2Admissible ceiling

/-- One normalized pure extremal configuration at a fixed scale. -/
structure PureWZ2ExtremalConfiguration
    (sigma loss delta : ℝ) where
  family : Kakeya.Streamlined.TubeFamily delta
  shading : Kakeya.Streamlined.TubeShading family
  extremal :
    WZ2PaperPureIsExtremal
      sigma loss family shading

/--
The lower-volume consequence of the normalized pure critical exponent.
-/
def PureWZ2CriticalVolumeFloor (sigma : ℝ) : Prop :=
  ∀ floorLoss structuralBudget : ℝ,
    0 < floorLoss →
    0 < structuralBudget →
    ∃ structuralLoss delta₀ : ℝ,
      0 < structuralLoss ∧
      structuralLoss ≤ structuralBudget ∧
      0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        ∀ family : Kakeya.Streamlined.TubeFamily delta,
          family.Nonempty →
          ∀ shading : Kakeya.Streamlined.TubeShading family,
            WZ2PaperPureCWAAtNearbyScales family
                (Kakeya.realRpowENN delta (-structuralLoss)) →
            shading.IsLambdaDense
                (Kakeya.realRpowENN delta structuralLoss) →
              Kakeya.realRpowENN delta (sigma + floorLoss) ≤
                MeasureTheory.volume shading.union

/--
One critical exponent together with the two consequences of its supremum
definition used by the rest of the WZ2 proof.
-/
structure PureWZ2CriticalPackage (sigma : ℝ) : Prop where
  sigma_pos : 0 < sigma
  sigma_lt_one : sigma < 1
  extremal_sequence :
    ∀ loss delta₀ : ℝ,
      0 < loss → 0 < delta₀ →
        ∃ delta : ℝ,
          0 < delta ∧ delta ≤ delta₀ ∧
          Nonempty
            (PureWZ2ExtremalConfiguration
              sigma loss delta)
  critical_floor :
    PureWZ2CriticalVolumeFloor sigma

/--
Node 2: failure of the pure WZ2 theorem produces a subunit critical exponent,
arbitrarily small pure extremizers, and the global pure critical floor.
-/
def PureWZ2CriticalExtractionStatement : Prop :=
  PureWZ2SubunitPackageStatement →
    ¬ PureWZ2Theorem5_2Statement →
      ∃ sigma : ℝ,
        Nonempty (PureWZ2CriticalPackage sigma)

end Kakeya.Assouad

end
