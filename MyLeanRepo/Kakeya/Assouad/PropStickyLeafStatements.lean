import MyLeanRepo.Kakeya.Assouad.PropStickyStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyBoundaryCellPruningStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperRescalingDistinctnessStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperMultiplicityNormalizationStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralGlobalOutputV2Statements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperPostDeletionLargeMassRegularizedStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperFinalBalancedLargeMassStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperBoundaryLogCoefficient
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperLiteralSeparationConstants
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12CoverSynchronization

/-!
# Proof leaves for WZ2 Section 6 `prop: sticky`

The split follows the paper:

1. the one-parent rescaling lemma treats one final full geometric fiber;
2. the proposition constructs the final geometric cover, applies that lemma
   parentwise, and performs the global balancing and multiplicity refinements.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

/--
The coarse-family half of `multiScaleWolffLem`, specialized to the stronger
GWZ exact-scale source convention.

At the caller's exact `rho`, the supplied strict scale witness determines the
final coarse family.  The conclusion constructs only its recursive
nearby-scale CWA, using carrier-faithful literal partitioning covers.
-/
def WZ2PropStickyCoarseNearbyClosureStatement : Prop :=
  ∀ {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {inputConstant outputConstant : ENNReal},
    inputConstant * inputConstant ≤ outputConstant →
    100 < outputConstant →
    WZ2PaperCWAAtEveryScale family inputConstant →
    ∀ rho : Kakeya.Streamlined.AdmissibleScale delta,
      ∀ scaleData :
          WZ2PaperScaleCoverData family rho inputConstant,
        WZ2PaperCWAAtNearbyScales
          scaleData.coarse outputConstant

/--
The rescaled-full-fiber half of `multiScaleWolffLem`.

The source fiber is the strict full geometric fiber of the final caller-scale
cover.  Recursive nearby-scale witnesses use literal strict full fibers;
factor-two assigned covers may appear only as internal adapters after their
fibers have been proved equal to those strict full fibers.
-/
def WZ2PropStickyRescaledFiberNearbyClosureStatement : Prop :=
  ∀ {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {inputConstant outputConstant : ENNReal},
    inputConstant * inputConstant ≤ outputConstant →
    100 < outputConstant →
    WZ2PaperCWAAtEveryScale family inputConstant →
    ∀ rho : Kakeya.Streamlined.AdmissibleScale delta,
      ∀ scaleData :
          WZ2PaperScaleCoverData family rho inputConstant,
        ∀ parent : Fin scaleData.coarse.card,
          Nonempty
            (WZ2PaperStableUnitRescaledFamilyData
              scaleData.cover parent
              scaleData.rho_pos outputConstant)

/--
The multiscale closure used at the start of WZ2 `prop: sticky`.

The source uses the stronger GWZ exact-scale convention.  At the caller's
exact `rho`, select one partitioning cover whose coarse family and every
unit-rescaled full fiber satisfy Assouad Definition 2.12's nearby-scale CWA,
with the requested weaker loss measured at their respective radii.  The
output does not claim exact-scale hereditary stability.
-/
def WZ2PropStickyMultiscaleClosureStatement : Prop :=
  ∀ outputLoss : ℝ, 0 < outputLoss →
    ∃ inputLoss delta₀ : ℝ,
      0 < inputLoss ∧ inputLoss ≤ outputLoss ∧
      0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        ∀ family : Kakeya.Streamlined.TubeFamily delta,
          WZ2PaperCWAAtEveryScale family
              (Kakeya.realRpowENN delta (-inputLoss)) →
          ∀ rho : Kakeya.Streamlined.AdmissibleScale delta,
            Real.rpow delta (1 - outputLoss) ≤ rho.1 →
            rho.1 ≤ Real.rpow delta outputLoss →
              Nonempty
                (WZ2PaperStableScaleCoverData
                  family rho
                  (Kakeya.realRpowENN rho.1 (-outputLoss))
                  (Kakeya.realRpowENN
                    (delta / rho.1) (-outputLoss)))

/-- Closed parameter assembly from the two mathematical closure leaves. -/
def WZ2PropStickyMultiscaleClosureFromPaperLeavesStatement : Prop :=
  WZ2PropStickyCoarseNearbyClosureStatement →
    WZ2PropStickyRescaledFiberNearbyClosureStatement →
      WZ2PropStickyMultiscaleClosureStatement

/--
The paper preparation immediately before applying the one-parent rescaling
lemma.

Paper text:

> “We begin by reducing to the case where each `T ∈ 𝕋` satisfies
> `|Y(T)| ≥ (1/2) δ^η |T|`.”

The same finite regularization must be synchronized with the caller-scale
cover.  The selected strict cover therefore retains stable nearby-scale CWA
on its coarse family and every complete rescaled full fiber.  Its final field
is the absolute full-fiber mass lower bound used to invoke Lemma 3.3.
-/
structure WZ2PaperPreparedStableScaleCoverData
    {delta sourceLoss stableLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading source)
    (rho : Kakeya.Streamlined.AdmissibleScale delta)
    (preparationExponent : ℕ) where
  sourceLoss_lt_stable : sourceLoss < stableLoss
  refinement :
    WZ1PaperRefinement shading preparationExponent
  refined_cubical :
    WZ1PaperIsCubicalShading refinement.refined
  per_tube :
    ∀ index,
      (1 / 2 : ENNReal) *
            Kakeya.realRpowENN delta sourceLoss *
            Kakeya.realRpowENN delta 2 ≤
        MeasureTheory.volume
          (refinement.refined.carrier index)
  stable :
    WZ2PaperStableScaleCoverData
      refinement.selected.family rho
      (Kakeya.realRpowENN rho.1 (-stableLoss))
      (Kakeya.realRpowENN
        (delta / rho.1) (-stableLoss))
  parent_mass :
    ∀ parent : Fin stable.coarse.card,
      Kakeya.realRpowENN delta stableLoss *
            Kakeya.realRpowENN rho.1 2 ≤
        (restrictPaperShading
          (stable.cover.fullFiberSubfamily parent)
          refinement.refined).mass

/--
Prepare the exact caller-scale cover after the initial per-tube and finite
parent-map regularizations.

The scale window is controlled by the proposition's requested output loss;
`stableLoss` is the smaller loss consumed by the one-parent Lemma 3.3.
-/
def WZ2PropStickyPaperPreparedStableCoverStatement : Prop :=
  ∃ preparationExponent : ℕ,
  ∀ scaleLoss stableLoss : ℝ,
    0 < scaleLoss →
    0 < stableLoss →
    stableLoss ≤ scaleLoss →
      ∃ sourceLoss delta₀ : ℝ,
        0 < sourceLoss ∧ sourceLoss < stableLoss ∧
        0 < delta₀ ∧ delta₀ ≤ 1 ∧
        ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
          ∀ source : Kakeya.Streamlined.TubeFamily delta,
            ∀ shading : WZ1PaperTubeShading source,
              ∀ sigma : ℝ,
                WZ2PaperExactScaleExtremal
                    sigma sourceLoss source shading →
                  ∀ rho :
                      Kakeya.Streamlined.AdmissibleScale delta,
                    Real.rpow delta (1 - scaleLoss) ≤ rho.1 →
                    rho.1 ≤ Real.rpow delta scaleLoss →
                      Nonempty
                        (WZ2PaperPreparedStableScaleCoverData
                          (sourceLoss := sourceLoss)
                          (stableLoss := stableLoss)
                          shading rho preparationExponent)

/--
Paper `multiScaleWolffLem` after the initial repeated-pigeonholing step.

The stronger GWZ exact-scale source supplies a strict cover at every grid
scale and at the caller itself.  Insert that literal caller cover into one
nested tree, then prune only whole parent branches.  The resulting selected
family retains the caller cover and satisfies the paper nearby-scale window.
-/
def wz2PaperPreparedOneParentDepth (sourceLoss : ℝ) : ℕ :=
  Nat.ceil (1 / sourceLoss) + 2

def wz2PaperPreparedOneParentFiniteLoss (sourceLoss : ℝ) : ENNReal :=
  (packingConstant10000 : ENNReal) *
    (2 : ENNReal) ^ wz2PaperPreparedOneParentDepth sourceLoss

def wz2PaperBoundaryAbsorptionConstant : ENNReal :=
  (8 : ENNReal) * 24000000 *
    ((55296 * Kakeya.deltaTubeVolume 1) + 1)

structure WZ2PaperCallerStrictPreparationData
    {delta sourceLoss stableLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    (shading : WZ1PaperTubeShading source)
    (caller : Kakeya.Streamlined.AdmissibleScale delta)
    (preparationExponent : ℕ) where
  delta_pos : 0 < delta
  sourceLoss_pos : 0 < sourceLoss
  sourceLoss_lt_stable : sourceLoss < stableLoss
  sourceLoss_boundary_budget :
    16 * sourceLoss < stableLoss
  caller_lower_stable :
    Real.rpow delta (1 - stableLoss) ≤ caller.1
  boundary_mass_absorption :
    wz2PaperBoundaryAbsorptionConstant *
        (ENNReal.ofReal
          (wz2PaperBoundaryLogCoefficient *
            (1 + Real.log delta⁻¹))) ^ 5 ≤
      Kakeya.realRpowENN delta
        (-(stableLoss / 2 - 5 * sourceLoss))
  refinement :
    WZ1PaperRefinement shading preparationExponent
  refined_cubical :
    WZ1PaperIsCubicalShading refinement.refined
  per_tube :
    ∀ index,
      (1 / 2 : ENNReal) *
            Kakeya.realRpowENN delta sourceLoss *
            Kakeya.realRpowENN delta 2 ≤
        MeasureTheory.volume
          (refinement.refined.carrier index)
  structuralLoss : ℝ
  structuralLoss_pos : 0 < structuralLoss
  structuralLoss_eq_eight_source :
    structuralLoss = 8 * sourceLoss
  structuralLoss_le_stable :
    structuralLoss ≤ stableLoss
  structuralConstant : ENNReal
  structuralConstant_eq :
    structuralConstant =
      Kakeya.realRpowENN delta (-structuralLoss)
  closureConstant : ENNReal
  closureConstant_eq :
    closureConstant =
      (1000000 : ENNReal) * structuralConstant ^ 2
  nestedJohn_le_closure :
    (81000000 : ENNReal) * structuralConstant ≤
      closureConstant
  closure_le_coarse :
    closureConstant ≤
      Kakeya.realRpowENN caller.1 (-stableLoss)
  closure_le_fiber :
    closureConstant ≤
      Kakeya.realRpowENN
        (delta / caller.1) (-stableLoss)
  caller_tree_safe :
    100 * delta ≤ caller.1
  caller_five_le_one :
    5 * caller.1 ≤ 1
  levelCount : ℕ
  levelCount_eq :
    levelCount = Nat.ceil (1 / sourceLoss) + 1
  strictScaleCount : ℕ
  strictScaleCount_pos : 0 < strictScaleCount
  strictScaleCount_le :
    strictScaleCount ≤ levelCount + 1
  selected_cardinality_retention :
    Kakeya.realRpowENN delta sourceLoss * source.enncard ≤
      (2 *
          (packingConstant10000 : ENNReal) ^ strictScaleCount *
          (2 : ENNReal) ^ strictScaleCount *
          (55296 * Kakeya.deltaTubeVolume 1)) *
        refinement.selected.family.enncard
  selected_card_pos :
    0 < refinement.selected.family.card
  topLevelDimensionConstant : ℕ
  topLevelDimensionConstant_pos :
    0 < topLevelDimensionConstant
  selectedTopLevelConstant : ENNReal
  selectedTopLevelConstant_eq :
    selectedTopLevelConstant =
      ((Kakeya.realRpowENN delta sourceLoss)⁻¹ *
          (2 *
            (packingConstant10000 : ENNReal) ^ strictScaleCount *
            (2 : ENNReal) ^ strictScaleCount *
            (55296 * Kakeya.deltaTubeVolume 1))) *
        ((topLevelDimensionConstant : ENNReal) *
          Kakeya.realRpowENN delta (-sourceLoss))
  selected_top_level_convex_wolff :
    WZ2PaperConvexWolffBound
      refinement.selected.family selectedTopLevelConstant
  boundaryMergedTopLevelConstant : ENNReal
  boundaryMergedTopLevelConstant_eq :
    boundaryMergedTopLevelConstant =
      ((((1 / 2 : ENNReal) *
            Kakeya.realRpowENN delta sourceLoss)⁻¹ *
          (wz2PaperPreparedOneParentFiniteLoss sourceLoss *
            (55296 * Kakeya.deltaTubeVolume 1))) *
        selectedTopLevelConstant)
  boundaryMergedTopLevelConstant_le :
    boundaryMergedTopLevelConstant ≤
      Kakeya.realRpowENN delta (-4 * sourceLoss)
  strictScale :
    Fin strictScaleCount →
      Kakeya.Streamlined.AdmissibleScale delta
  strictScaleData :
    ∀ coordinate,
      WZ2PaperScaleCoverData
        refinement.selected.family
        (strictScale coordinate)
        structuralConstant
  sourceExactCWA :
    WZ2PaperCWAAtEveryScale source
      (Kakeya.realRpowENN delta (-sourceLoss))
  strictAmbientScaleData :
    ∀ coordinate,
      WZ2PaperScaleCoverData
        source
        (strictScale coordinate)
        (Kakeya.realRpowENN delta (-sourceLoss))
  strict_ambient_canonical :
    ∀ coordinate,
      HEq (strictAmbientScaleData coordinate)
        (Classical.choice
          (sourceExactCWA.2.2.2 (strictScale coordinate)))
  selectedFiberConstant : ENNReal
  pure_restriction_constant_le :
    max selectedFiberConstant
        (((Kakeya.realRpowENN delta sourceLoss)⁻¹ *
            (Kakeya.realRpowENN delta (-sourceLoss) *
              ((2 *
                  (packingConstant10000 : ENNReal) ^ strictScaleCount *
                  (2 : ENNReal) ^ strictScaleCount) *
                (55296 * Kakeya.deltaTubeVolume 1) *
                selectedFiberConstant)) *
          Kakeya.realRpowENN delta (-sourceLoss))) ≤
      structuralConstant
  strict_coarse_eq :
    ∀ coordinate,
      (strictScaleData coordinate).coarse =
        ((strictAmbientScaleData coordinate).cover
          |>.hitParentSubfamily refinement.selected).family
  strict_cover_eq :
    ∀ coordinate,
      HEq (strictScaleData coordinate).cover
        ((strictAmbientScaleData coordinate).cover
          |>.restrictToHitParents refinement.selected)
  strict_hit_full_fiber_uniform_tight :
    ∀ coordinate,
      ∀ first second :
          Fin ((strictAmbientScaleData coordinate).cover
            |>.hitParentSubfamily refinement.selected).family.card,
        wz2PaperFullFiberCount
            refinement.selected.family
            ((strictAmbientScaleData coordinate).cover
              |>.hitParentSubfamily refinement.selected).family first ≤
          selectedFiberConstant *
            wz2PaperFullFiberCount
              refinement.selected.family
              ((strictAmbientScaleData coordinate).cover
                |>.hitParentSubfamily refinement.selected).family second
  strict_synchronization :
    (∀ rho : Kakeya.Streamlined.AdmissibleScale delta,
      let scaleData :=
        Classical.choice
          (sourceExactCWA.2.2.2 rho)
      WZ2PaperPureInternalCoverSynchronization
        source scaleData.coarse scaleData.cover) →
      ∀ coordinate,
        WZ2PaperPureInternalCoverSynchronization
          refinement.selected.family
          (strictScaleData coordinate).coarse
          (strictScaleData coordinate).cover
  strict_parent_nested :
    ∀ level,
      ∀ hnext : level + 1 < strictScaleCount,
        ∀ first second : Fin refinement.selected.family.card,
          (strictScaleData ⟨level + 1, hnext⟩).cover.parent first =
              (strictScaleData ⟨level + 1, hnext⟩).cover.parent second →
            (strictScaleData
                ⟨level, Nat.lt_of_succ_lt hnext⟩).cover.parent first =
              (strictScaleData
                ⟨level, Nat.lt_of_succ_lt hnext⟩).cover.parent second
  strict_hit_parent_separated :
    ∀ coordinate,
      ∀ first second :
          Fin (strictScaleData coordinate).coarse.card,
        first ≠ second →
          wz2PaperLiteralSourceSeparationFactor * (strictScale coordinate).1 <
            wz1PaperLineDistance
              ((strictScaleData coordinate).coarse.tube first)
              ((strictScaleData coordinate).coarse.tube second)
  callerStrict :
    WZ2PaperScaleCoverData
      refinement.selected.family caller structuralConstant
  callerLevel : Fin strictScaleCount
  callerScale_eq :
    strictScale callerLevel = caller
  callerScaleData_eq :
    HEq (strictScaleData callerLevel) callerStrict
  caller_parent_nested :
    ∀ coordinate,
      coordinate.val ≤ callerLevel.val →
        ∀ first second :
            Fin refinement.selected.family.card,
          callerStrict.cover.parent first =
              callerStrict.cover.parent second →
            (strictScaleData coordinate).cover.parent first =
              (strictScaleData coordinate).cover.parent second
  caller_hit_parent_separated :
    ∀ first second : Fin callerStrict.coarse.card,
      first ≠ second →
        wz2PaperLiteralSourceSeparationFactor * caller.1 <
          wz1PaperLineDistance
            (callerStrict.coarse.tube first)
            (callerStrict.coarse.tube second)
  strictRepresentative :
    Kakeya.Streamlined.AdmissibleScale delta →
      Fin strictScaleCount
  representative_coarse_of_caller_le :
    ∀ requested,
      caller.1 ≤ requested.1 →
        (strictRepresentative requested).val ≤ callerLevel.val
  strict_caller_representative_nested :
    2 * caller.1 ≤
      (strictScale (strictRepresentative caller)).1
  representative_fine_of_structural_le_caller :
    ∀ requested,
      structuralConstant * ENNReal.ofReal requested.1 ≤
          ENNReal.ofReal caller.1 →
        callerLevel.val ≤
          (strictRepresentative requested).val
  strict_requested_le :
    ∀ requested,
      requested.1 ≤
        (strictScale (strictRepresentative requested)).1
  strict_within_structural_window :
    ∀ requested,
      ENNReal.ofReal
          (strictScale (strictRepresentative requested)).1 <
        structuralConstant * ENNReal.ofReal requested.1
  strict_within_window :
    ∀ requested,
      ENNReal.ofReal
          (strictScale (strictRepresentative requested)).1 <
        Kakeya.realRpowENN delta (-stableLoss) *
          ENNReal.ofReal requested.1
  cwa_nearby :
    WZ2PaperCWAAtNearbyScales
      refinement.selected.family
      structuralConstant
  caller_parent_mass :
    ∀ parent : Fin callerStrict.coarse.card,
      Kakeya.realRpowENN delta stableLoss *
            Kakeya.realRpowENN caller.1 2 ≤
        (restrictPaperShading
          (callerStrict.cover.fullFiberSubfamily parent)
          refinement.refined).mass

/--
Initial per-tube pruning and all finite parent-map regularizations, synchronized
with the caller's exact strict cover.

Unlike the rejected thickening route, this stage retains the exact caller
partitioning witness supplied by the stronger GWZ source convention.  It
therefore pays only fixed finite/polylogarithmic losses.
-/
def WZ2PropStickyPaperCallerStrictPreparationStatement : Prop :=
  ∃ preparationExponent : ℕ,
  ∀ scaleLoss stableLoss : ℝ,
    0 < scaleLoss →
    0 < stableLoss →
    stableLoss ≤ scaleLoss →
      ∃ sourceLoss delta₀ : ℝ,
        0 < sourceLoss ∧ sourceLoss < stableLoss ∧
        16 * sourceLoss < stableLoss ∧
        0 < delta₀ ∧ delta₀ ≤ 1 ∧
        ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
          ∀ source : Kakeya.Streamlined.TubeFamily delta,
            ∀ shading : WZ1PaperTubeShading source,
              ∀ sigma : ℝ,
                WZ2PaperExactScaleExtremal
                    sigma sourceLoss source shading →
                  ∀ caller :
                      Kakeya.Streamlined.AdmissibleScale delta,
                    Real.rpow delta (1 - scaleLoss) ≤ caller.1 →
                    caller.1 ≤ Real.rpow delta scaleLoss →
                      Nonempty
                        (WZ2PaperCallerStrictPreparationData
                          (sourceLoss := sourceLoss)
                          (stableLoss := stableLoss)
                          shading caller preparationExponent)

/--
Stable caller cover built on the exact same strict caller witness.

The output may prove nearby-scale CWA using the finite strict schedule, but it
must not change the caller coarse family, the caller partitioning cover, or
the selected fine family.  The parent mass field is the exact Lemma 3.3 input.
-/
structure WZ2PaperStableCallerFromStrictData
    {delta sourceLoss stableLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {shading : WZ1PaperTubeShading source}
    {caller : Kakeya.Streamlined.AdmissibleScale delta}
    {preparationExponent : ℕ}
    (prepared :
      WZ2PaperCallerStrictPreparationData
        (sourceLoss := sourceLoss)
        (stableLoss := stableLoss)
        shading caller preparationExponent) where
  stable :
    WZ2PaperStableScaleCoverData
      prepared.refinement.selected.family caller
      (Kakeya.realRpowENN caller.1 (-stableLoss))
      (Kakeya.realRpowENN
        (delta / caller.1) (-stableLoss))
  coarse_eq :
    stable.coarse = prepared.callerStrict.coarse
  cover_eq :
    HEq stable.cover prepared.callerStrict.cover
  parent_mass :
    ∀ parent : Fin stable.coarse.card,
      Kakeya.realRpowENN delta stableLoss *
            Kakeya.realRpowENN caller.1 2 ≤
        (restrictPaperShading
          (stable.cover.fullFiberSubfamily parent)
          prepared.refinement.refined).mass

def WZ2PropStickyPaperStableCallerFromStrictStatement : Prop :=
  ∀ {delta sourceLoss stableLoss : ℝ},
    ∀ {source : Kakeya.Streamlined.TubeFamily delta},
      ∀ {shading : WZ1PaperTubeShading source},
        ∀ {caller :
            Kakeya.Streamlined.AdmissibleScale delta},
          ∀ {preparationExponent : ℕ},
            ∀ (prepared :
                WZ2PaperCallerStrictPreparationData
                  (sourceLoss := sourceLoss)
                  (stableLoss := stableLoss)
                  shading caller preparationExponent),
              Nonempty
                (WZ2PaperStableCallerFromStrictData prepared)

/-- Mechanical record assembly from the two corrected preparation stages. -/
def WZ2PropStickyPaperPreparedStableCoverFromStagesStatement : Prop :=
  WZ2PropStickyPaperCallerStrictPreparationStatement →
  WZ2PropStickyPaperStableCallerFromStrictStatement →
    WZ2PropStickyPaperPreparedStableCoverStatement

/--
The active one-parent rescaling lemma in the cropped WZ2 paper model.

The input is the unit-rescaled full geometric parent fiber already produced by
the multiscale closure, together with its hereditary every-scale cover data.
The source refinement is performed on the genuine full-fiber subfamily and
must restore top-level essential distinctness on the target, exactly as in
the paper after (3.3).  It does not assert either that an unrescaled subfamily
inherits the ambient normalized CWA or that the complete rescaled fiber is
already essentially distinct.
-/
def WZ2PropStickyPaperLemma3_3Statement : Prop :=
  WZ2PaperStrongSourceSeparationTransferStatement →
  ∃ logExponent : ℕ,
  ∀ sigma outputLoss : ℝ,
    0 < outputLoss →
    HasWZ2PaperCriticalVolumeFloor sigma →
      ∃ inputLoss strongLoss delta₀ : ℝ,
        0 < inputLoss ∧ inputLoss ≤ strongLoss ∧
        0 < strongLoss ∧ 3 * strongLoss ≤ outputLoss ∧
        0 < delta₀ ∧ delta₀ ≤ 1 ∧
        ∀ {delta rho : ℝ},
          0 < delta → delta ≤ delta₀ →
          Real.rpow delta (1 - outputLoss) ≤ rho →
          rho ≤ Real.rpow delta outputLoss →
          ∀ hrho : 0 < rho,
          ∀ {fine : Kakeya.Streamlined.TubeFamily delta},
            ∀ {coarse : Kakeya.Streamlined.TubeFamily rho},
              ∀ (cover : WZ2PaperPartitioningCover fine coarse),
                ∀ parent : Fin coarse.card,
                  WZ1PaperIsLineClass
                    (wz2PaperFullFiberSubfamily
                      fine coarse parent).family →
                  WZ1PaperIsEssentiallyDistinct
                    (wz2PaperFullFiberSubfamily
                      fine coarse parent).family →
                    ∀ stable :
                        WZ2PaperStableUnitRescaledFamilyData
                          cover parent hrho
                          (Kakeya.realRpowENN
                            (delta / rho) (-inputLoss)),
                      ∀ fineShading :
                          WZ1PaperTubeShading
                            (wz2PaperFullFiberSubfamily
                              fine coarse parent).family,
                        WZ1PaperIsCubicalShading fineShading →
                  Kakeya.realRpowENN delta inputLoss *
                      Kakeya.realRpowENN rho 2 ≤
                    fineShading.mass →
                  Nonempty
                    (WZ2PaperLiteralLemma3_3Data
                      (sigma := sigma)
                      (strongLoss := strongLoss)
                      (outputLoss := outputLoss)
                      fineShading (coarse.tube parent)
                      hrho logExponent)

/--
The active WZ2 `prop: sticky` assembly after multiscale closure and the
one-parent rescaling lemma.
-/
def WZ2PropStickyFromPaperLeavesStatement : Prop :=
  WZ2PaperPostDeletionLargeMassRegularizedStatement →
    WZ2PaperFinalBalancedLargeMassStatement →
      WZ2PropStickyPaperPreparedStableCoverStatement →
        WZ2PropStickyPaperLemma3_3Statement →
          WZ2PropStickyPaperMultiplicityNormalizationStatement →
            WZ2PropStickyBoundaryCellPruningStatement →
              WZ2PropStickyExactCellBalancingStatement →
                WZ2PaperLiteralPropStickyStatementV2

/-- Mechanical active-paper assembly. -/
def WZ2PropStickyAssemblyStatement : Prop :=
  WZ2PaperPostDeletionLargeMassRegularizedStatement →
    WZ2PaperFinalBalancedLargeMassStatement →
      WZ2PropStickyPaperPreparedStableCoverStatement →
        WZ2PropStickyPaperLemma3_3Statement →
          WZ2PropStickyFromPaperLeavesStatement →
            WZ2PropStickyBoundaryCellPruningStatement →
              WZ2PropStickyExactCellBalancingStatement →
                WZ2PaperLiteralPropStickyStatementV2

/--
The structural cover selected before the shading-balancing argument.

This is the exact WZ2 analogue of `multiScaleWolffLem` at the caller's scale:
the retained fine family has one geometric partitioning cover, and the coarse
family carries its own independent every-scale structure.  No cross-scale
transition map is asserted.
-/
structure WZ2FormalCarrierPropStickyStructuralCoverData
    {delta sigma inputLoss structuralLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    (sourceUniform :
      Kakeya.Streamlined.UniformTubeStructure source)
    (shading : Kakeya.Streamlined.TubeShading source)
    (rho : Kakeya.Streamlined.AdmissibleScale delta)
    (logExponent : ℕ) where
  selected : Kakeya.Streamlined.TubeSubfamily source
  structuralShading :
    Kakeya.Streamlined.TubeShading selected.family
  subshading :
    ∀ index,
      structuralShading.carrier index ⊆
        shading.carrier (selected.embedding index)
  retained_mass :
    wz1PaperRefinementFraction delta logExponent *
        shading.mass ≤
      structuralShading.mass
  structural_nonempty :
    ∀ index, (structuralShading.carrier index).Nonempty
  fineUniform :
    Kakeya.Streamlined.UniformTubeStructure selected.family
  fine_extremal :
    IsExtremalPair
      sigma structuralLoss
      selected.family fineUniform structuralShading
  coarse : Kakeya.Streamlined.TubeFamily rho.1
  cover :
    Kakeya.Streamlined.TubeCover selected.family coarse
  geometric :
    WZ2GeometricPartitioningCertificate cover
  coarseUniform :
    Kakeya.Streamlined.UniformTubeStructure coarse
  coarse_uniformity_bound :
    coarseUniform.uniformity ≤
      Kakeya.realRpowENN rho.1 (-structuralLoss)
  coarse_frostman_bound :
    coarseUniform.IsFrostmanAtEveryScale
      (Kakeya.realRpowENN rho.1 (-structuralLoss))

/--
Select the paper-semantic geometric cover from the actual WZ2 every-scale
input.

The theorem may refine the fine family and shading by the paper's fixed
polylogarithmic amount.  It must not manufacture transition maps or replace
full carrier-containment fibers by the auxiliary assigned fibers.
-/
def WZ2FormalCarrierPropStickyStructuralCoverStatement : Prop :=
  ∃ logExponent : ℕ,
  ∀ sigma outputLoss : ℝ,
    0 < sigma → sigma < 1 →
    0 < outputLoss →
    HasCriticalVolumeFloor sigma →
      ∃ inputLoss structuralLoss delta₀ : ℝ,
        0 < inputLoss ∧ inputLoss ≤ structuralLoss ∧
        0 < structuralLoss ∧
        3 * structuralLoss < outputLoss ∧
        0 < delta₀ ∧ delta₀ ≤ 1 ∧
        ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
          ∀ source : Kakeya.Streamlined.TubeFamily delta,
            ∀ sourceUniform :
                Kakeya.Streamlined.UniformTubeStructure source,
              ∀ shading :
                  Kakeya.Streamlined.TubeShading source,
                IsExtremalPair
                    sigma inputLoss
                    source sourceUniform shading →
                ∀ rho :
                    Kakeya.Streamlined.AdmissibleScale delta,
                  Real.rpow delta (1 - outputLoss) ≤ rho.1 →
                  rho.1 ≤ Real.rpow delta outputLoss →
                    Nonempty
                      (WZ2FormalCarrierPropStickyStructuralCoverData
                        (sigma := sigma)
                        (inputLoss := inputLoss)
                        (structuralLoss := structuralLoss)
                        sourceUniform shading rho logExponent)

/--
The WZ2 analogue of the one-parent WZ Lemma 3.3 on the already-final
configuration.

The global producer supplies the geometric partitioning certificate and the
parent density obtained after applying the paper's internal refinement lemma.
This leaf constructs the coarse-relative image of the complete final full
fiber and restores WZ2 extremality at radius `delta / rho`.
-/
def WZ2FormalCarrierPropStickyLemma3_3Statement : Prop :=
  ∀ sigma outputLoss : ℝ,
    0 < sigma → sigma < 1 →
    0 < outputLoss →
    HasCriticalVolumeFloor sigma →
      ∃ inputLoss strongLoss delta₀ : ℝ,
        0 < inputLoss ∧ inputLoss ≤ strongLoss ∧
        0 < strongLoss ∧ 3 * strongLoss < outputLoss ∧
        0 < delta₀ ∧ delta₀ ≤ 1 ∧
        ∀ {delta rho : ℝ},
          0 < delta → delta ≤ delta₀ →
          Real.rpow delta (1 - outputLoss) ≤ rho →
          rho ≤ Real.rpow delta outputLoss →
          ∀ hrho : 0 < rho,
          ∀ {fine : Kakeya.Streamlined.TubeFamily delta},
            ∀ {fineUniform :
                Kakeya.Streamlined.UniformTubeStructure fine},
              ∀ {refined :
                  Kakeya.Streamlined.TubeShading fine},
                IsExtremalPair
                    sigma inputLoss fine fineUniform refined →
                ∀ {coarse :
                    Kakeya.Streamlined.TubeFamily rho},
                  ∀ {cover :
                      Kakeya.Streamlined.TubeCover fine coarse},
                    ∀ (geometric :
                        WZ2GeometricPartitioningCertificate cover),
                      ∀ parent : Fin coarse.card,
                        Kakeya.realRpowENN delta inputLoss *
                            (cover.toFactoring.fiberMass parent) ≤
                          cover.toFactoring.fiberShadedMass
                            refined parent →
                        Nonempty
                          (WZ2UnitRescaledFullFiberData
                            (sigma := sigma)
                            (strongLoss := strongLoss)
                            (outputLoss := outputLoss)
                            cover geometric refined parent
                            hrho)

/--
Convert the strong absolute multiplicity and cardinality estimates into the
two cardinality-normalized conclusions of `prop: sticky`.

The fiber half explicitly includes the finite source multiplicity created by
unit-segment rediscretization.
-/
def WZ2FormalCarrierPropStickyMultiplicityNormalizationStatement : Prop :=
  ∀ {delta rho sigma strongLoss outputLoss : ℝ},
    0 < rho → rho ≤ 1 →
    0 < delta / rho → delta / rho ≤ 1 →
    3 * strongLoss ≤ outputLoss →
    ∀ {coarse : Kakeya.Streamlined.TubeFamily rho},
      ∀ {coarseShading :
          Kakeya.Streamlined.TubeShading coarse},
        (∀ point,
          (coarseShading.pointMultiplicity point : ENNReal) ≤
            Kakeya.realRpowENN rho
              (-sigma - strongLoss)) →
        Kakeya.realRpowENN rho
            (-2 + 2 * strongLoss) ≤
          coarse.enncard →
        (∀ point,
          (coarseShading.pointMultiplicity point : ENNReal) ≤
            Kakeya.realRpowENN rho
                (2 - sigma - outputLoss) *
              coarse.enncard) ∧
        ∀ {fine : Kakeya.Streamlined.TubeFamily delta},
          ∀ {refined : Kakeya.Streamlined.TubeShading fine},
            ∀ parent : Fin coarse.card,
              Kakeya.realRpowENN (delta / rho)
                  (-2 + outputLoss - strongLoss) ≤
                wz2FullFiberCount fine coarse parent →
              (∀ point,
                (wz2FullFiberPointMultiplicity
                    coarse refined parent point : ENNReal) ≤
                  Kakeya.realRpowENN (delta / rho)
                    (-sigma - strongLoss)) →
              ∀ point,
                (wz2FullFiberPointMultiplicity
                    coarse refined parent point : ENNReal) ≤
                  Kakeya.realRpowENN (delta / rho)
                      (2 - sigma - outputLoss) *
                    wz2FullFiberCount
                      fine coarse parent

/--
The parentwise synchronization, balancing, and multiplicity part of
`prop: sticky`.
-/
def WZ2FormalCarrierPropStickyFromLemma3_3Statement : Prop :=
  WZ2FormalCarrierPropStickyStructuralCoverStatement →
    WZ2FormalCarrierPropStickyLemma3_3Statement →
      WZ2FormalCarrierPropStickyMultiplicityNormalizationStatement →
        WZ2FormalCarrierPropStickyStatement

/-- Mechanical form of the repaired two-leaf decomposition. -/
def WZ2FormalCarrierPropStickyAssemblyStatement : Prop :=
  WZ2FormalCarrierPropStickyStructuralCoverStatement →
    WZ2FormalCarrierPropStickyLemma3_3Statement →
      WZ2FormalCarrierPropStickyFromLemma3_3Statement →
        WZ2FormalCarrierPropStickyStatement

end Kakeya.Assouad
