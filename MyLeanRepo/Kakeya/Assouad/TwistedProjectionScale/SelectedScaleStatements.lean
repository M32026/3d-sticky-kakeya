import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.RelationInducedShading
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.SelectedEnvelopeBlockLift
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.SelectedScaleFactoring
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameters
import MyLeanRepo.Kakeya.Assouad.AnisotropicRescaling.WeightedSelection
import MyLeanRepo.Kakeya.Streamlined.Statements

/-!
# Selected-scale Section 7 statements

These propositions consume the dependent block packages defined by the
selected-scale rediscretization infrastructure.  They live outside the base
statement module to avoid a circular import.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

/--
Cross-block conflict degree for one selected-scale four-block family.

Every flattened coarse tube retains the supporting line of its selected
source representative.  A target conflict is first placed in a
`100000 * rho` parameter box, then counted by the source indexed parameter
Frostman bound; the factor four restores the four slots over each selected
representative.
-/
def SelectedScaleFourBlockConflictDegreeStatement : Prop :=
  NonessentialTargetTubeParameterClusterBaseFiveStatement →
    ∀ {delta rho : ℝ},
      0 < rho → rho ≤ 1 / 1000 →
      ∀ fine : Kakeya.Streamlined.TubeFamily delta,
        HasBoundedBase fine 4 →
        IsInVerticalChart fine →
        ∀ C : ENNReal,
          TubeParameterFrostmanBound fine C →
          delta ≤ 100000 * rho →
          100000 * rho ≤ 1 →
          ∀ data : SelectedScaleFourBlockData fine rho,
            ∀ q : Fin data.coarse.card,
              ((Finset.univ.filter fun r =>
                ¬(data.coarse.tube q).EssentiallyDistinct
                  (data.coarse.tube r)).card : ENNReal) ≤
                4 *
                  (C *
                    Kakeya.realRpowENN (100000 * rho) 2 *
                      fine.enncard)

/--
Additive mass loss from clipping the exact selected-scale tube shading to the
iteration window.

The fine shading lies in the positive half-window.  Hence its `rho`-thickening
can leave `[-1,1]` only through the top boundary slab `[1,1+rho]`.  The
vertical-tube cap estimate charges at most `100 rho³` for each indexed coarse
tube.  No multiplicative density conclusion is asserted before this additive
term is absorbed.
-/
def SelectedScaleWindowedShadingMassStatement : Prop :=
  VerticalTubeTopBoundaryVolumeStatement →
    ∀ {delta rho : ℝ},
      0 < rho → rho ≤ 1 / 8 →
      ∀ fine : Kakeya.Streamlined.TubeFamily delta,
        ∀ data : SelectedScaleFourBlockData fine rho,
          IsInVerticalChart fine →
          ∀ Y : Kakeya.Streamlined.TubeShading fine,
            Y.union ⊆ horizontalSlab 0 1 →
              (data.exactTubeRelationInducedShading Y rho).mass ≤
                (relationInducedShading data.relation Y rho).mass +
                  data.coarse.enncard *
                    ENNReal.ofReal (100 * rho ^ 3)

/--
Window clipping for an arbitrary retained lifted shading.

This is the factoring-compatible form of the additive boundary estimate.
The lifted shading need only lie in the `rho`-thickening of a fine shading
supported in the positive half-window; it need not be the full exact relation
shading.  Restricting every lifted carrier to `z ∈ [-1,1]` stays on the same
indexed family, loses at most one `100 rho³` cap per tube, and preserves the
global thickening containment.
-/
def SelectedLiftedWindowClippingStatement : Prop :=
  VerticalTubeTopBoundaryVolumeStatement →
    ∀ {delta rho : ℝ},
      0 < rho → rho ≤ 1 / 8 →
      ∀ fine : Kakeya.Streamlined.TubeFamily delta,
        ∀ Y : Kakeya.Streamlined.TubeShading fine,
          Y.union ⊆ horizontalSlab 0 1 →
          ∀ lifted : Kakeya.Streamlined.TubeFamily rho,
            IsInVerticalChart lifted →
            ∀ Z : Kakeya.Streamlined.TubeShading lifted,
              Z.union ⊆ Metric.cthickening rho Y.union →
                let W := slabRestriction Z (-1) 1
                IsSubshading W Z ∧
                  IsInSlopeWindow W ∧
                  Z.mass ≤
                    W.mass +
                      lifted.enncard *
                        ENNReal.ofReal (100 * rho ^ 3) ∧
                  W.union ⊆ Metric.cthickening rho Y.union

/--
Absorb the additive top-boundary loss into a genuine density on the same
retained lifted family.

The raw lifted shading satisfies the cancellation-free density product
`lambda * mass ≤ L * shadedMass`.  Every radius-`rho` tube has volume at
least `rho²`, so the clipping error `100 rho³` per tube costs at most the
relative fraction `100 rho`.  The explicit budget
`ofReal (200 rho) * L ≤ lambda` leaves one half of the raw density after
clipping.  Finiteness of `lambda` and the nonzero finite loss `L` are stated
at the cancellation boundary.
-/
def SelectedLiftedWindowDensityAbsorptionStatement : Prop :=
  SelectedLiftedWindowClippingStatement →
    ∀ {delta rho : ℝ},
      0 < rho → rho ≤ 1 / 8 →
      ∀ fine : Kakeya.Streamlined.TubeFamily delta,
        ∀ Y : Kakeya.Streamlined.TubeShading fine,
          Y.union ⊆ horizontalSlab 0 1 →
          ∀ lifted : Kakeya.Streamlined.TubeFamily rho,
            IsInVerticalChart lifted →
            ∀ Z : Kakeya.Streamlined.TubeShading lifted,
              Z.union ⊆ Metric.cthickening rho Y.union →
              ∀ lambda L : ENNReal,
                lambda ≠ ⊤ →
                L ≠ 0 → L ≠ ⊤ →
                lambda * lifted.toBodyFamily.mass ≤ L * Z.mass →
                ENNReal.ofReal (200 * rho) * L ≤ lambda →
                  let W := slabRestriction Z (-1) 1
                  IsSubshading W Z ∧
                    IsInSlopeWindow W ∧
                    W.IsLambdaDense ((2 * L)⁻¹ * lambda) ∧
                    W.union ⊆ Metric.cthickening rho Y.union

/--
Terminal branch of the selected-scale iteration.

Once the current scale reaches `delta^(epsilon²)`, the telescoping projection
inequality already implies a lower bound at the original scale.  The only
geometric input is that the `rho`-thickening of a nonempty planar set contains
one radius-`rho` ball and hence has volume at least `rho²`.  This statement is
independent of every coarsening construction and therefore does not revive
the disproved arbitrary-scale coarsening API.
-/
def SelectedScaleTerminalProjectionStatement : Prop :=
  ∀ {delta rho epsilon : ℝ},
    0 < delta → delta < 1 →
    0 < rho →
    0 < epsilon → epsilon < 1 →
    Real.rpow delta (epsilon ^ 2) ≤ rho →
      ∀ X : Set Point2,
        X.Nonempty →
        ∀ V : ENNReal,
          Kakeya.realRpowENN (delta / rho) epsilon *
              MeasureTheory.volume (Metric.cthickening rho X) ≤ V →
            Kakeya.realRpowENN
                delta (epsilon + epsilon ^ 2 * (2 - epsilon)) ≤
              V

/--
Arithmetic dichotomy between the terminal selected scale and the additive
window budget.

When `4 * eta < epsilon^2`, the fixed factor `80000` is absorbed by the
positive exponent gap `epsilon^2 - 4 * eta`.  Hence every nonnegative
selected radius is either already at least `delta^(epsilon^2)`, or is small
enough that the full-family top-cap coefficient `200 * rho` is bounded by
`delta^(4*eta) / 400`.
-/
def SelectedScaleWindowBudgetDichotomyStatement : Prop :=
  ∀ epsilon eta : ℝ,
    0 < epsilon → epsilon < 1 →
    0 < eta → 4 * eta < epsilon ^ 2 →
      ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
        ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
          ∀ rho : ℝ, 0 ≤ rho →
            Real.rpow delta (epsilon ^ 2) ≤ rho ∨
              ENNReal.ofReal (200 * rho) ≤
                ENNReal.ofReal (1 / 400 : ℝ) *
                  Kakeya.realRpowENN delta (4 * eta)

/--
Tube-specific Fubini density for a shaded piece already lying in both tubes.

The full fine tube need not lie in the coarse tube.  This is the exact
geometric weakening needed by a finite relation-valued cover: after splitting
one fine shaded piece among the coarse tubes that cover it, each split piece
lies in one fine tube and one coarse tube.  The conclusion is kept in
cancellation-free product form.
-/
def TubePieceThickeningDensityStatement : Prop :=
  ∀ {delta rho : ℝ},
    0 < delta → delta ≤ rho → rho ≤ 1 →
      ∀ T : Kakeya.DeltaTube delta,
        ∀ S : Kakeya.DeltaTube rho,
          ∀ E : Set Point3,
            MeasurableSet E →
            E ⊆ T.carrier →
            E ⊆ S.carrier →
              ENNReal.ofReal (1 / 100 : ℝ) *
                    MeasureTheory.volume E * S.volume ≤
                Kakeya.deltaTubeVolume delta *
                  MeasureTheory.volume
                    (S.carrier ∩ Metric.cthickening rho E)

/--
Linear density transfer through the selected relation-valued four-tube cover.

Essential distinctness makes the selected-envelope parent map injective:
each selected representative is the unique fine tube in its parent fiber.
Split that fine shaded piece measurably among the four coarse carriers and
apply `TubePieceThickeningDensityStatement` to each piece.  The four slots
cost exactly the factor four, while thickening from radius `delta` to `rho`
supplies the compensating transverse area.  Thus no
`(rho / delta)^2` fiber-Frostman loss and no square of the input density
appears.
-/
def SelectedScaleRelationTubeDensityStatement : Prop :=
  TubeVolumeScalingStatement →
    TubePieceThickeningDensityStatement →
      ∀ {delta rho : ℝ},
        0 < delta → delta ≤ rho → rho ≤ 1 →
          ∀ fine : Kakeya.Streamlined.TubeFamily delta,
            fine.IsEssentiallyDistinct →
              ∀ data : SelectedScaleFourBlockData fine rho,
                ∀ Y : Kakeya.Streamlined.TubeShading fine,
                  ∀ lambda : ENNReal,
                    Y.IsLambdaDense lambda →
                      (ENNReal.ofReal (1 / 400 : ℝ) * lambda) *
                          data.coarse.toBodyFamily.mass ≤
                        (data.exactTubeRelationInducedShading Y rho).mass

/--
Aggregate the GWZ per-parent induced-density estimate over the certified
selected-scale envelope factoring.

The uniform lower bound `lambdaSq` on the squared shaded fiber fractions is
an explicit input.  It is the real output needed from the paper's uniform
refinement; aggregate fine density alone does not imply it.  The factor four
is exactly the number of flattened tube slots over each convex envelope.
-/
def SelectedScaleInducedDensityAggregationStatement : Prop :=
  Kakeya.Streamlined.InducedShadingDensityStatement →
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ A : ℝ, 1 ≤ A ∧
        ∀ {delta rho : ℝ},
          0 < delta → 0 < rho →
          ∀ fine : Kakeya.Streamlined.TubeFamily delta,
            fine.toBodyFamily.IsMeasurable →
            fine.toBodyFamily.IsConvex →
            0 < fine.toBodyFamily.mass →
            fine.toBodyFamily.HasComparableDimensions
              delta delta 1 3 →
            ∀ data : SelectedScaleFourBlockData fine rho,
              ∀ C : ENNReal, 1 ≤ C → C ≠ ⊤ →
                data.toEnvelopeFactoring.FibersAreCFrostman C →
                ∀ Y : Kakeya.Streamlined.TubeShading fine,
                  ∀ lambdaSq : ENNReal,
                    (∀ j,
                      lambdaSq ≤
                        ENNReal.rpow
                          (data.toEnvelopeFactoring.fiberShadedMass Y j /
                            data.toEnvelopeFactoring.fiberMass j) 2) →
                      lambdaSq * data.coarse.toBodyFamily.mass ≤
                        4 *
                            (ENNReal.ofReal A *
                              Kakeya.realRpowENN delta (-epsilon) * C) *
                          (data.exactTubeRelationInducedShading Y rho).mass

/--
Fiber Frostman control for the selected-scale envelope factoring.

At the Section 7 boundary the fine family is already pairwise essentially
distinct.  The recorded failure of essential distinctness with the selected
representative therefore forces every parent fiber to be a singleton.  A
fine `delta`-tube has volume at least `delta²`, while the certified
`rho × rho × 4` envelope with comparison factor `3` has volume at most
`108 rho²`.  Thus every singleton fiber is Frostman with the explicit
scale-ratio loss below.  This is the exact input needed by the generic
factoring-multiplicity adapter; no recursive target `UniformTubeStructure` is
asserted.
-/
def SelectedScaleEnvelopeFiberFrostmanStatement : Prop :=
  ∀ {delta rho : ℝ},
    0 < delta → delta ≤ 1 / 2 →
    0 < rho → delta ≤ rho →
    ∀ fine : Kakeya.Streamlined.TubeFamily delta,
      fine.IsEssentiallyDistinct →
      ∀ data : SelectedScaleFourBlockData fine rho,
        let C : ENNReal :=
          108 * Kakeya.realRpowENN (rho / delta) 2
        1 ≤ C ∧ C ≠ ⊤ ∧
          data.toEnvelopeFactoring.FibersAreCFrostman C

/--
Cardinality retained by one selected-envelope factoring refinement.

Fine-family essential distinctness makes the selected-envelope parent map
injective, while every factoring refinement keeps it surjective.  Hence the
retained fine and envelope subfamilies have the same cardinality.  Equal
`delta`-tube volumes then convert retained shaded mass and input aggregate
density into the cancellation-free cardinality product below.  This is the
normalization bridge needed before transferring source Tube-Wolff and indexed
parameter-Frostman bounds to the lifted block family.
-/
def SelectedScaleFactoringCardinalityRetentionStatement : Prop :=
  TubeVolumeScalingStatement →
    ∀ {delta rho : ℝ},
      0 < delta → delta ≤ 1 →
      ∀ fine : Kakeya.Streamlined.TubeFamily delta,
        fine.IsEssentiallyDistinct →
        ∀ data : SelectedScaleFourBlockData fine rho,
          ∀ Y : Kakeya.Streamlined.TubeShading fine,
            ∀ lambda : ENNReal,
              Y.IsLambdaDense lambda →
              ∀ R :
                  Kakeya.Streamlined.FactoringRefinement
                    data.toEnvelopeFactoring Y,
                ∀ q : ENNReal,
                  R.fineRefinement.RetainsMass q →
                    q * lambda * fine.enncard ≤
                      R.coarseSubfamily.family.enncard

/--
Transfer source indexed parameter non-concentration to the all-scale
Tube-Wolff bound for one retained selected-envelope block family.

At container scales at most `1 / 100000`, radius-five common-container
geometry places every contained lifted tube in a parameter box of width at
most one.  Supporting-line provenance pulls that box back to selected source
representatives, and the four target slots over each representative cancel
against the factor four in the lifted family cardinality.  Larger scales use
the trivial total-cardinality bound with the explicit constant `10^10`.
The retained-cardinality fraction is an explicit cancellation-free input,
normally supplied by
`SelectedScaleFactoringCardinalityRetentionStatement`.
-/
def SelectedScaleLiftedTubeWolffTransferStatement : Prop :=
  CommonContainerTargetTubeParameterClusterBaseFiveStatement →
    ∀ {delta rho : ℝ},
      0 < delta → delta ≤ rho → 0 < rho →
      ∀ fine : Kakeya.Streamlined.TubeFamily delta,
        HasBoundedBase fine 4 →
        IsInVerticalChart fine →
        ∀ C : ENNReal, C ≠ ⊤ →
          TubeParameterFrostmanBound fine C →
          ∀ data : SelectedScaleFourBlockData fine rho,
            ∀ S : Kakeya.Streamlined.Subfamily data.envelopeFamily,
              ∀ cardinalityFraction : ENNReal,
                cardinalityFraction ≠ 0 →
                cardinalityFraction ≠ ⊤ →
                cardinalityFraction * fine.enncard ≤
                  S.family.enncard →
                  TubeWolffBound
                    (data.selectedEnvelopeBlockFamily S)
                    (10000000000 +
                      C * Kakeya.realRpowENN 100000 2 *
                        cardinalityFraction⁻¹)

/--
Transfer source indexed parameter non-concentration to one retained lifted
four-block family.

Every lifted tube has the same four supporting-line parameters as its
selected source representative.  Hence a target parameter box pulls back to
the identical source box.  The four target slots over each representative
cancel against the exact factor four in the lifted family cardinality, while
the retained-cardinality fraction converts source normalization to retained
normalization.
-/
def SelectedScaleLiftedParameterFrostmanTransferStatement : Prop :=
  ∀ {delta rho : ℝ},
    delta ≤ rho →
    ∀ fine : Kakeya.Streamlined.TubeFamily delta,
      IsInVerticalChart fine →
      ∀ C : ENNReal, C ≠ ⊤ →
        TubeParameterFrostmanBound fine C →
        ∀ data : SelectedScaleFourBlockData fine rho,
          ∀ S : Kakeya.Streamlined.Subfamily data.envelopeFamily,
            ∀ cardinalityFraction : ENNReal,
              cardinalityFraction ≠ 0 →
              cardinalityFraction ≠ ⊤ →
              cardinalityFraction * fine.enncard ≤
                S.family.enncard →
                TubeParameterFrostmanBound
                  (data.selectedEnvelopeBlockFamily S)
                  (C * cardinalityFraction⁻¹)

/--
Convert weighted shaded-mass retention into cardinality retention for the
same selected tube subfamily.

The input shading is `lambda`-dense in the ambient family and loses at most
the finite nonzero factor `L` after selecting tube indices.  Since all tubes
at one radius have the same positive finite volume and every shaded piece is
contained in its tube, cancellation yields the explicit indexed-cardinality
fraction below.  No family or shading mass is divided directly.
-/
def SelectedTubeCardinalityRetentionFromMassStatement : Prop :=
  TubeVolumeScalingStatement →
    ∀ {rho : ℝ},
      0 < rho → rho ≤ 1 →
      ∀ F : Kakeya.Streamlined.TubeFamily rho,
        ∀ Y : Kakeya.Streamlined.TubeShading F,
          ∀ selected : Finset (Fin F.card),
            ∀ lambda L : ENNReal,
              Y.IsLambdaDense lambda →
              Y.mass ≤
                L * (selectedTubeShading Y selected).mass →
              L ≠ 0 → L ≠ ⊤ →
                (L⁻¹ * lambda) * F.enncard ≤
                  (selectedTubeFamily F selected).enncard

/--
Hereditary Tube-Wolff and indexed parameter-Frostman bounds for a selected
tube subfamily with an explicit cardinality fraction.

Contained indices and parameter-cluster indices inject into the corresponding
ambient index sets.  The sole normalization loss is the inverse of the
retained indexed-cardinality fraction.
-/
def SelectedTubeNonconcentrationTransferStatement : Prop :=
  ∀ {rho : ℝ},
    ∀ F : Kakeya.Streamlined.TubeFamily rho,
      ∀ selected : Finset (Fin F.card),
        ∀ cardinalityFraction : ENNReal,
          cardinalityFraction ≠ 0 →
          cardinalityFraction ≠ ⊤ →
          cardinalityFraction * F.enncard ≤
            (selectedTubeFamily F selected).enncard →
          ∀ tubeConstant parameterConstant : ENNReal,
            TubeWolffBound F tubeConstant →
            TubeParameterFrostmanBound F parameterConstant →
              TubeWolffBound
                  (selectedTubeFamily F selected)
                  (tubeConstant * cardinalityFraction⁻¹) ∧
                TubeParameterFrostmanBound
                  (selectedTubeFamily F selected)
                  (parameterConstant * cardinalityFraction⁻¹)

/--
Tube-Wolff and indexed parameter-Frostman control for the full selected-scale
four-block family.

Essential distinctness makes the representative parent map bijective, so the
four target slots give exactly four coarse indices per fine index.  The
existing retained-envelope transfer statements may therefore be applied to
the full envelope family with cardinality fraction one.  This statement keeps
that bookkeeping independent of the later weighted conflict cleanup.
-/
def SelectedScaleFullBlockNonconcentrationStatement : Prop :=
  SelectedScaleLiftedTubeWolffTransferStatement →
    SelectedScaleLiftedParameterFrostmanTransferStatement →
      ∀ {delta rho : ℝ},
        0 < delta → delta ≤ rho → 0 < rho →
          ∀ fine : Kakeya.Streamlined.TubeFamily delta,
            fine.IsEssentiallyDistinct →
            HasBoundedBase fine 4 →
            IsInVerticalChart fine →
            ∀ C : ENNReal, C ≠ ⊤ →
              TubeParameterFrostmanBound fine C →
                ∀ data : SelectedScaleFourBlockData fine rho,
                  TubeWolffBound data.coarse
                      (10000000000 +
                        C * Kakeya.realRpowENN 100000 2) ∧
                    TubeParameterFrostmanBound data.coarse C

/--
Produce one iterable selected-scale state without the generic convex-body
factoring theorem.

The full four-block relation shading first receives the linear
`lambda / 400` tube-specific Fubini density.  A bounded-degree weighted
coloring then selects an essentially-distinct tube subfamily.  The same mass
loss determines the retained indexed-cardinality fraction, so Tube-Wolff and
parameter-Frostman control transfer to exactly that selected family.  Finally
the top-boundary cap is absorbed on the same family.

All scale-dependent losses are exposed below.  In particular, the explicit
budget `ofReal (200 * rho) * L ≤ lambda₀` is the small-scale condition needed
to preserve positive windowed density; no generic factoring, ambient packing,
or hidden uniform structure is assumed.
-/
def SelectedScaleRelationCleanupStatement : Prop :=
  WeightedEssentiallyDistinctSelectionStatement →
    SelectedScaleRelationTubeDensityStatement →
      SelectedScaleFourBlockConflictDegreeStatement →
        SelectedScaleFullBlockNonconcentrationStatement →
          SelectedTubeCardinalityRetentionFromMassStatement →
            SelectedTubeNonconcentrationTransferStatement →
              SelectedLiftedWindowDensityAbsorptionStatement →
                TwistedProjectionRelationInducedShadingFromParametersStatement →
                  PlanarThickeningFortyVolumeStatement →
                ∀ {delta rho : ℝ},
                  0 < delta → delta ≤ 1 →
                  delta ≤ rho → 0 < rho → rho ≤ 1 / 1000 →
                  ∀ fine : Kakeya.Streamlined.TubeFamily delta,
                    fine.Nonempty →
                    fine.IsEssentiallyDistinct →
                    HasBoundedBase fine 4 →
                    IsInVerticalChart fine →
                    ∀ C : ENNReal, 1 ≤ C → C ≠ ⊤ →
                      TubeParameterFrostmanBound fine C →
                      delta ≤ 100000 * rho →
                      100000 * rho ≤ 1 →
                      ∀ data : SelectedScaleFourBlockData fine rho,
                        ∀ Y : Kakeya.Streamlined.TubeShading fine,
                          Y.union ⊆ horizontalSlab 0 1 →
                          ∀ lambda : ENNReal,
                            lambda ≠ 0 → lambda ≠ ⊤ →
                            Y.IsLambdaDense lambda →
                              let lambda₀ :=
                                ENNReal.ofReal (1 / 400 : ℝ) * lambda
                              let conflict :=
                                4 *
                                  (C *
                                    Kakeya.realRpowENN (100000 * rho) 2 *
                                      fine.enncard)
                              let L := conflict + 1
                              let cardinalityFraction := L⁻¹ * lambda₀
                              ENNReal.ofReal (200 * rho) * L ≤ lambda₀ →
                                ∃ selected :
                                    Finset (Fin data.coarse.card),
                                  let nextFamily :=
                                    selectedTubeFamily data.coarse selected
                                  let rawShading :=
                                    selectedTubeShading
                                      (data.exactTubeRelationInducedShading
                                        Y rho)
                                      selected
                                  let nextShading :=
                                    slabRestriction rawShading (-1) 1
                                  nextFamily.Nonempty ∧
                                    nextFamily.IsEssentiallyDistinct ∧
                                    IsInVerticalChart nextFamily ∧
                                    (∀ q : Fin nextFamily.card,
                                      |(tubeParamsOfTube
                                        (nextFamily.tube q)).a| ≤ 12 ∧
                                      |(tubeParamsOfTube
                                        (nextFamily.tube q)).b| ≤ 12 ∧
                                      |(tubeParamsOfTube
                                        (nextFamily.tube q)).c| ≤ 2 ∧
                                      |(tubeParamsOfTube
                                        (nextFamily.tube q)).d| ≤ 2) ∧
                                    nextShading.IsLambdaDense
                                      ((2 * L)⁻¹ * lambda₀) ∧
                                    IsInSlopeWindow nextShading ∧
                                    TubeWolffBound nextFamily
                                      ((10000000000 +
                                          C *
                                            Kakeya.realRpowENN 100000 2) *
                                        cardinalityFraction⁻¹) ∧
                                    TubeParameterFrostmanBound nextFamily
                                      (C * cardinalityFraction⁻¹) ∧
                                    nextShading.union ⊆
                                      Metric.cthickening rho Y.union ∧
                                    ∀ f : SlopeFunction,
                                      f.IsNonsingular → f 0 = 0 →
                                        twistedUnion nextShading f ⊆
                                            Metric.cthickening (40 * rho)
                                              (twistedUnion Y f) ∧
                                          MeasureTheory.volume
                                              (twistedUnion nextShading f) ≤
                                            (6889 : ENNReal) *
                                              MeasureTheory.volume
                                                (Metric.cthickening rho
                                                  (twistedUnion Y f))

/--
Canonical selected-scale adapter through the generic GWZ factoring theorem.

The GWZ theorem performs the simultaneous fine/envelope refinement from
aggregate shading mass and fiber Frostman control.  Its retained envelope
subfamily is then lifted to all four corresponding tube members.  The output
keeps the complete factoring refinement for downstream multiplicity use and
also exposes the cancellation-free tube density inequality, vertical chart,
and inherited line-parameter certificate needed by the next one-scale call.
-/
def SelectedScaleFactoringMultiplicityAdapterStatement : Prop :=
  Kakeya.Streamlined.FactoringMultiplicityStatement →
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ A : ℝ, 1 ≤ A ∧
        ∀ {delta rho : ℝ},
          0 < delta → 0 < rho →
          ∀ fine : Kakeya.Streamlined.TubeFamily delta,
            HasBoundedBase fine 4 →
            IsInVerticalChart fine →
            fine.toBodyFamily.IsMeasurable →
            fine.toBodyFamily.IsConvex →
            0 < fine.toBodyFamily.mass →
            fine.toBodyFamily.HasComparableDimensions
              delta delta 1 3 →
            ∀ data : SelectedScaleFourBlockData fine rho,
              ∀ C : ENNReal, 1 ≤ C → C ≠ ⊤ →
                data.toEnvelopeFactoring.FibersAreCFrostman C →
                ∀ Y : Kakeya.Streamlined.TubeShading fine,
                  0 < Y.mass →
                    ∃ R :
                        Kakeya.Streamlined.FactoringRefinement
                          data.toEnvelopeFactoring Y,
                      ∃ mcoarse Mcoarse mfiber Mfiber : ℕ,
                        let liftedFamily :=
                          data.selectedEnvelopeBlockFamily
                            R.coarseSubfamily
                        let liftedShading :=
                          data.selectedEnvelopeBlockShading
                            R.coarseSubfamily R.coarseShading
                        R.fineRefinement.RetainsMass
                          (Kakeya.realRpowENN delta epsilon *
                            ENNReal.rpow
                              (fine.toBodyFamily.enncard + 1)
                              (-epsilon) *
                            (ENNReal.ofReal A)⁻¹) ∧
                        R.factoring.IsInducedSubshading
                          R.fineRefinement.shading
                          R.coarseShading rho ∧
                        ENNReal.rpow
                            (Y.mass / fine.toBodyFamily.mass) 2 *
                            liftedFamily.toBodyFamily.mass ≤
                          (4 *
                              (ENNReal.ofReal A *
                                Kakeya.realRpowENN delta (-epsilon) *
                                ENNReal.rpow
                                  (fine.toBodyFamily.enncard + 1)
                                  epsilon *
                                C)) *
                            liftedShading.mass ∧
                        1 ≤ mcoarse ∧
                        (Mcoarse : ENNReal) ≤
                          ENNReal.ofReal A *
                            Kakeya.realRpowENN delta (-epsilon) *
                            ENNReal.rpow
                              (fine.toBodyFamily.enncard + 1)
                              epsilon *
                            (mcoarse : ENNReal) ∧
                        R.coarseShading.HasConstantMultiplicity
                          mcoarse Mcoarse ∧
                        1 ≤ mfiber ∧
                        (Mfiber : ENNReal) ≤
                          ENNReal.ofReal A *
                            Kakeya.realRpowENN delta (-epsilon) *
                            ENNReal.rpow
                              (fine.toBodyFamily.enncard + 1)
                              epsilon *
                            (mfiber : ENNReal) ∧
                        (∀ j,
                          R.factoring.FiberHasConstantMultiplicity
                            R.fineRefinement.shading j
                            mfiber Mfiber) ∧
                        liftedShading.union =
                          R.coarseShading.union ∧
                        liftedShading.union ⊆
                          Metric.cthickening rho Y.union ∧
                        IsInVerticalChart liftedFamily ∧
                        (∀ q : Fin liftedFamily.card,
                          |(tubeParamsOfTube
                            (liftedFamily.tube q)).a| ≤ 12 ∧
                          |(tubeParamsOfTube
                            (liftedFamily.tube q)).b| ≤ 12 ∧
                          |(tubeParamsOfTube
                            (liftedFamily.tube q)).c| ≤ 2 ∧
                          |(tubeParamsOfTube
                            (liftedFamily.tube q)).d| ≤ 2)

end Kakeya.Assouad
