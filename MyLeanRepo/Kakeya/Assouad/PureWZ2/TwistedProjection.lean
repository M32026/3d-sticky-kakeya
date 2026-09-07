import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope
import MyLeanRepo.Kakeya.Assouad.ProjectionNormalization

/-!
# Pure WZ2 small twisted projection

This module freezes the geometric counterexample supplied to the already
proved parameter-Frostman twisted-projection estimate.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

/--
The paper-facing analogue of WZ Corollary 6.5.

The exponent is the paper-faithful WZ1 value `sigma - loss`.  WZ2 prints
`sigma + epsilon` while citing WZ1 Corollary 6.5, but the cited result and the
available formalized anisotropic-rescaling theorem both give the minus sign.
The plus-sign version is a false strengthening and is not needed for the
final contradiction.

Indexed parameter Frostman control, analytic distinctness, and the extremal
cardinality window belong to the specialized Section 7 preparation below,
not to this paper-facing lemma.
-/
structure PureWZ2SmallTwistedProjectionData
    (sigma loss delta : ℝ) where
  family : Kakeya.Streamlined.TubeFamily delta
  family_nonempty : family.Nonempty
  line_class : WZ1PaperIsLineClass family
  convex_wolff :
    WZ2PaperConvexWolffBound family
      (Kakeya.realRpowENN delta (-loss))
  shading : WZ1PaperTubeShading family
  dense :
    shading.IsLambdaDense
      (Kakeya.realRpowENN delta loss)
  slope : SlopeFunction
  slope_nonsingular : slope.IsNonsingular
  projection_upper :
    volume (twistedProjection slope '' shading.union) ≤
      Kakeya.realRpowENN delta (sigma - loss)

/--
The ordinary unit-segment configuration consumed by the corrected
Theorem-5.2-specific parameter-Frostman projection estimate.

This is selected independently of the paper-facing Corollary-6.5 output.
Its slope and geometric configuration are produced together by the
proof-local WZ-Lemma-8 normalization.
-/
structure PureWZ2ParameterFrostmanPreparationData
    (sigma loss delta : ℝ) where
  family : Kakeya.Streamlined.TubeFamily delta
  family_nonempty : family.Nonempty
  shading : Kakeya.Streamlined.TubeShading family
  dense :
    shading.IsLambdaDense
      (Kakeya.realRpowENN delta loss)
  bounded_base : HasBoundedBase family 4
  analytic_distinct : family.IsEssentiallyDistinct
  vertical_chart : IsInVerticalChart family
  tube_wolff :
    TubeWolffBound family
      (Kakeya.realRpowENN delta (-loss))
  parameter_frostman :
    TubeParameterFrostmanBound family
      (Kakeya.realRpowENN delta (-loss))
  cardinality_upper :
    HasExtremalCardinalityUpper family (loss / 10)
  slope_window : IsInSlopeWindow shading
  analysisSlope : SlopeFunction
  analysisSlope_zero : analysisSlope 0 = 0
  analysisSlope_nonsingular : analysisSlope.IsNonsingular
  projection_upper :
    volume (twistedUnion shading analysisSlope) ≤
      Kakeya.realRpowENN delta (sigma - loss)

/--
The paper-facing output of WZ Lemma 8 and the large-slope normalization for
one pure critical package.
-/
def PureWZ2SmallTwistedProjectionFromCriticalStatement : Prop :=
  ∀ sigma : ℝ,
    PureWZ2CriticalPackage sigma →
      ∀ outputLoss scaleCeiling : ℝ,
        0 < outputLoss →
        0 < scaleCeiling →
          ∃ delta : ℝ,
            0 < delta ∧
            delta ≤ scaleCeiling ∧
            delta < 1 ∧
            Nonempty
              (PureWZ2SmallTwistedProjectionData
                sigma outputLoss delta)

/--
Specialized preparation of a paper small-projection output for the corrected
parameter-Frostman Proposition 6.8/7.1 route.
-/
def PureWZ2ParameterFrostmanPreparationStatement : Prop :=
  ∀ sigma : ℝ,
    PureWZ2CriticalPackage sigma →
      ∀ analyticLoss scaleCeiling : ℝ,
        0 < analyticLoss →
        analyticLoss < sigma →
        0 < scaleCeiling →
          ∃ delta : ℝ,
            0 < delta ∧
            delta ≤ scaleCeiling ∧
            delta < 1 ∧
            Nonempty
              (PureWZ2ParameterFrostmanPreparationData
                sigma analyticLoss delta)

/-- Node 7 in the serial heavy-task chain. -/
def PureWZ2SmallTwistedProjectionStatement : Prop :=
  PureWZ2SubunitPackageStatement →
    PureWZ2CriticalExtractionStatement →
      PureWZ2PropStickyStatement →
        PureWZ2GrainsStatement →
          PureWZ2C2GrainsStatement →
            PureWZ2LargeSlopeStatement →
              PureWZ2SmallTwistedProjectionFromCriticalStatement ∧
                PureWZ2ParameterFrostmanPreparationStatement

end Kakeya.Assouad

end
