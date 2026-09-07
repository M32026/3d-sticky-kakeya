import MyLeanRepo.Kakeya.Cinematic.Section5.UniformC2ShortCurveInput
import MyLeanRepo.Kakeya.Cinematic.Section5.FaithfulAssemblyInputs

/-!
# Faithful uniform-C2 short-curve assembly boundary

This is the same paper-facing Section 5 dependency list as the existing
family-dependent short-curve assembly, but its output fixes the absolute
two-jet bound before the small-scale threshold and the concrete family.
-/

namespace Kakeya.Cinematic

def WZ2UniformC2ShortCurveLevelSetFromFaithfulInputsStatement : Prop :=
  FineShadingComparisonStatement →
    MaximalFineRectangleSelectionStatement →
    FineCarrierMeasurableAssignmentStatement →
    DyadicPieceVolumeRefinementStatement →
    PolynomialDyadicPieceRangeStatement →
    NonThinFineRectangleCountStatement →
    CoarseFiberCarrierContainmentStatement →
    CommonTangentRectangleStatement →
    FineToCoarseContainmentStatement →
    FineToCoarseCentralStatement →
    FineTangencyLiftToCoarseStatement →
    CoarseRectangleGroupingStatement →
    ComparableCoarseTangencyStatement →
    FiniteAmbientBallCoverStatement →
    Lemma45BadSetBoundsStatement →
    PointwiseGoodPairSelectionStatement →
    CoarseFiberNonconcentrationStatement →
    FinePairIncidenceBoundStatement →
    CoarseMultiplicityInterpolationStatement →
    ProductScaleFixedPairIncidenceStatement →
    FiniteTangentBallCoverStatement →
    FiberwiseSeparatedTangentBallPairAtStatement →
    SharedTangentBallPairPigeonholeAtStatement →
    NormalCoarseRectangleCountStatement →
    ScaleFreeNormalCoarseRectangleCountStatement →
    TangencyGeometryCompletionStatement →
    ComparableRectanglesStatement →
    RectanglePackingStatement →
    ComparabilityTransitivityStatement →
    PolynomialScaleCoarseRectangleCountStatement →
    RectangleSubfamilySelectionStatement →
    RectangleRefinementStatement →
    PolynomialRectangleRefinementStatement →
    BipartiteTangencyRobustFullStatement →
    TwoEndsSelectionStatement →
    TangencyTwoEndsSelectionStatement →
    FineRectangleAssignmentStatement →
    GoodPairCountingStatement →
    PairIncidenceCountingStatement →
    WZ2UniformC2ShortCurveLevelSetInput

end Kakeya.Cinematic
