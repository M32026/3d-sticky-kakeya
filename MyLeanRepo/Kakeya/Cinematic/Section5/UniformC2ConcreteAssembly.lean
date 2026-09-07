import MyLeanRepo.Kakeya.Cinematic.Section5.WZ2UniformC2ShortCurveLevelSetFromFaithfulInputs
import MyLeanRepo.Kakeya.Cinematic.Targets.FineShadingComparison
import MyLeanRepo.Kakeya.Cinematic.Targets.MaximalFineRectangleSelection
import MyLeanRepo.Kakeya.Cinematic.Section5.FineCarrierMeasurableAssignment
import MyLeanRepo.Kakeya.Cinematic.Section5.DyadicPieceVolumeRefinement
import MyLeanRepo.Kakeya.Cinematic.Section5.PolynomialDyadicPieceRange
import MyLeanRepo.Kakeya.Cinematic.Section5.NonThinFineRectangleCount
import MyLeanRepo.Kakeya.Cinematic.Section5.CoarseFiberCarrierContainment
import MyLeanRepo.Kakeya.Cinematic.Targets.CommonTangentRectangle
import MyLeanRepo.Kakeya.Cinematic.Targets.FineToCoarseContainment
import MyLeanRepo.Kakeya.Cinematic.Targets.FineToCoarseCentral
import MyLeanRepo.Kakeya.Cinematic.Targets.FineTangencyLiftToCoarse
import MyLeanRepo.Kakeya.Cinematic.Targets.CoarseRectangleGrouping
import MyLeanRepo.Kakeya.Cinematic.Targets.ComparableCoarseTangency
import MyLeanRepo.Kakeya.Cinematic.Targets.FiniteAmbientBallCover
import MyLeanRepo.Kakeya.Cinematic.Section5.Lemma45BadSetBounds
import MyLeanRepo.Kakeya.Cinematic.Section5.PointwiseGoodPairSelection
import MyLeanRepo.Kakeya.Cinematic.Targets.CoarseFiberNonconcentration
import MyLeanRepo.Kakeya.Cinematic.Section5.FinePairIncidenceBound
import MyLeanRepo.Kakeya.Cinematic.Targets.CoarseMultiplicityInterpolation
import MyLeanRepo.Kakeya.Cinematic.Section5.ProductScaleFixedPairIncidence
import MyLeanRepo.Kakeya.Cinematic.Section5.FiniteTangentBallCover
import MyLeanRepo.Kakeya.Cinematic.Section5.FiberwiseSeparatedTangentBallPairAt
import MyLeanRepo.Kakeya.Cinematic.Section5.SharedTangentBallPairPigeonholeAt
import MyLeanRepo.Kakeya.Cinematic.Section5.NormalCoarseRectangleCount
import MyLeanRepo.Kakeya.Cinematic.Section5.ScaleFreeNormalCoarseRectangleCount
import MyLeanRepo.Kakeya.Cinematic.TangencyGeometryCompletion
import MyLeanRepo.Kakeya.Cinematic.Targets.ComparableRectangles
import MyLeanRepo.Kakeya.Cinematic.Targets.RectanglePacking
import MyLeanRepo.Kakeya.Cinematic.Targets.ComparabilityTransitivity
import MyLeanRepo.Kakeya.Cinematic.Targets.PolynomialScaleCoarseRectangleCount
import MyLeanRepo.Kakeya.Cinematic.Targets.RectangleSubfamily
import MyLeanRepo.Kakeya.Cinematic.Targets.RectangleRefinement
import MyLeanRepo.Kakeya.Cinematic.Targets.PolynomialRectangleRefinement
import MyLeanRepo.Kakeya.Cinematic.Targets.BipartiteTangencyRobustFull
import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.RobustUnitCoreFromGraphLenses
import MyLeanRepo.Kakeya.Cinematic.Targets.BipartiteTangencyRobustCoreFromLenses
import MyLeanRepo.Kakeya.Cinematic.Targets.TwoEndsSelection
import MyLeanRepo.Kakeya.Cinematic.Targets.TangencyTwoEndsSelection
import MyLeanRepo.Kakeya.Cinematic.Targets.FineRectangleAssignment
import MyLeanRepo.Kakeya.Cinematic.Section5.Counting
import MyLeanRepo.Kakeya.Cinematic.Section5.UniformC2PaperAssembly
import MyLeanRepo.Kakeya.Cinematic.Targets.CenteredSixteenthIntervalCover
import MyLeanRepo.Kakeya.Cinematic.Targets.HorizontalGraphNeighborhoodVolume
import MyLeanRepo.Kakeya.Cinematic.Targets.HorizontalStubMultiplicityVolume
import MyLeanRepo.Kakeya.Cinematic.Targets.HorizontalStubLevelSetAbsorption
import MyLeanRepo.Kakeya.Cinematic.Targets.CenteredTaylorQuadraticCinematicTransport
import MyLeanRepo.Kakeya.Cinematic.Section5.CenteredTaylorUniformFiniteGraphTransport
import MyLeanRepo.Kakeya.Cinematic.Targets.MultiplicityLevelSelection
import MyLeanRepo.Kakeya.Cinematic.Section5.Foundations
import MyLeanRepo.Kakeya.Cinematic.Targets.MarcusTardosEqualLength
import MyLeanRepo.Kakeya.Cinematic.Targets.MarcusTardosTotalLength
import MyLeanRepo.Kakeya.Cinematic.Targets.MarcusTardosGraphLenses
import MyLeanRepo.Kakeya.Cinematic.PreliminaryDichotomy
import MyLeanRepo.Kakeya.Cinematic.Targets.TwoZeros
import MyLeanRepo.Kakeya.Cinematic.Targets.IntervalScaling
import MyLeanRepo.Kakeya.Cinematic.Targets.CommonTangentRectangleRobust
import MyLeanRepo.Kakeya.Cinematic.Perturbation.FiniteAvoidance

/-!
# Concrete uniform-C2 PYZ assembly

Assemble the closed Section 5 leaves into the uniform short-curve estimate,
then apply the closed Taylor-globalization and analytic tail to obtain the
WZ2-facing export without additional hypotheses.
-/

namespace Kakeya.Cinematic

theorem wz2_uniformC2_short_curve_level_set :
    WZ2UniformC2ShortCurveLevelSetInput := by
  have hCommon : CommonTangentRectangleStatement :=
    common_tangent_rectangle_controls_parameter
  have hComparable : ComparableRectanglesStatement :=
    comparable_rectangles_have_close_graphs hCommon
  have hPacking : RectanglePackingStatement :=
    incomparable_rectangles_packing_bound
  have hTransitivity : ComparabilityTransitivityStatement :=
    comparability_transitivity hComparable
  have hFineToCoarse : FineToCoarseContainmentStatement :=
    fine_to_coarse_containment
  have hFineToCoarseCentral : FineToCoarseCentralStatement :=
    fine_to_coarse_central hFineToCoarse
  have hTangency : TangencyGeometryCompletionStatement :=
    tangency_geometry_completion
  have hRefinement : RectangleRefinementStatement :=
    rectangle_refinement interval_scaling_api hComparable hPacking
      rectangle_subfamily_selection
  have hEqual : MarcusTardos.EqualLengthSequenceBoundStatement :=
    MarcusTardos.equal_length_sequence_bound
  have hTotal : MarcusTardos.TotalLengthSequenceBoundStatement :=
    MarcusTardos.total_length_from_equal_length hEqual
  have hGraphLenses : GraphLensBoundStatement :=
    graph_lens_bound_from_sequences hTotal
  have hPreliminary : PreliminaryDichotomyStatement :=
    preliminary_dichotomy
  have hTwoZeros : TwoZerosStatement :=
    cinematic_difference_has_at_most_two_zeros hPreliminary
  have hUnit : BipartiteTangencyRobustUnitCoreStatement :=
    bipartite_tangency_robust_unit_core_from_graph_lenses
      hGraphLenses hTwoZeros hTangency common_tangent_rectangle_robust
      hComparable hPacking finiteAvoidanceExactTangencies
  have hCore : BipartiteTangencyRobustCoreStatement :=
    bipartite_tangency_robust_core_from_graph_lenses hUnit
  have hBipartite : BipartiteTangencyRobustFullStatement :=
    bipartite_tangency_robust_full hTangency hComparable hPacking hRefinement
      polynomial_rectangle_refinement common_tangent_rectangle_robust hCore
  have hFineAssignment : FineRectangleAssignmentStatement :=
    fine_rectangle_assignment hTangency
  exact
    wz2_uniformC2_short_curve_level_set_from_faithful_inputs
      fine_shading_comparison
      maximal_fine_rectangle_selection
      fine_carrier_measurable_assignment
      dyadic_piece_volume_refinement
      polynomial_dyadic_piece_range
      non_thin_fine_rectangle_count
      coarse_fiber_carrier_containment
      hCommon
      hFineToCoarse
      hFineToCoarseCentral
      fine_tangency_lifts_to_coarse
      coarse_rectangle_grouping
      comparable_coarse_tangency
      finite_ambient_ball_cover
      lemma45_bad_set_bounds
      pointwise_good_pair_selection
      coarse_fiber_nonconcentration
      fine_pair_incidence_bound
      coarse_multiplicity_interpolation
      product_scale_fixed_pair_incidence
      finite_tangent_ball_cover
      fiberwise_separated_tangent_ball_pair_at
      shared_tangent_ball_pair_pigeonhole_at
      normal_coarse_rectangle_count
      scale_free_normal_coarse_rectangle_count
      hTangency
      hComparable
      hPacking
      hTransitivity
      polynomial_scale_coarse_rectangle_count
      rectangle_subfamily_selection
      hRefinement
      polynomial_rectangle_refinement
      hBipartite
      two_ends_selection
      tangency_two_ends_selection
      hFineAssignment
      good_pair_counting
      pair_incidence_counting

theorem wz2_uniformC2_input : WZ2UniformC2Input :=
  wz2_uniformC2_input_from_taylor_globalization
    centered_sixteenth_interval_cover
    horizontal_graphNeighborhood_volume
    horizontal_stub_multiplicity_volume
    horizontal_stub_level_set_absorption
    centered_taylor_quadratic_cinematic_transport
    centered_taylor_uniform_finite_graph_transport
    wz2_uniformC2_short_curve_level_set
    multiplicity_level_selection
    restricted_weak_type_reduction

end Kakeya.Cinematic
