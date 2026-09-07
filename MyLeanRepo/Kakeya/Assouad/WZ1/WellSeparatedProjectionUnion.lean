import MyLeanRepo.Kakeya.Assouad.OSWInput
import MyLeanRepo.Kakeya.Assouad.Targets.WZ1Proposition8_9WideSequentialRescaling
import MyLeanRepo.Kakeya.Assouad.Targets.WZ1Proposition8_9NarrowStrip
import MyLeanRepo.Kakeya.Assouad.Targets.WZ1WideCoarseEndpointAxialDenominatorBudget
import MyLeanRepo.Kakeya.Assouad.Targets.WZ1WideCoarseEndpointAxialProjectiveRawBudget
import MyLeanRepo.Kakeya.Assouad.Targets.WZ1WideCoarseEndpointProjectiveFrostmanCount
import MyLeanRepo.Kakeya.Assouad.Targets.WZ1WideCoarseEndpointProjectiveFrostmanScalar
import MyLeanRepo.Kakeya.Assouad.Targets.WZ1WideCoarseEndpointSmallCoefficientFrostmanCount
import MyLeanRepo.Kakeya.Assouad.Targets.WZ1WideCoarseEndpointSmallCoefficientFrostmanScalar
import MyLeanRepo.Kakeya.Assouad.Targets.WZ1WideCoarseEndpointTransverseBudget
import MyLeanRepo.Kakeya.Assouad.Targets.WZ1WideFixedCellSelection
import MyLeanRepo.Kakeya.Assouad.WZ1.AnisotropicFrostmanRescaling
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma8_13FaithfulAssembly
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma8_13FaithfulClosingTarget
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma8_13FaithfulKaufmanInputTarget
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma8_13FaithfulViewpointAffineTarget
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma49OuterAssembly
import MyLeanRepo.Kakeya.Assouad.WZ1.LineNonconcentrationProjection
import MyLeanRepo.Kakeya.Assouad.WZ1.ProjectionDichotomyFromLeaves
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition8_9CommonStripFromPreparation
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition8_9ParameterSelection
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition8_9TwoEndsPreparation
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition8_9UnionSplitAssembly
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition8_9WideCoarseFromSplit
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition8_9WideSplitAssembly
import MyLeanRepo.Kakeya.Assouad.WZ1.WideCoarseEndpointAxialBudgetAssembly
import MyLeanRepo.Kakeya.Assouad.WZ1.WideCoarseEndpointFrostmanSplitAssembly
import MyLeanRepo.Kakeya.Assouad.WZ1.WideCoarseEndpointLineSplitAssembly
import MyLeanRepo.Kakeya.Assouad.WZ1.WideCoarseEndpointTransverseBudgetAssembly
import MyLeanRepo.Kakeya.Assouad.WZ1.WideCoarseLineFromEndpointSynthesis
import MyLeanRepo.Kakeya.Assouad.WZ1.WideFixedCellNormalization
import MyLeanRepo.Kakeya.Assouad.WZ1.WideNormalizedFromFixedCells
import MyLeanRepo.Kakeya.Assouad.WZ1.WideSnappedCoveringTransport

/-!
# Union-valued well-separated projection theorem

This is the paper-faithful Chapter 8 exit used by the same-endpoint
common-graph application.  It deliberately does not pass through the
historical arbitrary-three-class standard-separation removal.
-/

namespace Kakeya.Assouad

theorem wz1_well_separated_projection_union :
    WZ1WellSeparatedProjectionUnionConclusion := by
  have hKaufman : WZ1StripLocalizationKaufmanCaseStatement :=
    wz1_lemma8_13_faithful_assembly
      wz1_lemma8_13_faithful_viewpoint_affine
      wz1_lemma8_13_faithful_kaufman_input
      wz1_lemma8_13_faithful_closing
  have hStrip : WZ1StripLocalizationDichotomyStatement :=
    wz1_strip_localization_dichotomy_from_kaufman hKaufman
  have hTransverse : WZ1WideCoarseEndpointTransverseStatement :=
    wz1_wide_coarse_endpoint_transverse_budget_assembly
      wz1_wide_coarse_endpoint_transverse_budget
  have hProjectiveFrostman :
      WZ1WideCoarseEndpointAxialProjectiveFrostmanBudgetStatement :=
    wz1_wide_coarse_endpoint_projective_frostman_of_split
      wz1_wide_coarse_endpoint_projective_frostman_count
      wz1_wide_coarse_endpoint_projective_frostman_scalar
  have hSmallCoefficient :
      WZ1WideCoarseEndpointAxialSmallCoefficientBudgetStatement :=
    wz1_wide_coarse_endpoint_small_coefficient_of_split
      wz1_wide_coarse_endpoint_small_coefficient_frostman_count
      wz1_wide_coarse_endpoint_small_coefficient_frostman_scalar
  have hAxial : WZ1WideCoarseEndpointAxialStatement :=
    wz1_wide_coarse_endpoint_axial_budget_assembly
      hProjectiveFrostman
      wz1_wide_coarse_endpoint_axial_projective_raw_budget
      hSmallCoefficient
      wz1_wide_coarse_endpoint_axial_denominator_budget
  have hEndpoint : WZ1WideCoarseEndpointLineSynthesisStatement :=
    wz1_wide_coarse_endpoint_line_split_assembly hTransverse hAxial
  have hWideCoarse : WZ1Proposition8_9WideCoarsePreparationStatement :=
    wz1_proposition8_9_wide_coarse_from_split
      wz1_proposition8_9_wide_sequential_rescaling
      (wz1_wide_coarse_line_from_endpoint_synthesis hEndpoint)
  have hWideFromCoarse :
      WZ1Proposition8_9WideNormalizedFromCoarseStatement :=
    wz1_proposition8_9_wide_normalized_from_fixed_cells
      wz1_wide_fixed_cell_selection
      wz1_wide_fixed_cell_normalization
      wz1_wide_snapped_covering_transport
  have hWidePreparation :
      WZ1Proposition8_9WideNormalizedPreparationStatement :=
    wz1_proposition8_9_wide_split_assembly
      hWideCoarse hWideFromCoarse
  have hWide : WZ1Proposition8_9WideStripStatement :=
    wz1_proposition8_9_wide_from_normalized hWidePreparation
  have hCommon : WZ1Proposition8_9CommonStripConclusion :=
    wz1_proposition8_9_common_strip_from_preparation
      wz1_tripartite_hypergraph_refinement
      wz1_proposition8_9_two_ends_preparation
  exact
    wz1_proposition8_9_union_split_assembly
      wz1_proposition8_9_parameter_selection
      hCommon
      wz1_proposition8_9_narrow_strip
      hWide
      wz1_tripartite_hypergraph_refinement
      wz1_anisotropic_frostman_rescaling
      wz1_line_nonconcentration_projection
      hStrip
      osw_input

end Kakeya.Assouad
