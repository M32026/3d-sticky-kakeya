module

/-
  GOutput: output package for the G lemma (A1 + source family + provenance).

  G constructs A1, the fixed source tube family T_source, the global coarse
  parent T_Delta, Section 9 / 17Δ provenance, the dyadic cardinality bound,
  and all numerical hypotheses needed by H (A2→A4 assembly).

  Whiteprint node: front_end_lemmas / G_output
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CoveringUtils
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FrontEndLemmas.ScaleNormalization
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FrontEndLemmas.DeltasSetTreeExtraction
public import MyLeanRepo.DiscretisedFurstenbergEstimate.RegularIncidence.Definitions
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.FrontEndExtraction.ParameterSelection
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.UniformAppendixAAlternative
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.FrontEndExtraction.B1InductionApplication
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Section9.SourceToNiceConfigurationFront
public import MyLeanRepo.DiscretisedFurstenbergEstimate.SnappingSSetTransfer
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FrontEndLemmas.EndpointAdapter
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FrontEndLemmas.TFullUpperBound
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FrontEndLemmas.B1Assembly
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FrontEndLemmas.B1FrontUpperBounds
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.NiceConfigToA1
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.TwoSBoundHelper
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.TDeltaGlobalConstruction
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FrontEndLemmas.CGlobalCardBound
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A2_FromA1
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A2_PerSquare
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A1_to_LinkedA2
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A1_to_A4_v2_Assembly
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A2_to_A3_Bridge
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FrontEndLemmas.Provenance17Delta
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FrontEndLemmas.TSubSource
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FrontEndLemmas.HDyadicBound
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AssemblyNumericalHypotheses
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.B1ToA1Skeleton
public import MyLeanRepo.DiscretisedFurstenbergEstimate.InductionConfigurations
public import MyLeanRepo.OSWPrelude

@[expose] public section


open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DirecretisedFurstenbergEstimate.FrontEndLemmas.FrontEndComposition

open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.RegularIncidence
open DirecretisedFurstenbergEstimate.FrontEndLemmas
open DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral
open DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.FrontEndExtraction
open DirecretisedFurstenbergEstimate.Section9
open DiscretisedFurstenbergEstimate.CombiningTheorem
open DirecretisedFurstenbergEstimate.FrontEndLemmas.B1Assembly
open DirecretisedFurstenbergEstimate.FrontEndLemmas.B1FrontUpperBounds
open DiscretisedFurstenbergEstimate.InductionConfigurations
open HeavyParentFiltering
open B1HardFields
open SquareGeometry
open DirecretisedFurstenbergEstimate.AppendixA
open DirecretisedFurstenbergEstimate.AppendixA.A2DyadicAdapter
open DirecretisedFurstenbergEstimate.AssemblyNumerical

/--
  Output of the G lemma: A1, fixed source family, global coarse parent,
  provenance, dyadic bound, and all numerical hypotheses consumed by H.

  ## Fields

  ### Core constructed data
  - `a1`: A1 output from NiceConfigToA1
  - `T_source_dyadic`: per-square union of config' tube families
  - `T_source`: affine image of T_source_dyadic
  - `T_Delta`: global coarse parent family

  ### Equalities and inclusions
  - `hT_source_eq`: definitional equality T_source = image
  - `hT_sub_source`: a1.tubes p ⊆ T_source (fibre inclusion)
  - `hK_pack_eq`: a1.K_pack = K_pack

  ### Geometric bounds
  - `hT_Delta_provenance`: 17Δ thickening around swapLine '' T_oriented
  - `h_dyadic`: |T_Delta_global_dyadic| ≤ Δ^{-(2s+3ε)}
  - `h_slope_T_source`, `h_intercept_T_source`: slope/intercept ≤ 1 / ≤ 3

  ### Numerical hypotheses for H
  - `h_small_A2`: A2 smallness conditions
  - `h_num_u`: AssemblyNumericalBounds at exponent u
  - `h_small_eps`: Δ^{ε/4} ≤ 1/100
  - `h_absorb_energy`: energy constant absorption
  - `hKpack_le_ε`: K_pack absorption
  - `hRKP_at_Delta`: RKP theorem specialized to Δ
  - `h_center_bdd`, `hQset_nonempty`: center bounds

  ### Scale and parameter hypotheses
  - `hΔ_pos`, `hΔ_lt_half`, `hδ_n_pos`, `hδ_le_D`, `hδ_n_eq`
  - `hε_pos`, `hε_lt_one`, `hs_pos`, `hs_lt_one`, `hsu`, `hu_pos`, `h_run_lt_two`
  - `hA_one`, `hQTTC`, `A`, `K_pack`
-/
structure GOutput (n m : ℕ) (hnm : m ≤ n) (Δ δ_n s u ε : ℝ)
    (T_oriented : Set AffineLine) where
  -- Core constructed data
  a1 : A1_Output Δ δ_n u s ε
  T_source_dyadic : Finset (DiscretisedFurstenbergEstimate.DyadicTube n)
  T_source : Finset AppendixA.FineTube
  T_Delta : Finset AppendixA.CoarseTube
  K_pack : ℝ
  A : ℝ

  -- Equalities
  hT_source_eq : T_source = T_source_dyadic.image (AppendixA.A2DyadicAdapter.dyadicTubeToA2 (m := n))
  hK_pack_eq : a1.K_pack = K_pack
  hδ_n_eq : δ_n = Δ ^ 2
  hΔ_eq : Δ = DiscretisedFurstenbergEstimate.dyadicDelta m
  hδ_eq : δ_n = DiscretisedFurstenbergEstimate.dyadicDelta n
  hm_pos : 1 ≤ m
  hT_Delta_eq : T_Delta = AppendixA.TDeltaGlobal.T_Delta_global hnm T_source

  -- Fiber inclusion
  hT_sub_source : ∀ (p : EuclideanPlane), a1.tubes p ⊆ T_source

  -- Provenance and cardinality
  hT_Delta_provenance : (T_Delta : Set AppendixA.CoarseTube) ⊆
      Metric.cthickening (17 * Δ) (CoordinatePartition.swapLine '' T_oriented)
  h_dyadic : (AppendixA.TDeltaGlobal.T_Delta_global_dyadic hnm T_source).card ≤
      Real.rpow Δ (-(2 * s + 3 * ε))

  -- Slope / intercept bounds on T_source
  h_slope_T_source : ∀ ℓ ∈ T_source, |tubeSlope ℓ| ≤ 1
  h_intercept_T_source : ∀ ℓ ∈ T_source, |tubeIntercept ℓ| ≤ 3

  -- Slope / intercept bounds on dyadic T_Delta (for H slope bound)
  h_slope_T_Delta_dyadic : ∀ U ∈ AppendixA.TDeltaGlobal.T_Delta_global_dyadic hnm T_source, |U.slope| ≤ 1
  h_intercept_T_Delta_dyadic : ∀ U ∈ AppendixA.TDeltaGlobal.T_Delta_global_dyadic hnm T_source, |U.intercept| ≤ 3

  -- Numerical hypotheses for H
  h_small_A2 : AppendixA.A2.A2_Smallness Δ δ_n s u ε A K_pack (a1.M : ℝ)
  h_num_u : AssemblyNumericalBounds Δ s u ε
  h_small_eps : Real.rpow Δ (ε / 4) ≤ 1 / 100
  h_absorb_energy :
      (MainAppendix.plane_energy_constant s u 2) *
      (MainAppendix.plane_packing_constant : ℝ) ≤ Real.rpow Δ (-ε)
  hKpack_le_ε : K_pack ≤ Real.rpow Δ (-ε)
  hRKP_cond_u : 576 * ε < u - s
  δ₀_RKP : ℝ
  hRKP_u : RKPAtExponent s u ε δ₀_RKP
  hΔ_le_RKP : Δ ≤ δ₀_RKP

  -- Center bounds
  h_center_bdd : ∀ Q ∈ a1.Qset, ‖Lagoon.squareCenter Δ Q‖ ≤ 2
  hQset_nonempty : a1.Qset.Nonempty

  -- Scale and parameter hypotheses
  hΔ_pos : 0 < Δ
  hΔ_lt_half : Δ < 1 / 2
  hδ_n_pos : 0 < δ_n
  hδ_le_D : δ_n ≤ Δ
  hε_pos : 0 < ε
  hε_lt_one : ε < 1
  hs_pos : 0 < s
  hs_lt_one : s < 1
  hsu : s < u
  hu_pos : 0 < u
  h_run_lt_two : u < 2
  hA_one : 1 ≤ A
  hQTTC : ParameterSelectionQTTC s A

  -- δ_n ≤ Δ/4 (for canonical A2 parent construction)
  hδ_le_quarter : δ_n ≤ Δ / 4

end DirecretisedFurstenbergEstimate.FrontEndLemmas.FrontEndComposition
