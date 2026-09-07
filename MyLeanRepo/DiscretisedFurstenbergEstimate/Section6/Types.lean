module

/-
  Shared Section 6 type definitions.

  Canonical definitions of all data structures used in the Section 6
  coarse-branch integration:
    - B1RetentionData     — per-square B1 retention
    - CoarseRatioData     — coarse two-case incidence ratio
    - FineCor25Data       — fine normalized Corollary 2.5 ratio
    - B1FactorData        — B1 multiplicative reassembly
    - CoarseCaseData      — complete package for ConditionalAssembly

  These types are the single source of truth. All Section 6 modules import
  them from here; no local redefinitions.

  Whiteprint node: section6_types
  Dependencies: improved_incidence_two_scale_assembly, CombiningTheorem
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DirecretisedFurstenbergEstimate.Section6

open DiscretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.CombiningTheorem

/-- δ-covering number abbreviation for Section 6. -/
abbrev Ncover {X : Type*} [PseudoMetricSpace X] (δ : ℝ) (E : Set X) : ENNReal :=
  Metric.externalCoveringNumber δ.toNNReal E

/-! ========================================================================
   Input 2: Coarse-scale incidence ratio (two-case result)

   From the coarse bound Ncover(Δ, T) ≥ δ^{-(s+ε)} and the B1 coarse
   configuration, a two-case argument on MΔ yields the normalized coarse
   tube count ratio.

   Case 1: MΔ large → uniform_prop5 (Cor 2.5) gives gain.
   Case 2: MΔ small → coarse Appendix bound gives gain directly.

   `coarseGain` is the excess exponent beyond the trivial δ^{-s/2}.
   ======================================================================== -/

/-- Coarse-scale incidence ratio from Corollary 2.5 + coarse bound.

    `coarseCount / coarseMultiplicity` is the normalized coarse tube count.
    `coarseGain` is the power gain extracted from the coarse bound.

    The bound `hcoarse` says: NΔ/MΔ ≳ δ^{-(s/2 + coarseGain)}. -/
structure CoarseRatioData (δ s : ℝ) where
  coarseCount : ℝ
  coarseMultiplicity : ℝ
  coarseGain : ℝ
  hMΔ_pos : 0 < coarseMultiplicity
  hgainΔ : 0 < coarseGain
  hcoarse : δ ^ (-(s / 2 + coarseGain)) ≤ coarseCount / coarseMultiplicity

/-! ========================================================================
   Input 3: Fine normalized Corollary 2.5 ratio

   Inside a selected heavy coarse square Q, apply Corollary 2.5 at the
   fine scale δ (rescaled to the local coordinate system of Q).

   `localLoss` accounts for polylogarithmic factors and the rescaling.
   ======================================================================== -/

/-- Fine-scale local incidence ratio from normalized Corollary 2.5.

    `localCount / localMultiplicity` is the normalized fine tube count
    inside one heavy coarse square.
    `localLoss` is the exponent lost to polylog factors and rescaling.

    The bound `hfine` says: NQ/MQ ≳ δ^{-(s/2 - localLoss)}. -/
structure FineCor25Data (δ s : ℝ) where
  localCount : ℝ
  localMultiplicity : ℝ
  localLoss : ℝ
  hMQ_pos : 0 < localMultiplicity
  hlossQ : 0 ≤ localLoss
  hfine : δ ^ (-(s / 2 - localLoss)) ≤ localCount / localMultiplicity

end DirecretisedFurstenbergEstimate.Section6

end
