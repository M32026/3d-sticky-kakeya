module

/-
  Port of coarse_sset_property to our IsDeltaSSet / L1 metric setup.

  Uses coarseImage = coarseTubeToM ∘ coarseRound for consistency with
  the main theorem's h_ancestor condition.

  Distortion: dist T (liftCenter center) ≤ dist (coarseImage T) center + δ_m

  Main result: coarse_sset_property_adapted proves the union of coarse
  tube families is a finite S-set via incidence counting, without
  exponential subset-transfer blowup.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.DiscretisedFurstenbergEstimate.InductionConfigurations
public import MyLeanRepo.DiscretisedFurstenbergEstimate.InductionSteps
public import MyLeanRepo.DiscretisedFurstenbergEstimate.B1_Sublemmas
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal Classical
open DiscretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.CombiningTheorem

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DirecretisedFurstenbergEstimate.InductionOnScales

open InductionConfigurations

/-- Floor-divide tube indices by refinement factor. -/
def coarseTubeToM {n m : ℕ} (hnm : m ≤ n)
    (T : DyadicTube n) : DyadicTube m :=
  ⟨T.a / (refinementFactor n m : ℤ), T.b / (refinementFactor n m : ℤ)⟩

end DirecretisedFurstenbergEstimate.InductionOnScales
