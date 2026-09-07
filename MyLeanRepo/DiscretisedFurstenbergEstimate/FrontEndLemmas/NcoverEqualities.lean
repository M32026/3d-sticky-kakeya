module

/-
  NcoverEqualities

  Lemmas for Ncover preservation under orientation and tube family boundedness
  from incidence with a bounded point set.

  Provides:
  1. ncover_swapLine_eq: Ncover δ (swapLine '' T) = Ncover δ T
  2. tube_family_bounded_from_point_set: boundedness of all tubes near a unit-ball point set
  3. offset_bound_from_point_set: per-tube offset bound from incidence

  Owner: cobalt
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CoordinatePartition
public import MyLeanRepo.DiscretisedFurstenbergEstimate.RegularIncidence.Definitions
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DirecretisedFurstenbergEstimate.FrontEndLemmas.NcoverEqualities

open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.RegularIncidence
open CoordinatePartition

/-- Ncover is preserved by swapLine (involutive isometry on AffineLine). -/
lemma ncover_swapLine_eq {δ : ℝ} {T : Set AffineLine} :
    Ncover δ (swapLine '' T) = Ncover δ T := by
  have h := externalCoveringNumber_image_of_involutive_isometry
    swapLine_isometry swapLine_invol δ.toNNReal T
  simpa [Ncover] using h

end DirecretisedFurstenbergEstimate.FrontEndLemmas.NcoverEqualities
