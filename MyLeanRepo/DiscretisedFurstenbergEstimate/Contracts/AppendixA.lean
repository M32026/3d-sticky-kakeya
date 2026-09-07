module

/-
  Contract A: Appendix A Main Theorem.

  Frozen facade signature. Produces the Appendix A alternative
  for the canonical AffineLine identity carrier.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.RegularIncidence.Definitions
public import MyLeanRepo.DiscretisedFurstenbergEstimate.FrontEndLemmas.FrontEndComposition
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

namespace DirecretisedFurstenbergEstimate

open RegularIncidence

theorem appendix_a_main (s t : ℝ) (hs : 0 < s) (hs1 : s < 1) (hst : s < t) (ht2 : t < 2) :
    ∃ εA : ℝ, εA < 1 ∧
      UniformAppendixAAlternative (fun ℓ : AffineLine => ℓ.1) s t εA := by
  have ht_pos : 0 < t := by linarith
  exact FrontEndLemmas.FrontEndComposition.front_end_composition s t hs hs1 ht_pos ht2 hst

end DirecretisedFurstenbergEstimate
