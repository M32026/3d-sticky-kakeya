module

/-
  Contract B1: Theorem 6.1 Main.

  Frozen facade signature. Produces a uniform regular incidence estimate
  for the canonical AffineLine identity carrier, with εReg = η = ε_inc.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Contracts.AppendixA
public import MyLeanRepo.DiscretisedFurstenbergEstimate.RegularIncidence.Definitions
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheoremRework.Theorem61MainAssembly
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

namespace DirecretisedFurstenbergEstimate

open RegularIncidence

theorem theorem6_1_main (s t : ℝ) (hs : 0 < s) (hs1 : s < 1) (hst : s < t) (ht2 : t < 2) :
    ∃ ε_inc : ℝ, ε_inc < 1 ∧
      UniformRegularIncidenceEstimate (fun ℓ : AffineLine => ℓ.1) s t ε_inc ε_inc := by
  exact theorem6_1_main_assembly s t hs hs1 hst ht2

end DirecretisedFurstenbergEstimate

end
