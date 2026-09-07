module

/-
  Simple diagonal-dominated incidence bound for A3.

  Key insight: for t > s, the off-diagonal incidence energy E is negligible
  compared to the diagonal term |P|·M because:
    E ≤ C_common · C_T · M · Δ^s · K_energy · C_P · |P|²
    E / (|P|·M) = C_common · C_T · Δ^s · K_energy · C_P · |P|
                 ≈ Δ^{s-t-O(ε)} → 0

  Cauchy-Schwarz then gives:
    |U| ≥ |P|·M / 6

  Combined with counter-assumption |U| ≤ C_pack·Δ^{-2s-2ε}:
    M ≤ 6·C_pack·Δ^{-2s-2ε} / |P|

  With |P| ≥ Δ^{-t+ε}:
    M ≤ const·Δ^{-2s+t-3ε} < Δ^{-s-25ε} (for small Δ, since t-s+22ε > 0)

  Whiteprint node: a3_simple_incidence
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal


noncomputable section

attribute [local instance] Classical.propDecidable

namespace DirecretisedFurstenbergEstimate.AppendixA.SimpleIncidence

open DirecretisedFurstenbergEstimate

abbrev Tube := AffineLine

/-- Classical decidable equality for tubes. -/
noncomputable instance tubeDecidableEq : DecidableEq Tube := Classical.decEq Tube

end SimpleIncidence
