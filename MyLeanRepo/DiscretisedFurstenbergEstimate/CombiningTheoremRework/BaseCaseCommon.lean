module

/-
  Shared definitions for Combining Theorem base case files.

  Currently only contains the CTNiceConfiguration abbrev, shared by
  BaseCaseBad, BaseCaseNormal, and BaseCaseGood.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.CombiningTheorem
public import MyLeanRepo.OSWPrelude

@[expose] public section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

abbrev CTNiceConfiguration (k : ℕ) (s C : ℝ) (M : ℕ) :=
  CombiningTheorem.NiceConfiguration k s C M

end DiscretisedFurstenbergEstimate.CombiningTheoremRework
