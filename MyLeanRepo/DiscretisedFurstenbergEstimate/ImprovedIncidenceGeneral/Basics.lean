module

/-
  Shared definitions for ImprovedIncidenceGeneral.

  Provides E2 (Euclidean plane) and onesVec.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral

open DirecretisedFurstenbergEstimate

abbrev E2 := EuclideanSpace ℝ (Fin 2)

/-- The all-ones vector in E2. -/
def onesVec : E2 := WithLp.equiv 2 (Fin 2 → ℝ) |>.symm fun (_ : Fin 2) => (1 : ℝ)

end DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral
