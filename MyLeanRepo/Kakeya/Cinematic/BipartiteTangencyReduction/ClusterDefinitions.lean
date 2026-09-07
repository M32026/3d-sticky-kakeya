import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyInputs

/-!
# Finite function-family clusters
-/

namespace Kakeya.Cinematic

def FiniteFunctionFamily.cluster
    (F : FiniteFunctionFamily) (center : C2Function) (radius : ℝ) :
    FiniteFunctionFamily where
  carrier := F.carrier ∩ c2Ball center radius
  finite := F.finite.inter_of_left _

end Kakeya.Cinematic
