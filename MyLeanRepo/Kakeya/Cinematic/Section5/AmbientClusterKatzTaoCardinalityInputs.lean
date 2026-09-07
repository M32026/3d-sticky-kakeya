import MyLeanRepo.Kakeya.Cinematic.Section5.NormalCoarseCountAlgebra

/-!
# Katz--Tao cardinality of a fixed ambient cluster

The fixed ambient family is a `3t` cluster.  If `3t ≤ 1`, the local
Katz--Tao ball estimate applies directly.  If `3t > 1`, the global
cardinality estimate is already stronger after multiplying by `3t`.
-/

namespace Kakeya.Cinematic

def AmbientClusterKatzTaoCardinalityStatement : Prop :=
  ∀ (F : FiniteFunctionFamily)
    (center : C2Function) (delta t C_KT : ℝ),
    0 < delta →
    0 < t →
    delta ≤ t →
    F.HasKatzTaoBound delta C_KT →
    ((F.cluster center (3 * t)).card : ℝ) ≤
      C_KT * (3 * t / delta)

end Kakeya.Cinematic
