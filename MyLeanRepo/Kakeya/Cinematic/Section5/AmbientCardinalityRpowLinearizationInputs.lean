import MyLeanRepo.Kakeya.Cinematic.Section5.NormalCoarseCountAlgebra

/-!
# Linearize the ambient cardinality power

Proposition 26 produces a `3/2` power of a normalized ambient cardinality.
Before summing fixed ambient bins, one copy of the ambient cardinality must
remain linear.  A Katz--Tao cardinality cap controls the remaining square-root
factor.  This statement isolates that algebra without choosing any geometric
or logarithmic constants.
-/

namespace Kakeya.Cinematic

def AmbientCardinalityRpowLinearizationStatement : Prop :=
  ∀ (ambientCard : ℕ)
    (prefactor cardUpper coefficient logTail : ℝ),
    0 ≤ prefactor →
    0 ≤ cardUpper →
    (ambientCard : ℝ) ≤ cardUpper →
    0 ≤ coefficient →
    0 ≤ logTail →
    coefficient *
        Real.rpow (prefactor * (ambientCard : ℝ)) (3 / 2 : ℝ) *
        logTail ≤
      (ambientCard : ℝ) *
        (coefficient * prefactor *
          Real.sqrt (prefactor * cardUpper) * logTail)

end Kakeya.Cinematic
