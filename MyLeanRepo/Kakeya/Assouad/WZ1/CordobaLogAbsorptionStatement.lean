import MyLeanRepo.Kakeya.Assouad.WZ1.LocalGrainCubeCountStatements

/-!
# Logarithmic absorption for the WZ1 Lemma 17 Córdoba argument

The finite Córdoba denominator contributes
`8 + 64 * (1 + log k)`.  The separated family is polynomially bounded in
`rho⁻¹`, so one additional factor `rho^epsilon` absorbs this denominator once
`rho` is sufficiently small depending on `epsilon`.
-/

namespace Kakeya.Assouad

/-- The exact logarithmic loss budget used by the Córdoba slab lower bound. -/
def WZ1CordobaLogAbsorptionStatement : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ rho₀ : ℝ, 0 < rho₀ ∧ rho₀ ≤ 1 / 1000 ∧
      ∀ rho : ℝ, 0 < rho → rho ≤ rho₀ →
        ∀ k : ℕ, 1 ≤ k →
          (k : ℝ) ≤ 100 * Real.rpow rho (-3) →
            Real.rpow rho epsilon *
                (8 + 64 * (1 + Real.log (k : ℝ))) ≤
              125 / 3

/--
Assemble the geometric Córdoba leaf after the logarithmic denominator has
been absorbed at a sufficiently small scale.
-/
def WZ1Lemma17CordobaFromLogAbsorptionStatement : Prop :=
  WZ1CordobaLogAbsorptionStatement →
    WZ1Lemma17CordobaSlabLowerStatement

end Kakeya.Assouad
