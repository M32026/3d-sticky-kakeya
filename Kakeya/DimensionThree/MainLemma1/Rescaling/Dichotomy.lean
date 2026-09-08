/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.Rescaling.Pigeonhole

/-!
# Main Lemma 1, Case (ii): The flat-prism dichotomy

Split out of `Kakeya/DimensionThree/MainLemma1/Rescaling.lean`.
-/

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology

namespace Kakeya

universe u

namespace ml1Boot

/-! ### The flat-prism dichotomy -/

section Dichotomy

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! The coupled dichotomy `Kakeya.ml1Boot.flatPrism_dichotomy`, its numerical step
`Kakeya.ml1Boot.flatPrism_dichotomy_numeric`, and the local interface
`Kakeya.ml1Boot.multiplicity_le_of_factorsThroughFlatPrisms_atBetaPrime` that the former needed
have been **retired**.

The coupled statement could not be discharged: its fullness threshold was universally
quantified, while the interface it had to be derived from hands one out
(`∀ ε' > 0, ∃ η' > 0, …`), and the usable thresholds are downward closed, so no supply of a
single threshold could meet a universally quantified one.  It also coupled the fullness and
Frostman exponents into a single `a`, which no normalized family satisfies.  Both defects are
set out in the docstring of `Kakeya.ml1Boot.flatPrism_dichotomy_decoupled`.  Nothing referred to
the retired declarations in code. -/

/-- The numerical step of `Kakeya.ml1Boot.flatPrism_dichotomy_decoupled`: the decoupled form of
`Kakeya.ml1Boot.flatPrism_dichotomy_numeric`, in which the loss budget `ε'` of
`Kakeya.multiplicity_le_of_factorsThroughFlatPrisms'`, the Frostman exponent `aF` and the
plank-ratio exponent `aLam` are kept apart and tied only by `hslack`.

Writing `CF` for the Frostman constant and `B` for the bracket `(|u| δ̃²) ^ (1 - γ/2)`, the loss
`δ̃ ^ (-ε')` and the Frostman factor `CF ^ (1 - γ/2) ≤ δ̃ ^ (-aF (1 - γ/2))` together cost
`δ̃ ^ (-ε' - aF (1 - γ/2))`, while the failure of the second alternative of the dichotomy gives
`a♯/b♯ ≤ δ̃ ^ (10 aLam / (ε γ))` and hence `(a♯/b♯) ^ (3γ/2) ≤ δ̃ ^ (15 aLam / ε)`.  So `hslack`
is exactly what has to be paid, and nothing else relating `ε`, `aLam` and `aF` is used: in
particular `ε ≤ 1` is not needed here, whereas the coupled
`Kakeya.ml1Boot.flatPrism_dichotomy_numeric` needs it precisely because it forces
`ε' = aF = aLam` and then has to absorb `2 aLam` into `5 aLam / ε`. -/
theorem flatPrism_dichotomy_numeric_decoupled {δt ap bp : NNReal} {ε ε' aLam aF γ : ℝ}
    {CF B : ENNReal}
    (hδt0 : 0 < δt) (hδt1 : δt ≤ 1) (hε0 : 0 < ε) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hslack : ε' + aF * (1 - γ / 2) ≤ 5 * aLam / ε)
    (hCF : CF ≤ (δt : ENNReal) ^ (-aF))
    (hab : (ap : ENNReal) ≤ (δt : ENNReal) ^ (10 * aLam / (ε * γ)) * (bp : ENNReal)) :
    (δt : ENNReal) ^ (-ε') * CF ^ (1 - γ / 2)
        * ((ap : ENNReal) / (bp : ENNReal)) ^ (3 * γ / 2) * (δt : ENNReal) ^ (-2 * γ) * B
      ≤ (δt : ENNReal) ^ (10 * aLam / ε) * (δt : ENNReal) ^ (-2 * γ) * B := by
  let x : ENNReal := (δt : ENNReal)
  have hx0 : x ≠ 0 := by exact ENNReal.coe_ne_zero.mpr (ne_of_gt hδt0)
  have hxtop : x ≠ ⊤ := ENNReal.coe_ne_top
  have hx1 : x ≤ 1 := by exact ENNReal.coe_le_one_iff.mpr hδt1
  have hεne : ε ≠ 0 := ne_of_gt hε0
  have hγne : γ ≠ 0 := ne_of_gt hγ0
  -- CF ^ (1 - γ/2) ≤ x ^ (-(aF * (1 - γ/2)))
  have hCFb : CF ^ (1 - γ / 2) ≤ x ^ (-(aF * (1 - γ / 2))) := by
    have hg : (0 : ℝ) ≤ 1 - γ / 2 := by nlinarith [hγ1]
    calc
      CF ^ (1 - γ / 2) ≤ (x ^ (-aF)) ^ (1 - γ / 2) :=
        ENNReal.rpow_le_rpow hCF hg
      _ = x ^ (-aF * (1 - γ / 2)) := by rw [← ENNReal.rpow_mul]
      _ = x ^ (-(aF * (1 - γ / 2))) := by ring_nf
  -- (ap/bp) ^ (3γ/2) ≤ x ^ (15 * aLam / ε)
  have hdiv : (ap : ENNReal) / (bp : ENNReal) ≤ x ^ (10 * aLam / (ε * γ)) := by
    exact ENNReal.div_le_of_le_mul hab
  have hgt0 : (0 : ℝ) ≤ 3 * γ / 2 := by nlinarith [hγ0]
  have apeq : (10 * aLam / (ε * γ)) * (3 * γ / 2) = 15 * aLam / ε := by
    field_simp [hεne, hγne]
    ring
  have hRange : ((ap : ENNReal) / (bp : ENNReal)) ^ (3 * γ / 2) ≤ x ^ (15 * aLam / ε) := by
    calc
      ((ap : ENNReal) / (bp : ENNReal)) ^ (3 * γ / 2)
          ≤ (x ^ (10 * aLam / (ε * γ))) ^ (3 * γ / 2) :=
            ENNReal.rpow_le_rpow hdiv hgt0
      _ = x ^ (10 * aLam / (ε * γ) * (3 * γ / 2)) := by rw [← ENNReal.rpow_mul]
      _ = x ^ (15 * aLam / ε) := by rw [apeq]
  -- x^(-ε') * x^(-(aF (1 - γ/2))) * x^(15 aLam/ε) = x^(...)
  have hComb2 : x ^ (-ε') * x ^ (-(aF * (1 - γ / 2))) * x ^ (15 * aLam / ε)
      = x ^ (-ε' + -(aF * (1 - γ / 2)) + 15 * aLam / ε) := by
    rw [← ENNReal.rpow_add (-ε') (-(aF * (1 - γ / 2))) hx0 hxtop]
    rw [← ENNReal.rpow_add (-ε' + -(aF * (1 - γ / 2))) (15 * aLam / ε) hx0 hxtop]
  have hSpr : 10 * aLam / ε ≤ -ε' - aF * (1 - γ / 2) + 15 * aLam / ε := by
    have hterm : 15 * aLam / ε = 10 * aLam / ε + 5 * aLam / ε := by
      field_simp [hεne]
      ring
    rw [hterm]
    linarith [hslack]
  have hComb : x ^ (-ε') * x ^ (-(aF * (1 - γ / 2))) * x ^ (15 * aLam / ε)
      ≤ x ^ (10 * aLam / ε) := by
    calc
      x ^ (-ε') * x ^ (-(aF * (1 - γ / 2))) * x ^ (15 * aLam / ε)
          = x ^ (-ε' + -(aF * (1 - γ / 2)) + 15 * aLam / ε) := hComb2
      _ ≤ x ^ (10 * aLam / ε) := ENNReal.rpow_le_rpow_of_exponent_ge hx1 hSpr
  have hP : x ^ (-ε') * CF ^ (1 - γ / 2) * ((ap : ENNReal) / (bp : ENNReal)) ^ (3 * γ / 2)
      ≤ x ^ (-ε') * x ^ (-(aF * (1 - γ / 2))) * x ^ (15 * aLam / ε) := by
    exact mul_le_mul' (mul_le_mul' le_rfl hCFb) hRange
  calc
    (δt : ENNReal) ^ (-ε') * CF ^ (1 - γ / 2)
        * ((ap : ENNReal) / (bp : ENNReal)) ^ (3 * γ / 2) * (δt : ENNReal) ^ (-2 * γ) * B
        ≤ (x ^ (-ε') * x ^ (-(aF * (1 - γ / 2))) * x ^ (15 * aLam / ε)) * x ^ (-2 * γ) * B := by
          exact mul_le_mul' (mul_le_mul' hP le_rfl) le_rfl
    _ ≤ x ^ (10 * aLam / ε) * x ^ (-2 * γ) * B := by
          exact mul_le_mul' (mul_le_mul' hComb le_rfl) le_rfl
    _ = (δt : ENNReal) ^ (10 * aLam / ε) * (δt : ENNReal) ^ (-2 * γ) * B := by
          rfl



end Dichotomy

end ml1Boot

end Kakeya
