import MyLeanRepo.Kakeya.Assouad.Definitions

/-!
# Dyadic pigeonholing by integral mass

A nonnegative measurable function can take arbitrarily small positive values,
so its positive range cannot be partitioned into finitely many dyadic bands
without first discarding a low-value tail.  On a finite-measure support, the
tail below `a` has integral at most `a * μ X`.  Once that is at most half of
the total integral and the function is bounded above by `a * 2^K`, one of the
remaining `K+1` dyadic bands retains a definite fraction of the integral.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

/-- The half-open dyadic value band `[a 2^k, a 2^(k+1))`. -/
def dyadicValueBand
    {α : Type} (g : α → ENNReal) (a : ENNReal) (k : ℕ) : Set α :=
  {x | a * (2 ^ k : ENNReal) ≤ g x ∧
    g x < a * (2 ^ (k + 1) : ENNReal)}

/--
Select one dyadic value band carrying a fixed fraction of the total
`lintegral`.

`X` contains the support of `g`.  The low tail costs at most half of the
integral, and `b ≤ a * 2^K` makes the remaining range a union of `K+1`
half-open bands.  The conclusion also records that the selected band lies
inside `X`, which is needed when it is pulled back to a same-family shading.
-/
def DyadicIntegralBandStatement : Prop :=
  ∀ (α : Type) [MeasurableSpace α],
    ∀ (μ : Measure α),
      ∀ (g : α → ENNReal),
        Measurable g →
        ∀ X : Set α,
          MeasurableSet X →
          (∀ x, x ∉ X → g x = 0) →
          μ X ≠ ⊤ →
          ∀ a b : ENNReal,
            a ≠ 0 →
            a ≠ ⊤ →
            b ≠ ⊤ →
            (∀ x, g x ≤ b) →
            ∀ K : ℕ,
              b ≤ a * (2 ^ K : ENNReal) →
              2 * (a * μ X) ≤ ∫⁻ x, g x ∂μ →
              (∫⁻ x, g x ∂μ) ≠ 0 →
              (∫⁻ x, g x ∂μ) ≠ ⊤ →
              ∃ k : ℕ,
                k ≤ K ∧
                MeasurableSet (dyadicValueBand g a k) ∧
                dyadicValueBand g a k ⊆ X ∧
                (∫⁻ x, g x ∂μ) ≤
                  2 * (K + 1 : ENNReal) *
                    ∫⁻ x in dyadicValueBand g a k, g x ∂μ

end Kakeya.Assouad
