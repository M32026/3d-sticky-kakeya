import MyLeanRepo.Kakeya.Streamlined.Estimates

/-!
# Distinguished paper scale grid

This module contains only the numerical scale grid and its interpolation
statement.  It is independent of strict or assigned cover structures.
-/

noncomputable section

namespace Kakeya.Streamlined

/--
Number of adjacent scale intervals in the paper's
`M = ceil (log (log (1 / delta)))` grid.  The guards only affect large
`delta`; all refinement statements quantify over sufficiently small scales.
-/
def uniformScaleSteps (delta : ℝ) : ℕ :=
  max 1 (Nat.ceil (Real.log (max 1 (Real.log (1 / delta)))))

/-- Index type for the finite paper scale grid. -/
abbrev UniformScaleIndex (delta : ℝ) :=
  Fin (uniformScaleSteps delta + 1)

/--
The `k`-th paper scale, clamped to `[delta, 1]` so it is definitionally an
admissible scale even before smallness properties of `delta` are invoked.
-/
def uniformScale (delta : ℝ) (hdelta_le_one : delta ≤ 1)
    (k : UniformScaleIndex delta) : AdmissibleScale delta :=
  ⟨max delta
      (min 1
        (delta ^ ((k : ℝ) / (uniformScaleSteps delta : ℝ)))),
    le_max_left _ _,
    max_le hdelta_le_one (min_le_left _ _)⟩

/--
Every admissible scale is bounded above by a paper-grid scale within one
subpolynomial multiplicative factor.

This is the faithful numerical interpolation statement behind the paper's
all-scale convention.  It does not assert the generally false existence of an
exact-radius, essentially-distinct tube cover at every intermediate scale.
-/
def UniformScaleBracketingStatement : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
      ∀ hdelta_le_one : delta ≤ 1,
      ∀ rho : AdmissibleScale delta,
        ∃ k : UniformScaleIndex delta,
          rho.1 ≤ (uniformScale delta hdelta_le_one k).1 ∧
          (uniformScale delta hdelta_le_one k).1 ≤
            rho.1 * Real.rpow delta (-epsilon)

end Kakeya.Streamlined
