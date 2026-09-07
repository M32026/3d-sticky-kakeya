module

/-
  Lightweight UniformIncidenceData module.

  Moved from RestructuredStatement.lean to break the heavy Prop73 import chain.
  Contains three shared definitions:
  1. canonicalWideCarrier
  2. RegularIncidenceAtScale
  3. UniformIncidenceData

  These are the EXACT definitions from RestructuredStatement.lean, moved verbatim.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.RegularIncidence.Definitions
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AffineLineParams
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DiscretisedFurstenbergEstimate.CombiningTheoremRework

open DiscretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.RegularIncidence

/-- Canonical translated wide carrier for `DyadicTube k`.

    A strip of width `3 * δ_k` around the tube's representative line,
    translated by `(-1/2,-1/2)` so that incidence with the translated
    unit-square point set is preserved.

    This is the carrier for which `UniformRegularIncidenceEstimate`
    (Theorem 6.1) must be supplied. -/
def canonicalWideCarrier (k : ℕ) (T : DyadicTube k) : Set (EuclideanSpace ℝ (Fin 2)) :=
  let δ := dyadicDelta k
  let v : EuclideanSpace ℝ (Fin 2) := WithLp.toLp (2 : ENNReal) fun _ : Fin 2 => -1 / 2
  (fun p : EuclideanSpace ℝ (Fin 2) => p + v) ''
    {p | |p 1 - T.slope * p 0 - T.intercept| ≤ 3 * δ}

/-- Exact-scale regular incidence estimate.

    Unlike `RegularIncidenceBody`, which quantifies over all `0 < δ ≤ δR`,
    this predicate requires the estimate at exactly one scale `δ`. This is
    sufficient for Prop73 consumers, which always evaluate at `δ = dyadicDelta j`.

    This avoids the overstrength of requiring the theorem at every finer scale. -/
def RegularIncidenceAtScale
    {Line : Type*} [PseudoMetricSpace Line] [InStandardChart Line]
    (carrier : Line → Set (EuclideanSpace ℝ (Fin 2)))
    (s t εReg η δ : ℝ) : Prop :=
  ∀ (u : ℝ), t ≤ u → u ≤ 2 →
  ∀ (P : Set (EuclideanSpace ℝ (Fin 2))),
    P ⊆ Metric.closedBall 0 1 →
    IsSquareRootRegular δ u
      (Real.rpow δ (-εReg)) (Real.rpow δ (-εReg)) P →
  ∀ (tubeFamily :
      (p : EuclideanSpace ℝ (Fin 2)) → p ∈ P → Set Line),
    (∀ p hp,
      IsDeltaSSet δ s (Real.rpow δ (-εReg))
        (tubeFamily p hp)) →
    (∀ p hp, ∀ T ∈ tubeFamily p hp,
      p ∈ Metric.cthickening δ (carrier T)) →
    (hChart : ∀ p hp, ∀ T ∈ tubeFamily p hp,
      InStandardChart.inChart T) →
    ENNReal.ofReal (Real.rpow δ (-(2 * s + η))) ≤
      Ncover δ (⋃ p, ⋃ hp : p ∈ P, tubeFamily p hp)

/-- Uniform incidence data from Theorem 6.1: a common threshold δR and
    exact-scale regular-incidence estimates for each carrier scale j.

    EXACT-SCALE DESIGN: `h_body j` returns a `RegularIncidenceAtScale`
    evaluated at exactly `δ = dyadicDelta j`. This is sufficient because
    every Prop73 consumer evaluates the incidence estimate at exactly
    `δ = dyadicDelta j`. The common δR is retained as an upper bound so
    that only scales `dyadicDelta j ≤ δR` need to be supplied. -/
structure UniformIncidenceData (s t ε_inc : ℝ) where
  δR : ℝ
  hδR_pos : 0 < δR
  hδR_one : δR ≤ 1
  h_body : ∀ (j : ℕ), dyadicDelta j ≤ δR →
    RegularIncidenceAtScale (canonicalWideCarrier j) s t ε_inc ε_inc (dyadicDelta j)
  hε_inc_pos : 0 < ε_inc

end DiscretisedFurstenbergEstimate.CombiningTheoremRework
