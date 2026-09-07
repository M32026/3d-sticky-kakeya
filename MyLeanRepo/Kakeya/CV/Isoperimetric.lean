import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import MyLeanRepo.Kakeya.CV.Isoperimetric.Final

namespace Geometry

/-!
# Isoperimetric inequality (Knill §71)

§71 of Knill's *Some Fundamental Theorems in Mathematics*. For any
measurable bounded `B ⊆ ℝⁿ` with `n ≥ 2`,

  `n^n · |B|^{n−1} · |B₁| ≤ |∂B|^n`

where `|·|` denotes Lebesgue volume on `B` and `B₁` (the closed
Euclidean unit ball), and `μHE[n−1]` is the `(n−1)`-dimensional
Euclidean Hausdorff measure on the topological frontier `∂B`. The
classical Wiedijk-100 entry "The Isoperimetric Theorem".

The `2 ≤ n` hypothesis matches Knill's "smooth surface in `ℝⁿ`
homeomorphic to a sphere" setup, which presupposes `n ≥ 2`. The `n = 1`
case is degenerate and admits explicit counterexamples (e.g. `B = ∅`
gives LHS `= 1 · 0^0 · 2 = 2` in `ℝ≥0∞` while RHS `= 0`); it is
excluded.

`μHE[n−1]` is mathlib's `EuclideanSpace.euclideanHausdorffMeasure`,
scaled so its restriction to an `(n−1)`-dimensional affine subspace
equals Lebesgue, hence the right "surface area" for smooth submanifolds.
For a bounded measurable set, the inequality remains true (vacuously
when the frontier has dimension `> n − 1`); this is the
geometric-measure-theory extension Knill mentions.

## Mathlib status

`grep -i isoperimetric` and `grep -i brunn-minkowski` in mathlib: zero
hits. No isoperimetric inequality, no Brunn–Minkowski, no
perimeter / De Giorgi perimeter, no Minkowski content. Wiedijk's
100-theorems list has no `decl` in `docs/100.yaml` for "The Isoperimetric
Theorem". No open mathlib PRs for "isoperimetric" or "Brunn-Minkowski"
(verified 2026-05-27). Bhavik Mehta's `mirajcs/IsoperimetricInequality`
(2026) proves the `n = 2` planar fragment `L² ≥ 4πA` via
Hurwitz/Fourier but does not cover the `n`-dimensional GMT statement.

Mathlib *has* `MeasureTheory.Measure.euclideanHausdorffMeasure d`
(notation `μHE[d]`), `EuclideanSpace.volume_ball / volume_closedBall`,
and `frontier` — the statement elaborates cleanly. The proof goes
through Brunn–Minkowski plus Steiner symmetrization
(`~500–5000` LoC of new measure-theoretic formalization).
-/

open MeasureTheory ENNReal Metric

/-- **Isoperimetric inequality** (Knill §71). For any measurable bounded
`B ⊆ ℝⁿ` with `n ≥ 2`,
`n^n · volume B^{n−1} · volume (closedBall 0 1) ≤ μHE[n−1] (frontier B)^n`,
with `volume` the standard Lebesgue volume on `EuclideanSpace ℝ (Fin n)`
and `μHE[n−1]` the `(n−1)`-dimensional Euclidean Hausdorff measure on
the topological frontier. For a smooth bounded domain with smooth
bounding hypersurface `S = frontier B`, `μHE[n−1] (frontier B)` agrees
with the classical surface area, so the statement specialises to
Knill's smooth-surface form. -/
theorem isoperimetric (n : ℕ) (_hn : 2 ≤ n) (B : Set (E n))
    (_hB : MeasurableSet B) (_hBdd : Bornology.IsBounded B) :
    (n : ℝ≥0∞) ^ n * (volume B) ^ (n - 1) * volume (closedBall (0 : E n) 1)
      ≤ (μHE[n - 1] (frontier B)) ^ n := by
  have h_main := isoperimetric_main n _hn B _hB _hBdd
  simpa [unitBall] using h_main
