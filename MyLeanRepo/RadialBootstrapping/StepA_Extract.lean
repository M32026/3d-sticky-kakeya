module

/-
  Step A helper: Extract a finite delta-set P from a measure with ball growth.

  Uses:
  - localize_measure to get a bounded subset with positive measure
  - mass_distribution_content to get positive Hausdorff content
  - discreteFrostman_isDeltaSet to extract the delta-set
-/

public import MyLeanRepo.RadialBootstrapping.Basic
public import MyLeanRepo.RadialBootstrapping.MeasureHelpers
public import MyLeanRepo.RadialBootstrapping.DiscreteFrostman
public import MyLeanRepo.RadialBootstrapping.DiscreteFrostmanIsDeltaSet

@[expose] public section

open MeasureTheory Metric Set
open Vendored.MeasureTheory.FractalGeometry.FrostmanLemma
open scoped ENNReal

noncomputable section

namespace RadialBootstrapping

/-- Convert open-ball Frostman bound to closed-ball bound.
    If ν(ball x r) ≤ C*r for all r > 0, then ν(closedBall x r) ≤ C*r. -/
lemma frostman_open_to_closed {ν : Measure Point} [IsProbabilityMeasure ν]
    {C : ℝ} (hC_pos : 0 < C)
    (h_open : ∀ (x : Point) (r : ℝ), 0 < r →
      ν (Metric.ball x r) ≤ ENNReal.ofReal (C * r)) :
    ∀ (x : Point) (r : ℝ), 0 < r →
      ν (Metric.closedBall x r) ≤ ENNReal.ofReal (C * r) := by
  intro x r hr
  have h_fin : ν (Metric.closedBall x r) ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) (measure_mono (Set.subset_univ _))
  by_contra h
  have h_gt : ENNReal.ofReal (C * r) < ν (Metric.closedBall x r) := lt_of_not_ge h
  have h_iff : (ENNReal.ofReal (C * r)).toReal < (ν (Metric.closedBall x r)).toReal ↔
      ENNReal.ofReal (C * r) < ν (Metric.closedBall x r) :=
    ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top h_fin
  have hCr_nonneg : 0 ≤ C * r := mul_nonneg hC_pos.le hr.le
  have h_real_gt : (ν (Metric.closedBall x r)).toReal > C * r := by
    have h : (ENNReal.ofReal (C * r)).toReal < (ν (Metric.closedBall x r)).toReal :=
      h_iff.mpr h_gt
    have h' : (ENNReal.ofReal (C * r)).toReal = C * r := by
      rw [ENNReal.toReal_ofReal hCr_nonneg]
    rw [h'] at h
    exact h
  set gap : ℝ := (ν (Metric.closedBall x r)).toReal - C * r with hgap_def
  have hgap_pos : 0 < gap := by linarith [h_real_gt]
  set δ : ℝ := gap / (2 * C) with hδ_def
  have hδ_pos : 0 < δ := by
    dsimp only [δ]
    positivity
  have h1 : ν (Metric.closedBall x r) ≤ ν (Metric.ball x (r + δ)) :=
    measure_mono (Metric.closedBall_subset_ball (by linarith))
  have h2 : ν (Metric.ball x (r + δ)) ≤ ENNReal.ofReal (C * (r + δ)) :=
    h_open x (r + δ) (by linarith)
  have h3 : ν (Metric.closedBall x r) ≤ ENNReal.ofReal (C * (r + δ)) :=
    le_trans h1 h2
  have h4 : C * (r + δ) < (ν (Metric.closedBall x r)).toReal := by
    dsimp only [δ, gap]
    have h : C * (r + gap / (2 * C)) = C * r + gap / 2 := by
      field_simp [hC_pos.ne'] <;> ring
    rw [h]
    have h5 : C * r + gap / 2 < C * r + gap := by linarith [hgap_pos]
    have h6 : C * r + gap = (ν (Metric.closedBall x r)).toReal := by
      dsimp only [gap] <;> ring
    linarith
  have hCrδ_nonneg : 0 ≤ C * (r + δ) := by positivity
  have h4' : (ENNReal.ofReal (C * (r + δ))).toReal < (ν (Metric.closedBall x r)).toReal := by
    have h_eq : (ENNReal.ofReal (C * (r + δ))).toReal = C * (r + δ) := by
      rw [ENNReal.toReal_ofReal hCrδ_nonneg]
    rw [h_eq]
    exact h4
  have h_iff2 : (ENNReal.ofReal (C * (r + δ))).toReal < (ν (Metric.closedBall x r)).toReal ↔
      ENNReal.ofReal (C * (r + δ)) < ν (Metric.closedBall x r) :=
    ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top h_fin
  have h5 : ENNReal.ofReal (C * (r + δ)) < ν (Metric.closedBall x r) :=
    h_iff2.mp h4'
  exact not_le.mpr h5 h3

end RadialBootstrapping
end
