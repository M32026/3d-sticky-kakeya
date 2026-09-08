import MyLeanRepo.Kakeya.Streamlined.GeneralizedFrostman.DirectionalAntiConcentration
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Topology.MetricSpace.Isometry

/-!
# Measure transport between QuatSphere3 and the Euclidean 4-sphere

This module provides lemmas for transporting a probability measure with a
3-growth bound from the Euclidean sphere to `QuatSphere3` via an isometric
homeomorphism.
-/

open MeasureTheory Metric

namespace Kakeya.Streamlined.GeneralizedFrostman

/-- Transporting a probability measure via a homeomorphism gives a probability measure. -/
lemma transport_probability {α β : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [TopologicalSpace β] [MeasurableSpace β] [BorelSpace α] [BorelSpace β]
    (h : α ≃ₜ β) (μ : Measure β) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (Measure.map h.symm μ) := by
  have h1 : (Measure.map h.symm μ) Set.univ = 1 := by
    rw [Measure.map_apply h.symm.continuous.measurable MeasurableSet.univ]
    <;> simp [IsProbabilityMeasure.measure_univ]
  exact ⟨h1⟩

/-- Transporting a measure via an isometry preserves ball growth bounds. -/
lemma transport_ball_growth {α β : Type*} [PseudoMetricSpace α] [MeasurableSpace α] [BorelSpace α]
    [PseudoMetricSpace β] [MeasurableSpace β] [BorelSpace β]
    (h : α ≃ᵢ β) (μ : Measure β) (C : ENNReal)
    (hgrowth : ∀ (y : β) (r : ℝ), 0 < r → r ≤ 1 →
      μ (Metric.closedBall y r) ≤ C * ENNReal.ofReal (r ^ 3)) :
    ∀ (x : α) (r : ℝ), 0 < r → r ≤ 1 →
      (Measure.map h.symm μ) (Metric.closedBall x r) ≤ C * ENNReal.ofReal (r ^ 3) := by
  intro x r hr hr1
  have h_meas : MeasurableSet (Metric.closedBall x r) := by
    exact measurableSet_closedBall
  have h_preimage : h.symm ⁻¹' (Metric.closedBall x r) = Metric.closedBall (h x) r := by
    ext y
    simp only [Set.mem_preimage, Metric.mem_closedBall]
    have h2 : dist (h.symm y) x = dist y (h x) := by
      calc
        dist (h.symm y) x = dist (h (h.symm y)) (h x) := (h.isometry.dist_eq _ _).symm
        _ = dist y (h x) := by rw [h.apply_symm_apply y]
    rw [h2]
  have h1 : (Measure.map h.symm μ) (Metric.closedBall x r) =
      μ (Metric.closedBall (h x) r) := by
    rw [Measure.map_apply h.symm.continuous.measurable h_meas, h_preimage]
  rw [h1]
  exact hgrowth (h x) r hr hr1

/-- The measure of a set on the target equals the measure of its image. -/
lemma transport_set_measure {α β : Type*} [PseudoMetricSpace α] [MeasurableSpace α] [BorelSpace α]
    [PseudoMetricSpace β] [MeasurableSpace β] [BorelSpace β]
    (h : α ≃ᵢ β) (μ : Measure β) {s : Set α} (hs : MeasurableSet s) :
    (Measure.map h.symm μ) s = μ (h '' s) := by
  have h_preimage : h.symm ⁻¹' s = h '' s := by
    ext y
    simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · intro h2
      exact ⟨h.symm y, h2, h.apply_symm_apply y⟩
    · rintro ⟨z, hz, rfl⟩
      simpa using hz
  rw [Measure.map_apply h.symm.continuous.measurable hs, h_preimage]

end Kakeya.Streamlined.GeneralizedFrostman
