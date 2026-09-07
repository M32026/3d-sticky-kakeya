import MyLeanRepo.Kakeya.Assouad.WZ1.Statements
import Mathlib.Probability.UniformOn
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Smoothed probability measure from DiscreteSet — Basic definitions

Convolve the uniform atomic measure on a finite set with a uniform
ball measure to obtain a probability measure.

This module contains:
- `ballUniformMeasure`: uniform probability on `B(0, ρ)`
- `smoothMeasure`: average of translated ball-uniform measures
- Apply lemmas for both
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set Metric

/-- Uniform probability measure on the open ball `B(0, ρ)`. -/
def ballUniformMeasure (ρ : ℝ) (hρ : 0 < ρ) : ProbabilityMeasure Point2 :=
  let m : Measure Point2 := volume.restrict (Metric.ball (0 : Point2) ρ)
  let total : ENNReal := volume (Metric.ball (0 : Point2) ρ)
  have h_vol : total = ENNReal.ofReal ρ ^ 2 * ENNReal.ofReal Real.pi :=
    EuclideanSpace.volume_ball_fin_two (0 : Point2) ρ
  have h_total_pos : 0 < total := by
    rw [h_vol] <;> positivity
  have h_total_ne_zero : total ≠ 0 := h_total_pos.ne'
  have h_total_ne_top : total ≠ ⊤ := by
    rw [h_vol]
    have h1 : ENNReal.ofReal ρ ≠ ⊤ := ENNReal.ofReal_ne_top
    have h2 : (ENNReal.ofReal ρ)^2 ≠ ⊤ := by
      simpa [pow_two] using ENNReal.mul_ne_top h1 h1
    exact ENNReal.mul_ne_top h2 ENNReal.ofReal_ne_top
  ⟨total⁻¹ • m, by
    refine' ⟨_⟩
    have h2 : m Set.univ = total := by
      unfold m total
      have h_restrict : volume.restrict (Metric.ball (0 : Point2) ρ) Set.univ =
          volume (Set.univ ∩ Metric.ball (0 : Point2) ρ) := by
        exact MeasureTheory.Measure.restrict_apply₀ (by simp)
      rw [h_restrict] <;> simp
    have h : (total⁻¹ • m) Set.univ = total⁻¹ * m Set.univ := by rfl
    rw [h, h2]
    exact ENNReal.inv_mul_cancel h_total_ne_zero h_total_ne_top⟩

/-- The ball-uniform measure of a measurable set. -/
lemma ballUniformMeasure_apply {ρ : ℝ} (hρ : 0 < ρ) {S : Set Point2} (hS : MeasurableSet S) :
    (ballUniformMeasure ρ hρ : Measure Point2) S =
      (MeasureTheory.volume (Metric.ball (0 : Point2) ρ))⁻¹ *
        MeasureTheory.volume (Metric.ball (0 : Point2) ρ ∩ S) := by
  let total : ENNReal := MeasureTheory.volume (Metric.ball (0 : Point2) ρ)
  let m : Measure Point2 := MeasureTheory.volume.restrict (Metric.ball (0 : Point2) ρ)
  have h_eq : (ballUniformMeasure ρ hρ : Measure Point2) = total⁻¹ • m := by rfl
  rw [h_eq, MeasureTheory.Measure.smul_apply]
  have h2 : m S = MeasureTheory.volume (Metric.ball (0 : Point2) ρ ∩ S) := by
    have h_ball_meas : MeasurableSet (Metric.ball (0 : Point2) ρ) := Metric.isOpen_ball.measurableSet
    have h_restrict : m S = MeasureTheory.volume (S ∩ Metric.ball (0 : Point2) ρ) :=
      MeasureTheory.Measure.restrict_apply' h_ball_meas
    have h_comm : S ∩ Metric.ball (0 : Point2) ρ = Metric.ball (0 : Point2) ρ ∩ S := by
      ext x; simp [and_comm]
    rw [h_restrict, h_comm]
  rw [h2]
  dsimp only [total]
  <;> rfl

/-- Evaluation at a measurable set as an AddMonoidHom. -/
private def evalAt (E : Set Point2) (hE : MeasurableSet E) :
    AddMonoidHom (Measure Point2) ENNReal :=
  { toFun := fun μ => μ E
    map_zero' := by simp
    map_add' := fun μ₁ μ₂ => by simp }

/-- The smoothed measure: average of translated ball-uniform measures. -/
def smoothMeasure (A : DiscreteSet 2) (hne : A.Nonempty) (ρ : ℝ) (hρ : 0 < ρ) :
    ProbabilityMeasure Point2 :=
  let σ := ballUniformMeasure ρ hρ
  let f : Point2 → Measure Point2 := fun a =>
    (σ.map (f := fun y : Point2 => a + y)
      (f_aemble := (by fun_prop : Measurable (fun y : Point2 => a + y)).aemeasurable) : Measure Point2)
  let m : Measure Point2 := (A.card : ENNReal)⁻¹ • Finset.sum A f
  ⟨m, by
    refine' ⟨_⟩
    have h_each : ∀ a ∈ A, f a Set.univ = 1 := by
      intro a _
      have h4 : f a Set.univ = (σ : Measure Point2) Set.univ := by
        change (σ.map (f := fun y : Point2 => a + y)
          (f_aemble := (by fun_prop : Measurable (fun y : Point2 => a + y)).aemeasurable) : Measure Point2) Set.univ =
            (σ : Measure Point2) Set.univ
        rw [ProbabilityMeasure.map_apply' σ (f_aemble := (by fun_prop : Measurable (fun y : Point2 => a + y)).aemeasurable) MeasurableSet.univ]
        <;> simp
      rw [h4]
      <;> simp
    have h_sum1 : (Finset.sum A f) Set.univ = (A.card : ENNReal) := by
      have h_eval : (Finset.sum A f) Set.univ = ∑ a ∈ A, f a Set.univ := by
        exact map_sum (evalAt Set.univ MeasurableSet.univ) f A
      rw [h_eval]
      rw [Finset.sum_congr rfl h_each]
      <;> simp
      <;> norm_cast
    have h_smul : m Set.univ = (A.card : ENNReal)⁻¹ * (Finset.sum A f) Set.univ := by
      unfold m
      exact MeasureTheory.Measure.smul_apply ((A.card : ENNReal)⁻¹) (Finset.sum A f) Set.univ
    have h : m Set.univ = (A.card : ENNReal)⁻¹ * (A.card : ENNReal) := by
      rw [h_smul, h_sum1]
    rw [h]
    have hpos : (A.card : ENNReal) ≠ 0 := by exact_mod_cast hne.card_pos.ne'
    have htop : (A.card : ENNReal) ≠ ⊤ := by simp
    exact ENNReal.inv_mul_cancel hpos htop⟩

/-- The smoothed measure of a measurable set equals the average of translated ball measures. -/
lemma smoothMeasure_apply
    {A : DiscreteSet 2} {hne : A.Nonempty} {ρ : ℝ} {hρ : 0 < ρ}
    {E : Set Point2} (hE : MeasurableSet E) :
    (smoothMeasure A hne ρ hρ : Measure Point2) E =
      (A.card : ENNReal)⁻¹ * ∑ a ∈ A,
        (ballUniformMeasure ρ hρ : Measure Point2) {y : Point2 | a + y ∈ E} := by
  let σ := ballUniformMeasure ρ hρ
  let f : Point2 → Measure Point2 := fun a =>
    (σ.map (f := fun y : Point2 => a + y)
      (f_aemble := (by fun_prop : Measurable (fun y : Point2 => a + y)).aemeasurable) : Measure Point2)
  have h_main : (smoothMeasure A hne ρ hρ : Measure Point2) E =
      (A.card : ENNReal)⁻¹ * (Finset.sum A f) E := by
    unfold smoothMeasure
    <;> rfl
  rw [h_main]
  have h_sum : (Finset.sum A f) E = ∑ a ∈ A, f a E := by
    exact map_sum (evalAt E hE) f A
  rw [h_sum]
  apply congr_arg (fun x => (A.card : ENNReal)⁻¹ * x)
  apply Finset.sum_congr rfl
  intro a _
  have h4 : f a E = (σ : Measure Point2) {y : Point2 | a + y ∈ E} := by
    change (σ.map (f := fun y : Point2 => a + y)
      (f_aemble := (by fun_prop : Measurable (fun y : Point2 => a + y)).aemeasurable) : Measure Point2) E =
        (σ : Measure Point2) {y : Point2 | a + y ∈ E}
    rw [ProbabilityMeasure.map_apply' σ (f_aemble := (by fun_prop : Measurable (fun y : Point2 => a + y)).aemeasurable) hE]
    <;> rfl
  exact h4

end Kakeya.Assouad
