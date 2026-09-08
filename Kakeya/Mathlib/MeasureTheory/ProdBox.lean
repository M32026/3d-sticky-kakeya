/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Centred boxes in an `L²` product

The parameter space of `Kakeya.Tube.Dilate` is the `L²` product `ℝ × F₁ × F₂` of a line and two
copies of the transverse hyperplane of a tube, and the region in which the tube parameters live
is a centred box `[-h₀, h₀] × B̄(0, h₁) × B̄(0, h₂)` in it.  This file defines that box
(`Metric.prodBox`) and computes its volume as a product of three factors.

## Blueprint correspondence

The blueprint source is `GWZAdapted/section8_genkf.tex`.

* `Metric.volume_preimage_ofLp_closedBall_prod` ↔ `lem:prodClosedBallVolume`;
* `Metric.volume_prodBox` ↔ `lem:prodBoxVolume`.
-/

@[expose] public section

open MeasureTheory Metric Set

namespace Metric

/-- **The centred box** `[-h₀, h₀] × B̄(0, h₁) × B̄(0, h₂)` of the `L²` product
`ℝ × F₁ × F₂` (blueprint `lem:prodBoxVolume`, `lem:boxThickeningVolume` and
`lem:endpointRegionMeasure`). -/
def prodBox {F₁ F₂ : Type*} [Norm F₁] [Norm F₂] (h₀ h₁ h₂ : ℝ) :
    Set (WithLp 2 (ℝ × WithLp 2 (F₁ × F₂))) :=
  {z | |(WithLp.ofLp z).1| ≤ h₀ ∧ ‖(WithLp.ofLp (WithLp.ofLp z).2).1‖ ≤ h₁ ∧
    ‖(WithLp.ofLp (WithLp.ofLp z).2).2‖ ≤ h₂}

variable {F₁ F₂ : Type*} [NormedAddCommGroup F₁] [InnerProductSpace ℝ F₁]
  [FiniteDimensional ℝ F₁] [MeasurableSpace F₁] [BorelSpace F₁]
  [NormedAddCommGroup F₂] [InnerProductSpace ℝ F₂] [FiniteDimensional ℝ F₂]
  [MeasurableSpace F₂] [BorelSpace F₂]

/-- **Volume of a product of two balls in an `L²` product** (blueprint
`lem:prodClosedBallVolume`).  The forgetful map `WithLp.ofLp` is measure preserving, so the
preimage of a product of two closed balls is measurable and its volume is the product of the two
volumes.  No sign hypothesis on `h₁, h₂` is needed: for a negative radius both sides vanish. -/
theorem volume_preimage_ofLp_closedBall_prod (h₁ h₂ : ℝ) :
    MeasurableSet ((WithLp.ofLp : WithLp 2 (F₁ × F₂) → F₁ × F₂) ⁻¹'
        (closedBall (0 : F₁) h₁ ×ˢ closedBall (0 : F₂) h₂)) ∧
      volume ((WithLp.ofLp : WithLp 2 (F₁ × F₂) → F₁ × F₂) ⁻¹'
          (closedBall (0 : F₁) h₁ ×ˢ closedBall (0 : F₂) h₂))
        = volume (closedBall (0 : F₁) h₁) * volume (closedBall (0 : F₂) h₂) := by
  -- The forgetful map is measure preserving.
  have hmp : MeasurePreserving (@WithLp.ofLp 2 (F₁ × F₂)) :=
    WithLp.volume_preserving_ofLp F₁ F₂
  -- The target is a product of two closed balls, hence measurable.
  have h_meas : MeasurableSet (closedBall (0 : F₁) h₁ ×ˢ closedBall (0 : F₂) h₂) :=
    measurableSet_closedBall.prod measurableSet_closedBall
  constructor
  · exact hmp.measurable h_meas
  · rw [hmp.measure_preimage h_meas.nullMeasurableSet,
      MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod]

/-- **Volume of a centred box** (blueprint `lem:prodBoxVolume`): the box is the preimage under
the outer `WithLp.ofLp` of `[-h₀, h₀] ×ˢ (B̄(0, h₁) ×ˢ B̄(0, h₂))`, and `Real.volume_Icc`
evaluates the axial factor.  No sign hypothesis is needed on `h₀, h₁, h₂`. -/
theorem volume_prodBox (h₀ h₁ h₂ : ℝ) :
    volume (prodBox (F₁ := F₁) (F₂ := F₂) h₀ h₁ h₂)
      = ENNReal.ofReal (2 * h₀) * volume (closedBall (0 : F₁) h₁)
        * volume (closedBall (0 : F₂) h₂) := by
  /- The transverse factor: preimage of `B̄(0, h₁) × B̄(0, h₂)` under the inner forgetful map. -/
  let inner : Set (WithLp 2 (F₁ × F₂)) :=
    WithLp.ofLp ⁻¹' (Metric.closedBall (0 : F₁) h₁ ×ˢ Metric.closedBall (0 : F₂) h₂)
  -- The outer forgetful map is measure preserving.
  have hf : MeasurePreserving (@WithLp.ofLp 2 (ℝ × WithLp 2 (F₁ × F₂))) :=
    WithLp.volume_preserving_ofLp ℝ (WithLp 2 (F₁ × F₂))
  -- The box is the preimage of `[-h₀, h₀] ×ˢ inner`.
  have hB_eq : prodBox (F₁ := F₁) (F₂ := F₂) h₀ h₁ h₂ =
      (@WithLp.ofLp 2 (ℝ × WithLp 2 (F₁ × F₂))) ⁻¹' (Set.Icc (-h₀) h₀ ×ˢ inner) := by
    ext z
    simp [Metric.prodBox, inner, abs_le]
  -- `inner` is measurable and its volume is the product of the two ball volumes.
  have hmeas_inner : MeasurableSet inner := by
    change MeasurableSet
      ((WithLp.ofLp : WithLp 2 (F₁ × F₂) → F₁ × F₂) ⁻¹'
        (Metric.closedBall (0 : F₁) h₁ ×ˢ Metric.closedBall (0 : F₂) h₂))
    exact (Metric.volume_preimage_ofLp_closedBall_prod (F₁ := F₁) (F₂ := F₂) h₁ h₂).1
  have hvol_inner : volume inner = volume (closedBall (0 : F₁) h₁)
      * volume (closedBall (0 : F₂) h₂) := by
    change volume
      ((WithLp.ofLp : WithLp 2 (F₁ × F₂) → F₁ × F₂) ⁻¹'
        (Metric.closedBall (0 : F₁) h₁ ×ˢ Metric.closedBall (0 : F₂) h₂)) = _
    exact (Metric.volume_preimage_ofLp_closedBall_prod (F₁ := F₁) (F₂ := F₂) h₁ h₂).2
  -- The target is measurable as a product of intervals and balls.
  have hmeas : MeasurableSet (Set.Icc (-h₀) h₀ ×ˢ inner) := measurableSet_Icc.prod hmeas_inner
  rw [hB_eq, hf.measure_preimage hmeas.nullMeasurableSet,
    MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod, hvol_inner,
    Real.volume_Icc]
  ring_nf

end Metric
