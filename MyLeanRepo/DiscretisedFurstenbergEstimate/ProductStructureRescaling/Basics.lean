module

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.OSWPrelude

@[expose] public section

/-!
# Basic definitions for product-structure rescaling

This module contains all type definitions used in the product-structure
rescaling theorem and its helper lemmas.

Whiteprint node: `covering_scaling` / `grid_residual_scaling` (shared basics)
-/

noncomputable section

open scoped ENNReal NNReal

abbrev EuclideanPlane := EuclideanSpace ℝ (Fin 2)

/-- Convenience wrapper for external covering number. -/
def Ncover {X : Type*} [PseudoMetricSpace X]
    (δ : ℝ) (P : Set X) : ℝ≥0∞ :=
  Metric.externalCoveringNumber δ.toNNReal P

/--
The fine-scale estimate actually available inside the common `Δ`-tube.

This is intentionally not `IsDeltaSSet δ s C P`: the selected packet has only
about `Δ⁻ˢ` elements, not `δ⁻ˢ` elements.  Its regularity is measured in balls
of radius `Δ * r`, which become radius-`r` balls after dilation by `Δ⁻¹`.
-/
def IsRescalableDeltaSet {X : Type*} [PseudoMetricSpace X]
    (δ Δ s C : ℝ) (P : Set X) : Prop :=
  P.Nonempty ∧ 0 < δ ∧ 0 < Δ ∧ 0 < C ∧ 0 ≤ s ∧
    ∀ x : X, ∀ r : ℝ, Δ ≤ r →
      (Metric.externalCoveringNumber δ.toNNReal
          (P ∩ Metric.closedBall x (Δ * r)) : ℝ≥0∞) ≤
        ENNReal.ofReal C * (ENNReal.ofReal r) ^ s *
          (Metric.externalCoveringNumber δ.toNNReal P : ℝ≥0∞)

def integerGrid (δ : ℝ) : Set ℝ :=
  {x | ∃ k : ℤ, x = δ * (k : ℝ)}

def parameterGrid (δ : ℝ) : Set EuclideanPlane :=
  {p | p 0 ∈ integerGrid δ ∧ p 1 ∈ integerGrid δ}

def scaleParameters (Δ : ℝ) (P : Set EuclideanPlane) :
    Set EuclideanPlane :=
  (fun p => (Δ⁻¹ : ℝ) • p) '' P

def lineResidual (z θ : EuclideanPlane) : ℝ :=
  |z 0 - (θ 0 * z 1 + θ 1)|

def productIncidenceSet (Y : Set ℝ) (X : ℝ → Set ℝ) :
    Set EuclideanPlane :=
  ⋃ y ∈ Y, {z | z 0 ∈ X y ∧ z 1 = y}

def unscaleHorizontal (Δ : ℝ) (z : EuclideanPlane) :
    EuclideanPlane :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm
    (fun i : Fin 2 => if i = 0 then Δ * z 0 else z 1)

/-- Weaken the constant of an IsRescalableDeltaSet. -/
lemma IsRescalableDeltaSet.mono_const {X : Type*} [PseudoMetricSpace X]
    {δ Δ s C1 C2 : ℝ} {P : Set X}
    (h : IsRescalableDeltaSet δ Δ s C1 P) (hC : C1 ≤ C2) :
    IsRescalableDeltaSet δ Δ s C2 P := by
  rcases h with ⟨hne, hδ, hΔ, hC1_pos, hs, hmain⟩
  have hC2_pos : 0 < C2 := by linarith
  refine ⟨hne, hδ, hΔ, hC2_pos, hs, fun x r hr => ?_⟩
  have h := hmain x r hr
  have h' : ENNReal.ofReal C1 ≤ ENNReal.ofReal C2 := ENNReal.ofReal_le_ofReal hC
  calc (Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x (Δ * r)) : ENNReal)
    ≤ ENNReal.ofReal C1 * (ENNReal.ofReal r) ^ s *
        (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := h
  _ ≤ ENNReal.ofReal C2 * (ENNReal.ofReal r) ^ s *
        (Metric.externalCoveringNumber δ.toNNReal P : ENNReal) := by gcongr

end
