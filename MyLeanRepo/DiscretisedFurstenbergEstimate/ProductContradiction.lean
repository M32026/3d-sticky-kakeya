module

/-
  Product Contradiction Bridge and Helpers

  Extracted from AppendixAssembly.lean. Contains fully proved lemmas:
  - Coordinate conversions between Plane and ℝ×ℝ
  - Metric transfer (sset_metric_change)
  - allFine upper bound
  - mono_const lemmas for IsDeltaSSet and IsRescalableDeltaSet
  - product_configuration_contradiction: product config + A.7 axiom → False
  - CoarseSquare utilities
  - coarse_square_card_le_cover
  - ball_count_to_delta_sset_absorbed

  Whiteprint node: product_contradiction_bridge
-/
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ProductPropBounded
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CoveringUtils
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ProductStructureRescaling.Basics
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

namespace DirecretisedFurstenbergEstimate.ProductContradiction

open DirecretisedFurstenbergEstimate

local notation "Plane" => EuclideanPlane

/-- Abbrev for the theorem function returned by productProp_bounded. -/
abbrev ProductPropBoundedTheorem (s τ η_axiom δ₀ : ℝ) : Prop :=
  ∀ (δ : ℝ), δ ∈ Set.Ioc (0 : ℝ) δ₀ →
    ∀ (Y : Set ℝ)
      (X : ∀ (y : ℝ), y ∈ Y → Set ℝ)
      (T : ∀ (z : ℝ × ℝ),
         z ∈ (⋃ (y : ℝ) (hy : y ∈ Y), X y hy ×ˢ {y}) → Set (ℝ × ℝ)),
      Y ⊆ Set.Icc (-1 : ℝ) 1 →
      (∀ y hy, X y hy ⊆ Set.Icc (-1 : ℝ) 1) →
      (∀ z hz, T z hz ⊆ Set.Icc (-2 : ℝ) 2 ×ˢ Set.Icc (-2 : ℝ) 2) →
      IsDeltaSSet δ τ (Real.rpow δ (-η_axiom)) Y →
      (∀ y hy, IsDeltaSSet δ s (Real.rpow δ (-η_axiom)) (X y hy)) →
      (∀ z hz, IsDeltaSSet δ s (Real.rpow δ (-η_axiom)) (T z hz)) →
      (∀ z hz, ∀ (p : ℝ × ℝ), p ∈ T z hz →
         |p.1 * z.2 + p.2 - z.1| ≤ 4 * δ) →
      ENNReal.ofReal (Real.rpow δ (-(2 * s + η_axiom))) ≤
        (Metric.externalCoveringNumber δ.toNNReal
          (⋃ (z : ℝ × ℝ)
             (hz : z ∈ (⋃ (y : ℝ) (hy : y ∈ Y), X y hy ×ˢ {y})),
             T z hz) : ENNReal)

/-- Weaken the constant in an IsDeltaSSet. -/
lemma IsDeltaSSet.mono_const {X : Type*} [PseudoMetricSpace X] {δ s C1 C2 : ℝ} {P : Set X}
    (h : IsDeltaSSet δ s C1 P) (hC : C1 ≤ C2) : IsDeltaSSet δ s C2 P := by
  rcases h with ⟨hne, hδ, hC1_pos, hs, hbound⟩
  have hC2_pos : 0 < C2 := by linarith
  refine ⟨hne, hδ, hC2_pos, hs, fun x r hr => ?_⟩
  have h4 := hbound x r hr
  have h5 : ENNReal.ofReal C1 ≤ ENNReal.ofReal C2 := ENNReal.ofReal_le_ofReal hC
  have h6 : ENNReal.ofReal C1 * (ENNReal.ofReal r) ^ s * Metric.externalCoveringNumber δ.toNNReal P ≤
      ENNReal.ofReal C2 * (ENNReal.ofReal r) ^ s * Metric.externalCoveringNumber δ.toNNReal P := by
    gcongr
  exact le_trans h4 h6

/-- Weaken the constant in an IsRescalableDeltaSet. -/
lemma IsRescalableDeltaSet.mono_const {X : Type*} [PseudoMetricSpace X] {δ Δ s C1 C2 : ℝ} {P : Set X}
    (h : IsRescalableDeltaSet δ Δ s C1 P) (hC : C1 ≤ C2) : IsRescalableDeltaSet δ Δ s C2 P := by
  rcases h with ⟨hne, hδ, hΔ_pos, hC1_pos, hs, hbound⟩
  have hC2_pos : 0 < C2 := by linarith
  refine ⟨hne, hδ, hΔ_pos, hC2_pos, hs, fun x r hr => ?_⟩
  have h4 := hbound x r hr
  have h5 : ENNReal.ofReal C1 ≤ ENNReal.ofReal C2 := ENNReal.ofReal_le_ofReal hC
  have h6 : ENNReal.ofReal C1 * (ENNReal.ofReal r) ^ s * Metric.externalCoveringNumber δ.toNNReal P ≤
      ENNReal.ofReal C2 * (ENNReal.ofReal r) ^ s * Metric.externalCoveringNumber δ.toNNReal P := by
    gcongr
  exact le_trans h4 h6

end DirecretisedFurstenbergEstimate.ProductContradiction
