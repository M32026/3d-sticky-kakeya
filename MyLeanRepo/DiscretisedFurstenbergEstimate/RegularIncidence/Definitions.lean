module

/-
  Definitions for the improved incidence estimate on regular sets.

  Provides the interface types used by B2:
  - `Ncover`: abbreviation for δ-covering number
  - `IsSquareRootRegular`: S-set with sqrt-scale covering bound
  - `UniformAppendixAAlternative`: Appendix A output (fine or coarse bound)
  - `UniformRegularIncidenceEstimate`: the final regular incidence estimate

  Whiteprint node: B2_improved_incidence_regular
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

noncomputable section

namespace DirecretisedFurstenbergEstimate.RegularIncidence

open DirecretisedFurstenbergEstimate

/-- δ-covering number abbreviation. -/
abbrev Ncover {X : Type*} [PseudoMetricSpace X]
    (δ : ℝ) (E : Set X) : ENNReal :=
  Metric.externalCoveringNumber δ.toNNReal E

/-- A set is square-root regular if it is a `(δ,t,C)`-set and its
    `√δ`-covering number is bounded by `K · δ^{-t/2}`. -/
def IsSquareRootRegular
    (δ t C K : ℝ) (P : Set EuclideanPlane) : Prop :=
  IsDeltaSSet δ t C P ∧
  Ncover (Real.sqrt δ) P ≤
    ENNReal.ofReal (K * Real.rpow δ (-t / 2))

namespace IsSquareRootRegular

/-- Extract the `IsDeltaSSet` component. -/
lemma to_isDeltaSSet {δ t C K : ℝ} {P : Set EuclideanPlane}
    (h : IsSquareRootRegular δ t C K P) :
    IsDeltaSSet δ t C P :=
  h.1

/-- Extract the square-root scale covering number upper bound. -/
lemma ncover_sqrt_le {δ t C K : ℝ} {P : Set EuclideanPlane}
    (h : IsSquareRootRegular δ t C K P) :
    Ncover (Real.sqrt δ) P ≤ ENNReal.ofReal (K * Real.rpow δ (-t / 2)) :=
  h.2

/-- When `C = K = δ^{-ε}`, the sqrt bound simplifies to
    `Ncover(√δ, P) ≤ δ^{-(t/2 + ε)}`. -/
lemma ncover_sqrt_bound_simplified
    {δ t ε : ℝ} {P : Set EuclideanPlane}
    (hδ0 : 0 < δ)
    (h : IsSquareRootRegular δ t (Real.rpow δ (-ε)) (Real.rpow δ (-ε)) P) :
    Ncover (Real.sqrt δ) P ≤
      ENNReal.ofReal (Real.rpow δ (-(t / 2 + ε))) := by
  have h1 : Real.rpow δ (-ε) * Real.rpow δ (-t / 2) =
      Real.rpow δ ((-ε) + (-t / 2)) :=
    (Real.rpow_add (by linarith) (-ε) (-t / 2)).symm
  have h2 : (-ε) + (-t / 2) = -(t / 2 + ε) := by ring
  have h3 : Real.rpow δ (-ε) * Real.rpow δ (-t / 2) =
      Real.rpow δ (-(t / 2 + ε)) := by
    rw [h1, h2]
  have h4 := h.ncover_sqrt_le
  rw [h3] at h4
  exact h4

end IsSquareRootRegular

namespace IsDeltaSSet

/-- If `C ≤ C'`, a `(δ,s,C)`-set is also a `(δ,s,C')`-set. -/
lemma weaken_C {X : Type*} [PseudoMetricSpace X]
    {δ s C C' : ℝ} {E : Set X}
    (h : IsDeltaSSet δ s C E) (hC : C ≤ C') :
    IsDeltaSSet δ s C' E := by
  rcases h with ⟨hE, hδ, hC_pos, hs, hcover⟩
  refine' ⟨hE, hδ, by linarith, hs, _⟩
  intro x r hr
  have h4 := hcover x r hr
  have h5 : ENNReal.ofReal C ≤ ENNReal.ofReal C' :=
    ENNReal.ofReal_le_ofReal hC
  calc Ncover δ (E ∩ Metric.closedBall x r)
    ≤ ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * Ncover δ E := h4
  _ ≤ ENNReal.ofReal C' * (ENNReal.ofReal r) ^ s * Ncover δ E := by
    gcongr

end IsDeltaSSet

/-- Uniform metric translation of the main Appendix-A alternative.

    For any `u ∈ [t,2]`, any regular set P, and any tube families,
    either the fine-scale bound holds at δ, or the coarse-scale bound
    holds at √δ. -/
def UniformAppendixAAlternative
    {Line : Type*} [PseudoMetricSpace Line]
    (carrier : Line → Set EuclideanPlane)
    (s t εA : ℝ) : Prop :=
  0 < εA ∧
  ∃ δA : ℝ, 0 < δA ∧ δA ≤ 1 ∧
    ∀ (u : ℝ), t ≤ u → u ≤ 2 →
    ∀ {δ : ℝ}, 0 < δ → δ ≤ δA →
    ∀ (P : Set EuclideanPlane),
      P ⊆ Metric.closedBall 0 1 →
      IsDeltaSSet δ u (Real.rpow δ (-εA)) P →
      Ncover (Real.sqrt δ) P ≤
        ENNReal.ofReal (Real.rpow δ (-(u / 2 + εA))) →
    ∀ (tubeFamily :
        (p : EuclideanPlane) → p ∈ P → Set Line),
      (∀ p hp,
        IsDeltaSSet δ s (Real.rpow δ (-εA))
          (tubeFamily p hp)) →
      (∀ p hp, ∀ T ∈ tubeFamily p hp,
        p ∈ Metric.cthickening δ (carrier T)) →
      let allTubes := ⋃ p, ⋃ hp : p ∈ P, tubeFamily p hp
      ENNReal.ofReal (Real.rpow δ (-(2 * s + εA))) ≤
          Ncover δ allTubes ∨
        ENNReal.ofReal (Real.rpow δ (-(s + εA))) ≤
          Ncover (Real.sqrt δ) allTubes

/-- The body of `UniformRegularIncidenceEstimate` with a fixed threshold `δR`.

    This extracts the core implication so that a common `δR` can be shared
    across multiple carrier scales (needed by Prop73's multiscale induction). -/
def RegularIncidenceBody
    {Line : Type*} [PseudoMetricSpace Line] [InStandardChart Line]
    (carrier : Line → Set EuclideanPlane)
    (s t εReg η δR : ℝ) : Prop :=
  ∀ (u : ℝ), t ≤ u → u ≤ 2 →
  ∀ {δ : ℝ}, 0 < δ → δ ≤ δR →
  ∀ (P : Set EuclideanPlane),
    P ⊆ Metric.closedBall 0 1 →
    IsSquareRootRegular δ u
      (Real.rpow δ (-εReg)) (Real.rpow δ (-εReg)) P →
  ∀ (tubeFamily :
      (p : EuclideanPlane) → p ∈ P → Set Line),
    (∀ p hp,
      IsDeltaSSet δ s (Real.rpow δ (-εReg))
        (tubeFamily p hp)) →
    (∀ p hp, ∀ T ∈ tubeFamily p hp,
      p ∈ Metric.cthickening δ (carrier T)) →
    (hChart : ∀ p hp, ∀ T ∈ tubeFamily p hp,
      InStandardChart.inChart T) →
    ENNReal.ofReal (Real.rpow δ (-(2 * s + η))) ≤
      Ncover δ (⋃ p, ⋃ hp : p ∈ P, tubeFamily p hp)

/-- Uniform regular-set estimate consumed by all good multiscale blocks.
    `εReg` controls input losses; `η` is the output incidence gain. -/
def UniformRegularIncidenceEstimate
    {Line : Type*} [PseudoMetricSpace Line] [InStandardChart Line]
    (carrier : Line → Set EuclideanPlane)
    (s t εReg η : ℝ) : Prop :=
  0 < εReg ∧ 0 < η ∧
  ∃ δR : ℝ, 0 < δR ∧ δR ≤ 1 ∧
    RegularIncidenceBody carrier s t εReg η δR

/-- Extract a `RegularIncidenceBody` from a `UniformRegularIncidenceEstimate`.
    The returned `δR` is the existential witness. -/
lemma UniformRegularIncidenceEstimate.body
    {Line : Type*} [PseudoMetricSpace Line] [InStandardChart Line]
    {carrier : Line → Set EuclideanPlane}
    {s t εReg η : ℝ}
    (h : UniformRegularIncidenceEstimate carrier s t εReg η) :
    ∃ (δR : ℝ), 0 < δR ∧ δR ≤ 1 ∧
      RegularIncidenceBody carrier s t εReg η δR :=
  h.2.2

/-- Reconstruct a `UniformRegularIncidenceEstimate` from a `RegularIncidenceBody`
    with explicit positivity and threshold bounds. -/
lemma RegularIncidenceBody.to_uniform
    {Line : Type*} [PseudoMetricSpace Line] [InStandardChart Line]
    {carrier : Line → Set EuclideanPlane}
    {s t εReg η δR : ℝ}
    (hεReg_pos : 0 < εReg) (hη_pos : 0 < η)
    (hδR_pos : 0 < δR) (hδR_one : δR ≤ 1)
    (h : RegularIncidenceBody carrier s t εReg η δR) :
    UniformRegularIncidenceEstimate carrier s t εReg η :=
  ⟨hεReg_pos, hη_pos, δR, hδR_pos, hδR_one, h⟩

/-- Weaken both constants of `IsSquareRootRegular`. -/
lemma IsSquareRootRegular.weaken_constants
    {δ t C K C' K' : ℝ} {P : Set EuclideanPlane}
    (h : IsSquareRootRegular δ t C K P)
    (hC : C ≤ C') (hK : K ≤ K') :
    IsSquareRootRegular δ t C' K' P := by
  have hδ_pos : 0 < δ := h.1.2.1
  have h1 : IsDeltaSSet δ t C' P := IsDeltaSSet.weaken_C h.1 hC
  have h_nonneg : 0 ≤ Real.rpow δ (-t / 2) := Real.rpow_nonneg hδ_pos.le _
  have h3 : K * Real.rpow δ (-t / 2) ≤ K' * Real.rpow δ (-t / 2) :=
    mul_le_mul_of_nonneg_right hK h_nonneg
  have h4 : (Ncover (Real.sqrt δ) P) ≤ ENNReal.ofReal (K' * Real.rpow δ (-t / 2)) := by
    calc Ncover (Real.sqrt δ) P
      ≤ ENNReal.ofReal (K * Real.rpow δ (-t / 2)) := h.2
    _ ≤ ENNReal.ofReal (K' * Real.rpow δ (-t / 2)) :=
      ENNReal.ofReal_le_ofReal h3
  exact ⟨h1, h4⟩

/-- Shrink the threshold δR of a `RegularIncidenceBody`.
    If the body holds for δR, it holds for any smaller positive δR'. -/
lemma RegularIncidenceBody.shrink_threshold
    {Line : Type*} [PseudoMetricSpace Line] [InStandardChart Line]
    {carrier : Line → Set EuclideanPlane}
    {s t εReg η δR δR' : ℝ}
    (h : RegularIncidenceBody carrier s t εReg η δR)
    (hδR'_pos : 0 < δR') (h_le : δR' ≤ δR) :
    RegularIncidenceBody carrier s t εReg η δR' := by
  intro u hu_t hu_two δ hδ_pos hδ_le'
  have hδ_le : δ ≤ δR := le_trans hδ_le' h_le
  exact h u hu_t hu_two hδ_pos hδ_le

/-- Weaken the exponents of a `RegularIncidenceBody`.

    Smaller `εReg'` means a stronger S-set hypothesis (smaller covering constant),
    so any P satisfying the stronger hypothesis also satisfies the original weaker one.
    Smaller `η'` means a weaker conclusion (smaller lower bound).

    Requires `δR ≤ 1` so that `δ^x` is antitone in `x`. -/
lemma RegularIncidenceBody.weaken_exponents
    {Line : Type*} [PseudoMetricSpace Line] [InStandardChart Line]
    {carrier : Line → Set EuclideanPlane}
    {s t εReg η εReg' η' δR : ℝ}
    (h : RegularIncidenceBody carrier s t εReg η δR)
    (hεReg' : εReg' ≤ εReg) (hη' : η' ≤ η)
    (hεReg'_pos : 0 < εReg') (hη'_pos : 0 < η')
    (hδR_one : δR ≤ 1) :
    RegularIncidenceBody carrier s t εReg' η' δR := by
  intro u hu_t hu_two δ hδ_pos hδ_le P hP_subset hReg tubeFamily hTubes hIncidence hChart
  have hδ_le_one : δ ≤ 1 := le_trans hδ_le hδR_one
  have hC_weak : Real.rpow δ (-εReg') ≤ Real.rpow δ (-εReg) := by
    have h1 : -εReg ≤ -εReg' := by linarith
    exact Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_le_one h1
  have hReg' : IsSquareRootRegular δ u (Real.rpow δ (-εReg)) (Real.rpow δ (-εReg)) P :=
    hReg.weaken_constants hC_weak hC_weak
  have hTubes' : ∀ p hp, IsDeltaSSet δ s (Real.rpow δ (-εReg)) (tubeFamily p hp) := by
    intro p hp
    exact IsDeltaSSet.weaken_C (hTubes p hp) hC_weak
  have h_main : ENNReal.ofReal (Real.rpow δ (-(2 * s + η))) ≤
      Ncover δ (⋃ p, ⋃ hp : p ∈ P, tubeFamily p hp) :=
    h u hu_t hu_two hδ_pos hδ_le P hP_subset hReg' tubeFamily hTubes' hIncidence hChart
  have hη_weak : Real.rpow δ (-(2 * s + η')) ≤ Real.rpow δ (-(2 * s + η)) := by
    have h1 : -(2 * s + η) ≤ -(2 * s + η') := by linarith
    exact Real.rpow_le_rpow_of_exponent_ge hδ_pos hδ_le_one h1
  calc ENNReal.ofReal (Real.rpow δ (-(2 * s + η')))
    ≤ ENNReal.ofReal (Real.rpow δ (-(2 * s + η))) := ENNReal.ofReal_le_ofReal hη_weak
  _ ≤ Ncover δ (⋃ p, ⋃ hp : p ∈ P, tubeFamily p hp) := h_main

end DirecretisedFurstenbergEstimate.RegularIncidence
