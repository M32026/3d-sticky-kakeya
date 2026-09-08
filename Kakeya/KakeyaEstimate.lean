/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.KatzTao
public import Kakeya.Shading

/-!
We state the Kakeya estimate and scale δ.
-/

@[expose] public section

open scoped Topology

/-- (Discretised) Kakeya estimate in a n-dimensional Euclidean space with parameters β and η -/
noncomputable def KakeyaEstimate (n : ℕ) [NeZero n] (β : ℝ) (η : ℝ) :=
  open Classical in
  ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
    ∀ (ι : Type*) (s : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin n))),
    (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
    ConvexSpaceBody.IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody) (δ ^ (- η)) →
    ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
    MeasureTheory.volume (⋃ i ∈ s, (T i).shade) ≥ δ ^ β * s.card * δ ^ (n - 1)

/-- Monotonicity in `β`: since `δ ↦ δ^β` is decreasing in `β` for `δ ∈ (0, 1)`,
increasing `β` only weakens the conclusion of the Kakeya estimate. -/
theorem KakeyaEstimate.mono {n : ℕ} [NeZero n] {β β' η : ℝ} (h : β ≤ β')
    (hk : KakeyaEstimate.{u} n β η) : KakeyaEstimate.{u} n β' η := by
  filter_upwards [hk, Ioo_mem_nhdsGT (show (0 : NNReal) < 1 from zero_lt_one)]
    with δ hk_δ ⟨_, hδ_lt_one⟩ ι s T hball hKT hfull
  refine le_trans ?_ (hk_δ ι s T hball hKT hfull)
  have hδE_le_one : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ_lt_one.le
  have hbase : (δ : ENNReal) ^ β' ≤ (δ : ENNReal) ^ β :=
    ENNReal.rpow_le_rpow_of_exponent_ge hδE_le_one h
  exact mul_le_mul_left (mul_le_mul_left hbase _) _

/-- A Kakeya estimate applies equally to tube families contained in a unit ball with an
arbitrary center. -/
theorem KakeyaEstimate.centered {n : ℕ} [NeZero n] {β η : ℝ}
    (hKE : KakeyaEstimate.{u} n β η) :
    ∀ᶠ δ in 𝓝[>] (0 : NNReal),
      ∀ (c : EuclideanSpace ℝ (Fin n)) (ι : Type u) (s : Finset ι)
        (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin n))),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall c 1) →
        ConvexSpaceBody.IsKatzTao s (fun i ↦ (T i).toConvexSpaceBody) (δ ^ (-η)) →
        ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
        MeasureTheory.volume (⋃ i ∈ s, (T i).shade) ≥ δ ^ β * s.card * δ ^ (n - 1) := by
  filter_upwards [hKE] with δ hδ c ι s T hball hKT hfull
  let T' : ι → ShadedTube δ (EuclideanSpace ℝ (Fin n)) := fun i ↦ (T i).translate (-c)
  have hball' : ∀ i ∈ s, (T' i).carrier ⊆ Metric.closedBall 0 1 := by
    intro i hi x hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hyc := hball i hi hy
    simpa [dist_eq_norm, sub_eq_add_neg, add_comm] using hyc
  have hKT' : ConvexSpaceBody.IsKatzTao s
      (fun i ↦ (T' i).toConvexSpaceBody) (δ ^ (-η)) := by
    rw [ConvexSpaceBody.IsKatzTao_def]
    change Kakeya.maxDensity s
        (fun i ↦ ConvexSpaceBody.translate (T i).toConvexSpaceBody (-c)) ≤ _
    rw [Kakeya.maxDensity_translate]
    exact hKT
  have hfull' : ShadedBody.fullness s (fun i ↦ (T' i).toShadedBody) ≥ δ ^ η := by
    change ShadedBody.fullness s (fun i ↦ ((T i).toShadedBody).translate (-c)) ≥ δ ^ η
    rw [ShadedBody.fullness_translate_const]
    exact hfull
  have h := hδ ι s T' hball' hKT' hfull'
  have hunion : (⋃ i ∈ s, (T' i).shade) = (-c + ·) '' (⋃ i ∈ s, (T i).shade) := by
    change (⋃ i ∈ s, (-c + ·) '' (T i).shade) = (-c + ·) '' (⋃ i ∈ s, (T i).shade)
    rw [Set.image_iUnion]
    apply Set.iUnion_congr
    intro i
    rw [Set.image_iUnion]
  rw [hunion, MeasureTheory.measure_image_add] at h
  exact h
