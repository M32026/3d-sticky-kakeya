module

public import Kakeya.DimensionThree.MainLemma1.Rescaling.Normalized

@[expose] public section
open MeasureTheory ConvexSpaceBody Filter Topology
open Kakeya
namespace Kakeya.ml1Boot

lemma source_window_of_rescaled_window {ε : ℝ} {τ θ dt ρt : NNReal}
    (hε0 : 0 < ε) (hε1 : 5 * ε < 1)
    (hτ0 : 0 < τ) (hτθ : τ ≤ θ) (hθ0 : 0 < θ)
    (hquarter : τ / θ ≤ 1 / 4) (hdt : dt = fineScale τ θ)
    (hlow : dt ^ (1 - 5 * ε) ≤ ρt) (hupp : ρt ≤ dt ^ (5 * ε)) :
    τ * (θ / τ) ^ (5 * ε) ≤ ρt * θ ∧
      ρt * θ ≤ θ * (τ / θ) ^ (5 * ε) := by
  have hdt' : dt = τ / θ := by
    rw [hdt, fineScale, min_eq_left hquarter]
  have hlow' : (τ / θ) ^ (1 - 5 * ε) ≤ ρt := by simpa [hdt'] using hlow
  have hupp' : ρt ≤ (τ / θ) ^ (5 * ε) := by simpa [hdt'] using hupp
  have hτne : τ ≠ 0 := ne_of_gt hτ0
  have hθne : θ ≠ 0 := ne_of_gt hθ0
  have hratio : θ / τ * (τ / θ) = 1 := by field_simp
  have hratio' : τ / θ * (θ / τ) = 1 := by field_simp
  constructor
  · have hpow : (τ / θ) ^ (1 - 5 * ε) ≤ ρt := hlow'
    have hmul := mul_le_mul_of_nonneg_right hpow (show 0 ≤ θ by positivity)
    -- normalize the left endpoint using rpow arithmetic
    calc
      τ * (θ / τ) ^ (5 * ε) = θ * (τ / θ) ^ (1 - 5 * ε) := by
        have hratio2 : θ / τ = (τ / θ)⁻¹ := by field_simp
        have hp : (θ / τ) ^ (5 * ε) = (τ / θ) ^ (-(5 * ε)) := by
          rw [hratio2, NNReal.inv_rpow, ← NNReal.rpow_neg]
        have hτfactor : τ = θ * (τ / θ) := by field_simp
        rw [hp, hτfactor]
        have hratio3 : θ * (τ / θ) / θ = τ / θ := by field_simp
        rw [hratio3]
        have hinner : (τ / θ) * (τ / θ) ^ (-(5 * ε)) =
            (τ / θ) ^ (1 - 5 * ε) := by
          calc
            (τ / θ) * (τ / θ) ^ (-(5 * ε)) =
                (τ / θ) ^ (1 : ℝ) * (τ / θ) ^ (-(5 * ε)) := by rw [NNReal.rpow_one]
            _ = (τ / θ) ^ ((1 : ℝ) + (-(5 * ε))) := by
              rw [NNReal.rpow_add (ne_of_gt (div_pos hτ0 hθ0))]
            _ = (τ / θ) ^ (1 - 5 * ε) := by congr 1
        rw [mul_assoc, hinner]
      _ ≤ θ * ρt := by gcongr
      _ = ρt * θ := by ac_rfl
  · have hpow : ρt ≤ (τ / θ) ^ (5 * ε) := hupp'
    have hmul := mul_le_mul_of_nonneg_right hpow (show 0 ≤ θ by positivity)
    calc
      ρt * θ ≤ (τ / θ) ^ (5 * ε) * θ := hmul
      _ = θ * (τ / θ) ^ (5 * ε) := by ac_rfl

lemma ambient_lower_at_rescaled_source_radius
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {ε e n : ℝ} {δ τ θ dt ρt : NNReal}
    (hε0 : 0 < ε) (hε1 : 5 * ε < 1)
    (hτ0 : 0 < τ) (hτθ : τ ≤ θ) (hθ0 : 0 < θ)
    (hquarter : τ / θ ≤ 1 / 4) (hdt : dt = fineScale τ θ)
    {ι : Type*} {u u' un : Finset ι} (hu'u : u' ⊆ u)
    (Tθ : Tube θ E) (U : ι → ShadedTube τ E)
    (hFb : ∀ σ : NNReal, τ * (θ / τ) ^ (5 * ε) ≤ σ →
      σ ≤ θ * (τ / θ) ^ (5 * ε) → ∀ k ∈ u,
      ∃ Tσ : Tube σ E, Tσ.toConvexSpaceBody ≤ Tθ.toConvexSpaceBody ∧
        (U k).toConvexSpaceBody ≤ Tσ.toConvexSpaceBody ∧
        (δ : ENNReal) ^ e * ((σ / τ : NNReal) : ENNReal) ^ n
          ≤ frostmanConstIn
              (familyIn un (fun k' => (U k').toConvexSpaceBody) Tσ.toConvexSpaceBody)
              (fun k' => (U k').toConvexSpaceBody) Tσ.toConvexSpaceBody)
    (hlow : dt ^ (1 - 5 * ε) ≤ ρt) (hupp : ρt ≤ dt ^ (5 * ε))
    {k : ι} (hk : k ∈ u') :
    ∃ Tσ : Tube (ρt * θ) E, Tσ.toConvexSpaceBody ≤ Tθ.toConvexSpaceBody ∧
      (U k).toConvexSpaceBody ≤ Tσ.toConvexSpaceBody ∧
      (δ : ENNReal) ^ e * (((ρt * θ) / τ : NNReal) : ENNReal) ^ n
        ≤ frostmanConstIn
            (familyIn un (fun k' => (U k').toConvexSpaceBody) Tσ.toConvexSpaceBody)
            (fun k' => (U k').toConvexSpaceBody) Tσ.toConvexSpaceBody := by
  obtain ⟨hlow', hupp'⟩ := source_window_of_rescaled_window hε0 hε1 hτ0 hτθ hθ0
    hquarter hdt hlow hupp
  exact hFb (ρt * θ) hlow' hupp' k (hu'u hk)

/-- The source-scale Frostman gain is exactly the normalized gain after `σ = ρt * θ`. -/
lemma source_gain_ratio_eq_normalized {τ θ ρt : NNReal} (hτ0 : 0 < τ) (hθ0 : 0 < θ) :
    (ρt * θ) / τ = ρt / (τ / θ) := by
  field_simp

end Kakeya.ml1Boot

#print axioms Kakeya.ml1Boot.source_window_of_rescaled_window
#print axioms Kakeya.ml1Boot.ambient_lower_at_rescaled_source_radius
#print axioms Kakeya.ml1Boot.source_gain_ratio_eq_normalized
