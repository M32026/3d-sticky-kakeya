import MyLeanRepo.Kakeya.Streamlined.Geometry
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Generic helpers for deterministic random-translation assemblies

This module contains the two dependency-light facts that were previously
available only through the open `StickyImpliesGeneral` target:

* the unit ball has positive finite volume;
* every fixed finite `ENNReal` constant is absorbed by a negative power at
  sufficiently small scale.

Existing closed modules remain the canonical owners of tube-family mass and
`realRpowENN` algebra.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Streamlined

/-- The unit ball has positive, finite volume. -/
lemma unitBall_volume_pos_and_lt_top :
    0 < volume unitBall.carrier ∧ volume unitBall.carrier ≠ ⊤ := by
  have hcarrier :
      unitBall.carrier = Metric.closedBall (0 : Point3) 1 := by
    simp [unitBall, Kakeya.DeltaTube.unitBall]
  have hfinite : volume unitBall.carrier ≠ ⊤ := by
    rw [hcarrier]
    exact Metric.isBounded_closedBall.measure_lt_top.ne
  have hopen : IsOpen (Metric.ball (0 : Point3) 1) :=
    Metric.isOpen_ball
  have hnonempty : Set.Nonempty (Metric.ball (0 : Point3) 1) := by
    exact ⟨0, by simp⟩
  have hsubset :
      Metric.ball (0 : Point3) 1 ⊆ unitBall.carrier := by
    rw [hcarrier]
    exact Metric.ball_subset_closedBall
  have hpositive : 0 < volume unitBall.carrier :=
    lt_of_lt_of_le
      (hopen.measure_pos volume hnonempty)
      (measure_mono hsubset)
  exact ⟨hpositive, hfinite⟩

/--
Every fixed finite constant is bounded by `δ⁻γ` at sufficiently small scale.
-/
lemma exists_delta_pow_bound
    (D : ENNReal) (hD : D ≠ ⊤) {γ : ℝ} (hγ : 0 < γ) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
        D ≤ Kakeya.realRpowENN δ (-γ) := by
  by_cases hD0 : D = 0
  · refine ⟨1, by norm_num, fun δ _ _ => ?_⟩
    rw [hD0]
    simp [Kakeya.realRpowENN]
  · have hD_pos : 0 < D := Ne.bot_lt hD0
    have hD_real_pos : 0 < D.toReal :=
      ENNReal.toReal_pos hD0 hD
    let δ₀ : ℝ := (D.toReal)⁻¹ ^ (γ⁻¹)
    have hδ₀_pos : 0 < δ₀ := by positivity
    refine ⟨δ₀, hδ₀_pos, fun δ hδ hδle => ?_⟩
    have hpow : δ ^ γ ≤ D.toReal⁻¹ := by
      have hmono : δ ^ γ ≤ δ₀ ^ γ := by gcongr
      have hδ₀_pow : δ₀ ^ γ = D.toReal⁻¹ := by
        dsimp only [δ₀]
        rw [← Real.rpow_mul (by positivity)]
        have hinv_mul : γ⁻¹ * γ = 1 := by field_simp
        rw [hinv_mul]
        simp
      simpa [hδ₀_pow] using hmono
    have hreal : D.toReal ≤ δ ^ (-γ) := by
      rw [Real.rpow_neg (by linarith)]
      have hinv :
          (D.toReal⁻¹)⁻¹ ≤ (δ ^ γ)⁻¹ := by
        gcongr
      have hinv_inv : (D.toReal⁻¹)⁻¹ = D.toReal := by
        field_simp [hD_real_pos.ne']
      simpa [hinv_inv] using hinv
    have hmain : D ≤ ENNReal.ofReal (δ ^ (-γ)) := by
      rw [ENNReal.le_ofReal_iff_toReal_le hD (by positivity)]
      exact hreal
    simpa [Kakeya.realRpowENN] using hmain

end Kakeya.Streamlined
