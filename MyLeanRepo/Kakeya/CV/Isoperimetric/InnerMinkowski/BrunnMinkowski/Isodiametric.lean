import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.BrunnMinkowski.BM
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.Convex.Measure

/-!
# 2D Isodiametric Inequality and Hausdorff Measure Lower Bound

## Main results

- `isodiametric_twoDim_compact`: isodiametric inequality for compact sets in `E 2`.
- `isodiametric_twoDim`: isodiametric inequality for all bounded sets in `E 2`.
- `hausdorff_ge_area_two_dim`: `μH[2] ≥ (4/π) • volume` on `E 2`.

## Proof sketch

1. Brunn–Minkowski with `A = S`, `B = -S` gives `volume(S - S) ≥ 4 · volume(S)`.
2. `S - S ⊆ closedBall(0, diam S)`, and `volume(closedBall(0, r)) = π · r²`.
3. Therefore `volume(S) ≤ (π/4) · diam(S)²`.
4. For arbitrary bounded sets, pass to the closure (compact in finite dimensions).
5. Define `μ := (4/π) • volume`. From (3), `μ(S) ≤ ediam(S)²` for all bounded `S`.
6. Apply `Metric.le_hausdorffMeasure` to get `μ ≤ μH[2]`.
-/

noncomputable section

open scoped Pointwise ENNReal

open MeasureTheory Metric Set ENNReal

namespace Geometry

/-- Helper: square of square root on ENNReal. -/
private lemma ennreal_sqrt_sq (x : ENNReal) : (x ^ (1 / (2 : ℝ))) ^ 2 = x := by
  have h1 : (x ^ (1 / (2 : ℝ))) ^ 2 =
      (x ^ (1 / (2 : ℝ))) * (x ^ (1 / (2 : ℝ))) := by
    rw [pow_two]
  rw [h1]
  have h2 : (x ^ (1 / (2 : ℝ))) * (x ^ (1 / (2 : ℝ))) =
      x ^ ((1 / (2 : ℝ)) + (1 / (2 : ℝ))) := by
    rw [← ENNReal.rpow_add_of_nonneg] <;> norm_num
  rw [h2]
  have h3 : (1 / (2 : ℝ)) + (1 / (2 : ℝ)) = 1 := by norm_num
  rw [h3]
  simp

/-- **2D isodiametric inequality for compact sets.** -/
lemma isodiametric_twoDim_compact (S : Set (E 2)) (hS : IsCompact S)
    (hS_nonempty : S.Nonempty) :
    volume S ≤ ENNReal.ofReal (Real.pi / 4) * ENNReal.ofReal (Metric.diam S) ^ 2 := by
  let B : Set (E 2) := -S
  have hB : IsCompact B := hS.neg
  have hB_nonempty : B.Nonempty := by
    simpa [B] using hS_nonempty.image (fun x => -x)
  have hS_meas : MeasurableSet S := hS.measurableSet
  have hB_meas : MeasurableSet B := hB.measurableSet
  have h_sum_meas : MeasurableSet (S + B) := (hS.add hB).measurableSet
  have hBM := brunnMinkowski 2 (by norm_num) S B hS_meas hB_meas hS_nonempty hB_nonempty h_sum_meas
  have hvolB : volume B = volume S := by
    simpa [B] using volume_preimage_neg S
  have h1 : volume (S + B) ^ (1 / (2 : ℝ)) ≥
      volume S ^ (1 / (2 : ℝ)) + volume B ^ (1 / (2 : ℝ)) := hBM
  rw [hvolB] at h1
  set y : ENNReal := volume S ^ (1 / (2 : ℝ)) with hy_def
  have h2 : volume (S + B) ^ (1 / (2 : ℝ)) ≥ 2 * y := by
    have h21 : y + y = 2 * y := by rw [← two_mul]
    rw [h21] at h1
    exact h1
  have h3 : volume (S + B) ≥ 4 * volume S := by
    have h4 : (volume (S + B) ^ (1 / (2 : ℝ))) ^ 2 ≥ (2 * y) ^ 2 := by gcongr
    have h5 : (volume (S + B) ^ (1 / (2 : ℝ))) ^ 2 = volume (S + B) := ennreal_sqrt_sq _
    have h6 : (2 * y) ^ 2 = 4 * volume S := by
      have h61 : (2 * y) ^ 2 = (2 : ENNReal) ^ 2 * y ^ 2 := by rw [mul_pow]
      rw [h61]
      have h62 : (2 : ENNReal) ^ 2 = 4 := by norm_num
      rw [h62]
      have h63 : y ^ 2 = volume S := ennreal_sqrt_sq (volume S)
      rw [h63]
      <;> rfl
    rw [h5, h6] at h4
    exact h4
  have hS_bdd := hS.isBounded
  have h_subset : S + B ⊆ closedBall (0 : E 2) (Metric.diam S) := by
    intro z hz
    rcases hz with ⟨x, hx, y, hy, rfl⟩
    have hny : -y ∈ S := by simpa [B] using hy
    have h_dist : dist x (-y) ≤ Metric.diam S := Metric.dist_le_diam_of_mem hS_bdd hx hny
    have h_eq : dist x (-y) = ‖x + y‖ := by
      simp [dist_eq_norm] <;> abel
    rw [h_eq] at h_dist
    simpa [dist_zero_right, dist_eq_norm] using h_dist
  have h4 : volume (S + B) ≤ volume (closedBall (0 : E 2) (Metric.diam S)) :=
    measure_mono h_subset
  have h5 : volume (closedBall (0 : E 2) (Metric.diam S)) =
      ENNReal.ofReal (Metric.diam S) ^ 2 * ENNReal.ofReal Real.pi := by
    exact EuclideanSpace.volume_closedBall_fin_two 0 (Metric.diam S)
  rw [h5] at h4
  have h6 : 4 * volume S ≤ ENNReal.ofReal (Metric.diam S) ^ 2 * ENNReal.ofReal Real.pi :=
    le_trans h3 h4
  set a : ENNReal := ENNReal.ofReal (Metric.diam S) ^ 2 with ha
  set b : ENNReal := ENNReal.ofReal Real.pi with hb
  set c : ENNReal := ENNReal.ofReal (1 / 4 : ℝ) with hc
  have h7 : c * (4 * volume S) ≤ c * (a * b) := by gcongr
  have h8 : c * (4 * volume S) = volume S := by
    have hc4 : c = (4 : ENNReal)⁻¹ := by
      simp [hc] <;> norm_num
    rw [hc4, ENNReal.inv_mul_cancel_left] <;> norm_num
  have h_real : (1 / 4 : ℝ) * Real.pi = Real.pi / 4 := by ring
  have hcb : c * b = ENNReal.ofReal (Real.pi / 4) := by
    rw [hc, hb, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 4)]
    rw [h_real]
  have h9 : c * (a * b) = a * (c * b) := by
    simp [mul_assoc, mul_comm, mul_left_comm]
  have h10 : c * (a * b) = ENNReal.ofReal (Real.pi / 4) * a := by
    rw [h9, hcb, mul_comm]
  rw [h8, h10] at h7
  exact h7

/-- **2D isodiametric inequality for all bounded sets.** -/
lemma isodiametric_twoDim (S : Set (E 2)) {hS_bdd : Bornology.IsBounded S} :
    volume S ≤ ENNReal.ofReal (Real.pi / 4) * ENNReal.ofReal (Metric.diam S) ^ 2 := by
  by_cases h_empty : S = ∅
  · rw [h_empty] <;> simp
  · have hS_nonempty : S.Nonempty := Set.nonempty_iff_ne_empty.mpr h_empty
    let S' : Set (E 2) := closure S
    have hS'_compact : IsCompact S' := hS_bdd.isCompact_closure
    have hS'_nonempty : S'.Nonempty := hS_nonempty.closure
    have h1 : S ⊆ S' := subset_closure
    have h2 : volume S ≤ volume S' := measure_mono h1
    have h3 : Metric.diam S' = Metric.diam S := by
      exact Metric.diam_closure (s := S)
    have h4 := isodiametric_twoDim_compact S' hS'_compact hS'_nonempty
    rw [h3] at h4
    exact le_trans h2 h4

/-- **`μH[2]` is at least `(4/π) • volume` on Euclidean 2-space.** -/
theorem hausdorff_ge_area_two_dim :
    ENNReal.ofReal (4 / Real.pi) • (volume : Measure (E 2)) ≤ μH[2] := by
  let μ : Measure (E 2) := ENNReal.ofReal (4 / Real.pi) • volume
  have h4pi_pos : 0 < (4 / Real.pi : ℝ) := by positivity
  have h4pi_nonneg : 0 ≤ (4 / Real.pi : ℝ) := by positivity
  have h_main : ∀ (s : Set (E 2)), Metric.ediam s ≤ 1 → μ s ≤ Metric.ediam s ^ (2 : ℝ) := by
    intro s hs
    by_cases h_empty : s = ∅
    · simp [h_empty, μ]
    · have h_ediam_ne_top : Metric.ediam s ≠ ⊤ := by
        by_contra h
        rw [h] at hs
        simpa using hs
      have h_bdd : Bornology.IsBounded s :=
        Metric.isBounded_iff_ediam_ne_top.mpr h_ediam_ne_top
      have h_ediam_eq : Metric.ediam s = ENNReal.ofReal (Metric.diam s) := by
        have h : Metric.diam s = ENNReal.toReal (Metric.ediam s) := by rfl
        rw [h]
        rw [ENNReal.ofReal_toReal h_ediam_ne_top]
      have h_iso : volume s ≤ ENNReal.ofReal (Real.pi / 4) * ENNReal.ofReal (Metric.diam s) ^ 2 :=
        isodiametric_twoDim s (hS_bdd := h_bdd)
      have h5 : μ s = ENNReal.ofReal (4 / Real.pi) * volume s := by
        simp [μ] <;> rfl
      rw [h5]
      have h_ediam_pow : Metric.ediam s ^ (2 : ℝ) = ENNReal.ofReal (Metric.diam s) ^ 2 := by
        rw [h_ediam_eq]
        have h : (ENNReal.ofReal (Metric.diam s)) ^ (2 : ℝ) = (ENNReal.ofReal (Metric.diam s)) ^ 2 := by
          rw [ENNReal.rpow_two]
        exact h
      rw [h_ediam_pow]
      have h6 : ENNReal.ofReal (4 / Real.pi) * volume s ≤
          ENNReal.ofReal (4 / Real.pi) * (ENNReal.ofReal (Real.pi / 4) * ENNReal.ofReal (Metric.diam s) ^ 2) := by
        gcongr
      have h7 : ENNReal.ofReal (4 / Real.pi) * ENNReal.ofReal (Real.pi / 4) = 1 := by
        rw [← ENNReal.ofReal_mul h4pi_nonneg]
        <;> norm_num <;> field_simp <;> linarith
      have h8 : ENNReal.ofReal (4 / Real.pi) * (ENNReal.ofReal (Real.pi / 4) * ENNReal.ofReal (Metric.diam s) ^ 2) =
          (ENNReal.ofReal (4 / Real.pi) * ENNReal.ofReal (Real.pi / 4)) * ENNReal.ofReal (Metric.diam s) ^ 2 := by
        simp [mul_assoc]
      calc
        ENNReal.ofReal (4 / Real.pi) * volume s
          ≤ ENNReal.ofReal (4 / Real.pi) * (ENNReal.ofReal (Real.pi / 4) * ENNReal.ofReal (Metric.diam s) ^ 2) := h6
        _ = (ENNReal.ofReal (4 / Real.pi) * ENNReal.ofReal (Real.pi / 4)) * ENNReal.ofReal (Metric.diam s) ^ 2 := h8
        _ = 1 * ENNReal.ofReal (Metric.diam s) ^ 2 := by rw [h7]
        _ = ENNReal.ofReal (Metric.diam s) ^ 2 := by simp
  have h := MeasureTheory.Measure.le_hausdorffMeasure 2 μ 1 (by norm_num) h_main
  exact h

/-- **Pointwise corollary:** `μH[2](S) ≥ (4/π) · volume(S)` for any set `S` in `E 2`. -/
lemma hausdorff_twoDim_ge_volume_scaled (S : Set (E 2)) :
    μH[2] S ≥ ENNReal.ofReal (4 / Real.pi) * volume S := by
  have h : ENNReal.ofReal (4 / Real.pi) • (volume : Measure (E 2)) ≤ μH[2] :=
    hausdorff_ge_area_two_dim
  have h2 : (ENNReal.ofReal (4 / Real.pi) • (volume : Measure (E 2))) S ≤ μH[2] S := h S
  have h3 : (ENNReal.ofReal (4 / Real.pi) • (volume : Measure (E 2))) S =
      ENNReal.ofReal (4 / Real.pi) * volume S := by
    simp [Measure.smul_apply] <;> rfl
  rw [h3] at h2
  exact h2

end Geometry
