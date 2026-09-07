import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Tactic


/-!
# BV Compactness for Indicator Functions — Main Theorem

Ball-average mollification approach.
-/

open MeasureTheory Metric Set ENNReal Filter
open scoped MeasureTheory

namespace Geometry

variable {n : ℕ}

/-- Symmetric difference. -/
def symmDiff (A B : Set (E n)) : Set (E n) := (A \ B) ∪ (B \ A)

/-- The set of translations h where χ_A(x) ≠ χ_A(x+h). -/
def translateMismatch (A : Set (E n)) (x : E n) : Set (E n) :=
  {h | (x ∈ A ↔ x + h ∉ A)}

/-- Ball average error. -/
noncomputable def avgError (δ : ℝ) (A : Set (E n)) (x : E n) : ENNReal :=
  volume (translateMismatch A x ∩ ball (0 : E n) δ) / volume (ball (0 : E n) δ)

/-- Ball-average mollified indicator. -/
noncomputable def ballAverage (A : Set (E n)) (δ : ℝ) (x : E n) : ENNReal :=
  volume (A ∩ ball x δ) / volume (ball (0 : E n) δ)

/-- Volume of ball is translation-invariant. -/
lemma volume_ball_translate (x : E n) (δ : ℝ) :
    volume (ball x δ) = volume (ball (0 : E n) δ) := by
  have h1 : ball x δ = (fun y : E n => y - x) ⁻¹' (ball (0 : E n) δ) := by
    ext y
    simp only [Set.mem_preimage, mem_ball]
    have h_eq : dist y x = dist (y - x) (0 : E n) := by
      simp [dist_eq_norm, dist_zero_right] <;> abel
    rw [h_eq]
  rw [h1]
  have h2 : (fun y : E n => y - x) = fun y : E n => (-x) + y := by
    funext y <;> abel
  rw [h2]
  exact MeasureTheory.measure_preimage_add volume (-x) (ball (0 : E n) δ)

/-- Helper: `volume {h ∈ Bδ | x+h ∈ A} = volume (A ∩ ball x δ)`. -/
lemma volume_mismatch_pos {A : Set (E n)} (hA : MeasurableSet A) (x : E n) (δ : ℝ) :
    volume ({h : E n | h ∈ ball (0 : E n) δ ∧ x + h ∈ A}) =
    volume (A ∩ ball x δ) := by
  let Bδ := ball (0 : E n) δ
  have h1 : {h : E n | h ∈ Bδ ∧ x + h ∈ A} =
      (fun h : E n => x + h) ⁻¹' (A ∩ ball x δ) := by
    ext h
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_inter_iff]
    <;> constructor
    · rintro ⟨hB, hA2⟩
      exact ⟨hA2, by simpa [Bδ, dist_zero_right] using hB⟩
    · rintro ⟨hA2, hB⟩
      exact ⟨by simpa [Bδ, dist_zero_right] using hB, hA2⟩
  rw [h1]
  exact MeasureTheory.measure_preimage_add volume x (A ∩ ball x δ)

/-- Helper: `volume {h ∈ Bδ | x+h ∉ A} = volume ((ball x δ) \ A)`. -/
lemma volume_mismatch_neg {A : Set (E n)} (hA : MeasurableSet A) (x : E n) (δ : ℝ) :
    volume ({h : E n | h ∈ ball (0 : E n) δ ∧ x + h ∉ A}) =
    volume ((ball x δ) \ A) := by
  let Bδ := ball (0 : E n) δ
  have h1 : {h : E n | h ∈ Bδ ∧ x + h ∉ A} =
      (fun h : E n => x + h) ⁻¹' ((ball x δ) \ A) := by
    ext h
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_diff, Set.mem_inter_iff]
    <;> constructor
    · rintro ⟨hB, hnA⟩
      exact ⟨by simpa [Bδ, dist_zero_right] using hB, hnA⟩
    · rintro ⟨hB, hnA⟩
      exact ⟨by simpa [Bδ, dist_zero_right] using hB, hnA⟩
  rw [h1]
  exact MeasureTheory.measure_preimage_add volume x ((ball x δ) \ A)

/-- Ball averages are uniformly bounded in [0,1]. -/
lemma ballAverage_bounded {A : Set (E n)} {δ : ℝ} (hδ : 0 < δ) (x : E n) :
    0 ≤ (ballAverage A δ x).toReal ∧ (ballAverage A δ x).toReal ≤ 1 := by
  classical
  let Bδ := ball (0 : E n) δ
  have hBδ_nonempty : Bδ.Nonempty := ⟨0, by simpa [Bδ, dist_zero_right] using hδ⟩
  have hBδ_pos : 0 < volume Bδ := IsOpen.measure_pos (μ := volume) isOpen_ball hBδ_nonempty
  have hBδ_ne_zero : volume Bδ ≠ 0 := hBδ_pos.ne'
  have hBδ_ne_top : volume Bδ ≠ ⊤ := by
    have h1 : Bδ ⊆ closedBall (0 : E n) δ := ball_subset_closedBall
    have h2 : volume Bδ ≤ volume (closedBall (0 : E n) δ) := measure_mono h1
    have h3 : volume (closedBall (0 : E n) δ) ≠ ⊤ := (isCompact_closedBall (0 : E n) δ).measure_lt_top.ne
    exact ne_top_of_le_ne_top h3 h2
  have h_sub : A ∩ ball x δ ⊆ ball x δ := by simp
  have h_vol1 : volume (A ∩ ball x δ) ≤ volume (ball x δ) := measure_mono h_sub
  have h_vol2 : volume (ball x δ) = volume Bδ := volume_ball_translate x δ
  have h_vol3 : volume (A ∩ ball x δ) ≤ volume Bδ := by
    rw [h_vol2] at h_vol1; exact h_vol1
  have h_le1 : ballAverage A δ x ≤ 1 := by
    dsimp only [ballAverage]
    have h : volume (A ∩ ball x δ) / volume Bδ ≤ volume Bδ / volume Bδ :=
      ENNReal.div_le_div h_vol3 (by rfl)
    have h2 : volume Bδ / volume Bδ = 1 := ENNReal.div_self hBδ_ne_zero hBδ_ne_top
    rw [h2] at h; exact h
  have h_finite : ballAverage A δ x ≠ ⊤ := ne_top_of_le_ne_top one_ne_top h_le1
  have h_iff : (ballAverage A δ x).toReal ≤ (1 : ENNReal).toReal ↔ ballAverage A δ x ≤ 1 :=
    ENNReal.toReal_le_toReal h_finite one_ne_top
  exact ⟨by positivity, h_iff.mpr h_le1⟩

/-- Pointwise identity: `|ballAverage A δ x − χ_A(x)| = avgError δ A x`. -/
lemma ballAverage_error {A : Set (E n)} (hA : MeasurableSet A) {δ : ℝ} (hδ : 0 < δ) (x : E n) :
    ENNReal.ofReal |(ballAverage A δ x).toReal - Set.indicator A (1 : E n → ℝ) x| =
    avgError δ A x := by
  classical
  let Bδ := ball (0 : E n) δ
  have hBδ_nonempty : Bδ.Nonempty := ⟨0, by simpa [Bδ, dist_zero_right] using hδ⟩
  have hBδ_pos : 0 < volume Bδ := IsOpen.measure_pos (μ := volume) isOpen_ball hBδ_nonempty
  have hBδ_ne_zero : volume Bδ ≠ 0 := hBδ_pos.ne'
  have hBδ_ne_top : volume Bδ ≠ ⊤ := by
    have h1 : Bδ ⊆ closedBall (0 : E n) δ := ball_subset_closedBall
    have h2 : volume Bδ ≤ volume (closedBall (0 : E n) δ) := measure_mono h1
    have h3 : volume (closedBall (0 : E n) δ) ≠ ⊤ := (isCompact_closedBall (0 : E n) δ).measure_lt_top.ne
    exact ne_top_of_le_ne_top h3 h2
  have h_ball_vol : volume (ball x δ) = volume Bδ := volume_ball_translate x δ
  have h_sub : A ∩ ball x δ ⊆ ball x δ := by simp
  have h_vol3 : volume (A ∩ ball x δ) ≤ volume Bδ := by
    have h : volume (A ∩ ball x δ) ≤ volume (ball x δ) := measure_mono h_sub
    rw [h_ball_vol] at h; exact h
  have h_finite : ballAverage A δ x ≠ ⊤ :=
    ne_top_of_le_ne_top one_ne_top (by
      dsimp only [ballAverage]
      have h : volume (A ∩ ball x δ) / volume Bδ ≤ volume Bδ / volume Bδ :=
        ENNReal.div_le_div h_vol3 (by rfl)
      have h2 : volume Bδ / volume Bδ = 1 := ENNReal.div_self hBδ_ne_zero hBδ_ne_top
      rw [h2] at h; exact h)
  have h_meas1 : MeasurableSet (A ∩ ball x δ) := hA.inter isOpen_ball.measurableSet
  have h_meas2 : MeasurableSet ((ball x δ) \ A) := isOpen_ball.measurableSet.diff hA
  have h_dis : Disjoint (A ∩ ball x δ) ((ball x δ) \ A) := by
    rw [Set.disjoint_left]
    intro y hy1 hy2
    have h_yinA : y ∈ A := hy1.1
    exact hy2.2 h_yinA
  have h_union : (A ∩ ball x δ) ∪ ((ball x δ) \ A) = ball x δ := by
    ext y; simp [Set.mem_union, Set.mem_diff]; tauto
  have h_add : volume (ball x δ) = volume (A ∩ ball x δ) + volume ((ball x δ) \ A) := by
    have h_union2 : (A ∩ ball x δ) ∪ ((ball x δ) \ A) = ball x δ := h_union
    have h_measure : volume ((A ∩ ball x δ) ∪ ((ball x δ) \ A)) =
        volume (A ∩ ball x δ) + volume ((ball x δ) \ A) := by
      exact measure_union h_dis h_meas2
    rw [h_union2] at h_measure
    exact h_measure
  have h_eq_vol : volume Bδ = volume (A ∩ ball x δ) + volume ((ball x δ) \ A) := by
    rw [← h_ball_vol, h_add]
  by_cases hx : x ∈ A
  · -- x ∈ A
    have h_ind : Set.indicator A (1 : E n → ℝ) x = 1 := by
      simp [Set.indicator_apply, hx]
    have h_set_eq : translateMismatch A x ∩ Bδ = {h | h ∈ Bδ ∧ x + h ∉ A} := by
      ext h; simp [translateMismatch, hx, Set.mem_inter_iff]; tauto
    have h_avg : avgError δ A x = volume ((ball x δ) \ A) / volume Bδ := by
      dsimp only [avgError]; rw [h_set_eq]; rw [volume_mismatch_neg hA x δ]
    have h_le1 : ballAverage A δ x ≤ 1 := by
      dsimp only [ballAverage]
      have h : volume (A ∩ ball x δ) / volume Bδ ≤ volume Bδ / volume Bδ :=
        ENNReal.div_le_div h_vol3 (by rfl)
      have h2 : volume Bδ / volume Bδ = 1 := ENNReal.div_self hBδ_ne_zero hBδ_ne_top
      rw [h2] at h; exact h
    have h_real_le1 : (ballAverage A δ x).toReal ≤ 1 := by
      have h_iff : (ballAverage A δ x).toReal ≤ (1 : ENNReal).toReal ↔ ballAverage A δ x ≤ 1 :=
        ENNReal.toReal_le_toReal h_finite one_ne_top
      exact h_iff.mpr h_le1
    have h_abs : |(ballAverage A δ x).toReal - 1| = 1 - (ballAverage A δ x).toReal := by
      rw [abs_of_nonpos] <;> linarith
    have h9 : ENNReal.ofReal ((ballAverage A δ x).toReal) = ballAverage A δ x :=
      ENNReal.ofReal_toReal h_finite
    have h10 : 0 ≤ (ballAverage A δ x).toReal := by positivity
    have h11 : 0 ≤ 1 - (ballAverage A δ x).toReal := by linarith
    have h_sum_real : (1 - (ballAverage A δ x).toReal) + (ballAverage A δ x).toReal = 1 := by linarith
    have h_ofReal_add : ENNReal.ofReal ((1 - (ballAverage A δ x).toReal) + (ballAverage A δ x).toReal) =
        ENNReal.ofReal (1 - (ballAverage A δ x).toReal) + ENNReal.ofReal ((ballAverage A δ x).toReal) := by
      rw [ENNReal.ofReal_add] <;> linarith
    have h11 : ENNReal.ofReal (1 - (ballAverage A δ x).toReal) + ballAverage A δ x = 1 := by
      have h12 : ENNReal.ofReal (1 - (ballAverage A δ x).toReal) + ENNReal.ofReal ((ballAverage A δ x).toReal) = 1 := by
        rw [← h_ofReal_add, h_sum_real] <;> norm_num
      have h13 : ENNReal.ofReal (1 - (ballAverage A δ x).toReal) + ballAverage A δ x =
          ENNReal.ofReal (1 - (ballAverage A δ x).toReal) + ENNReal.ofReal ((ballAverage A δ x).toReal) := by
        rw [h9]
      rw [h13]
      exact h12
    have h14 : ENNReal.ofReal (1 - (ballAverage A δ x).toReal) ≤ 1 := by
      rw [← h11] <;> exact le_add_right le_rfl
    have h_ofReal : (1 : ENNReal) - ballAverage A δ x =
        ENNReal.ofReal (1 - (ballAverage A δ x).toReal) := by
      have h15 : (ENNReal.ofReal (1 - (ballAverage A δ x).toReal) + ballAverage A δ x) - ballAverage A δ x =
          ENNReal.ofReal (1 - (ballAverage A δ x).toReal) :=
        ENNReal.add_sub_cancel_right h_finite
      rw [h11] at h15
      exact h15
    have h_ba_finite : volume (A ∩ ball x δ) / volume Bδ ≠ ⊤ :=
      ne_top_of_le_ne_top one_ne_top h_le1
    have h_sub : (1 : ENNReal) - ballAverage A δ x = avgError δ A x := by
      dsimp only [ballAverage]
      rw [h_avg]
      have h10 : (1 : ENNReal) = volume Bδ / volume Bδ := by
        rw [ENNReal.div_self hBδ_ne_zero hBδ_ne_top]
      rw [h10]
      have h12 : volume Bδ = volume (A ∩ ball x δ) + volume ((ball x δ) \ A) := h_eq_vol
      have h13 : volume Bδ / volume Bδ =
          (volume (A ∩ ball x δ) + volume ((ball x δ) \ A)) / volume Bδ := by rw [h12]
      rw [h13, ENNReal.add_div]
      exact ENNReal.add_sub_cancel_left h_ba_finite
    rw [h_ind, h_abs, ← h_ofReal, h_sub]
  · -- x ∉ A
    have h_ind : Set.indicator A (1 : E n → ℝ) x = 0 := by
      simp [Set.indicator_apply, hx]
    have h_set_eq : translateMismatch A x ∩ Bδ = {h | h ∈ Bδ ∧ x + h ∈ A} := by
      ext h; simp [translateMismatch, hx, Set.mem_inter_iff]; tauto
    have h_avg : avgError δ A x = volume (A ∩ ball x δ) / volume Bδ := by
      dsimp only [avgError]; rw [h_set_eq]; rw [volume_mismatch_pos hA x δ]
    have h_nonneg : 0 ≤ (ballAverage A δ x).toReal := by positivity
    have h_abs : |(ballAverage A δ x).toReal - 0| = (ballAverage A δ x).toReal := by
      rw [sub_zero, abs_of_nonneg h_nonneg]
    have h_ofReal : ENNReal.ofReal ((ballAverage A δ x).toReal) = ballAverage A δ x :=
      ENNReal.ofReal_toReal h_finite
    rw [h_ind, h_abs, h_ofReal]
    exact Eq.symm h_avg

/-- **Equicontinuity of ball averages.**

For fixed `δ > 0`, the family of functions `{x ↦ ballAverage A δ x | A : Set (E n)}`
is equicontinuous (in fact, uniformly so). The bound is uniform in `A` because
the difference is controlled by the symmetric difference of two balls, which
is independent of `A`. -/
lemma ballAverage_equicontinuous {δ : ℝ} (hδ : 0 < δ) :
    Equicontinuous (fun (A : Set (E n)) => fun (x : E n) => (ballAverage A δ x).toReal) := by
  let V := volume (ball (0 : E n) δ)
  have hV_pos : 0 < V := IsOpen.measure_pos (μ := volume) isOpen_ball
    ⟨(0 : E n), by simpa [dist_zero_right] using hδ⟩
  have hV_ne_zero : V ≠ 0 := hV_pos.ne'
  have hV_ne_top : V ≠ ⊤ := by have h : V < ⊤ := isBounded_ball.measure_lt_top; exact h.ne

  -- Bound: |ba x - ba y| ≤ volume(symmDiff) / V  (real-valued)
  have h_bound : ∀ (A : Set (E n)) (x y : E n),
      |(ballAverage A δ x).toReal - (ballAverage A δ y).toReal| ≤
        ((volume (symmDiff (ball x δ) (ball y δ)) / V).toReal) := by
    intro A x y
    let D1 := volume (ball x δ \ ball y δ)
    let D2 := volume (ball y δ \ ball x δ)
    let SD := volume (symmDiff (ball x δ) (ball y δ))
    have hD1_le : D1 ≤ SD := by apply measure_mono; exact subset_union_left
    have hD2_le : D2 ≤ SD := by apply measure_mono; exact subset_union_right
    have h1 : volume (A ∩ ball x δ) ≤ volume (A ∩ ball y δ) + D1 := by
      have h_sub : A ∩ ball x δ ⊆ (A ∩ ball y δ) ∪ (ball x δ \ ball y δ) := by
        intro z hz; by_cases h : z ∈ ball y δ
        · exact Or.inl ⟨hz.1, h⟩
        · exact Or.inr ⟨hz.2, h⟩
      exact (measure_mono h_sub).trans (measure_union_le _ _)
    have h2 : volume (A ∩ ball y δ) ≤ volume (A ∩ ball x δ) + D2 := by
      have h_sub : A ∩ ball y δ ⊆ (A ∩ ball x δ) ∪ (ball y δ \ ball x δ) := by
        intro z hz; by_cases h : z ∈ ball x δ
        · exact Or.inl ⟨hz.1, h⟩
        · exact Or.inr ⟨hz.2, h⟩
      exact (measure_mono h_sub).trans (measure_union_le _ _)
    have hba_le1 : ∀ (z : E n), ballAverage A δ z ≤ 1 := by
      intro z; dsimp only [ballAverage]
      have h_sub : A ∩ ball z δ ⊆ ball z δ := by simp
      have h_vol : volume (A ∩ ball z δ) ≤ volume (ball z δ) := measure_mono h_sub
      have h_vol2 : volume (ball z δ) = V := volume_ball_translate z δ
      have h : volume (A ∩ ball z δ) / V ≤ volume (ball z δ) / V := ENNReal.div_le_div h_vol (by rfl)
      rw [h_vol2] at h
      have h3 : V / V = 1 := ENNReal.div_self hV_ne_zero hV_ne_top
      rw [h3] at h; exact h
    have hba_finite : ∀ (z : E n), ballAverage A δ z ≠ ⊤ := by
      intro z; exact ne_top_of_le_ne_top one_ne_top (hba_le1 z)
    have hD1_le_V : D1 ≤ V := by
      have h : ball x δ \ ball y δ ⊆ ball x δ := by simp
      have h' : volume (ball x δ \ ball y δ) ≤ volume (ball x δ) := measure_mono h
      rw [volume_ball_translate x δ] at h'
      exact h'
    have hD2_le_V : D2 ≤ V := by
      have h : ball y δ \ ball x δ ⊆ ball y δ := by simp
      have h' : volume (ball y δ \ ball x δ) ≤ volume (ball y δ) := measure_mono h
      rw [volume_ball_translate y δ] at h'
      exact h'
    have hD1_ne_top : D1 ≠ ⊤ := ne_top_of_le_ne_top hV_ne_top hD1_le_V
    have hD2_ne_top : D2 ≠ ⊤ := ne_top_of_le_ne_top hV_ne_top hD2_le_V
    have hSD_le_2V : SD ≤ 2 * V := by
      have h_union : SD ≤ volume (ball x δ ∪ ball y δ) := by
        have h_sub : symmDiff (ball x δ) (ball y δ) ⊆ ball x δ ∪ ball y δ := by
          intro z hz
          simp only [symmDiff, Set.mem_union, Set.mem_diff] at hz
          rcases hz with (h | h)
          · exact Or.inl h.1
          · exact Or.inr h.1
        exact measure_mono h_sub
      have h_vol_union : volume (ball x δ ∪ ball y δ) ≤ volume (ball x δ) + volume (ball y δ) :=
        measure_union_le _ _
      rw [volume_ball_translate x δ, volume_ball_translate y δ] at h_vol_union
      exact h_union.trans (by simpa [two_mul] using h_vol_union)
    have h2V_ne_top : (2 : ENNReal) * V ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) hV_ne_top
    have hSD_ne_top : SD ≠ ⊤ := ne_top_of_le_ne_top h2V_ne_top hSD_le_2V
    have h_div1_ne_top : D1 / V ≠ ⊤ := div_ne_top hD1_ne_top hV_ne_zero
    have h_div2_ne_top : D2 / V ≠ ⊤ := div_ne_top hD2_ne_top hV_ne_zero
    have h_ineq1 : ballAverage A δ x ≤ ballAverage A δ y + D1 / V := by
      dsimp only [ballAverage]
      have h : volume (A ∩ ball x δ) / V ≤ (volume (A ∩ ball y δ) + D1) / V :=
        ENNReal.div_le_div h1 (by rfl)
      rw [ENNReal.add_div] at h; exact h
    have h_ineq2 : ballAverage A δ y ≤ ballAverage A δ x + D2 / V := by
      dsimp only [ballAverage]
      have h : volume (A ∩ ball y δ) / V ≤ (volume (A ∩ ball x δ) + D2) / V :=
        ENNReal.div_le_div h2 (by rfl)
      rw [ENNReal.add_div] at h; exact h
    have h_add1_ne_top : ballAverage A δ y + D1 / V ≠ ⊤ :=
      add_ne_top.mpr ⟨hba_finite y, h_div1_ne_top⟩
    have h_add2_ne_top : ballAverage A δ x + D2 / V ≠ ⊤ :=
      add_ne_top.mpr ⟨hba_finite x, h_div2_ne_top⟩
    have h_real1 : (ballAverage A δ x).toReal ≤ (ballAverage A δ y).toReal + (D1 / V).toReal := by
      have h_add : (ballAverage A δ y + D1 / V).toReal = (ballAverage A δ y).toReal + (D1 / V).toReal :=
        ENNReal.toReal_add (hba_finite y) h_div1_ne_top
      have h_iff : (ballAverage A δ x).toReal ≤ (ballAverage A δ y + D1 / V).toReal ↔
          ballAverage A δ x ≤ ballAverage A δ y + D1 / V :=
        ENNReal.toReal_le_toReal (hba_finite x) h_add1_ne_top
      rw [h_add] at h_iff; exact h_iff.mpr h_ineq1
    have h_real2 : (ballAverage A δ y).toReal ≤ (ballAverage A δ x).toReal + (D2 / V).toReal := by
      have h_add : (ballAverage A δ x + D2 / V).toReal = (ballAverage A δ x).toReal + (D2 / V).toReal :=
        ENNReal.toReal_add (hba_finite x) h_div2_ne_top
      have h_iff : (ballAverage A δ y).toReal ≤ (ballAverage A δ x + D2 / V).toReal ↔
          ballAverage A δ y ≤ ballAverage A δ x + D2 / V :=
        ENNReal.toReal_le_toReal (hba_finite y) h_add2_ne_top
      rw [h_add] at h_iff; exact h_iff.mpr h_ineq2
    have hD1_real_le : (D1 / V).toReal ≤ (SD / V).toReal :=
      (ENNReal.toReal_le_toReal (div_ne_top hD1_ne_top hV_ne_zero)
        (div_ne_top hSD_ne_top hV_ne_zero)).mpr (ENNReal.div_le_div hD1_le (by rfl))
    have hD2_real_le : (D2 / V).toReal ≤ (SD / V).toReal :=
      (ENNReal.toReal_le_toReal (div_ne_top hD2_ne_top hV_ne_zero)
        (div_ne_top hSD_ne_top hV_ne_zero)).mpr (ENNReal.div_le_div hD2_le (by rfl))
    have h_abs1 : (ballAverage A δ x).toReal - (ballAverage A δ y).toReal ≤ (SD / V).toReal := by
      have h : (ballAverage A δ x).toReal - (ballAverage A δ y).toReal ≤ (D1 / V).toReal := by
        linarith [h_real1]
      linarith [hD1_real_le]
    have h_abs2 : (ballAverage A δ y).toReal - (ballAverage A δ x).toReal ≤ (SD / V).toReal := by
      have h : (ballAverage A δ y).toReal - (ballAverage A δ x).toReal ≤ (D2 / V).toReal := by
        linarith [h_real2]
      linarith [hD2_real_le]
    exact abs_le.mpr ⟨by linarith, h_abs1⟩

  -- Symmetric difference bounded by annulus
  have h_symm : ∀ (x y : E n) (η : ℝ), 0 < η → η < δ → dist x y < η →
      volume (symmDiff (ball x δ) (ball y δ)) ≤
        2 * volume (ball (0 : E n) δ \ ball (0 : E n) (δ - η)) := by
    intro x y η hη_pos hη_lt h_dist
    have h1 : ball x δ \ ball y δ ⊆ ball x δ \ ball x (δ - η) := by
      intro z hz
      have h_contra : z ∉ ball x (δ - η) := by
        intro h
        have h_dist_zx : dist z x < δ - η := by simpa [Metric.mem_ball] using h
        have h4 : dist z y < δ := by
          have h_sum : dist z y ≤ dist z x + dist x y := dist_triangle _ _ _
          have h5 : dist z x + dist x y < (δ - η) + η := add_lt_add h_dist_zx h_dist
          have h6 : (δ - η) + η = δ := by ring
          rw [h6] at h5
          exact lt_of_le_of_lt h_sum h5
        exact hz.2 (by simpa [Metric.mem_ball] using h4)
      exact ⟨hz.1, h_contra⟩
    have h2 : ball y δ \ ball x δ ⊆ ball y δ \ ball y (δ - η) := by
      intro z hz
      have h_contra : z ∉ ball y (δ - η) := by
        intro h
        have h_dist_zy : dist z y < δ - η := by simpa [Metric.mem_ball] using h
        have h4 : dist z x < δ := by
          have h_sum : dist z x ≤ dist z y + dist y x := dist_triangle _ _ _
          have h5 : dist z y + dist y x < (δ - η) + η := add_lt_add h_dist_zy (by rwa [dist_comm] at h_dist)
          have h6 : (δ - η) + η = δ := by ring
          rw [h6] at h5
          exact lt_of_le_of_lt h_sum h5
        exact hz.2 (by simpa [Metric.mem_ball] using h4)
      exact ⟨hz.1, h_contra⟩
    have h3 : volume (ball x δ \ ball x (δ - η)) = volume (ball (0 : E n) δ \ ball (0 : E n) (δ - η)) := by
      have h_eq : ball x δ \ ball x (δ - η) =
          (fun z : E n => z - x) ⁻¹' (ball (0 : E n) δ \ ball (0 : E n) (δ - η)) := by
        ext z; simp [Metric.mem_ball, dist_eq_norm] <;> abel
      rw [h_eq]
      have h_trans : (fun z : E n => z - x) = fun z => (-x) + z := by funext z; abel
      rw [h_trans]; exact MeasureTheory.measure_preimage_add volume (-x) _
    have h4 : volume (ball y δ \ ball y (δ - η)) = volume (ball (0 : E n) δ \ ball (0 : E n) (δ - η)) := by
      have h_eq : ball y δ \ ball y (δ - η) =
          (fun z : E n => z - y) ⁻¹' (ball (0 : E n) δ \ ball (0 : E n) (δ - η)) := by
        ext z; simp [Metric.mem_ball, dist_eq_norm] <;> abel
      rw [h_eq]
      have h_trans : (fun z : E n => z - y) = fun z => (-y) + z := by funext z; abel
      rw [h_trans]; exact MeasureTheory.measure_preimage_add volume (-y) _
    calc volume (symmDiff (ball x δ) (ball y δ))
      ≤ volume (ball x δ \ ball y δ) + volume (ball y δ \ ball x δ) := measure_union_le _ _
      _ ≤ volume (ball x δ \ ball x (δ - η)) + volume (ball y δ \ ball y (δ - η)) := by gcongr
      _ = 2 * volume (ball (0 : E n) δ \ ball (0 : E n) (δ - η)) := by rw [h3, h4] <;> ring

  -- Annulus volume tends to 0 via continuity from above
  let S : ℕ → Set (E n) := fun k =>
    ball (0 : E n) δ \ ball (0 : E n) (δ - 1 / (k + 1 : ℝ))
  have hS_antitone : Antitone S := by
    intro k l hkl
    have h1 : (1 : ℝ) / (l + 1) ≤ 1 / (k + 1) := by gcongr <;> omega
    have h3 : ball (0 : E n) (δ - 1 / (l + 1 : ℝ)) ⊇ ball (0 : E n) (δ - 1 / (k + 1 : ℝ)) := by
      intro z hz
      have h4 : dist z (0 : E n) < δ - 1 / (k + 1 : ℝ) := by simpa [Metric.mem_ball] using hz
      have h5 : dist z (0 : E n) < δ - 1 / (l + 1 : ℝ) := by linarith
      simpa [Metric.mem_ball] using h5
    exact diff_subset_diff_right h3
  have hS_meas : ∀ k, NullMeasurableSet (S k) := by
    intro k; exact (isOpen_ball.measurableSet.diff isOpen_ball.measurableSet).nullMeasurableSet
  have hS0_sub : S 0 ⊆ ball (0 : E n) δ := by
    intro z hz; exact hz.1
  have hS0_le : volume (S 0) ≤ V := measure_mono hS0_sub
  have hS_fin : ∃ k, volume (S k) ≠ ⊤ := ⟨0, ne_top_of_le_ne_top hV_ne_top hS0_le⟩
  have hS_inter_empty : (⋂ k, S k) = ∅ := by
    ext x
    simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false]
    intro h
    by_cases hxin : x ∈ ball (0 : E n) δ
    · have hdist : dist x (0 : E n) < δ := by simpa [Metric.mem_ball] using hxin
      have hpos : 0 < δ - dist x (0 : E n) := by linarith
      have h_exists_k : ∃ k : ℕ, (1 : ℝ) / (k + 1) < δ - dist x (0 : E n) := by
        let ε' := δ - dist x (0 : E n)
        refine ⟨Nat.ceil (1 / ε'), ?_⟩
        have h7 : (Nat.ceil (1 / ε') + 1 : ℝ) > 1 / ε' := by
          have h8 : (1 : ℝ) / ε' ≤ Nat.ceil (1 / ε') := Nat.le_ceil _
          linarith
        calc (1 : ℝ) / (Nat.ceil (1 / ε') + 1)
          < (1 : ℝ) / (1 / ε') := by gcongr <;> linarith
        _ = ε' := by field_simp [hpos.ne'] <;> ring
      rcases h_exists_k with ⟨k, hk⟩
      have h6 : dist x (0 : E n) < δ - 1 / (k + 1 : ℝ) := by linarith
      have h7 : x ∈ ball (0 : E n) (δ - 1 / (k + 1 : ℝ)) := by simpa [Metric.mem_ball] using h6
      have h8 : x ∉ S k := by
        simp only [S, Set.mem_diff]
        intro h9
        exact h9.2 h7
      exact h8 (h k)
    · have h9 : x ∉ S 0 := by
        simp only [S, Set.mem_diff]
        intro h10; exact hxin h10.1
      exact h9 (h 0)
  have h_tendsto : Tendsto (fun k => volume (S k)) atTop (nhds 0) := by
    have h := MeasureTheory.tendsto_measure_iInter_atTop hS_meas hS_antitone hS_fin
    rw [hS_inter_empty] at h
    simpa [Function.comp_def] using h

  -- For any ε > 0, find η > 0 with 2 * annulusVol(η) / V < ofReal ε
  have h_annulus : ∀ (ε : ℝ), 0 < ε → ∃ (η : ℝ), 0 < η ∧ η < δ ∧
      2 * volume (ball (0 : E n) δ \ ball (0 : E n) (δ - η)) / V < ENNReal.ofReal ε := by
    intro ε hε
    have h_ofReal_pos : 0 < ENNReal.ofReal ε := ENNReal.ofReal_pos.mpr hε
    have h_mul_ne_zero : ENNReal.ofReal ε * V ≠ 0 := mul_ne_zero h_ofReal_pos.ne' hV_pos.ne'
    let half_target := (ENNReal.ofReal ε * V) / 2
    have h_half_pos : 0 < half_target := by
      have h4 : half_target ≠ 0 := ENNReal.div_ne_zero.mpr ⟨h_mul_ne_zero, by norm_num⟩
      exact lt_of_le_of_ne (by simp) h4.symm
    have h_event : ∀ᶠ k in atTop, volume (S k) < half_target :=
      h_tendsto (Iio_mem_nhds h_half_pos)
    rcases Filter.eventually_atTop.mp h_event with ⟨N0, hN0⟩
    let N := max N0 (Nat.ceil (1 / δ))
    have hN_ge : N ≥ N0 := le_max_left _ _
    have hN_ltδ : (1 : ℝ) / (N + 1) < δ := by
      have h1 : N ≥ Nat.ceil (1 / δ) := le_max_right _ _
      have h2 : (N + 1 : ℝ) > 1 / δ := by
        have h3 : (Nat.ceil (1 / δ) : ℝ) ≥ 1 / δ := Nat.le_ceil _
        have h4 : (N : ℝ) ≥ Nat.ceil (1 / δ) := by exact_mod_cast h1
        linarith
      have h4 : (1 : ℝ) / (N + 1) < 1 / (1 / δ) := by gcongr <;> linarith
      have h5 : (1 : ℝ) / (1 / δ) = δ := by
        field_simp [hδ.ne'] <;> ring
      rw [h5] at h4
      exact h4
    have hk1 : volume (S N) < half_target := hN0 N hN_ge
    have hSN_le_V : volume (S N) ≤ V := by
      have h_sub : S N ⊆ S 0 := hS_antitone (by linarith)
      exact (measure_mono h_sub).trans hS0_le
    have h_target_ne_top : (ENNReal.ofReal ε * V) ≠ ⊤ :=
      ENNReal.mul_ne_top (by simp) hV_ne_top
    have h_half_ne_top : half_target ≠ ⊤ := div_ne_top h_target_ne_top (by norm_num)
    have h_mul_lt : 2 * volume (S N) < 2 * half_target := by
      have h_eq1 : ∀ (a : ENNReal), 2 * a = a / (1 / 2 : ENNReal) := by
        intro a
        have h_inv : ((1 / 2 : ENNReal)⁻¹) = (2 : ENNReal) := by norm_num
        have h_div : a / (1 / 2 : ENNReal) = a * ((1 / 2 : ENNReal)⁻¹) := by
          rw [div_eq_mul_inv]
        rw [h_div, h_inv, mul_comm]
      rw [h_eq1 (volume (S N)), h_eq1 half_target]
      exact ENNReal.div_lt_div_right (by norm_num) (by norm_num) hk1
    have h_double : 2 * half_target = ENNReal.ofReal ε * V := by
      dsimp only [half_target]
      rw [div_eq_mul_inv]
      have h4 : (2 : ENNReal) * ((ENNReal.ofReal ε * V) * (2 : ENNReal)⁻¹) =
          (ENNReal.ofReal ε * V) * ((2 : ENNReal) * (2 : ENNReal)⁻¹) := by
        rw [mul_left_comm]
      rw [h4]
      have h5 : (2 : ENNReal) * (2 : ENNReal)⁻¹ = 1 := by
        exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
      rw [h5, mul_one]
    have hk2 : 2 * volume (S N) < ENNReal.ofReal ε * V := by
      rw [h_double] at h_mul_lt
      exact h_mul_lt
    have h10 : 2 * volume (S N) / V < (ENNReal.ofReal ε * V) / V :=
      ENNReal.div_lt_div_right hV_ne_zero hV_ne_top hk2
    have h11 : (ENNReal.ofReal ε * V) / V = ENNReal.ofReal ε := by
      rw [mul_div_assoc, ENNReal.div_self hV_ne_zero hV_ne_top, mul_one]
    rw [h11] at h10
    refine ⟨1 / (N + 1 : ℝ), by positivity, hN_ltδ, ?_⟩
    simpa [S] using h10

  -- Combine
  have h_main : ∀ (x0 : E n), EquicontinuousAt (fun (A : Set (E n)) => fun (x : E n) => (ballAverage A δ x).toReal) x0 := by
    intro x0
    rw [Metric.equicontinuousAt_iff_pair]
    intro ε hε
    rcases h_annulus ε hε with ⟨η, hη_pos, hη_lt, hη_choice⟩
    refine ⟨ball x0 (η / 2), Metric.ball_mem_nhds x0 (by linarith), ?_⟩
    intro x hx y hy A
    have h_dist : dist x y < η := by
      have hx' : dist x x0 < η / 2 := by simpa [Metric.mem_ball] using hx
      have hy' : dist x0 y < η / 2 := by
        rw [dist_comm]
        simpa [Metric.mem_ball] using hy
      calc dist x y ≤ dist x x0 + dist x0 y := dist_triangle _ _ _
        _ < η / 2 + η / 2 := by linarith
        _ = η := by ring
    have h1 : volume (symmDiff (ball x δ) (ball y δ)) ≤
        2 * volume (ball (0 : E n) δ \ ball (0 : E n) (δ - η)) := h_symm x y η hη_pos hη_lt h_dist
    have h2 : volume (symmDiff (ball x δ) (ball y δ)) / V < ENNReal.ofReal ε := by
      calc volume (symmDiff (ball x δ) (ball y δ)) / V
        ≤ (2 * volume (ball (0 : E n) δ \ ball (0 : E n) (δ - η))) / V := ENNReal.div_le_div h1 (by rfl)
        _ < ENNReal.ofReal ε := hη_choice
    have h_bdd1 : Bornology.IsBounded (ball x δ) := Metric.isBounded_ball
    have h_bdd2 : Bornology.IsBounded (ball y δ) := Metric.isBounded_ball
    have h_bdd : Bornology.IsBounded (ball x δ ∪ ball y δ) := h_bdd1.union h_bdd2
    have h_vol_ne_top : volume (ball x δ ∪ ball y δ) ≠ ⊤ := h_bdd.measure_lt_top.ne
    have h_sub : symmDiff (ball x δ) (ball y δ) ⊆ ball x δ ∪ ball y δ := by
      intro z hz
      simp only [symmDiff, Set.mem_union, Set.mem_diff] at hz
      rcases hz with (h | h)
      · exact Or.inl h.1
      · exact Or.inr h.1
    have hSD_ne_top : volume (symmDiff (ball x δ) (ball y δ)) ≠ ⊤ :=
      ne_top_of_le_ne_top h_vol_ne_top (measure_mono h_sub)
    have h3 : ((volume (symmDiff (ball x δ) (ball y δ)) / V).toReal) < ε := by
      have h4 : ((volume (symmDiff (ball x δ) (ball y δ)) / V).toReal) < (ENNReal.ofReal ε).toReal :=
        (ENNReal.toReal_lt_toReal (div_ne_top hSD_ne_top hV_ne_zero) (by simp)).mpr h2
      have h5 : (ENNReal.ofReal ε).toReal = ε := ENNReal.toReal_ofReal (by linarith)
      rw [h5] at h4
      exact h4
    have h5 : |(ballAverage A δ x).toReal - (ballAverage A δ y).toReal| ≤
        ((volume (symmDiff (ball x δ) (ball y δ)) / V).toReal) := h_bound A x y
    calc |(ballAverage A δ x).toReal - (ballAverage A δ y).toReal|
      ≤ ((volume (symmDiff (ball x δ) (ball y δ)) / V).toReal) := h5
    _ < ε := h3
  exact h_main
/-- Arzelà-Ascoli extraction. -/
lemma arzela_ascoli_sequence {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (f : ℕ → (X → ℝ))
    (h_bounded : ∀ k x, f k x ∈ Icc (0 : ℝ) 1)
    (h_eqcont : Equicontinuous f) :
    ∃ (subseq : ℕ → ℕ) (g : X → ℝ),
      StrictMono subseq ∧ Continuous g ∧
      Tendsto (fun k => f (subseq k)) atTop (nhds g) := by
  let F : ℕ → BoundedContinuousFunction X ℝ := fun k =>
    BoundedContinuousFunction.mkOfCompact ⟨f k, h_eqcont.continuous k⟩
  let A : Set (BoundedContinuousFunction X ℝ) := Set.range F
  have hF_apply : ∀ k x, F k x = f k x := by
    intro k x; simp [F, BoundedContinuousFunction.mkOfCompact_apply]
  have h_in_s : ∀ (g : BoundedContinuousFunction X ℝ) (x : X),
      g ∈ A → g x ∈ Icc (0 : ℝ) 1 := by
    intro g x hg
    rcases (Set.mem_range.1 hg) with ⟨k, rfl⟩
    rw [hF_apply k x]
    exact h_bounded k x
  choose u hu using fun (a : A) => show ∃ k : ℕ, F k = (a : BoundedContinuousFunction X ℝ) by
    exact Set.mem_range.1 a.prop
  have hA_eqcont : Equicontinuous ((↑) : A → X → ℝ) := by
    have h1 : ((↑) : A → X → ℝ) = f ∘ u := by
      funext a; ext x
      have h2 : F (u a) = (a : BoundedContinuousFunction X ℝ) := hu a
      have h3 : (F (u a) : X → ℝ) x = ((a : BoundedContinuousFunction X ℝ) : X → ℝ) x := by
        rw [h2]
      exact Eq.symm (by simpa [hF_apply] using h3)
    rw [h1]
    exact h_eqcont.comp u
  have h_compact : IsCompact (closure A) :=
    BoundedContinuousFunction.arzela_ascoli (Icc (0 : ℝ) 1) isCompact_Icc A h_in_s hA_eqcont
  have h_seq_in : ∀ k, F k ∈ closure A := by
    intro k
    apply subset_closure
    exact Set.mem_range_self k
  have h_first : FirstCountableTopology (BoundedContinuousFunction X ℝ) :=
    UniformSpace.firstCountableTopology (BoundedContinuousFunction X ℝ)
  rcases h_compact.tendsto_subseq h_seq_in with ⟨g, hg_in, subseq, hsub_strict, h_tendsto⟩
  have h_uniform : TendstoUniformly (fun k => (F (subseq k) : X → ℝ)) (g : X → ℝ) atTop :=
    (BoundedContinuousFunction.tendsto_iff_tendstoUniformly).mp h_tendsto
  have h_pointwise : ∀ (x : X), Tendsto (fun k => f (subseq k) x) atTop (nhds (g x)) := by
    intro x
    have h4 : (fun k => f (subseq k) x) = fun k => (F (subseq k) : X → ℝ) x := by
      funext k; rw [hF_apply (subseq k) x]
    rw [h4]
    exact h_uniform.tendsto_at x
  have h_tendsto_pi : Tendsto (fun k => f (subseq k)) atTop (nhds (g : X → ℝ)) := by
    rw [tendsto_pi_nhds]
    exact h_pointwise
  exact ⟨subseq, g, hsub_strict, g.continuous, h_tendsto_pi⟩

/-- Arzelà-Ascoli extraction on a compact subset. -/
lemma arzelaAscoliOn_extraction {X : Type*} [TopologicalSpace X]
    (K : Set X) (hK : IsCompact K)
    (f : ℕ → (X → ℝ))
    (h_bounded : ∀ k x, x ∈ K → f k x ∈ Icc (0 : ℝ) 1)
    (h_cont : ∀ k, ContinuousOn (f k) K)
    (h_eqcont : EquicontinuousOn f K) :
    ∃ (subseq : ℕ → ℕ) (g : X → ℝ),
      StrictMono subseq ∧ ContinuousOn g K ∧
      ∀ x ∈ K, Tendsto (fun k => f (subseq k) x) atTop (nhds (g x)) := by
  let K' : Type _ := {x : X // x ∈ K}
  letI : CompactSpace K' := isCompact_iff_compactSpace.1 hK
  let f' : ℕ → (K' → ℝ) := fun k x' => f k x'.val
  have h_bounded' : ∀ k (x' : K'), f' k x' ∈ Icc (0 : ℝ) 1 := by
    intro k x'; exact h_bounded k x'.val x'.property
  have h_eqcont' : Equicontinuous f' :=
    (equicontinuous_restrict_iff f).mpr h_eqcont
  rcases arzela_ascoli_sequence f' h_bounded' h_eqcont' with ⟨subseq, g', hsub_strict, hg_cont, hg_tendsto⟩
  classical
  let g : X → ℝ := fun x => if h : x ∈ K then g' ⟨x, h⟩ else 0
  have hg_contOn : ContinuousOn g K := by
    rw [continuousOn_iff_continuous_restrict]
    have h1 : Set.restrict K g = g' := by
      funext x'; simp [g, x'.property]
    exact h1 ▸ hg_cont
  have h_conv : ∀ x ∈ K, Tendsto (fun k => f (subseq k) x) atTop (nhds (g x)) := by
    intro x hx
    have h5 : g x = g' ⟨x, hx⟩ := by
      simp [g, hx]
    rw [h5]
    have h6 : Tendsto (fun k => f' (subseq k) ⟨x, hx⟩) atTop (nhds (g' ⟨x, hx⟩)) := by
      have h7 := (tendsto_pi_nhds.mp hg_tendsto) ⟨x, hx⟩
      exact h7
    simpa [f'] using h6
  exact ⟨subseq, g, hsub_strict, hg_contOn, h_conv⟩

/-- Diagonal extraction over countably many compact sets and scales. -/
lemma diagonal_extraction (f : ℕ → ℕ → (E n → ℝ))
    (K : ℕ → Set (E n)) (hK : ∀ j, IsCompact (K j))
    (h_bounded : ∀ k m x, 0 ≤ f k m x ∧ f k m x ≤ 1)
    (h_cont : ∀ k m, Continuous (f k m))
    (h_eqcont : ∀ j m, EquicontinuousOn (fun k => f k m) (K j)) :
    ∃ (subseq : ℕ → ℕ), StrictMono subseq ∧
      ∀ (j m : ℕ), ∃ (g : E n → ℝ), ContinuousOn g (K j) ∧
        ∀ x ∈ K j, Tendsto (fun l => f (subseq l) m x) atTop (nhds (g x)) := by
  let h_exists_prop : (ℕ → ℕ) → ℕ → Prop := fun σ_i i =>
    let j := (Nat.unpair i).1
    let m := (Nat.unpair i).2
    ∃ (p : (ℕ → ℕ) × (E n → ℝ)),
      StrictMono p.1 ∧ ContinuousOn p.2 (K j) ∧
      ∀ x ∈ K j, Tendsto (fun k => f (σ_i (p.1 k)) m x) atTop (nhds (p.2 x))
  have h_exists : ∀ (σ_i : ℕ → ℕ) (i : ℕ), h_exists_prop σ_i i := by
    intro σ_i i
    dsimp only [h_exists_prop]
    let j := (Nat.unpair i).1
    let m := (Nat.unpair i).2
    rcases arzelaAscoliOn_extraction (K j) (hK j) (fun k => f (σ_i k) m)
      (fun k x _ => let h := h_bounded (σ_i k) m x; ⟨h.1, h.2⟩)
      (fun k => (h_cont (σ_i k) m).continuousOn)
      ((h_eqcont j m).comp σ_i) with ⟨τ, g, hτ, hg, hconv⟩
    exact ⟨(τ, g), hτ, hg, hconv⟩
  let extract : (ℕ → ℕ) → ℕ → (ℕ → ℕ) × (E n → ℝ) := fun σ_i i =>
    Classical.choose (h_exists σ_i i)
  have extract_spec : ∀ (σ_i : ℕ → ℕ) (i : ℕ),
      StrictMono (extract σ_i i).1 ∧
      ContinuousOn (extract σ_i i).2 (K (Nat.unpair i).1) ∧
      ∀ x ∈ K (Nat.unpair i).1,
        Tendsto (fun k => f (σ_i ((extract σ_i i).1 k)) (Nat.unpair i).2 x) atTop
          (nhds ((extract σ_i i).2 x)) := by
    intro σ_i i
    exact Classical.choose_spec (h_exists σ_i i)
  let P : ℕ → ((ℕ → ℕ) × ((ℕ → ℕ) × (E n → ℝ))) :=
    Nat.rec (id, (id, fun _ => 0)) fun i prev =>
      let σ_i := prev.1
      let (τ_i, g_i) := extract σ_i i
      (σ_i ∘ τ_i, (τ_i, g_i))
  let σ : ℕ → (ℕ → ℕ) := fun i => (P i).1
  let τ : ℕ → (ℕ → ℕ) := fun i => (P (i + 1)).2.1
  let g : ℕ → (E n → ℝ) := fun i => (P (i + 1)).2.2
  have hσ_succ : ∀ i, σ (i + 1) = σ i ∘ τ i := by
    intro i; simp [σ, τ, g, P]
  have hτ_strict : ∀ i, StrictMono (τ i) := by
    intro i; exact (extract_spec (σ i) i).1
  have hg_spec : ∀ i,
      ContinuousOn (g i) (K (Nat.unpair i).1) ∧
      ∀ x ∈ K (Nat.unpair i).1,
        Tendsto (fun k => f (σ (i + 1) k) (Nat.unpair i).2 x) atTop
          (nhds ((g i) x)) := by
    intro i
    have h := extract_spec (σ i) i
    have h2 : σ (i + 1) = σ i ∘ τ i := hσ_succ i
    rw [h2]; exact h.2
  let d : ℕ → ℕ := fun n => σ (n + 1) n
  have hσ_strict : ∀ i, StrictMono (σ i) := by
    intro i; induction i with
    | zero => exact strictMono_id
    | succ i ih => rw [hσ_succ i]; exact ih.comp (hτ_strict i)
  have h_strictMono_nat_ge : ∀ {ρ : ℕ → ℕ}, StrictMono ρ → ∀ n, n ≤ ρ n := by
    intro ρ hρ n; induction n with
    | zero => exact Nat.zero_le _
    | succ n ih => have h1 : ρ n < ρ (n + 1) := hρ n.lt_succ_self; omega
  have hd_strict : StrictMono d := by
    have h_succ : ∀ n, d n < d (n + 1) := by
      intro n; dsimp only [d]
      have h2 : σ (n + 2) = σ (n + 1) ∘ τ (n + 1) := hσ_succ (n + 1)
      rw [h2]
      have h4 : n + 1 ≤ τ (n + 1) (n + 1) := h_strictMono_nat_ge (hτ_strict (n + 1)) (n + 1)
      have h5 : n < τ (n + 1) (n + 1) := by omega
      exact (hσ_strict (n + 1)) h5
    intro n m hnm
    induction' hnm with m hnm ih
    · exact h_succ n
    · exact lt_trans ih (h_succ m)
  have h_factor : ∀ (i l : ℕ), i ≤ l → ∃ (ρ : ℕ → ℕ), StrictMono ρ ∧ σ (l + 1) = σ (i + 1) ∘ ρ := by
    intro i l hile
    induction' hile with l hile ih
    · refine ⟨id, strictMono_id, by rfl⟩
    · rcases ih with ⟨ρ, hρ_strict, hρ_eq⟩
      refine ⟨ρ ∘ τ (l + 1), hρ_strict.comp (hτ_strict (l + 1)), ?_⟩
      rw [hσ_succ (l + 1), hρ_eq] <;> rfl
  refine ⟨d, hd_strict, ?_⟩
  intro j m
  let i : ℕ := Nat.pair j m
  have h_unpair : Nat.unpair i = (j, m) := Nat.unpair_pair j m
  have h_main_i := hg_spec i
  have h_j : (Nat.unpair i).1 = j := by rw [h_unpair] <;> rfl
  have h_m : (Nat.unpair i).2 = m := by rw [h_unpair] <;> rfl
  rcases h_main_i with ⟨hg_contOn, h_tendsto_i⟩
  rw [h_j] at hg_contOn; rw [h_j, h_m] at h_tendsto_i
  choose ρ hρ_strict hρ_eq using h_factor i
  let a : ℕ → ℕ := fun l => if h : i ≤ l then (ρ l h) l else 0
  have ha_tendsto : Tendsto a atTop atTop := by
    apply Filter.tendsto_atTop_atTop.mpr; intro b
    refine ⟨max b i, fun l hl => ?_⟩
    have h_i : i ≤ l := by have h : max b i ≤ l := hl; exact le_trans (le_max_right b i) h
    have h_b : b ≤ l := by have h : max b i ≤ l := hl; exact le_trans (le_max_left b i) h
    have h1 : a l = (ρ l h_i) l := by simp [a, h_i] <;> rfl
    rw [h1]
    have h2 : l ≤ (ρ l h_i) l := h_strictMono_nat_ge (hρ_strict l h_i) l
    linarith
  have h_d_eq : ∀ l, i ≤ l → d l = σ (i + 1) (a l) := by
    intro l hl; dsimp only [d, a]; rw [dif_pos hl]
    have h3 : σ (l + 1) = σ (i + 1) ∘ ρ l hl := hρ_eq l hl
    rw [h3] <;> rfl
  have h_final : ∀ x ∈ K j, Tendsto (fun l => f (d l) m x) atTop (nhds (g i x)) := by
    intro x hx
    have h4 : ∀ᶠ l in atTop, i ≤ l := Filter.eventually_ge_atTop i
    have h5 : Tendsto (fun l => f (σ (i + 1) (a l)) m x) atTop (nhds (g i x)) :=
      (h_tendsto_i x hx).comp ha_tendsto
    exact h5.congr' (h4.mono fun l hl => by
      have h_eq : f (σ (i + 1) (a l)) m x = f (d l) m x := by rw [h_d_eq l hl]
      exact h_eq)
  exact ⟨g i, hg_contOn, h_final⟩

/-- L^1 approximation error of ball average: ≤ C*δ.

Requires `Kδ` to contain the `δ`-neighborhood of `K`, so that `K + h ⊆ Kδ`
for all `‖h‖ < δ`. -/
lemma avgError_lintegral_bound {A : Set (E n)} (hA : MeasurableSet A)
    {K : Set (E n)} (hK : MeasurableSet K) (δ : ℝ) (hδ : 0 < δ)
    (C : ℝ) (hC : 0 ≤ C)
    (Kδ : Set (E n)) (hKδ : ∀ (x : E n), x ∈ K → ∀ (h : E n), ‖h‖ < δ → x + h ∈ Kδ)
    (h_trans : ∀ (h : E n),
      volume (symmDiff A ((fun x => x + h) '' A) ∩ Kδ) ≤ ENNReal.ofReal (C * ‖h‖)) :
    ∫⁻ x in K, avgError δ A x ≤ ENNReal.ofReal (C * δ) := by
  classical
  let Bδ := ball (0 : E n) δ
  have hBδ_meas : MeasurableSet Bδ := isOpen_ball.measurableSet
  have hBδ_nonempty : (Bδ).Nonempty := ⟨0, by simpa [Bδ, dist_zero_right] using hδ⟩
  have hBδ_pos : 0 < volume Bδ := IsOpen.measure_pos (μ := volume) isOpen_ball hBδ_nonempty
  have hBδ_ne_zero : volume Bδ ≠ 0 := hBδ_pos.ne'
  have hBδ_ne_top : volume Bδ ≠ ⊤ := by
    have h : volume Bδ < ⊤ := isBounded_ball.measure_lt_top
    exact h.ne
  let S_prod : Set (E n × E n) :=
    {p | p.1 ∈ K ∧ p.2 ∈ Bδ ∧ (p.1 ∈ A ↔ p.1 + p.2 ∉ A)}
  have h1_meas : MeasurableSet {p : E n × E n | p.1 ∈ K} := hK.preimage measurable_fst
  have h2_meas : MeasurableSet {p : E n × E n | p.2 ∈ Bδ} := hBδ_meas.preimage measurable_snd
  have h3_meas : MeasurableSet {p : E n × E n | p.1 ∈ A} := hA.preimage measurable_fst
  have h4_meas : MeasurableSet {p : E n × E n | p.1 + p.2 ∈ A} :=
    hA.preimage (measurable_fst.add measurable_snd)
  have h5_meas : MeasurableSet {p : E n × E n | (p.1 ∈ A ↔ p.1 + p.2 ∉ A)} := by
    let P : Set (E n × E n) := {p | p.1 ∈ A}
    let Q : Set (E n × E n) := {p | p.1 + p.2 ∈ A}
    have h51 : {p | (p.1 ∈ A ↔ p.1 + p.2 ∉ A)} = (P \ Q) ∪ (Q \ P) := by
      ext p; simp only [P, Q, Set.mem_setOf_eq, Set.mem_union, Set.mem_diff]
      constructor
      · intro h; by_cases hP : p.1 ∈ A
        · left; exact ⟨hP, h.mp hP⟩
        · right; have hQ : p.1 + p.2 ∈ A := by by_contra hQ2; exact hP (h.mpr hQ2)
          exact ⟨hQ, hP⟩
      · rintro (h | h)
        · exact ⟨fun _ => h.2, fun _ => h.1⟩
        · exact ⟨fun hP => False.elim (h.2 hP), fun hQ => False.elim (hQ h.1)⟩
    rw [h51]; exact (h3_meas.diff h4_meas).union (h4_meas.diff h3_meas)
  have hS_prod_meas : MeasurableSet S_prod := h1_meas.inter (h2_meas.inter h5_meas)
  let g : E n × E n → ENNReal := Set.indicator S_prod (fun _ => 1)
  have hg_meas : Measurable g := measurable_const.indicator hS_prod_meas
  have h_step1 : ∀ (x : E n), ∫⁻ h, g (x, h) =
      (if x ∈ K then volume (translateMismatch A x ∩ Bδ) else 0) := by
    intro x; by_cases hx : x ∈ K
    · let T := translateMismatch A x ∩ Bδ
      have hT_meas : MeasurableSet T := by
        have h6 : MeasurableSet (translateMismatch A x) := by
          by_cases hxA : x ∈ A
          · have h_eq : translateMismatch A x = {h | x + h ∉ A} := by ext h; simp [translateMismatch, hxA] <;> tauto
            rw [h_eq]; exact hA.preimage (measurable_const.add measurable_id) |>.compl
          · have h_eq : translateMismatch A x = {h | x + h ∈ A} := by ext h; simp [translateMismatch, hxA] <;> tauto
            rw [h_eq]; exact hA.preimage (measurable_const.add measurable_id)
        exact h6.inter hBδ_meas
      have h_eq1 : ∀ h, g (x, h) = Set.indicator T (fun _ : E n => (1 : ENNReal)) h := by
        intro h; simp [g, S_prod, T, hx, translateMismatch, Set.indicator_apply] <;> aesop
      have h_int : ∫⁻ h, g (x, h) = volume T := by
        rw [lintegral_congr h_eq1]
        exact lintegral_indicator_one hT_meas
      rw [h_int]; simp [hx, T]
    · have h9 : ∀ h, g (x, h) = 0 := by intro h; simp [g, S_prod, hx, Set.indicator_apply] <;> tauto
      rw [funext h9]; simp [hx]
  let fK : E n → ENNReal := fun x => volume (translateMismatch A x ∩ Bδ)
  have h_step2 : ∫⁻ x in K, fK x = ∫⁻ x, ∫⁻ h, g (x, h) := by
    have h10 : ∫⁻ x in K, fK x = ∫⁻ x, Set.indicator K fK x := by
      have h11 := setLIntegral_indicator (μ := volume) (s := K) (t := Set.univ) hK fK
      simpa using Eq.symm h11
    rw [h10]
    have h12 : ∀ x, Set.indicator K fK x = ∫⁻ h, g (x, h) := by
      intro x; rw [Set.indicator_apply, h_step1 x] <;> split_ifs <;> simp [fK] <;> tauto
    rw [← lintegral_congr h12]
  have h_fubini : ∫⁻ x, ∫⁻ h, g (x, h) = ∫⁻ h, ∫⁻ x, g (x, h) :=
    lintegral_lintegral_swap hg_meas.aemeasurable
  let f_h : E n → ENNReal := fun h => volume {x : E n | x ∈ K ∧ (x ∈ A ↔ x + h ∉ A)}
  have h_step4 : ∀ (h : E n), ∫⁻ x, g (x, h) =
      (if h ∈ Bδ then f_h h else 0) := by
    intro h; by_cases hh : h ∈ Bδ
    · let M_h : Set (E n) := {x | x ∈ K ∧ (x ∈ A ↔ x + h ∉ A)}
      have hM_meas : MeasurableSet M_h := by
        have h6 : MeasurableSet {x : E n | (x ∈ A ↔ x + h ∉ A)} := by
          let P : Set (E n) := A
          let Q : Set (E n) := (fun y : E n => y + h) ⁻¹' A
          have h7 : {x | (x ∈ A ↔ x + h ∉ A)} = (P \ Q) ∪ (Q \ P) := by
            ext x; simp only [P, Q, Set.mem_setOf_eq, Set.mem_union, Set.mem_diff, Set.mem_preimage]
            constructor
            · intro h_iff; by_cases hP : x ∈ A
              · left; exact ⟨hP, h_iff.mp hP⟩
              · right; have hQ : x + h ∈ A := by by_contra hQ2; exact hP (h_iff.mpr hQ2)
                exact ⟨hQ, hP⟩
            · rintro (h | h)
              · exact ⟨fun _ => h.2, fun _ => h.1⟩
              · exact ⟨fun hP => False.elim (h.2 hP), fun hQ => False.elim (hQ h.1)⟩
          rw [h7]; have h8 : MeasurableSet Q := hA.preimage (measurable_id.add measurable_const)
          exact (hA.diff h8).union (h8.diff hA)
        exact hK.inter h6
      have h_eq3 : ∀ x, g (x, h) = Set.indicator M_h (fun _ : E n => (1 : ENNReal)) x := by
        intro x; simp [g, S_prod, M_h, hh, Set.indicator_apply] <;> aesop
      have h_int : ∫⁻ x, g (x, h) = volume M_h := by
        rw [lintegral_congr h_eq3]
        exact lintegral_indicator_one hM_meas
      have h_fh_eq : f_h h = volume M_h := by
        simp [f_h, M_h]
        <;> rfl
      rw [h_int, h_fh_eq]
      <;> simp [hh]
    · have h10 : ∀ x, g (x, h) = 0 := by intro x; simp [g, S_prod, hh, Set.indicator_apply] <;> tauto
      rw [funext h10]; simp [hh]
  have h_step5 : ∫⁻ h, ∫⁻ x, g (x, h) = ∫⁻ h in Bδ, f_h h := by
    have h12 : ∫⁻ h, ∫⁻ x, g (x, h) = ∫⁻ h, (if h ∈ Bδ then f_h h else 0) := by
      congr with h; exact h_step4 h
    rw [h12]
    have h13 : ∫⁻ h, (if h ∈ Bδ then f_h h else 0) = ∫⁻ h, Set.indicator Bδ f_h h := by
      apply lintegral_congr; intro h; simp [Set.indicator_apply] <;> split_ifs <;> tauto
    rw [h13, lintegral_indicator hBδ_meas f_h]
  have h_bound_mismatch : ∀ (h : E n), h ∈ Bδ →
      f_h h ≤ volume (symmDiff A ((fun x => x + h) '' A) ∩ Kδ) := by
    intro h hh
    let Ah : Set (E n) := (fun x : E n => x + h) '' A
    let S_h : Set (E n) := symmDiff A Ah
    let Kh : Set (E n) := (fun x : E n => x + h) '' K
    have hKh_sub : Kh ⊆ Kδ := by
      intro y hy; rcases hy with ⟨x, hx, rfl⟩
      have h_norm : ‖h‖ < δ := by simpa [Bδ, dist_zero_right] using hh
      exact hKδ x hx h h_norm
    let M_h : Set (E n) := {x | x ∈ K ∧ (x ∈ A ↔ x + h ∉ A)}
    have h_set_eq : M_h = (fun z : E n => z - h) '' (S_h ∩ Kh) := by
      ext x; simp only [M_h, Set.mem_setOf_eq, Set.mem_image]
      constructor
      · intro hx; refine ⟨x + h, ?_, by simp⟩
        have h_in_Kh : x + h ∈ Kh := ⟨x, hx.1, by simp⟩
        have h_in_S : x + h ∈ S_h := by
          simp [S_h, symmDiff, Set.mem_union, Set.mem_diff, Ah, Set.mem_image] <;> tauto
        exact ⟨h_in_S, h_in_Kh⟩
      · rintro ⟨y, hy, rfl⟩
        have h1 : y ∈ S_h := hy.1
        have h2 : y ∈ Kh := hy.2
        rcases h2 with ⟨x, hx, h_eq⟩
        have h3 : y - h ∈ K := by
          have h4 : y - h = x := by
            have h5 : x + h = y := h_eq
            exact sub_eq_iff_eq_add.mpr h5.symm
          rw [h4]
          exact hx
        have h4 : ((y - h) ∈ A ↔ (y - h) + h ∉ A) := by
          have h5 : (y - h) + h = y := by abel
          rw [h5]
          simp [S_h, symmDiff, Set.mem_union, Set.mem_diff, Ah, Set.mem_image] at h1 <;> tauto
        exact ⟨h3, h4⟩
    have h_image_eq2 : (fun z : E n => z - h) '' (S_h ∩ Kh) = (fun y : E n => y + h) ⁻¹' (S_h ∩ Kh) := by
      ext y; simp [Set.mem_preimage] <;> constructor
      · rintro ⟨z, hz, rfl⟩; simpa using hz
      · intro hy; refine ⟨y + h, hy, by simp⟩
    have h_vol : volume M_h = volume (S_h ∩ Kh) := by
      rw [h_set_eq, h_image_eq2]
      have h_fn_eq : (fun y : E n => y + h) ⁻¹' (S_h ∩ Kh) = (fun h_1 : E n => h + h_1) ⁻¹' (S_h ∩ Kh) := by
        ext z; simp [add_comm]
      rw [h_fn_eq]; exact MeasureTheory.measure_preimage_add volume h (S_h ∩ Kh)
    have h_f_h_eq : f_h h = volume M_h := by simp [f_h, M_h]
    rw [h_f_h_eq, h_vol]; exact measure_mono (inter_subset_inter_right _ hKh_sub)
  have h_bound_integral : ∫⁻ h in Bδ, f_h h ≤
      ∫⁻ h in Bδ, volume (symmDiff A ((fun x => x + h) '' A) ∩ Kδ) := by
    apply setLIntegral_mono' hBδ_meas; intro h hh; exact h_bound_mismatch h hh
  have h_bound_trans : ∫⁻ h in Bδ, volume (symmDiff A ((fun x => x + h) '' A) ∩ Kδ) ≤
      ∫⁻ h in Bδ, ENNReal.ofReal (C * ‖h‖) := by
    apply setLIntegral_mono' hBδ_meas; intro h _; exact h_trans h
  have h_bound_final : ∫⁻ h in Bδ, ENNReal.ofReal (C * ‖h‖) ≤ ENNReal.ofReal (C * δ) * volume Bδ := by
    have h9 : ∀ h ∈ Bδ, ENNReal.ofReal (C * ‖h‖) ≤ ENNReal.ofReal (C * δ) := by
      intro h hh; have h10 : ‖h‖ < δ := by simpa [Bδ, dist_zero_right] using hh
      have h11 : C * ‖h‖ ≤ C * δ := mul_le_mul_of_nonneg_left h10.le hC
      exact ENNReal.ofReal_le_ofReal h11
    calc ∫⁻ h in Bδ, ENNReal.ofReal (C * ‖h‖)
        ≤ ∫⁻ _ in Bδ, ENNReal.ofReal (C * δ) := by apply setLIntegral_mono' hBδ_meas; intro h hh; exact h9 h hh
      _ = ENNReal.ofReal (C * δ) * volume Bδ := by rw [setLIntegral_const, mul_comm]
  have h_set1 : ∫⁻ x in K, avgError δ A x = ∫⁻ x, Set.indicator K (avgError δ A) x :=
    Eq.symm (lintegral_indicator hK (avgError δ A))
  have h_avg_le_fK : ∀ x ∈ K, (volume Bδ) * avgError δ A x ≤ fK x := by
    intro x _
    have h10 : (volume Bδ) * avgError δ A x = (volume Bδ) * (fK x / volume Bδ) := by rfl
    rw [h10]
    have h11 : (volume Bδ) * (fK x / volume Bδ) ≤ fK x := by
      rw [ENNReal.mul_div_cancel hBδ_ne_zero hBδ_ne_top] <;> exact le_refl _
    exact h11
  have h_set2 : ∫⁻ x in K, (volume Bδ) * avgError δ A x =
      ∫⁻ x, Set.indicator K (fun x => (volume Bδ) * avgError δ A x) x :=
    Eq.symm (lintegral_indicator hK (fun x => (volume Bδ) * avgError δ A x))
  have h2 : ∀ x, (volume Bδ) * Set.indicator K (avgError δ A) x =
      Set.indicator K (fun x => (volume Bδ) * avgError δ A x) x := by
    intro x; simp [Set.indicator_apply] <;> split_ifs <;> ring
  have h_mult : (volume Bδ) * ∫⁻ x in K, avgError δ A x ≤ ∫⁻ x in K, (volume Bδ) * avgError δ A x := by
    calc (volume Bδ) * ∫⁻ x in K, avgError δ A x
      = (volume Bδ) * ∫⁻ x, Set.indicator K (avgError δ A) x := by rw [h_set1]
    _ ≤ ∫⁻ x, (volume Bδ) * Set.indicator K (avgError δ A) x :=
      lintegral_const_mul_le (volume Bδ) (Set.indicator K (avgError δ A))
    _ = ∫⁻ x, Set.indicator K (fun x => (volume Bδ) * avgError δ A x) x := by
      rw [← lintegral_congr h2]
    _ = ∫⁻ x in K, (volume Bδ) * avgError δ A x := h_set2.symm
  have h_mult2 : ∫⁻ x in K, (volume Bδ) * avgError δ A x ≤ ∫⁻ x in K, fK x := by
    apply setLIntegral_mono' hK; exact h_avg_le_fK
  have h_main_ineq : (volume Bδ) * ∫⁻ x in K, avgError δ A x ≤ ∫⁻ x in K, fK x :=
    le_trans h_mult h_mult2
  have h_final : ∫⁻ x in K, avgError δ A x ≤ (∫⁻ x in K, fK x) / volume Bδ := by
    have h12 : (volume Bδ) * ∫⁻ x in K, avgError δ A x ≤
        (volume Bδ) * ((∫⁻ x in K, fK x) / volume Bδ) := by
      rw [ENNReal.mul_div_cancel hBδ_ne_zero hBδ_ne_top]; exact h_main_ineq
    exact (ENNReal.mul_le_mul_iff_right hBδ_ne_zero hBδ_ne_top).mp h12
  calc ∫⁻ x in K, avgError δ A x
      ≤ (∫⁻ x in K, fK x) / volume Bδ := h_final
    _ = (∫⁻ x, ∫⁻ h, g (x, h)) / volume Bδ := by rw [h_step2]
    _ = (∫⁻ h, ∫⁻ x, g (x, h)) / volume Bδ := by rw [h_fubini]
    _ = (∫⁻ h in Bδ, f_h h) / volume Bδ := by rw [h_step5]
    _ ≤ (∫⁻ h in Bδ, volume (symmDiff A ((fun x => x + h) '' A) ∩ Kδ)) / volume Bδ := by gcongr
    _ ≤ (∫⁻ h in Bδ, ENNReal.ofReal (C * ‖h‖)) / volume Bδ := by gcongr
    _ ≤ (ENNReal.ofReal (C * δ) * volume Bδ) / volume Bδ := by gcongr
    _ = ENNReal.ofReal (C * δ) := by exact ENNReal.mul_div_cancel_right hBδ_ne_zero hBδ_ne_top

/-- Convert lintegral bound to Bochner L¹ bound. -/
lemma l1_error_bound {A : Set (E n)} (hA : MeasurableSet A)
    {K : Set (E n)} (hK : MeasurableSet K) (hKfin : volume K ≠ ⊤)
    (δ : ℝ) (hδ : 0 < δ) (C : ℝ) (hC : 0 ≤ C)
    (Kδ : Set (E n)) (hKδ : ∀ (x : E n), x ∈ K → ∀ (h : E n), ‖h‖ < δ → x + h ∈ Kδ)
    (h_trans : ∀ (h : E n),
      volume (symmDiff A ((fun x => x + h) '' A) ∩ Kδ) ≤ ENNReal.ofReal (C * ‖h‖)) :
    ∫ x in K, |(ballAverage A δ x).toReal - Set.indicator A (1 : E n → ℝ) x| ≤ C * δ := by
  have h1 := avgError_lintegral_bound hA hK δ hδ C hC Kδ hKδ h_trans
  let e : E n → ℝ := fun x => |(ballAverage A δ x).toReal - Set.indicator A (1 : E n → ℝ) x|
  have he_nonneg : ∀ x, 0 ≤ e x := fun x => abs_nonneg _
  have h2 : ∀ x, avgError δ A x = ENNReal.ofReal (e x) := by
    intro x; exact (ballAverage_error hA hδ x).symm
  rw [lintegral_congr h2] at h1
  have h_cont_ba : Continuous (fun x : E n => (ballAverage A δ x).toReal) :=
    (ballAverage_equicontinuous hδ).continuous A
  have h_ind_meas : Measurable (Set.indicator A (1 : E n → ℝ)) :=
    measurable_const.indicator hA
  have he_meas : Measurable e := by
    simpa only [Real.norm_eq_abs] using
      (h_cont_ba.measurable.sub h_ind_meas).norm
  have he_bound : ∀ x, e x ≤ 1 := by
    intro x
    have hba : 0 ≤ (ballAverage A δ x).toReal ∧ (ballAverage A δ x).toReal ≤ 1 := ballAverage_bounded hδ x
    by_cases h : x ∈ A
    · have hi : Set.indicator A (1 : E n → ℝ) x = 1 := by
        simp [Set.indicator_apply, h]
      have heq : e x = |(ballAverage A δ x).toReal - 1| := by
        simp [e, hi]
      rw [heq]
      have h6 : |(ballAverage A δ x).toReal - 1| ≤ 1 := by
        rw [abs_le] <;> constructor <;> linarith [hba.1, hba.2]
      exact h6
    · have hi : Set.indicator A (1 : E n → ℝ) x = 0 := by
        simp [Set.indicator_apply, h]
      have heq : e x = |(ballAverage A δ x).toReal - 0| := by
        simp [e, hi]
      rw [heq]
      have h_nonneg : 0 ≤ (ballAverage A δ x).toReal := hba.1
      have h_abs : |(ballAverage A δ x).toReal - 0| = (ballAverage A δ x).toReal := by
        rw [sub_zero, abs_of_nonneg h_nonneg]
      rw [h_abs]
      exact hba.2
  have h_const_int : IntegrableOn (fun _ : E n => (1 : ℝ)) K := by
    rw [MeasureTheory.integrableOn_const_iff (C := (1 : ℝ))]
    have h_lt : volume K < ⊤ := lt_top_iff_ne_top.mpr hKfin
    exact Or.inr h_lt
  have h_bound_ae : ∀ᵐ x ∂volume.restrict K, ‖e x‖ ≤ 1 := by
    filter_upwards with x
    have h_abs : ‖e x‖ = |e x| := by
      simp [Real.norm_eq_abs]
    rw [h_abs, abs_of_nonneg (he_nonneg x)]
    exact he_bound x
  have h_bound_ae2 : ∀ᵐ x ∂volume.restrict K, ‖e x‖ ≤ ‖(fun _ : E n => (1 : ℝ)) x‖ := by
    filter_upwards [h_bound_ae] with x hx
    simpa using hx
  have he_ae : AEStronglyMeasurable e (volume.restrict K) := by
    exact he_meas.aestronglyMeasurable
  have he_int : IntegrableOn e K :=
    Integrable.mono h_const_int he_ae h_bound_ae2
  have h4 : (∫⁻ x in K, ENNReal.ofReal (e x)).toReal = ∫ x in K, e x := by
    have h_eq : ∫ x in K, e x = (∫⁻ x in K, ENNReal.ofReal (e x)).toReal :=
      MeasureTheory.integral_eq_lintegral_of_nonneg_ae
        (Eventually.of_forall he_nonneg) he_meas.aestronglyMeasurable
    exact h_eq.symm
  have h5 : ∫⁻ x in K, ENNReal.ofReal (e x) ≠ ⊤ := by
    have h_bound : ∫⁻ x in K, ENNReal.ofReal (e x) ≤ ∫⁻ x in K, (1 : ENNReal) := by
      apply setLIntegral_mono' hK
      intro x _
      have h6 : ENNReal.ofReal (e x) ≤ 1 := by
        have h7 : e x ≤ 1 := by linarith [he_bound x]
        have h8 : ENNReal.ofReal (e x) ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal h7
        simpa using h8
      exact h6
    have h7 : ∫⁻ x in K, (1 : ENNReal) = volume K := by
      simpa [setLIntegral_const] using rfl
    rw [h7] at h_bound
    exact ne_top_of_le_ne_top hKfin h_bound
  have h3 : ∫⁻ x in K, ENNReal.ofReal (e x) = ENNReal.ofReal (∫ x in K, e x) := by
    have h7 : ENNReal.ofReal ((∫⁻ x in K, ENNReal.ofReal (e x)).toReal) = ∫⁻ x in K, ENNReal.ofReal (e x) :=
      ENNReal.ofReal_toReal h5
    rw [h4] at h7
    exact h7.symm
  rw [h3] at h1
  have h4' : 0 ≤ ∫ x in K, e x := by positivity
  have h5' : 0 ≤ C * δ := by positivity
  have h6 : ENNReal.ofReal (∫ x in K, e x) ≤ ENNReal.ofReal (C * δ) := h1
  have h_ne_top1 : ENNReal.ofReal (∫ x in K, e x) ≠ ⊤ := by simp
  have h_ne_top2 : ENNReal.ofReal (C * δ) ≠ ⊤ := by simp
  have h7 : (ENNReal.ofReal (∫ x in K, e x)).toReal ≤ (ENNReal.ofReal (C * δ)).toReal :=
    (ENNReal.toReal_le_toReal h_ne_top1 h_ne_top2).mpr h6
  simpa [ENNReal.toReal_ofReal h4', ENNReal.toReal_ofReal h5'] using h7

/-- **L¹ closure of {0,1}-valued functions**. If a sequence of integrable
{0,1}-valued functions `h n` converges in L¹(μ) to an integrable function `g`,
then `g x ∈ {0,1}` for μ-a.e. `x`. -/
lemma binary_l1_closure {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {h : ℕ → α → ℝ} {g : α → ℝ}
    (h_binary : ∀ n x, h n x = 0 ∨ h n x = 1)
    (h_int : ∀ n, Integrable (h n) μ)
    (hg_int : Integrable g μ)
    (h_conv : Tendsto (fun n => ∫ x, |h n x - g x| ∂μ) atTop (nhds 0)) :
    ∀ᵐ x ∂μ, g x = 0 ∨ g x = 1 := by
  let d : α → ℝ := fun x => min |g x| |g x - 1|
  have hd_nonneg : ∀ x, 0 ≤ d x := fun x => le_min (abs_nonneg _) (abs_nonneg _)
  have hd_le1 : ∀ x, d x ≤ |g x| := fun x => min_le_left _ _
  have hd_le2 : ∀ x, d x ≤ |g x - 1| := fun x => min_le_right _ _
  have hd_meas : AEStronglyMeasurable d μ := by
    have h1 : AEStronglyMeasurable (fun x => |g x|) μ := hg_int.aestronglyMeasurable.norm
    have h2 : AEStronglyMeasurable (fun x => |g x - 1|) μ :=
      (hg_int.aestronglyMeasurable.sub aestronglyMeasurable_const).norm
    exact continuous_min.comp_aestronglyMeasurable₂ h1 h2
  have hd_int : Integrable d μ := by
    have h_bound : ∀ᵐ x ∂μ, ‖d x‖ ≤ ‖g x‖ := by
      filter_upwards with x
      have h1 : ‖d x‖ = d x := by
        rw [Real.norm_eq_abs, abs_of_nonneg (hd_nonneg x)]
      have h2 : ‖g x‖ = |g x| := by simp [Real.norm_eq_abs]
      rw [h1, h2]; exact hd_le1 x
    exact Integrable.mono hg_int hd_meas h_bound
  have h_dist : ∀ n x, d x ≤ |h n x - g x| := by
    intro n x
    rcases h_binary n x with (h1 | h1)
    · rw [h1]; rw [zero_sub, abs_neg]; exact hd_le1 x
    · rw [h1]; rw [show (1 : ℝ) - g x = -(g x - 1) by ring, abs_neg]; exact hd_le2 x
  have h_int_dist : ∀ n, ∫ x, d x ∂μ ≤ ∫ x, |h n x - g x| ∂μ := by
    intro n
    have h_abs_int : Integrable (fun x => |h n x - g x|) μ :=
      ((h_int n).sub hg_int).norm
    have h_ae : ∀ᵐ x ∂μ, d x ≤ |h n x - g x| := by
      filter_upwards with x; exact h_dist n x
    exact integral_mono_ae hd_int h_abs_int h_ae
  have h_zero_dist : ∫ x, d x ∂μ = 0 := by
    have h_nonneg : 0 ≤ ∫ x, d x ∂μ := integral_nonneg hd_nonneg
    have h_le : ∫ x, d x ∂μ ≤ 0 := by
      by_contra h_contra
      have h_pos : 0 < ∫ x, d x ∂μ := by linarith
      have h_tend' : ∃ N, ∀ n ≥ N, dist (∫ x, |h n x - g x| ∂μ) 0 < ∫ x, d x ∂μ :=
        Metric.tendsto_atTop.mp h_conv (∫ x, d x ∂μ) h_pos
      rcases h_tend' with ⟨N, hN⟩
      have h9 := hN N (le_refl N)
      have h10 : 0 ≤ ∫ x, |h N x - g x| ∂μ := by positivity
      have h_eq : dist (∫ x, |h N x - g x| ∂μ) 0 = ∫ x, |h N x - g x| ∂μ := by
        rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg h10]
      rw [h_eq] at h9
      have h11 : ∫ x, d x ∂μ ≤ ∫ x, |h N x - g x| ∂μ := h_int_dist N
      linarith
    exact le_antisymm h_le h_nonneg
  have h_ae_dist : ∀ᵐ x ∂μ, d x = 0 :=
    (MeasureTheory.integral_eq_zero_iff_of_nonneg_ae
      (Eventually.of_forall hd_nonneg) hd_int).mp h_zero_dist
  filter_upwards [h_ae_dist] with x hx
  have h5 : min |g x| |g x - 1| = 0 := hx
  have h6 : |g x| = 0 ∨ |g x - 1| = 0 := by
    by_cases h7 : |g x| ≤ |g x - 1|
    · have h9 : min |g x| |g x - 1| = |g x| := by
        rw [min_eq_left h7]
      rw [h9] at h5
      exact Or.inl h5
    · have h10 : |g x - 1| < |g x| := by linarith
      have h9 : min |g x| |g x - 1| = |g x - 1| := by
        rw [min_eq_right (by linarith)]
      rw [h9] at h5
      exact Or.inr h5
  rcases h6 with (h6 | h6)
  · exact Or.inl (abs_eq_zero.mp h6)
  · have h7 : g x = 1 := by
      have h8 : g x - 1 = 0 := abs_eq_zero.mp h6
      linarith
    exact Or.inr h7

/-- For an integrable real function on a finite measure, the L¹ eLpNorm equals
`ENNReal.ofReal` of the integral of the absolute value. -/
lemma eLpNorm_one_eq_ofReal_abs_integral {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {g : α → ℝ} (hg : Integrable g μ) :
    eLpNorm g 1 μ = ENNReal.ofReal (∫ x, |g x| ∂μ) := by
  have h1 : eLpNorm g 1 μ = ∫⁻ x, ‖g x‖ₑ ∂μ := eLpNorm_one_eq_lintegral_enorm
  have h2 : ∫⁻ x, ‖g x‖ₑ ∂μ = ∫⁻ x, ENNReal.ofReal |g x| ∂μ := by
    congr with x; exact Real.enorm_eq_ofReal_abs (g x)
  have h3 : ∀ᵐ x ∂μ, 0 ≤ |g x| := by filter_upwards with x; exact abs_nonneg _
  have h4 : ∫ x, |g x| ∂μ = (∫⁻ x, ENNReal.ofReal |g x| ∂μ).toReal :=
    MeasureTheory.integral_eq_lintegral_of_nonneg_ae h3 hg.abs.aestronglyMeasurable
  have h5 : ∫⁻ x, ENNReal.ofReal |g x| ∂μ ≠ ⊤ := by
    have h_lt : (∫⁻ x, ‖g x‖ₑ ∂μ) < ⊤ := hg.2
    rw [h2] at h_lt
    exact h_lt.ne
  have h6 : ENNReal.ofReal (∫ x, |g x| ∂μ) = ∫⁻ x, ENNReal.ofReal |g x| ∂μ := by
    rw [h4]
    exact ENNReal.ofReal_toReal h5
  rw [h1, h2, h6.symm]

end Geometry
