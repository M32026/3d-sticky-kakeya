import MyLeanRepo.Kakeya.CV.Statements
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Volume lemmas for unit cube ellipsoid packing

Provides basic volume and containment lemmas for the unit cube and unit ball
in three-dimensional Euclidean space.

## Main results

- `volume_unitCube`: the unit cube has volume 1.
- `unitCube_zero_subset_unitBall`: the centered unit cube is contained in the unit ball.
- `unitBall_volume_le_eight`: the unit ball has volume at most 8.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace Kakeya.CV

/-- The unit cube centered at `c` has volume 1. -/
lemma volume_unitCube (c : Point 3) : volume (unitCube c) = 1 := by
  let e : Point 3 → (Fin 3 → ℝ) := WithLp.ofLp
  have hmp : MeasurePreserving e := PiLp.volume_preserving_ofLp (ι := Fin 3)
  let B' : Set (Fin 3 → ℝ) :=
    Set.Icc (fun i : Fin 3 => c i - 1 / 2) (fun i : Fin 3 => c i + 1 / 2)
  have h_eq : unitCube c = e ⁻¹' B' := by
    ext x
    simp only [unitCube, B', Set.mem_preimage, Set.mem_Icc, Set.mem_setOf_eq, Pi.le_def]
    constructor
    · intro h
      constructor
      · intro i
        have h1 : |x i - c i| ≤ 1 / 2 := h i
        have h2 : -(1 / 2 : ℝ) ≤ x i - c i := (abs_le.mp h1).1
        linarith
      · intro i
        have h1 : |x i - c i| ≤ 1 / 2 := h i
        have h2 : x i - c i ≤ (1 / 2 : ℝ) := (abs_le.mp h1).2
        linarith
    · rintro ⟨h1, h2⟩
      intro i
      have h3 : c i - 1 / 2 ≤ x i := h1 i
      have h4 : x i ≤ c i + 1 / 2 := h2 i
      rw [abs_le]
      constructor <;> linarith
  have h_vol : volume (unitCube c) = volume B' := by
    rw [h_eq]
    exact hmp.measure_preimage (by measurability)
  rw [h_vol]
  rw [Real.volume_Icc_pi]
  have h_prod : ∏ i : Fin 3, ENNReal.ofReal ((c i + 1 / 2 : ℝ) - (c i - 1 / 2 : ℝ)) = 1 := by
    have h5 : ∀ i : Fin 3, ENNReal.ofReal ((c i + 1 / 2 : ℝ) - (c i - 1 / 2 : ℝ)) = 1 := by
      intro i
      have h6 : (c i + 1 / 2 : ℝ) - (c i - 1 / 2 : ℝ) = 1 := by ring
      rw [h6]
      simp
    rw [Finset.prod_congr rfl (fun i _ => h5 i)]
    simp
  rw [h_prod]

/-- The centered unit cube is contained in the unit ball. -/
lemma unitCube_zero_subset_unitBall : unitCube (0 : Point 3) ⊆ unitBall 3 := by
  intro x hx
  have h1 : ∀ i : Fin 3, |x i| ≤ 1 / 2 := by
    simpa [unitCube] using hx
  have h_sum_nonneg : 0 ≤ ∑ i : Fin 3, (x i) ^ 2 := by
    positivity
  have h3 : ‖x‖ ^ 2 = ∑ i : Fin 3, (x i) ^ 2 := by
    have h4 : ‖x‖ = Real.sqrt (∑ i : Fin 3, (x i) ^ 2) := by
      simp [EuclideanSpace.norm_eq]
    rw [h4]
    rw [Real.sq_sqrt h_sum_nonneg]
  have h4 : ∑ i : Fin 3, (x i) ^ 2 ≤ 1 := by
    have h5 : ∑ i : Fin 3, (x i) ^ 2 ≤ ∑ i : Fin 3, (1 / 2 : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      have h6 : |x i| ≤ 1 / 2 := h1 i
      have h7 : (x i) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
        have h8 : |x i| ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by gcongr
        simpa [sq_abs] using h8
      exact h7
    have h9 : ∑ i : Fin 3, (1 / 2 : ℝ) ^ 2 = 3 / 4 := by
      simp [Finset.sum_const]
      norm_num
    rw [h9] at h5
    linarith
  have h9 : ‖x‖ ^ 2 ≤ 1 := by
    rw [h3]
    exact h4
  have h10 : ‖x‖ ≤ 1 := by
    nlinarith [norm_nonneg x]
  simpa [unitBall, Metric.mem_closedBall] using h10

/-- The unit ball in 3D has volume at most 8. -/
lemma unitBall_volume_le_eight : volume (unitBall 3) ≤ 8 := by
  let e : Point 3 → (Fin 3 → ℝ) := WithLp.ofLp
  have hmp : MeasurePreserving e := PiLp.volume_preserving_ofLp (ι := Fin 3)
  let B' : Set (Fin 3 → ℝ) :=
    Set.Icc (fun _ : Fin 3 => (-1 : ℝ)) (fun _ : Fin 3 => (1 : ℝ))
  have h1 : unitBall 3 ⊆ e ⁻¹' B' := by
    intro x hx
    have h2 : ‖x‖ ≤ 1 := by simpa [unitBall, Metric.mem_closedBall] using hx
    have h3 : ∀ i : Fin 3, |x i| ≤ ‖x‖ := by
      intro i
      have h_sum_nonneg : 0 ≤ ∑ j : Fin 3, (x j) ^ 2 := by positivity
      have h4 : ‖x‖ ^ 2 = ∑ j : Fin 3, (x j) ^ 2 := by
        have h5 : ‖x‖ = Real.sqrt (∑ j : Fin 3, (x j) ^ 2) := by
          simp [EuclideanSpace.norm_eq]
        rw [h5, Real.sq_sqrt h_sum_nonneg]
      have h6 : (x i) ^ 2 ≤ ‖x‖ ^ 2 := by
        rw [h4]
        exact Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
      have h7 : |x i| ^ 2 ≤ ‖x‖ ^ 2 := by simpa [sq_abs] using h6
      nlinarith [abs_nonneg (x i), norm_nonneg x]
    have h4 : ∀ i : Fin 3, |x i| ≤ 1 := by
      intro i
      calc |x i| ≤ ‖x‖ := h3 i
           _ ≤ 1 := h2
    simp only [B', Set.mem_preimage, Set.mem_Icc, Pi.le_def]
    constructor
    · intro i
      have h5 : |x i| ≤ 1 := h4 i
      have h6 : -(1 : ℝ) ≤ x i := by
        have h7 : -|x i| ≤ x i := neg_abs_le (x i)
        linarith [abs_le.mp h5]
      exact h6
    · intro i
      have h5 : |x i| ≤ 1 := h4 i
      have h6 : x i ≤ (1 : ℝ) := by
        have h7 : x i ≤ |x i| := le_abs_self (x i)
        linarith [abs_le.mp h5]
      exact h6
  have h5 : volume (e ⁻¹' B') = volume B' :=
    hmp.measure_preimage (by measurability)
  have h6 : volume B' = 8 := by
    rw [Real.volume_Icc_pi]
    have h7 : ∏ i : Fin 3, ENNReal.ofReal ((1 : ℝ) - (-1 : ℝ)) = 8 := by
      have h8 : ∀ i : Fin 3, ENNReal.ofReal ((1 : ℝ) - (-1 : ℝ)) = 2 := by
        intro i
        norm_num
      rw [Finset.prod_congr rfl (fun i _ => h8 i)]
      simp [Finset.prod_const]
      norm_num
    rw [h7]
  calc volume (unitBall 3)
      ≤ volume (e ⁻¹' B') := measure_mono h1
    _ = volume B' := h5
    _ = 8 := h6

end Kakeya.CV
