import MyLeanRepo.Kakeya.Assouad.TubeVolumeLowerBound
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Cardinality bound from Katz-Tao convex Wolff estimate

Given a tube family `F` in the unit ball satisfying `KatzTaoConvexWolffBound F C`,
derive `(F.card : ℝ) ≤ (4π/3) * C * δ^{-2}`.

This is used to bound the logarithm of the fiber count in the stable parent
assembly, so that the logarithmic balancing loss can be absorbed by
`exists_delta_pow_log_bound`.
-/

noncomputable section

open MeasureTheory Metric

attribute [local instance] Classical.propDecidable

namespace Kakeya.Assouad

/-- Cardinality bound from Katz-Tao: a family in the unit ball with KT constant C
has at most `(4π/3) * C * δ^{-2}` tubes.

The bound follows by applying the KT estimate with `W := unitBall` (convex) and
using `deltaTubeVolume δ ≥ δ²`. -/
lemma katz_tao_card_bound {δ : ℝ} (hδ : 0 < δ)
    {F : Kakeya.TubeFamily δ} (hF_ball : F.IsInUnitBall)
    {C : ℝ} (hC_nonneg : 0 ≤ C)
    (hKT : Kakeya.KatzTaoConvexWolffBound F C) :
    (F.card : ℝ) ≤ (4 * Real.pi / 3) * C * δ ^ (-2 : ℝ) := by
  let W : Set Point3 := Kakeya.DeltaTube.unitBall
  have hW_convex : Convex ℝ W := convex_closedBall 0 1
  have h_filter : F.filter (fun T : Kakeya.DeltaTube δ => T.carrier ⊆ W) = F := by
    apply Finset.filter_true_of_mem
    intro T hT
    exact hF_ball hT
  have h_contained_all : F.containedCount W = F.enncard := by
    unfold Kakeya.TubeFamily.containedCount Kakeya.TubeFamily.enncard
    rw [h_filter]
    <;> rfl
  have h1 := hKT W hW_convex
  rw [h_contained_all] at h1
  have h_vol_W : volume W = ENNReal.ofReal (4 * Real.pi / 3) := by
    have h : volume W = ENNReal.ofReal (Real.pi * 4 / 3) := by
      simp [W, Kakeya.DeltaTube.unitBall]
    rw [h]
    congr 1
    ring
  have h_lower : ENNReal.ofReal (δ ^ 2) ≤ Kakeya.deltaTubeVolume δ :=
    canonical_volume_lower hδ
  have hδ2_pos : 0 < δ ^ 2 := by positivity
  have h_inv : (Kakeya.deltaTubeVolume δ)⁻¹ ≤ (ENNReal.ofReal (δ ^ 2))⁻¹ :=
    ENNReal.inv_le_inv.mpr h_lower
  have h4 : (δ ^ 2 : ℝ)⁻¹ = δ ^ (-2 : ℝ) := by
    have h5 : (δ ^ 2 : ℝ)⁻¹ = 1 / (δ ^ 2) := by simp
    have h6 : δ ^ (-2 : ℝ) = 1 / (δ ^ 2) := by
      rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num]
      rw [Real.rpow_neg hδ.le]
      <;> norm_cast <;> field_simp
    rw [h5, h6]
  have h_inv21 : (ENNReal.ofReal (δ ^ 2))⁻¹ = ENNReal.ofReal ((δ ^ 2)⁻¹) :=
    (ENNReal.ofReal_inv_of_pos hδ2_pos).symm
  have h_inv2 : (ENNReal.ofReal (δ ^ 2))⁻¹ = ENNReal.ofReal (δ ^ (-2 : ℝ)) := by
    rw [h_inv21]
    apply congr_arg ENNReal.ofReal
    exact h4
  set Y : ℝ := (4 * Real.pi / 3) * C * δ ^ (-2 : ℝ) with hY_def
  have hY_nonneg : 0 ≤ Y := by positivity
  have h_pos1 : 0 ≤ C := hC_nonneg
  have h_pos2 : 0 ≤ (4 * Real.pi / 3 : ℝ) := by positivity
  have h_pos3 : 0 ≤ δ ^ (-2 : ℝ) := by positivity
  have h1mul : ENNReal.ofReal C * ENNReal.ofReal (4 * Real.pi / 3) =
      ENNReal.ofReal (C * (4 * Real.pi / 3)) :=
    Eq.symm (ENNReal.ofReal_mul h_pos1)
  have h2mul : ENNReal.ofReal (C * (4 * Real.pi / 3)) * ENNReal.ofReal (δ ^ (-2 : ℝ)) =
      ENNReal.ofReal ((C * (4 * Real.pi / 3)) * δ ^ (-2 : ℝ)) :=
    Eq.symm (ENNReal.ofReal_mul (by positivity))
  have hY_eq : (C * (4 * Real.pi / 3)) * δ ^ (-2 : ℝ) = Y := by
    rw [hY_def]
    ring
  have h_mul : ENNReal.ofReal C * ENNReal.ofReal (4 * Real.pi / 3) *
        ENNReal.ofReal (δ ^ (-2 : ℝ)) = ENNReal.ofReal Y := by
    calc
      ENNReal.ofReal C * ENNReal.ofReal (4 * Real.pi / 3) * ENNReal.ofReal (δ ^ (-2 : ℝ))
        = (ENNReal.ofReal C * ENNReal.ofReal (4 * Real.pi / 3)) * ENNReal.ofReal (δ ^ (-2 : ℝ)) := by
          rw [mul_assoc]
      _ = ENNReal.ofReal (C * (4 * Real.pi / 3)) * ENNReal.ofReal (δ ^ (-2 : ℝ)) := by rw [h1mul]
      _ = ENNReal.ofReal ((C * (4 * Real.pi / 3)) * δ ^ (-2 : ℝ)) := h2mul
      _ = ENNReal.ofReal Y := by rw [hY_eq]
  have h_main : F.enncard ≤ ENNReal.ofReal Y := by
    calc F.enncard
      ≤ ENNReal.ofReal C * volume W * (Kakeya.deltaTubeVolume δ)⁻¹ := h1
    _ = ENNReal.ofReal C * ENNReal.ofReal (4 * Real.pi / 3) *
          (Kakeya.deltaTubeVolume δ)⁻¹ := by rw [h_vol_W]
    _ ≤ ENNReal.ofReal C * ENNReal.ofReal (4 * Real.pi / 3) *
          (ENNReal.ofReal (δ ^ 2))⁻¹ := by gcongr
    _ = ENNReal.ofReal C * ENNReal.ofReal (4 * Real.pi / 3) *
          ENNReal.ofReal (δ ^ (-2 : ℝ)) := by rw [h_inv2]
    _ = ENNReal.ofReal Y := h_mul
  have hF_card : F.enncard = ENNReal.ofReal (F.card : ℝ) := by
    simp [Kakeya.TubeFamily.enncard] <;> norm_cast
  rw [hF_card] at h_main
  exact_mod_cast (ENNReal.ofReal_le_ofReal_iff hY_nonneg).mp h_main

/-- Logarithmic bound on fiber count using the KT cardinality bound.

If `N ≤ |F|` and `F` satisfies the KT bound at exponent `inputEta`, then
`1 + log N ≤ 1 + log(4π/3) + (inputEta + 2) * log(1/δ)`.
This is of the form `b + c * log(1/δ)` for `exists_delta_pow_log_bound`. -/
lemma log_fiber_count_bound {δ inputEta : ℝ} (hδ : 0 < δ)
    (h_inputEta_pos : 0 < inputEta)
    {F : Kakeya.TubeFamily δ} (hF_ball : F.IsInUnitBall)
    (hKT : Kakeya.KatzTaoConvexWolffBound F (Real.rpow δ (-inputEta)))
    {N : ℕ} (hN_pos : 0 < N) (hN_le_F : N ≤ F.card) :
    1 + Real.log (N : ℝ) ≤
      (1 + Real.log (4 * Real.pi / 3)) + (inputEta + 2) * Real.log (1 / δ) := by
  set K : ℝ := 4 * Real.pi / 3 with hK_def
  have hK_pos : 0 < K := by positivity
  have hC_nonneg : 0 ≤ Real.rpow δ (-inputEta) := Real.rpow_nonneg hδ.le _
  have h_card : (F.card : ℝ) ≤ K * Real.rpow δ (-inputEta) * δ ^ (-2 : ℝ) :=
    katz_tao_card_bound hδ hF_ball hC_nonneg hKT
  have h_rpow : Real.rpow δ (-inputEta) * δ ^ (-2 : ℝ) =
      δ ^ (-(inputEta + 2)) := by
    have h1 : Real.rpow δ (-inputEta) = δ ^ (-inputEta : ℝ) := by rfl
    rw [h1]
    rw [← Real.rpow_add hδ] <;> ring
  have h_card2 : (F.card : ℝ) ≤ K * (Real.rpow δ (-inputEta) * δ ^ (-2 : ℝ)) := by
    have h_assoc : K * Real.rpow δ (-inputEta) * δ ^ (-2 : ℝ) =
        K * (Real.rpow δ (-inputEta) * δ ^ (-2 : ℝ)) := by ring
    rw [h_assoc] at h_card
    exact h_card
  rw [h_rpow] at h_card2
  have hN_pos' : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN_pos
  have hN1 : (N : ℝ) ≤ (F.card : ℝ) := by exact_mod_cast hN_le_F
  have hN_le : (N : ℝ) ≤ K * δ ^ (-(inputEta + 2)) :=
    hN1.trans h_card2
  have h_log : Real.log (N : ℝ) ≤
      Real.log K + (inputEta + 2) * Real.log (1 / δ) := by
    have h5 : Real.log (N : ℝ) ≤ Real.log (K * δ ^ (-(inputEta + 2))) :=
      Real.log_le_log (by exact_mod_cast hN_pos) hN_le
    have h6 : Real.log (K * δ ^ (-(inputEta + 2))) =
        Real.log K + Real.log (δ ^ (-(inputEta + 2))) := by
      rw [Real.log_mul hK_pos.ne'] <;> positivity
    rw [h6] at h5
    have h7 : Real.log (δ ^ (-(inputEta + 2))) =
        (inputEta + 2) * Real.log (1 / δ) := by
      calc
        Real.log (δ ^ (-(inputEta + 2)))
          = (-(inputEta + 2)) * Real.log δ := by rw [Real.log_rpow hδ]
        _ = (inputEta + 2) * (-Real.log δ) := by ring
        _ = (inputEta + 2) * Real.log (1 / δ) := by
          have h9 : Real.log (1 / δ) = -Real.log δ := by
            rw [Real.log_div (by norm_num) hδ.ne'] <;> simp
          rw [h9] <;> ring
    rw [h7] at h5
    exact h5
  linarith

end Kakeya.Assouad
