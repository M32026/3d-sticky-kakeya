import MyLeanRepo.Kakeya.Streamlined.TubePacking.Proof

/-!
# Packing tubes in the unit ball

The squared plank phase-space bound gives the polynomial cardinality estimate
needed by finite-grid uniformization.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Streamlined

/-- The closed unit ball is a framed `1 × 1 × 1` body up to factor `2`. -/
lemma unitBall_hasDimensionsInFrame :
    unitBall.HasDimensionsInFrame
      (AffineIsometryEquiv.refl ℝ Point3) 1 1 1 2 := by
  let frame : Point3 ≃ᵃⁱ[ℝ] Point3 := AffineIsometryEquiv.refl ℝ Point3
  have h_inner : frame '' axisBox 1 1 1 ⊆ unitBall.carrier := by
    intro x hx
    rcases hx with ⟨y, hy, rfl⟩
    have h0 : |y 0| ≤ 1 / 2 := hy.1
    have h1 : |y 1| ≤ 1 / 2 := hy.2.1
    have h2 : |y 2| ≤ 1 / 2 := hy.2.2
    have h_norm_sq : ‖y‖ ^ 2 = (y 0) ^ 2 + (y 1) ^ 2 + (y 2) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simp [Fin.sum_univ_succ]
      <;> ring
    have h0_sq : (y 0) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
      rw [← sq_abs]
      gcongr
    have h1_sq : (y 1) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
      rw [← sq_abs]
      gcongr
    have h2_sq : (y 2) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
      rw [← sq_abs]
      gcongr
    have h_norm : ‖y‖ ≤ 1 := by
      have h_nonneg : 0 ≤ ‖y‖ := norm_nonneg _
      nlinarith [h_norm_sq, h0_sq, h1_sq, h2_sq]
    simpa [frame, unitBall, Kakeya.DeltaTube.unitBall,
      Metric.mem_closedBall] using h_norm
  have h_outer :
      unitBall.carrier ⊆ frame '' axisBox (2 * 1) (2 * 1) (2 * 1) := by
    intro x hx
    have h_norm : ‖x‖ ≤ 1 := by
      simpa [unitBall, Kakeya.DeltaTube.unitBall,
        Metric.mem_closedBall] using hx
    have h_coord : ∀ i : Fin 3, |x i| ≤ ‖x‖ := by
      intro i
      have h_sq : (x i) ^ 2 ≤ ‖x‖ ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq]
        exact Finset.single_le_sum
          (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
      nlinarith [sq_abs (x i), abs_nonneg (x i), norm_nonneg x]
    refine ⟨x, ?_, by simp [frame]⟩
    exact ⟨by simpa using (h_coord 0).trans h_norm,
      by simpa using (h_coord 1).trans h_norm,
      by simpa using (h_coord 2).trans h_norm⟩
  exact ⟨by norm_num, by norm_num, by norm_num, by norm_num,
    h_inner, h_outer⟩

/--
An essentially distinct family of `delta`-tubes in the unit ball has
cardinality `O(delta⁻⁴)`.
-/
theorem unitBall_tube_cardinality_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
      ∀ F : TubeFamily delta,
        F.IsEssentiallyDistinct →
        F.IsInUnitBall →
        (F.card : ℝ) ≤ C * (1 / delta) ^ 4 := by
  rcases tube_packing_in_plank 2 (by norm_num) with
    ⟨C, hC_pos, hpack⟩
  refine ⟨C, hC_pos, ?_⟩
  intro delta hdelta hdelta_one F hdistinct hball
  have hpack' := hpack delta 1 1 hdelta hdelta_one le_rfl le_rfl
    unitBall (AffineIsometryEquiv.refl ℝ Point3)
    unitBall_hasDimensionsInFrame F hdistinct hball
  have h_left : F.enncard ≠ ⊤ := by
    simp [TubeFamily.enncard]
  have h_right :
      ENNReal.ofReal (C * (1 * 1 / delta ^ 2) ^ 2) ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have h_real :
      F.enncard.toReal ≤
        (ENNReal.ofReal (C * (1 * 1 / delta ^ 2) ^ 2)).toReal :=
    (ENNReal.toReal_le_toReal h_left h_right).mpr hpack'
  have h_expr_nonneg : 0 ≤ C * (1 * 1 / delta ^ 2) ^ 2 := by
    positivity
  have h_cast : F.enncard.toReal = (F.card : ℝ) := by
    simp [TubeFamily.enncard]
  have h_rhs :
      (ENNReal.ofReal (C * (1 * 1 / delta ^ 2) ^ 2)).toReal =
        C * (1 / delta) ^ 4 := by
    rw [ENNReal.toReal_ofReal h_expr_nonneg]
    field_simp [hdelta.ne']
    <;> ring
  rw [h_cast, h_rhs] at h_real
  exact h_real

/--
After shrinking the scale, the constant in the `O(delta⁻⁴)` bound is absorbed
by one further power of `delta⁻¹`.
-/
theorem unitBall_tube_cardinality_five :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
      ∀ F : TubeFamily delta,
        F.IsEssentiallyDistinct →
        F.IsInUnitBall →
        (F.card : ℝ) ≤ (1 / delta) ^ 5 := by
  rcases unitBall_tube_cardinality_bound with ⟨C, hC_pos, hbound⟩
  let delta₀ : ℝ := min 1 (1 / C)
  have hdelta₀_pos : 0 < delta₀ := by
    exact lt_min zero_lt_one (one_div_pos.mpr hC_pos)
  have hdelta₀_one : delta₀ ≤ 1 := min_le_left _ _
  refine ⟨delta₀, hdelta₀_pos, hdelta₀_one, ?_⟩
  intro delta hdelta hdelta_small F hdistinct hball
  have hdelta_one : delta ≤ 1 :=
    hdelta_small.trans hdelta₀_one
  have h_base : 0 ≤ 1 / delta := by positivity
  have hC_le : C ≤ 1 / delta := by
    have hdelta_C : delta ≤ 1 / C :=
      hdelta_small.trans (min_le_right _ _)
    have hmul : C * delta ≤ 1 := by
      have h := mul_le_mul_of_nonneg_left hdelta_C hC_pos.le
      have hcancel : C * (1 / C) = 1 := by
        field_simp [hC_pos.ne']
      calc
        C * delta ≤ C * (1 / C) := h
        _ = 1 := hcancel
    calc
      C = C * delta / delta := by
        field_simp [hdelta.ne']
      _ ≤ 1 / delta := by
        exact div_le_div_of_nonneg_right hmul hdelta.le
  have h4 := hbound delta hdelta hdelta_one F hdistinct hball
  calc
    (F.card : ℝ) ≤ C * (1 / delta) ^ 4 := h4
    _ ≤ (1 / delta) * (1 / delta) ^ 4 := by gcongr
    _ = (1 / delta) ^ 5 := by ring

end Kakeya.Streamlined
