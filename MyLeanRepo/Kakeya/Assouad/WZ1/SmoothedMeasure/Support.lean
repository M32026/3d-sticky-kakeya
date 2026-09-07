import MyLeanRepo.Kakeya.Assouad.WZ1.SmoothedMeasure.Basic
import Mathlib.MeasureTheory.Measure.Support

/-!
# Support of smoothed measures

This module proves that the support of `smoothMeasure A hne ρ hρ` is contained
in the union of closed balls of radius `ρ` centered at points of `A`.

## Main results
- `ballUniformMeasure_support_subset`: support of ball-uniform measure ⊆ closed ball
- `smoothMeasure_support_subset`: support of smoothed measure ⊆ union of closed balls
- `smoothMeasure_support_in_ball`: if A ⊆ closedBall 0 R, then support ⊆ closedBall 0 (R + ρ)
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set Metric

/-- Support of a nonzero scalar multiple of a measure equals the original support. -/
lemma support_smul_eq {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    {μ : Measure X} {c : ENNReal} (hc : c ≠ 0) :
    (c • μ).support = μ.support := by
  ext x
  simp only [Measure.mem_support_iff_forall]
  constructor
  · intro h U hU
    have h' : 0 < (c • μ) U := h U hU
    have h_apply : (c • μ) U = c * μ U := Measure.smul_apply c μ U
    rw [h_apply] at h'
    have : 0 < μ U := (ENNReal.mul_pos_iff).mp h' |>.2
    exact this
  · intro h U hU
    have h' : 0 < μ U := h U hU
    have h_apply : (c • μ) U = c * μ U := Measure.smul_apply c μ U
    rw [h_apply]
    exact ENNReal.mul_pos hc h'.ne'

/-- Support of `ballUniformMeasure ρ hρ` is contained in `closedBall 0 ρ`. -/
lemma ballUniformMeasure_support_subset {ρ : ℝ} (hρ : 0 < ρ) :
    (ballUniformMeasure ρ hρ : Measure Point2).support ⊆ Metric.closedBall (0 : Point2) ρ := by
  let total : ENNReal := volume (Metric.ball (0 : Point2) ρ)
  let m : Measure Point2 := volume.restrict (Metric.ball (0 : Point2) ρ)
  have h_eq : (ballUniformMeasure ρ hρ : Measure Point2) = total⁻¹ • m := by rfl
  rw [h_eq]
  have h_total_ne_top : total ≠ ⊤ := by
    dsimp only [total]
    rw [EuclideanSpace.volume_ball_fin_two (0 : Point2) ρ]
    have h1 : (ENNReal.ofReal ρ)^2 ≠ ⊤ := by
      simp [pow_two]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    exact ENNReal.mul_ne_top h1 ENNReal.ofReal_ne_top
  have h_inv_ne_zero : total⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr h_total_ne_top
  rw [support_smul_eq (c := total⁻¹) h_inv_ne_zero]
  have h_restrict : m.support ⊆ closure (Metric.ball (0 : Point2) ρ) ∩ volume.support :=
    Measure.support_restrict_subset (s := Metric.ball (0 : Point2) ρ)
  have h1 : m.support ⊆ closure (Metric.ball (0 : Point2) ρ) := by
    exact h_restrict.trans (by simp)
  have h2 : closure (Metric.ball (0 : Point2) ρ) ⊆ Metric.closedBall (0 : Point2) ρ :=
    Metric.closure_ball_subset_closedBall
  exact h1.trans h2

/-- Support of a finite sum of measures is contained in the union of their supports. -/
lemma support_finset_sum_subset {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    {ι : Type*} {s : Finset ι} {f : ι → Measure X} :
    (Finset.sum s f).support ⊆ ⋃ i ∈ s, (f i).support := by
  classical
  exact Finset.induction_on s (by simp)
    (fun a s ha IH => by
      rw [Finset.sum_insert ha, Measure.support_add]
      intro x hx
      cases hx with
      | inl hxa =>
        exact Set.mem_iUnion₂.mpr ⟨a, Finset.mem_insert_self a s, hxa⟩
      | inr hxs =>
        have h_xs : x ∈ ⋃ i ∈ s, (f i).support := IH hxs
        rcases Set.mem_iUnion₂.mp h_xs with ⟨i, hi, hxi⟩
        exact Set.mem_iUnion₂.mpr ⟨i, Finset.mem_insert_of_mem hi, hxi⟩)

/-- If `μ.support ⊆ closedBall 0 ρ`, then the support of the translated measure
`μ.map (fun y => a + y)` is contained in `closedBall a ρ`. -/
lemma support_map_translation_subset {μ : Measure Point2} {a : Point2} {ρ : ℝ}
    (h : μ.support ⊆ Metric.closedBall (0 : Point2) ρ) :
    (μ.map (fun y : Point2 => a + y)).support ⊆ Metric.closedBall a ρ := by
  intro x hx
  by_contra h_x
  have h_dist : ρ < dist x a := by
    simpa [Metric.mem_closedBall] using h_x
  set ε : ℝ := (dist x a - ρ) / 2 with hε_def
  have hε_pos : 0 < ε := by linarith
  have h_ball_mem : Metric.ball x ε ∈ nhds x := Metric.ball_mem_nhds x hε_pos
  have h_preimage : (fun y : Point2 => a + y) ⁻¹' (Metric.ball x ε) = Metric.ball (x - a) ε := by
    ext y
    simp [Metric.mem_ball, dist_eq_norm]
  have h_disj : Disjoint (Metric.ball (x - a) ε) (Metric.closedBall (0 : Point2) ρ) := by
    rw [Set.disjoint_left]
    intro y hy
    have h1 : dist y (x - a) < ε := hy
    have h3 : dist (x - a) 0 ≤ dist (x - a) y + dist y 0 := dist_triangle (x - a) y 0
    have h4 : dist (x - a) 0 = dist x a := by
      simp [dist_eq_norm]
    have h5 : ρ < dist y 0 := by
      rw [h4] at h3
      have h6 : dist x a ≤ dist y (x - a) + dist y 0 := by
        simpa [dist_comm y (x - a)] using h3
      linarith
    simpa [Metric.mem_closedBall] using not_le.mpr h5
  have h_subset : Metric.ball (x - a) ε ⊆ μ.supportᶜ := by
    intro y hy
    have h_y : y ∉ Metric.closedBall (0 : Point2) ρ := h_disj.subset_compl_right hy
    have h' : y ∉ μ.support := by
      intro hys
      exact h_y (h hys)
    exact h'
  have h_measure_zero : μ (Metric.ball (x - a) ε) = 0 := by
    have h_main : μ μ.supportᶜ = 0 := Measure.measure_compl_support (μ := μ)
    have h_le : μ (Metric.ball (x - a) ε) ≤ μ μ.supportᶜ := μ.mono h_subset
    rw [h_main] at h_le
    exact le_zero_iff.mp h_le
  have h_map_zero : (μ.map (fun y : Point2 => a + y)) (Metric.ball x ε) = 0 := by
    rw [Measure.map_apply (by fun_prop) Metric.isOpen_ball.measurableSet]
    rw [h_preimage]
    exact h_measure_zero
  have h_contra : x ∉ (μ.map (fun y : Point2 => a + y)).support := by
    rw [Measure.notMem_support_iff_exists]
    exact ⟨Metric.ball x ε, h_ball_mem, h_map_zero⟩
  exact h_contra hx

/-- The support of `smoothMeasure A hne ρ hρ` is contained in the union of
closed balls of radius `ρ` centered at points of `A`. -/
lemma smoothMeasure_support_subset
    {A : DiscreteSet 2} {hne : A.Nonempty} {ρ : ℝ} {hρ : 0 < ρ} :
    (smoothMeasure A hne ρ hρ : Measure Point2).support ⊆
      ⋃ a ∈ A, Metric.closedBall a ρ := by
  let σ := ballUniformMeasure ρ hρ
  let f : Point2 → Measure Point2 := fun a =>
    (σ.map (f := fun y : Point2 => a + y)
      (f_aemble := (by fun_prop : Measurable (fun y : Point2 => a + y)).aemeasurable) : Measure Point2)
  have h_main : (smoothMeasure A hne ρ hρ : Measure Point2) =
      (A.card : ENNReal)⁻¹ • Finset.sum A f := by
    unfold smoothMeasure
    rfl
  rw [h_main]
  have h_card_pos : (A.card : ENNReal) ≠ 0 := by
    exact_mod_cast hne.card_pos.ne'
  have h_inv_ne_zero : (A.card : ENNReal)⁻¹ ≠ 0 := by
    exact ENNReal.inv_ne_zero.mpr (by simp)
  rw [support_smul_eq (c := (A.card : ENNReal)⁻¹) h_inv_ne_zero]
  have h_sum : (Finset.sum A f).support ⊆ ⋃ a ∈ A, (f a).support :=
    support_finset_sum_subset
  have h_each : ∀ a ∈ A, (f a).support ⊆ Metric.closedBall a ρ := by
    intro a _
    exact support_map_translation_subset (ballUniformMeasure_support_subset hρ)
  calc
    (Finset.sum A f).support
      ⊆ ⋃ a ∈ A, (f a).support := h_sum
    _ ⊆ ⋃ a ∈ A, Metric.closedBall a ρ := by
      gcongr with a ha
      exact h_each a ha

/-- If `A ⊆ closedBall 0 R`, then the support of `smoothMeasure A hne ρ hρ`
is contained in `closedBall 0 (R + ρ)`. -/
lemma smoothMeasure_support_in_ball
    {A : DiscreteSet 2} {hne : A.Nonempty} {ρ : ℝ} {hρ : 0 < ρ}
    {R : ℝ} (hA : (A : Set Point2) ⊆ Metric.closedBall 0 R) :
    (smoothMeasure A hne ρ hρ : Measure Point2).support ⊆
      Metric.closedBall 0 (R + ρ) := by
  have h1 : (smoothMeasure A hne ρ hρ : Measure Point2).support ⊆
      ⋃ a ∈ A, Metric.closedBall a ρ := smoothMeasure_support_subset
  have h2 : (⋃ a ∈ A, Metric.closedBall a ρ) ⊆ Metric.closedBall 0 (R + ρ) := by
    intro x hx
    rcases Set.mem_iUnion₂.mp hx with ⟨a, ha, hxa⟩
    have h_a_in : a ∈ Metric.closedBall (0 : Point2) R := hA ha
    have h_dist1 : dist a 0 ≤ R := by simpa [Metric.mem_closedBall] using h_a_in
    have h_dist2 : dist x a ≤ ρ := by simpa [Metric.mem_closedBall] using hxa
    have h : dist x 0 ≤ R + ρ := by
      calc dist x 0 ≤ dist x a + dist a 0 := dist_triangle x a 0
           _ = dist x a + dist a 0 := by rfl
           _ ≤ ρ + R := by linarith
           _ = R + ρ := by ring
    simpa [Metric.mem_closedBall] using h
  exact h1.trans h2

/-- The original finite set `A` is contained in the support of `smoothMeasure A hne ρ hρ`. -/
lemma smoothMeasure_support_contains
    {A : DiscreteSet 2} {hne : A.Nonempty} {ρ : ℝ} {hρ : 0 < ρ} :
    (A : Set Point2) ⊆ (smoothMeasure A hne ρ hρ : Measure Point2).support := by
  intro a ha
  have h_main : ∀ (U : Set Point2), IsOpen U → a ∈ U →
      0 < (smoothMeasure A hne ρ hρ : Measure Point2) U := by
    intro U hU_open ha_in_U
    rw [smoothMeasure_apply hU_open.measurableSet]
    let S : Set Point2 := {y | a + y ∈ U}
    have hS_open : IsOpen S := hU_open.preimage (continuous_const.add continuous_id)
    have h0_in_S : (0 : Point2) ∈ S := by simpa [S] using ha_in_U
    have h_inter_nonempty : (Metric.ball (0 : Point2) ρ ∩ S).Nonempty := by
      refine ⟨0, ?_⟩
      exact ⟨by simpa [Metric.mem_ball] using hρ, h0_in_S⟩
    have h_ball_pos : 0 < (ballUniformMeasure ρ hρ : Measure Point2) S := by
      rw [ballUniformMeasure_apply hρ hS_open.measurableSet]
      have h_vol_pos : 0 < MeasureTheory.volume (Metric.ball (0 : Point2) ρ ∩ S) :=
        (Metric.isOpen_ball.inter hS_open).measure_pos MeasureTheory.volume h_inter_nonempty
      have h_total_pos : 0 < MeasureTheory.volume (Metric.ball (0 : Point2) ρ) := by
        rw [EuclideanSpace.volume_ball_fin_two (0 : Point2) ρ] <;> positivity
      have h_total_ne_top : MeasureTheory.volume (Metric.ball (0 : Point2) ρ) ≠ ⊤ := by
        rw [EuclideanSpace.volume_ball_fin_two (0 : Point2) ρ]
        have h1 : (ENNReal.ofReal ρ)^2 ≠ ⊤ := by
          simp [pow_two] <;> exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
        exact ENNReal.mul_ne_top h1 ENNReal.ofReal_ne_top
      rw [ENNReal.mul_pos_iff]
      exact ⟨by exact ENNReal.inv_pos.mpr h_total_ne_top, h_vol_pos⟩
    have h_sum_pos : 0 < ∑ x ∈ A, (ballUniformMeasure ρ hρ : Measure Point2) {y : Point2 | x + y ∈ U} := by
      have h_a_term : 0 < (ballUniformMeasure ρ hρ : Measure Point2) {y : Point2 | a + y ∈ U} := by
        simpa [S] using h_ball_pos
      have h : (ballUniformMeasure ρ hρ : Measure Point2) {y : Point2 | a + y ∈ U} ≤
          ∑ x ∈ A, (ballUniformMeasure ρ hρ : Measure Point2) {y : Point2 | x + y ∈ U} := by
        apply Finset.single_le_sum (fun i _ => by simp) ha
      exact lt_of_lt_of_le h_a_term h
    have h_card_pos : 0 < (A.card : ENNReal) := by exact_mod_cast hne.card_pos
    have h_inv_pos : 0 < (A.card : ENNReal)⁻¹ := by
      exact ENNReal.inv_pos.mpr (by simp)
    exact ENNReal.mul_pos h_inv_pos.ne' h_sum_pos.ne'
  rw [Measure.mem_support_iff_forall]
  intro U hU
  rcases Metric.nhds_basis_ball.mem_iff.mp hU with ⟨r, hr_pos, hr_sub⟩
  have h_ball_open : IsOpen (Metric.ball a r) := Metric.isOpen_ball
  have h_a_in_ball : a ∈ Metric.ball a r := by
    simp [Metric.mem_ball, hr_pos]
  have h_pos : 0 < (smoothMeasure A hne ρ hρ : Measure Point2) (Metric.ball a r) :=
    h_main (Metric.ball a r) h_ball_open h_a_in_ball
  have h_le : (smoothMeasure A hne ρ hρ : Measure Point2) (Metric.ball a r) ≤
      (smoothMeasure A hne ρ hρ : Measure Point2) U :=
    OuterMeasureClass.measure_mono (smoothMeasure A hne ρ hρ : Measure Point2) hr_sub
  exact lt_of_lt_of_le h_pos h_le

end Kakeya.Assouad
