import MyLeanRepo.Kakeya.Assouad.WZ1.DiscreteThinTubes
import MyLeanRepo.Kakeya.Assouad.WZ1.SmoothedMeasure.Basic
import MyLeanRepo.Kakeya.Assouad.WZ1.SmoothedMeasure.Support
import MyLeanRepo.Kakeya.Assouad.WZ1.SmoothedThinTubes
import MyLeanRepo.Kakeya.Assouad.WZ1.NonConcentrationToThinTubes
import MyLeanRepo.Kakeya.Assouad.WZ1.DiscreteToSmoothedThinTubesStatement
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Discrete-to-smoothed thin tubes

Promotes a discrete exceptional relation to an all-scale thin-tubes witness
for the corresponding smoothed probability measures.
-/

noncomputable section

open MeasureTheory Set Metric

open scoped ENNReal NNReal

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

private lemma closedBall_disjoint_of_deltaSeparated
    {G : DiscreteSet 2} {δ ρ : ℝ} (hρ2 : 2 * ρ < δ)
    (hsep : G.IsDeltaSeparated δ) {a b : Point2}
    (ha : a ∈ G) (hb : b ∈ G) (hne : a ≠ b) :
    Disjoint (Metric.closedBall a ρ) (Metric.closedBall b ρ) := by
  have h_dist : δ ≤ dist a b := hsep ha hb hne
  have h : ρ + ρ < dist a b := by linarith
  exact Metric.closedBall_disjoint_closedBall h

private def smoothedExceptionalSet
    (E : Finset (Point2 × Point2)) (ρ : ℝ) :
    Set (Point2 × Point2) :=
  ⋃ p ∈ E, Metric.closedBall p.1 ρ ×ˢ Metric.closedBall p.2 ρ

private lemma smoothedExceptionalSet_measurable
    (E : Finset (Point2 × Point2)) (ρ : ℝ) :
    MeasurableSet (smoothedExceptionalSet E ρ) := by
  have h_count : Set.Countable (E : Set (Point2 × Point2)) :=
    (Finset.finite_toSet E).countable
  apply MeasurableSet.biUnion h_count
  intro p _
  exact
    (Metric.isClosed_closedBall.prod
      Metric.isClosed_closedBall).measurableSet

private lemma smoothMeasure_closedBall
    {G : DiscreteSet 2} (hG : G.Nonempty) {δ ρ : ℝ}
    (hδ : 0 < δ) (hρpos : 0 < ρ) (hρ2 : 2 * ρ < δ)
    (hsep : G.IsDeltaSeparated δ) {a : Point2} (ha : a ∈ G) :
    (smoothMeasure G hG ρ hρpos : Measure Point2)
        (Metric.closedBall a ρ) =
      (1 : ENNReal) / (G.card : ENNReal) := by
  let σ := ballUniformMeasure ρ hρpos
  have h_apply :
      (smoothMeasure G hG ρ hρpos : Measure Point2)
          (Metric.closedBall a ρ) =
        (G.card : ENNReal)⁻¹ *
          ∑ x ∈ G, (σ : Measure Point2)
            {y : Point2 | x + y ∈ Metric.closedBall a ρ} :=
    smoothMeasure_apply Metric.isClosed_closedBall.measurableSet
  rw [h_apply]
  have h_a_term :
      (σ : Measure Point2)
          {y : Point2 | a + y ∈ Metric.closedBall a ρ} = 1 := by
    have h_set :
        {y : Point2 | a + y ∈ Metric.closedBall a ρ} =
          Metric.closedBall (0 : Point2) ρ := by
      ext y
      simp only [Set.mem_setOf_eq, Metric.mem_closedBall]
      have h_eq : dist (a + y) a = dist y (0 : Point2) := by
        simp [dist_eq_norm]
      rw [h_eq]
    rw [h_set]
    have h1 :
        (σ : Measure Point2) (Metric.closedBall (0 : Point2) ρ) =
          (volume (Metric.ball (0 : Point2) ρ))⁻¹ *
            volume
              (Metric.ball (0 : Point2) ρ ∩
                Metric.closedBall (0 : Point2) ρ) :=
      ballUniformMeasure_apply hρpos
        Metric.isClosed_closedBall.measurableSet
    rw [h1]
    have h_inter :
        Metric.ball (0 : Point2) ρ ∩ Metric.closedBall (0 : Point2) ρ =
          Metric.ball (0 : Point2) ρ := by
      apply Set.inter_eq_left.mpr
      exact Metric.ball_subset_closedBall
    rw [h_inter]
    have h_vol_pos :
        0 < volume (Metric.ball (0 : Point2) ρ) := by
      rw [EuclideanSpace.volume_ball_fin_two (0 : Point2) ρ] <;>
        positivity
    have h_vol_ne_zero :
        volume (Metric.ball (0 : Point2) ρ) ≠ 0 :=
      h_vol_pos.ne'
    have h_vol_ne_top :
        volume (Metric.ball (0 : Point2) ρ) ≠ ⊤ := by
      rw [EuclideanSpace.volume_ball_fin_two (0 : Point2) ρ]
      have h1 : ENNReal.ofReal ρ ≠ ⊤ := ENNReal.ofReal_ne_top
      have h2 : (ENNReal.ofReal ρ)^2 ≠ ⊤ := by
        simpa [pow_two] using ENNReal.mul_ne_top h1 h1
      exact ENNReal.mul_ne_top h2 ENNReal.ofReal_ne_top
    rw [ENNReal.inv_mul_cancel h_vol_ne_zero h_vol_ne_top]
  have h_other_term : ∀ x ∈ G, x ≠ a →
      (σ : Measure Point2)
          {y : Point2 | x + y ∈ Metric.closedBall a ρ} = 0 := by
    intro x hx hne
    have h_dist : δ ≤ dist x a := hsep hx ha hne
    have h_set_eq :
        {y : Point2 | x + y ∈ Metric.closedBall a ρ} =
          Metric.closedBall (a - x) ρ := by
      ext y
      simp only [Set.mem_setOf_eq, Metric.mem_closedBall]
      have h_eq1 : x + y - a = y - (a - x) := by abel
      rw [dist_eq_norm, dist_eq_norm, h_eq1]
    rw [h_set_eq]
    have h_eq : dist (0 : Point2) (a - x) = dist x a := by
      simp [dist_eq_norm]
    have h_le : ρ + ρ ≤ dist (0 : Point2) (a - x) := by
      rw [h_eq]
      linarith
    have h_disj :
        Disjoint (Metric.ball (0 : Point2) ρ)
          (Metric.closedBall (a - x) ρ) :=
      Metric.ball_disjoint_closedBall h_le
    have h_empty :
        Metric.ball (0 : Point2) ρ ∩ Metric.closedBall (a - x) ρ = ∅ :=
      Set.disjoint_iff_inter_eq_empty.mp h_disj
    rw [ballUniformMeasure_apply hρpos
      Metric.isClosed_closedBall.measurableSet, h_empty]
    simp
  have h_sum :
      ∑ x ∈ G, (σ : Measure Point2)
          {y : Point2 | x + y ∈ Metric.closedBall a ρ} = 1 := by
    have h3 :
        ∑ x ∈ G, (σ : Measure Point2)
            {y : Point2 | x + y ∈ Metric.closedBall a ρ} =
          (σ : Measure Point2)
            {y : Point2 | a + y ∈ Metric.closedBall a ρ} := by
      rw [Finset.sum_eq_single_of_mem a ha]
      intro x _ hne
      exact h_other_term x ‹x ∈ G› hne
    rw [h3, h_a_term]
  rw [h_sum]
  simp [div_eq_mul_inv]

private lemma smoothedExceptionalSet_cells_disjoint
    {G₁ G₂ : DiscreteSet 2} {δ ρ : ℝ} (hδ : 0 < δ)
    (hρ2 : 2 * ρ < δ)
    (hsep₁ : G₁.IsDeltaSeparated δ) (hsep₂ : G₂.IsDeltaSeparated δ)
    {E : Finset (Point2 × Point2)} (hE : E ⊆ G₁ ×ˢ G₂)
    {p q : Point2 × Point2} (hp : p ∈ E) (hq : q ∈ E)
    (hne : p ≠ q) :
    Disjoint
      (Metric.closedBall p.1 ρ ×ˢ Metric.closedBall p.2 ρ)
      (Metric.closedBall q.1 ρ ×ˢ Metric.closedBall q.2 ρ) := by
  have hp1 : p.1 ∈ G₁ := (Finset.mem_product.mp (hE hp)).1
  have hp2 : p.2 ∈ G₂ := (Finset.mem_product.mp (hE hp)).2
  have hq1 : q.1 ∈ G₁ := (Finset.mem_product.mp (hE hq)).1
  have hq2 : q.2 ∈ G₂ := (Finset.mem_product.mp (hE hq)).2
  by_cases h1 : p.1 ≠ q.1
  · have h_disj1 :=
      closedBall_disjoint_of_deltaSeparated hρ2 hsep₁ hp1 hq1 h1
    rw [Set.disjoint_left]
    intro x hxp hxq
    exact Set.disjoint_left.mp h_disj1 hxp.1 hxq.1
  · have h1' : p.1 = q.1 := by tauto
    have h2 : p.2 ≠ q.2 := by
      intro h
      have h3 : p = q := by
        exact Prod.ext h1' h
      exact hne h3
    have h_disj2 :=
      closedBall_disjoint_of_deltaSeparated hρ2 hsep₂ hp2 hq2 h2
    rw [Set.disjoint_left]
    intro x hxp hxq
    exact Set.disjoint_left.mp h_disj2 hxp.2 hxq.2

private lemma smoothedExceptionalSet_mass
    {G₁ G₂ : DiscreteSet 2} (hG₁ : G₁.Nonempty) (hG₂ : G₂.Nonempty)
    {δ c : ℝ} (hδ : 0 < δ)
    (hsep₁ : G₁.IsDeltaSeparated δ) (hsep₂ : G₂.IsDeltaSeparated δ)
    {E : Finset (Point2 × Point2)} (hE : E ⊆ G₁ ×ˢ G₂)
    (hmass :
      (1 - ENNReal.ofReal c) * (G₁.card : ENNReal) *
          (G₂.card : ENNReal) ≤
        (E.card : ENNReal)) :
    (1 - ENNReal.ofReal c) ≤
      ((smoothMeasure G₁ hG₁ (δ / 10) (by linarith) : Measure Point2).prod
        (smoothMeasure G₂ hG₂ (δ / 10) (by linarith) : Measure Point2))
        (smoothedExceptionalSet E (δ / 10)) := by
  set ρ : ℝ := δ / 10 with hρ_def
  have hρpos : 0 < ρ := by
    rw [hρ_def]
    linarith
  have hρ2 : 2 * ρ < δ := by
    rw [hρ_def]
    linarith
  let μ₁ : Measure Point2 := smoothMeasure G₁ hG₁ ρ hρpos
  let μ₂ : Measure Point2 := smoothMeasure G₂ hG₂ ρ hρpos
  let cell : Point2 × Point2 → Set (Point2 × Point2) := fun p =>
    Metric.closedBall p.1 ρ ×ˢ Metric.closedBall p.2 ρ
  set denom : ENNReal :=
    (G₁.card : ENNReal) * (G₂.card : ENNReal) with hdenom
  have h_meas_cell : ∀ p ∈ E, MeasurableSet (cell p) := by
    intro p _
    exact
      (Metric.isClosed_closedBall.prod
        Metric.isClosed_closedBall).measurableSet
  have h_disj :
      ∀ p ∈ E, ∀ q ∈ E, p ≠ q → Disjoint (cell p) (cell q) := by
    intro p hp q hq hne
    exact
      smoothedExceptionalSet_cells_disjoint
        hδ hρ2 hsep₁ hsep₂ hE hp hq hne
  have h_measure_union :
      (μ₁.prod μ₂) (smoothedExceptionalSet E ρ) =
        ∑ p ∈ E, (μ₁.prod μ₂) (cell p) := by
    exact measure_biUnion_finset h_disj h_meas_cell
  rw [h_measure_union]
  have h_cell_measure :
      ∀ p ∈ E, (μ₁.prod μ₂) (cell p) = (1 : ENNReal) / denom := by
    intro p hp
    have hp1 : p.1 ∈ G₁ := (Finset.mem_product.mp (hE hp)).1
    have hp2 : p.2 ∈ G₂ := (Finset.mem_product.mp (hE hp)).2
    have h1 :
        μ₁ (Metric.closedBall p.1 ρ) =
          (1 : ENNReal) / (G₁.card : ENNReal) :=
      smoothMeasure_closedBall hG₁ hδ hρpos hρ2 hsep₁ hp1
    have h2 :
        μ₂ (Metric.closedBall p.2 ρ) =
          (1 : ENNReal) / (G₂.card : ENNReal) :=
      smoothMeasure_closedBall hG₂ hδ hρpos hρ2 hsep₂ hp2
    rw [Measure.prod_prod, h1, h2]
    have h41 : (G₁.card : ENNReal) ≠ 0 := by
      exact_mod_cast hG₁.card_pos.ne'
    have h42 : (G₂.card : ENNReal) ≠ 0 := by
      exact_mod_cast hG₂.card_pos.ne'
    have h43 : (G₁.card : ENNReal) ≠ ⊤ := by simp
    have h44 : (G₂.card : ENNReal) ≠ ⊤ := by simp
    have h_inv :
        (G₁.card : ENNReal)⁻¹ * (G₂.card : ENNReal)⁻¹ =
          ((G₁.card : ENNReal) * (G₂.card : ENNReal))⁻¹ := by
      apply ENNReal.eq_inv_of_mul_eq_one_left
      calc
        ((G₁.card : ENNReal)⁻¹ * (G₂.card : ENNReal)⁻¹) *
              ((G₁.card : ENNReal) * (G₂.card : ENNReal))
            =
          (G₁.card : ENNReal)⁻¹ * (G₁.card : ENNReal) *
              ((G₂.card : ENNReal)⁻¹ * (G₂.card : ENNReal)) := by ring
        _ = 1 := by
          rw [ENNReal.inv_mul_cancel h41 h43,
            ENNReal.inv_mul_cancel h42 h44]
          ring
    simp [div_eq_mul_inv, hdenom, h_inv]
  rw [Finset.sum_congr rfl h_cell_measure]
  have h_sum :
      ∑ _p ∈ E, ((1 : ENNReal) / denom) =
        (E.card : ENNReal) / denom := by
    simp [Finset.sum_const, div_eq_mul_inv]
  rw [h_sum]
  have h_card_pos1 : (G₁.card : ENNReal) ≠ 0 := by
    exact_mod_cast hG₁.card_pos.ne'
  have h_card_pos2 : (G₂.card : ENNReal) ≠ 0 := by
    exact_mod_cast hG₂.card_pos.ne'
  have hdenom_pos : denom ≠ 0 :=
    mul_ne_zero h_card_pos1 h_card_pos2
  have hdenom_top : denom ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) (by simp)
  have h_ineq :
      (1 - ENNReal.ofReal c) * denom ≤ (E.card : ENNReal) := by
    simpa [mul_assoc, hdenom] using hmass
  by_contra h
  have h' :
      (E.card : ENNReal) / denom < 1 - ENNReal.ofReal c :=
    lt_of_not_ge h
  have h'' :
      ((E.card : ENNReal) / denom) * denom <
        (1 - ENNReal.ofReal c) * denom := by
    gcongr
  have h3 :
      ((E.card : ENNReal) / denom) * denom =
        (E.card : ENNReal) := by
    rw [mul_comm]
    exact ENNReal.mul_div_cancel hdenom_pos hdenom_top
  rw [h3] at h''
  exact not_le.mpr h'' h_ineq

private lemma thickening_enlargement_parallel_lines
    {b₁ a₁ : Point2} {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r)
    (hdist : dist b₁ a₁ ≤ ρ)
    {ℓ ℓ' : AffineSubspace ℝ Point2}
    (hb₁ : b₁ ∈ (ℓ : Set Point2))
    (ha₁ : a₁ ∈ (ℓ' : Set Point2))
    (hparallel : ℓ.direction = ℓ'.direction)
    (hfin : Module.finrank ℝ ℓ.direction = 1)
    {a₂ : Point2} {y : Point2} (hy : ‖y‖ < ρ)
    (h_in : a₂ + y ∈ Metric.thickening r (ℓ : Set Point2)) :
    a₂ ∈ Metric.thickening (r + 2 * ρ) (ℓ' : Set Point2) := by
  rcases Metric.mem_thickening_iff.mp h_in with
    ⟨q, hq, hdist_q⟩
  have h1 : q - b₁ ∈ ℓ.direction :=
    AffineSubspace.vsub_mem_direction hq hb₁
  have h2 : q - b₁ ∈ ℓ'.direction := by
    rw [←hparallel]
    exact h1
  let q' : Point2 := a₁ + (q - b₁)
  have hq'_in : q' ∈ (ℓ' : Set Point2) := by
    have h :
        (q - b₁) +ᵥ a₁ ∈ (ℓ' : Set Point2) :=
      AffineSubspace.vadd_mem_of_mem_direction h2 ha₁
    simpa [q', vadd_eq_add, add_comm] using h
  have h_dist_q_q' : dist q q' ≤ ρ := by
    have h3 : q' - q = a₁ - b₁ := by
      simp [q']
      abel
    have h4 : dist q q' = ‖q - q'‖ := by
      rw [dist_eq_norm]
    rw [h4]
    have h5 : ‖q - q'‖ = ‖q' - q‖ := by
      rw [←norm_neg]
      simp
    rw [h5, h3]
    have h6 : ‖a₁ - b₁‖ = dist a₁ b₁ := by rfl
    rw [h6, dist_comm]
    exact hdist
  apply Metric.mem_thickening_iff.mpr
  refine ⟨q', hq'_in, ?_⟩
  calc
    dist a₂ q'
        ≤ dist a₂ (a₂ + y) + dist (a₂ + y) q + dist q q' := by
      calc
        dist a₂ q'
            ≤ dist a₂ (a₂ + y) + dist (a₂ + y) q' :=
          dist_triangle _ _ _
        _ ≤ dist a₂ (a₂ + y) +
              (dist (a₂ + y) q + dist q q') := by
          gcongr
          exact dist_triangle _ _ _
        _ = _ := by ring
    _ < r + 2 * ρ := by
      have h7 : dist a₂ (a₂ + y) = ‖y‖ := by
        simp [dist_eq_norm]
      rw [h7]
      linarith

private lemma ballUniformMeasure_thickening_bound
    {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r)
    {ℓ : AffineSubspace ℝ Point2}
    (hfin : Module.finrank ℝ ℓ.direction = 1)
    (p : Point2) (hp : p ∈ (ℓ : Set Point2))
    (a₂ : Point2) :
    (ballUniformMeasure ρ hρ : Measure Point2)
        {y : Point2 |
          a₂ + y ∈ Metric.thickening r (ℓ : Set Point2)} ≤
      ENNReal.ofReal (4 * r / (Real.pi * ρ)) := by
  obtain ⟨n, hn, hn_orth⟩ :=
    exists_unit_normal_of_finrank_one hfin
  let t : ℝ := inner ℝ p n
  have h_strip :
      Metric.thickening r (ℓ : Set Point2) ⊆
        {z : Point2 | |inner ℝ z n - t| ≤ r} :=
    thickening_subset_strip hfin n hn hn_orth p hp r hr
  let t' : ℝ := t - inner ℝ a₂ n
  have h_subset :
      {y : Point2 |
        a₂ + y ∈ Metric.thickening r (ℓ : Set Point2)} ⊆
        {y : Point2 | |inner ℝ y n - t'| ≤ r} := by
    intro y hy
    have h10 : |inner ℝ (a₂ + y) n - t| ≤ r := h_strip hy
    have h11 : inner ℝ (a₂ + y) n =
        inner ℝ a₂ n + inner ℝ y n := by
      rw [inner_add_left]
    rw [h11] at h10
    have h12 :
        inner ℝ a₂ n + inner ℝ y n - t =
          inner ℝ y n - t' := by
      simp [t']
      ring
    rw [h12] at h10
    exact h10
  exact
    (measure_mono h_subset).trans
      (ballUniformMeasure_strip_bound hρ hr n hn t')

private lemma ballUniformMeasure_ball_full {ρ : ℝ} (hρ : 0 < ρ) :
    (ballUniformMeasure ρ hρ : Measure Point2)
        (Metric.ball (0 : Point2) ρ) = 1 := by
  let ball : Set Point2 := Metric.ball (0 : Point2) ρ
  have h_vol :
      volume ball =
        ENNReal.ofReal ρ ^ 2 * ENNReal.ofReal Real.pi :=
    EuclideanSpace.volume_ball_fin_two (0 : Point2) ρ
  have h_total_pos : 0 < volume ball := by
    rw [h_vol]
    positivity
  have h_total_ne_top : volume ball ≠ ⊤ := by
    rw [h_vol]
    have h1 : ENNReal.ofReal ρ ≠ ⊤ := ENNReal.ofReal_ne_top
    exact ENNReal.mul_ne_top
      (by simpa [pow_two] using ENNReal.mul_ne_top h1 h1)
      ENNReal.ofReal_ne_top
  rw [show (ballUniformMeasure ρ hρ : Measure Point2) =
      (volume ball)⁻¹ • volume.restrict ball by rfl]
  rw [Measure.smul_apply, Measure.restrict_apply isOpen_ball.measurableSet]
  rw [inter_self]
  exact ENNReal.inv_mul_cancel h_total_pos.ne' h_total_ne_top

private lemma le_rpow_of_le_one
    {x β : ℝ} (hx_pos : 0 < x) (hx_one : x ≤ 1)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    x ≤ x ^ β := by
  by_cases h0 : x = 1
  · simp [h0]
  · have hx_lt_one : x < 1 := lt_of_le_of_ne hx_one h0
    have h_log_neg : Real.log x < 0 :=
      Real.log_neg hx_pos hx_lt_one
    have h_ineq : Real.log x ≤ β * Real.log x := by
      nlinarith
    have h_log_rpow : Real.log (x ^ β) = β * Real.log x :=
      Real.log_rpow hx_pos β
    have h4 : Real.log x ≤ Real.log (x ^ β) := by
      rwa [h_log_rpow]
    exact
      (Real.log_le_log_iff hx_pos (by positivity)).mp h4

private lemma r_delta_ineq
    {r δ β : ℝ} (hr : 0 < r) (hδ : 0 < δ) (hr_lt : r < δ)
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    r * δ ^ (β - 1) ≤ r ^ β := by
  let x : ℝ := r / δ
  have hx_pos : 0 < x := by positivity
  have hx_one : x ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    linarith
  have h1 : x ≤ x ^ β :=
    le_rpow_of_le_one hx_pos hx_one hβ0 hβ1
  have h2 : x ^ β = r ^ β / δ ^ β := by
    dsimp only [x]
    rw [Real.div_rpow (by positivity) (by positivity)]
  have h3 : r * δ ^ (β - 1) = x * δ ^ β := by
    have h4 : δ ^ (β - 1) = δ ^ β / δ := by
      rw [show β - 1 = β + (-1 : ℝ) by ring,
        Real.rpow_add (by positivity)]
      rw [Real.rpow_neg (by positivity)]
      simp
      ring
    rw [h4]
    dsimp only [x]
    ring
  rw [h3]
  have h5 : x * δ ^ β ≤ (x ^ β) * δ ^ β := by
    gcongr <;> positivity
  rw [h2] at h5
  have h6 : (r ^ β / δ ^ β) * δ ^ β = r ^ β := by
    field_simp [hδ.ne'] <;> ring
  rw [h6] at h5
  exact h5

private lemma smoothedExceptionalSet_fiber
    {G₁ G₂ : DiscreteSet 2} {δ ρ : ℝ} (hδ : 0 < δ)
    (hρ2 : 2 * ρ < δ)
    (hsep₁ : G₁.IsDeltaSeparated δ) (hsep₂ : G₂.IsDeltaSeparated δ)
    {E : Finset (Point2 × Point2)} (hE : E ⊆ G₁ ×ˢ G₂)
    {a₁ : Point2} (ha₁ : a₁ ∈ G₁) {a₂ : Point2} (ha₂ : a₂ ∈ G₂)
    {b₁ : Point2} (hb₁ : b₁ ∈ Metric.closedBall a₁ ρ)
    {z : Point2} (hz : z ∈ Metric.closedBall a₂ ρ) :
    (b₁, z) ∈ smoothedExceptionalSet E ρ ↔ (a₁, a₂) ∈ E := by
  constructor
  · intro h
    simp only [smoothedExceptionalSet, Set.mem_iUnion] at h
    rcases h with ⟨p, hp, hb₁p, hzp⟩
    have hp1 : p.1 ∈ G₁ := (Finset.mem_product.mp (hE hp)).1
    have hp2 : p.2 ∈ G₂ := (Finset.mem_product.mp (hE hp)).2
    have h_eq1 : p.1 = a₁ := by
      by_contra hne
      exact
        Set.disjoint_left.mp
          (closedBall_disjoint_of_deltaSeparated
            hρ2 hsep₁ hp1 ha₁ hne)
          hb₁p hb₁
    have h_eq2 : p.2 = a₂ := by
      by_contra hne
      exact
        Set.disjoint_left.mp
          (closedBall_disjoint_of_deltaSeparated
            hρ2 hsep₂ hp2 ha₂ hne)
          hzp hz
    have : p = (a₁, a₂) := Prod.ext h_eq1 h_eq2
    rwa [this] at hp
  · intro h
    simp only [smoothedExceptionalSet, Set.mem_iUnion]
    exact ⟨(a₁, a₂), h, hb₁, hz⟩

private lemma smoothed_thin_tube_bound
    {δ β K c : ℝ} (hδ : 0 < δ) (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ 1) (hK : 1 ≤ K)
    {G₁ G₂ : DiscreteSet 2} (hG₁ : G₁.Nonempty) (hG₂ : G₂.Nonempty)
    (hsep₁ : G₁.IsDeltaSeparated δ) (hsep₂ : G₂.IsDeltaSeparated δ)
    {E : Finset (Point2 × Point2)} (hE : E ⊆ G₁ ×ˢ G₂)
    (h_thin : ∀ b₁ ∈ G₁, ∀ ℓ : AffineSubspace ℝ Point2,
      b₁ ∈ (ℓ : Set Point2) → Module.finrank ℝ ℓ.direction = 1 →
      ∀ r : ℝ, δ ≤ r →
        ((G₂.filter fun b₂ =>
          b₂ ∈ Metric.thickening r (ℓ : Set Point2) ∧
          (b₁, b₂) ∈ E).card : ENNReal) ≤
          ENNReal.ofReal (K * r ^ β) * (G₂.card : ENNReal))
    {ρ : ℝ} (hρ : 0 < ρ) (hρ2 : 2 * ρ < δ)
    (hρ_eq : ρ = δ / 10)
    {μ₁ μ₂ : Measure Point2}
    (hμ₁ : μ₁ = smoothMeasure G₁ hG₁ ρ hρ)
    (hμ₂ : μ₂ = smoothMeasure G₂ hG₂ ρ hρ)
    {b₁ : Point2} (hb₁_supp : b₁ ∈ μ₁.support)
    {ℓ : AffineSubspace ℝ Point2} (hb₁_in : b₁ ∈ (ℓ : Set Point2))
    (hfin : Module.finrank ℝ ℓ.direction = 1)
    {r : ℝ} (hr : 0 < r) :
    μ₂ {b₂ : Point2 |
      b₂ ∈ Metric.thickening r (ℓ : Set Point2) ∧
      (b₁, b₂) ∈ smoothedExceptionalSet E ρ} ≤
      ENNReal.ofReal (100 * K * r ^ β) := by
  set E' := smoothedExceptionalSet E ρ with hE'_def
  set S : Set Point2 :=
    {b₂ |
      b₂ ∈ Metric.thickening r (ℓ : Set Point2) ∧
      (b₁, b₂) ∈ E'} with hS_def
  have h_supp1 :
      μ₁.support ⊆ ⋃ a ∈ G₁, Metric.closedBall a ρ := by
    rw [hμ₁]
    exact smoothMeasure_support_subset
  rcases Set.mem_iUnion₂.mp (h_supp1 hb₁_supp) with
    ⟨a₁, ha₁, hb₁_cell⟩
  let ℓ' : AffineSubspace ℝ Point2 :=
    AffineSubspace.mk' a₁ ℓ.direction
  have hparallel : ℓ.direction = ℓ'.direction := by simp [ℓ']
  have ha₁_in_ℓ' : a₁ ∈ (ℓ' : Set Point2) := by
    simpa [ℓ'] using AffineSubspace.mk'_mem a₁ ℓ.direction
  have h_dist_a1_b1 : dist b₁ a₁ ≤ ρ :=
    Metric.mem_closedBall.mp hb₁_cell
  have hE'_meas : MeasurableSet E' :=
    smoothedExceptionalSet_measurable E ρ
  have hS_meas : MeasurableSet S := by
    exact Metric.isOpen_thickening.measurableSet.inter
      (hE'_meas.preimage
        (show Measurable (fun b₂ : Point2 => (b₁, b₂)) from by fun_prop))
  let σ := ballUniformMeasure ρ hρ
  let ball := Metric.ball (0 : Point2) ρ
  have hσ_ball : (σ : Measure Point2) ball = 1 :=
    ballUniformMeasure_ball_full hρ
  have hσ_ball_compl : (σ : Measure Point2) ballᶜ = 0 := by
    have h_def :
        (σ : Measure Point2) =
          (volume ball)⁻¹ • volume.restrict ball := by
      rfl
    rw [h_def, Measure.smul_apply]
    have h_ball_meas : MeasurableSet ball := isOpen_ball.measurableSet
    rw [Measure.restrict_apply h_ball_meas.compl]
    simp
  have h_restrict_eq : ∀ (T : Set Point2), MeasurableSet T →
      (σ : Measure Point2) T =
        (σ : Measure Point2) (T ∩ ball) := by
    intro T hT
    have h_ball_meas : MeasurableSet ball := isOpen_ball.measurableSet
    have h_union : (T ∩ ball) ∪ (T \ ball) = T := by
      rw [Set.union_comm, Set.diff_union_inter]
    have h_disj : Disjoint (T ∩ ball) (T \ ball) :=
      Disjoint.symm disjoint_sdiff_inter
    have h_meas_diff : MeasurableSet (T \ ball) :=
      hT.diff h_ball_meas
    have h5 :
        (σ : Measure Point2) T =
          (σ : Measure Point2) (T ∩ ball) +
            (σ : Measure Point2) (T \ ball) := by
      have h_eq :
          (σ : Measure Point2) ((T ∩ ball) ∪ (T \ ball)) =
            (σ : Measure Point2) (T ∩ ball) +
              (σ : Measure Point2) (T \ ball) :=
        measure_union h_disj h_meas_diff
      rw [h_union] at h_eq
      exact h_eq
    rw [h5]
    have h6 : (σ : Measure Point2) (T \ ball) = 0 :=
      measure_mono_null
        (show T \ ball ⊆ ballᶜ by simp [Set.diff_subset_iff])
        hσ_ball_compl
    simp [h6]
  have h_term_char : ∀ (a₂ : Point2), a₂ ∈ G₂ →
      (σ : Measure Point2) {y : Point2 | a₂ + y ∈ S} =
        if (a₁, a₂) ∈ E then
          (σ : Measure Point2)
            {y : Point2 |
              a₂ + y ∈ Metric.thickening r (ℓ : Set Point2)}
        else 0 := by
    intro a₂ ha₂
    by_cases h_good : (a₁, a₂) ∈ E
    · let T1 := {y : Point2 | a₂ + y ∈ S}
      let T2 :=
        {y : Point2 |
          a₂ + y ∈ Metric.thickening r (ℓ : Set Point2)}
      have hT1_meas : MeasurableSet T1 :=
        hS_meas.preimage (by fun_prop)
      have hT2_meas : MeasurableSet T2 :=
        Metric.isOpen_thickening.measurableSet.preimage (by fun_prop)
      have h_iff : ∀ (y : Point2), y ∈ ball →
          (a₂ + y ∈ S ↔
            a₂ + y ∈ Metric.thickening r (ℓ : Set Point2)) := by
        intro y hy
        have h_ynorm : ‖y‖ < ρ := by
          simpa [ball, Metric.mem_ball, dist_zero_right] using hy
        have h_y_in_cell : a₂ + y ∈ Metric.closedBall a₂ ρ := by
          simp [Metric.mem_closedBall, dist_eq_norm]
          linarith
        have h_fiber :
            (b₁, a₂ + y) ∈ E' ↔ (a₁, a₂) ∈ E :=
          smoothedExceptionalSet_fiber
            hδ hρ2 hsep₁ hsep₂ hE ha₁ ha₂ hb₁_cell h_y_in_cell
        simp only [hS_def, Set.mem_setOf_eq]
        rw [h_fiber]
        simp [h_good]
      have h_set_eq : T1 ∩ ball = T2 ∩ ball := by
        ext y
        simp only [Set.mem_inter_iff]
        exact and_congr_left (fun hy => h_iff y hy)
      rw [h_restrict_eq T1 hT1_meas,
        h_restrict_eq T2 hT2_meas, h_set_eq]
      simp [h_good]
    · have h_subset :
          {y : Point2 | a₂ + y ∈ S} ⊆ ballᶜ := by
        intro y hy
        by_contra hnot
        have hyball : y ∈ ball := by simpa [ball] using hnot
        have h_y_in_cell : a₂ + y ∈ Metric.closedBall a₂ ρ := by
          have h_ynorm : ‖y‖ < ρ := by
            simpa [ball, Metric.mem_ball, dist_zero_right] using hyball
          simp [Metric.mem_closedBall, dist_eq_norm]
          linarith
        exact h_good
          ((smoothedExceptionalSet_fiber
            hδ hρ2 hsep₁ hsep₂ hE ha₁ ha₂
            hb₁_cell h_y_in_cell).mp hy.2)
      have h_null :
          (σ : Measure Point2) {y : Point2 | a₂ + y ∈ S} = 0 :=
        measure_mono_null h_subset hσ_ball_compl
      simp [h_null, h_good]
  have h_enlargement_zero : ∀ (a₂ : Point2), a₂ ∈ G₂ →
      a₂ ∉ Metric.thickening (r + 2 * ρ) (ℓ' : Set Point2) →
        (σ : Measure Point2)
          {y : Point2 |
            a₂ + y ∈ Metric.thickening r (ℓ : Set Point2)} = 0 := by
    intro a₂ _ h_not_in
    apply measure_mono_null _ hσ_ball_compl
    intro y hy
    by_contra hnot
    have hyball : y ∈ ball := by simpa [ball] using hnot
    have h_ynorm : ‖y‖ < ρ := by
      simpa [ball, Metric.mem_ball, dist_zero_right] using hyball
    exact h_not_in
      (thickening_enlargement_parallel_lines
        hρ hr h_dist_a1_b1 hb₁_in ha₁_in_ℓ'
        hparallel hfin h_ynorm hy)
  let C : Finset Point2 :=
    G₂.filter fun a₂ =>
      a₂ ∈ Metric.thickening (r + 2 * ρ) (ℓ' : Set Point2) ∧
        (a₁, a₂) ∈ E
  have h_sum_bound :
      ∑ a₂ ∈ G₂, (σ : Measure Point2)
          {y : Point2 | a₂ + y ∈ S} ≤
        ∑ a₂ ∈ C, (σ : Measure Point2)
          {y : Point2 |
            a₂ + y ∈ Metric.thickening r (ℓ : Set Point2)} := by
    have h4 : ∀ a₂ ∈ G₂, a₂ ∉ C →
        (σ : Measure Point2) {y : Point2 | a₂ + y ∈ S} = 0 := by
      intro a₂ ha₂ hnotC
      by_cases h_good : (a₁, a₂) ∈ E
      · have h_not_in :
            a₂ ∉ Metric.thickening (r + 2 * ρ) (ℓ' : Set Point2) := by
          intro hin
          exact hnotC (Finset.mem_filter.mpr ⟨ha₂, hin, h_good⟩)
        rw [h_term_char a₂ ha₂]
        simp [h_good, h_enlargement_zero a₂ ha₂ h_not_in]
      · rw [h_term_char a₂ ha₂]
        simp [h_good]
    have h3 :
        ∑ a₂ ∈ G₂, (σ : Measure Point2)
            {y : Point2 | a₂ + y ∈ S} =
          ∑ a₂ ∈ C, (σ : Measure Point2)
            {y : Point2 | a₂ + y ∈ S} := by
      rw [Finset.sum_subset (Finset.filter_subset _ _) h4]
    rw [h3]
    apply Finset.sum_le_sum
    intro a₂ ha₂
    have h_good : (a₁, a₂) ∈ E :=
      (Finset.mem_filter.mp ha₂).2.2
    rw [h_term_char a₂ (Finset.mem_filter.mp ha₂).1]
    simp [h_good]
  have h_decomp :
      μ₂ S =
        (G₂.card : ENNReal)⁻¹ *
          ∑ a₂ ∈ G₂, (σ : Measure Point2)
            {y : Point2 | a₂ + y ∈ S} := by
    rw [hμ₂]
    exact smoothMeasure_apply hS_meas
  rw [h_decomp]
  have hpos : (G₂.card : ENNReal) ≠ 0 := by
    exact_mod_cast hG₂.card_pos.ne'
  have htop : (G₂.card : ENNReal) ≠ ⊤ := by simp
  by_cases h_case : δ ≤ r
  · have h_r2ρ_ge_delta : δ ≤ r + 2 * ρ := by linarith
    have h_C_bound :
        (C.card : ENNReal) ≤
          ENNReal.ofReal (K * (r + 2 * ρ) ^ β) *
            (G₂.card : ENNReal) := by
      have hfin' : Module.finrank ℝ ℓ'.direction = 1 := by
        rw [←hparallel]
        exact hfin
      have h_discrete :=
        h_thin a₁ ha₁ ℓ' ha₁_in_ℓ' hfin'
          (r + 2 * ρ) h_r2ρ_ge_delta
      simpa [C] using h_discrete
    have h_each_le_one : ∀ a₂ ∈ C,
        (σ : Measure Point2)
          {y : Point2 |
            a₂ + y ∈ Metric.thickening r (ℓ : Set Point2)} ≤ 1 := by
      intro a₂ _
      exact (measure_mono (Set.subset_univ _)).trans_eq measure_univ
    have h_sum_le_C :
        ∑ a₂ ∈ C, (σ : Measure Point2)
            {y : Point2 |
              a₂ + y ∈ Metric.thickening r (ℓ : Set Point2)} ≤
          (C.card : ENNReal) := by
      simpa using Finset.sum_le_sum h_each_le_one
    have h5 :
        (G₂.card : ENNReal)⁻¹ *
            ∑ a₂ ∈ C, (σ : Measure Point2)
              {y : Point2 |
                a₂ + y ∈ Metric.thickening r (ℓ : Set Point2)} ≤
          (G₂.card : ENNReal)⁻¹ * (C.card : ENNReal) := by
      gcongr
    set y : ENNReal :=
      ENNReal.ofReal (K * (r + 2 * ρ) ^ β)
    set x : ENNReal := (G₂.card : ENNReal)
    have h_eq : x⁻¹ * (y * x) = y := by
      calc
        x⁻¹ * (y * x) = y * (x⁻¹ * x) := by
          simp [mul_assoc, mul_comm, mul_left_comm]
        _ = y := by rw [ENNReal.inv_mul_cancel hpos htop]; simp
    have h6 : x⁻¹ * (C.card : ENNReal) ≤ y := by
      calc
        x⁻¹ * (C.card : ENNReal) ≤ x⁻¹ * (y * x) := by gcongr
        _ = y := h_eq
    have h7 :
        K * (r + 2 * ρ) ^ β ≤ 100 * K * r ^ β := by
      have h8 : r + 2 * ρ ≤ (6 / 5 : ℝ) * r := by
        rw [hρ_eq]
        linarith
      have h10 :
          (r + 2 * ρ) ^ β ≤ (6 / 5 : ℝ) ^ β * r ^ β := by
        calc
          (r + 2 * ρ) ^ β ≤ ((6 / 5 : ℝ) * r) ^ β := by
            gcongr
          _ = (6 / 5 : ℝ) ^ β * r ^ β := by
            rw [Real.mul_rpow (by norm_num) (by positivity)]
      have h12 : (6 / 5 : ℝ) ^ β ≤ (6 / 5 : ℝ) :=
        Real.rpow_le_self_of_one_le (by norm_num) hβ1
      calc
        K * (r + 2 * ρ) ^ β
            ≤ K * ((6 / 5 : ℝ) ^ β * r ^ β) := by gcongr
        _ ≤ K * ((6 / 5 : ℝ) * r ^ β) := by gcongr
        _ ≤ 100 * K * r ^ β := by
          have : 0 ≤ K * r ^ β := by positivity
          nlinarith
    have h_sum_bound2 :
        (G₂.card : ENNReal)⁻¹ *
            ∑ a₂ ∈ G₂, (σ : Measure Point2)
              {y : Point2 | a₂ + y ∈ S} ≤
          (G₂.card : ENNReal)⁻¹ *
            ∑ a₂ ∈ C, (σ : Measure Point2)
              {y : Point2 |
                a₂ + y ∈ Metric.thickening r (ℓ : Set Point2)} :=
      mul_le_mul_left' h_sum_bound _
    exact
      (h_sum_bound2.trans (h5.trans (by simpa [x, y] using h6))).trans
        (ENNReal.ofReal_le_ofReal h7)
  · have h_r_lt_delta : r < δ := by linarith
    set R : ℝ := 6 * δ / 5 with hR_def
    have hR_ge_delta : δ ≤ R := by
      rw [hR_def]
      linarith
    have h_r2ρ_le_R : r + 2 * ρ ≤ R := by
      rw [hρ_eq, hR_def]
      linarith
    have h_C_subset :
        C ⊆ G₂.filter fun b₂ =>
          b₂ ∈ Metric.thickening R (ℓ' : Set Point2) ∧
          (a₁, b₂) ∈ E := by
      intro a₂ ha₂
      exact Finset.mem_filter.mpr
        ⟨(Finset.mem_filter.mp ha₂).1,
          Metric.thickening_mono h_r2ρ_le_R _
            (Finset.mem_filter.mp ha₂).2.1,
          (Finset.mem_filter.mp ha₂).2.2⟩
    have h_C_bound :
        (C.card : ENNReal) ≤
          ENNReal.ofReal (K * R ^ β) * (G₂.card : ENNReal) := by
      have hfin' : Module.finrank ℝ ℓ'.direction = 1 := by
        rw [←hparallel]
        exact hfin
      have h_discrete :=
        h_thin a₁ ha₁ ℓ' ha₁_in_ℓ' hfin' R hR_ge_delta
      exact le_trans
        (mod_cast Finset.card_le_card h_C_subset) h_discrete
    have h_strip_bound : ∀ a₂ ∈ C,
        (σ : Measure Point2)
            {y : Point2 |
              a₂ + y ∈ Metric.thickening r (ℓ : Set Point2)} ≤
          ENNReal.ofReal (4 * r / (Real.pi * ρ)) := by
      intro a₂ _
      exact ballUniformMeasure_thickening_bound hρ hr hfin b₁ hb₁_in a₂
    have h_sum_le :
        ∑ a₂ ∈ C, (σ : Measure Point2)
            {y : Point2 |
              a₂ + y ∈ Metric.thickening r (ℓ : Set Point2)} ≤
          (C.card : ENNReal) *
            ENNReal.ofReal (4 * r / (Real.pi * ρ)) := by
      calc
        _ ≤ ∑ a₂ ∈ C,
              ENNReal.ofReal (4 * r / (Real.pi * ρ)) :=
          Finset.sum_le_sum h_strip_bound
        _ = _ := by simp [Finset.sum_const]
    have h5 :
        (G₂.card : ENNReal)⁻¹ *
            ∑ a₂ ∈ C, (σ : Measure Point2)
              {y : Point2 |
                a₂ + y ∈ Metric.thickening r (ℓ : Set Point2)} ≤
          (G₂.card : ENNReal)⁻¹ *
            ((C.card : ENNReal) *
              ENNReal.ofReal (4 * r / (Real.pi * ρ))) := by
      gcongr
    set y2 : ENNReal := ENNReal.ofReal (K * R ^ β)
    set x2 : ENNReal := (G₂.card : ENNReal)
    set X : ENNReal := ENNReal.ofReal (4 * r / (Real.pi * ρ))
    have h6 :
        x2⁻¹ * ((C.card : ENNReal) * X) ≤ y2 * X := by
      calc
        x2⁻¹ * ((C.card : ENNReal) * X)
            ≤ x2⁻¹ * ((y2 * x2) * X) := by gcongr
        _ = y2 * X := by
          have h1 :
              x2⁻¹ * ((y2 * x2) * X) =
                y2 * (x2⁻¹ * x2) * X := by
            simp only [mul_assoc]
            ac_rfl
          rw [h1, ENNReal.inv_mul_cancel hpos htop]
          simp
    have h_pos1 : 0 ≤ K * R ^ β := by positivity
    have h7 :
        ENNReal.ofReal (K * R ^ β) *
            ENNReal.ofReal (4 * r / (Real.pi * ρ)) =
          ENNReal.ofReal
            ((K * R ^ β) * (4 * r / (Real.pi * ρ))) := by
      rw [← ENNReal.ofReal_mul h_pos1]
    rw [h7] at h6
    have h8 :
        (K * R ^ β) * (4 * r / (Real.pi * ρ)) ≤
          100 * K * r ^ β := by
      have hR : R = (6 / 5 : ℝ) * δ := by
        rw [hR_def]
        ring
      have h10 :
          ((6 / 5 : ℝ) * δ) ^ β =
            (6 / 5 : ℝ) ^ β * δ ^ β := by
        rw [Real.mul_rpow (by norm_num) (by positivity)]
      have h11 :
          δ ^ β * (4 * r / (Real.pi * (δ / 10))) =
            (40 / Real.pi) * (r * δ ^ (β - 1)) := by
        have h12 :
            4 * r / (Real.pi * (δ / 10)) =
              (40 / Real.pi) * (r / δ) := by
          field_simp [hδ.ne']
          ring
        have h15 : δ ^ β / δ = δ ^ (β - 1) := by
          have h_mult : δ ^ (β - 1) * δ = δ ^ β := by
            have h1 :
                δ ^ (β - 1) * δ =
                  δ ^ (β - 1) * δ ^ (1 : ℝ) := by simp
            rw [h1]
            have h2 :
                δ ^ ((β - 1) + (1 : ℝ)) =
                  δ ^ (β - 1) * δ ^ (1 : ℝ) :=
              Real.rpow_add hδ (β - 1) (1 : ℝ)
            have h3 : (β - 1) + (1 : ℝ) = β := by ring
            have h4 :
                δ ^ (β - 1) * δ ^ (1 : ℝ) =
                  δ ^ ((β - 1) + (1 : ℝ)) :=
              h2.symm
            rw [h4, h3]
          calc
            δ ^ β / δ
                = (δ ^ (β - 1) * δ) / δ := by rw [h_mult]
            _ = δ ^ (β - 1) := by
              field_simp [hδ.ne'] <;> ring
        calc
          δ ^ β * (4 * r / (Real.pi * (δ / 10)))
              = δ ^ β * ((40 / Real.pi) * (r / δ)) := by rw [h12]
          _ = (40 / Real.pi) * (δ ^ β * (r / δ)) := by ring
          _ = (40 / Real.pi) * (r * (δ ^ β / δ)) := by ring
          _ = (40 / Real.pi) * (r * δ ^ (β - 1)) := by rw [h15]
      have h_expr :
          (K * ((6 / 5 : ℝ) ^ β * δ ^ β)) *
              (4 * r / (Real.pi * (δ / 10))) =
            K * (6 / 5 : ℝ) ^ β * (40 / Real.pi) *
              (r * δ ^ (β - 1)) := by
        have h_intermediate :
            K * ((6 / 5 : ℝ) ^ β * δ ^ β) *
                (4 * r / (Real.pi * (δ / 10))) =
              K * (6 / 5 : ℝ) ^ β *
                (δ ^ β * (4 * r / (Real.pi * (δ / 10)))) := by
          ring
        rw [h_intermediate, h11]
        ring
      rw [hR, hρ_eq, h10]
      rw [h_expr]
      have h11' :
          r * δ ^ (β - 1) ≤ r ^ β :=
        r_delta_ineq hr hδ h_r_lt_delta hβ0 hβ1
      have h12' : (6 / 5 : ℝ) ^ β ≤ 6 / 5 :=
        Real.rpow_le_self_of_one_le (by norm_num) hβ1
      have h19 : (6 / 5 : ℝ) * (40 / Real.pi) ≤ 100 := by
        have hpi3 : 3 < Real.pi := Real.pi_gt_three
        have hpospi : 0 < Real.pi := Real.pi_pos
        rw [show (6 / 5 : ℝ) * (40 / Real.pi) = 48 / Real.pi by ring]
        apply (div_le_iff₀ hpospi).mpr
        linarith
      calc
        K * (6 / 5 : ℝ) ^ β * (40 / Real.pi) *
              (r * δ ^ (β - 1))
            ≤ K * (6 / 5 : ℝ) * (40 / Real.pi) * r ^ β := by
          gcongr
        _ ≤ 100 * K * r ^ β := by
          have hnonneg : 0 ≤ K * r ^ β := by positivity
          nlinarith
    have h_sum_bound3 :
        (G₂.card : ENNReal)⁻¹ *
            ∑ a₂ ∈ G₂, (σ : Measure Point2)
              {y : Point2 | a₂ + y ∈ S} ≤
          (G₂.card : ENNReal)⁻¹ *
            ∑ a₂ ∈ C, (σ : Measure Point2)
              {y : Point2 |
                a₂ + y ∈ Metric.thickening r (ℓ : Set Point2)} :=
      mul_le_mul_left' h_sum_bound _
    exact
      (h_sum_bound3.trans (h5.trans (by simpa [x2, y2, X] using h6))).trans
        (ENNReal.ofReal_le_ofReal h8)

theorem wz1_discrete_to_smoothed_thin_tubes :
    WZ1DiscreteToSmoothedThinTubesStatement := by
  intro δ β K c G₁ G₂ hG₁ hG₂ hδ hβ1 hsep₁ hsep₂ hdisc
  rcases hdisc with
    ⟨hβ, hK, hc, E, hE_sub, hE_mass, h_thin⟩
  set ρ : ℝ := δ / 10 with hρ_def
  have hρpos : 0 < ρ := by linarith
  have hρ2 : 2 * ρ < δ := by linarith
  let ν₁ : ProbabilityMeasure Point2 :=
    smoothMeasure G₁ hG₁ ρ hρpos
  let ν₂ : ProbabilityMeasure Point2 :=
    smoothMeasure G₂ hG₂ ρ hρpos
  let μ₁ : Measure Point2 := ν₁
  let μ₂ : Measure Point2 := ν₂
  let E' : Set (Point2 × Point2) :=
    smoothedExceptionalSet E ρ
  have hE'_meas : MeasurableSet E' :=
    smoothedExceptionalSet_measurable E ρ
  have h_supp1_meas : MeasurableSet μ₁.support :=
    Measure.isClosed_support.measurableSet
  have h_supp2_meas : MeasurableSet μ₂.support :=
    Measure.isClosed_support.measurableSet
  have h_supp_prod_meas :
      MeasurableSet (μ₁.support ×ˢ μ₂.support) :=
    h_supp1_meas.prod h_supp2_meas
  let E'' : Set (Point2 × Point2) :=
    E' ∩ (μ₁.support ×ˢ μ₂.support)
  have hE''_meas : MeasurableSet E'' :=
    hE'_meas.inter h_supp_prod_meas
  have hE''_sub :
      E'' ⊆ μ₁.support ×ˢ μ₂.support :=
    Set.inter_subset_right
  have h_supp1_full : μ₁ μ₁.support = 1 := by
    have h1 : μ₁ μ₁.supportᶜ = 0 :=
      Measure.measure_compl_support (μ := μ₁)
    have h5 :
        μ₁ Set.univ =
          μ₁ μ₁.support + μ₁ μ₁.supportᶜ := by
      rw [show Set.univ = μ₁.support ∪ μ₁.supportᶜ by ext x; simp,
        measure_union (by simp [Set.disjoint_left])
          h_supp1_meas.compl]
    have h2 : μ₁ Set.univ = 1 := measure_univ
    rw [h5, h1] at h2
    simpa using h2
  have h_supp2_full : μ₂ μ₂.support = 1 := by
    have h1 : μ₂ μ₂.supportᶜ = 0 :=
      Measure.measure_compl_support (μ := μ₂)
    have h5 :
        μ₂ Set.univ =
          μ₂ μ₂.support + μ₂ μ₂.supportᶜ := by
      rw [show Set.univ = μ₂.support ∪ μ₂.supportᶜ by ext x; simp,
        measure_union (by simp [Set.disjoint_left])
          h_supp2_meas.compl]
    have h2 : μ₂ Set.univ = 1 := measure_univ
    rw [h5, h1] at h2
    simpa using h2
  have h_prod_supp_full :
      (μ₁.prod μ₂) (μ₁.support ×ˢ μ₂.support) = 1 := by
    rw [Measure.prod_prod, h_supp1_full, h_supp2_full]
    norm_num
  have hE''_mass_eq :
      (μ₁.prod μ₂) E'' = (μ₁.prod μ₂) E' := by
    let s := E' ∩ (μ₁.support ×ˢ μ₂.support)
    let t := E' \ (μ₁.support ×ˢ μ₂.support)
    have hs_meas : MeasurableSet s :=
      hE'_meas.inter h_supp_prod_meas
    have ht_meas : MeasurableSet t :=
      hE'_meas.diff h_supp_prod_meas
    have h_union : s ∪ t = E' := by
      ext x
      simp [s, t, Set.mem_diff]
    have h_disj : Disjoint s t := by
      simp [s, t, Set.disjoint_left, Set.mem_diff]
      tauto
    have h1 :
        (μ₁.prod μ₂) E' =
          (μ₁.prod μ₂) s + (μ₁.prod μ₂) t := by
      rw [←h_union, measure_union h_disj ht_meas]
    have h_null_supp :
        (μ₁.prod μ₂)
            (μ₁.support ×ˢ μ₂.support)ᶜ = 0 := by
      have h4 :
          (μ₁.prod μ₂) Set.univ =
            (μ₁.prod μ₂) (μ₁.support ×ˢ μ₂.support) +
              (μ₁.prod μ₂)
                (μ₁.support ×ˢ μ₂.support)ᶜ := by
        rw [show Set.univ =
            (μ₁.support ×ˢ μ₂.support) ∪
              (μ₁.support ×ˢ μ₂.support)ᶜ by ext x; simp,
          measure_union (by simp [Set.disjoint_left])
            h_supp_prod_meas.compl]
      have h_univ :
          (μ₁.prod μ₂) Set.univ = 1 := measure_univ
      rw [h4, h_prod_supp_full] at h_univ
      simpa using h_univ
    have h_null : (μ₁.prod μ₂) t = 0 :=
      measure_mono_null
        (show t ⊆ (μ₁.support ×ˢ μ₂.support)ᶜ by
          simp [t, Set.diff_subset_iff])
        h_null_supp
    rw [show E'' = s by rfl, h1, h_null]
    simp
  have hE'_mass :
      (1 - ENNReal.ofReal c) ≤ (μ₁.prod μ₂) E' :=
    smoothedExceptionalSet_mass
      hG₁ hG₂ hδ hsep₁ hsep₂ hE_sub hE_mass
  have hE''_mass :
      (1 - ENNReal.ofReal c) ≤ (μ₁.prod μ₂) E'' := by
    rwa [hE''_mass_eq]
  have h_tube_bound :
      ∀ (b₁ : Point2), b₁ ∈ μ₁.support →
      ∀ (ℓ : AffineSubspace ℝ Point2),
        b₁ ∈ (ℓ : Set Point2) →
        Module.finrank ℝ ℓ.direction = 1 →
        ∀ (r : ℝ), 0 < r →
          μ₂ {b₂ : Point2 |
            b₂ ∈ Metric.thickening r (ℓ : Set Point2) ∧
            (b₁, b₂) ∈ E'} ≤
            ENNReal.ofReal (100 * K * r ^ β) := by
    intro b₁ hb₁ ℓ hb₁_in hfin r hr
    exact
      smoothed_thin_tube_bound
        (c := c) hδ hβ hβ1 hK hG₁ hG₂
        hsep₁ hsep₂ hE_sub h_thin
        hρpos hρ2 hρ_def rfl rfl hb₁ hb₁_in hfin hr
  have h_final :
      ∀ (b₁ : Point2), b₁ ∈ μ₁.support →
      ∀ (ℓ : AffineSubspace ℝ Point2),
        b₁ ∈ (ℓ : Set Point2) →
        Module.finrank ℝ ℓ.direction = 1 →
        ∀ (r : ℝ), 0 < r →
          ν₂ {b₂ : Point2 |
            b₂ ∈ Metric.thickening r (ℓ : Set Point2) ∧
            (b₁, b₂) ∈ E''} ≤
            Real.toNNReal (100 * K * r ^ β) := by
    intro b₁ hb₁ ℓ hb₁_in hfin r hr
    let S' : Set Point2 :=
      {b₂ |
        b₂ ∈ Metric.thickening r (ℓ : Set Point2) ∧
        (b₁, b₂) ∈ E'}
    let S'' : Set Point2 :=
      {b₂ |
        b₂ ∈ Metric.thickening r (ℓ : Set Point2) ∧
        (b₁, b₂) ∈ E''}
    have hS'_meas : MeasurableSet S' :=
      Metric.isOpen_thickening.measurableSet.inter
        (hE'_meas.preimage
          (show Measurable (fun b₂ : Point2 => (b₁, b₂)) from by
            fun_prop))
    have h1 : S'' = S' ∩ μ₂.support := by
      ext b₂
      simp only [S'', S', E'', Set.mem_inter_iff, Set.mem_setOf_eq,
        Set.mem_prod]
      tauto
    let s2 := S' ∩ μ₂.support
    let t2 := S' \ μ₂.support
    have hs2_meas : MeasurableSet s2 :=
      hS'_meas.inter h_supp2_meas
    have ht2_meas : MeasurableSet t2 :=
      hS'_meas.diff h_supp2_meas
    have h_union2 : s2 ∪ t2 = S' := by
      ext x
      simp [s2, t2, Set.mem_diff]
    have h_disj2 : Disjoint s2 t2 := by
      simp [s2, t2, Set.disjoint_left, Set.mem_diff]
      tauto
    have h2 : μ₂ S' = μ₂ s2 + μ₂ t2 := by
      rw [←h_union2, measure_union h_disj2 ht2_meas]
    have h_null_supp2 : μ₂ μ₂.supportᶜ = 0 :=
      Measure.measure_compl_support
    have h_null : μ₂ t2 = 0 :=
      measure_mono_null
        (show t2 ⊆ μ₂.supportᶜ by
          simp [t2, Set.diff_subset_iff])
        h_null_supp2
    have h_eq_measure : μ₂ S'' = μ₂ S' := by
      rw [h1]
      change μ₂ s2 = μ₂ S'
      rw [h2, h_null]
      simp
    have h_bound :
        μ₂ S' ≤ ENNReal.ofReal (100 * K * r ^ β) :=
      h_tube_bound b₁ hb₁ ℓ hb₁_in hfin r hr
    have h_nonneg : 0 ≤ 100 * K * r ^ β := by positivity
    have h9 :
        ENNReal.ofReal (100 * K * r ^ β) =
          ↑(Real.toNNReal (100 * K * r ^ β)) := by
      rw [ENNReal.ofReal_eq_coe_nnreal h_nonneg]
      simp [Real.toNNReal_of_nonneg h_nonneg]
    have h10 : (↑(ν₂ S'') : ENNReal) = μ₂ S'' := by
      rw [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    have h11 :
        (ν₂ S'' : ENNReal) ≤
          ↑(Real.toNNReal (100 * K * r ^ β)) := by
      calc
        (ν₂ S'' : ENNReal) = μ₂ S'' := h10
        _ = μ₂ S' := h_eq_measure
        _ ≤ ENNReal.ofReal (100 * K * r ^ β) := h_bound
        _ = ↑(Real.toNNReal (100 * K * r ^ β)) := h9
    exact WithTop.coe_le_coe.mp h11
  have hK100 : 1 ≤ 100 * K := by nlinarith [hK]
  have hE''_mass' :
      (1 - ENNReal.ofReal c) ≤ ↑((ν₁.prod ν₂) E'') := by
    rw [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    change (1 - ENNReal.ofReal c) ≤ (μ₁.prod μ₂) E''
    exact hE''_mass
  exact
    ⟨hβ, hK100, hc, E'', hE''_meas, hE''_sub,
      hE''_mass', h_final⟩

end Kakeya.Assouad
