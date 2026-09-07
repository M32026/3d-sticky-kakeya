import MyLeanRepo.Kakeya.Assouad.Definitions
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Packing and logarithmic-decay helper lemmas

Two independent utilities used by the WZ1 anisotropic Frostman rescaling proof:

1. `delta_separated_ball_card_bound`: a δ-separated finite set in a ball of
   radius R has cardinality at most `(2R/δ + 1)^n`.
2. `log_poly_decay`: for any `a > 0`, `log(1/δ) + 1 ≤ 1/(4 δ^a)` for all
   sufficiently small `δ > 0`.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Metric Set Finset

/--
A δ-separated finite subset of a ball of radius R in `EuclideanSpace ℝ (Fin n)`
has cardinality at most `(2 * R / δ + 1)^n`.

Proof: disjoint open balls of radius δ/2 around each point are all contained in
the ball of radius `R + δ/2`; comparing volumes gives the bound.
-/
lemma delta_separated_ball_card_bound
    {n : ℕ} {E : DiscreteSet n} {delta R : ℝ}
    (hdelta : 0 < delta) (hR : 0 < R)
    (h_separation : E.IsDeltaSeparated delta)
    (x0 : Point n) (hball : ∀ y ∈ E, dist y x0 ≤ R) :
    E.enncard ≤ ENNReal.ofReal ((2 * R / delta + 1) ^ n) := by
  by_cases hn : n = 0
  · subst hn
    haveI : Subsingleton (Point 0) := Unique.instSubsingleton
    have h1 : E.card ≤ 1 := Finset.card_le_one.mpr
      fun x _ y _ => Subsingleton.elim x y
    have h2 : (2 * R / delta + 1) ^ 0 = 1 := by simp
    simpa [DiscreteSet.enncard, h2] using mod_cast h1
  · have hn_pos : 0 < n := Nat.pos_of_ne_zero hn
    -- Extract separation predicate with explicit arguments first (before any let bindings)
    have h_sep' : ∀ (x y : Point n), x ∈ E → y ∈ E → x ≠ y → delta ≤ dist x y := by
      intro x y hx hy hxy
      exact h_separation hx hy hxy
    set small_r := delta / 2 with hsmall_r
    have hr_pos : 0 < small_r := by
      rw [hsmall_r]
      exact half_pos hdelta
    let B : Point n → Set (Point n) := fun x => Metric.ball x small_r
    have h_disj : Set.PairwiseDisjoint E B := by
      intro x hx y hy hxy
      have h_goal : Disjoint (B x) (B y) := by
        rw [Set.disjoint_left]
        intro z hz1 hz2
        have h1 : dist z x < small_r := Metric.mem_ball.mp hz1
        have h2 : dist z y < small_r := Metric.mem_ball.mp hz2
        have h_eq : 2 * small_r = delta := by dsimp only [small_r]; ring
        have h_sum : dist z x + dist z y < delta := by
          calc dist z x + dist z y < small_r + small_r := by linarith
               _ = 2 * small_r := by ring
               _ = delta := h_eq
        have h3 : dist x y < delta := by
          calc dist x y ≤ dist x z + dist z y := dist_triangle x z y
               _ = dist z x + dist z y := by rw [dist_comm x z]
               _ < delta := h_sum
        have h4 : delta ≤ dist x y := h_sep' x y hx hy hxy
        exact False.elim (not_le.mpr h3 h4)
      simpa [Function.onFun] using h_goal
    have h_sub : (⋃ x ∈ E, B x) ⊆ Metric.ball x0 (R + small_r) := by
      intro z hz
      have h_exists : ∃ x, x ∈ E ∧ z ∈ B x := by simpa [B] using hz
      rcases h_exists with ⟨x, hx, hzx⟩
      have h5 : dist z x < small_r := Metric.mem_ball.mp hzx
      have h6 : dist x x0 ≤ R := hball x hx
      have h7 : dist z x0 < R + small_r := by
        calc dist z x0 ≤ dist z x + dist x x0 := dist_triangle z x x0
             _ < small_r + R := by linarith
             _ = R + small_r := by ring
      exact Metric.mem_ball.mpr h7
    have h_meas : ∀ x ∈ E, MeasurableSet (B x) := by
      intro x _; exact isOpen_ball.measurableSet
    have h_vol_union : volume (⋃ x ∈ E, B x) = ∑ x ∈ E, volume (B x) :=
      measure_biUnion_finset h_disj h_meas
    have h_vol_le : volume (⋃ x ∈ E, B x) ≤ volume (Metric.ball x0 (R + small_r)) :=
      measure_mono h_sub
    have h_sum_le : ∑ x ∈ E, volume (B x) ≤ volume (Metric.ball x0 (R + small_r)) := by
      rw [←h_vol_union]; exact h_vol_le
    have hfinrank : Module.finrank ℝ (Point n) = n := by
      simpa [Point] using finrank_fintype_fun (ι := Fin n) (M := ℝ)
    letI : Nontrivial (Point n) := by
      let z : Fin n := ⟨0, hn_pos⟩
      refine' ⟨(0 : Point n), EuclideanSpace.single z 1, _⟩
      intro h
      have h2 : (0 : ℝ) = 1 := by
        have h3 := congr_fun (congr_arg (fun (p : Point n) => (p : Fin n → ℝ)) h) z
        simpa [EuclideanSpace.single] using h3
      norm_num at h2
    have h_ball_formula : ∀ (x : Point n) (s : ℝ), 0 ≤ s →
        volume (Metric.ball x s) = ENNReal.ofReal (s ^ n) * volume (Metric.ball (0 : Point n) 1) := by
      intro x s hs
      have h_main : volume (Metric.ball x s) =
          ENNReal.ofReal (s ^ Module.finrank ℝ (Point n)) * volume (Metric.ball (0 : Point n) 1) :=
        MeasureTheory.Measure.addHaar_ball (μ := volume) (x := x) (hr := hs)
      rw [h_main, hfinrank]
    have h_sum_eq : ∑ x ∈ E, volume (B x) =
        (E.card : ENNReal) * ENNReal.ofReal (small_r ^ n) * volume (Metric.ball (0 : Point n) 1) := by
      have h : ∑ x ∈ E, volume (B x) = ∑ x ∈ E, (ENNReal.ofReal (small_r ^ n) * volume (Metric.ball (0 : Point n) 1)) := by
        apply Finset.sum_congr rfl
        intro x _
        exact h_ball_formula x small_r (by linarith)
      rw [h]
      simp
      <;> ring
    have h_big_eq : volume (Metric.ball x0 (R + small_r)) =
        ENNReal.ofReal ((R + small_r) ^ n) * volume (Metric.ball (0 : Point n) 1) :=
      h_ball_formula x0 (R + small_r) (by linarith)
    rw [h_sum_eq, h_big_eq] at h_sum_le
    let V := volume (Metric.ball (0 : Point n) 1)
    have hV_pos : 0 < V :=
      IsOpen.measure_pos volume isOpen_ball ⟨0, by simp⟩
    have hV_ne_top : V ≠ ⊤ := by
      have h_compact : IsCompact (Metric.closedBall (0 : Point n) 1) :=
        isCompact_closedBall 0 1
      have h1 : volume (Metric.closedBall (0 : Point n) 1) ≠ ⊤ := h_compact.measure_lt_top.ne
      have h2 : Metric.ball (0 : Point n) 1 ⊆ Metric.closedBall (0 : Point n) 1 := by
        intro z hz; exact le_of_lt (Metric.mem_ball.mp hz)
      have h3 : V ≤ volume (Metric.closedBall (0 : Point n) 1) := measure_mono h2
      exact ne_top_of_le_ne_top h1 h3
    have hV_ne_zero : V ≠ 0 := hV_pos.ne'
    have h_rpos : 0 < small_r ^ n := by positivity
    have h_ennpos : 0 < ENNReal.ofReal (small_r ^ n) := by positivity
    have h_enntop : ENNReal.ofReal (small_r ^ n) ≠ ⊤ := by simp
    -- Cancel V
    have h_cancel1 : (E.card : ENNReal) * ENNReal.ofReal (small_r ^ n) ≤
        ENNReal.ofReal ((R + small_r) ^ n) := by
      by_contra h
      push Not at h
      have h_lt : ENNReal.ofReal ((R + small_r) ^ n) < (E.card : ENNReal) * ENNReal.ofReal (small_r ^ n) := h
      have h_mult : ENNReal.ofReal ((R + small_r) ^ n) * V < (E.card : ENNReal) * ENNReal.ofReal (small_r ^ n) * V := by
        gcongr <;> exact hV_pos
      exact not_le.mpr h_mult h_sum_le
    -- Cancel small_r^n
    set A := (R + small_r) / small_r with hA_def
    have hA_nonneg : 0 ≤ A := by positivity
    have h1_nonneg : 0 ≤ A ^ n := by positivity
    have h2_nonneg : 0 ≤ small_r ^ n := by positivity
    have h_mul_ennreal : ENNReal.ofReal (A ^ n) * ENNReal.ofReal (small_r ^ n) =
        ENNReal.ofReal ((A ^ n) * (small_r ^ n)) := by
      have h : ENNReal.ofReal ((A ^ n) * (small_r ^ n)) =
          ENNReal.ofReal (A ^ n) * ENNReal.ofReal (small_r ^ n) :=
        ENNReal.ofReal_mul (p := A ^ n) (hp := h1_nonneg)
      exact h.symm
    have h_key : ENNReal.ofReal (A ^ n) * ENNReal.ofReal (small_r ^ n) = ENNReal.ofReal ((R + small_r) ^ n) := by
      rw [h_mul_ennreal]
      have h4 : (A ^ n) * (small_r ^ n) = (R + small_r) ^ n := by
        have h5 : A * small_r = R + small_r := by
          simp only [hA_def]
          field_simp [hr_pos.ne'] <;> ring
        calc (A ^ n) * (small_r ^ n) = (A * small_r) ^ n := by rw [← mul_pow] <;> ring
          _ = (R + small_r) ^ n := by rw [h5]
      rw [h4]
    have h_final : (E.card : ENNReal) ≤ ENNReal.ofReal (A ^ n) := by
      by_contra h
      push Not at h
      have h_lt : ENNReal.ofReal (A ^ n) < (E.card : ENNReal) := h
      have h_mult : ENNReal.ofReal (A ^ n) * ENNReal.ofReal (small_r ^ n) <
          (E.card : ENNReal) * ENNReal.ofReal (small_r ^ n) := by
        set c := ENNReal.ofReal (small_r ^ n) with hc_def
        have hc_pos : 0 < c := h_ennpos
        have hc_top : c ≠ ⊤ := h_enntop
        have h_le : ENNReal.ofReal (A ^ n) * c ≤ (E.card : ENNReal) * c :=
          mul_le_mul_right' h_lt.le c
        have h_ne : ENNReal.ofReal (A ^ n) * c ≠ (E.card : ENNReal) * c := by
          intro h_eq
          have h_cancel : ENNReal.ofReal (A ^ n) = (E.card : ENNReal) := by
            have h_inj : Function.Injective (fun x : ENNReal => x * c) := by
              intro x y hxy
              exact (ENNReal.mul_left_inj hc_pos.ne' hc_top).mp hxy
            exact h_inj h_eq
          exact h_lt.ne h_cancel
        exact lt_iff_le_and_ne.mpr ⟨h_le, h_ne⟩
      rw [h_key] at h_mult
      exact not_le.mpr h_mult h_cancel1
    have h_identity : A = 2 * R / delta + 1 := by
      simp only [hA_def, small_r]
      field_simp [hdelta.ne'] <;> ring
    rw [h_identity] at h_final
    exact h_final

/--
For any `a > 0`, there exists `0 < δ₀ ≤ 1` such that for all `0 < δ ≤ δ₀`,
`Real.log (1 / δ) + 1 ≤ 1 / (4 * δ ^ a)`.

Equivalently, `4 * δ^a * (log(1/δ) + 1) ≤ 1`.
Proof uses `log x ≤ x^ε / ε` with `ε = a/2`, then bounds the resulting
power terms by choosing δ₀ small enough.
-/
lemma log_poly_decay (a : ℝ) (ha : 0 < a) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta₀ →
        Real.log (1 / delta) + 1 ≤ 1 / (4 * delta ^ a) := by
  have h_log_bound : ∀ (t : ℝ), 1 ≤ t → Real.log t ≤ 2 / a * t ^ (a / 2) := by
    intro t ht
    have h1 : 0 ≤ t := by linarith
    have h2 : Real.log t ≤ t ^ (a / 2) / (a / 2) :=
      Real.log_le_rpow_div h1 (by linarith)
    have h3 : t ^ (a / 2) / (a / 2) = 2 / a * t ^ (a / 2) := by
      field_simp [ha.ne'] <;> ring
    rw [h3] at h2
    exact h2
  let delta₁ : ℝ := (a / 16) ^ (2 / a)
  let delta₂ : ℝ := (1 / 8 : ℝ) ^ (1 / a)
  let delta₀ : ℝ := min 1 (min delta₁ delta₂)
  have hd1_pos : 0 < delta₁ := by positivity
  have hd2_pos : 0 < delta₂ := by positivity
  have hdelta₀_pos : 0 < delta₀ := by positivity
  have hdelta₀_le_one : delta₀ ≤ 1 := min_le_left _ _
  refine ⟨delta₀, hdelta₀_pos, hdelta₀_le_one, ?_⟩
  intro delta hdelta_pos hdelta_le
  have hdelta_le_delta₁ : delta ≤ delta₁ := by
    calc delta ≤ delta₀ := hdelta_le
         _ ≤ min delta₁ delta₂ := min_le_right _ _
         _ ≤ delta₁ := min_le_left _ _
  have hdelta_le_delta₂ : delta ≤ delta₂ := by
    calc delta ≤ delta₀ := hdelta_le
         _ ≤ min delta₁ delta₂ := min_le_right _ _
         _ ≤ delta₂ := min_le_right _ _
  have h_exp1 : (2 / a : ℝ) * (a / 2) = 1 := by
    field_simp [ha.ne'] <;> ring
  have h4 : delta ^ (a / 2) ≤ a / 16 := by
    have h5 : delta ^ (a / 2) ≤ delta₁ ^ (a / 2) := by gcongr <;> linarith
    have h6 : delta₁ ^ (a / 2) = a / 16 := by
      dsimp only [delta₁]
      have h_rpow : ((a / 16) ^ (2 / a)) ^ (a / 2) = (a / 16) ^ ((2 / a) * (a / 2)) := by
        rw [← Real.rpow_mul (by positivity)] <;> rfl
      rw [h_rpow, h_exp1, Real.rpow_one]
    rw [h6] at h5
    exact h5
  have h_exp2 : (1 / a : ℝ) * a = 1 := by
    field_simp [ha.ne'] <;> ring
  have h8 : delta ^ a ≤ 1 / 8 := by
    have h9 : delta ^ a ≤ delta₂ ^ a := by gcongr <;> linarith
    have h10 : delta₂ ^ a = 1 / 8 := by
      dsimp only [delta₂]
      have h_rpow : ((1 / 8 : ℝ) ^ (1 / a)) ^ a = (1 / 8 : ℝ) ^ ((1 / a) * a) := by
        rw [← Real.rpow_mul (by positivity)] <;> rfl
      rw [h_rpow, h_exp2, Real.rpow_one]
    rw [h10] at h9
    exact h9
  have ht_one : 1 ≤ 1 / delta := by
    have h12 : delta ≤ 1 := hdelta_le.trans hdelta₀_le_one
    apply one_le_one_div <;> linarith
  have h14 : Real.log (1 / delta) ≤ 2 / a * (1 / delta) ^ (a / 2) :=
    h_log_bound (1 / delta) ht_one
  have h_inv_rpow : (1 / delta) ^ (a / 2) = 1 / (delta ^ (a / 2)) := by
    have h_pos : 0 < delta := hdelta_pos
    have h1 : (1 / delta) ^ (a / 2) = (delta⁻¹) ^ (a / 2) := by field_simp
    rw [h1]
    have h2 : (delta⁻¹) ^ (a / 2) = (delta ^ (a / 2))⁻¹ := by
      rw [Real.inv_rpow (by positivity)] <;> rfl
    rw [h2] <;> field_simp
  have h_mul_simp : delta ^ a * (1 / delta) ^ (a / 2) = delta ^ (a / 2) := by
    rw [h_inv_rpow]
    have h_pos : 0 < delta := hdelta_pos
    have h3 : delta ^ a * (1 / (delta ^ (a / 2))) = delta ^ a / delta ^ (a / 2) := by ring
    rw [h3]
    have h4 : delta ^ a / delta ^ (a / 2) = delta ^ (a - a / 2) := by
      rw [← Real.rpow_sub h_pos] <;> ring
    rw [h4]
    have h5 : a - a / 2 = a / 2 := by ring
    rw [h5]
  have h20 : 8 / a * delta ^ (a / 2) + 4 * delta ^ a ≤ 1 := by
    have h21 : 8 / a * delta ^ (a / 2) ≤ 8 / a * (a / 16) := by gcongr <;> linarith
    have h22 : 8 / a * (a / 16) = 1 / 2 := by
      field_simp [ha.ne'] <;> ring
    have h23 : 4 * delta ^ a ≤ 4 * (1 / 8 : ℝ) := by gcongr <;> linarith
    have h24 : 4 * (1 / 8 : ℝ) = 1 / 2 := by norm_num
    linarith
  have h_main : 4 * delta ^ a * (Real.log (1 / delta) + 1) ≤ 1 := by
    have h25 : 4 * delta ^ a * (Real.log (1 / delta) + 1) ≤
        4 * delta ^ a * (2 / a * (1 / delta) ^ (a / 2) + 1) := by
      gcongr <;> linarith [h14]
    have h26 : 4 * delta ^ a * (2 / a * (1 / delta) ^ (a / 2) + 1) =
        8 / a * (delta ^ a * (1 / delta) ^ (a / 2)) + 4 * delta ^ a := by ring
    rw [h26] at h25
    rw [h_mul_simp] at h25
    exact h25.trans h20
  have h_pos2 : 0 < 4 * delta ^ a := by positivity
  have h_eq : (Real.log (1 / delta) + 1) =
      ((Real.log (1 / delta) + 1) * (4 * delta ^ a)) / (4 * delta ^ a) := by
    field_simp [h_pos2.ne'] <;> ring
  have h_final : Real.log (1 / delta) + 1 ≤ 1 / (4 * delta ^ a) := by
    have h_pos : 0 < 4 * delta ^ a := h_pos2
    have h_ineq : (Real.log (1 / delta) + 1) * (4 * delta ^ a) ≤ 1 := by
      have h_comm : (Real.log (1 / delta) + 1) * (4 * delta ^ a) = 4 * delta ^ a * (Real.log (1 / delta) + 1) := by ring
      rw [h_comm]
      exact h_main
    have h_goal : ((Real.log (1 / delta) + 1) * (4 * delta ^ a)) / (4 * delta ^ a) ≤ (1 : ℝ) / (4 * delta ^ a) := by
      apply div_le_div_of_nonneg_right h_ineq (by positivity)
    have h2 : ((Real.log (1 / delta) + 1) * (4 * delta ^ a)) / (4 * delta ^ a) = (Real.log (1 / delta) + 1) := by
      field_simp [h_pos.ne'] <;> ring
    rw [h2] at h_goal
    exact h_goal
  exact h_final

/--
A δ-separated finite subset of a ball of radius 2 in `Point 2` has cardinality
at most `81 / δ^2`, provided `0 < δ ≤ 1`.

This is a convenient specialization of `delta_separated_ball_card_bound`
with `R = 2`, `n = 2`, using `4/δ + 1 ≤ 9/δ` when `δ ≤ 1`.
-/
lemma separated_set_packing_bound
    {E : DiscreteSet 2} {delta : ℝ}
    (hdelta : 0 < delta) (hdelta_le_one : delta ≤ 1)
    (h_separation : E.IsDeltaSeparated delta)
    (x0 : Point 2) (hball : ∀ y ∈ E, dist y x0 ≤ 2) :
    (E.card : ℝ) ≤ 81 / delta ^ 2 := by
  have h1 : E.enncard ≤ ENNReal.ofReal ((2 * (2 : ℝ) / delta + 1) ^ 2) :=
    delta_separated_ball_card_bound hdelta (by norm_num) h_separation x0 hball
  have h2 : (2 * (2 : ℝ) / delta + 1) ≤ 9 / delta := by
    have h3 : 1 ≤ 1 / delta := one_le_one_div hdelta hdelta_le_one
    calc
      2 * (2 : ℝ) / delta + 1 = 4 / delta + 1 := by ring
      _ ≤ 4 / delta + 1 / delta := by gcongr
      _ = 5 / delta := by ring
      _ ≤ 9 / delta := by
        have h_pos : 0 < delta := hdelta
        have h : 5 / delta ≤ 9 / delta := by
          apply div_le_div_of_nonneg_right
          <;> norm_num <;> linarith
        exact h
  have h4 : ((2 * (2 : ℝ) / delta + 1) ^ 2) ≤ (9 / delta) ^ 2 := by gcongr
  have h5 : (9 / delta) ^ 2 = 81 / delta ^ 2 := by ring
  have h6 : E.enncard ≤ ENNReal.ofReal (81 / delta ^ 2) := by
    calc
      E.enncard ≤ ENNReal.ofReal ((2 * (2 : ℝ) / delta + 1) ^ 2) := h1
      _ ≤ ENNReal.ofReal ((9 / delta) ^ 2) := by exact ENNReal.ofReal_le_ofReal h4
      _ = ENNReal.ofReal (81 / delta ^ 2) := by rw [h5]
  have h7 : (E.card : ENNReal) ≤ ENNReal.ofReal (81 / delta ^ 2) := h6
  have h_pos : 0 ≤ 81 / delta ^ 2 := by positivity
  have h8 : (E.card : ℝ) ≤ 81 / delta ^ 2 := by
    have h9 : (E.card : ENNReal) = ENNReal.ofReal (E.card : ℝ) := by
      norm_cast
    rw [h9] at h7
    have h10 : ENNReal.ofReal (E.card : ℝ) ≤ ENNReal.ofReal (81 / delta ^ 2) := h7
    have h11 : (E.card : ℝ) ≤ 81 / delta ^ 2 := by
      exact (ENNReal.ofReal_le_ofReal_iff h_pos).mp h10
    exact h11
  exact h8

end Kakeya.Assouad
