import MyLeanRepo.Kakeya.Streamlined.Geometry
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.TubeVolume
import Mathlib.Topology.MetricSpace.Thickening

/-!
# Close axial tubes intersection lemma

Two nearly-axial δ-tubes whose segments intercept a common axial plane at close
transverse positions, with close intercept parameters and close directions, are
not essentially distinct.

## Why intercept coordinates (not base coordinates)

A lemma using *base* transverse separation + bounded axial base separation is
false in general.  Counterexample: directions u = (0.48, 0, 0.877), bases
differing by (0, 0, 1/8).  The perpendicular axis separation is ≈ 0.06,
independent of δ, which dwarfs δ/50 for small δ.  Using the intercept on a
common axial plane eliminates this transverse offset.

## Geometric argument

1. Let q_i = p_i + t_i•u_i be the intercept with plane x_2 = c.
2. Overlap parameter range s ∈ [-min(t1,t2), 1-max(t1,t2)] has length
   L = 1 - |t1-t2| ≥ 7/8.
3. For s in this range, q2+s•u2 lies on S2, and
   ‖(q1+s•u1) - (q2+s•u2)‖ ≤ ‖q1-q2‖ + |s|·‖u1-u2‖ ≤ δ/50 + 3δ/100 = δ/20.
4. Hence the (19δ/20)-thickening of the overlap segment is contained in both
   tube carriers (since 19δ/20 + δ/20 = δ).
5. Its volume ≥ π(19δ/20)²·(7/8) + (4/3)π(19δ/20)³
   > (1/2)[πδ² + (8/3)πδ³] ≥ V(δ)/2.
-/

noncomputable section

open Kakeya.Streamlined MeasureTheory Metric

namespace Kakeya.Streamlined.GeometricLemmas

/-- Pure arithmetic bounds for the overlap parameterization. -/
lemma overlap_arithmetic_bounds (t1 t2 t L : ℝ)
    (ht1 : 0 ≤ t1) (ht1' : t1 ≤ 1)
    (ht2 : 0 ≤ t2) (ht2' : t2 ≤ 1)
    (ht0 : 0 ≤ t) (htL : t ≤ L)
    (hL : L = 1 - max t1 t2 + min t1 t2) :
    let s_min := -min t1 t2
    let s_max := 1 - max t1 t2
    let s := s_min + t
    (-1 ≤ s ∧ s ≤ 1 ∧
     0 ≤ t1 + s ∧ t1 + s ≤ 1 ∧
     0 ≤ t2 + s ∧ t2 + s ≤ 1) := by
  dsimp only
  have hmin1 : min t1 t2 ≤ t1 := min_le_left t1 t2
  have hmin2 : min t1 t2 ≤ t2 := min_le_right t1 t2
  have hmax1 : t1 ≤ max t1 t2 := le_max_left t1 t2
  have hmax2 : t2 ≤ max t1 t2 := le_max_right t1 t2
  have hmin_nonneg : 0 ≤ min t1 t2 := by
    exact le_min_iff.mpr ⟨ht1, ht2⟩
  have hmin_le_one : min t1 t2 ≤ 1 := by
    exact min_le_iff.mpr (Or.inl ht1')
  have hmax_nonneg : 0 ≤ max t1 t2 := by
    exact le_max_iff.mpr (Or.inl ht1)
  have hmax_le_one : max t1 t2 ≤ 1 := by
    exact max_le_iff.mpr ⟨ht1', ht2'⟩
  constructor
  · -- -1 ≤ s
    linarith
  constructor
  · -- s ≤ 1
    linarith [hL]
  constructor
  · -- 0 ≤ t1 + s
    linarith
  constructor
  · -- t1 + s ≤ 1
    linarith [hL, hmax1]
  constructor
  · -- 0 ≤ t2 + s
    linarith
  · -- t2 + s ≤ 1
    linarith [hL, hmax2]

/-- Lower bound on capsule volume: cylinder + full sphere (two half-balls). -/
def CapsuleLowerBound : Prop :=
  ∀ (L r : ℝ), 0 < L → 0 < r →
  ∀ (p u : Point3), ‖u‖ = 1 →
  ENNReal.ofReal (Real.pi * r^2 * L + (4 / 3 : ℝ) * Real.pi * r^3) ≤
  MeasureTheory.volume (Metric.cthickening r
    ((fun t : ℝ => p + t • u) '' Set.Icc 0 L))

/-- Upper bound on unit capsule volume: cylinder ∪ 2 balls union bound. -/
def CapsuleUpperBound : Prop :=
  ∀ (r : ℝ), 0 < r →
  Kakeya.deltaTubeVolume r ≤
  ENNReal.ofReal (Real.pi * r^2 + (8 / 3 : ℝ) * Real.pi * r^3)

/-- Monotonicity of closed thickening under set inclusion. -/
lemma cthickening_set_mono {α : Type*} [PseudoMetricSpace α] {r : ℝ} {s1 s2 : Set α}
    (hsub : s1 ⊆ s2) :
    Metric.cthickening r s1 ⊆ Metric.cthickening r s2 := by
  intro x hx
  have h_inf : Metric.infEDist x s2 ≤ Metric.infEDist x s1 := by
    rw [Metric.le_infEDist]
    intro y hy
    exact Metric.infEDist_le_edist_of_mem (hsub hy)
  have h7 : Metric.infEDist x s1 ≤ ENNReal.ofReal r := Metric.mem_cthickening_iff.mp hx
  exact Metric.mem_cthickening_iff.mpr (le_trans h_inf h7)

/-- Arithmetic coefficient inequality for the relaxed (1/2) version. -/
lemma volume_coefficient_ineq (δ L : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hL : L ≥ 7 / 8) :
    2 * ((187 * δ / 200)^2 * L) + 2 * ((4 / 3 : ℝ) * (187 * δ / 200)^3) -
    (δ^2 + (8 / 3 : ℝ) * δ^3) > 0 := by
  nlinarith [sq_nonneg δ, hδ1, hL]

private lemma overlap_r_le_delta (δ : ℝ) (hδ : 0 < δ) :
    187 * δ / 200 ≤ δ := by
  linarith

private lemma overlap_hdist_nonneg (δ : ℝ) (hδ : 0 < δ) :
    0 ≤ 13 * δ / 200 := by
  positivity

private lemma close_axial_volume_contradiction
    {δ L : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hL_ge : L ≥ 7 / 8)
    {T1 T2 : DeltaTube δ}
    (h_vol_inter :
      ENNReal.ofReal
          (Real.pi * (187 * δ / 200) ^ 2 * L +
            (4 / 3 : ℝ) * Real.pi * (187 * δ / 200) ^ 3) ≤
        MeasureTheory.volume (T1.carrier ∩ T2.carrier))
    (h_capsule_upper : CapsuleUpperBound) :
    ¬ T1.EssentiallyDistinct T2 := by
  let lower : ℝ :=
    Real.pi * (187 * δ / 200) ^ 2 * L +
      (4 / 3 : ℝ) * Real.pi * (187 * δ / 200) ^ 3
  let upper : ℝ := Real.pi * δ ^ 2 + (8 / 3 : ℝ) * Real.pi * δ ^ 3
  have h_real_ineq : lower > upper / 2 := by
    simp only [lower, upper]
    have h_main :
        2 * ((187 * δ / 200)^2 * L) +
          2 * ((4 / 3 : ℝ) * (187 * δ / 200)^3) -
            (δ^2 + (8 / 3 : ℝ) * δ^3) > 0 :=
      volume_coefficient_ineq δ L hδ hδ1 hL_ge
    have h_factor :
        2 *
              (Real.pi * (187 * δ / 200)^2 * L +
                (4 / 3 : ℝ) * Real.pi * (187 * δ / 200)^3) -
            (Real.pi * δ^2 + (8 / 3 : ℝ) * Real.pi * δ^3) =
          Real.pi *
            (2 * ((187 * δ / 200)^2 * L) +
              2 * ((4 / 3 : ℝ) * (187 * δ / 200)^3) -
                (δ^2 + (8 / 3 : ℝ) * δ^3)) := by
      ring
    have h_positive := mul_pos Real.pi_pos h_main
    rw [← h_factor] at h_positive
    linarith
  have h_lower_nonneg : 0 ≤ lower := by positivity
  have h_upper_nonneg : 0 ≤ upper := by positivity
  have h_ofReal_lt : ENNReal.ofReal upper / 2 < ENNReal.ofReal lower := by
    have h_a_ne_top : ENNReal.ofReal upper / 2 ≠ ⊤ :=
      ENNReal.div_ne_top ENNReal.ofReal_ne_top (by norm_num)
    have h_b_ne_top : ENNReal.ofReal lower ≠ ⊤ := ENNReal.ofReal_ne_top
    apply (ENNReal.toReal_lt_toReal h_a_ne_top h_b_ne_top).mp
    rw [ENNReal.toReal_ofReal h_lower_nonneg]
    have h_div2 :
        ENNReal.ofReal upper / 2 = ENNReal.ofReal upper * (2 : ENNReal)⁻¹ := by
      simp [div_eq_mul_inv]
    rw [h_div2, ENNReal.toReal_mul, ENNReal.toReal_ofReal h_upper_nonneg]
    norm_num
    simpa [div_eq_mul_inv] using h_real_ineq
  have h_vol_upper : Kakeya.deltaTubeVolume δ ≤ ENNReal.ofReal upper :=
    h_capsule_upper δ hδ
  have h_half_upper :
      Kakeya.deltaTubeVolume δ / 2 ≤ ENNReal.ofReal upper / 2 :=
    by gcongr
  have h_vol1 : T1.volume = Kakeya.deltaTubeVolume δ :=
    tube_volume_eq T1
      { base := 0
        direction := EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
        direction_unit := by simp [EuclideanSpace.norm_eq] <;> norm_num }
  have h_vol2 : T2.volume = Kakeya.deltaTubeVolume δ :=
    tube_volume_eq T2
      { base := 0
        direction := EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
        direction_unit := by simp [EuclideanSpace.norm_eq] <;> norm_num }
  intro h_distinct
  have h_distinct' :
      MeasureTheory.volume (T1.carrier ∩ T2.carrier) ≤
        Kakeya.deltaTubeVolume δ / 2 := by
    have h :
        MeasureTheory.volume (T1.carrier ∩ T2.carrier) ≤
          (2 : ENNReal)⁻¹ * max T1.volume T2.volume := h_distinct
    rw [h_vol1, h_vol2, max_self] at h
    simpa [div_eq_mul_inv, mul_comm] using h
  have h_lower :
      ENNReal.ofReal lower ≤ MeasureTheory.volume (T1.carrier ∩ T2.carrier) := by
    simpa [lower] using h_vol_inter
  have h_contra :
      MeasureTheory.volume (T1.carrier ∩ T2.carrier) <
        MeasureTheory.volume (T1.carrier ∩ T2.carrier) :=
    h_distinct'.trans_lt
      (h_half_upper.trans_lt (h_ofReal_lt.trans_le h_lower))
  exact (lt_irrefl _ h_contra)

/--
Two nearly-axial δ-tubes with close intercepts on a common axial plane are
not essentially distinct.

All geometric quantities (`p1`, `u1`, `q1`, etc.) are in `frame.symm` coordinates.
-/
lemma close_axial_tubes_not_distinct
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {T1 T2 : DeltaTube δ}
    (frame : Point3 ≃ᵃⁱ[ℝ] Point3)
    (p1 u1 p2 u2 q1 q2 : Point3) (t1 t2 : ℝ)
    (hp1 : p1 = frame.symm T1.base)
    (hu1 : u1 = frame.symm.linearIsometryEquiv T1.direction)
    (hp2 : p2 = frame.symm T2.base)
    (hu2 : u2 = frame.symm.linearIsometryEquiv T2.direction)
    (ht1 : t1 ∈ Set.Icc (0 : ℝ) 1)
    (ht2 : t2 ∈ Set.Icc (0 : ℝ) 1)
    (hq1 : q1 = p1 + t1 • u1)
    (hq2 : q2 = p2 + t2 • u2)
    (hplane : q1 2 = q2 2)
    (hq0 : |(q1 - q2) 0| ≤ δ / 100)
    (hq1' : |(q1 - q2) 1| ≤ δ / 100)
    (htdiff : |t1 - t2| ≤ 1 / 8)
    (hdir0 : |(u1 - u2) 0| ≤ δ / 100)
    (hdir1 : |(u1 - u2) 1| ≤ δ / 100)
    (hu2_1 : u1 2 ≥ 1 / 2)
    (hu2_2 : u2 2 ≥ 1 / 2)
    (h_capsule_lower : CapsuleLowerBound)
    (h_capsule_upper : CapsuleUpperBound) :
    ¬ T1.EssentiallyDistinct T2 := by
  have h_u1_norm : ‖u1‖ = 1 := by
    have h : ‖u1‖ = ‖T1.direction‖ := by
      rw [hu1]
      exact frame.symm.linearIsometryEquiv.norm_map T1.direction
    exact Eq.trans h T1.direction_unit
  have h_u2_norm : ‖u2‖ = 1 := by
    have h : ‖u2‖ = ‖T2.direction‖ := by
      rw [hu2]
      exact frame.symm.linearIsometryEquiv.norm_map T2.direction
    exact Eq.trans h T2.direction_unit

  /- ### Bound ‖u1 - u2‖ ≤ 3δ / 100 -/
  have h_norm_sq : ∀ (x : Point3), ‖x‖^2 = (x 0)^2 + (x 1)^2 + (x 2)^2 := by
    intro x
    have h1 : ‖x‖ = Real.sqrt ((x 0)^2 + (x 1)^2 + (x 2)^2) := by
      simp [EuclideanSpace.norm_eq, Fin.sum_univ_succ] <;> ring
    rw [h1]
    rw [Real.sq_sqrt (by positivity)]
  have h_sum1 : (u1 0)^2 + (u1 1)^2 + (u1 2)^2 = 1 := by
    have h : ‖u1‖^2 = (u1 0)^2 + (u1 1)^2 + (u1 2)^2 := h_norm_sq u1
    rw [h_u1_norm] at h; linarith
  have h_sum2 : (u2 0)^2 + (u2 1)^2 + (u2 2)^2 = 1 := by
    have h : ‖u2‖^2 = (u2 0)^2 + (u2 1)^2 + (u2 2)^2 := h_norm_sq u2
    rw [h_u2_norm] at h; linarith

  have h_abs_le_one : ∀ (x : ℝ), x^2 ≤ 1 → |x| ≤ 1 := by
    intro x hx
    have h1 : |x|^2 = x^2 := by rw [sq_abs]
    have h2 : |x|^2 ≤ 1 := by rw [h1]; exact hx
    have h3 : 0 ≤ |x| := abs_nonneg x
    by_contra h4
    have h5 : 1 < |x| := by linarith
    have h6 : 1 < |x|^2 := by
      have h7 : 0 ≤ 1 := by norm_num
      nlinarith
    linarith
  have h_abs_u10 : |u1 0| ≤ 1 := by
    have h1 : 0 ≤ (u1 1)^2 := by positivity
    have h2 : 0 ≤ (u1 2)^2 := by positivity
    have hsq : (u1 0)^2 ≤ 1 := by linarith [h_sum1]
    exact h_abs_le_one (u1 0) hsq
  have h_abs_u20 : |u2 0| ≤ 1 := by
    have h1 : 0 ≤ (u2 1)^2 := by positivity
    have h2 : 0 ≤ (u2 2)^2 := by positivity
    have hsq : (u2 0)^2 ≤ 1 := by linarith [h_sum2]
    exact h_abs_le_one (u2 0) hsq
  have h_abs_u11 : |u1 1| ≤ 1 := by
    have h1 : 0 ≤ (u1 0)^2 := by positivity
    have h2 : 0 ≤ (u1 2)^2 := by positivity
    have hsq : (u1 1)^2 ≤ 1 := by linarith [h_sum1]
    exact h_abs_le_one (u1 1) hsq
  have h_abs_u21 : |u2 1| ≤ 1 := by
    have h1 : 0 ≤ (u2 0)^2 := by positivity
    have h2 : 0 ≤ (u2 2)^2 := by positivity
    have hsq : (u2 1)^2 ≤ 1 := by linarith [h_sum2]
    exact h_abs_le_one (u2 1) hsq

  have h_abs_sq_diff : ∀ (a b : ℝ), |a^2 - b^2| = |a - b| * |a + b| := by
    intro a b
    have h : a^2 - b^2 = (a - b) * (a + b) := by ring
    rw [h, abs_mul]
  have h_sum_u10 : |u2 0 + u1 0| ≤ 2 := by
    have h_tri : |u2 0 + u1 0| ≤ |u2 0| + |u1 0| := by
      simpa [Real.norm_eq_abs] using norm_add_le (u2 0) (u1 0)
    calc |u2 0 + u1 0| ≤ |u2 0| + |u1 0| := h_tri
    _ ≤ 1 + 1 := by gcongr
    _ = 2 := by norm_num
  have h_sum_u11 : |u2 1 + u1 1| ≤ 2 := by
    have h_tri : |u2 1 + u1 1| ≤ |u2 1| + |u1 1| := by
      simpa [Real.norm_eq_abs] using norm_add_le (u2 1) (u1 1)
    calc |u2 1 + u1 1| ≤ |u2 1| + |u1 1| := h_tri
    _ ≤ 1 + 1 := by gcongr
    _ = 2 := by norm_num
  have hdir0' : |u2 0 - u1 0| ≤ δ / 100 := by
    have h_eq : |u2 0 - u1 0| = |(u1 - u2) 0| := by
      have h : u2 0 - u1 0 = -((u1 - u2) 0) := by simp
      rw [h, abs_neg]
    rw [h_eq]; exact hdir0
  have hdir1' : |u2 1 - u1 1| ≤ δ / 100 := by
    have h_eq : |u2 1 - u1 1| = |(u1 - u2) 1| := by
      have h : u2 1 - u1 1 = -((u1 - u2) 1) := by simp
      rw [h, abs_neg]
    rw [h_eq]; exact hdir1
  have h_diff_sq : |(u1 2)^2 - (u2 2)^2| ≤ δ / 25 := by
    have h_eq : (u1 2)^2 - (u2 2)^2 =
        ((u2 0)^2 - (u1 0)^2) + ((u2 1)^2 - (u1 1)^2) := by linarith
    rw [h_eq]
    have h_abs_add : |((u2 0)^2 - (u1 0)^2) + ((u2 1)^2 - (u1 1)^2)| ≤
        |(u2 0)^2 - (u1 0)^2| + |(u2 1)^2 - (u1 1)^2| := by
      simpa [Real.norm_eq_abs] using norm_add_le ((u2 0)^2 - (u1 0)^2) ((u2 1)^2 - (u1 1)^2)
    calc |((u2 0)^2 - (u1 0)^2) + ((u2 1)^2 - (u1 1)^2)|
        ≤ |(u2 0)^2 - (u1 0)^2| + |(u2 1)^2 - (u1 1)^2| := h_abs_add
    _ = |u2 0 - u1 0| * |u2 0 + u1 0| + |u2 1 - u1 1| * |u2 1 + u1 1| := by
      rw [h_abs_sq_diff (u2 0) (u1 0), h_abs_sq_diff (u2 1) (u1 1)]
    _ ≤ (δ / 100) * 2 + (δ / 100) * 2 := by
      have h1 : |u2 0 - u1 0| * |u2 0 + u1 0| ≤ (δ / 100) * 2 := by
        exact mul_le_mul hdir0' h_sum_u10 (abs_nonneg _) (by positivity)
      have h2 : |u2 1 - u1 1| * |u2 1 + u1 1| ≤ (δ / 100) * 2 := by
        exact mul_le_mul hdir1' h_sum_u11 (abs_nonneg _) (by positivity)
      linarith
    _ = δ / 25 := by ring

  have h_axial_diff : |u1 2 - u2 2| ≤ δ / 25 := by
    have h_pos : 0 < u1 2 + u2 2 := by linarith
    have h_abs_sum : |u1 2 + u2 2| = u1 2 + u2 2 := by
      rw [abs_of_pos] <;> linarith
    have h : |(u1 2)^2 - (u2 2)^2| = |u1 2 - u2 2| * (u1 2 + u2 2) := by
      rw [h_abs_sq_diff (u1 2) (u2 2), h_abs_sum]
    have h_diff : |u1 2 - u2 2| * (u1 2 + u2 2) ≤ δ / 25 := by
      rw [← h]; exact h_diff_sq
    have h_sum_ge_one : u1 2 + u2 2 ≥ 1 := by linarith
    have h' : |u1 2 - u2 2| * (u1 2 + u2 2) ≥ |u1 2 - u2 2| * 1 := by
      gcongr <;> linarith
    linarith

  have hdir_norm : ‖u1 - u2‖ ≤ 9 * δ / 200 := by
    have h_norm2 : ‖u1 - u2‖^2 =
        ((u1 - u2) 0)^2 + ((u1 - u2) 1)^2 + ((u1 - u2) 2)^2 := h_norm_sq (u1 - u2)
    have h4 : ((u1 - u2) 0)^2 ≤ (δ / 100)^2 := by
      have h7 : |(u1 - u2) 0| ≤ δ / 100 := hdir0
      have h8 : |(u1 - u2) 0|^2 ≤ (δ / 100)^2 := by gcongr
      have h9 : ((u1 - u2) 0)^2 = |(u1 - u2) 0|^2 := by rw [sq_abs]
      rw [h9]; exact h8
    have h5 : ((u1 - u2) 1)^2 ≤ (δ / 100)^2 := by
      have h7 : |(u1 - u2) 1| ≤ δ / 100 := hdir1
      have h8 : |(u1 - u2) 1|^2 ≤ (δ / 100)^2 := by gcongr
      have h9 : ((u1 - u2) 1)^2 = |(u1 - u2) 1|^2 := by rw [sq_abs]
      rw [h9]; exact h8
    have h6 : ((u1 - u2) 2)^2 ≤ (δ / 25)^2 := by
      have h10 : (u1 - u2) 2 = u1 2 - u2 2 := by simp
      rw [h10]
      have h7 : |u1 2 - u2 2| ≤ δ / 25 := h_axial_diff
      have h8 : |u1 2 - u2 2|^2 ≤ (δ / 25)^2 := by gcongr
      have h9 : (u1 2 - u2 2)^2 = |u1 2 - u2 2|^2 := by rw [sq_abs]
      rw [h9]; exact h8
    have h_arith : (δ / 100)^2 + (δ / 100)^2 + (δ / 25)^2 ≤ (9 * δ / 200)^2 := by
      have h1 : (δ / 100)^2 + (δ / 100)^2 + (δ / 25)^2 =
          δ^2 * (1 / 10000 + 1 / 10000 + 1 / 625) := by ring
      have h2 : (9 * δ / 200)^2 = δ^2 * (81 / 40000) := by ring
      rw [h1, h2]
      have h3 : (1 / 10000 + 1 / 10000 + 1 / 625 : ℝ) ≤ 81 / 40000 := by norm_num
      have h4 : 0 ≤ δ^2 := by positivity
      exact mul_le_mul_of_nonneg_left h3 h4
    have h_sq_le : ‖u1 - u2‖^2 ≤ (9 * δ / 200)^2 := by
      rw [h_norm2]
      have h_sum : ((u1 - u2) 0)^2 + ((u1 - u2) 1)^2 + ((u1 - u2) 2)^2 ≤
          (δ / 100)^2 + (δ / 100)^2 + (δ / 25)^2 := by
        exact add_le_add (add_le_add h4 h5) h6
      exact le_trans h_sum h_arith
    have h_nonneg : 0 ≤ ‖u1 - u2‖ := by positivity
    have h_c_nonneg : 0 ≤ 9 * δ / 200 := by positivity
    by_contra h
    have h' : 9 * δ / 200 < ‖u1 - u2‖ := by linarith
    have h'' : (9 * δ / 200)^2 < ‖u1 - u2‖^2 := by gcongr <;> linarith
    have h_cont : ‖u1 - u2‖^2 ≤ (9 * δ / 200)^2 := h_sq_le
    linarith

  /- ### Bound ‖q1 - q2‖ ≤ δ / 50 -/
  have hq_norm : ‖q1 - q2‖ ≤ δ / 50 := by
    have h_norm2 : ‖q1 - q2‖^2 =
        ((q1 - q2) 0)^2 + ((q1 - q2) 1)^2 + ((q1 - q2) 2)^2 := h_norm_sq (q1 - q2)
    have h2 : (q1 - q2) 2 = 0 := by
      have h21 : (q1 - q2) 2 = q1 2 - q2 2 := by simp
      rw [h21, hplane] <;> ring
    have h3 : ((q1 - q2) 0)^2 ≤ (δ / 100)^2 := by
      have h7 : |(q1 - q2) 0| ≤ δ / 100 := hq0
      have h8 : |(q1 - q2) 0|^2 ≤ (δ / 100)^2 := by gcongr
      have h9 : ((q1 - q2) 0)^2 = |(q1 - q2) 0|^2 := by rw [sq_abs]
      rw [h9]; exact h8
    have h4 : ((q1 - q2) 1)^2 ≤ (δ / 100)^2 := by
      have h7 : |(q1 - q2) 1| ≤ δ / 100 := hq1'
      have h8 : |(q1 - q2) 1|^2 ≤ (δ / 100)^2 := by gcongr
      have h9 : ((q1 - q2) 1)^2 = |(q1 - q2) 1|^2 := by rw [sq_abs]
      rw [h9]; exact h8
    have h_arith : (δ / 100)^2 + (δ / 100)^2 + 0^2 ≤ (δ / 50)^2 := by
      have h1 : (δ / 100)^2 + (δ / 100)^2 + 0^2 = δ^2 * (2 / 10000) := by ring
      have h2 : (δ / 50)^2 = δ^2 * (4 / 10000) := by ring
      rw [h1, h2]
      have h3 : (2 / 10000 : ℝ) ≤ 4 / 10000 := by norm_num
      have h4 : 0 ≤ δ^2 := by positivity
      exact mul_le_mul_of_nonneg_left h3 h4
    have h_sq_le : ‖q1 - q2‖^2 ≤ (δ / 50)^2 := by
      rw [h_norm2]
      have h5 : ((q1 - q2) 0)^2 + ((q1 - q2) 1)^2 + ((q1 - q2) 2)^2 =
          ((q1 - q2) 0)^2 + ((q1 - q2) 1)^2 + 0^2 := by rw [h2] <;> ring
      rw [h5]
      have h_sum : ((q1 - q2) 0)^2 + ((q1 - q2) 1)^2 + 0^2 ≤
          (δ / 100)^2 + (δ / 100)^2 + 0^2 := by
        exact add_le_add (add_le_add h3 h4) (by norm_num)
      exact le_trans h_sum h_arith
    have h_nonneg : 0 ≤ ‖q1 - q2‖ := by positivity
    have h_c_nonneg : 0 ≤ δ / 50 := by positivity
    by_contra h
    have h' : δ / 50 < ‖q1 - q2‖ := by linarith
    have h'' : (δ / 50)^2 < ‖q1 - q2‖^2 := by gcongr <;> linarith
    have h_cont : ‖q1 - q2‖^2 ≤ (δ / 50)^2 := h_sq_le
    linarith

  /- ### Define overlap segment in original coordinates -/
  let s_min : ℝ := -min t1 t2
  let s_max : ℝ := 1 - max t1 t2
  let L : ℝ := s_max - s_min

  have h_max_min : max t1 t2 - min t1 t2 = |t1 - t2| := by
    by_cases h : t1 ≤ t2
    · have hmax : max t1 t2 = t2 := max_eq_right h
      have hmin : min t1 t2 = t1 := min_eq_left h
      have hnonneg : 0 ≤ t2 - t1 := by linarith
      have habs : |t1 - t2| = t2 - t1 := by
        have h' : t1 - t2 ≤ 0 := by linarith
        rw [abs_of_nonpos h'] <;> linarith
      rw [hmax, hmin, habs]
    · have h' : t2 ≤ t1 := by linarith
      have hmax : max t1 t2 = t1 := max_eq_left h'
      have hmin : min t1 t2 = t2 := min_eq_right h'
      have hnonneg : 0 ≤ t1 - t2 := by linarith
      have habs : |t1 - t2| = t1 - t2 := abs_of_nonneg hnonneg
      rw [hmax, hmin, habs]
  have hL_eq : L = 1 - |t1 - t2| := by
    dsimp only [L, s_min, s_max]
    have h : (1 - max t1 t2) - (-min t1 t2) = 1 - (max t1 t2 - min t1 t2) := by ring
    rw [h, h_max_min]
  have hL_eq2 : L = 1 - max t1 t2 + min t1 t2 := by
    dsimp only [L, s_min, s_max] <;> ring
  have hL_ge : L ≥ 7 / 8 := by
    rw [hL_eq]
    have h' : |t1 - t2| ≤ 1 / 8 := htdiff
    linarith
  have hL_pos : 0 < L := by
    rw [hL_eq]
    have h' : |t1 - t2| ≤ 1 / 8 := htdiff
    linarith

  have ht1_nonneg : 0 ≤ t1 := ht1.1
  have ht1_le_one : t1 ≤ 1 := ht1.2
  have ht2_nonneg : 0 ≤ t2 := ht2.1
  have ht2_le_one : t2 ≤ 1 := ht2.2

  set p_overlap : Point3 := T1.base + (t1 + s_min) • T1.direction with hp_overlap_def
  set S_overlap : Set Point3 :=
    (fun t : ℝ => p_overlap + t • T1.direction) '' Set.Icc 0 L with hS_overlap_def

  have hS1_subset : S_overlap ⊆ unitSegment T1.base T1.direction := by
    intro x hx
    rcases hx with ⟨t, ht, rfl⟩
    have ht0 : 0 ≤ t := ht.1
    have htL : t ≤ L := ht.2
    set s : ℝ := s_min + t with hs_def
    have bounds := overlap_arithmetic_bounds t1 t2 t L ht1_nonneg ht1_le_one ht2_nonneg ht2_le_one ht0 htL hL_eq2
    have ⟨_, _, h_param, h_param2, _, _⟩ := bounds
    refine ⟨t1 + s, ⟨h_param, h_param2⟩, ?_⟩
    have h_eq : p_overlap + t • T1.direction = T1.base + (t1 + s) • T1.direction := by
      rw [hp_overlap_def, hs_def]
      simp [add_smul] <;> abel
    exact Eq.symm h_eq

  /- ### Every point of S_overlap is within δ/20 of S2 -/
  have h_close_to_S2 : ∀ x ∈ S_overlap,
      ∃ y ∈ unitSegment T2.base T2.direction, dist x y ≤ 13 * δ / 200 := by
    intro x hx
    rcases hx with ⟨t, ht, rfl⟩
    have ht0 : 0 ≤ t := ht.1
    have htL : t ≤ L := ht.2
    set s : ℝ := s_min + t with hs_def
    have bounds := overlap_arithmetic_bounds t1 t2 t L ht1_nonneg ht1_le_one ht2_nonneg ht2_le_one ht0 htL hL_eq2
    have ⟨h_s_neg, h_s_pos, _, _, hy1, hy2⟩ := bounds
    have h_s_abs : |s| ≤ 1 := abs_le.mpr ⟨h_s_neg, h_s_pos⟩
    let y : Point3 := T2.base + (t2 + s) • T2.direction
    have hy_in : y ∈ unitSegment T2.base T2.direction :=
      ⟨t2 + s, ⟨hy1, hy2⟩, rfl⟩
    have h_dist_frame : ‖(q1 + s • u1) - (q2 + s • u2)‖ ≤ 13 * δ / 200 := by
      calc ‖(q1 + s • u1) - (q2 + s • u2)‖
          = ‖(q1 - q2) + s • (u1 - u2)‖ := by
            have h_eq : (q1 + s • u1) - (q2 + s • u2) =
                (q1 - q2) + s • (u1 - u2) := by simp [smul_sub] <;> abel
            rw [h_eq]
      _ ≤ ‖q1 - q2‖ + ‖s • (u1 - u2)‖ := norm_add_le _ _
      _ = ‖q1 - q2‖ + |s| * ‖u1 - u2‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ δ / 50 + 1 * (9 * δ / 200) := by gcongr <;> linarith
      _ = 13 * δ / 200 := by ring
    have h_key : ∀ (p v : Point3),
        frame (frame.symm p + frame.symm.linearIsometryEquiv v) = p + v := by
      intro p v
      have h1 : frame.symm p + frame.symm.linearIsometryEquiv v =
          frame.symm.linearIsometryEquiv v +ᵥ frame.symm p := by
        ext i; simp [vadd_eq_add, add_comm]
      rw [h1]
      have h2 := frame.map_vadd (frame.symm p) (frame.symm.linearIsometryEquiv v)
      rw [h2]
      have h3 : frame.linearIsometryEquiv (frame.symm.linearIsometryEquiv v) = v :=
        frame.linearIsometryEquiv.apply_symm_apply v
      have h4 : frame (frame.symm p) = p := frame.apply_symm_apply p
      rw [h3, h4]
      ext i; simp [vadd_eq_add, add_comm]
    have h_x_eq : p_overlap + t • T1.direction = frame (q1 + s • u1) := by
      have h_eq1 : q1 + s • u1 =
          frame.symm T1.base + (t1 + s) • frame.symm.linearIsometryEquiv T1.direction := by
        rw [hq1, hp1, hu1] <;> simp [add_smul] <;> abel
      rw [h_eq1]
      have h_smul_symm : frame.symm.linearIsometryEquiv ((t1 + s) • T1.direction) =
          (t1 + s) • frame.symm.linearIsometryEquiv T1.direction :=
        frame.symm.linearIsometryEquiv.map_smul (t1 + s) T1.direction
      have h_key2 := h_key T1.base ((t1 + s) • T1.direction)
      rw [h_smul_symm] at h_key2
      rw [h_key2]
      rw [hp_overlap_def, hs_def]
      have h_add : (t1 + s_min) • T1.direction + t • T1.direction =
          (t1 + (s_min + t)) • T1.direction := by
        have h_scalar : (t1 + s_min) + t = t1 + (s_min + t) := by abel
        rw [← add_smul, h_scalar]
      have h_goal : T1.base + (t1 + s_min) • T1.direction + t • T1.direction =
          T1.base + (t1 + (s_min + t)) • T1.direction := by
        rw [add_assoc, h_add]
      exact h_goal
    have h_y_eq : y = frame (q2 + s • u2) := by
      dsimp only [y]
      have h_eq2 : q2 + s • u2 =
          frame.symm T2.base + (t2 + s) • frame.symm.linearIsometryEquiv T2.direction := by
        rw [hq2, hp2, hu2] <;> simp [add_smul] <;> abel
      have h_smul_symm2 : frame.symm.linearIsometryEquiv ((t2 + s) • T2.direction) =
          (t2 + s) • frame.symm.linearIsometryEquiv T2.direction :=
        frame.symm.linearIsometryEquiv.map_smul (t2 + s) T2.direction
      have h_key3 := h_key T2.base ((t2 + s) • T2.direction)
      rw [h_smul_symm2] at h_key3
      have h_goal : frame (q2 + s • u2) = T2.base + (t2 + s) • T2.direction := by
        rw [h_eq2, h_key3]
      exact h_goal.symm
    have h_dist : dist (p_overlap + t • T1.direction) y ≤ 13 * δ / 200 := by
      rw [h_x_eq, h_y_eq]
      have h_iso : ∀ (a b : Point3), dist (frame a) (frame b) = dist a b := by
        intro a b; exact frame.dist_map a b
      rw [h_iso]; exact h_dist_frame
    exact ⟨y, hy_in, h_dist⟩

  /- ### Contain (187δ/200)-thickening of S_overlap in T1 ∩ T2 -/
  set h_dist : ℝ := 13 * δ / 200 with hh_dist_def
  set r : ℝ := 187 * δ / 200 with hr_def
  have hr_pos : 0 < r := by
    rw [hr_def]
    exact div_pos (mul_pos (by norm_num) hδ) (by norm_num)
  have h_sum : r + h_dist = δ := by
    rw [hr_def, hh_dist_def] <;> ring

  have h_S2_thick : S_overlap ⊆ Metric.cthickening h_dist
      (unitSegment T2.base T2.direction) := by
    intro x hx
    rcases h_close_to_S2 x hx with ⟨y, hy_in, hdist⟩
    exact Metric.mem_cthickening_of_dist_le x y h_dist
      (unitSegment T2.base T2.direction) hy_in hdist

  have hS_nonempty : S_overlap.Nonempty := by
    refine ⟨p_overlap, ?_⟩
    have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) L := by
      constructor <;> linarith [hL_pos]
    have h_eq : p_overlap + (0 : ℝ) • T1.direction = p_overlap := by
      rw [zero_smul, add_zero]
    exact ⟨0, h0, h_eq⟩

  have h_thick_T1 : Metric.cthickening r S_overlap ⊆ T1.carrier := by
    have h1 : Metric.cthickening r S_overlap ⊆
        Metric.cthickening r (unitSegment T1.base T1.direction) :=
      cthickening_set_mono hS1_subset
    have h2 : r ≤ δ := by
      rw [hr_def]
      exact overlap_r_le_delta δ hδ
    have h3 : Metric.cthickening r (unitSegment T1.base T1.direction) ⊆
        Metric.cthickening δ (unitSegment T1.base T1.direction) :=
      Metric.cthickening_mono h2 (unitSegment T1.base T1.direction)
    exact h1.trans h3

  have h_thick_T2 : Metric.cthickening r S_overlap ⊆ T2.carrier := by
    have h1 : Metric.cthickening r S_overlap ⊆
        Metric.cthickening r (Metric.cthickening h_dist
          (unitSegment T2.base T2.direction)) :=
      cthickening_set_mono h_S2_thick
    have h2 : Metric.cthickening r (Metric.cthickening h_dist
          (unitSegment T2.base T2.direction)) ⊆
        Metric.cthickening (r + h_dist) (unitSegment T2.base T2.direction) :=
      Metric.cthickening_cthickening_subset
        (show 0 ≤ r from le_of_lt hr_pos)
        (show 0 ≤ h_dist from by
          rw [hh_dist_def]
          exact overlap_hdist_nonneg δ hδ)
        (unitSegment T2.base T2.direction)
    rw [h_sum] at h2
    exact h1.trans h2

  have h_inter : Metric.cthickening r S_overlap ⊆ T1.carrier ∩ T2.carrier := by
    intro x hx
    exact ⟨h_thick_T1 hx, h_thick_T2 hx⟩

  /- ### Volume lower bound via capsule formula -/
  have h_vol_lower : MeasureTheory.volume (Metric.cthickening r S_overlap) ≥
      ENNReal.ofReal (Real.pi * r^2 * L + (4 / 3 : ℝ) * Real.pi * r^3) := by
    rw [hS_overlap_def]
    exact h_capsule_lower L r hL_pos hr_pos p_overlap T1.direction T1.direction_unit

  have h_vol_inter : MeasureTheory.volume (T1.carrier ∩ T2.carrier) ≥
      ENNReal.ofReal (Real.pi * r^2 * L + (4 / 3 : ℝ) * Real.pi * r^3) :=
    le_trans h_vol_lower (MeasureTheory.measure_mono h_inter)

  apply close_axial_volume_contradiction hδ hδ1 hL_ge
    (T1 := T1) (T2 := T2) (h_capsule_upper := h_capsule_upper)
  simpa [hr_def] using h_vol_inter

end Kakeya.Streamlined.GeometricLemmas
