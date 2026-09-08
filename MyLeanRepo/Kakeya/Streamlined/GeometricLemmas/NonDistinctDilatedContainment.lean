import MyLeanRepo.Kakeya.Streamlined.Geometry
import MyLeanRepo.Kakeya.Streamlined.RogersShephard
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.CapsuleVolume
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.CapsuleBounds
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.DilatedTubeContainment
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.TubeVolume
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.Normed.Lp.Matrix

/-!
# Non-essentially-distinct tubes are contained in a universal dilation

If two radius-`ρ` tubes have intersection volume greater than half the tube volume,
then one carrier is contained in a fixed homothetic dilation of the other.

## Proof route

1. Rogers-Shephard overlap gives `vol(T1-T2) ≤ 128 · V(ρ)` when intersection > V/2.
2. Minkowski difference lower bound gives `vol(T1-T2) ≥ 4ρ · ‖cross d1 d2‖`.
3. Combining gives direction closeness: `‖cross d1 d2‖ ≤ (352π/3)ρ`.
4. Transverse midpoint bound from intersection gives radial closeness.
5. `tube_contained_in_dilated_transverse_general` gives containment in dilation A=1000.

## Main result

- `non_distinct_dilated_containment`: the key geometric leaf.
-/

noncomputable section

open MeasureTheory Metric Set
open scoped Pointwise

namespace Kakeya.Streamlined.GeometricLemmas

/-! ### Tubes are convex -/

lemma deltaTube_carrier_convex {δ : ℝ} (T : Kakeya.DeltaTube δ) :
    Convex ℝ T.carrier := by
  have h1 : Convex ℝ (Kakeya.unitSegment T.base T.direction) := by
    intro x hx y hy a b ha hb hab
    rcases hx with ⟨tx, htx, rfl⟩
    rcases hy with ⟨ty, hty, rfl⟩
    have htx0 : 0 ≤ tx := htx.1
    have htx1 : tx ≤ 1 := htx.2
    have hty0 : 0 ≤ ty := hty.1
    have hty1 : ty ≤ 1 := hty.2
    have hlo : 0 ≤ a * tx + b * ty := by positivity
    have hhi : a * tx + b * ty ≤ 1 := by
      calc
        a * tx + b * ty ≤ a * 1 + b * 1 := by gcongr <;> linarith
        _ = a + b := by ring
        _ = 1 := hab
    have h_eq : a • (T.base + tx • T.direction) + b • (T.base + ty • T.direction) =
        T.base + (a * tx + b * ty) • T.direction := by
      have h2 : a • (T.base + tx • T.direction) + b • (T.base + ty • T.direction) =
          a • T.base + (a * tx) • T.direction + b • T.base + (b * ty) • T.direction := by
        rw [smul_add, smul_add, smul_smul, smul_smul] <;> abel
      have h3 : a • T.base + (a * tx) • T.direction + b • T.base + (b * ty) • T.direction =
          (a + b) • T.base + (a * tx + b * ty) • T.direction := by
        have h4 : a • T.base + (a * tx) • T.direction + b • T.base + (b * ty) • T.direction =
            (a • T.base + b • T.base) + ((a * tx) • T.direction + (b * ty) • T.direction) := by abel
        rw [h4, ← add_smul, ← add_smul] <;> rfl
      rw [h2, h3, hab, one_smul]
    refine ⟨a * tx + b * ty, ⟨hlo, hhi⟩, h_eq.symm⟩
  exact Convex.cthickening h1 δ

/-! ### Cross product helpers -/

def cross (u v : Point3) : Point3 :=
  WithLp.toLp 2 ![u 1 * v 2 - u 2 * v 1,
    u 2 * v 0 - u 0 * v 2,
    u 0 * v 1 - u 1 * v 0]

private lemma inner_eq_sum (u v : Point3) :
    inner ℝ u v = ∑ i : Fin 3, u i * v i := by
  have h1 : inner ℝ u v = ∑ i : Fin 3, inner ℝ (u i) (v i) := by
    rw [PiLp.inner_apply]
  rw [h1]
  apply Finset.sum_congr rfl
  intro i _
  have h : inner ℝ (u i) (v i) = u i * v i := by simp <;> ring
  exact h

private lemma norm_sq_eq_sum (x : Point3) :
    ‖x‖ ^ 2 = ∑ i : Fin 3, (x i) ^ 2 := by
  have h : inner ℝ x x = ‖x‖ ^ 2 := real_inner_self_eq_norm_sq x
  rw [← h, inner_eq_sum]
  simp [pow_two]

lemma cross_norm_sq (u v : Point3) :
    ‖cross u v‖ ^ 2 = ‖u‖ ^ 2 * ‖v‖ ^ 2 - (inner ℝ u v) ^ 2 := by
  have h1 : ‖cross u v‖ ^ 2 = ∑ i : Fin 3, ((cross u v) i) ^ 2 := norm_sq_eq_sum (cross u v)
  have h2 : ‖u‖ ^ 2 = ∑ i : Fin 3, (u i) ^ 2 := norm_sq_eq_sum u
  have h3 : ‖v‖ ^ 2 = ∑ i : Fin 3, (v i) ^ 2 := norm_sq_eq_sum v
  have h4 : inner ℝ u v = ∑ i : Fin 3, u i * v i := inner_eq_sum u v
  rw [h1, h2, h3, h4]
  simp [cross, Fin.sum_univ_succ] <;> ring

lemma triple_product (a b : Point3) :
    cross b (cross a b) = ‖b‖ ^ 2 • a - (inner ℝ a b) • b := by
  ext i
  fin_cases i <;> simp [cross, inner_eq_sum, Fin.sum_univ_succ, norm_sq_eq_sum] <;> ring

lemma perp_norm_eq_cross (u v : Point3) (hv : ‖v‖ = 1) :
    ‖u - (inner ℝ u v) • v‖ = ‖cross u v‖ := by
  set c : ℝ := inner ℝ u v with hc_def
  set w : Point3 := c • v with hw_def
  have h_iuw : inner ℝ u w = c ^ 2 := by
    rw [hw_def, inner_smul_right]
    have h_eq : inner ℝ u v = c := hc_def.symm
    rw [h_eq] <;> ring
  have h_normw : ‖w‖ = |c| := by
    rw [hw_def, norm_smul, hv]
    have h : ‖c‖ = |c| := by
      simp [Real.norm_eq_abs]
    rw [h] <;> ring
  have h_abs2 : |c| ^ 2 = c ^ 2 := by
    rw [sq_abs]
  have h_normw2 : ‖w‖ ^ 2 = c ^ 2 := by
    rw [h_normw, h_abs2]
  have h1 : ‖u - w‖ ^ 2 = ‖u‖ ^ 2 - c ^ 2 := by
    have h_norm : ‖u - w‖ * ‖u - w‖ = ‖u‖ * ‖u‖ - 2 * inner ℝ u w + ‖w‖ * ‖w‖ :=
      norm_sub_mul_self_real u w
    have h_eq : ‖u - w‖ ^ 2 = ‖u‖ ^ 2 - 2 * inner ℝ u w + ‖w‖ ^ 2 := by linarith
    rw [h_eq, h_iuw, h_normw2] <;> ring
  have h2 : ‖cross u v‖ ^ 2 = ‖u‖ ^ 2 - c ^ 2 := by
    rw [cross_norm_sq, hv, hc_def] <;> ring
  have h3 : 0 ≤ ‖u - w‖ := by positivity
  have h4 : 0 ≤ ‖cross u v‖ := by positivity
  nlinarith

/--
For unit vectors, small cross product implies closeness up to orientation.
The relaxed linear constant is convenient in applications.
-/
lemma direction_close_or_reverse_of_cross_le
    {u v : Point3} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    {e : ℝ} (he : 0 ≤ e) (hcross : ‖cross u v‖ ≤ e)
    (he_small : e ≤ 1) :
    ‖u - v‖ ≤ 2 * e ∨ ‖u + v‖ ≤ 2 * e := by
  have hcross_sq :
      ‖cross u v‖ ^ 2 ≤ e ^ 2 := by
    gcongr
  have hinner_sq :
      1 - (inner ℝ u v) ^ 2 ≤ e ^ 2 := by
    rw [cross_norm_sq, hu, hv] at hcross_sq
    norm_num at hcross_sq ⊢
    exact hcross_sq
  have hinner_abs : 1 - e ^ 2 ≤ |inner ℝ u v| := by
    have habs_nonneg : 0 ≤ |inner ℝ u v| := abs_nonneg _
    have habs_sq :
        |inner ℝ u v| ^ 2 = (inner ℝ u v) ^ 2 := sq_abs _
    rw [← habs_sq] at hinner_sq
    nlinarith [sq_nonneg (|inner ℝ u v| - 1),
      abs_real_inner_le_norm u v]
  by_cases hsign : 0 ≤ inner ℝ u v
  · left
    have habs :
        |inner ℝ u v| = inner ℝ u v := abs_of_nonneg hsign
    rw [habs] at hinner_abs
    have hsq :
        ‖u - v‖ ^ 2 = 2 - 2 * inner ℝ u v := by
      rw [norm_sub_sq_real, hu, hv]
      ring
    have hnorm_nonneg : 0 ≤ ‖u - v‖ := norm_nonneg _
    have he2 : 0 ≤ 2 * e := by positivity
    nlinarith
  · right
    have hsign' : inner ℝ u v ≤ 0 := le_of_not_ge hsign
    have habs :
        |inner ℝ u v| = -inner ℝ u v := abs_of_nonpos hsign'
    rw [habs] at hinner_abs
    have hsq :
        ‖u + v‖ ^ 2 = 2 + 2 * inner ℝ u v := by
      rw [norm_add_sq_real, hu, hv]
      ring
    have hnorm_nonneg : 0 ≤ ‖u + v‖ := norm_nonneg _
    have he2 : 0 ≤ 2 * e := by positivity
    nlinarith

def det3 (a b c : Point3) : ℝ :=
  a 0 * (b 1 * c 2 - b 2 * c 1)
  - a 1 * (b 0 * c 2 - b 2 * c 0)
  + a 2 * (b 0 * c 1 - b 1 * c 0)

lemma det3_eq_inner_cross (a b c : Point3) :
    det3 a b c = inner ℝ a (cross b c) := by
  rw [inner_eq_sum, det3]
  simp [cross, Fin.sum_univ_succ] <;> ring

/-! ### Volume lower bound for Minkowski difference -/

lemma minkowski_diff_volume_lower {ρ : ℝ} (hρ : 0 < ρ)
    {p1 p2 d1 d2 : Point3} (hd1 : ‖d1‖ = 1) (hd2 : ‖d2‖ = 1)
    (K L : Set Point3)
    (hK : Metric.cthickening ρ (Kakeya.unitSegment p1 d1) ⊆ K)
    (hL : Metric.cthickening ρ (Kakeya.unitSegment p2 d2) ⊆ L) :
    ENNReal.ofReal (4 * ρ * ‖cross d1 d2‖) ≤
      MeasureTheory.volume (minkowskiDiff K L) := by
  let S1 := Kakeya.unitSegment p1 d1
  let S2 := Kakeya.unitSegment p2 d2
  let B := Metric.closedBall (0 : Point3) ρ
  have hK' : S1 + B ⊆ K := by
    intro p hp
    rcases Set.mem_add.mp hp with ⟨x, hx, y, hy, rfl⟩
    have h_ynorm : ‖y‖ ≤ ρ := by
      simpa [B, Metric.mem_closedBall, dist_eq_norm] using hy
    have h_dist : dist (x + y) x ≤ ρ := by
      simpa [dist_eq_norm] using h_ynorm
    have h_in : x + y ∈ Metric.cthickening ρ S1 :=
      Metric.mem_cthickening_of_dist_le (x + y) x ρ S1 hx h_dist
    exact hK h_in
  have hL' : S2 + B ⊆ L := by
    intro p hp
    rcases Set.mem_add.mp hp with ⟨x, hx, y, hy, rfl⟩
    have h_ynorm : ‖y‖ ≤ ρ := by
      simpa [B, Metric.mem_closedBall, dist_eq_norm] using hy
    have h_dist : dist (x + y) x ≤ ρ := by
      simpa [dist_eq_norm] using h_ynorm
    have h_in : x + y ∈ Metric.cthickening ρ S2 :=
      Metric.mem_cthickening_of_dist_le (x + y) x ρ S2 hx h_dist
    exact hL h_in
  have h_main : (S1 - S2) + Metric.closedBall (0 : Point3) (2 * ρ) ⊆ minkowskiDiff K L := by
    intro p hp
    rcases Set.mem_add.mp hp with ⟨z, hz, w, hw, rfl⟩
    rcases Set.mem_sub.mp hz with ⟨s1, hs1, s2, hs2, rfl⟩
    let w1 := (1 / 2 : ℝ) • w
    let w2 := -(1 / 2 : ℝ) • w
    have hwnorm : ‖w‖ ≤ 2 * ρ := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hw
    have hw1 : ‖w1‖ ≤ ρ := by
      rw [norm_smul]
      calc |(1 / 2 : ℝ)| * ‖w‖ ≤ (1 / 2 : ℝ) * (2 * ρ) := by gcongr <;> norm_num
        _ = ρ := by ring
    have hw2 : ‖w2‖ ≤ ρ := by
      rw [norm_smul]
      calc |-(1 / 2 : ℝ)| * ‖w‖ ≤ (1 / 2 : ℝ) * (2 * ρ) := by gcongr <;> norm_num
        _ = ρ := by ring
    have h1 : s1 + w1 ∈ S1 + B := by
      exact Set.mem_add.mpr ⟨s1, hs1, w1, by
        simpa [B, Metric.mem_closedBall, dist_eq_norm] using hw1, by abel⟩
    have h2 : s2 + w2 ∈ S2 + B := by
      exact Set.mem_add.mpr ⟨s2, hs2, w2, by
        simpa [B, Metric.mem_closedBall, dist_eq_norm] using hw2, by abel⟩
    have h3 : s1 + w1 ∈ K := hK' h1
    have h4 : s2 + w2 ∈ L := hL' h2
    have h_smul : (1 / 2 : ℝ) • w + (1 / 2 : ℝ) • w = w := by
      rw [← add_smul]
      have h2 : (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1 := by norm_num
      rw [h2, one_smul]
    have h5 : (s1 - s2) + w = (s1 + w1) - (s2 + w2) := by
      dsimp only [w1, w2]
      have h_main : (s1 + (1 / 2 : ℝ) • w) - (s2 + (-(1 / 2 : ℝ) • w)) =
          (s1 - s2) + ((1 / 2 : ℝ) • w + (1 / 2 : ℝ) • w) := by
        rw [sub_eq_add_neg, sub_eq_add_neg]
        have h_neg : -(s2 + (-(1 / 2 : ℝ) • w)) = -s2 + (1 / 2 : ℝ) • w := by
          simp [neg_add] <;> abel
        rw [h_neg]
        simp [add_assoc] <;> abel
      rw [h_main, h_smul]
    rw [h5]
    exact Set.mem_sub.mpr ⟨s1 + w1, h3, s2 + w2, h4, rfl⟩
  by_cases h : ‖cross d1 d2‖ = 0
  · rw [h]; simp
  · let n := cross d1 d2
    have hn_pos : 0 < ‖n‖ := by
      have h' : ‖n‖ ≠ 0 := h
      exact lt_of_le_of_ne (norm_nonneg n) (Ne.symm h')
    let m : Matrix (Fin 3) (Fin 3) ℝ := !![
      d1 0, -d2 0, n 0;
      d1 1, -d2 1, n 1;
      d1 2, -d2 2, n 2
    ]
    let f : Point3 →ₗ[ℝ] Point3 := m.toLpLin 2 2
    have hf_eq : ∀ (x : Point3), f x = (x 0) • d1 - (x 1) • d2 + (x 2) • n := by
      intro x
      ext i
      have h : (f x) i = ∑ j : Fin 3, m i j * x j := by rfl
      rw [h]
      fin_cases i <;> simp [m, Fin.sum_univ_succ] <;> ring
    have hdet : LinearMap.det f = -‖n‖ ^ 2 := by
      have h1 : LinearMap.det f = Matrix.det m := LinearMap.det_toLpLin 2 m
      rw [h1]
      have h2 : Matrix.det m = -det3 d1 d2 n := by
        rw [Matrix.det_fin_three]
        simp [m, det3, Fin.sum_univ_succ] <;> ring
      rw [h2]
      have h3 : det3 d1 d2 n = inner ℝ d1 (cross d2 n) := det3_eq_inner_cross d1 d2 n
      rw [h3]
      have h4 : cross d2 n = (1 : ℝ) • d1 - (inner ℝ d1 d2) • d2 := by
        have h41 : cross d2 n = ‖d2‖ ^ 2 • d1 - (inner ℝ d1 d2) • d2 := triple_product d1 d2
        rw [h41, hd2] <;> norm_num
      rw [h4]
      have h5 : inner ℝ d1 ((1 : ℝ) • d1 - (inner ℝ d1 d2) • d2) = ‖n‖ ^ 2 := by
        have h61 : inner ℝ d1 ((1 : ℝ) • d1 - (inner ℝ d1 d2) • d2) =
            inner ℝ d1 ((1 : ℝ) • d1) - inner ℝ d1 ((inner ℝ d1 d2) • d2) := by
          exact inner_sub_right _ _ _
        rw [h61]
        have h62 : inner ℝ d1 ((1 : ℝ) • d1) = ‖d1‖ ^ 2 := by
          rw [inner_smul_right, one_mul, real_inner_self_eq_norm_sq]
        have h63 : inner ℝ d1 ((inner ℝ d1 d2) • d2) = (inner ℝ d1 d2) ^ 2 := by
          rw [inner_smul_right]
          have h_comm : inner ℝ d1 d2 = inner ℝ d2 d1 :=
            (real_inner_comm d1 d2).symm
          rw [h_comm] <;> ring
        rw [h62, h63]
        have h7 : ‖n‖ ^ 2 = ‖d1‖ ^ 2 - (inner ℝ d1 d2) ^ 2 := by
          rw [cross_norm_sq d1 d2, hd2] <;> ring
        linarith
      rw [h5] <;> ring
    have hdet_ne_zero : LinearMap.det f ≠ 0 := by
      rw [hdet]
      have h : (-‖n‖ ^ 2 : ℝ) ≠ 0 := by
        exact neg_ne_zero.mpr (pow_ne_zero 2 hn_pos.ne')
      exact h
    let lo : Fin 3 → ℝ := ![0, 0, -(2 * ρ) / ‖n‖]
    let hi : Fin 3 → ℝ := ![1, 1, (2 * ρ) / ‖n‖]
    have h2pos : 0 ≤ (2 * ρ) / ‖n‖ := by positivity
    have h_box : ∀ i : Fin 3, lo i ≤ hi i := by
      intro i
      fin_cases i
      · simp [lo, hi] <;> norm_num
      · simp [lo, hi] <;> norm_num
      · have h_pos' : 0 ≤ (2 * ρ) / ‖n‖ := h2pos
        have h_goal : -(2 * ρ) / ‖n‖ ≤ (2 * ρ) / ‖n‖ := by
          have h_nonneg : 0 ≤ (2 * ρ) / ‖n‖ := h2pos
          have h_neg : -(2 * ρ) / ‖n‖ ≤ 0 := by
            have h_eq : -(2 * ρ) / ‖n‖ = -((2 * ρ) / ‖n‖) := by rw [neg_div]
            rw [h_eq]
            exact neg_nonpos.mpr h_nonneg
          exact le_trans h_neg h_nonneg
        simpa [lo, hi] using h_goal
    let toLp : (Fin 3 → ℝ) → Point3 := WithLp.toLp 2
    let box_raw : Set (Fin 3 → ℝ) := Set.Icc lo hi
    let box : Set Point3 := toLp '' box_raw
    have h_mp : MeasurePreserving toLp := PiLp.volume_preserving_toLp (ι := Fin 3)
    have h_inj : Function.Injective toLp := WithLp.toLp_injective (p := 2)
    have h_box_raw_meas : MeasurableSet box_raw := measurableSet_Icc
    have h_cont : Continuous toLp := PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 3 => ℝ)
    have h_box_meas : MeasurableSet box :=
      (isCompact_Icc.image h_cont).measurableSet
    have h_box_null : NullMeasurableSet box volume := h_box_meas.nullMeasurableSet
    have h_pre : volume (toLp ⁻¹' box) = volume box :=
      h_mp.measure_preimage h_box_null
    have h_eq : toLp ⁻¹' box = box_raw := by
      ext x
      simp only [box, Set.mem_preimage, Set.mem_image]
      constructor
      · rintro ⟨y, hy, hxy⟩
        have h_x_eq_y : x = y := h_inj hxy.symm
        rw [h_x_eq_y]; exact hy
      · intro hx
        exact ⟨x, hx, rfl⟩
    have h_vol_box : volume box = ENNReal.ofReal (4 * ρ / ‖n‖) := by
      have h : volume box = volume box_raw := by
        calc volume box
          = volume (toLp ⁻¹' box) := h_pre.symm
        _ = volume box_raw := by rw [h_eq]
      rw [h, Real.volume_Icc_pi]
      have h_pos : ∀ i, 0 ≤ hi i - lo i := by
        intro i; have h := h_box i; linarith
      have h9 : (∏ i : Fin 3, ENNReal.ofReal (hi i - lo i)) =
          ENNReal.ofReal ((hi 0 - lo 0) * (hi 1 - lo 1) * (hi 2 - lo 2)) := by
        have h10 : (∏ i : Fin 3, ENNReal.ofReal (hi i - lo i)) =
            ENNReal.ofReal (hi 0 - lo 0) * ENNReal.ofReal (hi 1 - lo 1) * ENNReal.ofReal (hi 2 - lo 2) := by
          simp [Fin.prod_univ_succ] <;> ring
        rw [h10]
        have h11 : 0 ≤ hi 0 - lo 0 := h_pos 0
        have h12 : 0 ≤ hi 1 - lo 1 := h_pos 1
        have h13 : 0 ≤ hi 2 - lo 2 := h_pos 2
        have h_step : ENNReal.ofReal (hi 0 - lo 0) * ENNReal.ofReal (hi 1 - lo 1) =
            ENNReal.ofReal ((hi 0 - lo 0) * (hi 1 - lo 1)) := by
          rw [← ENNReal.ofReal_mul h11]
        rw [h_step]
        have h14 : 0 ≤ (hi 0 - lo 0) * (hi 1 - lo 1) := by positivity
        rw [← ENNReal.ofReal_mul h14] <;> ring
      rw [h9]
      have h14 : (hi 0 - lo 0) * (hi 1 - lo 1) * (hi 2 - lo 2) = 4 * ρ / ‖n‖ := by
        simp [lo, hi] <;> field_simp [hn_pos.ne'] <;> ring
      rw [h14]
    let P0 : Set Point3 :=
      {z | ∃ (t s : ℝ), t ∈ Set.Icc (0 : ℝ) 1 ∧ s ∈ Set.Icc (0 : ℝ) 1 ∧ z = t • d1 - s • d2}
    let shift : Point3 := p1 - p2
    have h_image_subset : f '' box ⊆ P0 + Metric.closedBall (0 : Point3) (2 * ρ) := by
      rintro z ⟨x, hx, rfl⟩
      rcases hx with ⟨y, hy, hxy⟩
      have h_x_eq : x = toLp y := hxy.symm
      have hy0 : 0 ≤ y 0 := hy.1 0
      have hy0' : y 0 ≤ 1 := hy.2 0
      have hy1 : 0 ≤ y 1 := hy.1 1
      have hy1' : y 1 ≤ 1 := hy.2 1
      have hy2 : -(2 * ρ) / ‖n‖ ≤ y 2 := hy.1 2
      have hy2' : y 2 ≤ (2 * ρ) / ‖n‖ := hy.2 2
      let y_vec := (y 0) • d1 - (y 1) • d2
      let w_vec := (y 2) • n
      have h_fx : f x = y_vec + w_vec := by
        rw [hf_eq x]
        have h9 : ∀ i : Fin 3, x i = y i := by
          intro i; rw [h_x_eq]
        have h10 : (x 0) • d1 - (x 1) • d2 + (x 2) • n = y_vec + w_vec := by
          simp [y_vec, w_vec, h9] <;> abel
        exact h10
      rw [h_fx]
      have hy_vec : y_vec ∈ P0 := by
        exact ⟨y 0, y 1, ⟨hy0, hy0'⟩, ⟨hy1, hy1'⟩, by simp [y_vec] <;> abel⟩
      have hw_vec : w_vec ∈ Metric.closedBall (0 : Point3) (2 * ρ) := by
        have h_norm : ‖w_vec‖ = |y 2| * ‖n‖ := by
          rw [norm_smul] <;> rfl
        have h_goal : ‖w_vec‖ ≤ 2 * ρ := by
          rw [h_norm]
          have h_abs : |y 2| ≤ (2 * ρ) / ‖n‖ := by
            by_cases hsign : 0 ≤ y 2
            · rw [abs_of_nonneg hsign]
              exact hy2'
            · rw [abs_of_neg (by linarith)]
              have h5 : -(2 * ρ) / ‖n‖ = -((2 * ρ) / ‖n‖) := by rw [neg_div]
              have h6 : -((2 * ρ) / ‖n‖) ≤ y 2 := by rw [←h5]; exact hy2
              have h : -(y 2) ≤ (2 * ρ) / ‖n‖ := by linarith
              exact h
          calc |y 2| * ‖n‖ ≤ ((2 * ρ) / ‖n‖) * ‖n‖ := by gcongr
            _ = 2 * ρ := by field_simp [hn_pos.ne'] <;> ring
        simpa [Metric.mem_closedBall, dist_eq_norm] using h_goal
      exact Set.mem_add.mpr ⟨y_vec, hy_vec, w_vec, hw_vec, by simp [y_vec, w_vec] <;> abel⟩
    have h_shifted_P0_subset : {shift} + P0 ⊆ S1 - S2 := by
      intro z hz
      rcases Set.mem_add.mp hz with ⟨q, hq, p0, hp0, rfl⟩
      have hq_eq : q = shift := by simpa using hq
      rw [hq_eq]
      have h_exists : ∃ (t s : ℝ), t ∈ Set.Icc (0 : ℝ) 1 ∧ s ∈ Set.Icc (0 : ℝ) 1 ∧ p0 = t • d1 - s • d2 := by
        simpa [P0] using hp0
      rcases h_exists with ⟨t, s, ht, hs, rfl⟩
      refine ⟨p1 + t • d1, ?_, p2 + s • d2, ?_, ?_⟩
      · exact ⟨t, ht, by simp [Kakeya.unitSegment] <;> abel⟩
      · exact ⟨s, hs, by simp [Kakeya.unitSegment] <;> abel⟩
      · simp [Kakeya.unitSegment, shift] <;> abel
    have h1_img : {shift} + f '' box ⊆ {shift} + (P0 + Metric.closedBall (0 : Point3) (2 * ρ)) := by
      intro z hz
      rcases Set.mem_add.mp hz with ⟨q, hq, x, hx, rfl⟩
      have hq' : q = shift := by simpa using hq
      rw [hq']
      have h2 : x ∈ P0 + Metric.closedBall (0 : Point3) (2 * ρ) := h_image_subset hx
      exact Set.mem_add.mpr ⟨shift, by simp, x, h2, by abel⟩
    have h_assoc : {shift} + (P0 + Metric.closedBall (0 : Point3) (2 * ρ)) =
        ({shift} + P0) + Metric.closedBall (0 : Point3) (2 * ρ) := by
      ext z
      simp only [Set.mem_add]
      constructor
      · rintro ⟨a, ha, b, hb, rfl⟩
        rcases hb with ⟨p0, hp0, w, hw, rfl⟩
        exact ⟨a + p0, Set.mem_add.mpr ⟨a, ha, p0, hp0, by abel⟩, w, hw, by abel⟩
      · rintro ⟨x, hx, w, hw, rfl⟩
        rcases hx with ⟨a, ha, p0, hp0, rfl⟩
        exact ⟨a, ha, p0 + w, Set.mem_add.mpr ⟨p0, hp0, w, hw, by abel⟩, by abel⟩
    have h_shifted_image : ({shift} + f '' box) ⊆ minkowskiDiff K L := by
      calc ({shift} + f '' box)
        ⊆ {shift} + (P0 + Metric.closedBall (0 : Point3) (2 * ρ)) := h1_img
      _ = ({shift} + P0) + Metric.closedBall (0 : Point3) (2 * ρ) := h_assoc
      _ ⊆ (S1 - S2) + Metric.closedBall (0 : Point3) (2 * ρ) := by gcongr
      _ ⊆ minkowskiDiff K L := h_main
    have h_vol_image : volume (f '' box) =
        ENNReal.ofReal (|LinearMap.det f|) * volume box :=
      MeasureTheory.Measure.addHaar_image_continuousLinearMap volume f.toContinuousLinearMap box
    have h_vol_transl : volume ({shift} + f '' box) = volume (f '' box) := by
      simpa [measure_preimage_add_right] using rfl
    have h_main_ineq : ENNReal.ofReal (4 * ρ * ‖n‖) ≤ volume ({shift} + f '' box) := by
      rw [h_vol_transl, h_vol_image, hdet, h_vol_box]
      have h_abs : |(-‖n‖ ^ 2 : ℝ)| = ‖n‖ ^ 2 := by
        rw [abs_neg]
        have h_nonneg : 0 ≤ ‖n‖ ^ 2 := by positivity
        rw [abs_of_nonneg h_nonneg]
      rw [h_abs]
      have h_pos1 : 0 ≤ ‖n‖ ^ 2 := by positivity
      have h_pos2 : 0 ≤ 4 * ρ / ‖n‖ := by positivity
      have h_mul : ENNReal.ofReal (‖n‖ ^ 2) * ENNReal.ofReal (4 * ρ / ‖n‖) =
          ENNReal.ofReal (4 * ρ * ‖n‖) := by
        rw [← ENNReal.ofReal_mul h_pos1]
        have h_eq : ‖n‖ ^ 2 * (4 * ρ / ‖n‖) = 4 * ρ * ‖n‖ := by
          field_simp [hn_pos.ne'] <;> ring
        rw [h_eq]
      rw [h_mul]
    exact le_trans h_main_ineq (measure_mono h_shifted_image)

/-! ### Main theorem: non-ED implies dilated containment -/

/--
If two radius-`ρ` tubes are not essentially distinct, then:

* their transverse midpoint displacement is `O(ρ)`;
* their directions are `O(ρ)`-close up to orientation; and
* one carrier lies in the `1000`-dilation of the other.
-/
lemma non_distinct_local_geometry {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (T1 T2 : Kakeya.DeltaTube ρ)
    (h_m1 : ‖tubeMidpoint T1‖ ≤ 3) (h_m2 : ‖tubeMidpoint T2‖ ≤ 3)
    (h_non_ed : ¬T1.EssentiallyDistinct T2) :
    ‖(tubeMidpoint T1 - tubeMidpoint T2) -
        inner ℝ (tubeMidpoint T1 - tubeMidpoint T2) T2.direction •
          T2.direction‖ ≤ 1000 * ρ ∧
      (‖T1.direction - T2.direction‖ ≤ 1000 * ρ ∨
        ‖T1.direction + T2.direction‖ ≤ 1000 * ρ) ∧
      T1.carrier ⊆ dilatedTubeCarrier 1000 T2 := by
  let canonical : Kakeya.DeltaTube ρ :=
    { base := 0
      direction := EuclideanSpace.single (0 : Fin 3) 1
      direction_unit := by simp [EuclideanSpace.norm_eq] <;> norm_num }
  let V := Kakeya.deltaTubeVolume ρ
  have h_vol1 : T1.volume = V := by
    have h : T1.volume = canonical.volume := tube_volume_eq T1 canonical
    rw [h]; rfl
  have h_vol2 : T2.volume = V := by
    have h : T2.volume = canonical.volume := tube_volume_eq T2 canonical
    rw [h]; rfl
  have h_max : max T1.volume T2.volume = V := by
    rw [h_vol1, h_vol2] <;> simp
  have h_non_ed' : ¬ volume (T1.carrier ∩ T2.carrier) ≤ (2 : ENNReal)⁻¹ * max T1.volume T2.volume :=
    h_non_ed
  rw [h_max] at h_non_ed'
  have h_inter_gt : volume (T1.carrier ∩ T2.carrier) > (2 : ENNReal)⁻¹ * V := by
    exact lt_of_not_ge h_non_ed'
  have hV_pos : 0 < V := by
    have h_lower : V ≥ ENNReal.ofReal (Real.pi * ρ ^ 2 + (4 / 3 : ℝ) * Real.pi * ρ ^ 3) := by
      exact capsule_volume_lower ρ hρ
    have h_pos : 0 < Real.pi * ρ ^ 2 + (4 / 3 : ℝ) * Real.pi * ρ ^ 3 := by positivity
    have h_ennreal_pos : 0 < ENNReal.ofReal (Real.pi * ρ ^ 2 + (4 / 3 : ℝ) * Real.pi * ρ ^ 3) :=
      ENNReal.ofReal_pos.mpr h_pos
    exact lt_of_lt_of_le h_ennreal_pos h_lower
  have hV_finite : V ≠ ⊤ := by
    have h_upper : V ≤ ENNReal.ofReal (Real.pi * ρ ^ 2 + (8 / 3 : ℝ) * Real.pi * ρ ^ 3) :=
      capsule_upper_bound_instantiation ρ hρ
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h_upper
  have hT1_pos : 0 < T1.volume := by
    rw [h_vol1] <;> exact hV_pos
  have hT1_finite : T1.volume ≠ ⊤ := by
    rw [h_vol1] <;> exact hV_finite
  have h_inter_pos : 0 < volume (T1.carrier ∩ T2.carrier) := by
    have h : (0 : ENNReal) < (2 : ENNReal)⁻¹ * V := by
      have h2pos : (0 : ENNReal) < (2 : ENNReal)⁻¹ := by simp
      exact ENNReal.mul_pos h2pos.ne' hV_pos.ne'
    exact lt_trans h h_inter_gt
  have h_inter_nonempty : (T1.carrier ∩ T2.carrier).Nonempty := by
    by_contra h
    have h' : T1.carrier ∩ T2.carrier = ∅ := by simpa [Set.not_nonempty_iff_eq_empty] using h
    rw [h'] at h_inter_pos
    simp at h_inter_pos <;> exact h_inter_pos
  have hK_conv : Convex ℝ T1.carrier := deltaTube_carrier_convex T1
  have hL_conv : Convex ℝ T2.carrier := deltaTube_carrier_convex T2
  have h_rs2 : volume (minkowskiDiff T1.carrier T2.carrier) ≤ 128 * V := by
    have h1 : volume (minkowskiDiff T1.carrier T2.carrier) * volume (T1.carrier ∩ T2.carrier) ≤
        64 * T1.volume * T2.volume := rogers_shephard_general hK_conv hL_conv
    have h2 : 64 * T1.volume * T2.volume = 64 * V * V := by
      rw [h_vol1, h_vol2] <;> ring
    rw [h2] at h1
    have h3 : volume (minkowskiDiff T1.carrier T2.carrier) * volume (T1.carrier ∩ T2.carrier) ≤
        (128 * V) * volume (T1.carrier ∩ T2.carrier) := by
      have h128inv : (128 : ENNReal) * (2 : ENNReal)⁻¹ = (64 : ENNReal) := by
        have h_factor : (128 : ENNReal) = (64 : ENNReal) * (2 : ENNReal) := by norm_num
        calc (128 : ENNReal) * (2 : ENNReal)⁻¹
          = ((64 : ENNReal) * (2 : ENNReal)) * (2 : ENNReal)⁻¹ := by rw [h_factor]
        _ = (64 : ENNReal) * ((2 : ENNReal) * (2 : ENNReal)⁻¹) := by rw [mul_assoc]
        _ = (64 : ENNReal) * 1 := by
          have h2 : (2 : ENNReal) * (2 : ENNReal)⁻¹ = 1 := by
            rw [ENNReal.mul_inv_cancel] <;> norm_num
          rw [h2]
        _ = (64 : ENNReal) := by rw [mul_one]
      have h_rearrange : (128 * V) * ((2 : ENNReal)⁻¹ * V) = (128 * (2 : ENNReal)⁻¹) * (V * V) := by
        have h9 : (128 * V) * ((2 : ENNReal)⁻¹ * V) = 128 * (V * ((2 : ENNReal)⁻¹ * V)) := by rw [mul_assoc]
        rw [h9]
        have h10 : V * ((2 : ENNReal)⁻¹ * V) = (V * (2 : ENNReal)⁻¹) * V := by rw [mul_assoc]
        rw [h10]
        have h11 : V * (2 : ENNReal)⁻¹ = (2 : ENNReal)⁻¹ * V := mul_comm V _
        rw [h11]
        have h12 : ((2 : ENNReal)⁻¹ * V) * V = (2 : ENNReal)⁻¹ * (V * V) := by rw [mul_assoc]
        rw [h12, ← mul_assoc]
      calc volume (minkowskiDiff T1.carrier T2.carrier) * volume (T1.carrier ∩ T2.carrier)
        ≤ 64 * V * V := h1
      _ = (128 * V) * ((2 : ENNReal)⁻¹ * V) := by
        rw [h_rearrange, h128inv]
        <;> simp [mul_assoc]
      _ ≤ (128 * V) * volume (T1.carrier ∩ T2.carrier) := by
        gcongr
    have h4 : volume (T1.carrier ∩ T2.carrier) ≠ 0 := h_inter_pos.ne'
    have h5 : volume (T1.carrier ∩ T2.carrier) ≠ ⊤ := by
      have h_sub : T1.carrier ∩ T2.carrier ⊆ T1.carrier := by simp
      have h6 : volume (T1.carrier ∩ T2.carrier) ≤ volume T1.carrier :=
        measure_mono h_sub
      have h7 : volume T1.carrier = T1.volume := by rfl
      rw [h7] at h6
      intro h_top
      rw [h_top] at h6
      have h8 : T1.volume = ⊤ := by simpa using h6
      rw [h_vol1] at h8
      exact hV_finite h8
    have h_cancel : (volume (minkowskiDiff T1.carrier T2.carrier) * volume (T1.carrier ∩ T2.carrier)) / volume (T1.carrier ∩ T2.carrier) =
        volume (minkowskiDiff T1.carrier T2.carrier) := by
      simp [div_eq_mul_inv, mul_assoc, ENNReal.mul_inv_cancel h4 h5]
    have h_result : (volume (minkowskiDiff T1.carrier T2.carrier) * volume (T1.carrier ∩ T2.carrier)) / volume (T1.carrier ∩ T2.carrier) ≤ 128 * V :=
      ENNReal.div_le_of_le_mul h3
    rw [h_cancel] at h_result
    exact h_result
  have h_inter_ge_half : volume (T1.carrier ∩ T2.carrier) ≥ (2 : ENNReal)⁻¹ * V :=
    le_of_lt h_inter_gt
  let d1 := T1.direction
  let d2 := T2.direction
  have hd1 : ‖d1‖ = 1 := T1.direction_unit
  have hd2 : ‖d2‖ = 1 := T2.direction_unit
  have h_lower : ENNReal.ofReal (4 * ρ * ‖cross d1 d2‖) ≤
      volume (minkowskiDiff T1.carrier T2.carrier) :=
    minkowski_diff_volume_lower hρ hd1 hd2 T1.carrier T2.carrier
      (by rfl) (by rfl)
  have h_capsule : V ≤ ENNReal.ofReal (Real.pi * ρ ^ 2 + (8 / 3 : ℝ) * Real.pi * ρ ^ 3) :=
    capsule_upper_bound_instantiation ρ hρ
  have h_comb : ENNReal.ofReal (4 * ρ * ‖cross d1 d2‖) ≤ 128 * V :=
    le_trans h_lower h_rs2
  have h_cross_nonneg : 0 ≤ 4 * ρ * ‖cross d1 d2‖ := by positivity
  have h_V_nonneg : 0 ≤ Real.pi * ρ ^ 2 + (8 / 3 : ℝ) * Real.pi * ρ ^ 3 := by positivity
  have h_real_ineq : 4 * ρ * ‖cross d1 d2‖ ≤
      128 * (Real.pi * ρ ^ 2 + (8 / 3 : ℝ) * Real.pi * ρ ^ 3) := by
    have h1 : ENNReal.ofReal (4 * ρ * ‖cross d1 d2‖) ≤
        ENNReal.ofReal (128 * (Real.pi * ρ ^ 2 + (8 / 3 : ℝ) * Real.pi * ρ ^ 3)) := by
      calc ENNReal.ofReal (4 * ρ * ‖cross d1 d2‖)
        ≤ 128 * V := h_comb
      _ ≤ 128 * ENNReal.ofReal (Real.pi * ρ ^ 2 + (8 / 3 : ℝ) * Real.pi * ρ ^ 3) := by
        gcongr <;> exact h_capsule
      _ = ENNReal.ofReal (128 * (Real.pi * ρ ^ 2 + (8 / 3 : ℝ) * Real.pi * ρ ^ 3)) := by
        have h128 : (128 : ENNReal) = ENNReal.ofReal (128 : ℝ) := by simp
        rw [h128, ← ENNReal.ofReal_mul (by norm_num)]
        <;> rfl
    have h_b_nonneg : 0 ≤ 128 * (Real.pi * ρ ^ 2 + (8 / 3 : ℝ) * Real.pi * ρ ^ 3) := by positivity
    exact (ENNReal.ofReal_le_ofReal_iff h_b_nonneg).mp h1
  have h_cross_bound : ‖cross d1 d2‖ ≤ (352 : ℝ) / 3 * Real.pi * ρ := by
    have h_pos : 0 < ρ := hρ
    have h : 4 * ρ * ‖cross d1 d2‖ ≤ 128 * (Real.pi * ρ ^ 2 + (8 / 3 : ℝ) * Real.pi * ρ ^ 3) := h_real_ineq
    have h4pos : 0 < 4 * ρ := by positivity
    have h2 : ‖cross d1 d2‖ ≤ 32 * Real.pi * ρ + (256 : ℝ) / 3 * Real.pi * ρ ^ 2 := by
      have h_div1 : (4 * ρ * ‖cross d1 d2‖) / (4 * ρ) = ‖cross d1 d2‖ := by
        field_simp [h4pos.ne'] <;> ring
      have h_div3 : (128 * (Real.pi * ρ ^ 2 + (8 / 3 : ℝ) * Real.pi * ρ ^ 3)) / (4 * ρ) =
          32 * Real.pi * ρ + (256 : ℝ) / 3 * Real.pi * ρ ^ 2 := by
        field_simp [h4pos.ne'] <;> ring
      calc ‖cross d1 d2‖
        = (4 * ρ * ‖cross d1 d2‖) / (4 * ρ) := h_div1.symm
      _ ≤ (128 * (Real.pi * ρ ^ 2 + (8 / 3 : ℝ) * Real.pi * ρ ^ 3)) / (4 * ρ) := by gcongr
      _ = 32 * Real.pi * ρ + (256 : ℝ) / 3 * Real.pi * ρ ^ 2 := h_div3
    have h3 : 32 * Real.pi * ρ + (256 : ℝ) / 3 * Real.pi * ρ ^ 2 ≤ (352 : ℝ) / 3 * Real.pi * ρ := by
      have h4 : ρ ^ 2 ≤ ρ := by nlinarith
      nlinarith [Real.pi_pos]
    linarith
  set m1 := tubeMidpoint T1 with hm1
  set m2 := tubeMidpoint T2 with hm2
  have h_perp_dir : ‖d1 - inner ℝ d1 d2 • d2‖ = ‖cross d1 d2‖ :=
    perp_norm_eq_cross d1 d2 hd2
  have h_trans_mid : ‖(m1 - m2) - inner ℝ (m1 - m2) d2 • d2‖ ≤
      2 * ρ + (1 / 2 : ℝ) * ‖d1 - inner ℝ d1 d2 • d2‖ :=
    transverse_midpoint_bound_of_intersection hρ T1 T2 h_inter_nonempty
  have h_trans :
      ‖(m1 - m2) - inner ℝ (m1 - m2) d2 • d2‖ +
      (1 / 2 : ℝ) * ‖d1 - inner ℝ d1 d2 • d2‖ ≤ (1000 - 1) * ρ := by
    calc
      ‖(m1 - m2) - inner ℝ (m1 - m2) d2 • d2‖ +
          (1 / 2 : ℝ) * ‖d1 - inner ℝ d1 d2 • d2‖
        ≤ (2 * ρ + (1 / 2 : ℝ) * ‖d1 - inner ℝ d1 d2 • d2‖) +
            (1 / 2 : ℝ) * ‖d1 - inner ℝ d1 d2 • d2‖ := by gcongr
      _ = 2 * ρ + ‖d1 - inner ℝ d1 d2 • d2‖ := by ring
      _ = 2 * ρ + ‖cross d1 d2‖ := by rw [h_perp_dir]
      _ ≤ 2 * ρ + (352 : ℝ) / 3 * Real.pi * ρ := by gcongr
      _ ≤ (1000 - 1) * ρ := by
        have hpi : Real.pi ≤ 4 := Real.pi_le_four
        nlinarith [hpi]
  have h_trans_mid_bound :
      ‖(tubeMidpoint T1 - tubeMidpoint T2) -
          inner ℝ (tubeMidpoint T1 - tubeMidpoint T2) T2.direction •
            T2.direction‖ ≤ 1000 * ρ := by
    simpa [m1, m2, d1, d2] using
      (calc
        ‖(m1 - m2) - inner ℝ (m1 - m2) d2 • d2‖
            ≤ 2 * ρ +
              (1 / 2 : ℝ) *
                ‖d1 - inner ℝ d1 d2 • d2‖ := h_trans_mid
        _ = 2 * ρ + (1 / 2 : ℝ) * ‖cross d1 d2‖ := by
          rw [h_perp_dir]
        _ ≤ 2 * ρ +
            (1 / 2 : ℝ) * ((352 : ℝ) / 3 * Real.pi * ρ) := by
          gcongr
        _ ≤ 1000 * ρ := by
          nlinarith [Real.pi_le_four])
  have h_direction_local :
      ‖T1.direction - T2.direction‖ ≤ 1000 * ρ ∨
        ‖T1.direction + T2.direction‖ ≤ 1000 * ρ := by
    let e : ℝ := (352 : ℝ) / 3 * Real.pi * ρ
    have he : 0 ≤ e := by
      dsimp only [e]
      positivity
    by_cases he_one : e ≤ 1
    · have hlocal :=
        direction_close_or_reverse_of_cross_le hd1 hd2 he
          h_cross_bound he_one
      rcases hlocal with hlocal | hlocal
      · left
        exact hlocal.trans (by
          dsimp only [e] at hlocal ⊢
          nlinarith [Real.pi_le_four])
      · right
        exact hlocal.trans (by
          dsimp only [e] at hlocal ⊢
          nlinarith [Real.pi_le_four])
    · left
      have he_large : 1 < e := lt_of_not_ge he_one
      have hnorm : ‖d1 - d2‖ ≤ 2 := by
        calc
          ‖d1 - d2‖ ≤ ‖d1‖ + ‖d2‖ := norm_sub_le _ _
          _ = 2 := by rw [hd1, hd2] <;> norm_num
      simpa [d1, d2] using hnorm.trans (by
        dsimp only [e] at he_large
        nlinarith [Real.pi_le_four])
  refine ⟨h_trans_mid_bound, h_direction_local, ?_⟩
  exact tube_contained_in_dilated_transverse_general
    hρ hρ1 (1000 : ℝ) (3 : ℝ)
    (by norm_num) (by norm_num) T1 T2 h_m1 h_m2 h_trans

/-- Compatibility export of the containment conclusion. -/
lemma non_distinct_dilated_containment {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (T1 T2 : Kakeya.DeltaTube ρ)
    (h_m1 : ‖tubeMidpoint T1‖ ≤ 3) (h_m2 : ‖tubeMidpoint T2‖ ≤ 3)
    (h_non_ed : ¬T1.EssentiallyDistinct T2) :
    T1.carrier ⊆ dilatedTubeCarrier 1000 T2 :=
  (non_distinct_local_geometry hρ hρ1 T1 T2
    h_m1 h_m2 h_non_ed).2.2

end Kakeya.Streamlined.GeometricLemmas
