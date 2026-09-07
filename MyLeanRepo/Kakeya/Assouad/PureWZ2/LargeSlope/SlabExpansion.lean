import MyLeanRepo.Kakeya.Assouad.Definitions
import MyLeanRepo.Kakeya.Assouad.Statements
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition3_2PaperStatements
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperTubeCarrierGeometryHelpers

/-!
# Slab expansion geometry for density+CWA cancellation

Given a slab W containing a point p from a tube's paper carrier, and a slab
normal n that is nearly perpendicular to the tube direction d (|inner(d,n)| ≤ K),
expand W by O(δ) to contain the FULL paper carrier of that tube.

Key estimate: for any q in the paper carrier,
|inner(q-p, n)| ≤ 12δ + (12δ + 2√3)·K

Proof:
- Extract axis line witnesses yp, yq within 6δ of p, q
- Both p,q ∈ axisBox, so dist(p,q) ≤ 2√3
- dist(yp,yq) ≤ dist(yp,p) + dist(p,q) + dist(q,yq) ≤ 6δ + 2√3 + 6δ = 12δ + 2√3
- |inner(yp-yq,n)| = |tp-tq|·|inner(d,n)| ≤ dist(yp,yq)·K ≤ (12δ+2√3)·K
- |inner(q-p,n)| ≤ |inner(q-yq,n)| + |inner(yq-yp,n)| + |inner(yp-p,n)|
                 ≤ 6δ + (12δ+2√3)K + 6δ
-/

noncomputable section

open Metric Set

namespace Kakeya.Assouad

/--
Slab expansion lemma: if a point p from a tube's paper carrier lies in a
slab centered at c with normal n and width w, and the tube direction d is
nearly perpendicular to n (|inner(d,n)| ≤ K), then the FULL paper carrier
lies in the expanded slab with width w + 12*δ + (12*δ + 2*Real.sqrt 3)*K.
-/
lemma paper_carrier_in_expanded_slab
    {delta : ℝ} (hdelta : 0 < delta)
    {T : Kakeya.DeltaTube delta}
    {n c : Point3} {w K : ℝ}
    (hn_unit : ‖n‖ = 1)
    (_hK : 0 ≤ K)
    (hinc : |inner ℝ T.direction n| ≤ K)
    {p : Point3}
    (hp_in_carrier : p ∈ wz1PaperTubeCarrier T)
    (hp_in_slab : |inner ℝ (p - c) n| ≤ w) :
    ∀ q ∈ wz1PaperTubeCarrier T,
      |inner ℝ (q - c) n| ≤ w + 12 * delta + (12 * delta + 2 * Real.sqrt 3) * K := by
  intro q hq

  -- Extract axis line witnesses using closed thickening property
  have h_closed : IsClosed (tubeAxisLine T) := isClosed_tubeAxisLine T
  have h_pos : 0 ≤ 6 * delta := by positivity
  rcases exists_dist_le_of_mem_cthickening_closed h_closed h_pos hp_in_carrier.1
    with ⟨yp, hyp_mem, hyp_dist⟩
  rcases exists_dist_le_of_mem_cthickening_closed h_closed h_pos hq.1
    with ⟨yq, hyq_mem, hyq_dist⟩

  rcases hyp_mem with ⟨tp, rfl⟩
  rcases hyq_mem with ⟨tq, rfl⟩
  let yp := T.base + tp • T.direction
  let yq := T.base + tq • T.direction

  -- Both p and q are in axisBox
  have hp_box : p ∈ Kakeya.Streamlined.axisBox 2 2 2 := hp_in_carrier.2
  have hq_box : q ∈ Kakeya.Streamlined.axisBox 2 2 2 := hq.2

  -- Distance between p and q is bounded by axisBox diameter
  have h_pq_dist : dist p q ≤ 2 * Real.sqrt 3 := by
    rcases hp_box with ⟨h10, h11, h12⟩
    rcases hq_box with ⟨h40, h41, h42⟩
    have h1 : ∀ i : Fin 3, |p i| ≤ 1 := by
      intro i; fin_cases i <;> norm_num at * <;> tauto
    have h4 : ∀ i : Fin 3, |q i| ≤ 1 := by
      intro i; fin_cases i <;> norm_num at * <;> tauto
    have h5 : ‖p - q‖ ^ 2 = ∑ i : Fin 3, (p i - q i)^2 :=
      EuclideanSpace.real_norm_sq_eq (p - q)
    have h6 : ∀ i : Fin 3, (p i - q i)^2 ≤ 4 := by
      intro i
      have h7 : |p i - q i| ≤ 2 := by
        calc |p i - q i| ≤ |p i| + |q i| := abs_sub _ _
             _ ≤ 1 + 1 := by linarith [h1 i, h4 i]
             _ = 2 := by norm_num
      have h8 : (p i - q i)^2 ≤ 4 := by
        calc (p i - q i)^2 = |p i - q i|^2 := by rw [sq_abs]
             _ ≤ 2^2 := by gcongr
             _ = 4 := by norm_num
      exact h8
    have h7 : ‖p - q‖ ^ 2 ≤ 12 := by
      rw [h5]
      have hsum : ∑ i : Fin 3, (p i - q i)^2 ≤ 12 := by
        have h9 : (p 0 - q 0)^2 ≤ 4 := h6 0
        have h10 : (p 1 - q 1)^2 ≤ 4 := h6 1
        have h11 : (p 2 - q 2)^2 ≤ 4 := h6 2
        have h12 : ∑ i : Fin 3, (p i - q i)^2 = (p 0 - q 0)^2 + (p 1 - q 1)^2 + (p 2 - q 2)^2 := by
          simp [Fin.sum_univ_succ] <;> ring
        rw [h12]
        linarith
      exact hsum
    have h8 : ‖p - q‖ ≤ 2 * Real.sqrt 3 := by
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    simpa [dist_eq_norm] using h8

  -- Distance between yp and yq
  have h_yp_yq_dist : dist yp yq ≤ 12 * delta + 2 * Real.sqrt 3 := by
    have h_tri1 : dist yp yq ≤ dist yp p + dist p yq := dist_triangle yp p yq
    have h_tri2 : dist p yq ≤ dist p q + dist q yq := dist_triangle p q yq
    calc dist yp yq
        ≤ dist yp p + dist p yq := h_tri1
      _ ≤ dist yp p + (dist p q + dist q yq) := by gcongr
      _ = dist p yp + dist p q + dist q yq := by
          rw [dist_comm yp p] <;> ring
      _ ≤ 6 * delta + 2 * Real.sqrt 3 + 6 * delta := by gcongr
      _ = 12 * delta + 2 * Real.sqrt 3 := by ring

  -- inner product difference along axis
  have h_axis_inner : |inner ℝ (yp - yq) n| ≤ (12 * delta + 2 * Real.sqrt 3) * K := by
    have h_eq : yp - yq = (tp - tq) • T.direction := by
      simp [yp, yq, sub_smul]
    rw [h_eq]
    have h : inner ℝ ((tp - tq) • T.direction) n = (tp - tq) * inner ℝ T.direction n := by
      simp [inner_smul_left]
    rw [h, abs_mul]
    have h_t_diff : |tp - tq| ≤ dist yp yq := by
      have h9 : ‖(tp - tq) • T.direction‖ = |tp - tq| * ‖T.direction‖ := by
        rw [norm_smul, Real.norm_eq_abs]
      have h10 : ‖yp - yq‖ = |tp - tq| := by
        have h11 : yp - yq = (tp - tq) • T.direction := by
          simp [yp, yq, sub_smul]
        rw [h11, h9, T.direction_unit] <;> ring
      have h12 : dist yp yq = ‖yp - yq‖ := dist_eq_norm yp yq
      rw [h12, h10]
    have h_nonneg1 : 0 ≤ |inner ℝ T.direction n| := abs_nonneg _
    have h_t_diff' : |tp - tq| ≤ 12 * delta + 2 * Real.sqrt 3 :=
      le_trans h_t_diff h_yp_yq_dist
    have h_coeff_nonneg : 0 ≤ 12 * delta + 2 * Real.sqrt 3 := by positivity
    calc |tp - tq| * |inner ℝ T.direction n|
        ≤ (12 * delta + 2 * Real.sqrt 3) * |inner ℝ T.direction n| := by
          exact mul_le_mul_of_nonneg_right h_t_diff' h_nonneg1
      _ ≤ (12 * delta + 2 * Real.sqrt 3) * K := by
          exact mul_le_mul_of_nonneg_left hinc h_coeff_nonneg

  -- Perpendicular differences
  have h_perp_p : |inner ℝ (p - yp) n| ≤ 6 * delta := by
    calc |inner ℝ (p - yp) n|
        ≤ ‖p - yp‖ * ‖n‖ := abs_real_inner_le_norm (p - yp) n
      _ = ‖p - yp‖ := by rw [hn_unit] <;> ring
      _ = dist p yp := by rfl
      _ ≤ 6 * delta := hyp_dist
  have h_perp_q : |inner ℝ (q - yq) n| ≤ 6 * delta := by
    calc |inner ℝ (q - yq) n|
        ≤ ‖q - yq‖ * ‖n‖ := abs_real_inner_le_norm (q - yq) n
      _ = ‖q - yq‖ := by rw [hn_unit] <;> ring
      _ = dist q yq := by rfl
      _ ≤ 6 * delta := hyq_dist

  -- Total bound for inner(q-p, n)
  let ia := inner ℝ (q - yq) n
  let ib := inner ℝ (yq - yp) n
  let ic := inner ℝ (yp - p) n
  have h_qp : inner ℝ (q - p) n = ia + ib + ic := by
    have h : q - p = (q - yq) + (yq - yp) + (yp - p) := by abel
    rw [h]
    rw [inner_add_left, inner_add_left]
  have h_abs_a : |ia| ≤ 6 * delta := h_perp_q
  have h_abs_b : |ib| ≤ (12 * delta + 2 * Real.sqrt 3) * K := by
    have h_eq : ib = -inner ℝ (yp - yq) n := by
      simp [ib, ← inner_neg_left, neg_sub]
    rw [h_eq, abs_neg]
    exact h_axis_inner
  have h_abs_c : |ic| ≤ 6 * delta := by
    have h_eq : ic = -inner ℝ (p - yp) n := by
      simp [ic, ← inner_neg_left, neg_sub]
    rw [h_eq, abs_neg]
    exact h_perp_p
  have h_sum_bound : |ia + ib + ic| ≤ |ia| + |ib| + |ic| := by
    have h1 : ‖ia + ib + ic‖ ≤ ‖ia‖ + ‖ib‖ + ‖ic‖ := by
      calc ‖ia + ib + ic‖
          ≤ ‖ia + ib‖ + ‖ic‖ := norm_add_le (ia + ib) ic
        _ ≤ ‖ia‖ + ‖ib‖ + ‖ic‖ := by gcongr <;> exact norm_add_le ia ib
    simpa [Real.norm_eq_abs] using h1
  have h_main : |inner ℝ (q - p) n| ≤
      6 * delta + (12 * delta + 2 * Real.sqrt 3) * K + 6 * delta := by
    rw [h_qp]
    calc |ia + ib + ic|
        ≤ |ia| + |ib| + |ic| := h_sum_bound
      _ ≤ 6 * delta + (12 * delta + 2 * Real.sqrt 3) * K + 6 * delta := by
        linarith [h_abs_a, h_abs_b, h_abs_c]

  -- Final: inner(q-c,n) = inner(p-c,n) + inner(q-p,n)
  have h_decomp : inner ℝ (q - c) n = inner ℝ (p - c) n + inner ℝ (q - p) n := by
    rw [← inner_add_left] <;> abel
  rw [h_decomp]
  set x := inner ℝ (p - c) n with hx_def
  set y := inner ℝ (q - p) n with hy_def
  have h_tri : |x + y| ≤ |x| + |y| := by
    simpa [Real.norm_eq_abs] using norm_add_le x y
  calc |x + y|
      ≤ |x| + |y| := h_tri
    _ ≤ w + (6 * delta + (12 * delta + 2 * Real.sqrt 3) * K + 6 * delta) := by
      gcongr
    _ = w + 12 * delta + (12 * delta + 2 * Real.sqrt 3) * K := by ring

end Kakeya.Assouad

end
