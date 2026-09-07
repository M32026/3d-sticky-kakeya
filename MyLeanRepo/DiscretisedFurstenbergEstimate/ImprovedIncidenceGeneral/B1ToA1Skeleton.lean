module

/-
  B1 bridge output → A1_Output conversion skeleton.

  Takes coarse and fine configurations from the B1 induction bridge
  and produces an A1_Output suitable for the Appendix A contradiction chain.

  Each major sub-step is a `sorry` with an OBLIGATION comment.
  These obligations can be assigned in parallel.

  NOTE: Avoids importing DyadicBridge (which pulls in InductionOnScales
  with EuclideanPlane := ℝ×ℝ) because AppendixA.Interfaces uses
  EuclideanPlane := EuclideanSpace ℝ (Fin 2). The center map is
  defined locally.

  Whiteprint node: b1_to_a1_conversion
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.LocalSquareCenter
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicCardToNcover
public import MyLeanRepo.DiscretisedFurstenbergEstimate.CoordinatePartition
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.Interfaces
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A1_Assembly
public import MyLeanRepo.DiscretisedFurstenbergEstimate.BallGrowth
public import MyLeanRepo.DiscretisedFurstenbergEstimate.HeavySquareRefinement
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Phase2Support
public import MyLeanRepo.DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral.SlopeBoundFromStrip
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicToAffineAdapters
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral

open DiscretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.AppendixA
open DirecretisedFurstenbergEstimate.Lagoon
open DirecretisedFurstenbergEstimate.Phase2
open DirecretisedFurstenbergEstimate.AppendixA.A1_Assembly
open CoordinatePartition
open DyadicCardToNcover


/-- `localSquareCenter` is injective. -/
lemma localSquareCenter_injective {n : ℕ} :
    Function.Injective (localSquareCenter (n := n)) := by
  intro q1 q2 h
  have h0 : (localSquareCenter q1) 0 = (localSquareCenter q2) 0 := by rw [h]
  have h1 : (localSquareCenter q1) 1 = (localSquareCenter q2) 1 := by rw [h]
  have hδ_pos : 0 < dyadicDelta n := dyadicDelta_pos n
  set δ := dyadicDelta n with hδ
  have h_eq0 : ((q1.i : ℝ) + 1 / 2) * δ = ((q2.i : ℝ) + 1 / 2) * δ := by
    simpa [localSquareCenter] using h0
  have h_eq1 : ((q1.j : ℝ) + 1 / 2) * δ = ((q2.j : ℝ) + 1 / 2) * δ := by
    simpa [localSquareCenter] using h1
  have hi : (q1.i : ℝ) = (q2.i : ℝ) := by
    apply (mul_right_inj' hδ_pos.ne').mp
    linarith
  have hj : (q1.j : ℝ) = (q2.j : ℝ) := by
    apply (mul_right_inj' hδ_pos.ne').mp
    linarith
  have hi' : q1.i = q2.i := by exact_mod_cast hi
  have hj' : q1.j = q2.j := by exact_mod_cast hj
  cases q1 <;> cases q2 <;> simp_all <;> tauto

/-- Centers of distinct dyadic squares are at least δ apart (local version). -/
lemma localSquareCenter_distinct_separated {n : ℕ} (q1 q2 : DyadicSquare n) (hne : q1 ≠ q2) :
    dyadicDelta n ≤ dist (localSquareCenter q1) (localSquareCenter q2) := by
  set δ := dyadicDelta n with hδ
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  set c1 := localSquareCenter q1 with hc1
  set c2 := localSquareCenter q2 with hc2
  set v := c1 - c2 with hv
  have hc10 : c1 0 = ((q1.i : ℝ) + 1 / 2) * δ := by
    have h : (localSquareCenter q1) 0 = ((q1.i : ℝ) + 1 / 2) * dyadicDelta n := by
      simp [localSquareCenter] <;> norm_num
    simpa [c1, hδ] using h
  have hc11 : c1 1 = ((q1.j : ℝ) + 1 / 2) * δ := by
    have h : (localSquareCenter q1) 1 = ((q1.j : ℝ) + 1 / 2) * dyadicDelta n := by
      simp [localSquareCenter] <;> norm_num
    simpa [c1, hδ] using h
  have hc20 : c2 0 = ((q2.i : ℝ) + 1 / 2) * δ := by
    have h : (localSquareCenter q2) 0 = ((q2.i : ℝ) + 1 / 2) * dyadicDelta n := by
      simp [localSquareCenter] <;> norm_num
    simpa [c2, hδ] using h
  have hc21 : c2 1 = ((q2.j : ℝ) + 1 / 2) * δ := by
    have h : (localSquareCenter q2) 1 = ((q2.j : ℝ) + 1 / 2) * dyadicDelta n := by
      simp [localSquareCenter] <;> norm_num
    simpa [c2, hδ] using h
  have h_norm_sq : ‖v‖ ^ 2 = (v 0) ^ 2 + (v 1) ^ 2 := by
    have h_pos : 0 ≤ (v 0) ^ 2 + (v 1) ^ 2 := by positivity
    have h : ‖v‖ = Real.sqrt ((v 0) ^ 2 + (v 1) ^ 2) := by
      simp [EuclideanSpace.norm_eq, Fin.sum_univ_two] <;> rfl
    rw [h, Real.sq_sqrt h_pos]
  have h_abs_le_norm0 : |v 0| ≤ ‖v‖ := by
    have h : (v 0) ^ 2 ≤ ‖v‖ ^ 2 := by
      rw [h_norm_sq] <;> nlinarith [sq_nonneg (v 1)]
    have h2 : 0 ≤ |v 0| := by positivity
    have h3 : 0 ≤ ‖v‖ := by positivity
    nlinarith [sq_abs (v 0)]
  have h_abs_le_norm1 : |v 1| ≤ ‖v‖ := by
    have h : (v 1) ^ 2 ≤ ‖v‖ ^ 2 := by
      rw [h_norm_sq] <;> nlinarith [sq_nonneg (v 0)]
    have h2 : 0 ≤ |v 1| := by positivity
    have h3 : 0 ≤ ‖v‖ := by positivity
    nlinarith [sq_abs (v 1)]
  have h_coord : (q1.i ≠ q2.i) ∨ (q1.j ≠ q2.j) := by
    by_contra h
    push Not at h
    have h_i : q1.i = q2.i := h.1
    have h_j : q1.j = q2.j := h.2
    have h_eq : q1 = q2 := by
      cases q1 <;> cases q2 <;> simp_all <;> tauto
    exact hne h_eq
  rcases h_coord with (h_i | h_j)
  · have h_int : (1 : ℝ) ≤ |(q1.i : ℝ) - (q2.i : ℝ)| := by
      have h1 : q1.i - q2.i ≠ 0 := by omega
      have h2 : (1 : ℤ) ≤ |q1.i - q2.i| := Int.one_le_abs h1
      exact_mod_cast h2
    have h_diff0 : v 0 = δ * ((q1.i : ℝ) - (q2.i : ℝ)) := by
      have hv0 : v 0 = c1 0 - c2 0 := by simp [v]
      rw [hv0, hc10, hc20] <;> ring
    have h_abs0 : δ ≤ |v 0| := by
      rw [h_diff0, abs_mul, abs_of_pos hδ_pos]
      have h3 : δ * |(q1.i : ℝ) - (q2.i : ℝ)| ≥ δ * 1 := by gcongr
      linarith
    have h5 : δ ≤ ‖v‖ := by
      calc δ ≤ |v 0| := h_abs0
           _ ≤ ‖v‖ := h_abs_le_norm0
    have h_goal : dist c1 c2 = ‖v‖ := by rw [dist_eq_norm, hv]
    rw [h_goal]; exact h5
  · have h_int : (1 : ℝ) ≤ |(q1.j : ℝ) - (q2.j : ℝ)| := by
      have h1 : q1.j - q2.j ≠ 0 := by omega
      have h2 : (1 : ℤ) ≤ |q1.j - q2.j| := Int.one_le_abs h1
      exact_mod_cast h2
    have h_diff1 : v 1 = δ * ((q1.j : ℝ) - (q2.j : ℝ)) := by
      have hv1 : v 1 = c1 1 - c2 1 := by simp [v]
      rw [hv1, hc11, hc21] <;> ring
    have h_abs1 : δ ≤ |v 1| := by
      rw [h_diff1, abs_mul, abs_of_pos hδ_pos]
      have h3 : δ * |(q1.j : ℝ) - (q2.j : ℝ)| ≥ δ * 1 := by gcongr
      linarith
    have h5 : δ ≤ ‖v‖ := by
      calc δ ≤ |v 1| := h_abs1
           _ ≤ ‖v‖ := h_abs_le_norm1
    have h_goal : dist c1 c2 = ‖v‖ := by rw [dist_eq_norm, hv]
    rw [h_goal]; exact h5

/-- `lineOfSlopeIntercept` is injective in (m, b). -/
lemma lineOfSlopeIntercept_injective {m1 m2 b1 b2 : ℝ}
    (h : DyadicCardToNcover.lineOfSlopeIntercept m1 b1 =
         DyadicCardToNcover.lineOfSlopeIntercept m2 b2) :
    m1 = m2 ∧ b1 = b2 := by
  let v1 := DyadicCardToNcover.tubeDirV m1
  let dir1 := Submodule.span ℝ {v1}
  let v2 := DyadicCardToNcover.tubeDirV m2
  let dir2 := Submodule.span ℝ {v2}
  let p1 := TubesAndSlopes.mkPlane 0 b1
  let p2 := TubesAndSlopes.mkPlane 0 b2
  have h_sub : (DyadicCardToNcover.lineOfSlopeIntercept m1 b1).1 =
                (DyadicCardToNcover.lineOfSlopeIntercept m2 b2).1 :=
    congr_arg Subtype.val h
  let L1 := (DyadicCardToNcover.lineOfSlopeIntercept m1 b1).1
  let L2 := (DyadicCardToNcover.lineOfSlopeIntercept m2 b2).1
  have h_dir : dir1 = dir2 := by
    have h1 : L1.direction = dir1 := DyadicCardToNcover.lineOfSlopeIntercept_direction m1 b1
    have h2 : L2.direction = dir2 := DyadicCardToNcover.lineOfSlopeIntercept_direction m2 b2
    have h3 : L1.direction = L2.direction := by rw [show L1 = L2 from h_sub]
    rw [h1, h2] at *
    <;> tauto
  have h_v1_in_dir2 : v1 ∈ dir2 := by
    rw [←h_dir]; exact Submodule.subset_span (by simp)
  rcases Submodule.mem_span_singleton.mp h_v1_in_dir2 with ⟨c, hc⟩
  have h_v1_0 : v1 0 = 1 := by
    simp [v1, DyadicCardToNcover.tubeDirV, TubesAndSlopes.mkPlane_apply0]
  have h_v2_0 : v2 0 = 1 := by
    simp [v2, DyadicCardToNcover.tubeDirV, TubesAndSlopes.mkPlane_apply0]
  have hc1 : c = 1 := by
    have h_eq0 : v1 0 = (c • v2) 0 := by rw [hc]
    have h_eq1 : (c • v2) 0 = c * (v2 0) := by simp
    rw [h_eq1] at h_eq0
    rw [h_v1_0, h_v2_0] at h_eq0 <;> linarith
  have h_v1_eq_v2 : v1 = v2 := by
    calc v1 = c • v2 := hc.symm
         _ = (1 : ℝ) • v2 := by rw [hc1]
         _ = v2 := by simp
  have hm : m1 = m2 := by
    have h : v1 1 = v2 1 := by rw [h_v1_eq_v2]
    have h_v1_1 : v1 1 = m1 := by
      simp [v1, DyadicCardToNcover.tubeDirV, TubesAndSlopes.mkPlane_apply1]
    have h_v2_1 : v2 1 = m2 := by
      simp [v2, DyadicCardToNcover.tubeDirV, TubesAndSlopes.mkPlane_apply1]
    rw [h_v1_1, h_v2_1] at h
    exact h
  have h_p1_in_L1 : p1 ∈ L1 := by
    have h_L1_eq : L1 = AffineSubspace.mk' p1 dir1 := by
      simp [L1, DyadicCardToNcover.lineOfSlopeIntercept]
      <;> rfl
    rw [h_L1_eq]
    have h : p1 - p1 ∈ dir1 := by simp
    simpa [AffineSubspace.mem_mk'] using h
  have h_p1_in_L2 : p1 ∈ L2 := by
    rw [show L1 = L2 from h_sub] at h_p1_in_L1
    exact h_p1_in_L1
  have h_L2_eq : L2 = AffineSubspace.mk' p2 dir2 := by
    simp [L2, DyadicCardToNcover.lineOfSlopeIntercept] <;> rfl
  have h_diff : p1 - p2 ∈ dir2 := by
    rw [h_L2_eq] at h_p1_in_L2
    simpa [AffineSubspace.mem_mk'] using h_p1_in_L2
  rcases Submodule.mem_span_singleton.mp h_diff with ⟨d, hd⟩
  have h_p1_p2_0 : (p1 - p2) 0 = 0 := by
    simp [p1, p2, TubesAndSlopes.mkPlane_apply0]
  have hd1 : d = 0 := by
    have h_eq0 : (p1 - p2) 0 = (d • v2) 0 := by rw [hd]
    have h_eq1 : (d • v2) 0 = d * (v2 0) := by simp
    rw [h_eq1] at h_eq0
    rw [h_p1_p2_0, h_v2_0] at h_eq0 <;> linarith
  have h_p1_p2_1 : (p1 - p2) 1 = b1 - b2 := by
    simp [p1, p2, TubesAndSlopes.mkPlane_apply1] <;> ring
  have h_eq1 : (p1 - p2) 1 = (d • v2) 1 := by rw [hd]
  have h_eq2 : (d • v2) 1 = d * (v2 1) := by simp
  rw [h_eq2] at h_eq1
  rw [h_p1_p2_1, hd1] at h_eq1
  have h_b : b1 - b2 = 0 := by linarith
  have hb : b1 = b2 := by linarith
  exact ⟨hm, hb⟩

/-- `toAffineLine` is injective on DyadicTubes. -/
lemma toAffineLine_injective {n : ℕ} :
    Function.Injective (DyadicCardToNcover.toAffineLine (n := n)) := by
  intro T1 T2 h
  have h_slopes : T1.slope = T2.slope := (lineOfSlopeIntercept_injective h).1
  have h_intercepts : T1.intercept = T2.intercept := (lineOfSlopeIntercept_injective h).2
  have ha : T1.a = T2.a := by
    have hδ_pos : 0 < dyadicDelta n := dyadicDelta_pos n
    have h : (T1.a : ℝ) * dyadicDelta n = (T2.a : ℝ) * dyadicDelta n := by
      simpa [DyadicTube.slope] using h_slopes
    have h' : (T1.a : ℝ) = (T2.a : ℝ) := by
      have h'' : dyadicDelta n * (T1.a : ℝ) = dyadicDelta n * (T2.a : ℝ) := by
        ring_nf at h ⊢ <;> exact h
      exact (mul_right_inj' hδ_pos.ne').mp h''
    exact_mod_cast h'
  have hb : T1.b = T2.b := by
    have hδ_pos : 0 < dyadicDelta n := dyadicDelta_pos n
    have h : (T1.b : ℝ) * dyadicDelta n = (T2.b : ℝ) * dyadicDelta n := by
      simpa [DyadicTube.intercept] using h_intercepts
    have h' : (T1.b : ℝ) = (T2.b : ℝ) := by
      have h'' : dyadicDelta n * (T1.b : ℝ) = dyadicDelta n * (T2.b : ℝ) := by
        ring_nf at h ⊢ <;> exact h
      exact (mul_right_inj' hδ_pos.ne').mp h''
    exact_mod_cast h'
  cases T1 <;> cases T2 <;> simp_all <;> tauto

/-- If a dyadic tube intersects a dyadic square in the unit grid and |slope| ≤ 1,
    then |intercept| ≤ 2. Geometric bound gives < 2+δ; quantization rounds down to ≤2. -/
lemma dyadic_tube_intercept_le_two {n : ℕ} {t : DyadicTube n} {q : DyadicSquare n}
    (h_slope : |t.slope| ≤ 1)
    (h_inter : (t.toSet ∩ q.toSet).Nonempty)
    (hqi : 0 ≤ q.i) (hqi' : q.i < (2 ^ n : ℤ))
    (hqj : 0 ≤ q.j) (hqj' : q.j < (2 ^ n : ℤ)) :
    |t.intercept| ≤ 2 := by
  set δ := dyadicDelta n with hδ
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  rcases h_inter with ⟨p, hpT, hpQ⟩
  have hx1 : (q.i : ℝ) * δ ≤ p 0 := hpQ.1
  have hx2 : p 0 < ((q.i : ℝ) + 1) * δ := hpQ.2.1
  have hy1 : (q.j : ℝ) * δ ≤ p 1 := hpQ.2.2.1
  have hy2 : p 1 < ((q.j : ℝ) + 1) * δ := hpQ.2.2.2
  have htube : |p 1 - t.slope * p 0 - t.intercept| ≤ δ := hpT
  have htube1 : p 1 - t.slope * p 0 - t.intercept ≤ δ := (abs_le.mp htube).2
  have htube2 : -δ ≤ p 1 - t.slope * p 0 - t.intercept := (abs_le.mp htube).1
  have hqi_pos : 0 ≤ (q.i : ℝ) * δ := by positivity
  have hqj_pos : 0 ≤ (q.j : ℝ) * δ := by positivity
  have h_p0_nonneg : 0 ≤ p 0 := by linarith [hx1, hqi_pos]
  have h_p1_nonneg : 0 ≤ p 1 := by linarith [hy1, hqj_pos]
  have h_qi_le : (q.i : ℝ) + 1 ≤ (2 ^ n : ℝ) := by
    have h : q.i + 1 ≤ (2 ^ n : ℤ) := by omega
    exact_mod_cast h
  have h_qj_le : (q.j : ℝ) + 1 ≤ (2 ^ n : ℝ) := by
    have h : q.j + 1 ≤ (2 ^ n : ℤ) := by omega
    exact_mod_cast h
  have h_qi_le_one : ((q.i : ℝ) + 1) * δ ≤ 1 := by
    have h2 : ((q.i : ℝ) + 1) * δ ≤ (2 ^ n : ℝ) * δ := by gcongr
    have h3 : (2 ^ n : ℝ) * δ = 1 := by simp [hδ, dyadicDelta] <;> norm_num
    linarith
  have h_qj_le_one : ((q.j : ℝ) + 1) * δ ≤ 1 := by
    have h2 : ((q.j : ℝ) + 1) * δ ≤ (2 ^ n : ℝ) * δ := by gcongr
    have h3 : (2 ^ n : ℝ) * δ = 1 := by simp [hδ, dyadicDelta] <;> norm_num
    linarith
  have h_p1_lt_one : p 1 < 1 := by
    calc p 1 < ((q.j : ℝ) + 1) * δ := hy2
         _ ≤ 1 := h_qj_le_one
  have h_slope_p0_le_one : |t.slope| * p 0 ≤ 1 := by
    have h : |t.slope| * p 0 < 1 := by
      calc |t.slope| * p 0 ≤ 1 * p 0 := by gcongr <;> exact h_slope
        _ = p 0 := by ring
        _ < ((q.i : ℝ) + 1) * δ := hx2
        _ ≤ 1 := h_qi_le_one
    exact le_of_lt h
  have h_upper : t.intercept < 2 + δ := by
    have h1 : t.intercept ≤ p 1 + |t.slope| * p 0 + δ := by
      have h2 : -t.slope * p 0 ≤ |t.slope| * p 0 := by
        have h3 : -t.slope ≤ |t.slope| := by exact neg_le_abs t.slope
        nlinarith [h_p0_nonneg]
      linarith
    linarith [h_p1_lt_one, h_slope_p0_le_one]
  have h_lower : -(2 + δ) < t.intercept := by
    have h1 : t.intercept ≥ p 1 - |t.slope| * p 0 - δ := by
      have h2 : t.slope * p 0 ≤ |t.slope| * p 0 := by
        have h3 : t.slope ≤ |t.slope| := by exact le_abs_self t.slope
        nlinarith [h_p0_nonneg]
      linarith
    linarith [h_p1_nonneg, h_slope_p0_le_one]
  have h_abs : |t.intercept| < 2 + δ := abs_lt.mpr ⟨h_lower, h_upper⟩
  have h_eq : t.intercept = (t.b : ℝ) * δ := by
    simp [DyadicTube.intercept, hδ]
    <;> ring
  rw [h_eq] at h_abs
  have h_abs_delta : |δ| = δ := abs_of_pos hδ_pos
  have h9 : |(t.b : ℝ)| * δ < 2 + δ := by
    have h10 : |(t.b : ℝ) * δ| = |(t.b : ℝ)| * |δ| := by rw [abs_mul]
    rw [h10, h_abs_delta] at h_abs
    exact h_abs
  have h10 : |(t.b : ℝ)| < 2 / δ + 1 := by
    have h11 : |(t.b : ℝ)| * δ < 2 + δ := h9
    have h12 : |(t.b : ℝ)| < (2 + δ) / δ := by
      calc |(t.b : ℝ)|
        = (|(t.b : ℝ)| * δ) / δ := by field_simp [hδ_pos.ne'] <;> ring
      _ < (2 + δ) / δ := by gcongr
    have h13 : (2 + δ) / δ = 2 / δ + 1 := by
      field_simp [hδ_pos.ne'] <;> ring
    rw [h13] at h12
    exact h12
  have h14 : 2 / δ = 2 * (2 ^ n : ℝ) := by
    simp [hδ, dyadicDelta] <;> field_simp <;> norm_num
  rw [h14] at h10
  have h15 : |t.b| < 2 * (2 ^ n) + 1 := by exact_mod_cast h10
  have h16 : |t.b| ≤ 2 * (2 ^ n) := by omega
  have h17 : |(t.b : ℝ)| * δ ≤ (2 * (2 ^ n : ℝ)) * δ := by gcongr <;> exact_mod_cast h16
  have h18 : (2 * (2 ^ n : ℝ)) * δ = 2 := by simp [hδ, dyadicDelta] <;> norm_num
  have h19 : |(t.b : ℝ)| * δ ≤ 2 := by
    rw [h18] at h17
    exact h17
  have h20 : |t.intercept| ≤ 2 := by
    rw [h_eq]
    have h21 : |(t.b : ℝ) * δ| = |(t.b : ℝ)| * δ := by
      rw [abs_mul]
      <;> rw [abs_of_pos hδ_pos]
    rw [h21]
    exact h19
  exact h20

/-- Swapping a tube line preserves slope magnitude and intercept.
    After swap, tubeSlope = original slope (so ≤1), and tubeIntercept = original intercept. -/
lemma swapped_tube_params {n : ℕ} (t : DyadicTube n) (h_slope : |t.slope| ≤ 1) :
    (LemmaE.getDirV (swapLine (toAffineLine t))) 1 ≠ 0 ∧
    |tubeSlope (swapLine (toAffineLine t))| ≤ 1 ∧
    tubeIntercept (swapLine (toAffineLine t)) = t.intercept := by
  set m := t.slope with hm
  set b := t.intercept with hb
  let ℓ := toAffineLine t
  let ℓ' := swapLine ℓ
  let v' := LemmaE.getDirV ℓ'
  have hv'_dir : v' ∈ ℓ'.1.direction := (LemmaE.getDirV_spec ℓ').1
  have hv'_ne : v' ≠ 0 := (LemmaE.getDirV_spec ℓ').2

  -- Direction of original and swapped line
  have h_dir1 : ℓ.1.direction = ℝ ∙ tubeDirV m :=
    lineOfSlopeIntercept_direction m b
  have h_swap_vec : swapCoords (tubeDirV m) = TubesAndSlopes.mkPlane m 1 := by
    simp [tubeDirV, swapCoords, TubesAndSlopes.mkPlane] <;> ext i <;> fin_cases i <;> simp <;> ring
  have h_dir3 : ℓ'.1.direction = ℝ ∙ TubesAndSlopes.mkPlane m 1 := by
    have h_map : ℓ'.1.direction = Submodule.map (swapCoordsLI : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)) ℓ.1.direction :=
      AffineSubspace.map_direction _ ℓ.1
    rw [h_map, h_dir1]
    have h : Submodule.map (swapCoordsLI : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2)) (ℝ ∙ tubeDirV m) =
        ℝ ∙ swapCoords (tubeDirV m) := by
      simp [Submodule.map_span] <;> rfl
    rw [h, h_swap_vec]

  -- v' is nonzero scalar multiple of (m, 1)
  have h_exists : ∃ (c : ℝ), c ≠ 0 ∧ v' = c • TubesAndSlopes.mkPlane m 1 := by
    rw [h_dir3] at hv'_dir
    have h7 : ∃ (c : ℝ), c • TubesAndSlopes.mkPlane m 1 = v' := by
      rw [Submodule.mem_span_singleton] at hv'_dir <;> exact hv'_dir
    rcases h7 with ⟨c, hc⟩
    refine ⟨c, ?_, hc.symm⟩
    by_contra hc0
    rw [hc0, zero_smul] at hc
    exact hv'_ne hc.symm
  rcases h_exists with ⟨c, hc_ne, hvc⟩
  have h_v1 : v' 1 = c := by rw [hvc] <;> simp [TubesAndSlopes.mkPlane] <;> ring
  have h_v0 : v' 0 = c * m := by rw [hvc] <;> simp [TubesAndSlopes.mkPlane] <;> ring
  have h1 : v' 1 ≠ 0 := by rw [h_v1] <;> exact hc_ne

  -- Slope of swapped line equals m
  have h_slope_eq : tubeSlope ℓ' = m := by
    have h3 : tubeSlope ℓ' = v' 0 / v' 1 := by
      have h_def : tubeSlope ℓ' = (LemmaE.affineLineParams ℓ').1 := by rfl
      rw [h_def]
      have h4 : (LemmaE.affineLineParams ℓ').1 =
          if v' 1 = 0 then 0 else v' 0 / v' 1 := by
        simp only [LemmaE.affineLineParams]
        <;> rfl
      rw [h4, if_neg h1]
    rw [h3, h_v0, h_v1] <;> field_simp [hc_ne] <;> ring
  have h2 : |tubeSlope ℓ'| ≤ 1 := by rw [h_slope_eq] <;> exact h_slope

  -- Points on original line: (0, b) and (1, m+b)
  have h_p1 : TubesAndSlopes.mkPlane 0 b ∈ ℓ.1 := by
    have h_def : ℓ.1 = AffineSubspace.mk' (TubesAndSlopes.mkPlane 0 b) (Submodule.span ℝ {tubeDirV m}) := by
      rfl
    rw [h_def]
    have h_mem : (0 : EuclideanSpace ℝ (Fin 2)) +ᵥ TubesAndSlopes.mkPlane 0 b ∈
        AffineSubspace.mk' (TubesAndSlopes.mkPlane 0 b) (ℝ ∙ tubeDirV m) :=
      AffineSubspace.vadd_mem_mk' (TubesAndSlopes.mkPlane 0 b) (Submodule.zero_mem _)
    have h_zero : (0 : EuclideanSpace ℝ (Fin 2)) +ᵥ TubesAndSlopes.mkPlane 0 b = TubesAndSlopes.mkPlane 0 b := by simp
    rw [h_zero] at h_mem
    exact h_mem
  have h_p2 : TubesAndSlopes.mkPlane 1 (m + b) ∈ ℓ.1 := by
    have h_eq : TubesAndSlopes.mkPlane 1 (m + b) = TubesAndSlopes.mkPlane 0 b + tubeDirV m := by
      ext i; fin_cases i <;> simp [tubeDirV, TubesAndSlopes.mkPlane] <;> ring
    rw [h_eq]
    have h_dir : tubeDirV m ∈ ℓ.1.direction := by
      rw [h_dir1] <;> exact Submodule.mem_span_singleton.mpr ⟨1, by simp⟩
    have h_vadd : tubeDirV m +ᵥ TubesAndSlopes.mkPlane 0 b ∈ ℓ.1 :=
      (AffineSubspace.vadd_mem_iff_mem_direction (tubeDirV m) h_p1).mpr h_dir
    have h_comm : tubeDirV m +ᵥ TubesAndSlopes.mkPlane 0 b = TubesAndSlopes.mkPlane 0 b + tubeDirV m := by
      ext i; fin_cases i <;> simp [tubeDirV, TubesAndSlopes.mkPlane] <;> ring
    rw [h_comm] at h_vadd
    exact h_vadd

  -- Swapped points: (b, 0) and (m+b, 1) are on ℓ'
  have h_set : (ℓ'.1 : Set (EuclideanSpace ℝ (Fin 2))) = swapCoords '' (ℓ.1 : Set (EuclideanSpace ℝ (Fin 2))) :=
    swapLine_set_eq ℓ
  have h_q1 : TubesAndSlopes.mkPlane b 0 ∈ ℓ'.1 := by
    have h_goal : TubesAndSlopes.mkPlane b 0 ∈ (ℓ'.1 : Set (EuclideanSpace ℝ (Fin 2))) := by
      rw [h_set]
      refine ⟨TubesAndSlopes.mkPlane 0 b, h_p1, ?_⟩
      ext i <;> fin_cases i <;> simp [swapCoords, TubesAndSlopes.mkPlane] <;> ring
    exact h_goal
  have h_q2 : TubesAndSlopes.mkPlane (m + b) 1 ∈ ℓ'.1 := by
    have h_goal : TubesAndSlopes.mkPlane (m + b) 1 ∈ (ℓ'.1 : Set (EuclideanSpace ℝ (Fin 2))) := by
      rw [h_set]
      refine ⟨TubesAndSlopes.mkPlane 1 (m + b), h_p2, ?_⟩
      ext i <;> fin_cases i <;> simp [swapCoords, TubesAndSlopes.mkPlane] <;> ring
    exact h_goal

  -- Use affineLineParams_correct to derive intercept
  let a' := tubeSlope ℓ'
  let b' := tubeIntercept ℓ'
  have h_correct : ∀ (q : EuclideanSpace ℝ (Fin 2)), q ∈ ℓ'.1 → q 0 = a' * q 1 + b' :=
    LemmaE.affineLineParams_correct ℓ' h1
  have h_eq1 : b = a' * 0 + b' := h_correct (TubesAndSlopes.mkPlane b 0) h_q1
  have h_eq2 : m + b = a' * 1 + b' := h_correct (TubesAndSlopes.mkPlane (m + b) 1) h_q2
  have h_b' : b' = b := by linarith
  have h4 : tubeIntercept ℓ' = b := by
    simpa [b'] using h_b'
  exact ⟨h1, h2, h4⟩

-- ========================================================================
-- Helper: coordinate formulas and norm bound for localSquareCenter
-- ========================================================================

lemma localSquareCenter_coord0 {n : ℕ} (q : DyadicSquare n) :
    (localSquareCenter q) 0 = ((q.i : ℝ) + 1 / 2) * dyadicDelta n := by
  unfold localSquareCenter
  <;> simp
  <;> rfl

lemma localSquareCenter_coord1 {n : ℕ} (q : DyadicSquare n) :
    (localSquareCenter q) 1 = ((q.j : ℝ) + 1 / 2) * dyadicDelta n := by
  unfold localSquareCenter
  <;> simp
  <;> rfl

lemma localSquareCenter_norm_le_sqrt2 {n : ℕ} (q : DyadicSquare n)
    (h_i_nonneg : 0 ≤ q.i) (h_i_lt : q.i < (2 ^ n : ℤ))
    (h_j_nonneg : 0 ≤ q.j) (h_j_lt : q.j < (2 ^ n : ℤ)) :
    ‖localSquareCenter q‖ ≤ Real.sqrt 2 := by
  set x := localSquareCenter q with hx
  have h_x0_eq : x 0 = ((q.i : ℝ) + 1 / 2) * dyadicDelta n := localSquareCenter_coord0 q
  have h_x1_eq : x 1 = ((q.j : ℝ) + 1 / 2) * dyadicDelta n := localSquareCenter_coord1 q
  have hδn_pos : 0 < dyadicDelta n := dyadicDelta_pos n
  have h_i_nonneg' : 0 ≤ (q.i : ℝ) := by exact_mod_cast h_i_nonneg
  have h_j_nonneg' : 0 ≤ (q.j : ℝ) := by exact_mod_cast h_j_nonneg
  have h_i_real : (q.i : ℝ) + 1 ≤ (2 ^ n : ℝ) := by
    have h_int : q.i + 1 ≤ (2 ^ n : ℤ) := by linarith
    have h1 : ((q.i + 1 : ℤ) : ℝ) ≤ ((2 ^ n : ℤ) : ℝ) := by exact_mod_cast h_int
    have h2 : ((q.i + 1 : ℤ) : ℝ) = (q.i : ℝ) + 1 := by simp
    have h3 : ((2 ^ n : ℤ) : ℝ) = (2 ^ n : ℝ) := by simp
    rw [h2, h3] at h1; exact h1
  have h_j_real : (q.j : ℝ) + 1 ≤ (2 ^ n : ℝ) := by
    have h_int : q.j + 1 ≤ (2 ^ n : ℤ) := by linarith
    have h1 : ((q.j + 1 : ℤ) : ℝ) ≤ ((2 ^ n : ℤ) : ℝ) := by exact_mod_cast h_int
    have h2 : ((q.j + 1 : ℤ) : ℝ) = (q.j : ℝ) + 1 := by simp
    have h3 : ((2 ^ n : ℤ) : ℝ) = (2 ^ n : ℝ) := by simp
    rw [h2, h3] at h1; exact h1
  have h_x0_nonneg : 0 ≤ x 0 := by
    rw [h_x0_eq]
    have h1 : 0 ≤ (q.i : ℝ) + 1 / 2 := by linarith
    exact mul_nonneg h1 hδn_pos.le
  have h_x1_nonneg : 0 ≤ x 1 := by
    rw [h_x1_eq]
    have h1 : 0 ≤ (q.j : ℝ) + 1 / 2 := by linarith
    exact mul_nonneg h1 hδn_pos.le
  have hδn_eq : dyadicDelta n = 1 / (2 : ℝ)^n := by rfl
  have h_x0_le1 : x 0 ≤ 1 := by
    rw [h_x0_eq, hδn_eq]
    have hpos : 0 < (2 : ℝ)^n := by positivity
    have h5 : (q.i : ℝ) + 1 / 2 ≤ (2 ^ n : ℝ) - 1 / 2 := by linarith
    have h6 : ((q.i : ℝ) + 1 / 2) * (1 / (2 : ℝ)^n) ≤ ((2 ^ n : ℝ) - 1 / 2) * (1 / (2 : ℝ)^n) := by gcongr <;> positivity
    have h7 : ((2 ^ n : ℝ) - 1 / 2) * (1 / (2 : ℝ)^n) ≤ 1 := by field_simp [hpos.ne'] <;> linarith
    exact le_trans h6 h7
  have h_x1_le1 : x 1 ≤ 1 := by
    rw [h_x1_eq, hδn_eq]
    have hpos : 0 < (2 : ℝ)^n := by positivity
    have h5 : (q.j : ℝ) + 1 / 2 ≤ (2 ^ n : ℝ) - 1 / 2 := by linarith
    have h6 : ((q.j : ℝ) + 1 / 2) * (1 / (2 : ℝ)^n) ≤ ((2 ^ n : ℝ) - 1 / 2) * (1 / (2 : ℝ)^n) := by gcongr <;> positivity
    have h7 : ((2 ^ n : ℝ) - 1 / 2) * (1 / (2 : ℝ)^n) ≤ 1 := by field_simp [hpos.ne'] <;> linarith
    exact le_trans h6 h7
  have h_norm_eq : ‖x‖ = Real.sqrt ((x 0)^2 + (x 1)^2) := by
    simp [EuclideanSpace.norm_eq, Fin.sum_univ_two] <;> ring_nf
  have h_sq_le2 : (x 0)^2 + (x 1)^2 ≤ 2 := by nlinarith
  have h_norm_le : ‖x‖ ≤ Real.sqrt 2 := by
    rw [h_norm_eq]
    apply Real.sqrt_le_sqrt
    exact h_sq_le2
  exact h_norm_le

-- ========================================================================
-- Geometric lemmas: center bounds from unit-ball intersection
-- ========================================================================

/-- Coordinate-wise distance from any point in a dyadic square to its center. -/
lemma localSquareCenter_coord_dist {n : ℕ} (q : DyadicSquare n)
    (p : EuclideanSpace ℝ (Fin 2)) (hp : p ∈ q.toSet) :
    |p 0 - (localSquareCenter q) 0| ≤ (dyadicDelta n) / 2 ∧
    |p 1 - (localSquareCenter q) 1| ≤ (dyadicDelta n) / 2 := by
  set δ := dyadicDelta n with hδ
  set c := localSquareCenter q with hc
  have h_c0 : c 0 = ((q.i : ℝ) + 1 / 2) * δ := localSquareCenter_coord0 q
  have h_c1 : c 1 = ((q.j : ℝ) + 1 / 2) * δ := localSquareCenter_coord1 q
  have h_p01 : (q.i : ℝ) * δ ≤ p 0 := hp.1
  have h_p02 : p 0 < ((q.i : ℝ) + 1) * δ := hp.2.1
  have h_p11 : (q.j : ℝ) * δ ≤ p 1 := hp.2.2.1
  have h_p12 : p 1 < ((q.j : ℝ) + 1) * δ := hp.2.2.2
  constructor
  · rw [h_c0, abs_sub_le_iff] <;> constructor <;> linarith
  · rw [h_c1, abs_sub_le_iff] <;> constructor <;> linarith

/-- Distance from any point in a dyadic square to its center is at most δ√2/2. -/
lemma localSquareCenter_dist_to_point {n : ℕ} (q : DyadicSquare n)
    (p : EuclideanSpace ℝ (Fin 2)) (hp : p ∈ q.toSet) :
    dist p (localSquareCenter q) ≤ (dyadicDelta n) * Real.sqrt 2 / 2 := by
  set δ := dyadicDelta n with hδ
  set c := localSquareCenter q with hc
  have h_coords := localSquareCenter_coord_dist q p hp
  have h0 : |p 0 - c 0| ≤ δ / 2 := h_coords.1
  have h1 : |p 1 - c 1| ≤ δ / 2 := h_coords.2
  have h_dist_eq : dist p c = Real.sqrt ((p 0 - c 0)^2 + (p 1 - c 1)^2) := by
    have h1 : dist p c = ‖p - c‖ := by rw [dist_eq_norm]
    rw [h1]
    have h2 : ‖p - c‖ = Real.sqrt (((p - c) 0)^2 + ((p - c) 1)^2) := by
      simp [EuclideanSpace.norm_eq, Fin.sum_univ_two] <;> rfl
    rw [h2]
    have h3 : (p - c) 0 = p 0 - c 0 := by simp
    have h4 : (p - c) 1 = p 1 - c 1 := by simp
    rw [h3, h4]
  rw [h_dist_eq]
  have h_sq : (p 0 - c 0)^2 + (p 1 - c 1)^2 ≤ (δ * Real.sqrt 2 / 2)^2 := by
    have h2 : (p 0 - c 0)^2 ≤ (δ / 2)^2 := by
      have h21 : (p 0 - c 0)^2 = |p 0 - c 0|^2 := by rw [sq_abs]
      rw [h21]; gcongr <;> linarith
    have h3 : (p 1 - c 1)^2 ≤ (δ / 2)^2 := by
      have h31 : (p 1 - c 1)^2 = |p 1 - c 1|^2 := by rw [sq_abs]
      rw [h31]; gcongr <;> linarith
    have h4 : (δ * Real.sqrt 2 / 2)^2 = 2 * (δ / 2)^2 := by
      calc (δ * Real.sqrt 2 / 2)^2
        = δ^2 * (Real.sqrt 2)^2 / 4 := by ring
      _ = δ^2 * 2 / 4 := by rw [Real.sq_sqrt (by norm_num)]
      _ = 2 * (δ / 2)^2 := by ring
    rw [h4]; linarith
  have h_nonneg : 0 ≤ (p 0 - c 0)^2 + (p 1 - c 1)^2 := by positivity
  have h_goal : Real.sqrt ((p 0 - c 0)^2 + (p 1 - c 1)^2) ≤ Real.sqrt ((δ * Real.sqrt 2 / 2)^2) :=
    Real.sqrt_le_sqrt h_sq
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  have h_rhs : Real.sqrt ((δ * Real.sqrt 2 / 2)^2) = δ * Real.sqrt 2 / 2 := by
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg]
    · have h : 0 ≤ δ * Real.sqrt 2 / 2 := by positivity
      exact h
  rw [h_rhs] at h_goal
  exact h_goal

/-- If a dyadic square intersects a set P contained in the unit ball,
    its center coordinates are bounded by 1 + δ/2. -/
lemma localSquareCenter_coord_near_ball {n : ℕ} {P : Set (EuclideanSpace ℝ (Fin 2))}
    (hP : P ⊆ Metric.closedBall 0 1)
    (q : DyadicSquare n)
    (h_inter : (P ∩ (q.toSet : Set (EuclideanSpace ℝ (Fin 2)))).Nonempty) :
    |(localSquareCenter q) 0| ≤ 1 + (dyadicDelta n) / 2 ∧
    |(localSquareCenter q) 1| ≤ 1 + (dyadicDelta n) / 2 := by
  rcases h_inter with ⟨p, hpP, hpq⟩
  have h_pball : p ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 := hP hpP
  have h_pnorm : ‖p‖ ≤ 1 := by simpa [Metric.mem_closedBall] using h_pball
  have h_p0_abs : |p 0| ≤ ‖p‖ := by
    have h_norm_eq : ‖p‖ = Real.sqrt ((p 0)^2 + (p 1)^2) := by
      simp [EuclideanSpace.norm_eq, Fin.sum_univ_two] <;> rfl
    have h_norm_sq : ‖p‖^2 = (p 0)^2 + (p 1)^2 := by
      rw [h_norm_eq]
      rw [Real.sq_sqrt] <;> nlinarith
    have h : (p 0)^2 ≤ ‖p‖^2 := by rw [h_norm_sq]; nlinarith [sq_nonneg (p 1)]
    have h_abs : 0 ≤ |p 0| := by positivity
    have h_norm_nonneg : 0 ≤ ‖p‖ := by positivity
    nlinarith [sq_abs (p 0)]
  have h_p1_abs : |p 1| ≤ ‖p‖ := by
    have h_norm_eq : ‖p‖ = Real.sqrt ((p 0)^2 + (p 1)^2) := by
      simp [EuclideanSpace.norm_eq, Fin.sum_univ_two] <;> rfl
    have h_norm_sq : ‖p‖^2 = (p 0)^2 + (p 1)^2 := by
      rw [h_norm_eq]
      rw [Real.sq_sqrt] <;> nlinarith
    have h : (p 1)^2 ≤ ‖p‖^2 := by rw [h_norm_sq]; nlinarith [sq_nonneg (p 0)]
    have h_abs : 0 ≤ |p 1| := by positivity
    have h_norm_nonneg : 0 ≤ ‖p‖ := by positivity
    nlinarith [sq_abs (p 1)]
  set c := localSquareCenter q with hc
  set δ := dyadicDelta n with hδ
  have h_coords := localSquareCenter_coord_dist q p hpq
  have h0 : |p 0 - c 0| ≤ δ / 2 := h_coords.1
  have h1 : |p 1 - c 1| ≤ δ / 2 := h_coords.2
  have h_c0_abs : |c 0| ≤ |p 0| + |p 0 - c 0| := by
    calc |c 0| = |p 0 - (p 0 - c 0)| := by ring_nf
      _ ≤ |p 0| + |p 0 - c 0| := by apply abs_sub
  have h_c1_abs : |c 1| ≤ |p 1| + |p 1 - c 1| := by
    calc |c 1| = |p 1 - (p 1 - c 1)| := by ring_nf
      _ ≤ |p 1| + |p 1 - c 1| := by apply abs_sub
  have h_p0_le1 : |p 0| ≤ 1 := by linarith
  have h_p1_le1 : |p 1| ≤ 1 := by linarith
  constructor <;> linarith

/-- If a dyadic square intersects a set P contained in the unit ball,
    its center norm is bounded by 1 + δ√2/2 (general version, no δ-small assumption). -/
lemma localSquareCenter_near_ball_general {n : ℕ} {P : Set (EuclideanSpace ℝ (Fin 2))}
    (hP : P ⊆ Metric.closedBall 0 1)
    (q : DyadicSquare n)
    (h_inter : (P ∩ (q.toSet : Set (EuclideanSpace ℝ (Fin 2)))).Nonempty) :
    ‖localSquareCenter q‖ ≤ 1 + (dyadicDelta n) * Real.sqrt 2 / 2 := by
  rcases h_inter with ⟨p, hpP, hpq⟩
  have h_pnorm : ‖p‖ ≤ 1 := by
    simpa [Metric.mem_closedBall] using hP hpP
  set c := localSquareCenter q with hc
  set δ := dyadicDelta n with hδ
  have h_dist : dist p c ≤ δ * Real.sqrt 2 / 2 :=
    localSquareCenter_dist_to_point q p hpq
  have h_dist' : dist p c = ‖c - p‖ := by
    simpa [dist_eq_norm, norm_sub_rev] using rfl
  have h_cp : ‖c - p‖ ≤ δ * Real.sqrt 2 / 2 := by
    rw [←h_dist']
    exact h_dist
  have h_norm : ‖c‖ ≤ ‖p‖ + ‖c - p‖ := by
    calc ‖c‖ = ‖p + (c - p)‖ := by abel_nf
      _ ≤ ‖p‖ + ‖c - p‖ := norm_add_le p (c - p)
  linarith [h_pnorm, h_cp, h_norm]

/-- If a dyadic square intersects a set P contained in the unit ball and δ ≤ 2 - √2,
    its center norm is bounded by √2. -/
lemma localSquareCenter_near_ball {n : ℕ} {P : Set (EuclideanSpace ℝ (Fin 2))}
    (hP : P ⊆ Metric.closedBall 0 1)
    (q : DyadicSquare n)
    (h_inter : (P ∩ (q.toSet : Set (EuclideanSpace ℝ (Fin 2)))).Nonempty)
    (hδ_small : dyadicDelta n ≤ 2 - Real.sqrt 2) :
    ‖localSquareCenter q‖ ≤ Real.sqrt 2 := by
  have h_general : ‖localSquareCenter q‖ ≤ 1 + (dyadicDelta n) * Real.sqrt 2 / 2 :=
    localSquareCenter_near_ball_general hP q h_inter
  set δ := dyadicDelta n with hδ
  have h_final : 1 + δ * Real.sqrt 2 / 2 ≤ Real.sqrt 2 := by
    have h5 : δ * Real.sqrt 2 / 2 ≤ Real.sqrt 2 - 1 := by
      have h6 : δ ≤ 2 - Real.sqrt 2 := hδ_small
      have h7 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    linarith [Real.sqrt_nonneg 2]
  exact le_trans h_general h_final

-- ========================================================================
-- Helper: IsDeltaSSet preserved under swapCoords (involutive isometry)
-- ========================================================================

lemma IsDeltaSSet.swapCoords_image {δ s C : ℝ} {P : Set (EuclideanSpace ℝ (Fin 2))}
    (h : IsDeltaSSet δ s C P) : IsDeltaSSet δ s C (swapCoords '' P) := by
  let e : EuclideanSpace ℝ (Fin 2) ≃ᵢ EuclideanSpace ℝ (Fin 2) := swapCoordsLI
  have h_e : ∀ (A : Set (EuclideanSpace ℝ (Fin 2))), e '' A = swapCoords '' A := by
    intro A; rfl
  have h1 : (e '' P).Nonempty := h.1.image e
  have h1' : (swapCoords '' P).Nonempty := by
    have h_eq : e '' P = swapCoords '' P := h_e P
    rw [h_eq] at h1
    exact h1
  have h2 : 0 < δ := h.2.1
  have h3 : 0 < C := h.2.2.1
  have h4 : 0 ≤ s := h.2.2.2.1
  refine ⟨h1', h2, h3, h4, ?_⟩
  intro y r hr
  let x := e.symm y
  have hfy : e x = y := e.apply_symm_apply y
  have h_inj : Function.Injective e := e.injective
  have h6 : (e '' P) ∩ Metric.closedBall y r = e '' (P ∩ Metric.closedBall x r) := by
    have h_img_inter : e '' P ∩ e '' (Metric.closedBall x r) = e '' (P ∩ Metric.closedBall x r) :=
      (Set.image_inter h_inj (s := P) (t := Metric.closedBall x r)).symm
    have h_ball : e '' Metric.closedBall x r = Metric.closedBall y r := by
      have h := e.image_closedBall x r
      rw [hfy] at h
      exact h
    rw [h_ball] at h_img_inter
    exact h_img_inter
  have h_goal : Metric.externalCoveringNumber δ.toNNReal ((e '' P) ∩ Metric.closedBall y r) ≤
      ENNReal.ofReal C * (ENNReal.ofReal r) ^ s * Metric.externalCoveringNumber δ.toNNReal (e '' P) := by
    rw [h6]
    have h7 : Metric.externalCoveringNumber δ.toNNReal (e '' (P ∩ Metric.closedBall x r)) =
        Metric.externalCoveringNumber δ.toNNReal (P ∩ Metric.closedBall x r) :=
      DiscretisedFurstenbergEstimate.CoveringUtils.externalCoveringNumber_image_isometryEquiv e
    have h8 : Metric.externalCoveringNumber δ.toNNReal (e '' P) =
        Metric.externalCoveringNumber δ.toNNReal P :=
      DiscretisedFurstenbergEstimate.CoveringUtils.externalCoveringNumber_image_isometryEquiv e
    rw [h7, h8]
    exact h.2.2.2.2 x r hr
  simpa [h_e P] using h_goal

-- ========================================================================
-- Helper: swapCoords maps squareSet Δ Q to squareSet Δ (Q.swap)
-- ========================================================================
/-- Convert B1 bridge output to A1_Output.
    Constructs swapped point/tube families and calls a1_stage. -/
def b1_output_to_a1_output_exists
    {n m : ℕ} (hnm : m ≤ n)
    {Δ δ t s ε : ℝ}
    -- Scale parameters
    (hΔ_eq : Δ = dyadicDelta m)
    (hδ_eq : δ = dyadicDelta n)
    (hΔ_pos : 0 < Δ)
    (hΔ_lt_half : Δ < 1 / 2)
    (hδ_pos : 0 < δ)
    (hδ_le_D : δ ≤ Δ)
    (ht : 0 < t) (ht_lt_two : t < 2)
    (hs : 0 < s) (hs_lt_one : s < 1)
    (hε_pos : 0 < ε)
    (h_small : Real.rpow Δ (ε / 4) ≤ 1 / 100)
    -- Fine configuration at scale n
    (fineP₀ : Finset (DyadicSquare n))
    (fineTubeFamily : (p : DyadicSquare n) → p ∈ fineP₀ → Finset (DyadicTube n))
    (C_fine : ℝ) (hC_fine : 1 ≤ C_fine)
    (hC_fine_bound : C_fine ≤ Real.rpow δ (-ε / 2))
    (h_tube_sset_absorb :
      (4000 : ℝ) * 44^s ≤ Real.rpow δ (-ε / 2))
    (M_fine : ℕ) (hM_fine : 0 < M_fine)
    (hM_fine_even : M_fine % 2 = 0)
    (hM_fine_lower : (M_fine : ℝ) / 2 ≥ Real.rpow Δ (-2 * s + 2 * ε))
    (hM_fine_upper : (M_fine : ℝ) ≤ Real.rpow Δ (-2 * s - ε))
    (h_fine_sset : ∀ p hp, IsDeltaSSet δ s C_fine (fineTubeFamily p hp : Set (DyadicTube n)))
    (h_fine_size : ∀ p hp, (M_fine / 2 : ℕ) ≤ (fineTubeFamily p hp).card ∧ (fineTubeFamily p hp).card ≤ M_fine)
    (h_fine_inc : ∀ p hp T, T ∈ fineTubeFamily p hp → (T.toSet ∩ p.toSet).Nonempty)
    -- Coarse squares at scale m
    (coarseP₀ : Finset (DyadicSquare m))
    (h_coarse_card_upper : (coarseP₀.card : ℝ) ≤ Real.rpow Δ (-t - ε / 2))
    -- Coarse-fine relationship
    (containingSquare : DyadicSquare n → DyadicSquare m)
    (h_containing : ∀ p ∈ fineP₀, containingSquare p ∈ coarseP₀)
    (h_squareIndex_compat : ∀ p ∈ fineP₀,
      squareIndex Δ (localSquareCenter p) = ((containingSquare p).i, (containingSquare p).j))
    -- Finite point set ball bound from B1 bridge: centers in B(0, 1 + √2*δ/2)
    (h_points_in_ball_R : (fineP₀.image localSquareCenter : Set (EuclideanSpace ℝ (Fin 2))) ⊆
      Metric.closedBall 0 (1 + Real.sqrt 2 * δ / 2))
    (h_tubes_strip : ∀ (p : DyadicSquare n) (hp : p ∈ fineP₀) (T : DyadicTube n),
      T ∈ fineTubeFamily p hp → -(2 ^ n : ℤ) ≤ T.a ∧ T.a < (2 ^ n : ℤ))
    (h_tubes_intercept : ∀ (p : DyadicSquare n) (hp : p ∈ fineP₀) (T : DyadicTube n),
      T ∈ fineTubeFamily p hp → |T.intercept| ≤ 3)
    -- Quantitative bounds
    (h_fine_card_lower : Real.rpow Δ (-2 * t + ε / 4) ≤ (fineP₀.card : ℝ))
    (h_fine_card_upper : (fineP₀.card : ℝ) ≤ Real.rpow Δ (-2 * t - ε / 4))
    -- Packing constant
    (K_pack : ℝ) (hK_pack_pos : 0 < K_pack)
    (hK_pack_bound : K_pack ≤ Real.rpow Δ (-2 * ε) / 6)
    -- Point ball-growth (supplied by B1 bridge; cannot be derived internally)
    (hP_ball_growth_data : ∀ (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ), Δ ≤ r →
      (((fineP₀.image localSquareCenter).filter (fun y => dist c y ≤ r)).card : ℝ) ≤
        Real.rpow Δ (-9 * ε / 4) * r^t * ((fineP₀.image localSquareCenter).card : ℝ))
    -- Global point S-set (supplied by B1 bridge, from target theorem's X S-set)
    (hPfin_sset : IsDeltaSSet δ t (Real.rpow δ (-2 * ε))
      ((fineP₀.image localSquareCenter) : Set (EuclideanSpace ℝ (Fin 2)))) :
    A1_Output Δ δ t s ε := by

  -- ========================================================================
  -- Setup: point and tube maps
  -- ========================================================================
  set Pfin : Finset (EuclideanSpace ℝ (Fin 2)) := fineP₀.image localSquareCenter with hPfin_def
  have hPfin_card : Pfin.card = fineP₀.card := by
    rw [hPfin_def, Finset.card_image_of_injective]
    exact localSquareCenter_injective
  set fullImage : EuclideanSpace ℝ (Fin 2) → Finset AffineLine := fun p =>
    if h : ∃ (p_dy : DyadicSquare n), p_dy ∈ fineP₀ ∧ localSquareCenter p_dy = p then
      let p_dy := Classical.choose h
      (fineTubeFamily p_dy (Classical.choose_spec h).1).image DyadicCardToNcover.toAffineLine
    else ∅
    with hfullImage_def
  -- Tp p is the raw image of the dyadic tube family under toAffineLine.
  -- It is δ/2-separated by dyadic_tube_affine_separated (obligation #6).
  set Tp : EuclideanSpace ℝ (Fin 2) → Finset AffineLine := fullImage
    with hTp_def

  -- Helper: for p ∈ Pfin, Tp p equals the image of the corresponding tube family.
  have hTp_eq : ∀ (p_dy : DyadicSquare n) (hp_dy : p_dy ∈ fineP₀),
      Tp (localSquareCenter p_dy) =
        (fineTubeFamily p_dy hp_dy).image DyadicCardToNcover.toAffineLine := by
    intro p_dy hp_dy
    have h_exists : ∃ (p_dy' : DyadicSquare n), p_dy' ∈ fineP₀ ∧ localSquareCenter p_dy' = localSquareCenter p_dy :=
      ⟨p_dy, hp_dy, rfl⟩
    have h1 : Tp (localSquareCenter p_dy) = fullImage (localSquareCenter p_dy) := by
      rw [hTp_def] <;> rfl
    rw [h1]
    have h2 : fullImage (localSquareCenter p_dy) =
        (fineTubeFamily (Classical.choose h_exists) (Classical.choose_spec h_exists).1).image DyadicCardToNcover.toAffineLine := by
      dsimp only [fullImage]
      rw [dif_pos h_exists] <;> rfl
    rw [h2]
    let p_chosen := Classical.choose h_exists
    have h_chosen_mem : p_chosen ∈ fineP₀ := (Classical.choose_spec h_exists).1
    have h_chosen_eq : localSquareCenter p_chosen = localSquareCenter p_dy := (Classical.choose_spec h_exists).2
    have h_chosen_eq' : p_chosen = p_dy := localSquareCenter_injective h_chosen_eq
    have h3 : fineTubeFamily p_chosen h_chosen_mem = fineTubeFamily p_dy hp_dy := by
      congr <;> tauto
    rw [h3]

  -- ========================================================================
  -- OBLIGATION 1: Points in closed ball 0 √2
  -- From B1 bridge ball bound R = 1 + √2*δ/2 < √2 for small δ.
  -- ========================================================================
  have hδ_small : δ ≤ 2 - Real.sqrt 2 := by
    have h1 : δ ≤ Δ := hδ_le_D
    have h2 : (1 / 2 : ℝ) ≤ 2 - Real.sqrt 2 := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    linarith
  have hR_le_sqrt2 : 1 + Real.sqrt 2 * δ / 2 ≤ Real.sqrt 2 := by
    have h3 : Real.sqrt 2 * δ / 2 ≤ Real.sqrt 2 - 1 := by
      have h4 : δ ≤ 2 - Real.sqrt 2 := hδ_small
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    linarith [Real.sqrt_nonneg 2]
  have hP_in_ball_R' : (Pfin : Set (EuclideanSpace ℝ (Fin 2))) ⊆
      Metric.closedBall 0 (1 + Real.sqrt 2 * δ / 2) := by
    simpa [hPfin_def] using h_points_in_ball_R
  have hP_in_ball : (Pfin : Set (EuclideanSpace ℝ (Fin 2))) ⊆ Metric.closedBall 0 (Real.sqrt 2) := by
    intro p hp
    have h5 : p ∈ Metric.closedBall 0 (1 + Real.sqrt 2 * δ / 2) := hP_in_ball_R' hp
    have h6 : dist p 0 ≤ 1 + Real.sqrt 2 * δ / 2 := by simpa [Metric.mem_closedBall] using h5
    have h7 : dist p 0 ≤ Real.sqrt 2 := by linarith
    simpa [Metric.mem_closedBall] using h7

  -- ========================================================================
  -- OBLIGATION 2: Point set δ-separated
  -- Inputs: distinct squares → centers ≥ δ apart (analogous to delivered lemma)
  -- Output: SeparatedAt δ (Pfin : Set Plane)
  -- ========================================================================
  have hP_sep : SSetBridges.SeparatedAt δ (Pfin : Set (EuclideanSpace ℝ (Fin 2))) := by
    intro p hp p' hp' hne
    rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
    rcases Finset.mem_image.mp hp' with ⟨q', hq', rfl⟩
    have hqne : q ≠ q' := by intro h; apply hne; rw [h]
    have hδ_eq' : δ = dyadicDelta n := hδ_eq
    rw [hδ_eq']
    exact localSquareCenter_distinct_separated q q' hqne

  -- ========================================================================
  -- OBLIGATION 3: REMOVED — now a hypothesis (hP_ball_growth_data), supplied by B1 bridge.
  -- Derive hP_ball_growth from the hypothesis using hPfin_def.
  -- ========================================================================
  have hP_ball_growth : ∀ (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ), Δ ≤ r →
      ((Pfin.filter (fun y => dist c y ≤ r)).card : ℝ) ≤
        Real.rpow Δ (-9 * ε / 4) * r^t * (Pfin.card : ℝ) := by
    intro c r hr
    have h_eq : Pfin = fineP₀.image localSquareCenter := by
      exact hPfin_def
    rw [h_eq]
    exact hP_ball_growth_data c r hr

  -- ========================================================================
  -- OBLIGATION 4: Coarse square index cover bound
  -- Inputs: h_coarse_card_upper, h_squareIndex_compat, h_containing
  -- Output: |Q_all| ≤ Δ^{-t-ε/2}
  -- ========================================================================
  have hN_cover : ∀ (Q_all : Finset (ℤ × ℤ)),
      Q_all = Pfin.image (fun p => Phase2.squareIndex Δ p) →
        (Q_all.card : ℝ) ≤ Real.rpow Δ (-t - ε / 2) := by
    intro Q_all hQ_all
    have h1 : Q_all = fineP₀.image (fun p => squareIndex Δ (localSquareCenter p)) := by
      rw [hQ_all, hPfin_def]
      rw [Finset.image_image]
      <;> rfl
    rw [h1]
    let f : DyadicSquare n → ℤ × ℤ := fun p => ((containingSquare p).i, (containingSquare p).j)
    have h2 : (fineP₀.image (fun p => squareIndex Δ (localSquareCenter p))) = fineP₀.image f := by
      apply Finset.image_congr
      intro p hp
      exact h_squareIndex_compat p hp
    rw [h2]
    let g : DyadicSquare m → ℤ × ℤ := fun Q => (Q.i, Q.j)
    have h3 : (fineP₀.image f) ⊆ coarseP₀.image g := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨p, hp, rfl⟩
      have h4 : containingSquare p ∈ coarseP₀ := h_containing p hp
      exact Finset.mem_image.mpr ⟨containingSquare p, h4, rfl⟩
    have h4 : ((fineP₀.image f).card : ℝ) ≤ ((coarseP₀.image g).card : ℝ) := by
      exact_mod_cast Finset.card_le_card h3
    have h5 : Function.Injective g := by
      intro Q1 Q2 h
      have h' : (Q1.i, Q1.j) = (Q2.i, Q2.j) := h
      have hi : Q1.i = Q2.i := by simp [Prod.ext_iff] at h' <;> tauto
      have hj : Q1.j = Q2.j := by simp [Prod.ext_iff] at h' <;> tauto
      have : Q1 = Q2 := by
        cases Q1 <;> cases Q2 <;> simp_all <;> tauto
      exact this
    have h6 : (coarseP₀.image g).card = coarseP₀.card := by
      rw [Finset.card_image_of_injective _ h5]
    rw [h6] at h4
    exact le_trans h4 h_coarse_card_upper

  -- ========================================================================
  -- OBLIGATION 5: Tube S-set transfer to AffineLine
  -- Inputs: h_fine_sset, finiteTubeSSet_to_affineSSet (constant C·400·44^s),
  --         slope_bound_from_strip, h_tubes_intercept, hC_fine_bound
  -- Output: IsDeltaSSet δ s (δ^{-ε}) (Tp p : Set AffineLine)
  -- hC_fine_bound ensures C_fine * 400 * 44^s ≤ δ^{-ε}
  -- ========================================================================
  have hTp_sset : ∀ p ∈ Pfin,
      IsDeltaSSet δ s (Real.rpow δ (-ε)) (Tp p : Set AffineLine) := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨p_dy, hp_dy, rfl⟩
    let F := fineTubeFamily p_dy hp_dy
    have hF_nonempty : F.Nonempty := by
      have h_card : (M_fine / 2 : ℕ) ≤ F.card := (h_fine_size p_dy hp_dy).1
      have h_pos : 0 < F.card := by
        have h5 : 0 < M_fine / 2 := by omega
        omega
      exact Finset.card_pos.mp h_pos
    -- Slope bound
    have hm : ∀ T ∈ F, |T.slope| ≤ 1 := by
      intro T hT
      exact DyadicToAffineAdapters.slope_bound_from_strip T
        (h_tubes_strip p_dy hp_dy T hT)
    -- Intercept bound
    have hb : ∀ T ∈ F, |T.intercept| ≤ 3 := by
      intro T hT
      exact h_tubes_intercept p_dy hp_dy T hT
    -- δ = dyadicDelta n
    have hδ_eq2 : δ = dyadicDelta n := hδ_eq
    -- Transfer S-set
    have h_sset_input : IsDeltaSSet (dyadicDelta n) s C_fine (F : Set (DyadicTube n)) := by
      simpa [F, hδ_eq2] using h_fine_sset p_dy hp_dy
    have h_sset_affine : IsDeltaSSet δ s
        (max 1 (10 * C_fine) * 400 * 44^s)
        (DyadicCardToNcover.toAffineLine '' (F : Set (DyadicTube n))) := by
      rw [hδ_eq2]
      exact DyadicToAffineAdapters.tubeSSet_transfer hs.le hs_lt_one hC_fine hm hb h_sset_input
    -- Tp p = toAffineLine '' F
    have hTp_eq2 : (Tp (localSquareCenter p_dy) : Set AffineLine) =
        DyadicCardToNcover.toAffineLine '' (F : Set (DyadicTube n)) := by
      have h1 : Tp (localSquareCenter p_dy) = F.image DyadicCardToNcover.toAffineLine := hTp_eq p_dy hp_dy
      rw [h1]
      <;> simp
    rw [hTp_eq2] at *
    -- Simplify constant
    have hC1 : max 1 (10 * C_fine) = 10 * C_fine := by
      have h : 1 ≤ 10 * C_fine := by linarith
      exact max_eq_right h
    rw [hC1] at h_sset_affine
    have hC_eq : (10 * C_fine) * 400 * 44^s = (4000 : ℝ) * C_fine * 44^s := by ring
    rw [hC_eq] at h_sset_affine
    -- Absorb constant: 4000 * C_fine * 44^s ≤ δ^{-ε}
    have h_absorb : (4000 : ℝ) * C_fine * 44^s ≤ Real.rpow δ (-ε) := by
      have h1 : C_fine ≤ Real.rpow δ (-ε / 2) := hC_fine_bound
      have h2 : (4000 : ℝ) * 44^s ≤ Real.rpow δ (-ε / 2) := h_tube_sset_absorb
      have h3 : Real.rpow δ (-ε / 2) * Real.rpow δ (-ε / 2) = Real.rpow δ (-ε) := by
        have h4 : Real.rpow δ ((-ε / 2) + (-ε / 2)) =
            Real.rpow δ (-ε / 2) * Real.rpow δ (-ε / 2) :=
          Real.rpow_add hδ_pos (-ε / 2) (-ε / 2)
        have h5 : (-ε / 2) + (-ε / 2) = -ε := by ring
        rw [h5] at h4
        exact h4.symm
      have h_rpow_nonneg : 0 ≤ Real.rpow δ (-ε / 2) := Real.rpow_nonneg (by linarith) _
      calc
        (4000 : ℝ) * C_fine * 44^s
          = ((4000 : ℝ) * 44^s) * C_fine := by ring
        _ ≤ ((4000 : ℝ) * 44^s) * Real.rpow δ (-ε / 2) := by gcongr
        _ ≤ Real.rpow δ (-ε / 2) * Real.rpow δ (-ε / 2) := by
          exact mul_le_mul_of_nonneg_right h2 h_rpow_nonneg
        _ = Real.rpow δ (-ε) := h3
    -- Weaken IsDeltaSSet constant
    rcases h_sset_affine with ⟨hne, hδ_pos', hC_pos', hs_nonneg', h_sset'⟩
    have hC_target_pos : 0 < Real.rpow δ (-ε) := Real.rpow_pos_of_pos hδ_pos _
    refine' ⟨hne, hδ_pos', hC_target_pos, hs_nonneg', _⟩
    intro x r hr
    have h4 := h_sset' x r hr
    have h5 : ENNReal.ofReal ((4000 : ℝ) * C_fine * 44^s) ≤
        ENNReal.ofReal (Real.rpow δ (-ε)) :=
      ENNReal.ofReal_le_ofReal h_absorb
    calc
      (Metric.externalCoveringNumber δ.toNNReal
          ((DyadicCardToNcover.toAffineLine '' (F : Set (DyadicTube n))) ∩ Metric.closedBall x r) : ENNReal)
        ≤ ENNReal.ofReal ((4000 : ℝ) * C_fine * 44^s) * (ENNReal.ofReal r) ^ s *
              Metric.externalCoveringNumber δ.toNNReal (DyadicCardToNcover.toAffineLine '' (F : Set (DyadicTube n))) := h4
      _ ≤ ENNReal.ofReal (Real.rpow δ (-ε)) * (ENNReal.ofReal r) ^ s *
              Metric.externalCoveringNumber δ.toNNReal (DyadicCardToNcover.toAffineLine '' (F : Set (DyadicTube n))) := by
          gcongr <;> exact h5

  -- ========================================================================
  -- OBLIGATION 6: Tube family δ/2-separated
  -- Uses dyadic_tube_affine_separated: distinct DyadicTubes with |slope|≤1
  -- map to AffineLines at distance ≥ δ/2.
  -- ========================================================================
  have hTp_sep : ∀ p ∈ Pfin,
      SSetBridges.SeparatedAt (δ / 2) (Tp p : Set AffineLine) := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨p_dy, hp_dy, rfl⟩
    rw [hTp_eq p_dy hp_dy]
    intro T1 hT1 T2 hT2 hne
    rcases Finset.mem_image.mp hT1 with ⟨t1, ht1, rfl⟩
    rcases Finset.mem_image.mp hT2 with ⟨t2, ht2, rfl⟩
    have h_t1_ne_t2 : t1 ≠ t2 := by
      intro h
      apply hne
      rw [h]
    have h_slope1 : |t1.slope| ≤ 1 := slope_bound_from_strip t1 (h_tubes_strip p_dy hp_dy t1 ht1)
    have h_slope2 : |t2.slope| ≤ 1 := slope_bound_from_strip t2 (h_tubes_strip p_dy hp_dy t2 ht2)
    have hδ_eq' : δ = dyadicDelta n := hδ_eq
    rw [hδ_eq']
    exact DyadicCardToNcover.dyadic_tube_affine_separated t1 t2 h_t1_ne_t2 h_slope1 h_slope2

  -- ========================================================================
  -- OBLIGATION 7: Tube cardinality lower bound
  -- Inputs: hM_fine_lower, maximal subset loses ≤ K_pack factor (packing)
  -- Output: Δ^{-2s+2ε} ≤ |Tp p|
  -- Need: |fullImage p| = M_fine ≥ Δ^{-2s+2ε}, and |Tp p| ≥ |fullImage p| / K_pack
  --       with K_pack absorbed into ε budget.
  -- ========================================================================
  have h_tube_card_lower : ∀ p ∈ Pfin,
      Real.rpow Δ (-2 * s + 2 * ε) ≤ (Tp p).card := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨p_dy, hp_dy, rfl⟩
    rw [hTp_eq p_dy hp_dy]
    have h_card : ((fineTubeFamily p_dy hp_dy).image DyadicCardToNcover.toAffineLine).card =
        (fineTubeFamily p_dy hp_dy).card :=
      Finset.card_image_of_injective _ toAffineLine_injective
    rw [h_card]
    have h_lb : (M_fine : ℝ) / 2 ≤ ((fineTubeFamily p_dy hp_dy).card : ℝ) := by
      have h_even : M_fine % 2 = 0 := hM_fine_even
      have h_div : (M_fine : ℝ) / 2 = ↑(M_fine / 2) := by
        have h4 : M_fine = 2 * (M_fine / 2) := by omega
        have h5 : (M_fine : ℝ) = 2 * ↑(M_fine / 2) := by exact_mod_cast h4
        rw [h5] <;> ring
      rw [h_div]
      exact_mod_cast (h_fine_size p_dy hp_dy).1
    exact le_trans hM_fine_lower h_lb

  -- ========================================================================
  -- OBLIGATION 8: Tube cardinality upper bound
  -- Inputs: Tp p ⊆ fullImage p, |fullImage p| = M_fine ≤ Δ^{-2s-ε} (hM_fine_upper)
  -- Output: |Tp p| ≤ Δ^{-2s-ε}
  -- ========================================================================
  have h_tube_card_upper : ∀ p ∈ Pfin,
      (Tp p).card ≤ Real.rpow Δ (-2 * s - ε) := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨p_dy, hp_dy, rfl⟩
    rw [hTp_eq p_dy hp_dy]
    have h_card : ((fineTubeFamily p_dy hp_dy).image DyadicCardToNcover.toAffineLine).card =
        (fineTubeFamily p_dy hp_dy).card :=
      Finset.card_image_of_injective _ toAffineLine_injective
    rw [h_card]
    have h_ub : ((fineTubeFamily p_dy hp_dy).card : ℝ) ≤ (M_fine : ℝ) := by
      exact_mod_cast (h_fine_size p_dy hp_dy).2
    exact le_trans h_ub hM_fine_upper

  -- Uniform M
  let M_in : ℕ := M_fine
  have hM_in_pos : 0 < M_in := hM_fine

  -- ========================================================================
  -- OBLIGATION 9: Uniform tube count
  -- Inputs: |fullImage p| = M_fine, maximal subset packing bound
  -- Output: M_in/2 < |Tp p| ≤ M_in
  -- NOTE: Tp p is now a maximal δ-separated subset, so |Tp p| ≤ M_fine trivially.
  -- The lower bound requires a packing argument: each tube in Tp p covers
  -- at most K_pack tubes from fullImage p, so M_fine ≤ K_pack * |Tp p|.
  -- Need K_pack small enough (or adjust M_in) to get M_in/2 < |Tp p|.
  -- ========================================================================
  have h_tube_uniform : ∀ p ∈ Pfin,
      M_in / 2 ≤ (Tp p).card ∧ (Tp p).card ≤ M_in := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨p_dy, hp_dy, rfl⟩
    rw [hTp_eq p_dy hp_dy]
    have h_card : ((fineTubeFamily p_dy hp_dy).image DyadicCardToNcover.toAffineLine).card =
        (fineTubeFamily p_dy hp_dy).card :=
      Finset.card_image_of_injective _ toAffineLine_injective
    rw [h_card]
    have h_bounds := h_fine_size p_dy hp_dy
    exact ⟨h_bounds.1, h_bounds.2⟩

  -- ========================================================================
  -- OBLIGATION 10: Solved via coordinate swap.
  -- Original tubes have |slope| ≤ 1 in y=mx+b convention, which gives
  -- |tubeSlope| ≥ 1 in x=ay+b convention. After swapCoords/swapLine,
  -- the slope parameter becomes the original slope (≤1), and intercept
  -- is preserved. The intercept ≤2 bound follows from tube-square incidence
  -- + quantization (see dyadic_tube_intercept_le_two).
  -- ========================================================================

  -- ========================================================================
  -- SWAP TRANSFER: Apply swapCoords to points and swapLine to tubes.
  -- This converts steep tubes (|m|≤1 in y=mx+b) to flat tubes (|a|≤1 in x=ay+b),
  -- satisfying A1's h_slope_bound requirement.
  -- ========================================================================
  let Pfin' : Finset (EuclideanSpace ℝ (Fin 2)) := Pfin.image swapCoords
  let Tp' (p' : EuclideanSpace ℝ (Fin 2)) : Finset AffineLine :=
    (Tp (swapCoords p')).image swapLine

  have hPfin'_card : Pfin'.card = Pfin.card := by
    rw [Finset.card_image_of_injective _ swapCoords_invol.injective]

  have h_swap_preimage : ∀ p' ∈ Pfin', swapCoords p' ∈ Pfin := by
    intro p' hp'
    rcases Finset.mem_image.mp hp' with ⟨p, hp, rfl⟩
    have h5 : swapCoords (swapCoords p) = p := swapCoords_invol p
    rw [h5] <;> exact hp

  -- Transfer separation
  have hP_sep' : SSetBridges.SeparatedAt δ (Pfin' : Set (EuclideanSpace ℝ (Fin 2))) := by
    intro p' hp' q' hq' hne
    have h_p : swapCoords p' ∈ Pfin := h_swap_preimage p' hp'
    have h_q : swapCoords q' ∈ Pfin := h_swap_preimage q' hq'
    have h_ne' : swapCoords p' ≠ swapCoords q' := by
      intro h; apply hne
      have h5 : swapCoords (swapCoords p') = swapCoords (swapCoords q') := by rw [h]
      have h6 : p' = q' := by
        have h7 : swapCoords (swapCoords p') = p' := swapCoords_invol p'
        have h8 : swapCoords (swapCoords q') = q' := swapCoords_invol q'
        rw [h7, h8] at h5
        exact h5
      exact h6
    have h : dist (swapCoords p') (swapCoords q') ≥ δ := hP_sep h_p h_q h_ne'
    have h2 : dist p' q' = dist (swapCoords p') (swapCoords q') :=
      (swapCoords_isometry.dist_eq p' q').symm
    rw [h2] <;> exact h

  -- Transfer tube S-set
  have hTp_sset' : ∀ p' ∈ Pfin', IsDeltaSSet δ s (Real.rpow δ (-ε)) (Tp' p' : Set AffineLine) := by
    intro p' hp'
    let p := swapCoords p'
    have hp : p ∈ Pfin := h_swap_preimage p' hp'
    have h_orig := hTp_sset p hp
    have h_eq : (Tp' p' : Set AffineLine) = swapLine '' (Tp p : Set AffineLine) := by
      simp [Tp'] <;> rfl
    rw [h_eq]
    exact swapLine_sset h_orig

  -- Transfer tube separation
  have hTp_sep' : ∀ p' ∈ Pfin', SSetBridges.SeparatedAt (δ / 2) (Tp' p' : Set AffineLine) := by
    intro p' hp'
    let p := swapCoords p'
    have hp : p ∈ Pfin := h_swap_preimage p' hp'
    have h_orig := hTp_sep p hp
    intro T1' hT1' T2' hT2' hne'
    rcases Finset.mem_image.mp hT1' with ⟨T1, hT1, rfl⟩
    rcases Finset.mem_image.mp hT2' with ⟨T2, hT2, rfl⟩
    have h_ne : T1 ≠ T2 := by
      intro h; apply hne'; rw [h]
    have h : dist T1 T2 ≥ δ / 2 := h_orig hT1 hT2 h_ne
    have h2 : dist (swapLine T1) (swapLine T2) = dist T1 T2 :=
      swapLine_isometry.dist_eq T1 T2
    rw [h2] <;> exact h

  -- Transfer cardinality
  have h_tube_card_lower' : ∀ p' ∈ Pfin', Real.rpow Δ (-2 * s + 2 * ε) ≤ (Tp' p').card := by
    intro p' hp'
    let p := swapCoords p'
    have hp : p ∈ Pfin := h_swap_preimage p' hp'
    have h : (Tp' p').card = (Tp p).card := by
      rw [Finset.card_image_of_injective _ swapLine_invol.injective]
    rw [h] <;> exact h_tube_card_lower p hp

  have h_tube_card_upper' : ∀ p' ∈ Pfin', (Tp' p').card ≤ Real.rpow Δ (-2 * s - ε) := by
    intro p' hp'
    let p := swapCoords p'
    have hp : p ∈ Pfin := h_swap_preimage p' hp'
    have h : (Tp' p').card = (Tp p).card := by
      rw [Finset.card_image_of_injective _ swapLine_invol.injective]
    rw [h] <;> exact h_tube_card_upper p hp

  have h_tube_uniform' : ∀ p' ∈ Pfin', M_in / 2 ≤ (Tp' p').card ∧ (Tp' p').card ≤ M_in := by
    intro p' hp'
    let p := swapCoords p'
    have hp : p ∈ Pfin := h_swap_preimage p' hp'
    have h : (Tp' p').card = (Tp p).card := by
      rw [Finset.card_image_of_injective _ swapLine_invol.injective]
    rw [h] <;> exact h_tube_uniform p hp

  -- Slope and intercept bound for swapped tubes (OBLIGATION #10 solved)
  have h_slope_bound' : ∀ p' ∈ Pfin', ∀ T' ∈ Tp' p',
      (LemmaE.getDirV T') 1 ≠ 0 ∧ |tubeSlope T'| ≤ 1 ∧ |tubeIntercept T'| ≤ 3 := by
    intro p' hp' T' hT'
    rcases Finset.mem_image.mp hT' with ⟨T, hT, rfl⟩
    let p := swapCoords p'
    have hp : p ∈ Pfin := h_swap_preimage p' hp'
    rcases Finset.mem_image.mp hp with ⟨p_dy, hp_dy, h_eq⟩
    have hTp_eq' : Tp p = (fineTubeFamily p_dy hp_dy).image toAffineLine := by
      have h : Tp (localSquareCenter p_dy) = (fineTubeFamily p_dy hp_dy).image toAffineLine :=
        hTp_eq p_dy hp_dy
      have h' : Tp p = Tp (localSquareCenter p_dy) := by rw [h_eq.symm]
      rw [h']
      exact h
    have hT' : T ∈ (fineTubeFamily p_dy hp_dy).image toAffineLine := by
      rw [hTp_eq'] at hT
      exact hT
    rcases Finset.mem_image.mp hT' with ⟨t, ht, rfl⟩
    have h_slope : |t.slope| ≤ 1 :=
      slope_bound_from_strip t (h_tubes_strip p_dy hp_dy t ht)
    have h_intercept_le_three : |t.intercept| ≤ 3 :=
      h_tubes_intercept p_dy hp_dy t ht
    have h_params := swapped_tube_params t h_slope
    rw [h_params.2.2]
    exact ⟨h_params.1, h_params.2.1, h_intercept_le_three⟩

  -- ========================================================================
  -- OBLIGATION 11: Tube incidence
  -- Inputs: h_fine_inc (tube-square intersection), square_center_near_affine_line
  -- Output: p ∈ cthickening (2*δ) T.1 for each p ∈ Pfin, T ∈ Tp p
  -- ========================================================================
  have h_inc : ∀ p ∈ Pfin, ∀ T ∈ Tp p, p ∈ Metric.cthickening (2 * δ) T.1 := by
    intro p hp T hT
    rcases Finset.mem_image.mp hp with ⟨p_dy, hp_dy, rfl⟩
    have hTp_eq' : Tp (localSquareCenter p_dy) =
        (fineTubeFamily p_dy hp_dy).image DyadicCardToNcover.toAffineLine :=
      hTp_eq p_dy hp_dy
    rw [hTp_eq'] at hT
    rcases Finset.mem_image.mp hT with ⟨t, ht, rfl⟩
    have h_slope : |t.slope| ≤ 1 :=
      slope_bound_from_strip t (h_tubes_strip p_dy hp_dy t ht)
    have h_inter : (t.toSet ∩ p_dy.toSet).Nonempty :=
      h_fine_inc p_dy hp_dy t ht
    have h_main : squareCenter (dyadicDelta n) (p_dy.i, p_dy.j) ∈
        Metric.cthickening (2 * dyadicDelta n) ((DyadicCardToNcover.toAffineLine t).1) :=
      DyadicToAffineAdapters.square_center_near_affine_line t p_dy h_slope h_inter
    have h_center_eq : localSquareCenter p_dy = squareCenter (dyadicDelta n) (p_dy.i, p_dy.j) := by
      ext i
      fin_cases i <;> simp [localSquareCenter, squareCenter] <;> ring
    simpa [h_center_eq, hδ_eq] using h_main

  -- Transfer incidence
  have h_inc' : ∀ p' ∈ Pfin', ∀ T' ∈ Tp' p',
      p' ∈ Metric.cthickening (2 * δ) T'.1 := by
    intro p' hp' T' hT'
    rcases Finset.mem_image.mp hT' with ⟨T, hT, rfl⟩
    have hp : swapCoords p' ∈ Pfin := h_swap_preimage p' hp'
    have h_orig : swapCoords p' ∈ Metric.cthickening (2 * δ) T.1 := h_inc (swapCoords p') hp T hT
    have h_result : swapCoords (swapCoords p') ∈ Metric.cthickening (2 * δ) (swapLine T).1 :=
      swapLine_near h_orig
    have h_sp : swapCoords (swapCoords p') = p' := swapCoords_invol p'
    rw [h_sp] at h_result
    exact h_result

  -- Transfer ball growth (swapCoords is isometry)
  have hP_ball_growth' : ∀ (c : EuclideanSpace ℝ (Fin 2)) (r : ℝ), Δ ≤ r →
      ((Pfin'.filter (fun y => dist c y ≤ r)).card : ℝ) ≤
        Real.rpow Δ (-9 * ε / 4) * r^t * (Pfin'.card : ℝ) := by
    intro c r hr
    let c' := swapCoords c
    have h_dist_eq : ∀ (z : EuclideanSpace ℝ (Fin 2)),
        dist c (swapCoords z) = dist c' z := by
      intro z
      have h : dist c (swapCoords z) = dist (swapCoords c) (swapCoords (swapCoords z)) :=
        (swapCoords_isometry.dist_eq c (swapCoords z)).symm
      rw [h]
      have h2 : swapCoords (swapCoords z) = z := swapCoords_invol z
      rw [h2] <;> rfl
    have h_filter : Pfin'.filter (fun y => dist c y ≤ r) =
        (Pfin.filter (fun y => dist c' y ≤ r)).image swapCoords := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨hx, hdist⟩
        rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
        have h5 : dist c' y ≤ r := by
          have h6 : dist c (swapCoords y) = dist c' y := h_dist_eq y
          rw [h6] at hdist
          exact hdist
        exact ⟨y, ⟨hy, h5⟩, by simp [swapCoords_invol]⟩
      · rintro ⟨y, ⟨hy, hdist⟩, rfl⟩
        have h6 : dist c (swapCoords y) ≤ r := by
          have h7 : dist c (swapCoords y) = dist c' y := h_dist_eq y
          rw [h7]
          exact hdist
        exact ⟨Finset.mem_image.mpr ⟨y, hy, rfl⟩, h6⟩
    rw [h_filter]
    have h_card : ((Pfin.filter (fun y => dist c' y ≤ r)).image swapCoords).card =
        (Pfin.filter (fun y => dist c' y ≤ r)).card := by
      rw [Finset.card_image_of_injective _ swapCoords_invol.injective]
    rw [h_card, hPfin'_card]
    exact hP_ball_growth c' r hr

  -- Transfer N_cover bound
  have hN_cover' : ∀ (Q_all : Finset (ℤ × ℤ)),
      Q_all = Pfin'.image (fun p => Phase2.squareIndex Δ p) →
        (Q_all.card : ℝ) ≤ Real.rpow Δ (-t - ε / 2) := by
    intro Q_all hQ_all
    have h_swap_idx : ∀ (p : EuclideanSpace ℝ (Fin 2)),
        Phase2.squareIndex Δ (swapCoords p) = (Phase2.squareIndex Δ p).swap := by
      intro p
      simp [Phase2.squareIndex, swapCoords]
      <;> ext i <;> fin_cases i <;> simp <;> ring
    have h_comm : Pfin'.image (fun p => Phase2.squareIndex Δ p) =
        (Pfin.image (fun p => Phase2.squareIndex Δ p)).image Prod.swap := by
      ext x
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨p', hp', rfl⟩
        have hp : swapCoords p' ∈ Pfin := h_swap_preimage p' hp'
        refine ⟨Phase2.squareIndex Δ (swapCoords p'), ⟨swapCoords p', hp, rfl⟩, ?_⟩
        have h : Phase2.squareIndex Δ (swapCoords (swapCoords p')) = (Phase2.squareIndex Δ (swapCoords p')).swap := h_swap_idx (swapCoords p')
        have h_sp : swapCoords (swapCoords p') = p' := swapCoords_invol p'
        rw [h_sp] at h
        exact h.symm
      · rintro ⟨idx, ⟨p, hp, rfl⟩, rfl⟩
        let p' := swapCoords p
        have hp' : p' ∈ Pfin' := Finset.mem_image.mpr ⟨p, hp, rfl⟩
        refine ⟨p', hp', ?_⟩
        have h : Phase2.squareIndex Δ (swapCoords p) = (Phase2.squareIndex Δ p).swap := h_swap_idx p
        have h_sp : p' = swapCoords p := by rfl
        rw [h_sp]
        exact h
    have h_card : ((Pfin.image (fun p => Phase2.squareIndex Δ p)).image Prod.swap).card =
        (Pfin.image (fun p => Phase2.squareIndex Δ p)).card := by
      rw [Finset.card_image_of_injective _ Prod.swap_injective]
    rw [hQ_all, h_comm]
    rw [h_card]
    exact hN_cover (Pfin.image (fun p => Phase2.squareIndex Δ p)) rfl

  -- ========================================================================
  -- √2 bound for Pfin' (swapCoords preserves norm)
  -- ========================================================================
  have hP_in_ball' : (Pfin' : Set (EuclideanSpace ℝ (Fin 2))) ⊆ Metric.closedBall 0 (Real.sqrt 2) := by
    intro p' hp'
    have h_p : swapCoords p' ∈ Pfin := h_swap_preimage p' hp'
    have h_norm : ‖swapCoords p'‖ ≤ Real.sqrt 2 := by
      simpa [Metric.mem_closedBall] using hP_in_ball h_p
    have h_eq : ‖swapCoords p'‖ = ‖p'‖ := by
      have h : dist (swapCoords p') (swapCoords (0 : EuclideanSpace ℝ (Fin 2))) =
            dist p' (0 : EuclideanSpace ℝ (Fin 2)) :=
        swapCoords_isometry.dist_eq p' 0
      have h0 : swapCoords (0 : EuclideanSpace ℝ (Fin 2)) = (0 : EuclideanSpace ℝ (Fin 2)) := by
        ext i; fin_cases i <;> simp [swapCoords]
      rw [h0] at h
      simpa [dist_eq_norm] using h
    rw [h_eq] at h_norm
    simpa [Metric.mem_closedBall] using h_norm

  have hP_y_bound' : ∀ (p' : EuclideanSpace ℝ (Fin 2)), p' ∈ Pfin' → |p' 1| ≤ Real.sqrt 2 := by
    intro p' hp'
    have h_swap : swapCoords p' ∈ Pfin := h_swap_preimage p' hp'
    rcases Finset.mem_image.mp h_swap with ⟨q, hq, h_eq_center⟩
    have h_swap_eq : swapCoords (localSquareCenter q) = p' := by
      rw [h_eq_center]
      exact swapCoords_invol p'
    set c := localSquareCenter q with hc
    have hc_in_Pfin : c ∈ Pfin := by
      rw [hPfin_def]
      exact Finset.mem_image.mpr ⟨q, hq, rfl⟩
    have hc_norm : ‖c‖ ≤ 1 + Real.sqrt 2 * δ / 2 := by
      have h : c ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) (1 + Real.sqrt 2 * δ / 2) :=
        h_points_in_ball_R hc_in_Pfin
      simpa [Metric.mem_closedBall] using h
    have h_coord_abs : |c 0| ≤ ‖c‖ := by
      have h_norm_eq : ‖c‖ = Real.sqrt ((c 0)^2 + (c 1)^2) := by
        simp [EuclideanSpace.norm_eq, Fin.sum_univ_two] <;> ring
      rw [h_norm_eq]
      have h6 : (c 0)^2 ≤ (c 0)^2 + (c 1)^2 := by nlinarith
      have h9 : Real.sqrt ((c 0)^2) ≤ Real.sqrt ((c 0)^2 + (c 1)^2) := Real.sqrt_le_sqrt h6
      have h10 : Real.sqrt ((c 0)^2) = |c 0| := by
        rw [Real.sqrt_sq_eq_abs]
      rw [h10] at h9
      exact h9
    have h_coord_eq : (swapCoords c) 1 = c 0 := by
      simp [swapCoords] <;> rfl
    have h_p1_eq : p' 1 = c 0 := by
      have h1 : p' 1 = (swapCoords c) 1 := by rw [←h_swap_eq]
      rw [h1, h_coord_eq]
    rw [h_p1_eq]
    have h_final : |c 0| ≤ Real.sqrt 2 := by
      calc |c 0| ≤ ‖c‖ := h_coord_abs
        _ ≤ 1 + Real.sqrt 2 * δ / 2 := hc_norm
        _ ≤ Real.sqrt 2 := hR_le_sqrt2
    exact h_final

  -- ========================================================================
  -- Global S-set transfer: Pfin → Pfin' via swapCoords isometry
  -- ========================================================================
  have hPfin_eq : (Pfin' : Set (EuclideanSpace ℝ (Fin 2))) = swapCoords '' (Pfin : Set (EuclideanSpace ℝ (Fin 2))) := by
    have h_def : Pfin' = Pfin.image swapCoords := by rfl
    rw [h_def]
    simp
  have hPfin_sset' : IsDeltaSSet δ t (Real.rpow δ (-2 * ε)) (Pfin' : Set (EuclideanSpace ℝ (Fin 2))) := by
    rw [hPfin_eq]
    exact IsDeltaSSet.swapCoords_image hPfin_sset

  -- ========================================================================
  -- Call a1_stage with swapped point/tube families
  -- ========================================================================
  exact a1_stage
    hΔ_pos hΔ_lt_half hδ_pos hδ_le_D ht ht_lt_two hs hs_lt_one hε_pos h_small
    Pfin' hP_in_ball' hP_y_bound' hP_sep'
      (by rw [hPfin'_card, hPfin_card]; exact h_fine_card_lower)
      (by rw [hPfin'_card, hPfin_card]; exact h_fine_card_upper)
    hP_ball_growth' hN_cover'
    Tp' hTp_sset' hTp_sep' h_tube_card_lower' h_tube_card_upper'
    M_in hM_in_pos hM_fine_even h_tube_uniform' h_slope_bound' h_inc' hPfin_sset'

end DiscretisedFurstenbergEstimate.ImprovedIncidenceGeneral
