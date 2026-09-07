module

/-
  Adapter lemmas: DyadicTube/Square → AffineLine/EuclideanPlane.

  Provides:
  1. `square_center_near_affine_line`: if T.toSet ∩ Q.toSet nonempty,
     then center(Q) ∈ cthickening(2δ, toAffineLine(T)).
  2. `image_separated`: the toAffineLine image of a bounded-slope Finset
     is δ/2-separated in AffineLine space.

  Whiteprint node: global_2s_bound_integration / dyadic_to_affine_adapters
  Dependencies: DyadicCardToNcover, HeavySquareRefinement
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicCardToNcover
public import MyLeanRepo.DiscretisedFurstenbergEstimate.HeavySquareRefinement
public import MyLeanRepo.DiscretisedFurstenbergEstimate.Bridge_SSetTransfer
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DyadicToAffineAdapters

open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.Lagoon
open DiscretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate.InductionOnScales
open DyadicCardToNcover

abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- L∞ parameter distance between dyadic tubes. -/
abbrev paramDistLinf {n : ℕ} (T U : DyadicTube n) : ℝ :=
  max |T.slope - U.slope| |T.intercept - U.intercept|

/-! ============================================================================
   1. Near-point lemma: square center is within 2δ of the affine line
   ============================================================================ -/

/-- If a dyadic tube T and dyadic square Q have nonempty intersection,
    and |T.slope| ≤ 1, then the center of Q is within 2δ of the
    representative affine line of T. -/
lemma square_center_near_affine_line {n : ℕ}
    (T : DyadicTube n) (Q : DyadicSquare n)
    (hm : |T.slope| ≤ 1)
    (h_inter : (T.toSet ∩ Q.toSet).Nonempty) :
    squareCenter (dyadicDelta n) (Q.i, Q.j) ∈
      Metric.cthickening (2 * dyadicDelta n) ((toAffineLine T).1) := by
  set δ := dyadicDelta n with hδ
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  rcases h_inter with ⟨p, hpT, hpQ⟩
  set c := squareCenter δ (Q.i, Q.j) with hc
  set m := T.slope with hm_def
  set b := T.intercept with hb_def
  set ℓ := toAffineLine T with hℓ

  -- Coordinate bounds from p ∈ Q.toSet
  have hxi1 : (Q.i : ℝ) * δ ≤ p 0 := hpQ.1
  have hxi2 : p 0 < ((Q.i : ℝ) + 1) * δ := hpQ.2.1
  have hyi1 : (Q.j : ℝ) * δ ≤ p 1 := hpQ.2.2.1
  have hyi2 : p 1 < ((Q.j : ℝ) + 1) * δ := hpQ.2.2.2

  have hcx : c 0 = δ * ((Q.i : ℝ) + 1 / 2) := squareCenter_zero δ (Q.i, Q.j)
  have hcy : c 1 = δ * ((Q.j : ℝ) + 1 / 2) := squareCenter_one δ (Q.i, Q.j)

  have hdx : |c 0 - p 0| ≤ δ / 2 := by
    rw [hcx]
    have h1 : -(δ / 2) ≤ p 0 - δ * ((Q.i : ℝ) + 1 / 2) := by linarith
    have h2 : p 0 - δ * ((Q.i : ℝ) + 1 / 2) ≤ δ / 2 := by linarith
    exact abs_le.mpr ⟨by linarith, by linarith⟩

  have hdy : |c 1 - p 1| ≤ δ / 2 := by
    rw [hcy]
    have h1 : -(δ / 2) ≤ p 1 - δ * ((Q.j : ℝ) + 1 / 2) := by linarith
    have h2 : p 1 - δ * ((Q.j : ℝ) + 1 / 2) ≤ δ / 2 := by linarith
    exact abs_le.mpr ⟨by linarith, by linarith⟩

  -- Tube condition: |p 1 - m * p 0 - b| ≤ δ
  have htube : |p 1 - m * p 0 - b| ≤ δ := hpT

  have habs_m : |m| ≤ 1 := hm

  -- Bound |c 1 - m * c 0 - b| ≤ 2δ
  have hmain : |c 1 - m * c 0 - b| ≤ 2 * δ := by
    have h_p0c0 : |p 0 - c 0| ≤ δ / 2 := by
      simpa [abs_sub_comm] using hdx
    have h_m_p0c0 : |m| * |p 0 - c 0| ≤ δ / 2 := by
      calc
        |m| * |p 0 - c 0| ≤ 1 * (δ / 2) := by gcongr <;> linarith
        _ = δ / 2 := by ring
    have h_sum : |c 1 - p 1| + |p 1 - m * p 0 - b| + |m| * |p 0 - c 0| ≤ 2 * δ := by
      linarith [hdy, htube, h_m_p0c0]
    have h_alg : c 1 - m * c 0 - b =
        (c 1 - p 1) + (p 1 - m * p 0 - b) + m * (p 0 - c 0) := by ring
    have h_abs : |c 1 - m * c 0 - b| ≤
        |c 1 - p 1| + |p 1 - m * p 0 - b| + |m * (p 0 - c 0)| := by
      rw [h_alg]
      exact abs_add_three (c.ofLp 1 - p.ofLp 1) (p.ofLp 1 - m * p.ofLp 0 - b) (m * (p.ofLp 0 - c.ofLp 0))
    have h_abs2 : |m * (p 0 - c 0)| = |m| * |p 0 - c 0| := by
      rw [abs_mul]
    rw [h_abs2] at h_abs
    exact le_trans h_abs h_sum

  -- Construct q on ℓ with same x-coordinate as c
  set q : Plane := TubesAndSlopes.mkPlane (c 0) (m * c 0 + b) with hq_def

  have hq0 : q 0 = c 0 := by
    simp [hq_def, TubesAndSlopes.mkPlane_apply0]
  have hq1 : q 1 = m * c 0 + b := by
    simp [hq_def, TubesAndSlopes.mkPlane_apply1]

  -- Prove q ∈ ℓ.1
  have hq_on_line : q ∈ ℓ.1 := by
    simp only [hℓ, toAffineLine, lineOfSlopeIntercept]
    have h : q - TubesAndSlopes.mkPlane 0 b ∈
        Submodule.span ℝ {tubeDirV m} := by
      have h2 : q - TubesAndSlopes.mkPlane 0 b =
          (c 0) • tubeDirV m := by
        ext i
        fin_cases i
        · simp [hq_def, TubesAndSlopes.mkPlane_apply0, TubesAndSlopes.mkPlane_apply1,
                tubeDirV, smul_eq_mul] <;> ring
        · simp [hq_def, TubesAndSlopes.mkPlane_apply0, TubesAndSlopes.mkPlane_apply1,
                tubeDirV, smul_eq_mul] <;> ring
      rw [h2]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    simpa [AffineSubspace.mem_mk'] using h

  -- Distance from c to q equals |c 1 - q 1|
  have hdist_eq : dist c q = |c 1 - q 1| := by
    have h1 : dist c q = ‖c - q‖ := by rfl
    rw [h1]
    have h2 : (c - q) 0 = 0 := by simp [hq0]
    have h3 : (c - q) 1 = c 1 - q 1 := by simp
    have h4 : ‖c - q‖ ^ 2 = ((c - q) 0)^2 + ((c - q) 1)^2 := by
      rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two] <;> ring
    have h5 : ‖c - q‖ ^ 2 = (c 1 - q 1)^2 := by
      rw [h4, h2, h3] <;> ring
    have h6 : 0 ≤ ‖c - q‖ := by positivity
    have h7 : ‖c - q‖ = |c 1 - q 1| := by
      have h8 : |c 1 - q 1| ^ 2 = (c 1 - q 1)^2 := by simp [sq_abs]
      have h9 : ‖c - q‖ ^ 2 = |c 1 - q 1| ^ 2 := by rw [h5, h8]
      have h10 : 0 ≤ ‖c - q‖ := by positivity
      have h11 : 0 ≤ |c 1 - q 1| := by positivity
      by_cases h12 : ‖c - q‖ + |c 1 - q 1| = 0
      · have h13 : ‖c - q‖ = 0 := by linarith [h10, h11]
        have h14 : |c 1 - q 1| = 0 := by linarith [h10, h11]
        linarith
      · have h13 : 0 < ‖c - q‖ + |c 1 - q 1| := by
          exact lt_of_le_of_ne (by positivity) (Ne.symm h12)
        have h14 : (‖c - q‖ - |c 1 - q 1|) * (‖c - q‖ + |c 1 - q 1|) = 0 := by linarith
        have h15 : ‖c - q‖ - |c 1 - q 1| = 0 := by
          exact (mul_eq_zero.mp h14).resolve_right h13.ne'
        linarith
    exact h7

  have hdist_le : dist c q ≤ 2 * δ := by
    rw [hdist_eq, hq1]
    have h_eq : c 1 - (m * c 0 + b) = c 1 - m * c 0 - b := by ring
    rw [h_eq]
    exact hmain

  have h_edist : edist c q ≤ ENNReal.ofReal (2 * δ) := by
    rw [edist_dist]
    exact ENNReal.ofReal_le_ofReal hdist_le
  have h_inf : Metric.infEDist c ((toAffineLine T).1) ≤ ENNReal.ofReal (2 * δ) := by
    have h : Metric.infEDist c ((toAffineLine T).1) ≤ edist c q :=
      Metric.infEDist_le_edist_of_mem hq_on_line
    exact le_trans h h_edist
  exact Metric.mem_cthickening_iff.mpr h_inf

/-! ============================================================================
   2. Separation transfer: image under toAffineLine is δ/2-separated
   ============================================================================ -/

/-- The toAffineLine image of a bounded-slope Finset of DyadicTubes
    is δ/2-separated in AffineLine space. -/
lemma image_separated {n : ℕ} {F : Finset (DyadicTube n)}
    (hm : ∀ T ∈ F, |T.slope| ≤ 1) :
    Set.Pairwise (toAffineLine '' (F : Set (DyadicTube n)))
      (fun x y => dyadicDelta n / 2 ≤ dist x y) := by
  intro x hx y hy hxy
  rcases hx with ⟨T1, hT1, rfl⟩
  rcases hy with ⟨T2, hT2, rfl⟩
  have h_ne : T1 ≠ T2 := by
    intro h
    rw [h] at hxy
    simp at hxy
  exact dyadic_tube_affine_separated T1 T2 h_ne (hm T1 hT1) (hm T2 hT2)

/-! ============================================================================
   3. Quasi-isometry bounds for toAffineLine on bounded tubes
   ============================================================================ -/

/-- Explicit formula for orthogonal projection onto line of slope m. -/
lemma starProjection_line_apply (m : ℝ) (w : Plane) :
    (Submodule.span ℝ {tubeDirV m}).starProjection w =
      ((w 0 + m * w 1) / (1 + m^2)) • tubeDirV m := by
  let v := tubeDirV m
  have h : (Submodule.span ℝ {v}).starProjection w =
      (inner ℝ v w / ‖v‖ ^ 2) • v :=
    Submodule.starProjection_singleton (𝕜 := ℝ) (v := v) (w := w)
  have h_inner : inner ℝ v w = w 0 + m * w 1 := by
    rw [PiLp.inner_apply, Fin.sum_univ_two]
    <;> simp [v, tubeDirV, TubesAndSlopes.mkPlane] <;> ring
  have h_norm : ‖v‖ ^ 2 = 1 + m^2 := by
    simp [v, tubeDirV, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, TubesAndSlopes.mkPlane] <;> ring
  rw [h, h_inner, h_norm] <;> rfl

/-- Pointwise bound: ‖(P1 - P2) w‖ ≤ |m1 - m2| * ‖w‖. -/
lemma proj_diff_bound (m1 m2 : ℝ) (w : Plane) :
    ‖(Submodule.span ℝ {tubeDirV m1}).starProjection w -
      (Submodule.span ℝ {tubeDirV m2}).starProjection w‖ ≤
    |m1 - m2| * ‖w‖ := by
  set P1 := (Submodule.span ℝ {tubeDirV m1}).starProjection with hP1
  set P2 := (Submodule.span ℝ {tubeDirV m2}).starProjection with hP2
  set v := P1 w - P2 w with hv
  have h0 : v 0 = (w 0 + m1 * w 1) / (1 + m1^2) - (w 0 + m2 * w 1) / (1 + m2^2) := by
    rw [hv]
    rw [starProjection_line_apply m1 w, starProjection_line_apply m2 w]
    <;> simp [tubeDirV, TubesAndSlopes.mkPlane, smul_eq_mul] <;> ring
  have h1 : v 1 = m1 * (w 0 + m1 * w 1) / (1 + m1^2) - m2 * (w 0 + m2 * w 1) / (1 + m2^2) := by
    rw [hv]
    rw [starProjection_line_apply m1 w, starProjection_line_apply m2 w]
    <;> simp [tubeDirV, TubesAndSlopes.mkPlane, smul_eq_mul] <;> ring
  have h_norm2 : ‖v‖ ^ 2 = (v 0)^2 + (v 1)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two] <;> ring
  have h_wnorm2 : ‖w‖ ^ 2 = (w 0)^2 + (w 1)^2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two] <;> ring
  have h_main : ‖v‖ ^ 2 = ((m1 - m2)^2 / ((1 + m1^2) * (1 + m2^2))) * ‖w‖ ^ 2 := by
    rw [h_norm2, h_wnorm2, h0, h1]
    field_simp
    <;> ring
  have h_denom_ge_one : (1 + m1^2) * (1 + m2^2) ≥ 1 := by nlinarith
  have h_frac_le : (m1 - m2)^2 / ((1 + m1^2) * (1 + m2^2)) ≤ (m1 - m2)^2 := by
    have h_nonneg : 0 ≤ (m1 - m2)^2 := by positivity
    exact (div_le_self h_nonneg h_denom_ge_one)
  have h4 : ‖v‖ ^ 2 ≤ (m1 - m2)^2 * ‖w‖ ^ 2 := by
    rw [h_main]
    gcongr
    <;> exact h_frac_le
  have h9 : (m1 - m2)^2 = (|m1 - m2|)^2 := by rw [sq_abs]
  have h10 : ‖v‖ ^ 2 ≤ (|m1 - m2| * ‖w‖) ^ 2 := by
    have h11 : (|m1 - m2| * ‖w‖) ^ 2 = |m1 - m2| ^ 2 * ‖w‖ ^ 2 := by ring
    rw [h11]
    rw [h9] at h4
    exact h4
  have h6 : 0 ≤ ‖v‖ := by positivity
  have h7 : 0 ≤ |m1 - m2| * ‖w‖ := by positivity
  nlinarith

/-- Operator norm bound: ‖P1 - P2‖ ≤ |m1 - m2|. -/
lemma proj_op_norm_bound (m1 m2 : ℝ) :
    ‖(Submodule.span ℝ {tubeDirV m1}).starProjection -
      (Submodule.span ℝ {tubeDirV m2}).starProjection‖ ≤ |m1 - m2| := by
  have h : ∀ (w : Plane), ‖((Submodule.span ℝ {tubeDirV m1}).starProjection -
      (Submodule.span ℝ {tubeDirV m2}).starProjection) w‖ ≤ |m1 - m2| * ‖w‖ := by
    intro w
    simpa [ContinuousLinearMap.sub_apply] using proj_diff_bound m1 m2 w
  exact ContinuousLinearMap.opNorm_le_bound _ (by positivity) h

/-- Upper bound: offset difference ≤ |b1-b2| + 3*|m1-m2|.
    No slope bound needed for the upper bound. -/
lemma offset_diff_upper (m1 m2 b1 b2 : ℝ) (hb2 : |b2| ≤ 3) :
    ‖b1 • offsetVec m1 - b2 • offsetVec m2‖ ≤ |b1 - b2| + 3 * |m1 - m2| := by
  have h_alg : b1 • offsetVec m1 - b2 • offsetVec m2 =
      (b1 - b2) • offsetVec m1 + b2 • (offsetVec m1 - offsetVec m2) := by
    simp [sub_smul, smul_sub] <;> abel
  rw [h_alg]
  have h1 : ‖offsetVec m1‖ ≤ 1 := by
    rw [offsetVec_norm m1]
    have h2 : 1 ≤ Real.sqrt (1 + m1^2) := by
      have h3 : 1 ≤ 1 + m1^2 := by nlinarith
      have h4 : Real.sqrt 1 ≤ Real.sqrt (1 + m1^2) := Real.sqrt_le_sqrt h3
      simpa using h4
    have h5 : 0 < Real.sqrt (1 + m1^2) := by positivity
    exact (div_le_one h5).mpr h2
  have h3 : ‖offsetVec m1 - offsetVec m2‖ ≤ |m1 - m2| := offsetVec_lipschitz m1 m2
  calc
    ‖(b1 - b2) • offsetVec m1 + b2 • (offsetVec m1 - offsetVec m2)‖
      ≤ ‖(b1 - b2) • offsetVec m1‖ + ‖b2 • (offsetVec m1 - offsetVec m2)‖ := norm_add_le _ _
    _ = |b1 - b2| * ‖offsetVec m1‖ + |b2| * ‖offsetVec m1 - offsetVec m2‖ := by
        rw [norm_smul, norm_smul] <;> rfl
    _ ≤ |b1 - b2| * 1 + 3 * |m1 - m2| := by gcongr <;> linarith
    _ = |b1 - b2| + 3 * |m1 - m2| := by ring

/-- toAffineLine is 5-Lipschitz from L∞ parameter distance to AffineLine distance,
    for tubes with |slope| ≤ 1 and |intercept(T2)| ≤ 3. -/
lemma toAffineLine_lipschitz {n : ℕ} (T1 T2 : DyadicTube n)
    (hm1 : |T1.slope| ≤ 1) (hm2 : |T2.slope| ≤ 1)
    (hb2 : |T2.intercept| ≤ 3) :
    dist (toAffineLine T1) (toAffineLine T2) ≤ 5 * paramDistLinf T1 T2 := by
  set m1 := T1.slope with hm1_def
  set m2 := T2.slope with hm2_def
  set b1 := T1.intercept with hb1_def
  set b2 := T2.intercept with hb2_def
  set ℓ1 := toAffineLine T1 with hℓ1
  set ℓ2 := toAffineLine T2 with hℓ2
  set d_inf := paramDistLinf T1 T2 with hd_inf_def

  have hdm : |m1 - m2| ≤ d_inf := by
    dsimp only [d_inf, paramDistLinf]; exact le_max_left _ _
  have hdb : |b1 - b2| ≤ d_inf := by
    dsimp only [d_inf, paramDistLinf]; exact le_max_right _ _

  have h_dir_eq1 : ℓ1.1.direction = Submodule.span ℝ {tubeDirV m1} := by
    rw [hℓ1]; exact lineOfSlopeIntercept_direction m1 b1
  have h_dir_eq2 : ℓ2.1.direction = Submodule.span ℝ {tubeDirV m2} := by
    rw [hℓ2]; exact lineOfSlopeIntercept_direction m2 b2

  have h_proj_le : ‖ℓ1.1.direction.starProjection - ℓ2.1.direction.starProjection‖ ≤ |m1 - m2| := by
    rw [h_dir_eq1, h_dir_eq2]
    exact proj_op_norm_bound m1 m2

  have h_off1 : ℓ1.offset = b1 • offsetVec m1 := by
    rw [hℓ1, toAffineLine]; exact offset_formula m1 b1
  have h_off2 : ℓ2.offset = b2 • offsetVec m2 := by
    rw [hℓ2, toAffineLine]; exact offset_formula m2 b2

  have h_off_le : ‖ℓ1.offset - ℓ2.offset‖ ≤ |b1 - b2| + 3 * |m1 - m2| := by
    rw [h_off1, h_off2]
    exact offset_diff_upper m1 m2 b1 b2 hb2

  have h_def : dist ℓ1 ℓ2 =
      ‖ℓ1.1.direction.starProjection - ℓ2.1.direction.starProjection‖ +
      ‖ℓ1.offset - ℓ2.offset‖ := by rfl
  rw [h_def]
  calc
    ‖ℓ1.1.direction.starProjection - ℓ2.1.direction.starProjection‖ + ‖ℓ1.offset - ℓ2.offset‖
      ≤ |m1 - m2| + (|b1 - b2| + 3 * |m1 - m2|) := by linarith
    _ = 4 * |m1 - m2| + |b1 - b2| := by ring
    _ ≤ 4 * d_inf + d_inf := by gcongr
    _ = 5 * d_inf := by ring

/-- Lower bound: offset difference ≥ |b1-b2|/√2 - 3*|m1-m2|,
    for |m1| ≤ 1, |b2| ≤ 3. -/
lemma offset_diff_lower (m1 m2 b1 b2 : ℝ)
    (hm1 : |m1| ≤ 1) (hb2 : |b2| ≤ 3) :
    ‖b1 • offsetVec m1 - b2 • offsetVec m2‖ ≥
      |b1 - b2| / Real.sqrt 2 - 3 * |m1 - m2| := by
  set x := (b1 - b2) • offsetVec m1 with hx
  set y := b2 • (offsetVec m1 - offsetVec m2) with hy
  have h_alg : b1 • offsetVec m1 - b2 • offsetVec m2 = x + y := by
    simp [hx, hy, sub_smul, smul_sub] <;> abel
  rw [h_alg]
  have h1 : ‖x‖ ≤ ‖x + y‖ + ‖y‖ := by
    have h2 : ‖(x + y) - y‖ ≤ ‖x + y‖ + ‖y‖ := by exact norm_sub_le (x + y) y
    have h3 : (x + y) - y = x := by abel
    rw [h3] at h2
    exact h2
  have h4 : ‖x‖ = |b1 - b2| * ‖offsetVec m1‖ := by
    rw [hx, norm_smul] <;> rfl
  have h5 : ‖offsetVec m1‖ ≥ 1 / Real.sqrt 2 := by
    rw [offsetVec_norm m1]
    have h6 : 0 < Real.sqrt (1 + m1^2) := by positivity
    have h7 : Real.sqrt (1 + m1^2) ≤ Real.sqrt 2 := by
      have h8 : 1 + m1^2 ≤ 2 := by nlinarith [abs_le.mp hm1]
      exact Real.sqrt_le_sqrt h8
    exact one_div_le_one_div_of_le h6 h7
  have h6 : ‖y‖ = |b2| * ‖offsetVec m1 - offsetVec m2‖ := by
    rw [hy, norm_smul] <;> rfl
  have h7 : ‖offsetVec m1 - offsetVec m2‖ ≤ |m1 - m2| := offsetVec_lipschitz m1 m2
  have h8 : |b2| ≤ 3 := hb2
  have h9 : |b1 - b2| / Real.sqrt 2 ≤ ‖x‖ := by
    have h91 : 0 ≤ |b1 - b2| := by positivity
    have h92 : |b1 - b2| / Real.sqrt 2 ≤ |b1 - b2| * ‖offsetVec m1‖ := by
      calc
        |b1 - b2| / Real.sqrt 2
          = |b1 - b2| * (1 / Real.sqrt 2) := by ring
        _ ≤ |b1 - b2| * ‖offsetVec m1‖ := by exact mul_le_mul_of_nonneg_left h5 h91
    rw [h4]
    exact h92
  have h10 : ‖x‖ ≤ ‖x + y‖ + ‖y‖ := h1
  have h11 : ‖y‖ ≤ 3 * |m1 - m2| := by
    calc
      ‖y‖ = |b2| * ‖offsetVec m1 - offsetVec m2‖ := h6
      _ ≤ 3 * |m1 - m2| := by gcongr <;> linarith
  linarith

/-- toAffineLine is 22-co-Lipschitz: paramDistLinf ≤ 22 * AffineLine dist,
    for |slope| ≤ 1, |intercept(T2)| ≤ 3. -/
lemma toAffineLine_co_lipschitz {n : ℕ} (T1 T2 : DyadicTube n)
    (hm1 : |T1.slope| ≤ 1) (hm2 : |T2.slope| ≤ 1)
    (hb2 : |T2.intercept| ≤ 3) :
    paramDistLinf T1 T2 ≤ 22 * dist (toAffineLine T1) (toAffineLine T2) := by
  set m1 := T1.slope with hm1_def
  set m2 := T2.slope with hm2_def
  set b1 := T1.intercept with hb1_def
  set b2 := T2.intercept with hb2_def
  set ℓ1 := toAffineLine T1 with hℓ1
  set ℓ2 := toAffineLine T2 with hℓ2
  set d_inf := paramDistLinf T1 T2 with hd_inf_def
  set d_aff := dist ℓ1 ℓ2 with hd_aff_def

  have hdm : |m1 - m2| ≤ d_inf := by
    dsimp only [d_inf, paramDistLinf]; exact le_max_left _ _
  have hdb : |b1 - b2| ≤ d_inf := by
    dsimp only [d_inf, paramDistLinf]; exact le_max_right _ _

  have h_dir_eq1 : ℓ1.1.direction = Submodule.span ℝ {tubeDirV m1} := by
    rw [hℓ1]; exact lineOfSlopeIntercept_direction m1 b1
  have h_dir_eq2 : ℓ2.1.direction = Submodule.span ℝ {tubeDirV m2} := by
    rw [hℓ2]; exact lineOfSlopeIntercept_direction m2 b2

  have h_proj_lower : ‖ℓ1.1.direction.starProjection - ℓ2.1.direction.starProjection‖ ≥ |m1 - m2| / 2 := by
    rw [h_dir_eq1, h_dir_eq2]
    exact proj_lower_bound_simple m1 m2 hm1 hm2

  have h_off1 : ℓ1.offset = b1 • offsetVec m1 := by
    rw [hℓ1, toAffineLine]; exact offset_formula m1 b1
  have h_off2 : ℓ2.offset = b2 • offsetVec m2 := by
    rw [hℓ2, toAffineLine]; exact offset_formula m2 b2

  have h_off_lower : ‖ℓ1.offset - ℓ2.offset‖ ≥ |b1 - b2| / Real.sqrt 2 - 3 * |m1 - m2| := by
    rw [h_off1, h_off2]
    exact offset_diff_lower m1 m2 b1 b2 hm1 hb2

  have h_def : d_aff =
      ‖ℓ1.1.direction.starProjection - ℓ2.1.direction.starProjection‖ +
      ‖ℓ1.offset - ℓ2.offset‖ := by rfl

  by_cases h_case : |m1 - m2| ≥ |b1 - b2| / 10
  · -- Case 1: slope difference dominates
    have h9 : d_inf ≤ 11 * |m1 - m2| := by
      dsimp only [d_inf, paramDistLinf]
      have h10 : max |m1 - m2| |b1 - b2| ≤ |m1 - m2| + |b1 - b2| := by
        have h101 : 0 ≤ |b1 - b2| := by positivity
        have h102 : 0 ≤ |m1 - m2| := by positivity
        exact max_le (by linarith) (by linarith)
      have h11 : |b1 - b2| ≤ 10 * |m1 - m2| := by linarith
      linarith
    have h10 : d_aff ≥ |m1 - m2| / 2 := by
      rw [h_def]
      have h11 : 0 ≤ ‖ℓ1.offset - ℓ2.offset‖ := by positivity
      linarith [h_proj_lower]
    calc
      d_inf ≤ 11 * |m1 - m2| := h9
      _ = 22 * (|m1 - m2| / 2) := by ring
      _ ≤ 22 * d_aff := by gcongr
  · -- Case 2: intercept difference dominates
    have h9 : |m1 - m2| < |b1 - b2| / 10 := by linarith
    have h10 : d_inf = |b1 - b2| := by
      dsimp only [d_inf, paramDistLinf]
      have h11 : |m1 - m2| < |b1 - b2| := by
        calc
          |m1 - m2| < |b1 - b2| / 10 := h9
          _ ≤ |b1 - b2| := by
            have h_nonneg : 0 ≤ |b1 - b2| := by positivity
            linarith
      exact max_eq_right h11.le
    have h_sqrt2_pos : 0 < Real.sqrt 2 := by positivity
    have h11 : 1 / Real.sqrt 2 - 3 / 10 > 0 := by
      have h12 : Real.sqrt 2 ≤ 2 := by
        have h13 : Real.sqrt 2 ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by norm_num)
        have h14 : Real.sqrt 4 = 2 := by norm_num
        rw [h14] at h13
        exact h13
      have h14 : 1 / Real.sqrt 2 ≥ 1 / 2 := by
        have h15 : 0 < Real.sqrt 2 := by positivity
        exact one_div_le_one_div_of_le h15 h12
      linarith
    have h12 : d_aff ≥ |b1 - b2| * (1 / Real.sqrt 2 - 3 / 10) := by
      have h13 : d_aff ≥ |b1 - b2| / Real.sqrt 2 - (5 / 2 : ℝ) * |m1 - m2| := by
        rw [h_def]
        linarith [h_proj_lower, h_off_lower]
      have h14 : (5 / 2 : ℝ) * |m1 - m2| ≤ (3 / 10 : ℝ) * |b1 - b2| := by
        have h15 : |m1 - m2| < |b1 - b2| / 10 := h9
        have h16 : (5 / 2 : ℝ) * |m1 - m2| < (5 / 2 : ℝ) * (|b1 - b2| / 10) := by
          gcongr <;> linarith
        have h17 : (5 / 2 : ℝ) * (|b1 - b2| / 10) = (1 / 4 : ℝ) * |b1 - b2| := by ring
        have h18 : (1 / 4 : ℝ) ≤ (3 / 10 : ℝ) := by norm_num
        linarith
      have h19 : |b1 - b2| / Real.sqrt 2 - (5 / 2 : ℝ) * |m1 - m2| ≥
          |b1 - b2| * (1 / Real.sqrt 2 - 3 / 10) := by
        have h20 : |b1 - b2| * (1 / Real.sqrt 2 - 3 / 10) =
            |b1 - b2| / Real.sqrt 2 - (3 / 10 : ℝ) * |b1 - b2| := by ring
        rw [h20]
        linarith
      linarith
    have h14 : 1 / (1 / Real.sqrt 2 - 3 / 10) ≤ 22 := by
      have h15 : 0 < 1 / Real.sqrt 2 - 3 / 10 := h11
      have h16 : 1 / (1 / Real.sqrt 2 - 3 / 10) =
          10 * Real.sqrt 2 / (10 - 3 * Real.sqrt 2) := by
        field_simp [h_sqrt2_pos.ne'] <;> ring
      rw [h16]
      have h17 : 10 - 3 * Real.sqrt 2 > 0 := by
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      have h18 : 10 * Real.sqrt 2 ≤ 22 * (10 - 3 * Real.sqrt 2) := by
        nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
      have h19 : 0 ≤ 10 * Real.sqrt 2 := by positivity
      have h20 : 10 * Real.sqrt 2 / (10 - 3 * Real.sqrt 2) ≤ 22 := by
        calc
          10 * Real.sqrt 2 / (10 - 3 * Real.sqrt 2)
            ≤ 22 * (10 - 3 * Real.sqrt 2) / (10 - 3 * Real.sqrt 2) := by gcongr
          _ = 22 := by
            field_simp [h17.ne'] <;> ring
      exact h20
    calc
      d_inf = |b1 - b2| := h10
      _ = (1 / (1 / Real.sqrt 2 - 3 / 10)) * (|b1 - b2| * (1 / Real.sqrt 2 - 3 / 10)) := by
        set c := 1 / Real.sqrt 2 - 3 / 10 with hc
        have hc_ne : c ≠ 0 := h11.ne'
        have h21 : (1 / c) * (|b1 - b2| * c) = |b1 - b2| := by
          have h22 : (1 / c) * c = 1 := by field_simp [hc_ne] <;> ring
          calc
            (1 / c) * (|b1 - b2| * c)
              = |b1 - b2| * ((1 / c) * c) := by ring
            _ = |b1 - b2| * 1 := by rw [h22]
            _ = |b1 - b2| := by ring
        exact h21.symm
      _ ≤ 22 * d_aff := by gcongr

/-! ============================================================================
   4. S-set transfer: IsFiniteTubeSSet → IsDeltaSSet on AffineLine image
   ============================================================================ -/

/-- Transfer IsFiniteTubeSSet from DyadicTube parameter space to IsDeltaSSet
    on the toAffineLine image.

    Uses:
    - 22-co-Lipschitz bound to map AffineLine balls to parameter balls
    - IsFiniteTubeSSet ball-growth in parameter space
    - dyadic_card_to_ncover for the covering number lower bound

    Constant: C' = C * 400 * 44^s.
-/
lemma finiteTubeSSet_to_affineSSet {n : ℕ} {s C : ℝ} {F : Finset (DyadicTube n)}
    (hs : 0 ≤ s) (hC_one : 1 ≤ C)
    (hm : ∀ T ∈ F, |T.slope| ≤ 1)
    (hb : ∀ T ∈ F, |T.intercept| ≤ 3)
    (h : InductionOnScales.IsFiniteTubeSSet s C F) :
    IsDeltaSSet (dyadicDelta n) s (C * 400 * 44^s)
      (toAffineLine '' (F : Set (DyadicTube n))) := by
  set δ := dyadicDelta n with hδ
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  have hC_pos : 0 < C := by linarith
  set S' : Set AffineLine := toAffineLine '' (F : Set (DyadicTube n)) with hS'_def
  have hF_nonempty : F.Nonempty := h.1
  have hS'_nonempty : S'.Nonempty := by
    rcases hF_nonempty with ⟨T, hT⟩
    exact ⟨toAffineLine T, ⟨T, hT, rfl⟩⟩
  have h_inj : Set.InjOn toAffineLine (F : Set (DyadicTube n)) := by
    intro T1 hT1 T2 hT2 h
    by_cases hne : T1 = T2
    · exact hne
    · exfalso
      have hsep : δ / 2 ≤ dist (toAffineLine T1) (toAffineLine T2) :=
        dyadic_tube_affine_separated T1 T2 hne (hm T1 hT1) (hm T2 hT2)
      rw [h] at hsep
      have h0 : dist (toAffineLine T2) (toAffineLine T2) = 0 := dist_self _
      rw [h0] at hsep
      have h_pos : 0 < δ / 2 := by linarith [hδ_pos]
      linarith
  refine' ⟨hS'_nonempty, hδ_pos, by positivity, hs, _⟩
  intro y r hr
  set G : Finset (DyadicTube n) := F.filter (fun T => dist (toAffineLine T) y ≤ r) with hG_def
  set B : Finset AffineLine := G.image toAffineLine with hB_def
  have hB_eq : (B : Set AffineLine) = S' ∩ Metric.closedBall y r := by
    ext ℓ
    simp only [hB_def, hS'_def, Finset.mem_coe, Finset.mem_image, Set.mem_inter_iff,
      Metric.mem_closedBall, Set.mem_image]
    constructor
    · rintro ⟨T, hT, rfl⟩
      have hT_in_F : T ∈ F := (Finset.mem_filter.mp hT).1
      have h_dist : dist (toAffineLine T) y ≤ r := (Finset.mem_filter.mp hT).2
      exact ⟨⟨T, hT_in_F, rfl⟩, h_dist⟩
    · rintro ⟨⟨T, hT, rfl⟩, h_dist⟩
      exact ⟨T, Finset.mem_filter.mpr ⟨hT, h_dist⟩, rfl⟩
  by_cases hG_empty : G.Nonempty
  · -- G is nonempty
    rcases hG_empty with ⟨T0, hT0⟩
    have hT0_in_F : T0 ∈ F := (Finset.mem_filter.mp hT0).1
    have h_dist0 : dist (toAffineLine T0) y ≤ r := (Finset.mem_filter.mp hT0).2
    have h_ball : G ⊆ F.filter (fun T => paramDistLinf T T0 ≤ 44 * r) := by
      intro T hT
      have hT_in_F : T ∈ F := (Finset.mem_filter.mp hT).1
      have h_distT : dist (toAffineLine T) y ≤ r := (Finset.mem_filter.mp hT).2
      have h_coLip : paramDistLinf T T0 ≤ 22 * dist (toAffineLine T) (toAffineLine T0) :=
        toAffineLine_co_lipschitz T T0 (hm T hT_in_F) (hm T0 hT0_in_F) (hb T0 hT0_in_F)
      have h_tri : dist (toAffineLine T) (toAffineLine T0) ≤ 2 * r := by
        calc
          dist (toAffineLine T) (toAffineLine T0)
            ≤ dist (toAffineLine T) y + dist y (toAffineLine T0) := dist_triangle _ _ _
          _ = dist (toAffineLine T) y + dist (toAffineLine T0) y := by rw [dist_comm y (toAffineLine T0)]
          _ ≤ r + r := by gcongr
          _ = 2 * r := by ring
      have h_final : paramDistLinf T T0 ≤ 44 * r := by
        calc
          paramDistLinf T T0 ≤ 22 * dist (toAffineLine T) (toAffineLine T0) := h_coLip
          _ ≤ 22 * (2 * r) := by gcongr
          _ = 44 * r := by ring
      exact Finset.mem_filter.mpr ⟨hT_in_F, h_final⟩
    have hG_card_le : (G.card : ℝ) ≤ ((F.filter (fun T => paramDistLinf T T0 ≤ 44 * r)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card h_ball
    have h44r_ge_delta : δ ≤ 44 * r := by
      have h1 : δ ≤ r := hr
      linarith [hδ_pos]
    have h_frost := h.2.2.2.2 T0 (44 * r) h44r_ge_delta
    have h_card_le : (G.card : ℝ) ≤ C * (44 * r)^s * (F.card : ℝ) := by
      calc
        (G.card : ℝ) ≤ (F.filter (fun T => paramDistLinf T T0 ≤ 44 * r)).card := hG_card_le
        _ ≤ C * (44 * r)^s * (F.card : ℝ) := h_frost
    let A : Set AffineLine := S' ∩ Metric.closedBall y r
    have h_ncover_le : (Metric.externalCoveringNumber δ.toNNReal A : ENNReal) ≤
        (B.card : ENNReal) := by
      have h : Metric.externalCoveringNumber δ.toNNReal A ≤ A.encard :=
        Metric.externalCoveringNumber_le_encard_self A
      have hA : A = S' ∩ Metric.closedBall y r := by rfl
      have h2 : A.encard = (B.card : ℕ∞) := by
        rw [hA, ←hB_eq] <;> simp
      rw [h2] at h
      exact_mod_cast h
    have h_card_image : B.card = G.card := by
      rw [hB_def, Finset.card_image_of_injOn]
      intro T1 _ T2 _ h
      exact h_inj (Finset.mem_filter.mp ‹_›).1 (Finset.mem_filter.mp ‹_›).1 h
    have h_lower : (F.card : ENNReal) ≤ (400 : ENNReal) *
        Metric.externalCoveringNumber δ.toNNReal S' := by
      have h_ncov : ENNReal.ofReal ((F.card : ℝ) / 400) ≤
          Metric.externalCoveringNumber δ.toNNReal S' :=
        dyadic_card_to_ncover F hm hb
      have h_eq : ENNReal.ofReal ((F.card : ℝ) / 400) = (F.card : ENNReal) / 400 := by
        have h : (F.card : ℝ) / 400 = (F.card : ℝ) * (1 / 400 : ℝ) := by ring
        rw [h]
        have h_mul : ENNReal.ofReal ((F.card : ℝ) * (1 / 400 : ℝ)) =
            ENNReal.ofReal (F.card : ℝ) * ENNReal.ofReal (1 / 400 : ℝ) :=
          ENNReal.ofReal_mul (by positivity)
        rw [h_mul]
        have h_inv : ENNReal.ofReal (1 / 400 : ℝ) = (400 : ENNReal)⁻¹ := by
          simp
        rw [h_inv]
        <;> simp [div_eq_mul_inv]
      rw [h_eq] at h_ncov
      have h : (F.card : ENNReal) ≤ Metric.externalCoveringNumber δ.toNNReal S' * (400 : ENNReal) := by
        simpa [ENNReal.div_le_iff_le_mul] using h_ncov
      have h' : Metric.externalCoveringNumber δ.toNNReal S' * (400 : ENNReal) =
          (400 : ENNReal) * Metric.externalCoveringNumber δ.toNNReal S' := by
        rw [mul_comm]
      rw [h'] at h
      exact h
    have h_r_nonneg : 0 ≤ r := by linarith [hδ_pos, hr]
    have h44_pos : 0 < (44 : ℝ) := by norm_num
    have h_B_card_real : (B.card : ℝ) = (G.card : ℝ) := by exact_mod_cast h_card_image
    have h_card_le_B : (B.card : ℝ) ≤ C * (44 * r)^s * (F.card : ℝ) := by
      rw [h_B_card_real]
      exact h_card_le
    have h_main : (B.card : ENNReal) ≤
        ENNReal.ofReal (C * 400 * 44^s) * (ENNReal.ofReal r)^s *
          Metric.externalCoveringNumber δ.toNNReal S' := by
      have h1 : (B.card : ENNReal) = ENNReal.ofReal (B.card : ℝ) := by simp
      rw [h1]
      have h2 : ENNReal.ofReal (B.card : ℝ) ≤
          ENNReal.ofReal (C * (44 * r)^s * (F.card : ℝ)) :=
        ENNReal.ofReal_le_ofReal h_card_le_B
      have h3 : C * (44 * r)^s * (F.card : ℝ) =
          (C * 400 * 44^s) * r^s * ((F.card : ℝ) / 400) := by
        have h4 : (44 * r)^s = 44^s * r^s :=
          Real.mul_rpow (x := (44 : ℝ)) (y := r) (z := s) (by norm_num) h_r_nonneg
        rw [h4] <;> ring
      have h5 : ENNReal.ofReal (C * (44 * r)^s * (F.card : ℝ)) =
          ENNReal.ofReal ((C * 400 * 44^s) * r^s * ((F.card : ℝ) / 400)) := by
        rw [h3]
      rw [h5] at h2
      have h_pos1 : 0 ≤ C * 400 * 44^s := by positivity
      have h_pos2 : 0 ≤ r^s := by positivity
      have h_pos3 : 0 ≤ (F.card : ℝ) / 400 := by positivity
      have h6 : ENNReal.ofReal ((C * 400 * 44^s) * r^s * ((F.card : ℝ) / 400)) =
          ENNReal.ofReal (C * 400 * 44^s) * ENNReal.ofReal (r^s) *
            ENNReal.ofReal ((F.card : ℝ) / 400) := by
        have h_step1 : ENNReal.ofReal (((C * 400 * 44^s) * r^s) * ((F.card : ℝ) / 400)) =
            ENNReal.ofReal ((C * 400 * 44^s) * r^s) * ENNReal.ofReal ((F.card : ℝ) / 400) :=
          ENNReal.ofReal_mul (by positivity)
        rw [h_step1]
        have h_step2 : ENNReal.ofReal ((C * 400 * 44^s) * r^s) =
            ENNReal.ofReal (C * 400 * 44^s) * ENNReal.ofReal (r^s) :=
          ENNReal.ofReal_mul h_pos1
        rw [h_step2] <;> ring
      rw [h6] at h2
      have h7 : ENNReal.ofReal (r^s) = (ENNReal.ofReal r)^s := by
        exact Eq.symm (ENNReal.ofReal_rpow_of_nonneg h_r_nonneg hs)
      rw [h7] at h2
      have h8 : ENNReal.ofReal ((F.card : ℝ) / 400) ≤ Metric.externalCoveringNumber δ.toNNReal S' :=
        dyadic_card_to_ncover F hm hb
      have h9 : ENNReal.ofReal (C * 400 * 44^s) * (ENNReal.ofReal r)^s *
            ENNReal.ofReal ((F.card : ℝ) / 400) ≤
          ENNReal.ofReal (C * 400 * 44^s) * (ENNReal.ofReal r)^s *
            Metric.externalCoveringNumber δ.toNNReal S' := by
        gcongr
        <;> ring
      exact le_trans h2 h9
    calc
      (Metric.externalCoveringNumber δ.toNNReal A : ENNReal)
        ≤ (B.card : ENNReal) := h_ncover_le
      _ ≤ ENNReal.ofReal (C * 400 * 44^s) * (ENNReal.ofReal r)^s *
            Metric.externalCoveringNumber δ.toNNReal S' := h_main
  · -- G is empty
    have hB_empty : B = ∅ := by
      rw [hB_def]
      simpa [hG_def] using hG_empty
    have h_cover : Metric.externalCoveringNumber δ.toNNReal (S' ∩ Metric.closedBall y r) = 0 := by
      rw [←hB_eq, hB_empty]
      <;> simp
    rw [h_cover]
    <;> simp

/-! ============================================================================
   5. Slope bound and full S-set transfer chain
   ============================================================================ -/

/-- Slope bound from the allowed parameter strip. -/
lemma slope_bound_from_strip {n : ℕ} (T : DyadicTube n)
    (h : -(2 ^ n : ℤ) ≤ T.a ∧ T.a < (2 ^ n : ℤ)) :
    |T.slope| ≤ 1 := by
  set δ := dyadicDelta n with hδ
  have hδ_pos : 0 < δ := dyadicDelta_pos n
  have hδ_eq : δ * (2 ^ n : ℝ) = 1 := by
    simp [hδ, dyadicDelta, Real.rpow_neg] <;> field_simp <;> ring
  have h_slope_eq : T.slope = (T.a : ℝ) * δ := by rfl
  have h1 : -1 ≤ T.slope := by
    rw [h_slope_eq]
    have h2 : -(2 ^ n : ℝ) ≤ (T.a : ℝ) := by exact_mod_cast h.1
    have h3 : (T.a : ℝ) * δ ≥ -1 := by
      calc
        (T.a : ℝ) * δ ≥ (-(2 ^ n : ℝ)) * δ := by gcongr
        _ = -1 := by
          have h4 : (-(2 ^ n : ℝ)) * δ = -1 := by
            have h5 : δ * (2 ^ n : ℝ) = 1 := hδ_eq
            linarith
          exact h4
    exact h3
  have h2 : T.slope < 1 := by
    rw [h_slope_eq]
    have h3 : (T.a : ℝ) < (2 ^ n : ℝ) := by exact_mod_cast h.2
    have h4 : (T.a : ℝ) * δ < 1 := by
      calc
        (T.a : ℝ) * δ < (2 ^ n : ℝ) * δ := by gcongr
        _ = 1 := by
          have h5 : (2 ^ n : ℝ) * δ = 1 := by linarith [hδ_eq]
          exact h5
    exact h4
  rw [abs_le] <;> constructor <;> linarith

/-- Full S-set transfer from DyadicTube (L1 metric) to AffineLine image.

    Chain: IsDeltaSSet → DiscreteFrostmanL1 (×5) → IsFiniteTubeSSet (×2)
           → IsDeltaSSet on AffineLine (×400×44^s).
    Output constant: `max 1 (10 * C_fine) * 400 * 44^s`. -/
lemma tubeSSet_transfer {n : ℕ} {s C_fine : ℝ} {F : Finset (DyadicTube n)}
    (hs : 0 ≤ s) (hs_lt_one : s < 1) (hC_one : 1 ≤ C_fine)
    (hm : ∀ T ∈ F, |T.slope| ≤ 1)
    (hb : ∀ T ∈ F, |T.intercept| ≤ 3)
    (h : IsDeltaSSet (dyadicDelta n) s C_fine (F : Set (DyadicTube n))) :
    IsDeltaSSet (dyadicDelta n) s
      (max 1 (10 * C_fine) * 400 * 44^s)
      (toAffineLine '' (F : Set (DyadicTube n))) := by
  have h1 : DiscreteFrostmanL1 s (5 * C_fine) F :=
    isDeltaSSet_to_discreteFrostmanL1 h
  have h2 : IsFiniteTubeSSet s (max 1 (2 * (5 * C_fine))) F :=
    discreteFrostmanL1_to_isFiniteTubeSSet hs_lt_one.le hs h1
  have h3 : max 1 (2 * (5 * C_fine)) = max 1 (10 * C_fine) := by ring_nf
  rw [h3] at h2
  exact finiteTubeSSet_to_affineSSet hs (by exact le_max_left _ _) hm hb h2

end DyadicToAffineAdapters
