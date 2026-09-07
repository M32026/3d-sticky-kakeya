module

/-
  Dyadic tube cardinality to δ-covering number lower bound.

  Main results:
  - `dyadic_tube_affine_separated`: distinct DyadicTubes with |slope|≤1
    are δ/2-separated in AffineLine space.
  - `dyadic_card_to_ncover`: δ-covering number ≥ cardinality / K.

  Mathematical core adapted from TranslationLayer.lean (archived),
  specialized for DyadicTube n.
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicTubes
public import MyLeanRepo.DiscretisedFurstenbergEstimate.TubesAndSlopes
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal
open DirecretisedFurstenbergEstimate
open DiscretisedFurstenbergEstimate

namespace DyadicCardToNcover

abbrev Plane := EuclideanSpace ℝ (Fin 2)

noncomputable def e0 : Plane := TubesAndSlopes.mkPlane 1 0
noncomputable def e1 : Plane := TubesAndSlopes.mkPlane 0 1

lemma e0_norm : ‖(e0 : Plane)‖ = 1 := by
  have h4 : ‖(e0 : Plane)‖ ^ 2 = 1 := by
    simp [e0, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, TubesAndSlopes.mkPlane]
    <;> norm_num
  have h7 : 0 ≤ ‖(e0 : Plane)‖ := by positivity
  nlinarith

lemma e1_norm : ‖(e1 : Plane)‖ = 1 := by
  have h4 : ‖(e1 : Plane)‖ ^ 2 = 1 := by
    simp [e1, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, TubesAndSlopes.mkPlane]
    <;> norm_num
  have h7 : 0 ≤ ‖(e1 : Plane)‖ := by positivity
  nlinarith

/-- Direction vector for slope m. -/
def tubeDirV (m : ℝ) : Plane := TubesAndSlopes.mkPlane 1 m

/-- Offset unit-ish vector for slope m: (-m, 1)/(1+m²). -/
noncomputable def offsetVec (m : ℝ) : Plane :=
  TubesAndSlopes.mkPlane (-m / (1 + m^2)) (1 / (1 + m^2))

-- ============================================================================
-- Construct AffineLine from slope-intercept
-- ============================================================================

/-- Construct an AffineLine for y = m*x + b. -/
noncomputable def lineOfSlopeIntercept (m b : ℝ) : AffineLine :=
  let p : Plane := TubesAndSlopes.mkPlane 0 b
  let v : Plane := tubeDirV m
  let dir : Submodule ℝ Plane := Submodule.span ℝ {v}
  let aff : AffineSubspace ℝ Plane := AffineSubspace.mk' p dir
  have h_v_ne_zero : v ≠ 0 := by
    intro h
    have h1 : v 0 = 0 := by rw [h] <;> simp
    have h2 : v 0 = 1 := TubesAndSlopes.mkPlane_apply0 1 m
    rw [h2] at h1 <;> norm_num at h1
  have h_finrank : Module.finrank ℝ dir = 1 := by
    exact finrank_span_singleton h_v_ne_zero
  have h_dir_eq : aff.direction = dir := AffineSubspace.direction_mk' p dir
  ⟨aff, by rw [h_dir_eq]; exact h_finrank⟩

/-- Map a DyadicTube to its center AffineLine. -/
noncomputable def toAffineLine {n : ℕ} (T : DyadicTube n) : AffineLine :=
  lineOfSlopeIntercept T.slope T.intercept

/-- The direction of lineOfSlopeIntercept is span{tubeDirV m}. -/
lemma lineOfSlopeIntercept_direction (m b : ℝ) :
    (lineOfSlopeIntercept m b).1.direction = Submodule.span ℝ {tubeDirV m} := by
  delta lineOfSlopeIntercept
  simp [AffineSubspace.direction_mk']
  <;> rfl

/-- Integer nonzero implies absolute value ≥ 1, in ℝ. -/
lemma int_abs_ge_one {x y : ℤ} (h : x ≠ y) : (1 : ℝ) ≤ |(x : ℝ) - (y : ℝ)| := by
  have h1 : x - y ≠ 0 := by omega
  have h2 : (1 : ℤ) ≤ |x - y| := by
    have h3 : 0 < |x - y| := abs_pos.mpr h1
    omega
  have h4 : ((1 : ℝ) ≤ ↑(|x - y|)) := by exact_mod_cast h2
  have h5 : (↑(|x - y|) : ℝ) = |(x : ℝ) - (y : ℝ)| := by
    by_cases h : 0 ≤ x - y
    · have h9 : |x - y| = x - y := by rw [abs_of_nonneg h]
      have h10 : 0 ≤ (x : ℝ) - (y : ℝ) := by exact_mod_cast h
      rw [h9, abs_of_nonneg h10] <;> simp
    · have h9 : |x - y| = -(x - y) := by rw [abs_of_neg (by omega)]
      have h10 : (x : ℝ) - (y : ℝ) < 0 := by exact_mod_cast (by omega)
      rw [h9, abs_of_neg h10] <;> simp
  rw [h5] at h4
  exact h4

-- ============================================================================
-- Projection formulas
-- ============================================================================

lemma proj_e1 (m : ℝ) :
    (Submodule.span ℝ {tubeDirV m}).starProjection e1 =
      (m / (1 + m^2)) • tubeDirV m := by
  have h : (Submodule.span ℝ {tubeDirV m}).starProjection e1 =
      (inner ℝ (tubeDirV m) e1 / ‖tubeDirV m‖ ^ 2) • tubeDirV m :=
    Submodule.starProjection_singleton (𝕜 := ℝ) (v := tubeDirV m) (w := e1)
  rw [h]
  have h_inner : inner ℝ (tubeDirV m) e1 = m := by
    rw [PiLp.inner_apply, Fin.sum_univ_two]
    <;> simp [tubeDirV, e1, TubesAndSlopes.mkPlane] <;> ring
  have h_norm : ‖tubeDirV m‖ ^ 2 = 1 + m^2 := by
    simp [tubeDirV, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, TubesAndSlopes.mkPlane]
    <;> ring
  rw [h_inner, h_norm] <;> ring

lemma proj_diff_e1_norm (m1 m2 : ℝ) :
    ‖(Submodule.span ℝ {tubeDirV m1}).starProjection e1 -
      (Submodule.span ℝ {tubeDirV m2}).starProjection e1‖ =
    |m1 - m2| / (Real.sqrt (1 + m1^2) * Real.sqrt (1 + m2^2)) := by
  set v1 := (Submodule.span ℝ {tubeDirV m1}).starProjection e1 with hv1
  set v2 := (Submodule.span ℝ {tubeDirV m2}).starProjection e1 with hv2
  have h_sub : v1 - v2 = TubesAndSlopes.mkPlane
        (m1 / (1 + m1^2) - m2 / (1 + m2^2))
        (m1^2 / (1 + m1^2) - m2^2 / (1 + m2^2)) := by
    rw [hv1, hv2, proj_e1 m1, proj_e1 m2]
    ext i; fin_cases i <;> simp [tubeDirV, TubesAndSlopes.mkPlane, smul_eq_mul] <;> ring
  have h_id : m1^2 / (1 + m1^2) - m2^2 / (1 + m2^2) =
        -(1 / (1 + m1^2) - 1 / (1 + m2^2)) := by field_simp <;> ring
  have h_norm2 : ‖v1 - v2‖ ^ 2 = ((v1 - v2) 0)^2 + ((v1 - v2) 1)^2 := by
    simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  have h_comp0 : (v1 - v2) 0 = m1 / (1 + m1^2) - m2 / (1 + m2^2) := by
    rw [h_sub] <;> simp [TubesAndSlopes.mkPlane]
  have h_comp1 : (v1 - v2) 1 = -(1 / (1 + m1^2) - 1 / (1 + m2^2)) := by
    rw [h_sub] <;> simp [TubesAndSlopes.mkPlane, h_id] <;> ring
  have h_main : ‖v1 - v2‖ ^ 2 = (m1 - m2)^2 / ((1 + m1^2) * (1 + m2^2)) := by
    rw [h_norm2, h_comp0, h_comp1]
    have h_neg : (-(1 / (1 + m1^2) - 1 / (1 + m2^2))) ^ 2 =
          (1 / (1 + m1^2) - 1 / (1 + m2^2)) ^ 2 := by ring
    rw [h_neg]
    exact TubesAndSlopes.semicircle_chord_algebraic m1 m2
  have h_nonneg : 0 ≤ ‖v1 - v2‖ := by positivity
  have h : ‖v1 - v2‖ = Real.sqrt ((m1 - m2)^2 / ((1 + m1^2) * (1 + m2^2))) := by
    rw [← h_main, Real.sqrt_sq h_nonneg]
  rw [h, Real.sqrt_div (by positivity)]
  have h3 : Real.sqrt ((m1 - m2)^2) = |m1 - m2| := by rw [Real.sqrt_sq_eq_abs]
  have h4 : Real.sqrt ((1 + m1^2) * (1 + m2^2)) =
      Real.sqrt (1 + m1^2) * Real.sqrt (1 + m2^2) := by
    rw [Real.sqrt_mul] <;> positivity
  rw [h3, h4] <;> ring

/-- Lower bound: ‖P1 - P2‖ ≥ |m1-m2| / √((1+m1²)(1+m2²)). -/
lemma proj_diff_lower_bound (m1 m2 : ℝ) :
    |m1 - m2| / (Real.sqrt (1 + m1^2) * Real.sqrt (1 + m2^2)) ≤
    ‖(Submodule.span ℝ {tubeDirV m1}).starProjection -
      (Submodule.span ℝ {tubeDirV m2}).starProjection‖ := by
  let P1 := (Submodule.span ℝ {tubeDirV m1}).starProjection
  let P2 := (Submodule.span ℝ {tubeDirV m2}).starProjection
  have h3 : ‖(P1 - P2) e1‖ ≤ ‖P1 - P2‖ * ‖(e1 : Plane)‖ :=
    ContinuousLinearMap.le_opNorm (P1 - P2) e1
  rw [e1_norm] at h3
  have h4 : ‖(P1 - P2) e1‖ = |m1 - m2| / (Real.sqrt (1 + m1^2) * Real.sqrt (1 + m2^2)) :=
    proj_diff_e1_norm m1 m2
  rw [h4] at h3
  simpa using h3

/-- For |m1|, |m2| ≤ 1: ‖P1 - P2‖ ≥ |m1-m2| / 2. -/
lemma proj_lower_bound_simple (m1 m2 : ℝ) (hm1 : |m1| ≤ 1) (hm2 : |m2| ≤ 1) :
    |m1 - m2| / 2 ≤
    ‖(Submodule.span ℝ {tubeDirV m1}).starProjection -
      (Submodule.span ℝ {tubeDirV m2}).starProjection‖ := by
  have h_denom : Real.sqrt (1 + m1^2) * Real.sqrt (1 + m2^2) ≤ 2 := by
    have h1 : 1 + m1^2 ≤ 2 := by nlinarith [abs_le.mp hm1]
    have h2 : 1 + m2^2 ≤ 2 := by nlinarith [abs_le.mp hm2]
    have h3 : Real.sqrt (1 + m1^2) ≤ Real.sqrt 2 := Real.sqrt_le_sqrt h1
    have h4 : Real.sqrt (1 + m2^2) ≤ Real.sqrt 2 := Real.sqrt_le_sqrt h2
    have h5 : Real.sqrt (1 + m1^2) * Real.sqrt (1 + m2^2) ≤ 2 := by
      calc
        Real.sqrt (1 + m1^2) * Real.sqrt (1 + m2^2)
          ≤ Real.sqrt 2 * Real.sqrt 2 := by gcongr
        _ = 2 := by
          rw [←Real.sqrt_mul (by norm_num)] <;> norm_num
    exact h5
  have h6 : 0 ≤ |m1 - m2| := by positivity
  have h7 : |m1 - m2| / 2 ≤ |m1 - m2| / (Real.sqrt (1 + m1^2) * Real.sqrt (1 + m2^2)) :=
    div_le_div_of_nonneg_left h6 (by positivity) h_denom
  exact le_trans h7 (proj_diff_lower_bound m1 m2)

-- ============================================================================
-- Offset formula
-- ============================================================================

lemma offset_formula (m b : ℝ) :
    (lineOfSlopeIntercept m b).offset = b • offsetVec m := by
  let p : Plane := TubesAndSlopes.mkPlane 0 b
  let v : Plane := tubeDirV m
  let dir : Submodule ℝ Plane := Submodule.span ℝ {v}
  let aff : AffineSubspace ℝ Plane := AffineSubspace.mk' p dir
  let P := dir.starProjection
  have h_p_mem : p ∈ aff := by exact AffineSubspace.self_mem_mk' p dir
  have h_dir : aff.direction = dir := by
    simp [aff, AffineSubspace.direction_mk'] <;> rfl
  have h_main : (EuclideanGeometry.orthogonalProjection aff 0 : Plane) = P (0 - p) + p := by
    have h := EuclideanGeometry.orthogonalProjection_apply_mem aff (x := p) h_p_mem (p := 0)
    have h_eq : ∀ (x : Plane), aff.direction.orthogonalProjectionOnto x = P x := by
      intro x; rw [h_dir] <;> rfl
    have h' : (EuclideanGeometry.orthogonalProjection aff 0 : Plane) =
        aff.direction.orthogonalProjectionOnto (0 - p) + p := by simpa using h
    rw [h', h_eq (0 - p)]
  have hPp : P p = ((b * m) / (1 + m^2)) • v := by
    have h : P p = (inner ℝ v p / ‖v‖ ^ 2) • v :=
      Submodule.starProjection_singleton (𝕜 := ℝ) (v := v) (w := p)
    rw [h]
    have h_inner : inner ℝ v p = b * m := by
      rw [PiLp.inner_apply, Fin.sum_univ_two]
      <;> simp [v, p, tubeDirV, TubesAndSlopes.mkPlane] <;> ring
    have h_norm : ‖v‖ ^ 2 = 1 + m^2 := by
      simp [v, tubeDirV, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, TubesAndSlopes.mkPlane]
      <;> ring
    rw [h_inner, h_norm] <;> ring
  have h0 : P (0 - p) = -P p := by
    have h : P (0 - p) = P (-p) := by simp
    rw [h, ContinuousLinearMap.map_neg P p]
  have h_goal : (P (0 - p) + p : Plane) = b • offsetVec m := by
    rw [h0, hPp]
    ext i
    fin_cases i
    · simp [v, p, tubeDirV, offsetVec, TubesAndSlopes.mkPlane, TubesAndSlopes.mkPlane_apply0, TubesAndSlopes.mkPlane_apply1, smul_eq_mul]
      <;> field_simp <;> ring
    · simp [v, p, tubeDirV, offsetVec, TubesAndSlopes.mkPlane, TubesAndSlopes.mkPlane_apply0, TubesAndSlopes.mkPlane_apply1, smul_eq_mul]
      <;> field_simp <;> ring
  have h_final : (lineOfSlopeIntercept m b).offset = (EuclideanGeometry.orthogonalProjection aff 0 : Plane) := by
    rfl
  rw [h_final, h_main, h_goal]

-- ============================================================================
-- Separation lemma
-- ============================================================================

/-- Distinct dyadic tubes with |slope| ≤ 1 are δ/2-separated in AffineLine space. -/
lemma dyadic_tube_affine_separated {n : ℕ} (T1 T2 : DyadicTube n)
    (h_ne : T1 ≠ T2) (hm1 : |T1.slope| ≤ 1) (hm2 : |T2.slope| ≤ 1) :
    DiscretisedFurstenbergEstimate.dyadicDelta n / 2 ≤
    dist (toAffineLine T1) (toAffineLine T2) := by
  set δ := DiscretisedFurstenbergEstimate.dyadicDelta n with hδ
  set m1 := T1.slope with hm1_def
  set m2 := T2.slope with hm2_def
  set b1 := T1.intercept with hb1_def
  set b2 := T2.intercept with hb2_def
  set ℓ1 := toAffineLine T1 with hℓ1
  set ℓ2 := toAffineLine T2 with hℓ2
  have hδ_pos : 0 < δ := DiscretisedFurstenbergEstimate.dyadicDelta_pos n
  have h_dist : dist ℓ1 ℓ2 =
      ‖ℓ1.1.direction.starProjection - ℓ2.1.direction.starProjection‖ +
      ‖ℓ1.offset - ℓ2.offset‖ := by rfl
  rw [h_dist]
  by_cases h_a : T1.a = T2.a
  · -- Same slope: use offset difference
    have h_m : m1 = m2 := by
      simp [m1, m2, DyadicTube.slope, h_a, hδ] <;> ring
    have h_b : T1.b ≠ T2.b := by
      intro h
      have h_eq : T1 = T2 := by
        cases T1 <;> cases T2 <;> simp_all <;> tauto
      exact h_ne h_eq
    have h_db : δ ≤ |b1 - b2| := by
      have h : b1 - b2 = δ * ((T1.b : ℝ) - (T2.b : ℝ)) := by
        simp [b1, b2, DyadicTube.intercept, hδ] <;> ring
      rw [h]
      have h3 : (1 : ℝ) ≤ |(T1.b : ℝ) - (T2.b : ℝ)| := int_abs_ge_one h_b
      have h4 : |δ * ((T1.b : ℝ) - (T2.b : ℝ))| = δ * |(T1.b : ℝ) - (T2.b : ℝ)| := by
        rw [abs_mul, abs_of_pos hδ_pos]
      rw [h4]
      have h_result : δ * 1 ≤ δ * |(T1.b : ℝ) - (T2.b : ℝ)| := mul_le_mul_of_nonneg_left h3 (by positivity)
      simpa using h_result
    have h_off_eq : ‖ℓ1.offset - ℓ2.offset‖ = |b1 - b2| / Real.sqrt (1 + m1^2) := by
      have h_eq1 : ℓ1 = lineOfSlopeIntercept m1 b1 := by
        simp [ℓ1, toAffineLine] <;> rfl
      have h_eq2' : ℓ2 = lineOfSlopeIntercept m1 b2 := by
        have h_eq2 : ℓ2 = lineOfSlopeIntercept m2 b2 := by
          simp [ℓ2, toAffineLine] <;> rfl
        rw [h_eq2, h_m] <;> rfl
      rw [h_eq1, h_eq2', offset_formula m1 b1, offset_formula m1 b2]
      have h_smul : b1 • offsetVec m1 - b2 • offsetVec m1 = (b1 - b2) • offsetVec m1 := by
        exact Eq.symm (sub_smul b1 b2 (offsetVec m1))
      rw [h_smul]
      have h : ‖(b1 - b2) • offsetVec m1‖ = |b1 - b2| * ‖offsetVec m1‖ := by
        rw [norm_smul] <;> rfl
      rw [h]
      have h_norm : ‖offsetVec m1‖ ^ 2 = 1 / (1 + m1^2) := by
        simp [offsetVec, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, TubesAndSlopes.mkPlane]
        <;> field_simp <;> ring
      have h_nonneg : 0 ≤ ‖offsetVec m1‖ := by positivity
      have h_sqrt : ‖offsetVec m1‖ = 1 / Real.sqrt (1 + m1^2) := by
        have h_pos : 0 < 1 + m1^2 := by positivity
        have h_pos2 : 0 ≤ 1 / Real.sqrt (1 + m1^2) := by positivity
        have h_sq : (1 / Real.sqrt (1 + m1^2)) ^ 2 = 1 / (1 + m1^2) := by
          have h9 : Real.sqrt (1 + m1^2) ^ 2 = 1 + m1^2 := Real.sq_sqrt (by positivity)
          calc
            (1 / Real.sqrt (1 + m1^2)) ^ 2
              = 1 / (Real.sqrt (1 + m1^2) ^ 2) := by field_simp <;> ring
            _ = 1 / (1 + m1^2) := by rw [h9]
        have h5 : ‖offsetVec m1‖ ^ 2 = (1 / Real.sqrt (1 + m1^2)) ^ 2 := by
          rw [h_norm, h_sq]
        have h7 : ‖offsetVec m1‖ = 1 / Real.sqrt (1 + m1^2) ∨
            ‖offsetVec m1‖ = -(1 / Real.sqrt (1 + m1^2)) := by
          exact sq_eq_sq_iff_eq_or_eq_neg.mp h5
        rcases h7 with (h7 | h7)
        · exact h7
        · have h8 : 0 ≤ ‖offsetVec m1‖ := by positivity
          have h10 : 0 < 1 / Real.sqrt (1 + m1^2) := by positivity
          linarith
      rw [h_sqrt] <;> ring
    have h7 : Real.sqrt (1 + m1^2) ≤ 2 := by
      have h8 : 1 + m1^2 ≤ 2 := by nlinarith [abs_le.mp hm1]
      have h9 : Real.sqrt (1 + m1^2) ≤ Real.sqrt 4 := Real.sqrt_le_sqrt (by nlinarith)
      have h10 : Real.sqrt 4 = 2 := by
        rw [Real.sqrt_eq_cases] <;> norm_num
      rw [h10] at h9
      exact h9
    have h6 : δ / 2 ≤ ‖ℓ1.offset - ℓ2.offset‖ := by
      rw [h_off_eq]
      have h11 : 0 ≤ |b1 - b2| := by positivity
      have h12 : 0 < Real.sqrt (1 + m1^2) := by positivity
      calc
        |b1 - b2| / Real.sqrt (1 + m1^2) ≥ δ / Real.sqrt (1 + m1^2) := by gcongr
        _ ≥ δ / 2 := by
          exact div_le_div_of_nonneg_left (by positivity) h12 h7
    have h_nonneg_dir : 0 ≤ ‖ℓ1.1.direction.starProjection - ℓ2.1.direction.starProjection‖ :=
      norm_nonneg _
    linarith [h6, h_nonneg_dir]
  · -- Different slope: use projection difference
    have h_ma : m1 ≠ m2 := by
      intro h
      have h' : (T1.a : ℝ) = (T2.a : ℝ) := by
        apply (mul_right_inj' hδ_pos.ne').mp
        simpa [m1, m2, DyadicTube.slope] using h
      have h'' : T1.a = T2.a := by
        exact_mod_cast h'
      exact h_a h''
    have h_dm : δ ≤ |m1 - m2| := by
      have h : m1 - m2 = δ * ((T1.a : ℝ) - (T2.a : ℝ)) := by
        simp [m1, m2, DyadicTube.slope, hδ] <;> ring
      rw [h]
      have h3 : (1 : ℝ) ≤ |(T1.a : ℝ) - (T2.a : ℝ)| := int_abs_ge_one h_a
      have h4 : |δ * ((T1.a : ℝ) - (T2.a : ℝ))| = δ * |(T1.a : ℝ) - (T2.a : ℝ)| := by
        rw [abs_mul, abs_of_pos hδ_pos]
      rw [h4]
      have h_result : δ * 1 ≤ δ * |(T1.a : ℝ) - (T2.a : ℝ)| := mul_le_mul_of_nonneg_left h3 (by positivity)
      simpa using h_result
    have h_dir_eq1 : ℓ1.1.direction = Submodule.span ℝ {tubeDirV m1} := by
      rw [hℓ1]
      exact lineOfSlopeIntercept_direction T1.slope T1.intercept
    have h_dir_eq2 : ℓ2.1.direction = Submodule.span ℝ {tubeDirV m2} := by
      rw [hℓ2]
      exact lineOfSlopeIntercept_direction T2.slope T2.intercept
    have hP : ‖ℓ1.1.direction.starProjection - ℓ2.1.direction.starProjection‖ ≥ |m1 - m2| / 2 := by
      rw [h_dir_eq1, h_dir_eq2]
      exact proj_lower_bound_simple m1 m2 hm1 hm2
    have h5 : δ / 2 ≤ ‖ℓ1.1.direction.starProjection - ℓ2.1.direction.starProjection‖ := by
      calc
        δ / 2 ≤ |m1 - m2| / 2 := by gcongr
        _ ≤ ‖ℓ1.1.direction.starProjection - ℓ2.1.direction.starProjection‖ := hP
    have h_nonneg_off : 0 ≤ ‖ℓ1.offset - ℓ2.offset‖ := norm_nonneg _
    linarith [h5, h_nonneg_off]

-- ============================================================================
-- offsetVec helper lemmas
-- ============================================================================

/-- Norm of offsetVec m. -/
lemma offsetVec_norm (m : ℝ) : ‖offsetVec m‖ = 1 / Real.sqrt (1 + m^2) := by
  have h_norm2 : ‖offsetVec m‖ ^ 2 = 1 / (1 + m^2) := by
    simp [offsetVec, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, TubesAndSlopes.mkPlane]
    <;> field_simp <;> ring
  have h_nonneg : 0 ≤ ‖offsetVec m‖ := by positivity
  have h_pos2 : 0 ≤ 1 / Real.sqrt (1 + m^2) := by positivity
  have h_sq : (1 / Real.sqrt (1 + m^2)) ^ 2 = 1 / (1 + m^2) := by
    have h9 : Real.sqrt (1 + m^2) ^ 2 = 1 + m^2 := Real.sq_sqrt (by positivity)
    calc
      (1 / Real.sqrt (1 + m^2)) ^ 2
        = 1 / (Real.sqrt (1 + m^2) ^ 2) := by field_simp <;> ring
      _ = 1 / (1 + m^2) := by rw [h9]
  have h5 : ‖offsetVec m‖ ^ 2 = (1 / Real.sqrt (1 + m^2)) ^ 2 := by
    rw [h_norm2, h_sq]
  have h7 : ‖offsetVec m‖ = 1 / Real.sqrt (1 + m^2) ∨
      ‖offsetVec m‖ = -(1 / Real.sqrt (1 + m^2)) := by
    exact sq_eq_sq_iff_eq_or_eq_neg.mp h5
  rcases h7 with (h7 | h7)
  · exact h7
  · have h8 : 0 ≤ ‖offsetVec m‖ := by positivity
    have h10 : 0 < 1 / Real.sqrt (1 + m^2) := by positivity
    linarith

/-- Exact norm of offsetVec difference. -/
lemma offsetVec_diff_norm (m1 m2 : ℝ) :
    ‖offsetVec m1 - offsetVec m2‖ =
      |m1 - m2| / (Real.sqrt (1 + m1^2) * Real.sqrt (1 + m2^2)) := by
  have h_main : ‖offsetVec m1 - offsetVec m2‖ ^ 2 =
        (m1 - m2)^2 / ((1 + m1^2) * (1 + m2^2)) := by
    simp [offsetVec, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, TubesAndSlopes.mkPlane]
    <;> field_simp <;> ring
  have h_nonneg : 0 ≤ ‖offsetVec m1 - offsetVec m2‖ := by positivity
  have h : ‖offsetVec m1 - offsetVec m2‖ =
      Real.sqrt ((m1 - m2)^2 / ((1 + m1^2) * (1 + m2^2))) := by
    rw [← h_main, Real.sqrt_sq h_nonneg]
  rw [h, Real.sqrt_div (by positivity)]
  have h3 : Real.sqrt ((m1 - m2)^2) = |m1 - m2| := by rw [Real.sqrt_sq_eq_abs]
  have h4 : Real.sqrt ((1 + m1^2) * (1 + m2^2)) =
      Real.sqrt (1 + m1^2) * Real.sqrt (1 + m2^2) := by
    rw [Real.sqrt_mul] <;> positivity
  rw [h3, h4] <;> ring

/-- offsetVec is 1-Lipschitz. -/
lemma offsetVec_lipschitz (m1 m2 : ℝ) :
    ‖offsetVec m1 - offsetVec m2‖ ≤ |m1 - m2| := by
  rw [offsetVec_diff_norm m1 m2]
  have h : 1 ≤ Real.sqrt (1 + m1^2) * Real.sqrt (1 + m2^2) := by
    have h1 : 1 ≤ 1 + m1^2 := by nlinarith
    have h2 : 1 ≤ 1 + m2^2 := by nlinarith
    have h3 : Real.sqrt 1 ≤ Real.sqrt (1 + m1^2) := Real.sqrt_le_sqrt h1
    have h4 : Real.sqrt 1 ≤ Real.sqrt (1 + m2^2) := Real.sqrt_le_sqrt h2
    have h5 : Real.sqrt 1 = 1 := by norm_num
    nlinarith
  have h6 : 0 ≤ |m1 - m2| := by positivity
  have h7 : |m1 - m2| / (Real.sqrt (1 + m1^2) * Real.sqrt (1 + m2^2)) ≤ |m1 - m2| := by
    calc
      |m1 - m2| / (Real.sqrt (1 + m1^2) * Real.sqrt (1 + m2^2))
        ≤ |m1 - m2| / 1 := div_le_div_of_nonneg_left h6 (by positivity) h
      _ = |m1 - m2| := by ring
  exact h7

-- ============================================================================
-- Parameter bounds from distance bound
-- ============================================================================

/-- If two tube images are within distance 2δ, their integer parameters
    satisfy |a1-a2| ≤ 4 and |b1-b2| ≤ 19. -/
lemma tube_pair_parameter_bound {n : ℕ} (T1 T2 : DyadicTube n)
    (hm1 : |T1.slope| ≤ 1) (hm2 : |T2.slope| ≤ 1)
    (hb2 : |T2.intercept| ≤ 3)
    (h_dist : dist (toAffineLine T1) (toAffineLine T2) ≤ 2 * DiscretisedFurstenbergEstimate.dyadicDelta n) :
    |T1.a - T2.a| ≤ 4 ∧ |T1.b - T2.b| ≤ 19 := by
  set δ := DiscretisedFurstenbergEstimate.dyadicDelta n with hδ
  have hδ_pos : 0 < δ := DiscretisedFurstenbergEstimate.dyadicDelta_pos n
  set m1 := T1.slope with hm1_def
  set m2 := T2.slope with hm2_def
  set b1 := T1.intercept with hb1_def
  set b2 := T2.intercept with hb2_def
  set ℓ1 := toAffineLine T1 with hℓ1
  set ℓ2 := toAffineLine T2 with hℓ2
  have h_dir_eq1 : ℓ1.1.direction = Submodule.span ℝ {tubeDirV m1} := by
    rw [hℓ1]; exact lineOfSlopeIntercept_direction m1 b1
  have h_dir_eq2 : ℓ2.1.direction = Submodule.span ℝ {tubeDirV m2} := by
    rw [hℓ2]; exact lineOfSlopeIntercept_direction m2 b2
  have h_proj_bound : ‖ℓ1.1.direction.starProjection - ℓ2.1.direction.starProjection‖ ≥ |m1 - m2| / 2 := by
    rw [h_dir_eq1, h_dir_eq2]; exact proj_lower_bound_simple m1 m2 hm1 hm2
  have h1 : |m1 - m2| / 2 ≤ ‖ℓ1.1.direction.starProjection - ℓ2.1.direction.starProjection‖ := h_proj_bound
  have h2 : ‖ℓ1.1.direction.starProjection - ℓ2.1.direction.starProjection‖ ≤ dist ℓ1 ℓ2 := by
    have h_def : dist ℓ1 ℓ2 = ‖ℓ1.1.direction.starProjection - ℓ2.1.direction.starProjection‖ + ‖ℓ1.offset - ℓ2.offset‖ := by rfl
    rw [h_def]
    have h3 : 0 ≤ ‖ℓ1.offset - ℓ2.offset‖ := norm_nonneg _
    linarith
  have h3 : |m1 - m2| / 2 ≤ 2 * δ := by linarith [h_dist]
  have h4 : |m1 - m2| ≤ 4 * δ := by linarith
  have ha : |(T1.a : ℝ) - (T2.a : ℝ)| ≤ 4 := by
    have h5 : m1 - m2 = δ * ((T1.a : ℝ) - (T2.a : ℝ)) := by
      simp [m1, m2, DyadicTube.slope, hδ] <;> ring
    have h6 : |m1 - m2| = δ * |(T1.a : ℝ) - (T2.a : ℝ)| := by
      rw [h5, abs_mul, abs_of_pos hδ_pos]
    rw [h6] at h4
    have h7 : δ * |(T1.a : ℝ) - (T2.a : ℝ)| ≤ 4 * δ := h4
    have h8 : |(T1.a : ℝ) - (T2.a : ℝ)| ≤ 4 := by
      nlinarith [hδ_pos]
    exact_mod_cast h8
  have h_off_bound : ‖ℓ1.offset - ℓ2.offset‖ ≤ 2 * δ := by
    have h_def : dist ℓ1 ℓ2 = ‖ℓ1.1.direction.starProjection - ℓ2.1.direction.starProjection‖ + ‖ℓ1.offset - ℓ2.offset‖ := by rfl
    rw [h_def] at h_dist
    have h3 : 0 ≤ ‖ℓ1.1.direction.starProjection - ℓ2.1.direction.starProjection‖ := norm_nonneg _
    linarith
  have h_eq1 : ℓ1 = lineOfSlopeIntercept m1 b1 := by simp [ℓ1, toAffineLine] <;> rfl
  have h_eq2 : ℓ2 = lineOfSlopeIntercept m2 b2 := by simp [ℓ2, toAffineLine] <;> rfl
  have h_off1 : ℓ1.offset = b1 • offsetVec m1 := by
    rw [h_eq1]; exact offset_formula m1 b1
  have h_off2 : ℓ2.offset = b2 • offsetVec m2 := by
    rw [h_eq2]; exact offset_formula m2 b2
  rw [h_off1, h_off2] at h_off_bound
  have h_rev : ‖(b1 - b2) • offsetVec m1 + b2 • (offsetVec m1 - offsetVec m2)‖ ≤ 2 * δ := by
    have h_alg : b1 • offsetVec m1 - b2 • offsetVec m2 =
        (b1 - b2) • offsetVec m1 + b2 • (offsetVec m1 - offsetVec m2) := by
      simp [sub_smul, smul_sub] <;> abel
    rw [h_alg] at h_off_bound
    exact h_off_bound
  have h_lower : ‖(b1 - b2) • offsetVec m1‖ - ‖b2 • (offsetVec m1 - offsetVec m2)‖ ≤
      ‖(b1 - b2) • offsetVec m1 + b2 • (offsetVec m1 - offsetVec m2)‖ := by
    set x := (b1 - b2) • offsetVec m1 with hx
    set y := b2 • (offsetVec m1 - offsetVec m2) with hy
    have h : ‖x‖ ≤ ‖x + y‖ + ‖y‖ := by
      have h3 : ‖(x + y) - y‖ ≤ ‖(x + y)‖ + ‖y‖ := by exact norm_sub_le (x + y) y
      have h4 : (x + y) - y = x := by abel
      rw [h4] at h3
      exact h3
    linarith
  have h9 : ‖(b1 - b2) • offsetVec m1‖ = |b1 - b2| * ‖offsetVec m1‖ := by
    rw [norm_smul] <;> rfl
  have h10 : ‖b2 • (offsetVec m1 - offsetVec m2)‖ = |b2| * ‖offsetVec m1 - offsetVec m2‖ := by
    rw [norm_smul] <;> rfl
  have h11 : ‖offsetVec m1‖ ≥ 1 / Real.sqrt 2 := by
    rw [offsetVec_norm m1]
    have h12 : Real.sqrt (1 + m1^2) ≤ Real.sqrt 2 := by
      have h13 : 1 + m1^2 ≤ 2 := by nlinarith [abs_le.mp hm1]
      exact Real.sqrt_le_sqrt h13
    have h14 : 0 < Real.sqrt (1 + m1^2) := by positivity
    exact one_div_le_one_div_of_le h14 h12
  have h15 : ‖offsetVec m1 - offsetVec m2‖ ≤ |m1 - m2| := offsetVec_lipschitz m1 m2
  have h16 : |b2| ≤ 3 := by simpa [hb2_def, DyadicTube.intercept] using hb2
  have h17 : |b1 - b2| * (1 / Real.sqrt 2) - 3 * |m1 - m2| ≤ 2 * δ := by
    calc
      |b1 - b2| * (1 / Real.sqrt 2) - 3 * |m1 - m2|
        ≤ |b1 - b2| * ‖offsetVec m1‖ - |b2| * ‖offsetVec m1 - offsetVec m2‖ := by
          gcongr <;> linarith
      _ = ‖(b1 - b2) • offsetVec m1‖ - ‖b2 • (offsetVec m1 - offsetVec m2)‖ := by
        rw [h9, h10] <;> ring
      _ ≤ ‖(b1 - b2) • offsetVec m1 + b2 • (offsetVec m1 - offsetVec m2)‖ := h_lower
      _ ≤ 2 * δ := h_rev
  have h18 : |b1 - b2| * (1 / Real.sqrt 2) ≤ 14 * δ := by linarith [h17, h4]
  have h_sqrt2_pos : 0 < Real.sqrt 2 := by positivity
  have h19_real : |b1 - b2| ≤ 14 * Real.sqrt 2 * δ := by
    calc
      |b1 - b2|
        = (|b1 - b2| * (1 / Real.sqrt 2)) * Real.sqrt 2 := by field_simp [h_sqrt2_pos.ne'] <;> ring
      _ ≤ (14 * δ) * Real.sqrt 2 := by gcongr
      _ = 14 * Real.sqrt 2 * δ := by ring
  have h_sqrt2_lt : Real.sqrt 2 < 10 / 7 := by
    have h_pos : (0 : ℝ) < 10 / 7 := by norm_num
    have h2 : (2 : ℝ) < (10 / 7 : ℝ) ^ 2 := by norm_num
    exact (Real.sqrt_lt' h_pos).mpr h2
  have h20 : 14 * Real.sqrt 2 < 20 := by
    calc
      14 * Real.sqrt 2 < 14 * (10 / 7) := by gcongr
      _ = 20 := by norm_num
  have h21 : b1 - b2 = δ * ((T1.b : ℝ) - (T2.b : ℝ)) := by
    simp [b1, b2, DyadicTube.intercept, hδ] <;> ring
  have h22 : |b1 - b2| = δ * |(T1.b : ℝ) - (T2.b : ℝ)| := by
    rw [h21, abs_mul, abs_of_pos hδ_pos]
  rw [h22] at h19_real
  have h23 : δ * |(T1.b : ℝ) - (T2.b : ℝ)| ≤ 14 * Real.sqrt 2 * δ := h19_real
  have h24 : |(T1.b : ℝ) - (T2.b : ℝ)| ≤ 14 * Real.sqrt 2 := by
    have h_eq : (14 * Real.sqrt 2) * δ = δ * (14 * Real.sqrt 2) := by ring
    have h : δ * |(T1.b : ℝ) - (T2.b : ℝ)| ≤ δ * (14 * Real.sqrt 2) := by
      rw [h_eq] at h23
      exact h23
    have h_pos : 0 < δ := hδ_pos
    by_contra h25
    have h26 : 14 * Real.sqrt 2 < |(T1.b : ℝ) - (T2.b : ℝ)| := by linarith
    have h27 : δ * (14 * Real.sqrt 2) < δ * |(T1.b : ℝ) - (T2.b : ℝ)| := mul_lt_mul_of_pos_left h26 h_pos
    linarith
  have h25 : |(T1.b : ℝ) - (T2.b : ℝ)| < 20 := by linarith
  have h26 : |T1.b - T2.b| < 20 := by exact_mod_cast h25
  have hb_int : |T1.b - T2.b| ≤ 19 := by omega
  have ha' : |T1.a - T2.a| ≤ 4 := by exact_mod_cast ha
  exact ⟨ha', hb_int⟩

-- ============================================================================
-- Covering number lower bound
-- ============================================================================

/-- Lower bound on δ-covering number.
    Distinct tubes are δ/2-separated; each δ-ball contains at most K tube images
    by quantization, so Ncover δ ≥ card / K. -/
lemma dyadic_card_to_ncover {n : ℕ} (S : Finset (DyadicTube n))
    (hm : ∀ T ∈ S, |T.slope| ≤ 1)
    (hb : ∀ T ∈ S, |T.intercept| ≤ 3) :
    ENNReal.ofReal ((S.card : ℝ) / 400) ≤
      (Metric.externalCoveringNumber (DiscretisedFurstenbergEstimate.dyadicDelta n).toNNReal
        (toAffineLine '' (S : Set (DyadicTube n))) : ℝ≥0∞) := by
  classical
  set δ := DiscretisedFurstenbergEstimate.dyadicDelta n with hδ
  set δ_nn := δ.toNNReal with hδ_nn
  have hδ_pos : 0 < δ := DiscretisedFurstenbergEstimate.dyadicDelta_pos n
  have hδ_nn_coe : (δ_nn : ℝ) = δ := by
    simp [hδ_nn, hδ_pos.le]
  set A : Set AffineLine := toAffineLine '' (S : Set (DyadicTube n)) with hA_def
  have hA_fin : A.Finite := Set.Finite.image _ (S.finite_toSet)
  have hcover_A : Metric.IsCover δ_nn A A := by
    intro x hx
    exact ⟨x, hx, by simp [Metric.IsCover, edist_dist]⟩
  let ι := {C : Set AffineLine // Metric.IsCover δ_nn A C}
  have hι_nonempty : Nonempty ι := ⟨⟨A, hcover_A⟩⟩
  let f : ι → ℕ∞ := fun C => (C.val).encard
  have h_exists : ∃ (C : ι), f C = ⨅ (x : ι), f x := by
    exact ENat.exists_eq_iInf f
  rcases h_exists with ⟨C_min, hC_min_eq⟩
  have h_ext_def : Metric.externalCoveringNumber δ_nn A = ⨅ (C : ι), f C := by
    have h : Metric.externalCoveringNumber δ_nn A =
        ⨅ (C : Set AffineLine) (_ : Metric.IsCover δ_nn A C), C.encard := by
      rfl
    rw [h]
    have h2 : (⨅ (C : Set AffineLine) (_ : Metric.IsCover δ_nn A C), C.encard) =
        ⨅ (C : ι), f C := by
      rw [iInf_subtype]
      <;> rfl
    rw [h2]
  have h9 : f C_min = (C_min.val).encard := by rfl
  have h_encard_eq : (C_min.val).encard = Metric.externalCoveringNumber δ_nn A := by
    have h10 : f C_min = Metric.externalCoveringNumber δ_nn A := by
      rw [hC_min_eq, h_ext_def]
    rw [h9] at h10
    exact h10
  have h_fin : (C_min.val).Finite := by
    have h1 : Metric.externalCoveringNumber δ_nn A ≤ A.encard :=
      Metric.externalCoveringNumber_le_encard_self A
    rw [←h_encard_eq] at h1
    exact Set.encard_lt_top_iff.mp (h1.trans_lt (hA_fin.encard_lt_top))
  let C_finset : Finset AffineLine := h_fin.toFinset
  have hC_coe : (C_finset : Set AffineLine) = C_min.val := by
    exact Set.Finite.coe_toFinset h_fin
  have h_edist_dist : ∀ (x c : AffineLine), edist x c ≤ (δ_nn : ENNReal) ↔ dist x c ≤ δ := by
    intro x c
    simp [edist_dist, hδ_nn_coe]
  have h_cover : ∀ (x : AffineLine), x ∈ A → ∃ (c : AffineLine), c ∈ C_finset ∧ x ∈ Metric.closedBall c δ_nn := by
    intro x hx
    have h2 := C_min.property hx
    rcases h2 with ⟨c, hc, hball⟩
    have hball' : x ∈ Metric.closedBall c δ_nn := by
      simpa [Metric.mem_closedBall, (h_edist_dist x c)] using hball
    have hc' : c ∈ C_finset := by
      have h1 : c ∈ (C_finset : Set AffineLine) := by
        rw [hC_coe] <;> exact hc
      simpa using h1
    exact ⟨c, hc', hball'⟩
  let S_c : AffineLine → Finset (DyadicTube n) := fun c =>
    S.filter (fun T => toAffineLine T ∈ Metric.closedBall c δ_nn)
  have h_union : S ⊆ Finset.biUnion C_finset S_c := by
    intro T hT
    have hT_in_A : toAffineLine T ∈ A := by
      exact ⟨T, hT, rfl⟩
    rcases h_cover (toAffineLine T) hT_in_A with ⟨c, hc, hball⟩
    have h3 : T ∈ S_c c := by
      simp only [S_c, Finset.mem_filter]
      exact ⟨hT, hball⟩
    exact Finset.mem_biUnion.mpr ⟨c, hc, h3⟩
  have h_ball_bound : ∀ (c : AffineLine), (S_c c).card ≤ 400 := by
    intro c
    by_cases h_empty : (S_c c).Nonempty
    · rcases h_empty with ⟨T0, hT0⟩
      have hT0_in_S : T0 ∈ S := (Finset.mem_filter.mp hT0).1
      have hT0_ball : toAffineLine T0 ∈ Metric.closedBall c δ_nn :=
        (Finset.mem_filter.mp hT0).2
      have h_inj : Set.InjOn (fun (T : DyadicTube n) => (T.a, T.b)) (S_c c : Set _) := by
        intro T1 _ T2 _ h
        cases T1 <;> cases T2 <;> simp_all <;> tauto
      have h_bound : ∀ T ∈ S_c c, |T.a - T0.a| ≤ 4 ∧ |T.b - T0.b| ≤ 19 := by
        intro T hT
        have hT_in_S : T ∈ S := (Finset.mem_filter.mp hT).1
        have hT_ball : toAffineLine T ∈ Metric.closedBall c δ_nn :=
          (Finset.mem_filter.mp hT).2
        have h_dist1 : dist (toAffineLine T) c ≤ δ := by
          simpa [Metric.mem_closedBall, hδ_nn_coe] using hT_ball
        have h_dist2 : dist (toAffineLine T0) c ≤ δ := by
          simpa [Metric.mem_closedBall, hδ_nn_coe] using hT0_ball
        have h_dist : dist (toAffineLine T) (toAffineLine T0) ≤ 2 * δ := by
          calc
            dist (toAffineLine T) (toAffineLine T0)
              ≤ dist (toAffineLine T) c + dist c (toAffineLine T0) := dist_triangle _ _ _
            _ = dist (toAffineLine T) c + dist (toAffineLine T0) c := by
              have h_eq : dist c (toAffineLine T0) = dist (toAffineLine T0) c := dist_comm _ _
              rw [h_eq]
            _ ≤ δ + δ := by gcongr
            _ = 2 * δ := by ring
        exact tube_pair_parameter_bound T T0 (hm T hT_in_S) (hm T0 hT0_in_S)
          (hb T0 hT0_in_S) h_dist
      let R_a := Finset.Icc (T0.a - 4) (T0.a + 4)
      let R_b := Finset.Icc (T0.b - 19) (T0.b + 19)
      have h1 : ∀ T ∈ S_c c, T.a ∈ R_a ∧ T.b ∈ R_b := by
        intro T hT
        have h2 : |T.a - T0.a| ≤ 4 ∧ |T.b - T0.b| ≤ 19 := h_bound T hT
        have h2a : |T.a - T0.a| ≤ 4 := h2.1
        have h2b : |T.b - T0.b| ≤ 19 := h2.2
        have ha_icc : T0.a - 4 ≤ T.a ∧ T.a ≤ T0.a + 4 := by
          have h : |T.a - T0.a| ≤ 4 := h2a
          have h' : -4 ≤ T.a - T0.a ∧ T.a - T0.a ≤ 4 := by
            exact abs_le.mp h2a
          exact ⟨by linarith, by linarith⟩
        have hb_icc : T0.b - 19 ≤ T.b ∧ T.b ≤ T0.b + 19 := by
          have h : |T.b - T0.b| ≤ 19 := h2b
          have h' : -19 ≤ T.b - T0.b ∧ T.b - T0.b ≤ 19 := by exact abs_le.mp h2b
          exact ⟨by linarith, by linarith⟩
        constructor
        · simp only [R_a, Finset.mem_Icc]; exact ha_icc
        · simp only [R_b, Finset.mem_Icc]; exact hb_icc
      let g : DyadicTube n → ℤ × ℤ := fun T => (T.a, T.b)
      have h_image : (S_c c).image g ⊆ R_a ×ˢ R_b := by
        intro p hp
        rcases Finset.mem_image.mp hp with ⟨T, hT, rfl⟩
        have h4 := h1 T hT
        simp only [Finset.mem_product]
        exact ⟨h4.1, h4.2⟩
      have h_inj : Set.InjOn g (S_c c : Set _) := by
        intro T1 _ T2 _ h
        have h' : T1.a = T2.a ∧ T1.b = T2.b := by
          simpa [g, Prod.ext_iff] using h
        cases T1 <;> cases T2 <;> simp_all (config := {decide := true}) <;> aesop
      have h_card_img : ((S_c c).image g).card = (S_c c).card :=
        Finset.card_image_of_injOn h_inj
      have h3 : (S_c c).card ≤ (R_a ×ˢ R_b).card := by
        rw [←h_card_img]
        exact Finset.card_le_card h_image
      have hRa : R_a.card = 9 := by
        rw [Int.card_Icc]
        have h' : (T0.a + 4) + 1 - (T0.a - 4) = 9 := by omega
        rw [h']
        have h'' : Int.toNat 9 = 9 := by decide
        rw [h'']
      have hRb : R_b.card = 39 := by
        rw [Int.card_Icc]
        have h' : (T0.b + 19) + 1 - (T0.b - 19) = 39 := by omega
        rw [h']
        have h'' : Int.toNat 39 = 39 := by decide
        rw [h'']
      have h4 : (R_a ×ˢ R_b).card = 9 * 39 := by
        rw [Finset.card_product, hRa, hRb] <;> norm_num
      rw [h4] at h3
      linarith
    · simp only [Finset.not_nonempty_iff_eq_empty] at h_empty
      rw [h_empty] <;> norm_num
  have h_card : S.card ≤ 400 * C_finset.card := by
    calc
      S.card ≤ (Finset.biUnion C_finset S_c).card := Finset.card_le_card h_union
      _ ≤ ∑ c ∈ C_finset, (S_c c).card := Finset.card_biUnion_le
      _ ≤ ∑ c ∈ C_finset, 400 := by gcongr <;> exact h_ball_bound c
      _ = 400 * C_finset.card := by simp [Finset.sum_const] <;> ring
  have h_ncard_eq : (C_finset.card : ℕ∞) = Metric.externalCoveringNumber δ_nn A := by
    have h5 : (C_finset.card : ℕ∞) = (C_min.val).encard := by
      have h6 : C_finset.card = (C_min.val).ncard := by
        exact Eq.symm (Set.ncard_eq_toFinset_card (C_min.val) h_fin)
      have h7 : ((C_min.val).ncard : ℕ∞) = (C_min.val).encard := by
        letI : Fintype (C_min.val) := Set.Finite.fintype h_fin
        have h_lemma : ((C_min.val).ncard : ℕ∞) = (C_min.val).encard := by
          exact Set.coe_ncard_eq_encard (s := C_min.val)
        exact h_lemma
      rw [h6, h7]
    rw [h5, h_encard_eq]
  have h_card' : (S.card : ℕ∞) ≤ 400 * (C_finset.card : ℕ∞) := by exact_mod_cast h_card
  rw [h_ncard_eq] at h_card'
  have h_main : (S.card : ℕ∞) ≤ 400 * Metric.externalCoveringNumber δ_nn A := h_card'
  set m : ℕ∞ := Metric.externalCoveringNumber δ_nn A with hm_def
  have h_m_lt : m < ⊤ := by
    exact (Metric.externalCoveringNumber_le_encard_self A).trans_lt hA_fin.encard_lt_top
  have h_m_ne_top : m ≠ ⊤ := h_m_lt.ne
  cases h_cases : m with
  | top =>
    exfalso
    exact h_m_ne_top h_cases
  | coe k =>
    have hmk : m = ↑k := h_cases
    have h_ineq : S.card ≤ 400 * k := by
      rw [hmk] at h_main
      exact_mod_cast h_main
    have h_real : (S.card : ℝ) / 400 ≤ (k : ℝ) := by
      have h : (S.card : ℝ) ≤ 400 * (k : ℝ) := by exact_mod_cast h_ineq
      linarith
    have h_goal : ENNReal.ofReal ((S.card : ℝ) / 400) ≤ (k : ENNReal) := by
      have h_ofReal_k : ENNReal.ofReal ((k : ℝ)) = (k : ENNReal) := by
        simp
      have h : ENNReal.ofReal ((S.card : ℝ) / 400) ≤ ENNReal.ofReal ((k : ℝ)) :=
        ENNReal.ofReal_le_ofReal h_real
      rw [h_ofReal_k] at h
      exact h
    exact h_goal

end DyadicCardToNcover
