import MyLeanRepo.Kakeya.CV.DyadicPolynomialBadSetDecomposition
import MyLeanRepo.Kakeya.CV.Targets.EllipsoidTranslatePacking.VolumeScaling

/-!
# Finite dyadic decomposition of polynomial bad sets

The concrete visibility body always has positive volume and lies in the unit
ball.  Its visibility therefore has a uniform positive lower bound, so only
finitely many dyadic levels can meet a fixed bad set.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal Real

namespace Kakeya.CV

lemma concreteMollifiedVisibility_unitBall_lower
    {k : ℕ} {P : PolynomialParameterization k}
    {ε : ℝ} {x : CoefficientSpace P.dim} {U : Set (Point 3)}
    (hBody : JohnEllipsoid.IsConvexBody
      (concreteMollifiedVisibilityBody P ε x U)) :
    Real.rpow (volume (unitBall 3)).toReal (-1 / 3 : ℝ) ≤
      concreteMollifiedVisibility P ε x U := by
  let K := concreteMollifiedVisibilityBody P ε x U
  have hK_sub : K ⊆ unitBall 3 := fun _ hx => hx.1
  have hvol_le : volume K ≤ volume (unitBall 3) := measure_mono hK_sub
  have hK_pos : 0 < volume K :=
    Measure.measure_pos_of_nonempty_interior volume hBody.2.2
  have hK_top : volume K ≠ ⊤ :=
    ne_top_of_le_ne_top volume_unitBall_lt_top.ne hvol_le
  have hB_top : volume (unitBall 3) ≠ ⊤ := volume_unitBall_lt_top.ne
  have hK_real_pos : 0 < (volume K).toReal :=
    ENNReal.toReal_pos hK_pos.ne' hK_top
  have hreal_le : (volume K).toReal ≤ (volume (unitBall 3)).toReal :=
    ENNReal.toReal_mono hB_top hvol_le
  exact Real.rpow_le_rpow_of_nonpos hK_real_pos hreal_le (by norm_num)

lemma concretePolynomialBadSet_zero
    (hBody : ConcreteMollifiedVisibilityStatement)
    {k : ℕ} (P : PolynomialParameterization k)
    (ε : ℝ) (c : Point 3) (hε : 0 < ε) :
    concretePolynomialBadSet P ε (unitCube c) 0 = ∅ := by
  ext x
  simp only [concretePolynomialBadSet, Set.mem_setOf_eq, Set.mem_empty_iff_false,
    iff_false]
  have hbody_x := hBody k P (unitCube c) c ε x
    (unitCube_measurableSet c) (unitCube_subset_closedBall c) hε
  have hball_real_pos : 0 < (volume (unitBall 3)).toReal :=
    ENNReal.toReal_pos volume_unitBall_pos.ne' volume_unitBall_lt_top.ne
  have hlower :
      Real.rpow (volume (unitBall 3)).toReal (-1 / 3 : ℝ) ≤
        concreteMollifiedVisibility P ε x (unitCube c) :=
    concreteMollifiedVisibility_unitBall_lower hbody_x.1
  exact not_le_of_gt
    ((Real.rpow_pos_of_pos hball_real_pos _).trans_le hlower)

lemma exists_dyadic_level_below (M B : ℝ) (hB : 0 < B) :
    ∃ n : ℕ, Real.rpow 2 (-(n : ℝ)) * M < B := by
  obtain ⟨n, hn⟩ :=
    pow_unbounded_of_one_lt (M / B) (show (1 : ℝ) < 2 by norm_num)
  refine ⟨n, ?_⟩
  have hpow : Real.rpow 2 (-(n : ℝ)) = ((2 : ℝ) ^ n)⁻¹ := by
    calc
      Real.rpow 2 (-(n : ℝ)) = (Real.rpow 2 (n : ℝ))⁻¹ :=
        Real.rpow_neg (by norm_num) (n : ℝ)
      _ = ((2 : ℝ) ^ n)⁻¹ := by
        congr 1
        exact Real.rpow_natCast 2 n
  rw [hpow, inv_mul_eq_div]
  apply (div_lt_iff₀ (pow_pos (by norm_num) n)).2
  simpa [mul_comm] using (div_lt_iff₀ hB).mp hn

lemma dyadic_rpow_antitone {n r : ℕ} (hnr : n ≤ r) :
    Real.rpow 2 (-(r : ℝ)) ≤ Real.rpow 2 (-(n : ℝ)) := by
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  exact neg_le_neg (by exact_mod_cast hnr)

theorem finite_dyadic_polynomial_badSet_decomposition
    (hBody : ConcreteMollifiedVisibilityStatement)
    (hDyadic : DyadicPolynomialBadSetDecompositionStatement) :
    FiniteDyadicPolynomialBadSetDecompositionStatement := by
  rcases hDyadic with
    ⟨α, N, net, colour, hα, hN, hcentered, hseparation, hDyadic⟩
  refine ⟨α, N, net, colour, hα, hN, hcentered, hseparation, ?_⟩
  intro k P ε c M hε hM
  rcases hDyadic k P ε c M hε hM with
    ⟨selected, h_even, h_close, h_decomposition⟩
  let B : ℝ := Real.rpow (volume (unitBall 3)).toReal (-1 / 3 : ℝ)
  have hball_real_pos : 0 < (volume (unitBall 3)).toReal :=
    ENNReal.toReal_pos volume_unitBall_pos.ne' volume_unitBall_lt_top.ne
  have hB_pos : 0 < B := Real.rpow_pos_of_pos hball_real_pos _
  obtain ⟨levels, hlevels⟩ := exists_dyadic_level_below M B hB_pos
  refine ⟨selected, levels, h_even, h_close, ?_⟩
  rw [h_decomposition]
  ext y
  simp only [Set.mem_iUnion, Set.mem_setOf_eq]
  constructor
  · rintro ⟨r, θ, hr, hθ⟩
    have hr_lt : r < levels := by
      by_contra hnot
      have hlevels_le : levels ≤ r := Nat.le_of_not_gt hnot
      have hpow_le :
          Real.rpow 2 (-(r : ℝ)) ≤ Real.rpow 2 (-(levels : ℝ)) :=
        dyadic_rpow_antitone hlevels_le
      have hvis_upper :
          concreteMollifiedVisibility P ε y (unitCube c) <
            B := by
        calc
          concreteMollifiedVisibility P ε y (unitCube c)
              ≤ Real.rpow 2 (-(r : ℝ)) * M := hr.2
          _ ≤ Real.rpow 2 (-(levels : ℝ)) * M := by
            exact mul_le_mul_of_nonneg_right hpow_le hM.le
          _ < B := hlevels
      have hbody_y := hBody k P (unitCube c) c ε y
        (unitCube_measurableSet c) (unitCube_subset_closedBall c) hε
      have hvis_lower :
          B ≤ concreteMollifiedVisibility P ε y (unitCube c) :=
        concreteMollifiedVisibility_unitBall_lower hbody_y.1
      exact (not_lt_of_ge hvis_lower) hvis_upper
    exact ⟨⟨r, hr_lt⟩, θ, hr, hθ⟩
  · rintro ⟨r, θ, hr, hθ⟩
    exact ⟨(r : ℕ), θ, hr, hθ⟩

end Kakeya.CV
