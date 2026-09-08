import MyLeanRepo.Kakeya.Streamlined.UniformRefinement.EndpointCovers

/-!
# Arithmetic of the distinguished paper scale grid

These are the numerical and finite-order helpers used by the Section 7
stopping-time argument.  They contain no geometric or concentration
assumptions.
-/

noncomputable section

namespace Kakeya.Streamlined

/-- The number of paper-scale intervals is always positive. -/
lemma uniformScaleSteps_pos (delta : ℝ) :
    0 < uniformScaleSteps delta := by
  simp [uniformScaleSteps]

/--
For `0 < delta ≤ 1`, the clamps in `uniformScale` are inactive: every grid
scale is exactly `delta^(k/M)`.
-/
lemma uniformScale_eq_rpow
    {delta : ℝ} (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    (k : UniformScaleIndex delta) :
    (uniformScale delta hdelta_one k).1 =
      delta ^ ((k : ℝ) / (uniformScaleSteps delta : ℝ)) := by
  let M := uniformScaleSteps delta
  have hM_nat : 0 < M := by
    simpa [M] using uniformScaleSteps_pos delta
  have hM : (0 : ℝ) < M := by
    exact_mod_cast hM_nat
  have hk_nat : (k : ℕ) ≤ M := by
    omega
  have hk : (k : ℝ) ≤ M := by
    exact_mod_cast hk_nat
  have hexp_nonneg :
      0 ≤ (k : ℝ) / (M : ℝ) := by
    positivity
  have hexp_one :
      (k : ℝ) / (M : ℝ) ≤ 1 := by
    apply (div_le_one hM).2
    exact hk
  have hraw_lower :
      delta ≤ delta ^ ((k : ℝ) / (M : ℝ)) := by
    have h :=
      Real.rpow_le_rpow_of_exponent_ge hdelta hdelta_one hexp_one
    simpa using h
  have hraw_upper :
      delta ^ ((k : ℝ) / (M : ℝ)) ≤ 1 := by
    have h :=
      Real.rpow_le_rpow_of_exponent_ge hdelta hdelta_one hexp_nonneg
    simpa using h
  rw [uniformScale]
  change max delta
      (min 1 (delta ^ ((k : ℝ) / (M : ℝ)))) =
    delta ^ ((k : ℝ) / (M : ℝ))
  rw [min_eq_right hraw_upper, max_eq_right hraw_lower]

/-- Exact ratio of any two distinguished paper scales. -/
lemma uniformScale_div_uniformScale
    {delta : ℝ} (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    (k l : UniformScaleIndex delta) :
    (uniformScale delta hdelta_one k).1 /
        (uniformScale delta hdelta_one l).1 =
      delta ^
        (((k : ℝ) - (l : ℝ)) /
          (uniformScaleSteps delta : ℝ)) := by
  rw [uniformScale_eq_rpow hdelta hdelta_one,
    uniformScale_eq_rpow hdelta hdelta_one]
  rw [← Real.rpow_sub hdelta]
  congr 1
  have hM :
      (uniformScaleSteps delta : ℝ) ≠ 0 := by
    exact_mod_cast (uniformScaleSteps_pos delta).ne'
  field_simp [hM]

/--
Every adjacent coarse-to-fine grid ratio is the same:
`delta^(-1/M)`.
-/
lemma uniformScale_adjacent_ratio
    {delta : ℝ} (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    (k : Fin (uniformScaleSteps delta)) :
    (uniformScale delta hdelta_one k.castSucc).1 /
        (uniformScale delta hdelta_one k.succ).1 =
      delta ^ (-(1 / (uniformScaleSteps delta : ℝ))) := by
  rw [uniformScale_div_uniformScale hdelta hdelta_one]
  congr 1
  have hM :
      (uniformScaleSteps delta : ℝ) ≠ 0 := by
    exact_mod_cast (uniformScaleSteps_pos delta).ne'
  have hcastSucc : (k.castSucc : ℝ) = (k : ℝ) := by
    simp
  have hsucc : (k.succ : ℝ) = (k : ℝ) + 1 := by
    norm_num
  rw [hcastSucc, hsucc]
  field_simp [hM]
  ring

/--
A finite Boolean sequence that is true at the first index and false at the
last index has an adjacent true-to-false transition.
-/
lemma exists_adjacent_true_false :
    ∀ n : ℕ,
      ∀ P : Fin (n + 1) → Prop,
        P 0 →
        ¬ P (Fin.last n) →
        ∃ k : Fin n, P k.castSucc ∧ ¬ P k.succ := by
  intro n
  induction n with
  | zero =>
      intro P hzero hlast
      exfalso
      apply hlast
      simpa using hzero
  | succ n ih =>
      intro P hzero hlast
      let one : Fin (n + 2) := ⟨1, by omega⟩
      by_cases hone : P one
      · let Q : Fin (n + 1) → Prop := fun i => P i.succ
        have hQzero : Q 0 := by
          simpa [Q, one] using hone
        have hQlast : ¬ Q (Fin.last n) := by
          simpa [Q] using hlast
        rcases ih Q hQzero hQlast with
          ⟨k, hk_good, hk_bad⟩
        refine ⟨k.succ, ?_, ?_⟩
        · simpa [Q] using hk_good
        · simpa [Q] using hk_bad
      · let k : Fin (n + 1) := ⟨0, by omega⟩
        refine ⟨k, ?_, ?_⟩
        · simpa [k] using hzero
        · simpa [k, one] using hone

end Kakeya.Streamlined
