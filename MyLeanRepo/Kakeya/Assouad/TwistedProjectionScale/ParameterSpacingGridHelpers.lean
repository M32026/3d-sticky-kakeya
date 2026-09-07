import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.CubicGridPartitionTree
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.TubeParameterGridParameterSelectionHelpers

/-!
# Grid parameters for the spacing lemma

The three-dimensional cubic tree uses the same large-base selection as the
closed four-parameter tree, with a smaller child bound.
-/

noncomputable section

namespace Kakeya.Assouad

/--
Choose a base for which one level of three-dimensional OS branching costs at
most `base^eta`.
-/
lemma exists_large_base3
    (eta : ℝ)
    (heta : 0 < eta) :
    ∃ base : ℕ,
      3 ≤ base ∧
        (2 *
            (Nat.log 2 ((base + 1) ^ 3) + 1) :
          ℝ) ≤
          Real.rpow (base : ℝ) eta := by
  rcases exists_large_base4 eta heta with
    ⟨base, hbase, hbase4⟩
  refine ⟨base, hbase, ?_⟩
  have hpow :
      (base + 1) ^ 3 ≤ (base + 1) ^ 4 := by
    have hone : 1 ≤ base + 1 := by omega
    exact pow_le_pow_right₀ hone (by omega)
  have hlog :
      Nat.log 2 ((base + 1) ^ 3) ≤
        Nat.log 2 ((base + 1) ^ 4) :=
    Nat.log_mono_right hpow
  calc
    (2 * (Nat.log 2 ((base + 1) ^ 3) + 1) : ℝ)
        ≤
          (2 * (Nat.log 2 ((base + 1) ^ 4) + 1) :
            ℝ) := by
          exact_mod_cast
            Nat.mul_le_mul_left 2
              (Nat.add_le_add_right hlog 1)
    _ ≤ Real.rpow (base : ℝ) eta := hbase4

/--
Choose the first cubic-grid depth whose cell diameter is below `delta`.

Minimality keeps the terminal mesh comparable to `delta`:
`delta / (3 * base) ≤ base⁻levels < delta / 3`.
-/
lemma exists_atomic_cubic_levels
    (base : ℕ)
    (hbase : 3 ≤ base)
    (delta : ℝ)
    (hdelta : 0 < delta)
    (hdelta_one : delta < 1) :
    ∃ levels : ℕ,
      0 < levels ∧
        delta / (3 * (base : ℝ)) ≤
          (base ^ levels : ℝ)⁻¹ ∧
        3 * (base ^ levels : ℝ)⁻¹ < delta := by
  let predicate : ℕ → Prop := fun level =>
    3 < delta * (base ^ level : ℝ)
  have hbase_growth :
      ∀ level : ℕ,
        (level : ℝ) ≤ (base ^ level : ℝ) := by
    intro level
    have htwo : level ≤ 2 ^ level := by
      induction level with
      | zero => norm_num
      | succ level ih =>
          have hone : 1 ≤ 2 ^ level :=
            Nat.one_le_two_pow
          calc
            level + 1 ≤ 2 ^ level + 2 ^ level :=
              add_le_add ih hone
            _ = 2 ^ (level + 1) := by
              rw [pow_succ]
              ring
    have hpow :
        2 ^ level ≤ base ^ level :=
      Nat.pow_le_pow_left (by omega) level
    exact_mod_cast htwo.trans hpow
  have hexists : ∃ level, predicate level := by
    obtain ⟨level, hlevel⟩ :=
      exists_nat_gt (3 / delta)
    refine ⟨level, ?_⟩
    have hlevel_pow :
        3 / delta < (base ^ level : ℝ) :=
      hlevel.trans_le (hbase_growth level)
    have hmul :=
      mul_lt_mul_of_pos_left hlevel_pow hdelta
    have hcancel : delta * (3 / delta) = 3 := by
      field_simp [hdelta.ne']
    nlinarith
  let levels := Nat.find hexists
  have hlevels_spec : predicate levels :=
    Nat.find_spec hexists
  have hlevels_pos : 0 < levels := by
    by_contra hnot
    have hzero : levels = 0 := by omega
    rw [hzero] at hlevels_spec
    dsimp only [predicate] at hlevels_spec
    norm_num at hlevels_spec
    linarith
  have hprevious :
      ¬predicate (levels - 1) :=
    Nat.find_min hexists (by omega)
  have hprevious_bound :
      delta * (base ^ (levels - 1) : ℝ) ≤ 3 := by
    exact le_of_not_gt hprevious
  have hpow_pos :
      0 < (base ^ levels : ℝ) := by positivity
  have hmesh_upper :
      3 * (base ^ levels : ℝ)⁻¹ < delta := by
    have hpositive :
        3 < delta * (base ^ levels : ℝ) :=
      hlevels_spec
    calc
      3 * (base ^ levels : ℝ)⁻¹
          < (delta * (base ^ levels : ℝ)) *
              (base ^ levels : ℝ)⁻¹ := by
            gcongr
      _ = delta := by
            rw [mul_assoc,
              mul_inv_cancel₀ hpow_pos.ne', mul_one]
  have hpow_factor :
      (base ^ levels : ℝ) =
        (base : ℝ) *
          (base ^ (levels - 1) : ℝ) := by
    rcases
      Nat.exists_eq_succ_of_ne_zero hlevels_pos.ne'
      with ⟨previous, hlevels_eq⟩
    rw [hlevels_eq]
    simp [pow_succ, mul_comm]
  have hterminal_product :
      delta * (base ^ levels : ℝ) ≤
        3 * (base : ℝ) := by
    rw [hpow_factor]
    calc
      delta *
            ((base : ℝ) *
              (base ^ (levels - 1) : ℝ))
          =
            (base : ℝ) *
              (delta *
                (base ^ (levels - 1) : ℝ)) := by
              ring
      _ ≤ (base : ℝ) * 3 := by
            gcongr
      _ = 3 * (base : ℝ) := by ring
  have hdenom_pos :
      0 < 3 * (base : ℝ) := by positivity
  have hmesh_lower :
      delta / (3 * (base : ℝ)) ≤
        (base ^ levels : ℝ)⁻¹ := by
    have hdiv :=
      (div_le_iff₀ hdenom_pos).2
        (show
          delta ≤
            (base ^ levels : ℝ)⁻¹ *
              (3 * (base : ℝ)) by
          calc
            delta =
                (delta * (base ^ levels : ℝ)) *
                  (base ^ levels : ℝ)⁻¹ := by
                    rw [mul_assoc,
                      mul_inv_cancel₀ hpow_pos.ne', mul_one]
            _ ≤ (3 * (base : ℝ)) *
                  (base ^ levels : ℝ)⁻¹ := by
                    gcongr
            _ =
                (base ^ levels : ℝ)⁻¹ *
                  (3 * (base : ℝ)) := by ring)
    exact hdiv
  exact
    ⟨levels, hlevels_pos,
      hmesh_lower, hmesh_upper⟩

end Kakeya.Assouad
