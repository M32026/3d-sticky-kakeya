import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.BranchingProfile
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.SuffixBranchingProfile

/-!
# Cumulative cubic-grid local dimension

The weighted local-dimension profile telescopes at every intermediate level,
not only at the terminal level.
-/

noncomputable section

namespace Kakeya.Assouad

theorem localDim_suffixProfileCumulative
    {base levels : ℕ}
    {A : DiscreteSet 3}
    (hbase : 2 ≤ base)
    (hA : A.Nonempty)
    (j : Fin (levels + 1)) :
    suffixProfileCumulative
        (scaleWeight levels)
        (fun i : Fin levels =>
          localDim base A i)
        j =
      Real.log
          ((cellCount base A j.val : ℝ) /
            (cellCount base A 0 : ℝ)) /
        ((levels : ℝ) * Real.log base) := by
  have hlevels_or_zero : levels = 0 ∨ 0 < levels := by omega
  rcases hlevels_or_zero with rfl | hlevels
  · have hj : j = 0 := by
      apply Fin.ext
      omega
    subst j
    rw [suffixProfileCumulative_zero]
    simp
  have hlevels_real : (0 : ℝ) < levels := by
    exact_mod_cast hlevels
  have hlog_base : 0 < Real.log (base : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < base by omega))
  let g : ℕ → ℝ := fun k =>
    Real.log
      ((cellCount base A k : ℝ) /
        (cellCount base A 0 : ℝ))
  have hcell_pos :
      ∀ k, 0 < (cellCount base A k : ℝ) := by
    intro k
    exact_mod_cast
      (cubicGridPartition_nonempty
        (base := base) (level := k) hA).card_pos
  have hstep :
      ∀ k : ℕ,
        g (k + 1) - g k =
          Real.log
              ((cellCount base A (k + 1) : ℝ) /
                (cellCount base A k : ℝ)) := by
    intro k
    dsimp only [g]
    have h0 := hcell_pos 0
    have hk := hcell_pos k
    have hks := hcell_pos (k + 1)
    rw [Real.log_div (by positivity) (by positivity),
      Real.log_div (by positivity) (by positivity),
      Real.log_div (by positivity) (by positivity)]
    ring
  have hg0 : g 0 = 0 := by
    dsimp only [g]
    have h0 := hcell_pos 0
    rw [div_self h0.ne', Real.log_one]
  have hclosed :
      ∀ j : Fin (levels + 1),
        suffixProfileCumulative
            (scaleWeight levels)
            (fun i : Fin levels =>
              localDim base A i)
            j =
          g j.val /
            ((levels : ℝ) * Real.log base) := by
    intro q
    induction q using Fin.induction with
    | zero =>
        rw [suffixProfileCumulative_zero]
        simpa using congrArg
          (fun value : ℝ =>
            value / ((levels : ℝ) * Real.log base))
          hg0.symm
    | succ i ih =>
        rw [suffixProfileCumulative_succ, ih]
        have hweight :
            scaleWeight levels i.succ -
                scaleWeight levels i.castSucc =
              1 / (levels : ℝ) := by
          simp [scaleWeight]
          field_simp [hlevels_real.ne']
          ring
        rw [hweight]
        change
          g i.val /
                ((levels : ℝ) * Real.log base) +
              localDim base A i.val *
                (1 / (levels : ℝ)) =
            g (i.val + 1) /
              ((levels : ℝ) * Real.log base)
        rw [localDim, ← hstep i.val]
        field_simp [hlevels_real.ne', hlog_base.ne']
        ring
  exact hclosed j

theorem localDim_suffix_cellCount_growth
    {base levels : ℕ}
    {A : DiscreteSet 3}
    (hbase : 2 ≤ base)
    (hlevels : 0 < levels)
    (hA : A.Nonempty)
    (d : ℝ)
    (k j : Fin (levels + 1))
    (hkj : k.val ≤ j.val)
    (hsuffix :
      d * (scaleWeight levels j - scaleWeight levels k) ≤
        suffixProfileCumulative
            (scaleWeight levels)
            (fun i : Fin levels =>
              localDim base A i)
            j -
          suffixProfileCumulative
            (scaleWeight levels)
            (fun i : Fin levels =>
              localDim base A i)
            k) :
    Real.rpow (base : ℝ)
          (((j.val - k.val : ℕ) : ℝ) * d) *
        (cellCount base A k.val : ℝ) ≤
      (cellCount base A j.val : ℝ) := by
  have hlevels_real : (0 : ℝ) < levels := by
    exact_mod_cast hlevels
  have hbase_real : (1 : ℝ) < base := by
    exact_mod_cast (show 1 < base by omega)
  have hlog_base : 0 < Real.log (base : ℝ) :=
    Real.log_pos hbase_real
  have hcell_pos :
      ∀ m, 0 < (cellCount base A m : ℝ) := by
    intro m
    exact_mod_cast
      (cubicGridPartition_nonempty
        (base := base) (level := m) hA).card_pos
  rw [localDim_suffixProfileCumulative hbase hA j,
    localDim_suffixProfileCumulative hbase hA k] at hsuffix
  have hscale :
      scaleWeight levels j - scaleWeight levels k =
        (((j.val - k.val : ℕ) : ℝ) /
          (levels : ℝ)) := by
    simp only [scaleWeight]
    have hcast :
        (((j.val - k.val : ℕ) : ℝ)) =
          (j.val : ℝ) - (k.val : ℝ) := by
      exact Nat.cast_sub hkj
    rw [hcast]
    ring
  have hlog_ratio :
      Real.log
            ((cellCount base A j.val : ℝ) /
              (cellCount base A 0 : ℝ)) -
          Real.log
            ((cellCount base A k.val : ℝ) /
              (cellCount base A 0 : ℝ)) =
        Real.log
          ((cellCount base A j.val : ℝ) /
            (cellCount base A k.val : ℝ)) := by
    have hj := hcell_pos j.val
    have hk := hcell_pos k.val
    have h0 := hcell_pos 0
    rw [Real.log_div hj.ne' h0.ne',
      Real.log_div hk.ne' h0.ne',
      Real.log_div hj.ne' hk.ne']
    ring
  have hcumulative :
      Real.log
              ((cellCount base A j.val : ℝ) /
                (cellCount base A 0 : ℝ)) /
            ((levels : ℝ) * Real.log base) -
          Real.log
              ((cellCount base A k.val : ℝ) /
                (cellCount base A 0 : ℝ)) /
            ((levels : ℝ) * Real.log base) =
        Real.log
              ((cellCount base A j.val : ℝ) /
                (cellCount base A k.val : ℝ)) /
            ((levels : ℝ) * Real.log base) := by
    rw [← sub_div, hlog_ratio]
  rw [hscale, hcumulative] at hsuffix
  let exponent : ℝ :=
    ((j.val - k.val : ℕ) : ℝ) * d
  have hscaled :
      exponent * Real.log base ≤
        Real.log
          ((cellCount base A j.val : ℝ) /
            (cellCount base A k.val : ℝ)) := by
    have hdenom :
        0 < (levels : ℝ) * Real.log base := by
      positivity
    have hleft :
        d *
            (((j.val - k.val : ℕ) : ℝ) /
              (levels : ℝ)) =
          (exponent * Real.log base) /
            ((levels : ℝ) * Real.log base) := by
      dsimp only [exponent]
      field_simp [hlevels_real.ne', hlog_base.ne']
    rw [hleft] at hsuffix
    exact
      (div_le_div_iff_of_pos_right hdenom).mp
        hsuffix
  have hrpow_pos :
      0 < Real.rpow (base : ℝ) exponent :=
    Real.rpow_pos_of_pos (by positivity) exponent
  have hratio_pos :
      0 <
        (cellCount base A j.val : ℝ) /
          (cellCount base A k.val : ℝ) := by
    exact div_pos (hcell_pos j.val) (hcell_pos k.val)
  have hlog_compare :
      Real.log (Real.rpow (base : ℝ) exponent) ≤
        Real.log
          ((cellCount base A j.val : ℝ) /
            (cellCount base A k.val : ℝ)) := by
    calc
      Real.log (Real.rpow (base : ℝ) exponent) =
          exponent * Real.log base :=
        Real.log_rpow (by positivity) exponent
      _ ≤ Real.log
          ((cellCount base A j.val : ℝ) /
            (cellCount base A k.val : ℝ)) := hscaled
  have hratio :
      Real.rpow (base : ℝ) exponent ≤
        (cellCount base A j.val : ℝ) /
          (cellCount base A k.val : ℝ) :=
    (Real.log_le_log_iff hrpow_pos hratio_pos).mp
      hlog_compare
  have hk_pos := hcell_pos k.val
  calc
    Real.rpow (base : ℝ) exponent *
          (cellCount base A k.val : ℝ)
        ≤ ((cellCount base A j.val : ℝ) /
              (cellCount base A k.val : ℝ)) *
            (cellCount base A k.val : ℝ) := by
          gcongr
    _ = (cellCount base A j.val : ℝ) := by
          field_simp [hk_pos.ne']

theorem localDim_average_lower_of_cellCount
    {base levels : ℕ}
    {A : DiscreteSet 3}
    (hbase : 2 ≤ base)
    (hlevels : 0 < levels)
    (hA : A.Nonempty)
    (average : ℝ)
    (hcard :
      (cellCount base A 0 : ℝ) *
          Real.rpow (base : ℝ)
            ((levels : ℝ) * average) ≤
        (cellCount base A levels : ℝ)) :
    average ≤
      ∑ i : Fin levels,
        localDim base A i *
          (scaleWeight levels i.succ -
            scaleWeight levels i.castSucc) := by
  have hlevels_real : (0 : ℝ) < levels := by
    exact_mod_cast hlevels
  have hbase_one : (1 : ℝ) < base := by
    exact_mod_cast (show 1 < base by omega)
  have hlog_base : 0 < Real.log (base : ℝ) :=
    Real.log_pos hbase_one
  have hcell_zero :
      0 < (cellCount base A 0 : ℝ) := by
    exact_mod_cast
      (cubicGridPartition_nonempty
        (base := base) (level := 0) hA).card_pos
  have hcell_terminal :
      0 < (cellCount base A levels : ℝ) := by
    exact_mod_cast
      (cubicGridPartition_nonempty
        (base := base) (level := levels) hA).card_pos
  have hratio :
      Real.rpow (base : ℝ)
          ((levels : ℝ) * average) ≤
        (cellCount base A levels : ℝ) /
          (cellCount base A 0 : ℝ) := by
    exact (le_div_iff₀ hcell_zero).2
      (by simpa [mul_comm] using hcard)
  have hratio_pos :
      0 <
        (cellCount base A levels : ℝ) /
          (cellCount base A 0 : ℝ) :=
    div_pos hcell_terminal hcell_zero
  have hlog :
      (levels : ℝ) * average *
          Real.log base ≤
        Real.log
          ((cellCount base A levels : ℝ) /
            (cellCount base A 0 : ℝ)) := by
    have hrpow_pos :
        0 <
          Real.rpow (base : ℝ)
            ((levels : ℝ) * average) :=
      Real.rpow_pos_of_pos (by positivity) _
    have hlog_mono :=
      (Real.log_le_log_iff hrpow_pos hratio_pos).2
        hratio
    calc
      (levels : ℝ) * average * Real.log base =
          Real.log
            (Real.rpow (base : ℝ)
              ((levels : ℝ) * average)) := by
        exact
          (Real.log_rpow
            (show 0 < (base : ℝ) by positivity)
            ((levels : ℝ) * average)).symm
      _ ≤
          Real.log
            ((cellCount base A levels : ℝ) /
              (cellCount base A 0 : ℝ)) := hlog_mono
  have havg :
      average ≤
        Real.log
            ((cellCount base A levels : ℝ) /
              (cellCount base A 0 : ℝ)) /
          ((levels : ℝ) * Real.log base) := by
    apply (le_div_iff₀ (mul_pos hlevels_real hlog_base)).2
    nlinarith
  have hweight :
      ∀ i : Fin levels,
        scaleWeight levels i.succ -
            scaleWeight levels i.castSucc =
          1 / (levels : ℝ) := by
    intro i
    simp [scaleWeight]
    field_simp [hlevels_real.ne']
    ring
  rw [Finset.sum_congr rfl
    (fun i _ => by rw [hweight i])]
  exact havg.trans_eq (localDim_sum hbase).symm

end Kakeya.Assouad
