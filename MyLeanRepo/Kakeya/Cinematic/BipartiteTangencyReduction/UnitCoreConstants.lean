import MyLeanRepo.Kakeya.Cinematic.BipartiteTangencyReduction.LensNonOverlapEnlarged

/-!
# Elementary constants for the robust unit core

These lemmas instantiate the polynomial comparability constant and widen the
endpoint localization interval after replacing a pair-dependent factor by a
uniform one.
-/

namespace Kakeya.Cinematic

lemma unit_core_comparison_ge_hundred
    {tangency C : ℝ} (hC : 100 ≤ C) (htangency : 5 ≤ tangency) :
    100 ≤ C * Real.rpow tangency C := by
  have hpower : 1 ≤ Real.rpow tangency C :=
    Real.one_le_rpow (by linarith) (by linarith)
  calc
    (100 : ℝ) ≤ C := hC
    _ = C * 1 := by ring
    _ ≤ C * Real.rpow tangency C := by gcongr

lemma unit_core_comparison_ge_ten
    {tangency C : ℝ} (hC : 100 ≤ C) (htangency : 5 ≤ tangency) :
    10 ≤ C * Real.rpow tangency C :=
  (by linarith : (10 : ℝ) ≤ 100).trans
    (unit_core_comparison_ge_hundred hC htangency)

lemma tangency_le_unit_core_comparison
    {tangency C : ℝ} (hC : 100 ≤ C) (htangency : 5 ≤ tangency) :
    tangency ≤ C * Real.rpow tangency C := by
  have hC_one : 1 ≤ C := by linarith
  have htangency_one : 1 ≤ tangency := by linarith
  have hpower :
      tangency ≤ Real.rpow tangency C := by
    calc
      tangency = Real.rpow tangency 1 := (Real.rpow_one tangency).symm
      _ ≤ Real.rpow tangency C :=
        Real.rpow_le_rpow_of_exponent_le htangency_one hC_one
  have hpower_nonneg : 0 ≤ Real.rpow tangency C :=
    Real.rpow_nonneg (by linarith) _
  exact hpower.trans (le_mul_of_one_le_left hpower_nonneg hC_one)

lemma mem_Icc_widen_factor
    {a b x e E s : ℝ} (heE : e ≤ E) (hs : 0 ≤ s)
    (h : x ∈ Set.Icc (a - e * s) (b + e * s)) :
    x ∈ Set.Icc (a - E * s) (b + E * s) := by
  have hfactor : e * s ≤ E * s :=
    mul_le_mul_of_nonneg_right heE hs
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

end Kakeya.Cinematic
