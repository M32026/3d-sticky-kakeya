import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.DistanceCoareaUpper
import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.DistanceCoareaLower
import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import Mathlib.Tactic

/-!
# Distance Function Coarea Formula — Equality

Combines the upper bound (`DistanceCoareaUpper`) and lower bound
(`DistanceCoareaLower`) to prove the exact coarea formula for the
distance function.

## Main result

- `distance_coarea_eq`: exact coarea formula for `d(x) = infDist x C`
  on `A ⊆ {d > 0}`.
-/

open MeasureTheory Metric Set ENNReal Filter
open scoped MeasureTheory

namespace Geometry

variable {n : ℕ} [Nonempty (Fin n)]

/-- **Exact coarea formula for the distance function.**

For a nonempty closed `C`, measurable `A ⊆ {d > 0}`, and `a < b`:

```
volume {x ∈ A | a < d x ≤ b} = ∫⁻ s in Ioc a b, μHE[n-1] {x ∈ A | d x = s}
```

where `d(x) = infDist x C`.

Proof: For every `0 < ε < 1`, the upper bound gives
`volume ≤ C_up(ε) * integral`, and the lower bound gives
`volume ≥ C_low(ε) * integral`, where
`C_up(ε) = (1+ε)^(n-1)/(1-ε)^n → 1` and
`C_low(ε) = (1-ε)^(n-1)/(1+ε)^n → 1`.
Taking `ε → 0` yields equality. -/
theorem distance_coarea_eq (hn : 2 ≤ n)
    {C : Set (E n)} (hC : IsClosed C) (hne : C.Nonempty)
    (h_d_meas : FunctionLevelMeasurable (fun x : E n => infDist x C))
    {A : Set (E n)} (hA : MeasurableSet A) (hA_bdd : Bornology.IsBounded A)
    (hA_sub : A ⊆ {x | 0 < infDist x C})
    {a b : ℝ} (hab : a < b) :
    volume {x ∈ A | a < infDist x C ∧ infDist x C ≤ b} =
      ∫⁻ s in Set.Ioc a b, μHE[n - 1] {x ∈ A | infDist x C = s} := by
  let d := fun x : E n => infDist x C
  let V := volume {x ∈ A | a < d x ∧ d x ≤ b}
  let I := ∫⁻ s in Set.Ioc a b, μHE[n - 1] {x ∈ A | d x = s}
  have h_upper : ∀ (ε : ℝ), 0 < ε → ε < 1 →
      V ≤ ENNReal.ofReal (((1 + ε) ^ (n - 1 : ℕ)) / ((1 - ε) ^ n)) * I := by
    intro ε hε hε2
    exact distance_coarea_upper hC hne hA hA_bdd hA_sub hab hε hε2
  have h_lower : ∀ (ε : ℝ), 0 < ε → ε < 1 →
      V ≥ ENNReal.ofReal (((1 - ε) ^ (n - 1 : ℕ)) / ((1 + ε) ^ n)) * I := by
    intro ε hε hε2
    exact distance_coarea_lower hn hC hne h_d_meas hA hA_bdd hA_sub hab hε hε2
  by_cases hI_top : I = ⊤
  · -- If I = ⊤, then upper bound gives V ≤ ⊤ (trivial) and lower bound gives V ≥ ⊤, so V = ⊤
    have h1 : V ≥ ⊤ := by
      have h2 := h_lower (1 / 2) (by norm_num) (by norm_num)
      rw [hI_top] at h2
      have h_coeff_pos : 0 < ENNReal.ofReal (((1 - (1 / 2 : ℝ)) ^ (n - 1 : ℕ)) / ((1 + (1 / 2 : ℝ)) ^ n)) := by positivity
      have h3 : ENNReal.ofReal (((1 - (1 / 2 : ℝ)) ^ (n - 1 : ℕ)) / ((1 + (1 / 2 : ℝ)) ^ n)) * ⊤ = ⊤ := by
        rw [mul_top] <;> exact h_coeff_pos.ne'
      rw [h3] at h2
      exact h2
    have h3 : V = ⊤ := by simpa using h1
    have h4 : V = I := by
      exact h3.trans hI_top.symm
    exact h4
  · -- I < ⊤
    have hI_lt_top : I ≠ ⊤ := hI_top
    have hC_up_at0 : ((1 + (0 : ℝ)) ^ (n - 1 : ℕ)) / ((1 - (0 : ℝ)) ^ n) = 1 := by
      have h_pos : 0 < n := by omega
      have h1 : (1 - (0 : ℝ)) ^ n ≠ 0 := by simp
      field_simp [h1] <;> norm_num
    have hC_low_at0 : ((1 - (0 : ℝ)) ^ (n - 1 : ℕ)) / ((1 + (0 : ℝ)) ^ n) = 1 := by
      have h_pos : 0 < n := by omega
      have h1 : (1 + (0 : ℝ)) ^ n ≠ 0 := by simp
      field_simp [h1] <;> norm_num
    let g_up : ℝ → ℝ := fun ε => (((1 + ε) ^ (n - 1 : ℕ)) / ((1 - ε) ^ n)) * I.toReal
    let g_low : ℝ → ℝ := fun ε => (((1 - ε) ^ (n - 1 : ℕ)) / ((1 + ε) ^ n)) * I.toReal
    let f_up : ℝ → ENNReal := fun ε => ENNReal.ofReal (g_up ε)
    let f_low : ℝ → ENNReal := fun ε => ENNReal.ofReal (g_low ε)
    have hg_up_cont_at : ContinuousAt g_up 0 := by
      have h1 : ContinuousAt (fun ε : ℝ => (1 + ε) ^ (n - 1 : ℕ)) 0 := by fun_prop
      have h2 : ContinuousAt (fun ε : ℝ => (1 - ε) ^ n) 0 := by fun_prop
      have h3 : (1 - (0 : ℝ)) ^ n ≠ 0 := by simp
      exact (h1.div h2 h3).mul continuousAt_const
    have hg_low_cont_at : ContinuousAt g_low 0 := by
      have h1 : ContinuousAt (fun ε : ℝ => (1 - ε) ^ (n - 1 : ℕ)) 0 := by fun_prop
      have h2 : ContinuousAt (fun ε : ℝ => (1 + ε) ^ n) 0 := by fun_prop
      have h3 : (1 + (0 : ℝ)) ^ n ≠ 0 := by simp
      exact (h1.div h2 h3).mul continuousAt_const
    have hf_up_cont_at : ContinuousAt f_up 0 :=
      ENNReal.continuous_ofReal.continuousAt.comp hg_up_cont_at
    have hf_low_cont_at : ContinuousAt f_low 0 :=
      ENNReal.continuous_ofReal.continuousAt.comp hg_low_cont_at
    have hf_up0 : f_up 0 = I := by
      simp [f_up, g_up, hC_up_at0, ENNReal.ofReal_toReal hI_lt_top] <;> ring
    have hf_low0 : f_low 0 = I := by
      simp [f_low, g_low, hC_low_at0, ENNReal.ofReal_toReal hI_lt_top] <;> ring
    have hf_up_eq : ∀ (ε : ℝ), 0 < ε → ε < 1 →
        f_up ε = ENNReal.ofReal (((1 + ε) ^ (n - 1 : ℕ)) / ((1 - ε) ^ n)) * I := by
      intro ε hε_pos hε_lt1
      set ratio : ℝ := ((1 + ε) ^ (n - 1 : ℕ)) / ((1 - ε) ^ n) with hratio
      have h1 : 0 ≤ ratio := by positivity
      have h2 : 0 ≤ I.toReal := by positivity
      calc
        f_up ε = ENNReal.ofReal (ratio * I.toReal) := by simp [f_up, g_up, hratio]
        _ = ENNReal.ofReal ratio * ENNReal.ofReal (I.toReal) := by
          rw [ENNReal.ofReal_mul h1]
        _ = ENNReal.ofReal ratio * I := by
          rw [ENNReal.ofReal_toReal hI_lt_top]
    have hf_low_eq : ∀ (ε : ℝ), 0 < ε → ε < 1 →
        f_low ε = ENNReal.ofReal (((1 - ε) ^ (n - 1 : ℕ)) / ((1 + ε) ^ n)) * I := by
      intro ε hε_pos hε_lt1
      set ratio : ℝ := ((1 - ε) ^ (n - 1 : ℕ)) / ((1 + ε) ^ n) with hratio
      have h1 : 0 ≤ ratio := by positivity
      have h2 : 0 ≤ I.toReal := by positivity
      calc
        f_low ε = ENNReal.ofReal (ratio * I.toReal) := by simp [f_low, g_low, hratio]
        _ = ENNReal.ofReal ratio * ENNReal.ofReal (I.toReal) := by
          rw [ENNReal.ofReal_mul h1]
        _ = ENNReal.ofReal ratio * I := by
          rw [ENNReal.ofReal_toReal hI_lt_top]
    have h_upper_le : V ≤ I := by
      by_contra h
      have h_strict : I < V := lt_of_not_ge h
      have h_lt : f_up 0 < V := by rw [hf_up0] <;> exact h_strict
      have h_nhds : Set.Iio V ∈ nhds (f_up 0) := Iio_mem_nhds h_lt
      have h_eventually : ∀ᶠ (ε : ℝ) in nhds 0, f_up ε < V :=
        hf_up_cont_at.eventually h_nhds |>.mono (fun ε hε => by simpa [Set.mem_Iio] using hε)
      rcases Metric.mem_nhds_iff.mp h_eventually with ⟨δ, hδ_pos, hδ⟩
      let ε : ℝ := min (δ / 2) (1 / 2)
      have hε_pos : 0 < ε := by positivity
      have hε_lt1 : ε < 1 := by
        have h : ε ≤ 1 / 2 := min_le_right _ _
        linarith
      have hε_in_ball : dist ε 0 < δ := by
        have h1 : ε ≤ δ / 2 := min_le_left _ _
        simpa [dist_eq_norm, abs_of_pos hε_pos] using by linarith
      have hlt : f_up ε < V := hδ hε_in_ball
      have h4 := h_upper ε hε_pos hε_lt1
      have h4' : V ≤ f_up ε := by rw [hf_up_eq ε hε_pos hε_lt1] at *; exact h4
      exact (not_le.mpr hlt) h4'
    have h_lower_ge : V ≥ I := by
      by_contra h
      have h_strict : V < I := lt_of_not_ge h
      have h_lt : V < f_low 0 := by rw [hf_low0] <;> exact h_strict
      have h_nhds : Set.Ioi V ∈ nhds (f_low 0) := Ioi_mem_nhds h_lt
      have h_eventually : ∀ᶠ (ε : ℝ) in nhds 0, V < f_low ε :=
        hf_low_cont_at.eventually h_nhds |>.mono (fun ε hε => by simpa [Set.mem_Ioi] using hε)
      rcases Metric.mem_nhds_iff.mp h_eventually with ⟨δ, hδ_pos, hδ⟩
      let ε : ℝ := min (δ / 2) (1 / 2)
      have hε_pos : 0 < ε := by positivity
      have hε_lt1 : ε < 1 := by
        have h : ε ≤ 1 / 2 := min_le_right _ _
        linarith
      have hε_in_ball : dist ε 0 < δ := by
        have h1 : ε ≤ δ / 2 := min_le_left _ _
        simpa [dist_eq_norm, abs_of_pos hε_pos] using by linarith
      have hlt : V < f_low ε := hδ hε_in_ball
      have h4 := h_lower ε hε_pos hε_lt1
      have h4' : f_low ε ≤ V := by rw [hf_low_eq ε hε_pos hε_lt1] at *; exact h4
      exact (not_le.mpr hlt) h4'
    exact le_antisymm h_upper_le h_lower_ge

end Geometry
