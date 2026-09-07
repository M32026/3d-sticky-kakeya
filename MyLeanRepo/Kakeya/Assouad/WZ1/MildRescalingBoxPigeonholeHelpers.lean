import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.ENNReal.Operations
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic
import MyLeanRepo.Kakeya.Assouad.WZ1.MildRescalingPopularBoxStatements

/-!
# Helpers for the WZ1 mild-rescaling box pigeonhole
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

lemma cube_mul_le
    (count : ℕ) (h : ℝ) (h_pos : 0 < h)
    (hcount : (count : ℝ) ≤ 3 / h) :
    (count : ENNReal) ^ 3 * ENNReal.ofReal (h ^ 3 / 27) ≤ 1 := by
  have h_real : (count : ℝ) ^ 3 * (h ^ 3 / 27) ≤ 1 := by
    have h_count_cube : (count : ℝ) ^ 3 ≤ (3 / h) ^ 3 := by
      gcongr
    have h_normalize : (3 / h) ^ 3 * (h ^ 3 / 27) = 1 := by
      field_simp [h_pos.ne']
      ring
    calc
      (count : ℝ) ^ 3 * (h ^ 3 / 27)
          ≤ (3 / h) ^ 3 * (h ^ 3 / 27) := by
            gcongr
      _ = 1 := h_normalize
  have h_eq :
      (count : ENNReal) ^ 3 * ENNReal.ofReal (h ^ 3 / 27) =
        ENNReal.ofReal ((count : ℝ) ^ 3 * (h ^ 3 / 27)) := by
    have h_count :
        (count : ENNReal) = ENNReal.ofReal (count : ℝ) := by
      simp
    rw [h_count, ← ENNReal.ofReal_pow (by positivity)]
    rw [← ENNReal.ofReal_mul (by positivity)]
  rw [h_eq, ENNReal.ofReal_le_one]
  exact h_real

lemma measure_cover_le_sum
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {s : Set X} {ι : Type*} [Fintype ι] {sets : ι → Set X}
    (hcover : s ⊆ ⋃ i, sets i) :
    μ s ≤ ∑ i : ι, μ (s ∩ sets i) := by
  have h_subset : s ⊆ ⋃ i : ι, s ∩ sets i := by
    intro x hx
    rcases Set.mem_iUnion.mp (hcover hx) with ⟨i, hi⟩
    exact Set.mem_iUnion.mpr ⟨i, hx, hi⟩
  have h_mono : μ s ≤ μ (⋃ i : ι, s ∩ sets i) :=
    measure_mono h_subset
  have h_union :
      μ (⋃ i : ι, s ∩ sets i) ≤ ∑ i : ι, μ (s ∩ sets i) := by
    have h_eq :
        (⋃ i : ι, s ∩ sets i) =
          ⋃ i ∈ (Finset.univ : Finset ι), s ∩ sets i := by
      ext x
      simp
    rw [h_eq]
    exact
      MeasureTheory.measure_biUnion_finset_le
        Finset.univ (fun i => s ∩ sets i)
  exact h_mono.trans h_union

lemma point3_apply (x y z : ℝ) :
    (point3 x y z) 0 = x ∧
      (point3 x y z) 1 = y ∧
        (point3 x y z) 2 = z := by
  simp [point3]

end Kakeya.Assouad
