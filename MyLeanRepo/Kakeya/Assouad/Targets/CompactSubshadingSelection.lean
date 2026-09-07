import MyLeanRepo.Kakeya.Assouad.Statements
import Mathlib.MeasureTheory.Measure.Regular

/-!
WZ2 Section 7: inner-regularize every carrier of a finite shading while
retaining at least half of its aggregate mass.
-/

noncomputable section

open MeasureTheory Set

namespace Kakeya.Assouad

theorem compact_subshading_selection :
    CompactSubshadingSelectionStatement := by
  intro delta F Y
  have h_main : ∀ i : Fin F.card, ∃ (K : Set Point3),
      K ⊆ Y.carrier i ∧ IsCompact K ∧
        (1 / 2 : ENNReal) * MeasureTheory.volume (Y.carrier i) ≤
          MeasureTheory.volume K := by
    intro i
    set A : Set Point3 := Y.carrier i with hA_def
    have hA_meas : MeasurableSet A := Y.measurable_carrier i
    have hA_sub : A ⊆ (F.tube i).carrier := Y.subset_body i
    have h_seg_compact :
        IsCompact (unitSegment (F.tube i).base (F.tube i).direction) := by
      exact isCompact_Icc.image
        (continuous_const.add (continuous_id.smul continuous_const))
    have h_tube_compact : IsCompact (F.tube i).carrier := by
      simpa [DeltaTube.carrier] using h_seg_compact.cthickening
    have hA_lt_top : MeasureTheory.volume A < ⊤ :=
      (measure_mono hA_sub).trans_lt h_tube_compact.measure_lt_top
    have hA_ne_top : MeasureTheory.volume A ≠ ⊤ := hA_lt_top.ne
    by_cases h0 : MeasureTheory.volume A = 0
    · refine ⟨∅, by simp, isCompact_empty, ?_⟩
      rw [h0, measure_empty]
      simp
    · have hε_pos : (MeasureTheory.volume A / 2) ≠ 0 := by
        simp [h0, ENNReal.div_eq_zero_iff]
      rcases hA_meas.exists_isCompact_isClosed_sdiff_lt hA_ne_top hε_pos with
        ⟨K, hK_sub, hK_compact, _, hK_sdiff⟩
      have hK_meas : MeasurableSet K := hK_compact.measurableSet
      have h_diff_meas : MeasurableSet (A \ K) :=
        MeasurableSet.diff hA_meas hK_meas
      have hK_ne_top : MeasureTheory.volume K ≠ ⊤ :=
        (measure_mono hK_sub).trans_lt hA_lt_top |>.ne
      have h_disj : Disjoint K (A \ K) := by
        exact Set.disjoint_left.mpr (fun x hx1 hx2 => hx2.2 hx1)
      have h_union_eq : K ∪ (A \ K) = A := Set.union_sdiff_cancel hK_sub
      have h_union_meas : MeasureTheory.volume (K ∪ (A \ K)) =
          MeasureTheory.volume K + MeasureTheory.volume (A \ K) :=
        measure_union h_disj h_diff_meas
      have h_eq : MeasureTheory.volume A =
          MeasureTheory.volume K + MeasureTheory.volume (A \ K) := by
        rw [h_union_eq] at h_union_meas
        exact h_union_meas
      have h_div : MeasureTheory.volume A / 2 =
          (1 / 2 : ENNReal) * MeasureTheory.volume A := by
        have h : MeasureTheory.volume A / 2 =
            MeasureTheory.volume A * (2 : ENNReal)⁻¹ := by
          exact div_eq_mul_inv (MeasureTheory.volume A) 2
        rw [h]
        have h2 : (2 : ENNReal)⁻¹ = (1 / 2 : ENNReal) := by
          simp
        rw [h2, mul_comm]
      have h_half_sdiff : MeasureTheory.volume (A \ K) <
          (1 / 2 : ENNReal) * MeasureTheory.volume A := by
        rw [h_div] at hK_sdiff
        exact hK_sdiff
      have h1 : (1 / 2 : ENNReal) + (1 / 2 : ENNReal) = 1 := by
        have h2 : (1 / 2 : ENNReal) + (1 / 2 : ENNReal) =
            2 * (1 / 2 : ENNReal) := by
          rw [two_mul]
        rw [h2]
        have h3 : 2 * (1 / 2 : ENNReal) = 1 := by
          have h4 : (1 / 2 : ENNReal) = (2 : ENNReal)⁻¹ := by simp
          rw [h4]
          exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)
        exact h3
      refine ⟨K, hK_sub, hK_compact, ?_⟩
      by_contra h
      have h' : MeasureTheory.volume K <
          (1 / 2 : ENNReal) * MeasureTheory.volume A :=
        lt_of_not_ge h
      have h_sum : MeasureTheory.volume K + MeasureTheory.volume (A \ K) <
          (1 / 2 : ENNReal) * MeasureTheory.volume A +
          (1 / 2 : ENNReal) * MeasureTheory.volume A := by
        exact ENNReal.add_lt_add h' h_half_sdiff
      have h_half : (1 / 2 : ENNReal) * MeasureTheory.volume A +
          (1 / 2 : ENNReal) * MeasureTheory.volume A =
            MeasureTheory.volume A := by
        calc
          (1 / 2 : ENNReal) * MeasureTheory.volume A +
              (1 / 2 : ENNReal) * MeasureTheory.volume A
            = ((1 / 2 : ENNReal) + (1 / 2 : ENNReal)) *
                MeasureTheory.volume A := by
              rw [add_mul]
          _ = (1 : ENNReal) * MeasureTheory.volume A := by rw [h1]
          _ = MeasureTheory.volume A := by simp
      rw [h_half] at h_sum
      rw [h_eq] at h_sum
      exact h_sum.false
  choose K hK_sub hK_compact hK_half using h_main
  let Z : Kakeya.Streamlined.TubeShading F :=
    { carrier := K
      measurable_carrier := fun i => (hK_compact i).measurableSet
      subset_body := fun i => (hK_sub i).trans (Y.subset_body i) }
  refine ⟨Z, fun i => hK_sub i, ?_, fun i => hK_compact i⟩
  have h_mass : Z.mass =
      ∑ i : Fin F.card, MeasureTheory.volume (K i) := by rfl
  rw [h_mass]
  have h_sum_ineq : ∑ i : Fin F.card, MeasureTheory.volume (K i) ≥
      ∑ i : Fin F.card,
        (1 / 2 : ENNReal) * MeasureTheory.volume (Y.carrier i) := by
    apply Finset.sum_le_sum
    intro i _
    exact hK_half i
  have hYmass : Y.mass =
      ∑ i : Fin F.card, MeasureTheory.volume (Y.carrier i) := by rfl
  have h' : ∑ i : Fin F.card,
      (1 / 2 : ENNReal) * MeasureTheory.volume (Y.carrier i) =
        (1 / 2 : ENNReal) * Y.mass := by
    rw [hYmass, ← Finset.mul_sum]
  rw [h'] at h_sum_ineq
  exact h_sum_ineq

end Kakeya.Assouad
