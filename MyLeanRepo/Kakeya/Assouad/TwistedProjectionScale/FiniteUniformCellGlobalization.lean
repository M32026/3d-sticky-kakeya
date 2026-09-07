import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.FiniteUniformCellGlobalizationStatement

/-!
# Finite uniform-cell globalization

A local certificate supported on boundedly many comparable cells controls the
closed thickening of their full finite disjoint union, without division or
`ENNReal` cancellation.
-/

open MeasureTheory

namespace Kakeya.Assouad

lemma cthickening_finset_biUnion
    {α ι : Type*} [PseudoMetricSpace α] [DecidableEq ι]
    (rho : ℝ) (s : Finset ι) (f : ι → Set α) :
    Metric.cthickening rho (⋃ i ∈ s, f i) =
      ⋃ i ∈ s, Metric.cthickening rho (f i) := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp
  | @insert a s ha ih =>
    have h1 :
        (⋃ i ∈ insert a s, f i) = f a ∪ (⋃ i ∈ s, f i) := by
      ext x
      simp [Finset.mem_insert]
    have h2 :
        (⋃ i ∈ insert a s, Metric.cthickening rho (f i)) =
          Metric.cthickening rho (f a) ∪
            (⋃ i ∈ s, Metric.cthickening rho (f i)) := by
      ext x
      simp [Finset.mem_insert]
    rw [h1, Metric.cthickening_union rho (f a) (⋃ i ∈ s, f i),
      ih, h2]

theorem finite_uniform_cell_globalization :
    FiniteUniformCellGlobalizationStatement := by
  intro α _ cells hcells_nonempty cellSet h_meas h_disj h_pos
    R h_comp globalSet h_global rho hrho V h_thick selected hsel
    M hcard localSet hlocal L hL
  have h_thick_union :
      Metric.cthickening rho globalSet =
        ⋃ c ∈ cells, Metric.cthickening rho (cellSet c) := by
    rw [h_global]
    exact cthickening_finset_biUnion rho cells cellSet
  have h1 :
      volume (Metric.cthickening rho globalSet) ≤
        (cells.card : ENNReal) * V := by
    calc
      volume (Metric.cthickening rho globalSet) =
          volume
            (⋃ c ∈ cells, Metric.cthickening rho (cellSet c)) := by
        rw [h_thick_union]
      _ ≤ ∑ c ∈ cells,
          volume (Metric.cthickening rho (cellSet c)) :=
        measure_biUnion_finset_le cells _
      _ ≤ ∑ c ∈ cells, V := by
        apply Finset.sum_le_sum
        intro c hc
        exact h_thick c hc
      _ = (cells.card : ENNReal) * V := by
        rw [Finset.sum_const, nsmul_eq_mul]
  have h2 :
      L ≤ ∑ s ∈ selected, volume (cellSet s) := by
    have h3 :
        volume localSet ≤
          volume (finiteAtomUnion selected cellSet) :=
      measure_mono hlocal
    have h4 :
        volume (finiteAtomUnion selected cellSet) ≤
          ∑ s ∈ selected, volume (cellSet s) := by
      simp only [finiteAtomUnion]
      exact measure_biUnion_finset_le selected _
    calc
      L ≤ volume localSet := hL
      _ ≤ volume (finiteAtomUnion selected cellSet) := h3
      _ ≤ ∑ s ∈ selected, volume (cellSet s) := h4
  have h_disj' : (↑cells : Set α).PairwiseDisjoint cellSet := by
    intro x hx y hy hxy
    exact h_disj x hx y hy hxy
  have h3 :
      volume globalSet =
        ∑ c ∈ cells, volume (cellSet c) := by
    rw [h_global]
    simp only [finiteAtomUnion]
    exact measure_biUnion_finset h_disj' h_meas
  have h4 :
      ∀ s ∈ selected,
        volume (cellSet s) * (cells.card : ENNReal) ≤
          R * volume globalSet := by
    intro s hs
    have h_s_in_cells : s ∈ cells := hsel hs
    have h5 :
        ∀ c ∈ cells,
          volume (cellSet s) ≤ R * volume (cellSet c) := by
      intro c hc
      exact h_comp s h_s_in_cells c hc
    have h6 :
        ∑ c ∈ cells, volume (cellSet s) ≤
          ∑ c ∈ cells, R * volume (cellSet c) := by
      apply Finset.sum_le_sum
      intro c hc
      exact h5 c hc
    have h7 :
        ∑ c ∈ cells, volume (cellSet s) =
          (cells.card : ENNReal) * volume (cellSet s) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    have h8 :
        ∑ c ∈ cells, R * volume (cellSet c) =
          R * ∑ c ∈ cells, volume (cellSet c) := by
      rw [Finset.mul_sum]
    rw [h7, h8] at h6
    have h9 :
        (cells.card : ENNReal) * volume (cellSet s) ≤
          R * volume globalSet := by
      rw [h3]
      exact h6
    rw [mul_comm]
    exact h9
  calc
    L * volume (Metric.cthickening rho globalSet) ≤
        L * ((cells.card : ENNReal) * V) := by
      gcongr
    _ = (L * (cells.card : ENNReal)) * V := by ring
    _ ≤ (∑ s ∈ selected, volume (cellSet s)) *
          (cells.card : ENNReal) * V := by
      gcongr
    _ = ∑ s ∈ selected,
          (volume (cellSet s) * (cells.card : ENNReal)) * V := by
      have h_sum1 :
          (∑ s ∈ selected, volume (cellSet s)) *
              (cells.card : ENNReal) =
            ∑ s ∈ selected,
              volume (cellSet s) * (cells.card : ENNReal) := by
        rw [Finset.sum_mul]
      rw [h_sum1, Finset.sum_mul]
    _ ≤ ∑ s ∈ selected, (R * volume globalSet) * V := by
      apply Finset.sum_le_sum
      intro s hs
      exact mul_le_mul_left (h4 s hs) V
    _ = (selected.card : ENNReal) *
          ((R * volume globalSet) * V) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (M : ENNReal) * ((R * volume globalSet) * V) := by
      gcongr
    _ = R * (M : ENNReal) * V * volume globalSet := by ring

end Kakeya.Assouad
