import MyLeanRepo.Kakeya.Cinematic.Section5.LevelSetInputs

/-!
# Retained mass from a finite measurable cover

This is the measure-theoretic pigeonhole used to retain a quantitative
fraction of a Section 5 level set after freezing finitely many parameters.
-/

namespace Kakeya.Cinematic

theorem finite_measurable_cover_retained_mass :
    FiniteMeasurableCoverRetainedMassStatement := by
  intro α _ μ ι _ _ E bins loss hE _hfin hbins hcover _hloss0 hcard
  have h1 : E ⊆ ⋃ i : ι, (E ∩ bins i) := by
    intro x hx
    have h2 : x ∈ (⋃ i : ι, bins i) := hcover hx
    have h2' : ∃ i : ι, x ∈ bins i := by
      simpa [Set.mem_iUnion] using h2
    rcases h2' with ⟨i, hi⟩
    have h3' : x ∈ E ∩ bins i := ⟨hx, hi⟩
    exact Set.mem_iUnion.mpr ⟨i, h3'⟩
  have h3 : μ E ≤ ∑ i : ι, μ (E ∩ bins i) := by
    have h4 : μ E ≤ μ (⋃ i : ι, (E ∩ bins i)) :=
      MeasureTheory.measure_mono h1
    have h5 : μ (⋃ i : ι, (E ∩ bins i)) ≤ ∑ i : ι, μ (E ∩ bins i) :=
      MeasureTheory.measure_iUnion_fintype_le μ (fun i : ι => E ∩ bins i)
    exact le_trans h4 h5
  have h6 : ∃ i : ι, ∀ j : ι, μ (E ∩ bins j) ≤ μ (E ∩ bins i) := by
    have h7 := Finset.exists_max_image (Finset.univ : Finset ι)
      (fun i : ι => μ (E ∩ bins i)) (by simp)
    rcases h7 with ⟨i, _, h8⟩
    exact ⟨i, fun j => h8 j (Finset.mem_univ j)⟩
  rcases h6 with ⟨i, hmax⟩
  have h9 : ∑ j : ι, μ (E ∩ bins j) ≤
      (Fintype.card ι : ENNReal) * μ (E ∩ bins i) := by
    have h10 : ∑ j : ι, μ (E ∩ bins j) ≤ ∑ j : ι, μ (E ∩ bins i) :=
      Finset.sum_le_sum fun j _ => hmax j
    have h11 : ∑ j : ι, μ (E ∩ bins i) =
        (Fintype.card ι : ENNReal) * μ (E ∩ bins i) := by
      rw [Finset.sum_const]
      simp
    rw [h11] at h10
    exact h10
  have h12 : (Fintype.card ι : ENNReal) ≤ ENNReal.ofReal loss := by
    have h13 : (Fintype.card ι : ℝ) ≤ loss := hcard
    have h14 : (Fintype.card ι : ENNReal) =
        ENNReal.ofReal (Fintype.card ι : ℝ) := by
      simp
    rw [h14]
    exact ENNReal.ofReal_le_ofReal h13
  have h15 : μ E ≤ ENNReal.ofReal loss * μ (E ∩ bins i) := by
    calc
      μ E ≤ ∑ j : ι, μ (E ∩ bins j) := h3
      _ ≤ (Fintype.card ι : ENNReal) * μ (E ∩ bins i) := h9
      _ ≤ ENNReal.ofReal loss * μ (E ∩ bins i) := by
        gcongr
  refine' ⟨i, _, _, h15⟩
  · exact hE.inter (hbins i)
  · exact Set.inter_subset_left

end Kakeya.Cinematic
