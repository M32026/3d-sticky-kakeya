import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Bounded overlap lemmas via lintegral
-/

noncomputable section

open MeasureTheory Metric Set Finset Real

attribute [local instance] Classical.propDecidable

namespace Kakeya.Assouad

/-- Upper bounded overlap: if every point of B is in at most k sets A i,
then ∑ μ(A i ∩ B) ≤ k * μ(B). -/
lemma bounded_overlap_sum
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α} {ι : Type*}
    (F : Finset ι) (A : ι → Set α) (B : Set α) (k : ℕ)
    (hB : MeasurableSet B) (hA : ∀ i ∈ F, MeasurableSet (A i))
    (h : ∀ x ∈ B, (F.filter (fun i => x ∈ A i)).card ≤ k) :
    ∑ i ∈ F, μ (A i ∩ B) ≤ (k : ENNReal) * μ B := by
  let g : ι → (α → ENNReal) := fun i => Set.indicator (A i ∩ B) (fun _ => (1 : ENNReal))
  let f : α → ENNReal := fun x => ∑ i ∈ F, g i x
  have hgm : ∀ i ∈ F, Measurable (g i) := by
    intro i hi
    apply Measurable.indicator
    · exact measurable_const
    · exact (hA i hi).inter hB
  have h_f_zero : ∀ x ∉ B, f x = 0 := by
    intro x hx
    have h9 : ∀ i ∈ F, g i x = 0 := by
      intro i _
      simp [g, Set.indicator_apply, hx]
    have h10 : f x = ∑ i ∈ F, g i x := by rfl
    rw [h10, Finset.sum_congr rfl h9] <;> simp
  have h_f_indicator : f = Set.indicator B f := by
    funext x
    by_cases hx : x ∈ B
    · simp [Set.indicator_apply, hx]
    · have h10 : f x = 0 := h_f_zero x hx
      simp [Set.indicator_apply, hx, h10]
  have h1 : ∀ x ∈ B, f x ≤ (k : ENNReal) := by
    intro x hx
    have h21 : ∀ i ∈ F, g i x = (if x ∈ A i then (1 : ENNReal) else 0) := by
      intro i _
      simp [g, Set.indicator_apply, hx] <;> split_ifs <;> tauto
    have h2 : f x = ∑ i ∈ F, (if x ∈ A i then (1 : ENNReal) else 0) := by
      dsimp only [f]
      rw [Finset.sum_congr rfl h21]
    rw [h2]
    have h3 : ∑ i ∈ F, (if x ∈ A i then (1 : ENNReal) else 0) =
        ((F.filter (fun i => x ∈ A i)).card : ENNReal) := by
      rw [Finset.sum_ite]
      <;> simp
      <;> norm_cast
    rw [h3]
    exact_mod_cast h x hx
  have hf_eq : ∫⁻ x, f x ∂μ = ∑ i ∈ F, μ (A i ∩ B) := by
    rw [MeasureTheory.lintegral_finsetSum F hgm]
    apply Finset.sum_congr rfl
    intro i hi
    have hAiB : MeasurableSet (A i ∩ B) := (hA i hi).inter hB
    have h_eq1 : ∫⁻ x, g i x ∂μ = ∫⁻ x in (A i ∩ B), (1 : ENNReal) ∂μ :=
      MeasureTheory.lintegral_indicator hAiB (fun _ => (1 : ENNReal))
    rw [h_eq1]
    exact MeasureTheory.setLIntegral_one (A i ∩ B)
  have h5 : ∫⁻ x, f x ∂μ = ∫⁻ x in B, f x ∂μ := by
    have h51 : (∫⁻ x, f x ∂μ) = (∫⁻ x, Set.indicator B f x ∂μ) := by
      congr
      <;> exact h_f_indicator
    rw [h51]
    exact MeasureTheory.lintegral_indicator hB f
  have h6 : ∫⁻ x in B, f x ∂μ ≤ ∫⁻ x in B, (k : ENNReal) ∂μ :=
    MeasureTheory.setLIntegral_mono' hB (fun x hx => h1 x hx)
  have hB' : NullMeasurableSet B μ := hB.nullMeasurableSet
  have h7 : ∫⁻ x in B, (k : ENNReal) ∂μ = (k : ENNReal) * μ B := by
    have h71 : (∫⁻ x in B, (k : ENNReal) ∂μ) = ∫⁻ a, Set.indicator B (fun _ : α => (k : ENNReal)) a ∂μ := by
      exact (MeasureTheory.lintegral_indicator hB (fun _ : α => (k : ENNReal))).symm
    rw [h71]
    exact MeasureTheory.lintegral_indicator_const₀ hB' (k : ENNReal)
  have h4 : ∫⁻ x, f x ∂μ ≤ (k : ENNReal) * μ B := by
    calc ∫⁻ x, f x ∂μ
      = ∫⁻ x in B, f x ∂μ := h5
    _ ≤ ∫⁻ x in B, (k : ENNReal) ∂μ := h6
    _ = (k : ENNReal) * μ B := h7
  rw [←hf_eq]
  exact h4

/-- Lower bounded overlap: if every point of B is in at least k sets A i,
then k * μ(B) ≤ ∑ μ(A i ∩ B). -/
lemma bounded_overlap_lower
    {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α} {ι : Type*}
    (F : Finset ι) (A : ι → Set α) (B : Set α) (k : ℕ)
    (hB : MeasurableSet B) (hA : ∀ i ∈ F, MeasurableSet (A i))
    (h : ∀ x ∈ B, k ≤ (F.filter (fun i => x ∈ A i)).card) :
    (k : ENNReal) * μ B ≤ ∑ i ∈ F, μ (A i ∩ B) := by
  let g : ι → (α → ENNReal) := fun i => Set.indicator (A i ∩ B) (fun _ => (1 : ENNReal))
  let f : α → ENNReal := fun x => ∑ i ∈ F, g i x
  have hgm : ∀ i ∈ F, Measurable (g i) := by
    intro i hi
    apply Measurable.indicator
    · exact measurable_const
    · exact (hA i hi).inter hB
  have h_f_zero : ∀ x ∉ B, f x = 0 := by
    intro x hx
    have h9 : ∀ i ∈ F, g i x = 0 := by
      intro i _
      simp [g, Set.indicator_apply, hx]
    have h10 : f x = ∑ i ∈ F, g i x := by rfl
    rw [h10, Finset.sum_congr rfl h9] <;> simp
  have h_f_indicator : f = Set.indicator B f := by
    funext x
    by_cases hx : x ∈ B
    · simp [Set.indicator_apply, hx]
    · have h10 : f x = 0 := h_f_zero x hx
      simp [Set.indicator_apply, hx, h10]
  have h1 : ∀ x ∈ B, (k : ENNReal) ≤ f x := by
    intro x hx
    have h21 : ∀ i ∈ F, g i x = (if x ∈ A i then (1 : ENNReal) else 0) := by
      intro i _
      simp [g, Set.indicator_apply, hx] <;> split_ifs <;> tauto
    have h2 : f x = ∑ i ∈ F, (if x ∈ A i then (1 : ENNReal) else 0) := by
      dsimp only [f]
      rw [Finset.sum_congr rfl h21]
    rw [h2]
    have h3 : ∑ i ∈ F, (if x ∈ A i then (1 : ENNReal) else 0) =
        ((F.filter (fun i => x ∈ A i)).card : ENNReal) := by
      rw [Finset.sum_ite] <;> simp <;> norm_cast
    rw [h3]
    exact_mod_cast h x hx
  have hf_eq : ∫⁻ x, f x ∂μ = ∑ i ∈ F, μ (A i ∩ B) := by
    rw [MeasureTheory.lintegral_finsetSum F hgm]
    apply Finset.sum_congr rfl
    intro i hi
    have hAiB : MeasurableSet (A i ∩ B) := (hA i hi).inter hB
    have h_eq1 : ∫⁻ x, g i x ∂μ = ∫⁻ x in (A i ∩ B), (1 : ENNReal) ∂μ :=
      MeasureTheory.lintegral_indicator hAiB (fun _ => (1 : ENNReal))
    rw [h_eq1]
    exact MeasureTheory.setLIntegral_one (A i ∩ B)
  have h5 : ∫⁻ x, f x ∂μ = ∫⁻ x in B, f x ∂μ := by
    have h51 : (∫⁻ x, f x ∂μ) = (∫⁻ x, Set.indicator B f x ∂μ) := by
      congr <;> exact h_f_indicator
    rw [h51]
    exact MeasureTheory.lintegral_indicator hB f
  have hB' : NullMeasurableSet B μ := hB.nullMeasurableSet
  have h7 : ∫⁻ x in B, (k : ENNReal) ∂μ = (k : ENNReal) * μ B := by
    have h71 : (∫⁻ x in B, (k : ENNReal) ∂μ) = ∫⁻ a, Set.indicator B (fun _ : α => (k : ENNReal)) a ∂μ := by
      exact (MeasureTheory.lintegral_indicator hB (fun _ : α => (k : ENNReal))).symm
    rw [h71]
    exact MeasureTheory.lintegral_indicator_const₀ hB' (k : ENNReal)
  have h6 : ∫⁻ x in B, (k : ENNReal) ∂μ ≤ ∫⁻ x in B, f x ∂μ :=
    MeasureTheory.setLIntegral_mono' hB (fun x hx => h1 x hx)
  have h4 : (k : ENNReal) * μ B ≤ ∫⁻ x, f x ∂μ := by
    calc (k : ENNReal) * μ B
      = ∫⁻ x in B, (k : ENNReal) ∂μ := h7.symm
    _ ≤ ∫⁻ x in B, f x ∂μ := h6
    _ = ∫⁻ x, f x ∂μ := h5.symm
  rw [←hf_eq]
  exact h4

end Kakeya.Assouad
