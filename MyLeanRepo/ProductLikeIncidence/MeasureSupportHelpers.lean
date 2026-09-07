module

/-
# Measure Support Helpers

Simple lemmas about measure supports needed by the incidence-to-ring endgame.

## Main results

- `support_smul_eq`: support of a nonzero scalar multiple of a measure equals the original support.
- `support_dirac_eq`: support of `Measure.dirac a` is `{a}` in a T1 space.
- `support_finset_sum`: support of a finite sum of measures is the union of their supports.
- `support_uniform_finset`: support of uniform measure on a nonempty finset is the finset itself.

## Dependencies

Only `Mathlib`.
-/

public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open scoped Topology
open MeasureTheory Measure

/-- Support of a nonzero scalar multiple of a measure equals the original support. -/
lemma support_smul_eq {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    {c : ENNReal} {μ : Measure α} (hc : c ≠ 0) :
    (c • μ).support = μ.support := by
  ext x
  have h1 : ∀ (U : Set α), U ∈ 𝓝 x → (0 < (c • μ) U ↔ 0 < μ U) := by
    intro U _
    have h2 : (c • μ) U = c * μ U := by exact EReal.coe_ennreal_eq_coe_ennreal_iff.mp rfl
    rw [h2]
    constructor
    · intro h
      by_contra h6
      have h7 : μ U = 0 := by simpa [not_lt] using h6
      rw [h7] at h
      simp at h
    · intro h
      exact ENNReal.mul_pos hc (ne_of_gt h)
  simpa [Measure.mem_support_iff_forall] using forall₂_congr h1

/-- Support of `Measure.dirac a` is `{a}` in a T1 space. -/
lemma support_dirac_eq {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] [T1Space α] (a : α) :
    (Measure.dirac a).support = {a} := by
  ext x
  simp only [Measure.mem_support_iff_forall, Set.mem_singleton_iff]
  constructor
  · intro h
    by_contra hxa
    have h_closed : IsClosed ({a} : Set α) := isClosed_singleton
    have h_open : IsOpen (({a} : Set α)ᶜ) := h_closed.isOpen_compl
    have h_meas : MeasurableSet (({a} : Set α)ᶜ) := h_open.measurableSet
    have hxa' : x ∉ ({a} : Set α) := by
      simpa [Set.mem_singleton_iff] using hxa
    have h_nhds : ({a} : Set α)ᶜ ∈ 𝓝 x := h_open.mem_nhds hxa'
    have h_pos : 0 < (Measure.dirac a) (({a} : Set α)ᶜ) := h (({a} : Set α)ᶜ) h_nhds
    have h_notin : a ∉ (({a} : Set α)ᶜ) := by simp
    have h_zero : (Measure.dirac a) (({a} : Set α)ᶜ) = 0 := by
      rw [Measure.dirac_apply' a h_meas]
      <;> simp [h_notin]
    rw [h_zero] at h_pos
    <;> simp at h_pos
  · intro hx
    have hxa : x = a := by simpa using hx
    rw [hxa]
    intro U hU
    have ha : a ∈ U := mem_of_mem_nhds hU
    rw [Measure.dirac_apply_of_mem ha]
    <;> norm_num

/-- Support of a finite sum of measures is the union of their supports. -/
lemma support_finset_sum {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {μ : ι → Measure α} :
    (∑ i ∈ s, μ i).support = ⋃ i ∈ s, (μ i).support := by
  ext x
  simp only [Measure.mem_support_iff_forall, Set.mem_iUnion]
  constructor
  · -- If x ∈ support of sum, then x ∈ support of some μ i
    intro h
    by_contra h'
    have h_exists : ∀ i ∈ s, ∃ (V : Set α), V ∈ 𝓝 x ∧ (μ i) V = 0 := by
      intro i hi
      have h_not : ¬(∀ (W : Set α), W ∈ 𝓝 x → 0 < (μ i) W) := by
        intro h_all
        exact h' ⟨i, hi, h_all⟩
      rcases not_forall₂.mp h_not with ⟨W, hW, hnotpos⟩
      have h_zero : (μ i) W = 0 := by simpa [not_lt] using hnotpos
      exact ⟨W, hW, h_zero⟩
    let V : ι → Set α := fun i =>
      if hi : i ∈ s then
        Classical.choose (h_exists i hi)
      else Set.univ
    have hV_prop : ∀ i ∈ s, (V i ∈ 𝓝 x) ∧ (μ i) (V i) = 0 := by
      intro i hi
      dsimp only [V]
      rw [dif_pos hi]
      exact Classical.choose_spec (h_exists i hi)
    let U_int : Set α := ⋂ i ∈ s, V i
    have h_finite : Set.Finite (s : Set ι) := by exact Finset.finite_toSet s
    have hU_int_nhds : U_int ∈ 𝓝 x := by
      have h : (⋂ i ∈ s, V i) ∈ 𝓝 x :=
        (Filter.biInter_mem h_finite).mpr (fun i hi => (hV_prop i hi).1)
      exact h
    have h_all_zero : ∀ i ∈ s, (μ i) U_int = 0 := by
      intro i hi
      have h_sub : U_int ⊆ V i := by
        intro y hy
        have h_y : ∀ j ∈ s, y ∈ V j := by simpa [U_int] using hy
        exact h_y i hi
      have h_le : (μ i) U_int ≤ (μ i) (V i) := measure_mono h_sub
      have h_zero : (μ i) (V i) = 0 := (hV_prop i hi).2
      rw [h_zero] at h_le
      simpa using h_le
    have h_sum_zero : (∑ i ∈ s, μ i) U_int = 0 := by
      have h_eq : (∑ i ∈ s, μ i) U_int = ∑ i ∈ s, (μ i) U_int := by exact finsetSum_apply s μ U_int
      rw [h_eq]
      exact Finset.sum_eq_zero h_all_zero
    have h_pos : 0 < (∑ i ∈ s, μ i) U_int := h U_int hU_int_nhds
    rw [h_sum_zero] at h_pos
    <;> simp at h_pos
  · -- If x ∈ support of some μ i, then x ∈ support of sum
    rintro ⟨i, hi, hx⟩
    intro U hU
    have h_pos : 0 < (μ i) U := hx U hU
    let f : ι → ENNReal := fun j => (μ j) U
    have h_nonneg : ∀ j ∈ s, 0 ≤ f j := by intro j _; exact zero_le
    have h_le : f i ≤ ∑ j ∈ s, f j := Finset.single_le_sum h_nonneg hi
    have h_eq : (∑ j ∈ s, μ j) U = ∑ j ∈ s, f j := by exact finsetSum_apply s μ U
    rw [h_eq]
    exact lt_of_lt_of_le h_pos h_le

/-- Support of uniform measure on a nonempty finset is the finset itself. -/
lemma support_uniform_finset {α : Type*} [TopologicalSpace α] [MeasurableSpace α]
    [OpensMeasurableSpace α] [T1Space α] [DecidableEq α] {S : Finset α} (hS : S.Nonempty) :
    (∑ p ∈ S, (1 / (S.card : ENNReal)) • Measure.dirac p).support = (S : Set α) := by
  have h_card_pos : 0 < S.card := by exact Finset.Nonempty.card_pos hS
  have h₁ : (S.card : ENNReal) ≠ 0 := by exact_mod_cast h_card_pos.ne'
  have h₂ : (S.card : ENNReal) ≠ ⊤ := by exact ENNReal.natCast_ne_top S.card
  have h_ne_zero : (1 / (S.card : ENNReal)) ≠ 0 := by
    have h₃ : 0 < (1 / (S.card : ENNReal)) := by
      rw [ENNReal.div_pos_iff] <;> simp [h₁, h₂] <;> norm_num
    exact ne_of_gt h₃
  have h_main : (∑ p ∈ S, (1 / (S.card : ENNReal)) • Measure.dirac p).support =
      ⋃ p ∈ S, ((1 / (S.card : ENNReal)) • Measure.dirac p).support :=
    support_finset_sum
  rw [h_main]
  have h_each : ∀ p ∈ S, ((1 / (S.card : ENNReal)) • Measure.dirac p).support = {p} := by
    intro p _
    rw [support_smul_eq h_ne_zero, support_dirac_eq p]
  ext z
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨p, hp, hz⟩
    rw [h_each p hp] at hz
    have hz' : z = p := by simpa using hz
    rw [hz']
    exact hp
  · intro hz
    refine ⟨z, hz, ?_⟩
    rw [h_each z hz]
    simp

end
