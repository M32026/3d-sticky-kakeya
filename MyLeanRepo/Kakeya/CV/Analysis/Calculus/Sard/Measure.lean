module

public import MyLeanRepo.Kakeya.CV.Analysis.Calculus.Sard.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousLinearMap
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Tactic

@[expose] public section

namespace ForMathlib.Analysis.Calculus.Sard

open MeasureTheory
open scoped ContDiff

variable {m : ℕ} {f : EuclideanSpace ℝ (Fin m) → ℝ}

/-- The set of non-regular values is a subset of the image of the critical set. -/
lemma non_regular_values_subset_critical_image :
    {c : ℝ | ¬ IsRegularValue f c} ⊆ criticalValues f := by
  intro c hc
  simp only [IsRegularValue, Set.mem_setOf_eq] at hc
  push Not at hc
  rcases hc with ⟨x, hfx, hderiv⟩
  exact ⟨x, hderiv, hfx⟩

/-- If the image of the critical set has measure zero, then almost every `c` is a regular value. -/
lemma regular_value_ae_of_critical_image_null
    (h : volume (criticalValues f) = 0) :
    ∀ᵐ c ∂(volume : Measure ℝ), IsRegularValue f c := by
  have h1 : {c : ℝ | ¬ IsRegularValue f c} ⊆ criticalValues f :=
    non_regular_values_subset_critical_image
  have h2 : volume {c : ℝ | ¬ IsRegularValue f c} = 0 :=
    measure_mono_null h1 h
  exact h2

/-- If a set `s` has the property that every point `x ∈ s` has a neighborhood `U` such that
`f '' (s ∩ U)` has measure zero, then `f '' s` has measure zero. -/
lemma measure_zero_of_locally_null {X : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    {s : Set X} {f : X → ℝ}
    (h : ∀ x ∈ s, ∃ (U : Set X), U ∈ nhds x ∧ (volume : Measure ℝ) (f '' (s ∩ U)) = 0) :
    (volume : Measure ℝ) (f '' s) = 0 := by
  have h_main : ∀ (x : {x // x ∈ s}), ∃ (U : Set X), IsOpen U ∧ (x : X) ∈ U ∧
      (volume : Measure ℝ) (f '' (s ∩ U)) = 0 := by
    intro x
    have hx : (x : X) ∈ s := x.property
    rcases h (x : X) hx with ⟨U, hU_nhds, h_null⟩
    rcases mem_nhds_iff.mp hU_nhds with ⟨V, hV_sub, hV_open, hV_mem⟩
    have h_null2 : (volume : Measure ℝ) (f '' (s ∩ V)) = 0 := by
      have h_sub : s ∩ V ⊆ s ∩ U := by
        intro z hz
        exact ⟨hz.1, hV_sub hz.2⟩
      have h_img_sub : f '' (s ∩ V) ⊆ f '' (s ∩ U) := by
        intro z hz
        rcases hz with ⟨x, hx, rfl⟩
        have h_x_in : x ∈ s ∩ U := h_sub hx
        exact Set.mem_image_of_mem f h_x_in
      exact measure_mono_null h_img_sub h_null
    exact ⟨V, hV_open, hV_mem, h_null2⟩
  choose U hU_open hU_mem hU_null using h_main
  have h_cover : s ⊆ ⋃ x : {x // x ∈ s}, U x := by
    intro y hy
    let y' : {x // x ∈ s} := ⟨y, hy⟩
    have h : y ∈ U y' := hU_mem y'
    exact Set.mem_iUnion_of_mem y' h
  have h_secondCountable : SecondCountableTopology X := by infer_instance
  have h_all_open : ∀ (i : {x // x ∈ s}), IsOpen (U i) := hU_open
  obtain ⟨T, hT_count, hT_cover⟩ := TopologicalSpace.isOpen_iUnion_countable U h_all_open
  have h1 : f '' s ⊆ ⋃ t ∈ T, f '' (s ∩ U t) := by
    intro z hz
    rcases hz with ⟨x, hx, rfl⟩
    have hx_in_union : x ∈ ⋃ t ∈ T, U t := by
      rw [hT_cover]
      exact h_cover hx
    rcases Set.mem_iUnion₂.mp hx_in_union with ⟨t, ht, hxt⟩
    have h_x_in_inter : x ∈ s ∩ U t := ⟨hx, hxt⟩
    have h_z_in_image : f x ∈ f '' (s ∩ U t) := Set.mem_image_of_mem f h_x_in_inter
    exact Set.mem_iUnion₂.mpr ⟨t, ht, h_z_in_image⟩
  have h2 : ∀ t ∈ T, (volume : Measure ℝ) (f '' (s ∩ U t)) = 0 := by
    intro t _
    exact hU_null t
  have h3 : (volume : Measure ℝ) (⋃ t ∈ T, f '' (s ∩ U t)) = 0 := by
    exact measure_biUnion_null_iff hT_count |>.mpr h2
  exact measure_mono_null h1 h3


end ForMathlib.Analysis.Calculus.Sard
