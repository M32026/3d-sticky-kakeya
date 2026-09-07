import MyLeanRepo.Kakeya.CV.Geometry
import Mathlib.Topology.Constructions
import Mathlib.Topology.Order.OrderClosed

/-!
# Frontier sum bound for polynomial sublevel sets

Topological frontier inclusions and measure bounds for the sum of frontier
measures of complementary polynomial sublevel sets inside the unit ball.

Extracted from `Targets.ManyBisections.Frontier` as a production dependency
free of Targets imports and forbidden tokens.

Main result: `measure_frontier_sum_bound`.
-/

noncomputable section

open Set MeasureTheory Metric
open scoped ENNReal

namespace Kakeya.CV

section FrontierInclusions

/-- Frontier of sublevel set inside open ball lies on zero set. -/
lemma frontier_inter_open {f : Point 3 → ℝ} (hf : Continuous f) :
    frontier (unitBall 3 ∩ {x | f x ≤ 0}) ∩ Metric.ball (0 : Point 3) 1 ⊆ {x | f x = 0} := by
  set E := unitBall 3 ∩ {x | f x ≤ 0} with hE_def
  set U := Metric.ball (0 : Point 3) 1 with hU_def
  have hU_open : IsOpen U := Metric.isOpen_ball
  have hU_sub : U ⊆ unitBall 3 := by
    intro x hx
    have h : dist x (0 : Point 3) < 1 := Metric.mem_ball.mp hx
    simpa [unitBall, Metric.mem_closedBall] using h.le
  have hEq : E ∩ U = {x | f x ≤ 0} ∩ U := by
    ext x
    simp only [hE_def, mem_inter_iff, mem_setOf_eq]
    constructor
    · rintro ⟨⟨hball, hle⟩, hU⟩
      exact ⟨hle, hU⟩
    · rintro ⟨hle, hU⟩
      exact ⟨⟨hU_sub hU, hle⟩, hU⟩
  have h21 : frontier (E ∩ U) ∩ U = frontier E ∩ U := frontier_inter_open_inter hU_open
  have h22 : frontier ({x | f x ≤ 0} ∩ U) ∩ U = frontier {x | f x ≤ 0} ∩ U :=
    frontier_inter_open_inter hU_open
  have h2 : frontier E ∩ U = frontier {x | f x ≤ 0} ∩ U := by
    calc
      frontier E ∩ U
        = frontier (E ∩ U) ∩ U := h21.symm
      _ = frontier ({x | f x ≤ 0} ∩ U) ∩ U := by rw [hEq]
      _ = frontier {x | f x ≤ 0} ∩ U := h22
  have h3 : frontier {x | f x ≤ 0} ⊆ {x | f x = 0} :=
    frontier_le_subset_eq hf continuous_const
  have h4 : (frontier {x | f x ≤ 0} ∩ U) ⊆ frontier {x | f x ≤ 0} :=
    Set.inter_subset_left
  have h5 : (frontier {x | f x ≤ 0} ∩ U) ⊆ {x | f x = 0} := subset_trans h4 h3
  rw [h2]
  exact h5

/-- Frontier of superlevel set inside open ball lies on zero set. -/
lemma frontier_inter_open' {f : Point 3 → ℝ} (hf : Continuous f) :
    frontier (unitBall 3 ∩ {x | f x ≥ 0}) ∩ Metric.ball (0 : Point 3) 1 ⊆ {x | f x = 0} := by
  set E := unitBall 3 ∩ {x | f x ≥ 0} with hE_def
  set U := Metric.ball (0 : Point 3) 1 with hU_def
  have hU_open : IsOpen U := Metric.isOpen_ball
  have hU_sub : U ⊆ unitBall 3 := by
    intro x hx
    have h : dist x (0 : Point 3) < 1 := Metric.mem_ball.mp hx
    simpa [unitBall, Metric.mem_closedBall] using h.le
  have hEq : E ∩ U = {x | f x ≥ 0} ∩ U := by
    ext x
    simp only [hE_def, mem_inter_iff, mem_setOf_eq]
    constructor
    · rintro ⟨⟨hball, hge⟩, hU⟩
      exact ⟨hge, hU⟩
    · rintro ⟨hge, hU⟩
      exact ⟨⟨hU_sub hU, hge⟩, hU⟩
  have h21 : frontier (E ∩ U) ∩ U = frontier E ∩ U := frontier_inter_open_inter hU_open
  have h22 : frontier ({x | f x ≥ 0} ∩ U) ∩ U = frontier {x | f x ≥ 0} ∩ U :=
    frontier_inter_open_inter hU_open
  have h2 : frontier E ∩ U = frontier {x | f x ≥ 0} ∩ U := by
    calc
      frontier E ∩ U
        = frontier (E ∩ U) ∩ U := h21.symm
      _ = frontier ({x | f x ≥ 0} ∩ U) ∩ U := by rw [hEq]
      _ = frontier {x | f x ≥ 0} ∩ U := h22
  have h_compl : frontier {x | f x ≥ 0} = frontier {x | f x < 0} := by
    have h_set : {x : Point 3 | f x ≥ 0} = {x : Point 3 | f x < 0}ᶜ := by
      ext x; simp
    rw [h_set, frontier_compl]
  rw [h2, h_compl]
  have h3 : frontier {x | f x < 0} ⊆ {x | f x = 0} :=
    frontier_lt_subset_eq hf continuous_const
  have h4 : (frontier {x | f x < 0} ∩ U) ⊆ frontier {x | f x < 0} :=
    Set.inter_subset_left
  exact subset_trans h4 h3

/-- Frontier on sphere lies in sublevel set. -/
lemma frontier_inter_sphere {f : Point 3 → ℝ} (hf : Continuous f) :
    frontier (unitBall 3 ∩ {x | f x ≤ 0}) ∩ unitSphere 3 ⊆ unitSphere 3 ∩ {x | f x ≤ 0} := by
  set E := unitBall 3 ∩ {x | f x ≤ 0} with hE_def
  have hE_closed : IsClosed E := by
    rw [hE_def]
    exact IsClosed.inter Metric.isClosed_closedBall (isClosed_le hf continuous_const)
  have h4 : frontier E ⊆ E := frontier_subset_iff_isClosed.mpr hE_closed
  have h5 : frontier E ∩ unitSphere 3 ⊆ E ∩ unitSphere 3 :=
    inter_subset_inter h4 Subset.rfl
  have hS_sub : unitSphere 3 ⊆ unitBall 3 := by
    intro x hx
    have h : dist x (0 : Point 3) = 1 := Metric.mem_sphere.mp hx
    simpa [unitBall, Metric.mem_closedBall] using h.le
  have h6 : E ∩ unitSphere 3 = unitSphere 3 ∩ {x | f x ≤ 0} := by
    ext x
    simp only [hE_def, mem_inter_iff, mem_setOf_eq]
    constructor
    · rintro ⟨⟨hball, hle⟩, hS⟩
      exact ⟨hS, hle⟩
    · rintro ⟨hS, hle⟩
      exact ⟨⟨hS_sub hS, hle⟩, hS⟩
  rw [h6] at h5
  exact h5

/-- Frontier on sphere lies in superlevel set. -/
lemma frontier_inter_sphere' {f : Point 3 → ℝ} (hf : Continuous f) :
    frontier (unitBall 3 ∩ {x | f x ≥ 0}) ∩ unitSphere 3 ⊆ unitSphere 3 ∩ {x | f x ≥ 0} := by
  set E := unitBall 3 ∩ {x | f x ≥ 0} with hE_def
  have hE_closed : IsClosed E := by
    rw [hE_def]
    exact IsClosed.inter Metric.isClosed_closedBall (isClosed_le continuous_const hf)
  have h4 : frontier E ⊆ E := frontier_subset_iff_isClosed.mpr hE_closed
  have h5 : frontier E ∩ unitSphere 3 ⊆ E ∩ unitSphere 3 :=
    inter_subset_inter h4 Subset.rfl
  have hS_sub : unitSphere 3 ⊆ unitBall 3 := by
    intro x hx
    have h : dist x (0 : Point 3) = 1 := Metric.mem_sphere.mp hx
    simpa [unitBall, Metric.mem_closedBall] using h.le
  have h6 : E ∩ unitSphere 3 = unitSphere 3 ∩ {x | f x ≥ 0} := by
    ext x
    simp only [hE_def, mem_inter_iff, mem_setOf_eq]
    constructor
    · rintro ⟨⟨hball, hge⟩, hS⟩
      exact ⟨hS, hge⟩
    · rintro ⟨hS, hge⟩
      exact ⟨⟨hS_sub hS, hge⟩, hS⟩
  rw [h6] at h5
  exact h5

end FrontierInclusions

section FrontierBounds

/-- Union of frontiers ⊆ sphere ∪ zero set. -/
lemma frontier_union_bound {f : Point 3 → ℝ} (hf : Continuous f) :
    frontier (unitBall 3 ∩ {x | f x ≤ 0}) ∪
    frontier (unitBall 3 ∩ {x | f x ≥ 0})
    ⊆ unitSphere 3 ∪ ({x | f x = 0} ∩ unitBall 3) := by
  set E := unitBall 3 ∩ {x | f x ≤ 0} with hE_def
  set F := unitBall 3 ∩ {x | f x ≥ 0} with hF_def
  set Z := {x | f x = 0} ∩ unitBall 3 with hZ_def
  have hE_sub2 : E ⊆ unitBall 3 := by
    intro x hx
    simp only [hE_def, mem_inter_iff] at hx
    exact hx.1
  have hE_sub : frontier E ⊆ unitBall 3 := by
    have h : frontier E ⊆ closure E := frontier_subset_closure
    have h' : closure E ⊆ unitBall 3 := closure_minimal hE_sub2 Metric.isClosed_closedBall
    exact subset_trans h h'
  have hF_sub2 : F ⊆ unitBall 3 := by
    intro x hx
    simp only [hF_def, mem_inter_iff] at hx
    exact hx.1
  have hF_sub : frontier F ⊆ unitBall 3 := by
    have h : frontier F ⊆ closure F := frontier_subset_closure
    have h' : closure F ⊆ unitBall 3 := closure_minimal hF_sub2 Metric.isClosed_closedBall
    exact subset_trans h h'
  intro x hx
  have hx_or : x ∈ frontier E ∨ x ∈ frontier F := by
    simpa [mem_union] using hx
  have hx_in : x ∈ unitBall 3 := by
    rcases hx_or with (h | h) <;> tauto
  by_cases hU : x ∈ Metric.ball (0 : Point 3) 1
  · have hz : f x = 0 := by
      rcases hx_or with (hE | hF)
      · exact frontier_inter_open hf ⟨hE, hU⟩
      · exact frontier_inter_open' hf ⟨hF, hU⟩
    exact Or.inr ⟨hz, hx_in⟩
  · have hS : x ∈ unitSphere 3 := by
      have h1 : ‖x‖ ≤ 1 := by
        simpa [unitBall, Metric.mem_closedBall] using hx_in
      have h2 : ¬‖x‖ < 1 := by simpa [Metric.mem_ball] using hU
      have h3 : ‖x‖ = 1 := by linarith
      simpa [unitSphere, Metric.mem_sphere] using h3
    exact Or.inl hS

/-- Intersection of frontiers ⊆ zero set. -/
lemma frontier_inter_bound {f : Point 3 → ℝ} (hf : Continuous f) :
    frontier (unitBall 3 ∩ {x | f x ≤ 0}) ∩
    frontier (unitBall 3 ∩ {x | f x ≥ 0})
    ⊆ {x | f x = 0} ∩ unitBall 3 := by
  set E := unitBall 3 ∩ {x | f x ≤ 0} with hE_def
  set F := unitBall 3 ∩ {x | f x ≥ 0} with hF_def
  set Z := {x | f x = 0} ∩ unitBall 3 with hZ_def
  have hE_sub2 : E ⊆ unitBall 3 := by
    intro x hx
    simp only [hE_def, mem_inter_iff] at hx
    exact hx.1
  have hE_sub : frontier E ⊆ unitBall 3 := by
    have h : frontier E ⊆ closure E := frontier_subset_closure
    have h' : closure E ⊆ unitBall 3 := closure_minimal hE_sub2 Metric.isClosed_closedBall
    exact subset_trans h h'
  intro x hx
  have hxE : x ∈ frontier E := hx.1
  have hxF : x ∈ frontier F := hx.2
  have hx_in : x ∈ unitBall 3 := hE_sub hxE
  by_cases hU : x ∈ Metric.ball (0 : Point 3) 1
  · have hz : f x = 0 := frontier_inter_open hf ⟨hxE, hU⟩
    exact ⟨hz, hx_in⟩
  · have hS : x ∈ unitSphere 3 := by
      have h1 : ‖x‖ ≤ 1 := by
        simpa [unitBall, Metric.mem_closedBall] using hx_in
      have h2 : ¬‖x‖ < 1 := by simpa [Metric.mem_ball] using hU
      have h3 : ‖x‖ = 1 := by linarith
      simpa [unitSphere, Metric.mem_sphere] using h3
    have hle : f x ≤ 0 := (frontier_inter_sphere hf ⟨hxE, hS⟩).2
    have hge : f x ≥ 0 := (frontier_inter_sphere' hf ⟨hxF, hS⟩).2
    have hz : f x = 0 := by linarith
    exact ⟨hz, hx_in⟩

/-- Sum of frontier measures ≤ sphere + 2 * zero set. -/
lemma measure_frontier_sum_bound {f : Point 3 → ℝ} (hf : Continuous f) :
    codimensionOneMeasure 3 (frontier (unitBall 3 ∩ {x | f x ≤ 0})) +
    codimensionOneMeasure 3 (frontier (unitBall 3 ∩ {x | f x ≥ 0})) ≤
    codimensionOneMeasure 3 (unitSphere 3) +
    2 * codimensionOneMeasure 3 ({x | f x = 0} ∩ unitBall 3) := by
  set E := unitBall 3 ∩ {x | f x ≤ 0} with hE_def
  set F := unitBall 3 ∩ {x | f x ≥ 0} with hF_def
  set Z := {x | f x = 0} ∩ unitBall 3 with hZ_def
  let μ := codimensionOneMeasure 3
  have hE_meas : MeasurableSet (frontier E) := isClosed_frontier.measurableSet
  have hF_meas : MeasurableSet (frontier F) := isClosed_frontier.measurableSet
  have h_union : frontier E ∪ frontier F ⊆ unitSphere 3 ∪ Z := frontier_union_bound hf
  have h_inter : frontier E ∩ frontier F ⊆ Z := frontier_inter_bound hf
  have h_sum : μ (frontier E) + μ (frontier F) =
      μ (frontier E ∪ frontier F) + μ (frontier E ∩ frontier F) := by
    exact (measure_union_add_inter (frontier E) hF_meas).symm
  rw [h_sum]
  have h3 : μ (frontier E ∪ frontier F) ≤ μ (unitSphere 3 ∪ Z) := measure_mono h_union
  have h4 : μ (frontier E ∩ frontier F) ≤ μ Z := measure_mono h_inter
  have h5 : μ (unitSphere 3 ∪ Z) ≤ μ (unitSphere 3) + μ Z := measure_union_le _ _
  calc
    μ (frontier E ∪ frontier F) + μ (frontier E ∩ frontier F)
      ≤ μ (unitSphere 3 ∪ Z) + μ Z := by gcongr
    _ ≤ μ (unitSphere 3) + μ Z + μ Z := by gcongr
    _ = μ (unitSphere 3) + 2 * μ Z := by
      simp [two_mul, add_assoc]

end FrontierBounds

end Kakeya.CV
