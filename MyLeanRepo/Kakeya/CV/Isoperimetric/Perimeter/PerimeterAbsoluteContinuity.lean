import MyLeanRepo.Kakeya.CV.Isoperimetric.Measure.UpperDensityAbsoluteContinuity
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.PerimeterDensityUpperBound
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.PerimeterMeasureSupport
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.RBCEasyLemmas
import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import Mathlib.Tactic


open MeasureTheory Metric Set ENNReal
open scoped MeasureTheory

namespace Geometry

variable {n' : ℕ}

theorem perimeterMeasure_absolutelyContinuous_hausdorff
    {U : Set (E n')} (hU : IsOpen U) (hBdd : Bornology.IsBounded U)
    (h_perim_finite : Perimeter.perimeter U < ⊤) (hn : 2 ≤ n') :
    Perimeter.perimeterMeasure U ≪ μHE[n' - 1].restrict (frontier U) := by
  let d : ℕ := n' - 1
  have hd_pos : 0 < d := by omega
  let μ := Perimeter.perimeterMeasure U
  have h_perim_eq : μ Set.univ = Perimeter.perimeter U :=
    (Perimeter.perimeter_eq_variation U h_perim_finite).symm
  have hμ_finite : μ Set.univ < ⊤ := by
    rw [h_perim_eq]; exact h_perim_finite
  letI h_fin : IsFiniteMeasure μ := ⟨hμ_finite⟩
  have h_density_ae : ∀ᵐ (x : E n') ∂μ,
      ∃ (C : ℝ) (r0 : ℝ), 0 < C ∧ 0 < r0 ∧
        ∀ r, 0 < r → r < r0 →
          Perimeter.perimeterIn U (ball x r) ≤ ENNReal.ofReal (C * r ^ d) :=
    StructureTheorem.perimeter_density_upper_bound hU hBdd h_perim_finite hn
  let G : Set (E n') := {x | ∃ (C : ℝ) (r0 : ℝ), 0 < C ∧ 0 < r0 ∧
        ∀ r, 0 < r → r < r0 →
          Perimeter.perimeterIn U (ball x r) ≤ ENNReal.ofReal (C * r ^ d)}
  have hG_null : μ Gᶜ = 0 := h_density_ae
  have h_closedBall_bound : ∀ x ∈ G, ∃ (C' : ℝ) (r0' : ℝ), 0 < C' ∧ 0 < r0' ∧
      ∀ r, 0 < r → r < r0' →
        μ (closedBall x r) ≤ ENNReal.ofReal (C' * r ^ d) := by
    intro x hx
    rcases hx with ⟨C, r0, hC_pos, hr0_pos, hbound⟩
    exact StructureTheorem.upper_bound_perimeterMeasure_from_perimeterIn
      h_perim_finite hC_pos hr0_pos hbound hn
  have h_support : μ (frontier U)ᶜ = 0 :=
    Perimeter.perimeterMeasure_support_frontier hU
  refine' Measure.AbsolutelyContinuous.mk fun B hB hμH => _
  have h_frontier_meas : MeasurableSet (frontier U) := isClosed_frontier.measurableSet
  have h10 : μHE[d] (B ∩ frontier U) = 0 := by
    have h_restrict : μHE[d].restrict (frontier U) B = μHE[d] (B ∩ frontier U) :=
      Measure.restrict_apply hB
    rw [h_restrict] at hμH
    exact hμH
  have h11 : B ∩ frontier U = frontier U ∩ B := by ext x; simp [and_comm]
  have h1 : μHE[d] (frontier U ∩ B) = 0 := by
    rw [←h11]
    exact h10
  have h6 : μ (B \ frontier U) = 0 := by
    have h7 : B \ frontier U ⊆ (frontier U)ᶜ := by simp
    exact measure_mono_null h7 h_support
  have hB_diff_meas : MeasurableSet (B \ frontier U) := hB.diff h_frontier_meas
  have h_disj : Disjoint (B ∩ frontier U) (B \ frontier U) := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    simp only [Set.mem_inter_iff, Set.mem_sdiff] at hx1 hx2
    exact hx2.2 hx1.2
  have h_union : (B ∩ frontier U) ∪ (B \ frontier U) = B := by
    ext x; simp [and_comm] <;> tauto
  have h2 : μ B = μ (frontier U ∩ B) := by
    have h_comm : B ∩ frontier U = frontier U ∩ B := by ext x; simp [and_comm]
    calc μ B
      = μ ((B ∩ frontier U) ∪ (B \ frontier U)) := by congr; exact h_union.symm
    _ = μ (B ∩ frontier U) + μ (B \ frontier U) := measure_union h_disj hB_diff_meas
    _ = μ (B ∩ frontier U) + 0 := by rw [h6]
    _ = μ (B ∩ frontier U) := by rw [add_zero]
    _ = μ (frontier U ∩ B) := by rw [h_comm]
  rw [h2]
  let S := frontier U ∩ B
  have hS1 : μHE[d] S = 0 := h1
  let A1 := S ∩ G
  let A2 := S ∩ Gᶜ
  have h_disj2 : Disjoint A1 A2 := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    simp only [A1, A2, Set.mem_inter_iff, Set.mem_compl_iff] at hx1 hx2
    exact hx2.2 hx1.2
  have h_union2 : A1 ∪ A2 = S := by
    ext x; simp [A1, A2, G] <;> tauto
  have h3 : μ S ≤ μ A1 + μ A2 := by
    calc μ S = μ (A1 ∪ A2) := by rw [h_union2]
         _ ≤ μ A1 + μ A2 := measure_union_le A1 A2
  have h5 : μ A2 = 0 :=
    measure_mono_null (show A2 ⊆ Gᶜ from by simp [A2]) hG_null
  set c : NNReal := (volume : Measure (E d)).addHaarScalarFactor
      (μH[d] : Measure (E d)) with hc
  have hc_ne_zero : c ≠ 0 := by
    rw [hc]
    exact MeasureTheory.Measure.addHaarScalarFactor_volume_hausdorffMeasure_ne_zero d
  have h_def : (μHE[d] : Measure (E n')) = c • μH[d] := by
    have h : (μHE[d] : Measure (E n')) =
        ((volume : Measure (E d)).addHaarScalarFactor (μH[d] : Measure (E d))) • μH[d] :=
      MeasureTheory.Measure.euclideanHausdorffMeasure_def (X := E n') d
    have hc' : c = (volume : Measure (E d)).addHaarScalarFactor (μH[d] : Measure (E d)) := by
      exact hc.symm
    rw [hc']
    exact h
  have h_eval : μHE[d] A1 = (c : ENNReal) * μH[d] A1 := by
    rw [h_def]
    exact Measure.coe_nnreal_smul_apply c μH[d] A1
  have h8 : μHE[d] A1 = 0 :=
    measure_mono_null (show A1 ⊆ S from by simp [A1]) hS1
  have h9 : (c : ENNReal) * μH[d] A1 = 0 := by
    rw [←h_eval]; exact h8
  have h10 : (c : ENNReal) ≠ 0 := by exact_mod_cast hc_ne_zero
  have h7 : μH[d] A1 = 0 :=
    (mul_eq_zero.mp h9).resolve_left h10
  have h_density_A1 : ∀ x ∈ A1, ∃ (C : ℝ) (r0 : ℝ), 0 < C ∧ 0 < r0 ∧
      ∀ (r : ℝ), 0 < r → r < r0 → μ (closedBall x r) ≤ ENNReal.ofReal (C * r ^ d) := by
    intro x hx
    exact h_closedBall_bound x (hx.2)
  have h6 : μ A1 = 0 :=
    measure_null_of_upper_density hd_pos h_density_A1 h7
  have h9' : μ S ≤ 0 := by
    calc μ S ≤ μ A1 + μ A2 := h3
         _ = 0 + 0 := by rw [h6, h5] <;> rfl
         _ = 0 := by simp
  exact le_zero_iff.mp h9'

end Geometry
