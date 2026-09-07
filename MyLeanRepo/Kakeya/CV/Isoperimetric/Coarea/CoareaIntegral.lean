/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kestrel
-/

import MyLeanRepo.Kakeya.CV.Isoperimetric.Coarea.DistanceCoareaEq
import MyLeanRepo.Kakeya.CV.Isoperimetric.Measure.LevelSetMeasurability
import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import Mathlib.Tactic


open MeasureTheory Metric Set ENNReal Filter
open scoped MeasureTheory

namespace Geometry.Perimeter

variable {n : ℕ}

/-- **Distance coarea integral formula**.

For a closed nonempty set `C`, a bounded measurable set `A` away from `C`,
and a measurable function `g : ℝ → ENNReal`,

`∫⁻ x in A, g(infDist x C) = ∫⁻ t, g t * μHE[n-1]{x ∈ A | infDist x C = t}`.

This is the layer-cake / coarea representation used to evaluate
radial integrals by integrating over level sets. -/
lemma coarea_integral (hn : 2 ≤ n)
    {C : Set (E n)} (hC : IsClosed C) (hne : C.Nonempty)
    {A : Set (E n)} (hA : MeasurableSet A) (hA_bdd : Bornology.IsBounded A)
    (hA_sub : A ⊆ {x | 0 < infDist x C})
    {g : ℝ → ENNReal} (hg : Measurable g) :
    ∫⁻ x in A, g (infDist x C) ∂volume =
      ∫⁻ t, g t * μHE[n - 1] {x ∈ A | infDist x C = t} ∂volume := by
  let d : E n → ℝ := fun x => infDist x C
  let μ_map : Measure ℝ := Measure.map d (volume.restrict A)
  let H : ℝ → ENNReal := fun t => μHE[n - 1] {x ∈ A | d x = t}
  let ν : Measure ℝ := volume.withDensity H
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (by linarith)
  have hd_meas : Measurable d := (Metric.continuous_infDist_pt C).measurable
  have h_d_meas : FunctionLevelMeasurable d :=
    functionLevelMeasurable_of_lipschitz hn (Metric.lipschitz_infDist_pt (s := C))
  have h_eq_Ioc : ∀ (a b : ℝ), a < b → μ_map (Set.Ioc a b) = ν (Set.Ioc a b) := by
    intro a b hab
    have h1 : μ_map (Set.Ioc a b) = volume {x ∈ A | a < d x ∧ d x ≤ b} := by
      rw [Measure.map_apply hd_meas measurableSet_Ioc]
      have h_restrict : (volume.restrict A) (d ⁻¹' (Set.Ioc a b)) = volume (d ⁻¹' (Set.Ioc a b) ∩ A) :=
        Measure.restrict_apply (hd_meas measurableSet_Ioc)
      rw [h_restrict]
      have h_set : d ⁻¹' (Set.Ioc a b) ∩ A = {x ∈ A | a < d x ∧ d x ≤ b} := by
        ext x; simp [Set.mem_preimage, Set.mem_Ioc] <;> tauto
      rw [h_set]
    have h2 : ν (Set.Ioc a b) = ∫⁻ s in Set.Ioc a b, H s := by
      simpa [ν] using rfl
    rw [h1, h2]
    exact distance_coarea_eq hn hC hne h_d_meas hA hA_bdd hA_sub hab
  let C_set : Set (Set ℝ) := {S | ∃ l u, l < u ∧ Set.Ioc l u = S}
  have h_pi : IsPiSystem C_set := isPiSystem_Ioc (fun x : ℝ => x) (fun x : ℝ => x)
  have h_borel : borel ℝ = MeasurableSpace.generateFrom C_set := borel_eq_generateFrom_Ioc ℝ
  let c₀ : E n := Classical.choose hne
  have hc0 : c₀ ∈ C := Classical.choose_spec hne
  have hne' : C.Nonempty := ⟨c₀, hc0⟩
  have h_exists_R : ∃ (R : ℝ), ∀ x ∈ A, dist x c₀ ≤ R := by
    rcases hA_bdd.subset_ball c₀ with ⟨R, hR⟩
    refine ⟨R, fun x hx => (hR hx).le⟩
  rcases h_exists_R with ⟨R, hR⟩
  let M : ℝ := max R 0
  have h_bdd_d : ∀ x ∈ A, d x ≤ M := by
    intro x hx
    have h2 : d x ≤ dist x c₀ := Metric.infDist_le_dist_of_mem hc0
    have h3 : dist x c₀ ≤ R := hR x hx
    exact h2.trans (h3.trans (le_max_left R 0))
  let a0 : ℝ := -1
  let b0 : ℝ := M + 1
  have h_support : ∀ (t : ℝ), t ∉ Set.Ioc a0 b0 → H t = 0 := by
    intro t ht
    have h3 : t ≤ a0 ∨ b0 < t := by
      have h4 : ¬(a0 < t ∧ t ≤ b0) := ht
      by_cases h5 : t ≤ a0
      · exact Or.inl h5
      · have h6 : a0 < t := by linarith
        have h7 : ¬(t ≤ b0) := by intro h8; exact h4 ⟨h6, h8⟩
        have h9 : b0 < t := by linarith
        exact Or.inr h9
    rcases h3 with (h3 | h3)
    · have h4 : {x ∈ A | d x = t} = ∅ := by
        ext x
        simp only [Set.mem_empty_iff_false, iff_false]
        intro hx
        have h5 : d x = t := hx.2
        have h6 : 0 < d x := hA_sub hx.1
        rw [h5] at h6
        linarith
      have hH : H t = μHE[n - 1] {x ∈ A | d x = t} := by rfl
      rw [hH, h4] <;> simp
    · have h4 : {x ∈ A | d x = t} = ∅ := by
        ext x
        simp only [Set.mem_empty_iff_false, iff_false]
        intro hx
        have h5 : d x = t := hx.2
        have h6 : d x ≤ M := h_bdd_d x hx.1
        rw [h5] at h6
        linarith
      have hH : H t = μHE[n - 1] {x ∈ A | d x = t} := by rfl
      rw [hH, h4] <;> simp
  have h_Ioc_meas : MeasurableSet (Set.Ioc a0 b0) := measurableSet_Ioc
  have h_compl_meas : MeasurableSet (Set.Ioc a0 b0)ᶜ := h_Ioc_meas.compl
  have h_μmap_supp : μ_map (Set.Ioc a0 b0)ᶜ = 0 := by
    rw [Measure.map_apply hd_meas h_compl_meas]
    have h_empty : d ⁻¹' ((Set.Ioc a0 b0)ᶜ) ∩ A = ∅ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false]
      intro ⟨hx1, hx2⟩
      have h_pos : 0 < d x := hA_sub hx2
      have h_le : d x ≤ M := h_bdd_d x hx2
      have h_in : d x ∈ Set.Ioc a0 b0 := ⟨by linarith, by linarith⟩
      exact hx1 h_in
    rw [Measure.restrict_apply (hd_meas h_compl_meas), h_empty] <;> simp
  have h1 : μ_map Set.univ = μ_map (Set.Ioc a0 b0) := by
    have h_disj : Disjoint (Set.Ioc a0 b0) (Set.Ioc a0 b0)ᶜ := disjoint_compl_right
    have h_union : (Set.Ioc a0 b0) ∪ (Set.Ioc a0 b0)ᶜ = Set.univ := by simp
    have h : μ_map ((Set.Ioc a0 b0) ∪ (Set.Ioc a0 b0)ᶜ) = μ_map (Set.Ioc a0 b0) + μ_map (Set.Ioc a0 b0)ᶜ := by
      exact measure_union h_disj h_compl_meas
    have h' : μ_map Set.univ = μ_map (Set.Ioc a0 b0) + μ_map (Set.Ioc a0 b0)ᶜ := by
      rw [← h_union] <;> exact h
    rw [h', h_μmap_supp] <;> simp
  have h_ab : a0 < b0 := by
    dsimp only [a0, b0, M] <;> linarith [le_max_right R 0]
  have h2 : μ_map (Set.Ioc a0 b0) < ⊤ := by
    have h_eq2 : μ_map (Set.Ioc a0 b0) = volume {x ∈ A | a0 < d x ∧ d x ≤ b0} := by
      rw [Measure.map_apply hd_meas measurableSet_Ioc]
      have h_restrict : (volume.restrict A) (d ⁻¹' (Set.Ioc a0 b0)) = volume (d ⁻¹' (Set.Ioc a0 b0) ∩ A) :=
        Measure.restrict_apply (hd_meas measurableSet_Ioc)
      rw [h_restrict]
      have h_set : d ⁻¹' (Set.Ioc a0 b0) ∩ A = {x ∈ A | a0 < d x ∧ d x ≤ b0} := by
        ext x; simp [Set.mem_preimage, Set.mem_Ioc] <;> tauto
      rw [h_set]
    rw [h_eq2]
    have h_sub : {x ∈ A | a0 < d x ∧ d x ≤ b0} ⊆ A := fun y hy => hy.1
    have h_set_bdd : Bornology.IsBounded {x ∈ A | a0 < d x ∧ d x ≤ b0} := by exact Bornology.IsBounded.subset hA_bdd h_sub
    exact Bornology.IsBounded.measure_lt_top h_set_bdd
  have hμ_finite : IsFiniteMeasure μ_map := by
    refine' ⟨_⟩
    rw [h1]
    exact h2
  have h_ν_supp : ν (Set.Ioc a0 b0)ᶜ = 0 := by
    have h : ∀ t ∈ (Set.Ioc a0 b0)ᶜ, H t = 0 := fun t ht => h_support t ht
    have h6 : ν ((Set.Ioc a0 b0)ᶜ) = ∫⁻ t in (Set.Ioc a0 b0)ᶜ, H t := by exact withDensity_apply' H (Ioc a0 b0)ᶜ
    rw [h6]
    have h7 : ∫⁻ t in (Set.Ioc a0 b0)ᶜ, H t = 0 := by
      rw [MeasureTheory.setLIntegral_congr_fun h_compl_meas (fun t ht => h t ht)] <;> simp
    exact h7
  have h_univ : μ_map Set.univ = ν Set.univ := by
    have h2 : ν Set.univ = ν (Set.Ioc a0 b0) := by
      have h_disj : Disjoint (Set.Ioc a0 b0) (Set.Ioc a0 b0)ᶜ := disjoint_compl_right
      have h_union : (Set.Ioc a0 b0) ∪ (Set.Ioc a0 b0)ᶜ = Set.univ := by simp
      have h : ν ((Set.Ioc a0 b0) ∪ (Set.Ioc a0 b0)ᶜ) = ν (Set.Ioc a0 b0) + ν (Set.Ioc a0 b0)ᶜ := by exact measure_union h_disj h_compl_meas
      have h' : ν Set.univ = ν (Set.Ioc a0 b0) + ν (Set.Ioc a0 b0)ᶜ := by
        rw [← h_union] <;> exact h
      rw [h', h_ν_supp] <;> simp
    rw [h1, h2, h_eq_Ioc a0 b0 h_ab]
  let _i : IsFiniteMeasure μ_map := hμ_finite
  have h_eq : μ_map = ν := by
    exact MeasureTheory.ext_of_generate_finite C_set h_borel h_pi
      (fun s hs => by rcases hs with ⟨l, u, hlu, rfl⟩; exact h_eq_Ioc l u hlu) h_univ
  have h_main1 : ∫⁻ x in A, g (d x) ∂volume = ∫⁻ t, g t ∂μ_map := by
    have h : ∫⁻ t, g t ∂μ_map = ∫⁻ x, g (d x) ∂(volume.restrict A) := by exact lintegral_map hg hd_meas
    have h' : ∫⁻ x in A, g (d x) ∂volume = ∫⁻ x, g (d x) ∂(volume.restrict A) := by exact setLIntegral_congr_fun hA fun ⦃x⦄ => congrFun rfl
    rw [h']
    exact h.symm
  rw [h_main1, h_eq]
  have h1 : AEMeasurable H (volume.restrict (Set.Ioc a0 b0)) := h_d_meas A hA a0 b0
  let H' := h1.mk H
  have hH'_meas : Measurable H' := h1.measurable_mk
  have h_eq1 : H =ᵐ[volume.restrict (Set.Ioc a0 b0)] H' := h1.ae_eq_mk
  have hIoc : MeasurableSet (Set.Ioc a0 b0) := by exact measurableSet_Ioc
  let H'' := (Set.Ioc a0 b0).indicator H'
  have hH''_meas : Measurable H'' := hH'_meas.indicator hIoc
  have h_eq2 : H =ᵐ[volume] H'' := by
    have h3 : ∀ᵐ (t : ℝ) ∂volume, t ∈ Set.Ioc a0 b0 → H t = H' t := by exact (ae_restrict_iff' h_Ioc_meas).mp h_eq1
    filter_upwards [h3] with t ht
    by_cases h4 : t ∈ Set.Ioc a0 b0
    · have h5 : H t = H' t := ht h4
      simpa [H'', h4] using h5
    · have h6 : H t = 0 := h_support t h4
      simpa [H'', h4] using h6
  have hH_ae : AEMeasurable H volume :=
    hH''_meas.aemeasurable.congr h_eq2.symm
  have h_main2 : ∫⁻ t, g t ∂ν = ∫⁻ t, g t * H t ∂volume := by
    have h : ∫⁻ t, g t ∂ν = ∫⁻ t, (H * g) t ∂volume :=
      MeasureTheory.lintegral_withDensity_eq_lintegral_mul₀' hH_ae hg.aemeasurable
    rw [h]
    have h4 : (fun t => (H * g) t) = fun t => g t * H t := by
      funext t; exact mul_comm (H t) (g t)
    rw [h4]
  exact h_main2

end Geometry.Perimeter
