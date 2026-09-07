import MyLeanRepo.Kakeya.Assouad.Subunit.Statements
import MyLeanRepo.Kakeya.Streamlined.GeneralizedKatzTao.ProbabilisticThinning
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.TubeDensityTestNet.Proof
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.TubeVolume
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.CapsuleBounds
import MyLeanRepo.Kakeya.Assouad.AbsorptionHelpers
import MyLeanRepo.Kakeya.Assouad.ExtremalHelpers
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Frostman bounds for streamlined tube families

1. `frostman_cardinality_bound`: `V_rho ≤ C * F.enncard * V_δ`
2. `deltaMax_ge_one`: `1 ≤ deltaMax`
3. `frostman_global_deltaMax_bound`: `deltaMax ≤ C * F.enncard * V_δ / V_rho`
-/

noncomputable section

open Kakeya.Streamlined
open Kakeya.Streamlined.GeometricLemmas

namespace Kakeya.Assouad

/-- Convexity of a DeltaTube carrier. -/
private lemma tube_carrier_is_convex {δ : ℝ} (T : Kakeya.DeltaTube δ) :
    Convex ℝ T.carrier := by
  have h_seg : Convex ℝ (Kakeya.unitSegment T.base T.direction) := by
    intro x hx y hy a b ha hb hab
    rcases hx with ⟨s, hs, rfl⟩
    rcases hy with ⟨t, ht, rfl⟩
    have h_comb : a • (T.base + s • T.direction) + b • (T.base + t • T.direction) =
        T.base + (a * s + b * t) • T.direction := by
      have h1 : a • (T.base + s • T.direction) = a • T.base + (a * s) • T.direction := by
        rw [smul_add, smul_smul]
      have h2 : b • (T.base + t • T.direction) = b • T.base + (b * t) • T.direction := by
        rw [smul_add, smul_smul]
      rw [h1, h2]
      have h3 : a • T.base + (a * s) • T.direction + (b • T.base + (b * t) • T.direction) =
          (a + b) • T.base + (a * s + b * t) • T.direction := by
        rw [add_smul, add_smul] <;> abel
      rw [h3, hab] <;> simp
    have h_s1 : 0 ≤ s := hs.1
    have h_s2 : s ≤ 1 := hs.2
    have h_t1 : 0 ≤ t := ht.1
    have h_t2 : t ≤ 1 := ht.2
    have h_low : 0 ≤ a * s + b * t := by
      exact add_nonneg (mul_nonneg ha h_s1) (mul_nonneg hb h_t1)
    have h_high : a * s + b * t ≤ 1 := by
      have h1 : a * s ≤ a := by
        calc a * s ≤ a * 1 := by exact mul_le_mul_of_nonneg_left h_s2 ha
             _ = a := by ring
      have h2 : b * t ≤ b := by
        calc b * t ≤ b * 1 := by exact mul_le_mul_of_nonneg_left h_t2 hb
             _ = b := by ring
      linarith [hab]
    have hst_in : a * s + b * t ∈ Set.Icc (0 : ℝ) 1 := ⟨h_low, h_high⟩
    exact ⟨a * s + b * t, hst_in, h_comb.symm⟩
  exact h_seg.cthickening δ

/-- All fine tubes have the canonical volume. -/
lemma all_tubes_have_volume {δ : ℝ} (hδ : 0 < δ)
    {F : Kakeya.Streamlined.TubeFamily δ} :
    ∀ i : Fin F.card, (F.toBodyFamily.body i).volume = Kakeya.deltaTubeVolume δ := by
  intro i
  let canonical : Kakeya.DeltaTube δ :=
    { base := 0
      direction := EuclideanSpace.single (0 : Fin 3) 1
      direction_unit := by simp <;> norm_num }
  have h1 : (F.tube i).volume = canonical.volume := tube_volume_eq (F.tube i) canonical
  have h2 : (F.toBodyFamily.body i).volume = (F.tube i).volume := by rfl
  rw [h2, h1] <;> rfl

/--
Cardinality lower bound from Frostman at scale `rho`:
`V_rho ≤ C * F.enncard * V_δ`.
-/
lemma frostman_cardinality_bound
    {δ : ℝ} (hδ : 0 < δ)
    {F : Kakeya.Streamlined.TubeFamily δ} (hF_nonempty : F.Nonempty)
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {C : ENNReal} (hC_ne_top : C ≠ ⊤)
    (rho : Kakeya.Streamlined.AdmissibleScale δ)
    (hFrost : U.IsFrostmanAtEveryScale C) :
    Kakeya.deltaTubeVolume rho.1 ≤
      C * F.enncard * Kakeya.deltaTubeVolume δ := by
  classical
  let coarse := U.coarse rho
  let cover := U.cover rho
  let Vδ := Kakeya.deltaTubeVolume δ
  let Vrho := Kakeya.deltaTubeVolume rho.1
  let P := cover.toFactoring
  let i0 : Fin F.card := ⟨0, hF_nonempty⟩
  let j0 : Fin coarse.card := P.parent i0
  let K : Set Point3 := (F.tube i0).carrier

  have hrho_pos : 0 < rho.1 := lt_of_lt_of_le hδ rho.property.1
  have hVδ_pos : 0 < Vδ := by
    have h1 : ENNReal.ofReal (2 * δ ^ 2) ≤ Vδ := tube_volume_ge_two_delta_sq δ hδ
    have h2 : 0 < ENNReal.ofReal (2 * δ ^ 2) := by
      apply ENNReal.ofReal_pos.mpr; positivity
    exact lt_of_lt_of_le h2 h1
  have hVδ_ne_top : Vδ ≠ ⊤ := by
    have h1 : Vδ ≤ ENNReal.ofReal (Real.pi * δ ^ 2 + (8 / 3 : ℝ) * Real.pi * δ ^ 3) :=
      capsule_upper_bound_instantiation δ hδ
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1
  have hVrho_pos : 0 < Vrho := by
    have h1 : ENNReal.ofReal (2 * rho.1 ^ 2) ≤ Vrho := tube_volume_ge_two_delta_sq rho.1 hrho_pos
    have h2 : 0 < ENNReal.ofReal (2 * rho.1 ^ 2) := by
      apply ENNReal.ofReal_pos.mpr; positivity
    exact lt_of_lt_of_le h2 h1
  have hVrho_ne_top : Vrho ≠ ⊤ := by
    have h1 : Vrho ≤ ENNReal.ofReal (Real.pi * rho.1 ^ 2 + (8 / 3 : ℝ) * Real.pi * rho.1 ^ 3) :=
      capsule_upper_bound_instantiation rho.1 hrho_pos
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1
  have hVδ_ne_zero : Vδ ≠ 0 := hVδ_pos.ne'

  have h_fine_vol : (F.toBodyFamily.body i0).volume = Vδ := all_tubes_have_volume hδ i0
  have h_coarse_vol : (coarse.toBodyFamily.body j0).volume = Vrho := by
    let canonical : Kakeya.DeltaTube rho.1 :=
      { base := 0
        direction := EuclideanSpace.single (0 : Fin 3) 1
        direction_unit := by simp <;> norm_num }
    have h1 : (coarse.tube j0).volume = canonical.volume := tube_volume_eq (coarse.tube j0) canonical
    have h_eq : (coarse.toBodyFamily.body j0).volume = (coarse.tube j0).volume := by rfl
    rw [h_eq, h1] <;> rfl

  have hK_convex : Convex ℝ K := tube_carrier_is_convex (F.tube i0)
  have hK_subset : K ⊆ (coarse.tube j0).carrier := P.contained i0
  have h_parent_eq : P.parent i0 = j0 := by rfl
  have h_i0_in_fiber : i0 ∈ P.fiberIndices j0 := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i0, h_parent_eq⟩
  have h_body_carrier_eq : (F.toBodyFamily.body i0).carrier = K := by rfl
  have h_i0_contained : i0 ∈ (P.fiberIndices j0).filter (fun i => (F.toBodyFamily.body i).carrier ⊆ K) := by
    exact Finset.mem_filter.mpr ⟨h_i0_in_fiber, h_body_carrier_eq.le⟩

  have h_fiber_contained_ge : (F.toBodyFamily.body i0).volume ≤ P.fiberContainedMass j0 K := by
    dsimp only [Factoring.fiberContainedMass]
    exact Finset.single_le_sum (fun i _ => show 0 ≤ (F.toBodyFamily.body i).volume from by positivity) h_i0_contained

  have hFrost_rho : P.FibersAreCFrostman C := hFrost rho
  have h_frostman : P.fiberContainedMass j0 K * (coarse.toBodyFamily.body j0).volume ≤
      C * P.fiberMass j0 * MeasureTheory.volume K :=
    hFrost_rho j0 K hK_convex hK_subset

  rw [h_coarse_vol] at h_frostman
  have h_vol_K : MeasureTheory.volume K = (F.toBodyFamily.body i0).volume := by rfl
  rw [h_vol_K, h_fine_vol] at h_frostman

  have h1 : P.fiberContainedMass j0 K * Vrho ≤ C * P.fiberMass j0 * Vδ := h_frostman
  have h2 : Vδ * Vrho ≤ P.fiberContainedMass j0 K * Vrho := by
    have h21 : Vδ ≤ P.fiberContainedMass j0 K := by
      have h_eq : Vδ = (F.toBodyFamily.body i0).volume := h_fine_vol.symm
      rw [h_eq]
      exact h_fiber_contained_ge
    exact mul_le_mul' h21 le_rfl
  have h3 : Vδ * Vrho ≤ C * P.fiberMass j0 * Vδ := le_trans h2 h1

  have h_fiber_mass_le : P.fiberMass j0 ≤ F.toBodyFamily.mass := by
    have h_subset : P.fiberIndices j0 ⊆ (Finset.univ : Finset (Fin F.card)) := Finset.subset_univ _
    have h : ∑ i ∈ P.fiberIndices j0, (F.toBodyFamily.body i).volume ≤
        ∑ i ∈ (Finset.univ : Finset (Fin F.card)), (F.toBodyFamily.body i).volume := by
      exact Finset.sum_le_sum_of_ne_zero fun _ hi _ => h_subset hi
    exact h

  have h4 : C * P.fiberMass j0 * Vδ ≤ C * F.toBodyFamily.mass * Vδ := by
    gcongr <;> exact h_fiber_mass_le

  have h5 : Vδ * Vrho ≤ C * F.toBodyFamily.mass * Vδ := le_trans h3 h4

  have hF_mass : F.toBodyFamily.mass = F.enncard * Vδ := by
    have h1 : F.toBodyFamily.mass = ∑ i : Fin F.card, (F.toBodyFamily.body i).volume := by rfl
    rw [h1]
    have h2 : ∑ i : Fin F.card, (F.toBodyFamily.body i).volume = ∑ i : Fin F.card, Vδ := by
      apply Finset.sum_congr rfl; intro i _; exact all_tubes_have_volume hδ i
    rw [h2]
    have h3 : ∑ i : Fin F.card, Vδ = (F.card : ENNReal) * Vδ := by
      rw [Finset.sum_const] <;> simp [mul_comm] <;> ring
    rw [h3] <;> rfl
  rw [hF_mass] at h5
  have h6 : Vδ * Vrho ≤ Vδ * (C * F.enncard * Vδ) := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using h5
  have h8 : Vrho ≤ C * F.enncard * Vδ := by
    exact (ENNReal.mul_le_mul_iff_right hVδ_ne_zero hVδ_ne_top).mp h6
  exact h8

/-- For a nonempty streamlined tube family, `deltaMax ≥ 1`. -/
lemma deltaMax_ge_one {δ : ℝ} (hδ : 0 < δ)
    {F : Kakeya.Streamlined.TubeFamily δ} (hF_nonempty : F.Nonempty) :
    (1 : ENNReal) ≤ F.toBodyFamily.deltaMax := by
  classical
  let i : Fin F.toBodyFamily.card := ⟨0, hF_nonempty⟩
  let K := (F.tube i).carrier
  have hK_convex : Convex ℝ K := tube_carrier_is_convex (F.tube i)
  have h_vol_eq : (F.toBodyFamily.body i).volume = Kakeya.deltaTubeVolume δ :=
    all_tubes_have_volume hδ i
  have hV_pos : 0 < (F.toBodyFamily.body i).volume := by
    rw [h_vol_eq]
    have h1 : ENNReal.ofReal (2 * δ ^ 2) ≤ Kakeya.deltaTubeVolume δ :=
      tube_volume_ge_two_delta_sq δ hδ
    have h2 : 0 < ENNReal.ofReal (2 * δ ^ 2) := by
      apply ENNReal.ofReal_pos.mpr; positivity
    exact lt_of_lt_of_le h2 h1
  have hV_ne_top : (F.toBodyFamily.body i).volume ≠ ⊤ := by
    rw [h_vol_eq]
    have h1 : Kakeya.deltaTubeVolume δ ≤
        ENNReal.ofReal (Real.pi * δ ^ 2 + (8 / 3 : ℝ) * Real.pi * δ ^ 3) :=
      capsule_upper_bound_instantiation δ hδ
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1
  have hV_ne_zero : (F.toBodyFamily.body i).volume ≠ 0 := hV_pos.ne'
  have h_carrier_eq : (F.toBodyFamily.body i).carrier = K := by rfl
  have h_i_in : i ∈ F.toBodyFamily.containedIndices K := by
    have h : (F.toBodyFamily.body i).carrier ⊆ K := h_carrier_eq.le
    have h_iff : i ∈ F.toBodyFamily.containedIndices K ↔ (F.toBodyFamily.body i).carrier ⊆ K :=
      BodyFamily.mem_containedIndices_iff
    exact h_iff.mpr h
  have h_mass_ge : (F.toBodyFamily.body i).volume ≤ F.toBodyFamily.containedMass K := by
    dsimp only [BodyFamily.containedMass]
    exact Finset.single_le_sum (fun i _ => show 0 ≤ (F.toBodyFamily.body i).volume from by positivity) h_i_in
  have h_density_ge_one : (1 : ENNReal) ≤ F.toBodyFamily.density K := by
    simp only [BodyFamily.density]
    have h7 : (F.toBodyFamily.body i).volume * ((F.toBodyFamily.body i).volume)⁻¹ = 1 :=
      ENNReal.mul_inv_cancel hV_ne_zero hV_ne_top
    have h8 : F.toBodyFamily.containedMass K * ((F.toBodyFamily.body i).volume)⁻¹ ≥
        (F.toBodyFamily.body i).volume * ((F.toBodyFamily.body i).volume)⁻¹ := by
      gcongr
    rw [h7] at h8
    exact h8
  have h_bdd1 : BddAbove {d : ENNReal | ∃ (K : Set Point3), Convex ℝ K ∧ d = F.toBodyFamily.density K} :=
      ⟨⊤, fun _ _ => le_top⟩
  have h9 : F.toBodyFamily.density K ≤ F.toBodyFamily.deltaMax := by
    rw [BodyFamily.deltaMax]
    exact le_csSup h_bdd1 ⟨K, hK_convex, rfl⟩
  exact h_density_ge_one.trans h9

/--
Global deltaMax bound from Frostman at scale `rho`:
`F.toBodyFamily.deltaMax ≤ C * F.enncard * V_δ / V_rho`.
-/
lemma frostman_global_deltaMax_bound
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {F : Kakeya.Streamlined.TubeFamily δ} (hF_nonempty : F.Nonempty)
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {C : ENNReal} (hC_ne_top : C ≠ ⊤)
    (rho : Kakeya.Streamlined.AdmissibleScale δ)
    (hFrost : U.IsFrostmanAtEveryScale C) :
    F.toBodyFamily.deltaMax ≤
      C * F.enncard * Kakeya.deltaTubeVolume δ / Kakeya.deltaTubeVolume rho.1 := by
  classical
  let coarse := U.coarse rho
  let G := coarse.toBodyFamily
  let P : Factoring F.toBodyFamily G := (U.cover rho).toFactoring
  let Vδ := Kakeya.deltaTubeVolume δ
  let Vrho := Kakeya.deltaTubeVolume rho.1

  have hrho_pos : 0 < rho.1 := lt_of_lt_of_le hδ rho.property.1
  have hVδ_pos : 0 < Vδ := by
    have h1 : ENNReal.ofReal (2 * δ ^ 2) ≤ Vδ := tube_volume_ge_two_delta_sq δ hδ
    have h2 : 0 < ENNReal.ofReal (2 * δ ^ 2) := by
      apply ENNReal.ofReal_pos.mpr; positivity
    exact lt_of_lt_of_le h2 h1
  have hVδ_ne_top : Vδ ≠ ⊤ := by
    have h1 : Vδ ≤ ENNReal.ofReal (Real.pi * δ ^ 2 + (8 / 3 : ℝ) * Real.pi * δ ^ 3) :=
      capsule_upper_bound_instantiation δ hδ
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1
  have hVrho_pos : 0 < Vrho := by
    have h1 : ENNReal.ofReal (2 * rho.1 ^ 2) ≤ Vrho := tube_volume_ge_two_delta_sq rho.1 hrho_pos
    have h2 : 0 < ENNReal.ofReal (2 * rho.1 ^ 2) := by
      apply ENNReal.ofReal_pos.mpr; positivity
    exact lt_of_lt_of_le h2 h1
  have hVrho_ne_top : Vrho ≠ ⊤ := by
    have h1 : Vrho ≤ ENNReal.ofReal (Real.pi * rho.1 ^ 2 + (8 / 3 : ℝ) * Real.pi * rho.1 ^ 3) :=
      capsule_upper_bound_instantiation rho.1 hrho_pos
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top h1
  have hVrho_ne_zero : Vrho ≠ 0 := hVrho_pos.ne'

  have h_coarse_vol : ∀ j : Fin G.card, (G.body j).volume = Vrho := by
    intro j
    let canonical : Kakeya.DeltaTube rho.1 :=
      { base := 0
        direction := EuclideanSpace.single (0 : Fin 3) 1
        direction_unit := by simp <;> norm_num }
    have h1 : (coarse.tube j).volume = canonical.volume := tube_volume_eq (coarse.tube j) canonical
    have h_eq : (G.body j).volume = (coarse.tube j).volume := by rfl
    rw [h_eq, h1] <;> rfl

  have h_fine_vol : ∀ i, (F.toBodyFamily.body i).volume = Vδ :=
    all_tubes_have_volume hδ

  have hF_mass : F.toBodyFamily.mass = F.enncard * Vδ := by
    have h1 : F.toBodyFamily.mass = ∑ i : Fin F.card, (F.toBodyFamily.body i).volume := by rfl
    rw [h1]
    have h2 : ∑ i : Fin F.card, (F.toBodyFamily.body i).volume = ∑ i : Fin F.card, Vδ := by
      apply Finset.sum_congr rfl; intro i _; exact h_fine_vol i
    rw [h2]
    have h3 : ∑ i : Fin F.card, Vδ = (F.card : ENNReal) * Vδ := by
      rw [Finset.sum_const] <;> simp [mul_comm] <;> ring
    rw [h3] <;> rfl

  have hFrost_rho : P.FibersAreCFrostman C := hFrost rho

  have h_fiber_sum_mass : (∑ j : Fin G.card, P.fiberMass j) = F.toBodyFamily.mass := by
    have h_disj : ∀ j1 j2 : Fin G.card, j1 ≠ j2 → Disjoint (P.fiberIndices j1) (P.fiberIndices j2) := by
      intro j1 j2 hne
      rw [Finset.disjoint_left]
      intro i hi1 hi2
      have h1 : P.parent i = j1 := by simpa [Factoring.fiberIndices, Finset.mem_filter] using hi1
      have h2 : P.parent i = j2 := by simpa [Factoring.fiberIndices, Finset.mem_filter] using hi2
      exact hne (h1.symm.trans h2)
    have h_univ : Finset.biUnion (Finset.univ : Finset (Fin G.card)) P.fiberIndices =
        (Finset.univ : Finset (Fin F.toBodyFamily.card)) := by
      apply Finset.eq_univ_of_forall
      intro i
      have h1 : i ∈ P.fiberIndices (P.parent i) := by
        simp only [Factoring.fiberIndices, Finset.mem_filter, Finset.mem_univ, true_and] <;> rfl
      exact Finset.mem_biUnion.mpr ⟨P.parent i, Finset.mem_univ _, h1⟩
    have h_disj' : ∀ i ∈ (Finset.univ : Finset (Fin G.card)), ∀ j ∈ (Finset.univ), i ≠ j → Disjoint (P.fiberIndices i) (P.fiberIndices j) := by
      intro i _ j _ hne; exact h_disj i j hne
    have h_sum : ∑ i ∈ Finset.biUnion (Finset.univ : Finset (Fin G.card)) P.fiberIndices, (F.toBodyFamily.body i).volume =
        ∑ j : Fin G.card, P.fiberMass j := by
      rw [Finset.sum_biUnion h_disj'] <;> rfl
    rw [←h_sum, h_univ] <;> rfl

  have h_main : ∀ (K : Set Point3), Convex ℝ K →
      F.toBodyFamily.density K ≤ C * F.enncard * Vδ / Vrho := by
    intro K hK_convex
    by_cases hK0 : MeasureTheory.volume K = 0
    · have h_cm_zero : F.toBodyFamily.containedMass K = 0 := by
        dsimp only [BodyFamily.containedMass]
        rw [Finset.sum_eq_zero_iff]
        intro i hi
        have h_sub : (F.toBodyFamily.body i).carrier ⊆ K := by
          simpa [BodyFamily.mem_containedIndices_iff] using hi
        have h_vol : (F.toBodyFamily.body i).volume ≤ MeasureTheory.volume K := MeasureTheory.measure_mono h_sub
        rw [hK0] at h_vol
        exact le_zero_iff.mp h_vol
      have h_dens : F.toBodyFamily.density K = 0 := by
        simp [BodyFamily.density, h_cm_zero, hK0]
      rw [h_dens] <;> simp
    by_cases hKtop : MeasureTheory.volume K = ⊤
    · have h_dens : F.toBodyFamily.density K = 0 := by
        simp [BodyFamily.density, hKtop, ENNReal.div_top]
      rw [h_dens] <;> simp
    let Kj : Fin G.card → Set Point3 := fun j => K ∩ (G.body j).carrier
    have hKj_convex : ∀ j, Convex ℝ (Kj j) := by
      intro j
      have h_coarse_convex : Convex ℝ (G.body j).carrier := tube_carrier_is_convex (coarse.tube j)
      exact hK_convex.inter h_coarse_convex
    have hKj_subset : ∀ j, Kj j ⊆ (G.body j).carrier := by
      intro j
      exact Set.inter_subset_right
    have h_vol_le : ∀ j, MeasureTheory.volume (Kj j) ≤ MeasureTheory.volume K := by
      intro j
      exact MeasureTheory.measure_mono Set.inter_subset_left

    let S : Fin G.card → Finset (Fin F.toBodyFamily.card) := fun j =>
      (P.fiberIndices j).filter (fun i => (F.toBodyFamily.body i).carrier ⊆ Kj j)
    have h_disj : ∀ j1 j2 : Fin G.card, j1 ≠ j2 → Disjoint (S j1) (S j2) := by
      intro j1 j2 hne
      have h : Disjoint (P.fiberIndices j1) (P.fiberIndices j2) := by
        rw [Finset.disjoint_left]
        intro i hi1 hi2
        have h1 : P.parent i = j1 := by simpa [Factoring.fiberIndices, Finset.mem_filter] using hi1
        have h2 : P.parent i = j2 := by simpa [Factoring.fiberIndices, Finset.mem_filter] using hi2
        exact hne (h1.symm.trans h2)
      exact Disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _) h
    have h_subset : F.toBodyFamily.containedIndices K ⊆ Finset.biUnion (Finset.univ) S := by
      intro i hi
      have h_cont : (F.toBodyFamily.body i).carrier ⊆ K := by
        simpa [BodyFamily.mem_containedIndices_iff] using hi
      let j : Fin G.card := P.parent i
      have hnest : (F.toBodyFamily.body i).carrier ⊆ (G.body j).carrier := P.contained i
      have hboth : (F.toBodyFamily.body i).carrier ⊆ Kj j := Set.subset_inter h_cont hnest
      have hinS : i ∈ S j := by
        dsimp only [S]
        have h_eq : P.parent i = j := by rfl
        have h1 : i ∈ P.fiberIndices j := by
          simpa [Factoring.fiberIndices, Finset.mem_filter] using h_eq
        exact Finset.mem_filter.mpr ⟨h1, hboth⟩
      exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hinS⟩
    have h_contained_le : F.toBodyFamily.containedMass K ≤
        ∑ j : Fin G.card, P.fiberContainedMass j (Kj j) := by
      dsimp only [BodyFamily.containedMass, Factoring.fiberContainedMass]
      have h1 : F.toBodyFamily.containedMass K ≤
          ∑ i ∈ Finset.biUnion (Finset.univ) S, (F.toBodyFamily.body i).volume :=
        Finset.sum_le_sum_of_subset_of_nonneg h_subset (fun x _ _ => by positivity)
      have h_disj' : ∀ i ∈ (Finset.univ : Finset (Fin G.card)), ∀ j ∈ (Finset.univ), i ≠ j → Disjoint (S i) (S j) := by
        intro i _ j _ hne; exact h_disj i j hne
      rw [Finset.sum_biUnion h_disj'] at h1
      exact h1

    have h_frostman_each : ∀ j,
        P.fiberContainedMass j (Kj j) * Vrho ≤
          C * P.fiberMass j * MeasureTheory.volume (Kj j) := by
      intro j
      have h := hFrost_rho j (Kj j) (hKj_convex j) (hKj_subset j)
      rw [h_coarse_vol j] at h
      exact h

    have h_sum_bound : (∑ j : Fin G.card, P.fiberContainedMass j (Kj j)) * Vrho ≤
        C * F.toBodyFamily.mass * MeasureTheory.volume K := by
      calc
        (∑ j, P.fiberContainedMass j (Kj j)) * Vrho
          = ∑ j, P.fiberContainedMass j (Kj j) * Vrho := by rw [Finset.sum_mul]
        _ ≤ ∑ j, C * P.fiberMass j * MeasureTheory.volume (Kj j) := by
            apply Finset.sum_le_sum; intro j _; exact h_frostman_each j
        _ = C * ∑ j, P.fiberMass j * MeasureTheory.volume (Kj j) := by
            have h_rew : ∑ j : Fin G.card, C * P.fiberMass j * MeasureTheory.volume (Kj j) =
                C * ∑ j : Fin G.card, P.fiberMass j * MeasureTheory.volume (Kj j) := by
              have h_assoc : ∀ j, C * P.fiberMass j * MeasureTheory.volume (Kj j) =
                  C * (P.fiberMass j * MeasureTheory.volume (Kj j)) := by
                intro j; simp [mul_assoc]
              have h_sum : ∑ j, C * P.fiberMass j * MeasureTheory.volume (Kj j) =
                  ∑ j, C * (P.fiberMass j * MeasureTheory.volume (Kj j)) := by
                apply Finset.sum_congr rfl; intro j _; exact h_assoc j
              rw [h_sum, Finset.mul_sum]
            exact h_rew
        _ ≤ C * (MeasureTheory.volume K * ∑ j, P.fiberMass j) := by
            have h : ∑ j, P.fiberMass j * MeasureTheory.volume (Kj j) ≤
                MeasureTheory.volume K * ∑ j, P.fiberMass j := by
              calc
                ∑ j, P.fiberMass j * MeasureTheory.volume (Kj j)
                  = ∑ j, MeasureTheory.volume (Kj j) * P.fiberMass j := by
                    apply Finset.sum_congr rfl; intro j _; simp [mul_comm]
                _ ≤ ∑ j, MeasureTheory.volume K * P.fiberMass j := by
                    apply Finset.sum_le_sum; intro j _
                    exact mul_le_mul_of_nonneg_right (h_vol_le j) (by positivity)
                _ = MeasureTheory.volume K * ∑ j, P.fiberMass j := by
                    rw [Finset.mul_sum] <;> simp [mul_comm]
            gcongr
        _ = C * F.toBodyFamily.mass * MeasureTheory.volume K := by
            rw [h_fiber_sum_mass] <;> simp [mul_assoc, mul_comm, mul_left_comm]

    have hK_ne_zero : MeasureTheory.volume K ≠ 0 := hK0
    have h1 : F.toBodyFamily.containedMass K * Vrho ≤
        C * F.enncard * Vδ * MeasureTheory.volume K := by
      have h1a : F.toBodyFamily.containedMass K * Vrho ≤
          C * F.toBodyFamily.mass * MeasureTheory.volume K :=
        le_trans (mul_le_mul_of_nonneg_right h_contained_le (by positivity)) h_sum_bound
      rw [hF_mass] at h1a
      simpa [mul_assoc] using h1a
    have h_goal : F.toBodyFamily.density K ≤ C * F.enncard * Vδ / Vrho := by
      simp only [BodyFamily.density]
      set a := F.toBodyFamily.containedMass K
      set b := MeasureTheory.volume K
      set c := C * F.enncard * Vδ
      set d := Vrho
      have h_mult : (a * d) * (b⁻¹ * d⁻¹) ≤ (c * b) * (b⁻¹ * d⁻¹) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
      have h_lhs : (a * d) * (b⁻¹ * d⁻¹) = a * b⁻¹ := by
        have h_eq : (a * d) * (b⁻¹ * d⁻¹) = a * b⁻¹ * (d * d⁻¹) := by
          simp [mul_assoc, mul_comm, mul_left_comm]
        rw [h_eq, ENNReal.mul_inv_cancel hVrho_ne_zero hVrho_ne_top, mul_one]
      have h_rhs : (c * b) * (b⁻¹ * d⁻¹) = c * d⁻¹ := by
        have h_eq : (c * b) * (b⁻¹ * d⁻¹) = c * d⁻¹ * (b * b⁻¹) := by
          simp [mul_assoc, mul_comm, mul_left_comm]
        rw [h_eq, ENNReal.mul_inv_cancel hK_ne_zero hKtop, mul_one]
      rw [h_lhs, h_rhs] at h_mult
      exact h_mult
    exact h_goal

  have h_bdd : BddAbove {d : ENNReal | ∃ (K : Set Point3), Convex ℝ K ∧ d = F.toBodyFamily.density K} := by
    refine' ⟨C * F.enncard * Vδ / Vrho, _⟩
    intro d hd
    rcases hd with ⟨K, hK, rfl⟩
    exact h_main K hK
  have h_all_le : ∀ d, d ∈ {d : ENNReal | ∃ (K : Set Point3), Convex ℝ K ∧ d = F.toBodyFamily.density K} →
      d ≤ C * F.enncard * Vδ / Vrho := by
    intro d hd
    rcases hd with ⟨K, hK, rfl⟩
    exact h_main K hK
  have h_nonempty : {d : ENNReal | ∃ (K : Set Point3), Convex ℝ K ∧ d = F.toBodyFamily.density K}.Nonempty := by
    refine' ⟨F.toBodyFamily.density Set.univ, _⟩
    exact ⟨Set.univ, convex_univ, rfl⟩
  unfold Kakeya.Streamlined.BodyFamily.deltaMax
  exact csSup_le h_nonempty h_all_le

end Kakeya.Assouad
