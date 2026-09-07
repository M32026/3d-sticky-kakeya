import MyLeanRepo.Kakeya.Assouad.Statements
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Elementary infrastructure for WZ2 extremal configurations

These lemmas isolate the order and finite-fiber bookkeeping used before the
large-slope interval selection and the anisotropic rescaling step.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

private lemma realRpowENN_add'
    {delta a b : ℝ} (hdelta : 0 < delta) :
    Kakeya.realRpowENN delta (a + b) =
      Kakeya.realRpowENN delta a *
        Kakeya.realRpowENN delta b := by
  simp only [Kakeya.realRpowENN]
  have hreal :
      Real.rpow delta (a + b) =
        Real.rpow delta a * Real.rpow delta b :=
    Real.rpow_add hdelta a b
  rw [hreal]
  exact ENNReal.ofReal_mul
    (Real.rpow_nonneg hdelta.le a)

/-- Increasing the error exponent weakens every extremality requirement. -/
lemma IsExtremalPair.mono_epsilon
    {delta sigma epsilon₁ epsilon₂ : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    (h : IsExtremalPair sigma epsilon₁ F U Y)
    (hepsilon : epsilon₁ ≤ epsilon₂) :
    IsExtremalPair sigma epsilon₂ F U Y := by
  rcases h with
    ⟨hdelta, hdelta_one, hF_nonempty, hF_ball, hF_distinct,
      hU_uniform, hU_frostman, hY_dense, hY_volume_upper,
      hY_volume_lower⟩
  have h_uniform_power :
      Kakeya.realRpowENN delta (-epsilon₁) ≤
        Kakeya.realRpowENN delta (-epsilon₂) := by
    apply ENNReal.ofReal_mono
    apply Real.rpow_le_rpow_of_exponent_ge hdelta hdelta_one
    linarith
  have h_density_power :
      Kakeya.realRpowENN delta epsilon₂ ≤
        Kakeya.realRpowENN delta epsilon₁ := by
    apply ENNReal.ofReal_mono
    exact Real.rpow_le_rpow_of_exponent_ge hdelta hdelta_one hepsilon
  have h_volume_power :
      Kakeya.realRpowENN delta (sigma - epsilon₁) ≤
        Kakeya.realRpowENN delta (sigma - epsilon₂) := by
    apply ENNReal.ofReal_mono
    apply Real.rpow_le_rpow_of_exponent_ge hdelta hdelta_one
    linarith
  have h_floor_power :
      Kakeya.realRpowENN delta (sigma + epsilon₂) ≤
        Kakeya.realRpowENN delta (sigma + epsilon₁) := by
    apply ENNReal.ofReal_mono
    apply Real.rpow_le_rpow_of_exponent_ge hdelta hdelta_one
    linarith
  refine
    ⟨hdelta, hdelta_one, hF_nonempty, hF_ball, hF_distinct,
      hU_uniform.trans h_uniform_power, ?_, ?_,
      hY_volume_upper.trans h_volume_power,
      h_floor_power.trans hY_volume_lower⟩
  · intro rho j K hK_convex hK_subset
    have h_old := hU_frostman rho j K hK_convex hK_subset
    exact h_old.trans (by
      gcongr)
  · exact (mul_le_mul_right' h_density_power F.toBodyFamily.mass).trans
      hY_dense

/-- Increasing the loss weakens the extremal cardinality upper bound. -/
lemma HasExtremalCardinalityUpper.mono_epsilon
    {delta epsilon₁ epsilon₂ : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    (h : HasExtremalCardinalityUpper F epsilon₁)
    (hepsilon : epsilon₁ ≤ epsilon₂) :
    HasExtremalCardinalityUpper F epsilon₂ := by
  exact h.trans (by
    apply ENNReal.ofReal_mono
    apply Real.rpow_le_rpow_of_exponent_ge hdelta hdelta_one
    linarith)

/-- Increasing the error exponent also weakens projection-ready extremality. -/
lemma IsProjectionExtremalPair.mono_epsilon
    {delta sigma epsilon₁ epsilon₂ : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    (h : IsProjectionExtremalPair sigma epsilon₁ F U Y)
    (hepsilon : epsilon₁ ≤ epsilon₂) :
    IsProjectionExtremalPair sigma epsilon₂ F U Y := by
  rcases h with
    ⟨hdelta, hdelta_one, hF_nonempty, hF_base, hF_distinct,
      hU_uniform, hU_frostman, hY_dense, hY_window,
      hY_volume_upper, hY_volume_lower⟩
  have h_uniform_power :
      Kakeya.realRpowENN delta (-epsilon₁) ≤
        Kakeya.realRpowENN delta (-epsilon₂) := by
    apply ENNReal.ofReal_mono
    apply Real.rpow_le_rpow_of_exponent_ge hdelta hdelta_one
    linarith
  have h_density_power :
      Kakeya.realRpowENN delta epsilon₂ ≤
        Kakeya.realRpowENN delta epsilon₁ := by
    apply ENNReal.ofReal_mono
    exact Real.rpow_le_rpow_of_exponent_ge hdelta hdelta_one hepsilon
  have h_volume_power :
      Kakeya.realRpowENN delta (sigma - epsilon₁) ≤
        Kakeya.realRpowENN delta (sigma - epsilon₂) := by
    apply ENNReal.ofReal_mono
    apply Real.rpow_le_rpow_of_exponent_ge hdelta hdelta_one
    linarith
  have h_floor_power :
      Kakeya.realRpowENN delta (sigma + epsilon₂) ≤
        Kakeya.realRpowENN delta (sigma + epsilon₁) := by
    apply ENNReal.ofReal_mono
    apply Real.rpow_le_rpow_of_exponent_ge hdelta hdelta_one
    linarith
  refine
    ⟨hdelta, hdelta_one, hF_nonempty, hF_base, hF_distinct,
      hU_uniform.trans h_uniform_power, ?_, ?_, hY_window,
      hY_volume_upper.trans h_volume_power,
      h_floor_power.trans hY_volume_lower⟩
  · intro rho j K hK_convex hK_subset
    have h_old := hU_frostman rho j K hK_convex hK_subset
    exact h_old.trans (by
      gcongr)
  · exact (mul_le_mul_right' h_density_power F.toBodyFamily.mass).trans
      hY_dense

/-- Increasing the loss parameter weakens the hereditary volume floor. -/
lemma HasHereditaryVolumeFloor.mono_epsilon
    {delta sigma epsilon₁ epsilon₂ : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Y : Kakeya.Streamlined.TubeShading F}
    (h : HasHereditaryVolumeFloor Y sigma epsilon₁)
    (hepsilon : epsilon₁ ≤ epsilon₂) :
    HasHereditaryVolumeFloor Y sigma epsilon₂ := by
  intro loss hloss Z hZY hZ_dense
  exact h loss (hepsilon.trans hloss) Z hZY hZ_dense

/-- The carrier of every formal `delta`-tube is convex. -/
lemma deltaTube_carrier_convex {delta : ℝ}
    (T : Kakeya.DeltaTube delta) :
    Convex ℝ T.carrier := by
  apply Convex.cthickening
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨s, hs, rfl⟩
  rcases hy with ⟨t, ht, rfl⟩
  refine ⟨a * s + b * t,
    (convex_Icc (0 : ℝ) 1) hs ht ha hb hab, ?_⟩
  simp only [Kakeya.unitSegment, Set.mem_image] at *
  have hbase : a • T.base + b • T.base = T.base := by
    rw [← add_smul, hab, one_smul]
  rw [smul_add, smul_add, smul_smul, smul_smul]
  rw [show
    a • T.base + (a * s) • T.direction +
        (b • T.base + (b * t) • T.direction) =
      (a • T.base + b • T.base) +
        ((a * s) • T.direction + (b * t) • T.direction) by abel]
  rw [hbase, ← add_smul]

/-- The canonical unit-scale tube contains a unit ball in volume. -/
lemma one_le_deltaTubeVolume_one :
    (1 : ENNReal) ≤ Kakeya.deltaTubeVolume 1 := by
  let midpoint : Point3 :=
    (1 / 2 : ℝ) • EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
  have hball :
      Metric.closedBall midpoint 1 ⊆
        Metric.cthickening 1
          (Kakeya.unitSegment 0
            (EuclideanSpace.single (0 : Fin 3) (1 : ℝ))) := by
    intro x hx
    exact Metric.mem_cthickening_of_dist_le
      x midpoint 1 _
      ⟨1 / 2, by norm_num, by simp [midpoint]⟩
      (by simpa [Metric.mem_closedBall] using hx)
  have hball_volume :
      (1 : ENNReal) ≤ volume (Metric.closedBall midpoint 1) := by
    rw [EuclideanSpace.volume_closedBall_fin_three]
    have hreal : (1 : ℝ) ≤ Real.pi * 4 / 3 := by
      linarith [Real.pi_gt_three]
    simpa using ENNReal.ofReal_mono hreal
  exact hball_volume.trans (measure_mono hball)

/-- The canonical unit-scale tube has finite volume. -/
lemma deltaTubeVolume_one_ne_top : Kakeya.deltaTubeVolume 1 ≠ ⊤ := by
  let e₀ : Point3 := EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
  have hseg_sub :
      Kakeya.unitSegment 0 e₀ ⊆ Metric.closedBall (0 : Point3) 1 := by
    intro p hp
    rcases hp with ⟨t, ht, rfl⟩
    have hnorm : ‖(t • e₀)‖ ≤ 1 := by
      have ht_nonneg : 0 ≤ t := ht.1
      calc
        ‖(t • e₀)‖ = ‖t‖ * ‖e₀‖ := norm_smul t e₀
        _ = t * ‖e₀‖ := by
          have h : ‖t‖ = t := by
            simpa [Real.norm_eq_abs] using abs_of_nonneg ht_nonneg
          rw [h]
        _ = t := by simp [e₀]
        _ ≤ 1 := ht.2
    simpa [Metric.mem_closedBall] using hnorm
  have hseg_bdd : Bornology.IsBounded (Kakeya.unitSegment 0 e₀) :=
    Metric.isBounded_closedBall.subset hseg_sub
  have hthick_bdd :
      Bornology.IsBounded (Metric.cthickening 1 (Kakeya.unitSegment 0 e₀)) :=
    hseg_bdd.cthickening
  exact hthick_bdd.measure_lt_top.ne

/--
Every-scale Frostman control and one nonempty fiber force the total fine-tube
mass to be at least the reciprocal error scale.
-/
lemma frostman_total_mass_lower
    (hvolume : TubeVolumeScalingStatement)
    {delta epsilon : ℝ}
    (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    (F : Kakeya.Streamlined.TubeFamily delta)
    (hF_nonempty : F.Nonempty)
    (U : Kakeya.Streamlined.UniformTubeStructure F)
    (C : ENNReal)
    (hC : C ≤ Kakeya.realRpowENN delta (-epsilon))
    (hFrostman : U.IsFrostmanAtEveryScale C) :
    Kakeya.realRpowENN delta epsilon ≤ F.toBodyFamily.mass := by
  classical
  rcases hvolume with ⟨h_equal_volume, h_volume_finite, _⟩
  have hVdelta := h_volume_finite delta hdelta hdelta_one
  let oneScale : Kakeya.Streamlined.AdmissibleScale delta :=
    ⟨1, hdelta_one, le_rfl⟩
  let coarse := U.coarse oneScale
  let cover := U.cover oneScale
  let factoring := cover.toFactoring
  let i : Fin F.card := ⟨0, hF_nonempty⟩
  let j : Fin coarse.card := factoring.parent i
  let K : Set Point3 := (F.tube i).carrier
  have hK_subset : K ⊆ (coarse.tube j).carrier := by
    exact factoring.contained i
  have h_frost :=
    hFrostman oneScale j K (deltaTube_carrier_convex (F.tube i))
      hK_subset
  have hi_fiber : i ∈ factoring.fiberIndices j := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  have hi_contained :
      i ∈ (factoring.fiberIndices j).filter
        (fun k => (F.tube k).carrier ⊆ K) := by
    exact Finset.mem_filter.mpr ⟨hi_fiber, Set.Subset.rfl⟩
  have h_contained_lower :
      (F.tube i).volume ≤ factoring.fiberContainedMass j K := by
    rw [Kakeya.Streamlined.Factoring.fiberContainedMass]
    exact Finset.single_le_sum
      (f := fun k => (F.tube k).volume)
      (fun _ _ => (bot_le : (0 : ENNReal) ≤ _)) hi_contained
  have h_raw :
      Kakeya.deltaTubeVolume delta * Kakeya.deltaTubeVolume 1 ≤
        (C * factoring.fiberMass j) *
          Kakeya.deltaTubeVolume delta := by
    calc
      Kakeya.deltaTubeVolume delta * Kakeya.deltaTubeVolume 1
          = (F.tube i).volume * (coarse.tube j).volume := by
              rw [h_equal_volume delta (F.tube i),
                h_equal_volume 1 (coarse.tube j)]
      _ ≤ factoring.fiberContainedMass j K *
          (coarse.tube j).volume := by
            exact mul_le_mul_right' h_contained_lower _
      _ ≤ C * factoring.fiberMass j * volume K := h_frost
      _ = (C * factoring.fiberMass j) *
          Kakeya.deltaTubeVolume delta := by
            rw [show volume K = (F.tube i).volume by rfl,
              h_equal_volume delta (F.tube i)]
  have h_unit_fiber :
      Kakeya.deltaTubeVolume 1 ≤ C * factoring.fiberMass j := by
    have h_raw' :
        Kakeya.deltaTubeVolume 1 * Kakeya.deltaTubeVolume delta ≤
          (C * factoring.fiberMass j) *
            Kakeya.deltaTubeVolume delta := by
      simpa [mul_comm] using h_raw
    have hcancel := mul_le_mul_right' h_raw'
      (Kakeya.deltaTubeVolume delta)⁻¹
    simpa [mul_assoc,
      ENNReal.mul_inv_cancel hVdelta.1.ne' hVdelta.2] using hcancel
  have h_power_cancel :
      Kakeya.realRpowENN delta epsilon *
          Kakeya.realRpowENN delta (-epsilon) = 1 := by
    rw [← realRpowENN_add' hdelta]
    simp [Kakeya.realRpowENN]
  have h_scaled_C :
      Kakeya.realRpowENN delta epsilon * C ≤ 1 := by
    calc
      Kakeya.realRpowENN delta epsilon * C
          ≤ Kakeya.realRpowENN delta epsilon *
              Kakeya.realRpowENN delta (-epsilon) := by
                exact mul_le_mul_left' hC _
      _ = 1 := h_power_cancel
  have h_fiber_lower :
      Kakeya.realRpowENN delta epsilon ≤ factoring.fiberMass j := by
    calc
      Kakeya.realRpowENN delta epsilon
          ≤ Kakeya.realRpowENN delta epsilon *
              Kakeya.deltaTubeVolume 1 := by
                simpa using mul_le_mul_left'
                  one_le_deltaTubeVolume_one
                  (Kakeya.realRpowENN delta epsilon)
      _ ≤ Kakeya.realRpowENN delta epsilon *
          (C * factoring.fiberMass j) := by
            exact mul_le_mul_left' h_unit_fiber _
      _ = (Kakeya.realRpowENN delta epsilon * C) *
          factoring.fiberMass j := by ring
      _ ≤ 1 * factoring.fiberMass j := by
            exact mul_le_mul_right' h_scaled_C _
      _ = factoring.fiberMass j := by simp
  have h_fiber_mass_le :
      factoring.fiberMass j ≤ F.toBodyFamily.mass := by
    simp only [Kakeya.Streamlined.Factoring.fiberMass,
      Kakeya.Streamlined.BodyFamily.mass]
    exact Finset.sum_le_sum_of_subset
      (factoring.fiberIndices j).subset_univ
  exact h_fiber_lower.trans h_fiber_mass_le

end Kakeya.Assouad
