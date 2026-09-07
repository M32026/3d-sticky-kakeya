import MyLeanRepo.Kakeya.Assouad.CylinderVolume
import MyLeanRepo.Kakeya.Assouad.TubeVolumeScaling
import MyLeanRepo.Kakeya.Assouad.TubeVolumeLowerBound
import MyLeanRepo.Kakeya.Assouad.EssentiallyDistinctCardBound
import MyLeanRepo.Kakeya.Streamlined.Estimates

/-!
# Tube volume ratio bounds and Frostman extension

Upper and lower bounds for `deltaTubeVolume` using cylinder geometry,
ratio bounds for Frostman constant extension, and the Frostman extension lemma.
-/

noncomputable section

open MeasureTheory Metric Set

namespace Kakeya.Assouad

private abbrev e0 : Point3 := EuclideanSpace.single 0 1

/-- Lower bound: canonical tube volume ≥ `π * δ²`. -/
lemma deltaTubeVolume_lower_pi {δ : ℝ} (hδ : 0 < δ) :
    ENNReal.ofReal (Real.pi * δ^2) ≤ Kakeya.deltaTubeVolume δ := by
  have h : stdCylinder δ 1 ⊆ Metric.cthickening δ (unitSegment 0 e0) :=
    canonical_tube_contains_cylinder hδ
  have h' : volume (stdCylinder δ 1) ≤ volume _ := measure_mono h
  have hvol_cyl : volume (stdCylinder δ 1) = ENNReal.ofReal (Real.pi * δ^2) := by
    have h9 := volume_stdCylinder δ 1 hδ.le (by norm_num)
    simpa using h9
  rw [hvol_cyl] at h'
  simpa [Kakeya.deltaTubeVolume] using h'

/-- Upper bound: canonical tube volume ≤ `π * δ² * (1 + 2δ)`. -/
lemma deltaTubeVolume_upper_pi {δ : ℝ} (hδ : 0 < δ) :
    Kakeya.deltaTubeVolume δ ≤ ENNReal.ofReal (Real.pi * δ^2 * (1 + 2 * δ)) := by
  have h_sub : Metric.cthickening δ (unitSegment 0 e0) ⊆
      {x : Point3 | (x 1)^2 + (x 2)^2 ≤ δ^2 ∧ -δ ≤ x 0 ∧ x 0 ≤ 1 + δ} :=
    canonical_tube_subset_shifted_cylinder hδ
  let S : Set Point3 := {x | (x 1)^2 + (x 2)^2 ≤ δ^2 ∧ -δ ≤ x 0 ∧ x 0 ≤ 1 + δ}
  have h_meas1 : volume (Metric.cthickening δ (unitSegment 0 e0)) ≤ volume S :=
    measure_mono h_sub
  let shift : Point3 ≃ᵐ Point3 :=
    { toFun := fun x => x - δ • e0
      invFun := fun y => y + δ • e0
      left_inv := by intro x; ext i; fin_cases i <;> simp [e0] <;> ring
      right_inv := by intro y; ext i; fin_cases i <;> simp [e0] <;> ring
      measurable_toFun := measurable_id.sub measurable_const
      measurable_invFun := measurable_id.add measurable_const }
  have hmp_shift : MeasurePreserving shift volume volume :=
    measurePreserving_sub_right volume (δ • e0)
  have h_image : shift '' stdCylinder δ (1 + 2 * δ) = S := by
    ext y
    simp only [S, Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have h_shift_def : shift x = x - δ • e0 := by rfl
      have h1 : (x 1)^2 + (x 2)^2 ≤ δ^2 := hx.1
      have h2 : 0 ≤ x 0 := hx.2.1
      have h3 : x 0 ≤ 1 + 2 * δ := hx.2.2
      have h41 : (shift x) 1 = x 1 := by rw [h_shift_def] <;> simp [e0]
      have h42 : (shift x) 2 = x 2 := by rw [h_shift_def] <;> simp [e0]
      have h43 : (shift x) 0 = x 0 - δ := by rw [h_shift_def] <;> simp [e0]
      exact ⟨by rw [h41, h42] <;> exact h1, by linarith, by linarith⟩
    · rintro ⟨h1, h2, h3⟩
      let x : Point3 := y + δ • e0
      have h_shift_x : shift x = y := by
        simp [shift, x, e0] <;> ext i <;> fin_cases i <;> simp [e0] <;> ring
      have hx1 : (x 1)^2 + (x 2)^2 ≤ δ^2 := by simpa [x, e0] using h1
      have hx2 : 0 ≤ x 0 := by simp [x, e0] <;> linarith
      have hx3 : x 0 ≤ 1 + 2 * δ := by simp [x, e0] <;> linarith
      exact ⟨x, ⟨hx1, hx2, hx3⟩, h_shift_x⟩
  have h_meas_set : MeasurableSet (stdCylinder δ (1 + 2 * δ)) := by
    have h11 : Measurable (fun x : Point3 => (x 1)^2 + (x 2)^2) := by fun_prop
    have h21 : Measurable (fun x : Point3 => x 0) := by fun_prop
    exact (measurableSet_le h11 (by fun_prop)).inter (h21 measurableSet_Icc)
  have hmp_symm : MeasurePreserving shift.symm volume volume := hmp_shift.symm shift
  have h_img_eq : shift '' stdCylinder δ (1 + 2 * δ) = shift.symm ⁻¹' (stdCylinder δ (1 + 2 * δ)) := by
    ext z
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨x, hx, rfl⟩; simpa using hx
    · intro hz; exact ⟨shift.symm z, hz, shift.apply_symm_apply z⟩
  have h_vol2 : volume (shift '' stdCylinder δ (1 + 2 * δ)) =
      volume (stdCylinder δ (1 + 2 * δ)) := by
    rw [h_img_eq]
    exact hmp_symm.measure_preimage h_meas_set.nullMeasurableSet
  have h_S_vol : volume S = volume (stdCylinder δ (1 + 2 * δ)) := by
    rw [←h_image, h_vol2]
  have h_vol_cyl : volume (stdCylinder δ (1 + 2 * δ)) =
      ENNReal.ofReal (Real.pi * δ^2 * (1 + 2 * δ)) :=
    volume_stdCylinder δ (1 + 2 * δ) hδ.le (by linarith)
  rw [h_S_vol, h_vol_cyl] at h_meas1
  simpa [Kakeya.deltaTubeVolume] using h_meas1

/--
Ratio bound: for `0 < ρ ≤ σ ≤ 1`,
`deltaTubeVolume σ ≤ 3 * (σ²/ρ²) * deltaTubeVolume ρ`.
-/
lemma deltaTubeVolume_ratio_bound_cylinder {σ ρ : ℝ} (hρ : 0 < ρ) (hσρ : ρ ≤ σ) (hσ1 : σ ≤ 1) :
    Kakeya.deltaTubeVolume σ ≤
      3 * Kakeya.realRpowENN σ 2 * (Kakeya.realRpowENN ρ 2)⁻¹ * Kakeya.deltaTubeVolume ρ := by
  have hσ_pos : 0 < σ := hρ.trans_le hσρ
  have h_upper : Kakeya.deltaTubeVolume σ ≤
      ENNReal.ofReal (Real.pi * σ^2 * (1 + 2 * σ)) :=
    deltaTubeVolume_upper_pi hσ_pos
  have h_lower : ENNReal.ofReal (Real.pi * ρ^2) ≤ Kakeya.deltaTubeVolume ρ :=
    deltaTubeVolume_lower_pi hρ
  have h_real : Real.pi * σ^2 * (1 + 2 * σ) ≤ 3 * Real.pi * σ^2 := by
    have h : (1 + 2 * σ) ≤ 3 := by linarith
    have h2 : Real.pi * σ^2 * (1 + 2 * σ) ≤ Real.pi * σ^2 * 3 := by gcongr
    linarith
  have h1 : ENNReal.ofReal (Real.pi * σ^2 * (1 + 2 * σ)) ≤
      ENNReal.ofReal (3 * Real.pi * σ^2) := ENNReal.ofReal_mono h_real
  have h_rho2 : Kakeya.realRpowENN ρ 2 = ENNReal.ofReal (ρ^2) := by
    simp [Kakeya.realRpowENN] <;> ring
  have h_sigma2 : Kakeya.realRpowENN σ 2 = ENNReal.ofReal (σ^2) := by
    simp [Kakeya.realRpowENN] <;> ring
  have h_rho2_ne_zero : (Kakeya.realRpowENN ρ 2) ≠ 0 := by
    rw [h_rho2] <;> simp [hρ.ne'] <;> positivity
  have h_rho2_ne_top : (Kakeya.realRpowENN ρ 2) ≠ ⊤ := by
    rw [h_rho2]
    exact ENNReal.ofReal_ne_top
  have h_pi_sigma2 : ENNReal.ofReal (3 * Real.pi * σ^2) =
      3 * ENNReal.ofReal Real.pi * Kakeya.realRpowENN σ 2 := by
    rw [h_sigma2]
    have h : ENNReal.ofReal (3 * Real.pi * σ^2) =
        ENNReal.ofReal (3 : ℝ) * ENNReal.ofReal Real.pi * ENNReal.ofReal (σ^2) := by
      rw [← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 3 by norm_num),
          ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 3 * Real.pi by positivity)]
      <;> ring_nf
    rw [h]
    <;> simp
  have h_step : ENNReal.ofReal Real.pi * Kakeya.realRpowENN ρ 2 ≤ Kakeya.deltaTubeVolume ρ := by
    have h_eq : ENNReal.ofReal Real.pi * Kakeya.realRpowENN ρ 2 = ENNReal.ofReal (Real.pi * ρ^2) := by
      rw [h_rho2]
      rw [← ENNReal.ofReal_mul (show (0 : ℝ) ≤ Real.pi by positivity)]
      <;> ring
    rw [h_eq]
    exact h_lower
  have h_step2 : ENNReal.ofReal Real.pi ≤
      Kakeya.deltaTubeVolume ρ * (Kakeya.realRpowENN ρ 2)⁻¹ := by
    have h : ENNReal.ofReal Real.pi * Kakeya.realRpowENN ρ 2 ≤ Kakeya.deltaTubeVolume ρ := h_step
    have h' : ENNReal.ofReal Real.pi ≤
        Kakeya.deltaTubeVolume ρ * (Kakeya.realRpowENN ρ 2)⁻¹ := by
      calc
        ENNReal.ofReal Real.pi
          = ENNReal.ofReal Real.pi * (Kakeya.realRpowENN ρ 2) * (Kakeya.realRpowENN ρ 2)⁻¹ := by
            rw [mul_assoc, ENNReal.mul_inv_cancel h_rho2_ne_zero h_rho2_ne_top, mul_one]
        _ ≤ Kakeya.deltaTubeVolume ρ * (Kakeya.realRpowENN ρ 2)⁻¹ := by gcongr
    exact h'
  calc
    Kakeya.deltaTubeVolume σ
        ≤ ENNReal.ofReal (Real.pi * σ^2 * (1 + 2 * σ)) := h_upper
    _ ≤ ENNReal.ofReal (3 * Real.pi * σ^2) := h1
    _ = 3 * ENNReal.ofReal Real.pi * Kakeya.realRpowENN σ 2 := h_pi_sigma2
    _ ≤ 3 * (Kakeya.deltaTubeVolume ρ * (Kakeya.realRpowENN ρ 2)⁻¹) * Kakeya.realRpowENN σ 2 := by gcongr
    _ = 3 * Kakeya.realRpowENN σ 2 * (Kakeya.realRpowENN ρ 2)⁻¹ * Kakeya.deltaTubeVolume ρ := by ring

/--
Frostman extension: if `F` satisfies the concrete Frostman bound in `Tρ`, all bodies
are in `Tρ ⊆ Tσ`, and `volume Tσ ≤ R * volume Tρ`, then `F` satisfies the bound
with constant `C * R` in `Tσ`.
-/
lemma frostman_extension_concrete
    {F : Kakeya.Streamlined.BodyFamily} {Tρ Tσ : Set Point3} {C R : ENNReal}
    (hFrost : ∀ (K : Set Point3), Convex ℝ K → K ⊆ Tρ →
      F.containedMass K * volume Tρ ≤ C * F.containedMass Tρ * volume K)
    (h_contained : ∀ i, (F.body i).carrier ⊆ Tρ)
    (hTρ_conv : Convex ℝ Tρ)
    (h_sub : Tρ ⊆ Tσ)
    (h_vol_ratio : volume Tσ ≤ R * volume Tρ) :
    ∀ (K : Set Point3), Convex ℝ K → K ⊆ Tσ →
      F.containedMass K * volume Tσ ≤ (C * R) * F.containedMass Tσ * volume K := by
  have h_all_in_Tρ : ∀ i : Fin F.card, (F.body i).carrier ⊆ Tρ := h_contained
  have h_indices_Tρ : F.containedIndices Tρ = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro i
    simp only [Kakeya.Streamlined.BodyFamily.containedIndices, Finset.mem_filter, Finset.mem_univ, true_and]
    exact h_all_in_Tρ i
  have h_indices_Tσ : F.containedIndices Tσ = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro i
    simp only [Kakeya.Streamlined.BodyFamily.containedIndices, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Set.Subset.trans (h_all_in_Tρ i) h_sub
  have h_mass_eq : F.containedMass Tσ = F.containedMass Tρ := by
    simp only [Kakeya.Streamlined.BodyFamily.containedMass, h_indices_Tσ, h_indices_Tρ]
  intro K hK_conv hK_sub
  let K' := K ∩ Tρ
  have hK'_conv : Convex ℝ K' := hK_conv.inter hTρ_conv
  have hK'_sub : K' ⊆ Tρ := Set.inter_subset_right
  have h_indices_K : F.containedIndices K = F.containedIndices K' := by
    ext i
    simp only [Kakeya.Streamlined.BodyFamily.containedIndices, Finset.mem_filter]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun x hx => ⟨h2 hx, h_all_in_Tρ i hx⟩⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun x hx => (h2 hx).1⟩
  have h_mass_K : F.containedMass K = F.containedMass K' := by
    simp only [Kakeya.Streamlined.BodyFamily.containedMass, h_indices_K]
  have h_frost_K' := hFrost K' hK'_conv hK'_sub
  have h_vol_K' : volume K' ≤ volume K := measure_mono (Set.inter_subset_left)
  have h_goal : F.containedMass K * volume Tσ ≤ (C * R) * F.containedMass Tσ * volume K := by
    rw [h_mass_K]
    calc
      F.containedMass K' * volume Tσ
          ≤ F.containedMass K' * (R * volume Tρ) := by gcongr
      _ = R * (F.containedMass K' * volume Tρ) := by ring
      _ ≤ R * (C * F.containedMass Tρ * volume K') := by gcongr
      _ ≤ R * (C * F.containedMass Tρ * volume K) := by gcongr
      _ = (C * R) * F.containedMass Tσ * volume K := by
        rw [h_mass_eq] <;> ring
  exact h_goal

end Kakeya.Assouad
