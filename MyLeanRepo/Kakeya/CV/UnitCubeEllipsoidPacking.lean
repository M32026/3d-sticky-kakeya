import MyLeanRepo.Kakeya.CV.Targets.UnitCubeEllipsoidPacking.VolumeLemmas
import MyLeanRepo.Kakeya.CV.Targets.UnitCubeEllipsoidPacking.ScalingLemmas
import MyLeanRepo.Kakeya.CV.Targets.EllipsoidTranslatePacking.VolumeScaling
import MyLeanRepo.Kakeya.CV.Statements

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace Kakeya.CV

theorem unitCube_ellipsoid_translate_packing
    (hPacking : EllipsoidTranslatePackingStatement) :
    UnitCubeEllipsoidPackingStatement := by
  rcases hPacking with ⟨C, hC_pos, hMain⟩
  let C' : NNReal := 8 * C
  have hC'_pos : 0 < C' := mul_pos (by norm_num) hC_pos
  refine' ⟨C', hC'_pos, _⟩
  intro A η c hη hcontain
  set η' : ℝ := 2 * η with hη'_def
  have hη'_pos : 0 < η' := by positivity
  have h_eq1 : 2 * η' = 4 * η := by
    simp [hη'_def] <;> ring
  have hcontain' : scaledEllipsoid A (2 * η') 0 ⊆ unitBall 3 := by
    have h_set : scaledEllipsoid A (2 * η') 0 = scaledEllipsoid A (4 * η) 0 := by
      congr
    rw [h_set]
    exact hcontain
  have hResult := hMain A η' hη'_pos hcontain'
  rcases hResult with ⟨n, z, h1_ball, h2_disj, h3_lower, h4_upper⟩
  let w : Fin n → Point 3 := fun i => c + (1 / 2 : ℝ) • (z i)
  have h1_cube : ∀ i, scaledEllipsoid A η (w i) ⊆ unitCube c := by
    intro i
    exact scaledEllipsoid_half_containment A η hη (z i) c (h1_ball i)
  have h2_cube : Pairwise (fun i j : Fin n =>
      Disjoint (scaledEllipsoid A η (w i)) (scaledEllipsoid A η (w j))) := by
    intro i j hne
    exact scaledEllipsoid_half_disjoint A η (z i) (z j) c (h2_disj hne)
  set V : ENNReal := volume (scaledEllipsoid A η 0) with hV_def
  set V2 : ENNReal := volume (scaledEllipsoid A η' 0) with hV2_def
  set B : ENNReal := volume (unitBall 3) with hB_def
  set Cube : ENNReal := volume (unitCube c) with hCube_def
  have hV2_eq : V2 = 8 * V := by
    rw [hV2_def, hV_def, hη'_def]
    exact volume_scaledEllipsoid_double A η hη 0
  have hV_pos : 0 < V := volume_scaledEllipsoid_pos A η hη 0
  have hV_ne_zero : V ≠ 0 := hV_pos.ne'
  have hV_lt_top : V < ⊤ := by
    have h_formula : V = ENNReal.ofReal (η ^ 3 * |LinearMap.det (A : Point 3 →ₗ[ℝ] Point 3)|) * B := by
      rw [hV_def, hB_def]
      exact volume_affine_ball A η hη 0
    rw [h_formula]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top volume_unitBall_lt_top
  have hV_ne_top : V ≠ ⊤ := hV_lt_top.ne
  have hB_lt_top : B < ⊤ := volume_unitBall_lt_top
  have hB_ne_top : B ≠ ⊤ := hB_lt_top.ne
  have hCube_eq1 : Cube = 1 := by
    rw [hCube_def]
    exact volume_unitCube c
  have hB_le8 : B ≤ 8 := by
    rw [hB_def]
    exact unitBall_volume_le_eight
  have h1_le_B : (1 : ENNReal) ≤ B := by
    have h : volume (unitCube (0 : Point 3)) ≤ B := by
      rw [hB_def]
      exact measure_mono unitCube_zero_subset_unitBall
    rw [volume_unitCube (0 : Point 3)] at h
    exact h
  have h8_pos : (8 : ENNReal) ≠ 0 := by norm_num
  have h8_top : (8 : ENNReal) ≠ ⊤ := by norm_num
  have h8V_pos : (8 * V) ≠ 0 := mul_ne_zero h8_pos hV_ne_zero
  have h8V_top : (8 * V) ≠ ⊤ := ENNReal.mul_ne_top h8_top hV_ne_top
  have hC_top : (C : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hCB_top : ((C : ENNReal) * B) ≠ ⊤ := ENNReal.mul_ne_top hC_top hB_ne_top
  rw [hV2_eq] at h3_lower h4_upper
  -- Lower bound
  have h3_mult : B ≤ (C : ENNReal) * (n : ENNReal) * (8 * V) := by
    have h : (B / (8 * V)) * (8 * V) ≤ ((C : ENNReal) * (n : ENNReal)) * (8 * V) := by gcongr
    have h_cancel : (B / (8 * V)) * (8 * V) = B := by
      have h' : (8 * V) * (B / (8 * V)) = B := ENNReal.mul_div_cancel h8V_pos h8V_top
      have h'' : (B / (8 * V)) * (8 * V) = (8 * V) * (B / (8 * V)) := mul_comm _ _
      rw [h'']
      exact h'
    rw [h_cancel] at h
    simpa [mul_assoc] using h
  have h3_divV : B / V ≤ (C : ENNReal) * (n : ENNReal) * 8 := by
    have h : B / V ≤ (((C : ENNReal) * (n : ENNReal) * (8 * V)) / V) := by gcongr
    have h_cancel2 : (((C : ENNReal) * (n : ENNReal) * (8 * V)) / V) =
        (C : ENNReal) * (n : ENNReal) * 8 := by
      have h_eq1 : ((C : ENNReal) * (n : ENNReal) * (8 * V)) =
          (((C : ENNReal) * (n : ENNReal) * 8) * V) := by
        simp [mul_assoc] <;> ring
      rw [h_eq1]
      exact ENNReal.mul_div_cancel_right hV_ne_zero hV_ne_top
    rw [h_cancel2] at h
    exact h
  have h_lower_final : Cube / V ≤ (C' : ENNReal) * (n : ENNReal) := by
    have h4 : Cube / V ≤ B / V := by
      rw [hCube_eq1]
      gcongr
    have h_reorder : (C : ENNReal) * (n : ENNReal) * 8 = (C' : ENNReal) * (n : ENNReal) := by
      simp [C', mul_assoc, mul_comm, mul_left_comm]
    have h5 : B / V ≤ (C' : ENNReal) * (n : ENNReal) := by
      rw [h_reorder] at h3_divV
      exact h3_divV
    exact h4.trans h5
  -- Upper bound
  have h4_mult : (n : ENNReal) * (8 * V) ≤ (C : ENNReal) * B := by
    have h : ((n : ENNReal) * (8 * V)) ≤ ((C : ENNReal) * B / (8 * V)) * (8 * V) := by gcongr
    have h_cancel : ((C : ENNReal) * B / (8 * V)) * (8 * V) = (C : ENNReal) * B := by
      have h' : (8 * V) * (((C : ENNReal) * B) / (8 * V)) = (C : ENNReal) * B :=
        ENNReal.mul_div_cancel h8V_pos h8V_top
      have h'' : (((C : ENNReal) * B) / (8 * V)) * (8 * V) = (8 * V) * (((C : ENNReal) * B) / (8 * V)) := mul_comm _ _
      rw [h'']
      exact h'
    rw [h_cancel] at h
    exact h
  have h4_le8 : (n : ENNReal) * (8 * V) ≤ (C : ENNReal) * 8 := by
    calc (n : ENNReal) * (8 * V)
        ≤ (C : ENNReal) * B := h4_mult
      _ ≤ (C : ENNReal) * 8 := by gcongr
  have h4_div8 : (n : ENNReal) * V ≤ (C : ENNReal) := by
    have h : ((n : ENNReal) * (8 * V)) / 8 ≤ ((C : ENNReal) * 8) / 8 := by gcongr
    have h_cancel1 : ((n : ENNReal) * (8 * V)) / 8 = (n : ENNReal) * V := by
      have h_eq : ((n : ENNReal) * (8 * V)) = ((n : ENNReal) * V) * 8 := by
        simp [mul_assoc] <;> ring
      rw [h_eq]
      exact ENNReal.mul_div_cancel_right h8_pos h8_top
    have h_cancel2 : ((C : ENNReal) * 8) / 8 = (C : ENNReal) :=
      ENNReal.mul_div_cancel_right h8_pos h8_top
    rw [h_cancel1, h_cancel2] at h
    exact h
  have h4_divV : (n : ENNReal) ≤ (C : ENNReal) / V := by
    have h : ((n : ENNReal) * V) / V ≤ (C : ENNReal) / V := by gcongr
    have h_cancel : ((n : ENNReal) * V) / V = (n : ENNReal) :=
      ENNReal.mul_div_cancel_right hV_ne_zero hV_ne_top
    rw [h_cancel] at h
    exact h
  have h_upper_final : (n : ENNReal) ≤ (C' : ENNReal) * Cube / V := by
    have hC_le : (C : ENNReal) ≤ (C' : ENNReal) := by
      have h : (C : ENNReal) ≤ (8 : ENNReal) * (C : ENNReal) :=
        le_mul_of_one_le_left (by positivity) (by norm_num)
      simpa [C'] using h
    have h6 : (C : ENNReal) / V ≤ (C' : ENNReal) / V := by gcongr
    have h7 : (n : ENNReal) ≤ (C' : ENNReal) / V := h4_divV.trans h6
    have h8 : (C' : ENNReal) / V = (C' : ENNReal) * Cube / V := by
      rw [hCube_eq1] <;> simp
    rw [h8] at h7
    exact h7
  exact ⟨n, w, h1_cube, h2_cube, h_lower_final, h_upper_final⟩

end Kakeya.CV
