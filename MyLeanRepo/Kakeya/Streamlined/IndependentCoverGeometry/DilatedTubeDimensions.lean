import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.DilatedTubeContainment
import MyLeanRepo.Kakeya.Streamlined.ThickenedShadingDensity.BoxThickeningBound
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# A framed outer plank for a dilated tube

The phase-space packing theorem expects a body with two displayed transverse
dimensions and one displayed unit axial dimension.  A homothetically dilated
`rho`-tube is contained in such a body with one universal comparability
constant.
-/

noncomputable section

namespace Kakeya.Streamlined

open Metric Set
open GeometricLemmas

namespace IndependentCoverGeometry

/-- The third standard coordinate vector. -/
private def e2 : Point3 :=
  EuclideanSpace.single (2 : Fin 3) 1

/-- Complete a unit vector to an orthonormal frame whose third axis is that vector. -/
private lemma exists_linearIsometryEquiv_map_e2
    (u : Point3) (hu : ‖u‖ = 1) :
    ∃ L : Point3 ≃ₗᵢ[ℝ] Point3, L e2 = u := by
  let b0 := EuclideanSpace.basisFun (Fin 3) ℝ
  let v : Fin 3 → Point3 := fun i => if i = 2 then u else 0
  let s2 : Set (Fin 3) := {2}
  let z2 : s2 := ⟨2, by simp [s2]⟩
  have h_orth : Orthonormal ℝ (s2.restrict v) := by
    rw [orthonormal_subsingleton_iff]
    intro i
    have hi : i = z2 := Subsingleton.elim i z2
    have hvalue : (s2.restrict v) i = u := by
      have hi2 : (i : Fin 3) = 2 :=
        congr_arg (fun x : s2 => (x : Fin 3)) hi
      simp [Set.restrict, v, hi2]
    rw [hvalue]
    exact hu
  have h_finrank :
      Module.finrank ℝ Point3 = Fintype.card (Fin 3) := by
    simp
  rcases Orthonormal.exists_orthonormalBasis_extension_of_card_eq
      h_finrank (s := s2) h_orth with
    ⟨b, hb⟩
  have hb2 : b 2 = u := by
    have h : b 2 = (s2.restrict v) z2 := hb 2 (by simp [s2])
    calc
      b 2 = (s2.restrict v) z2 := h
      _ = u := by
        simp [Set.restrict, v, z2]
  let L : Point3 ≃ₗᵢ[ℝ] Point3 :=
    OrthonormalBasis.equiv b0 b (Equiv.refl (Fin 3))
  have h_basis :
      L (b0 2) = b 2 :=
    OrthonormalBasis.equiv_apply_basis b0 b (Equiv.refl (Fin 3)) 2
  have hb0 : b0 2 = e2 :=
    EuclideanSpace.basisFun_apply (Fin 3) ℝ 2
  refine ⟨L, ?_⟩
  rw [← hb2, ← h_basis, hb0]

/--
The `B`-dilation of a radius-`rho` tube lies in a framed
`rho × rho × 1` plank with comparability factor `3 * B`.
-/
theorem exists_dilatedTube_outer_plank_general
    {rho B : ℝ} (hB : 1 ≤ B)
    (hrho : 0 < rho) (hrho_one : rho ≤ 1)
    (T : Kakeya.DeltaTube rho) :
    ∃ plank : Body,
      ∃ frame : Point3 ≃ᵃⁱ[ℝ] Point3,
        plank.HasDimensionsInFrame frame rho rho 1 (3 * B) ∧
          dilatedTubeCarrier B T ⊆ plank.carrier := by
  have hB_pos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  rcases exists_linearIsometryEquiv_map_e2 T.direction T.direction_unit with
    ⟨L, hL⟩
  let midpoint := tubeMidpoint T
  let frame : Point3 ≃ᵃⁱ[ℝ] Point3 :=
    AffineIsometryEquiv.mk'
      (fun x : Point3 => L x + midpoint)
      L 0
      (by
        intro x
        simp [vadd_eq_add]
        <;> ring)
  let plank : Body :=
    ⟨frame '' axisBox ((3 * B) * rho) ((3 * B) * rho) (3 * B)⟩

  have hsegment :
      extendedSegment B T ⊆
        frame '' axisBox rho rho B := by
    rintro z ⟨y, hy, rfl⟩
    rcases hy with ⟨t, ht, rfl⟩
    let s : ℝ := B * (t - 1 / 2)
    let x : Point3 := s • e2
    have ht_abs : |t - 1 / 2| ≤ 1 / 2 := by
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2]
    have hs_abs : |s| ≤ B / 2 := by
      rw [show s = B * (t - 1 / 2) by rfl, abs_mul,
        abs_of_pos hB_pos]
      nlinarith
    have hx_box : x ∈ axisBox rho rho B := by
      constructor
      · simp [x, e2]
        linarith
      constructor
      · simp [x, e2]
        linarith
      · simpa [x, e2] using hs_abs
    refine ⟨x, hx_box, ?_⟩
    have hLx : L x = s • T.direction := by
      rw [show x = s • e2 by rfl, L.map_smul, hL]
    change L x + midpoint =
      AffineMap.homothety midpoint B
        (T.base + t • T.direction)
    rw [hLx, AffineMap.homothety_apply]
    ext i
    simp [midpoint, tubeMidpoint, s, vsub_eq_sub]
    ring

  have hdilated :
      dilatedTubeCarrier B T ⊆
        Metric.cthickening (B * rho) (extendedSegment B T) :=
    dilatedTubeCarrier_subset_cthickening_extendedSegment
      hB_pos.le hrho.le T
  have hthick_mono :
      Metric.cthickening (B * rho) (extendedSegment B T) ⊆
        Metric.cthickening (B * rho)
          (frame '' axisBox rho rho B) :=
    Metric.cthickening_subset_of_subset (B * rho) hsegment
  have hthick_frame :
      Metric.cthickening (B * rho)
          (frame '' axisBox rho rho B) =
        frame '' Metric.cthickening (B * rho)
          (axisBox rho rho B) :=
    (AffineIsometryEquiv.cthickening_image frame
      (axisBox rho rho B) (B * rho)).symm
  have hbox :
      Metric.cthickening (B * rho) (axisBox rho rho B) ⊆
        axisBox (rho + 2 * (B * rho))
          (rho + 2 * (B * rho))
          (B + 2 * (B * rho)) :=
    cthickening_axisBox_subset rho rho B (B * rho)
      hrho hrho hB_pos (by positivity)
  have hexpanded :
      frame '' Metric.cthickening (B * rho)
          (axisBox rho rho B) ⊆
        frame '' axisBox (rho + 2 * (B * rho))
          (rho + 2 * (B * rho))
          (B + 2 * (B * rho)) :=
    Set.image_mono hbox
  have houter_box :
      axisBox (rho + 2 * (B * rho))
          (rho + 2 * (B * rho))
          (B + 2 * (B * rho)) ⊆
        axisBox ((3 * B) * rho) ((3 * B) * rho) (3 * B) := by
    intro x hx
    constructor
    · calc
        |x 0| ≤ (rho + 2 * (B * rho)) / 2 := hx.1
        _ ≤ ((3 * B) * rho) / 2 := by
          nlinarith [hB]
    constructor
    · calc
        |x 1| ≤ (rho + 2 * (B * rho)) / 2 := hx.2.1
        _ ≤ ((3 * B) * rho) / 2 := by
          nlinarith [hB]
    · calc
        |x 2| ≤ (B + 2 * (B * rho)) / 2 := hx.2.2
        _ ≤ (3 * B) / 2 := by
          nlinarith [mul_le_mul_of_nonneg_left hrho_one hB_pos.le]
  have hcarrier :
      dilatedTubeCarrier B T ⊆ plank.carrier := by
    intro x hx
    have hx1 := hdilated hx
    have hx2 := hthick_mono hx1
    rw [hthick_frame] at hx2
    have hx3 := hexpanded hx2
    exact Set.image_mono houter_box hx3

  have hinner :
      frame '' axisBox rho rho 1 ⊆ plank.carrier := by
    rintro z ⟨x, hx, rfl⟩
    refine ⟨x, ?_, rfl⟩
    constructor
    · calc
        |x 0| ≤ rho / 2 := hx.1
        _ ≤ ((3 * B) * rho) / 2 := by
          nlinarith [hB]
    constructor
    · calc
        |x 1| ≤ rho / 2 := hx.2.1
        _ ≤ ((3 * B) * rho) / 2 := by
          nlinarith [hB]
    · calc
        |x 2| ≤ 1 / 2 := hx.2.2
        _ ≤ (3 * B) / 2 := by nlinarith [hB]
  have houter :
      plank.carrier ⊆
        frame '' axisBox ((3 * B) * rho) ((3 * B) * rho)
          ((3 * B) * 1) := by
    simpa [plank]
  refine ⟨plank, frame, ?_, hcarrier⟩
  exact ⟨hrho, le_rfl, hrho_one, by nlinarith [hB], hinner, houter⟩

/--
The `13`-dilation of a radius-`rho` tube lies in a framed
`rho × rho × 1` plank with comparability factor `39`.
-/
theorem exists_dilatedTube_outer_plank
    {rho : ℝ} (hrho : 0 < rho) (hrho_one : rho ≤ 1)
    (T : Kakeya.DeltaTube rho) :
    ∃ plank : Body,
      ∃ frame : Point3 ≃ᵃⁱ[ℝ] Point3,
        plank.HasDimensionsInFrame frame rho rho 1 39 ∧
          dilatedTubeCarrier 13 T ⊆ plank.carrier := by
  rcases exists_dilatedTube_outer_plank_general
      (B := 13) (by norm_num) hrho hrho_one T with
    ⟨plank, frame, hdimensions, hcontain⟩
  exact ⟨plank, frame, by norm_num at hdimensions ⊢; exact hdimensions,
    hcontain⟩

end IndependentCoverGeometry

end Kakeya.Streamlined
