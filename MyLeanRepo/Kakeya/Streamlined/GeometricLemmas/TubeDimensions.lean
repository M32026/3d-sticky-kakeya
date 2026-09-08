import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.DilatedTubeContainment
import MyLeanRepo.Kakeya.Streamlined.ThickenedShadingDensity.BoxThickeningBound
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Dimensions of a delta-tube

A delta-tube has Euclidean dimensions `delta × delta × 1` up to the universal
factor `3`.
-/

noncomputable section

open Metric Set

namespace Kakeya.Streamlined.GeometricLemmas

private def e2 : Point3 :=
  EuclideanSpace.single (2 : Fin 3) 1

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
    have hi2 : (i : Fin 3) = 2 :=
      congr_arg (fun x : s2 => (x : Fin 3)) hi
    have hvalue : (s2.restrict v) i = u := by
      simp [Set.restrict, v, hi2]
    rw [hvalue]
    exact hu
  have h_finrank :
      Module.finrank ℝ Point3 = Fintype.card (Fin 3) := by
    simp
  rcases Orthonormal.exists_orthonormalBasis_extension_of_card_eq
      h_finrank (s := s2) h_orth with ⟨b, hb⟩
  have hb2 : b 2 = u := by
    have h : b 2 = (s2.restrict v) z2 := hb 2 (by simp [s2])
    rw [h]
    simp [Set.restrict, v, z2]
  let L : Point3 ≃ₗᵢ[ℝ] Point3 :=
    OrthonormalBasis.equiv b0 b (Equiv.refl (Fin 3))
  have h_basis : L (b0 2) = b 2 :=
    OrthonormalBasis.equiv_apply_basis b0 b (Equiv.refl (Fin 3)) 2
  have hb0 : b0 2 = e2 :=
    EuclideanSpace.basisFun_apply (Fin 3) ℝ 2
  refine ⟨L, ?_⟩
  rw [← hb2, ← h_basis, hb0]

private lemma unitSegment_convex (base direction : Point3) :
    Convex ℝ (Kakeya.unitSegment base direction) := by
  have h_sub : (base + direction) - base = direction := by simp
  have h_eq :
      Kakeya.unitSegment base direction =
        segment ℝ base (base + direction) := by
    rw [segment_eq_image']
    apply Set.ext
    intro x
    simp only [Kakeya.unitSegment, Set.mem_image]
    constructor
    · rintro ⟨t, ht, hxt⟩
      refine ⟨t, ht, ?_⟩
      rw [h_sub] at *
      exact hxt
    · rintro ⟨t, ht, hxt⟩
      refine ⟨t, ht, ?_⟩
      rw [h_sub] at *
      exact hxt
  rw [h_eq]
  exact convex_segment _ _

/-- A delta-tube has dimensions `delta × delta × 1` up to factor `3`. -/
lemma deltaTube_hasDimensions {delta : ℝ}
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (T : Kakeya.DeltaTube delta) :
    (tubeBody T).HasDimensions delta delta 1 3 := by
  rcases exists_linearIsometryEquiv_map_e2
      T.direction T.direction_unit with ⟨L, hL⟩
  let midpoint := tubeMidpoint T
  let frame : Point3 ≃ᵃⁱ[ℝ] Point3 :=
    AffineIsometryEquiv.mk'
      (fun x : Point3 => L x + midpoint)
      L
      (0 : Point3)
      (by intro x; simp [vadd_eq_add] <;> ring)

  have h_frame_apply :
      ∀ x : Point3, frame x = L x + midpoint := by
    intro x
    rfl
  have hL_e2 : L e2 = T.direction := hL

  have h_inner :
      frame '' axisBox delta delta 1 ⊆ T.carrier := by
    intro z hz
    rcases hz with ⟨x, hx, rfl⟩
    have hx0 : |x 0| ≤ delta / 2 := hx.1
    have hx1 : |x 1| ≤ delta / 2 := hx.2.1
    have hx2 : |x 2| ≤ 1 / 2 := hx.2.2
    have hx2_left : -(1 / 2 : ℝ) ≤ x 2 :=
      (abs_le.mp hx2).1
    have hx2_right : x 2 ≤ (1 / 2 : ℝ) :=
      (abs_le.mp hx2).2
    let t : ℝ := x 2 + 1 / 2
    have ht0 : 0 ≤ t := by
      dsimp only [t]
      linarith
    have ht1 : t ≤ 1 := by
      dsimp only [t]
      linarith
    let y : Point3 := T.base + t • T.direction
    have hy_in_seg :
        y ∈ Kakeya.unitSegment T.base T.direction :=
      ⟨t, ⟨ht0, ht1⟩, rfl⟩
    have h_y_eq :
        y = midpoint + (x 2) • T.direction := by
      simp [y, midpoint, tubeMidpoint, t, add_smul] <;> abel
    have h1 :
        frame x - y = L (x - (x 2) • e2) := by
      rw [h_frame_apply, h_y_eq]
      have h2 :
          L x + midpoint -
              (midpoint + (x 2) • T.direction) =
            L x - (x 2) • T.direction := by
        abel
      rw [h2]
      have h3 :
          (x 2) • T.direction = L ((x 2) • e2) := by
        rw [L.map_smul, hL_e2]
      rw [h3, ← L.map_sub]
      <;> rfl
    have h_norm :
        ‖frame x - y‖ = ‖x - (x 2) • e2‖ := by
      rw [h1, L.norm_map]
    have he2_0 : e2 0 = 0 := by
      simp [e2, EuclideanSpace.single]
    have he2_1 : e2 1 = 0 := by
      simp [e2, EuclideanSpace.single]
    have he2_2 : e2 2 = 1 := by
      simp [e2, EuclideanSpace.single]
    have h_coord0 :
        (x - (x 2) • e2) 0 = x 0 := by
      simp [he2_0] <;> ring
    have h_coord1 :
        (x - (x 2) • e2) 1 = x 1 := by
      simp [he2_1] <;> ring
    have h_coord2 :
        (x - (x 2) • e2) 2 = 0 := by
      simp [he2_2] <;> ring
    have h5 :
        ‖x - (x 2) • e2‖ ^ 2 =
          (x 0) ^ 2 + (x 1) ^ 2 := by
      have h_inner :
          inner ℝ (x - (x 2) • e2)
              (x - (x 2) • e2) =
            (x 0) ^ 2 + (x 1) ^ 2 := by
        rw [PiLp.inner_apply]
        have h_sum :
            ∑ i : Fin 3,
                (x - (x 2) • e2) i *
                  (x - (x 2) • e2) i =
              (x 0) ^ 2 + (x 1) ^ 2 := by
          rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
          <;> simp [h_coord0, h_coord1, h_coord2, he2_2]
          <;> ring
        exact h_sum
      have h_norm2 :
          ‖x - (x 2) • e2‖ ^ 2 =
            inner ℝ (x - (x 2) • e2)
              (x - (x 2) • e2) := by
        rw [real_inner_self_eq_norm_sq]
      rw [h_norm2, h_inner]
    have h7 : (x 0) ^ 2 ≤ (delta / 2) ^ 2 := by
      have h71 : |x 0| ≤ |delta / 2| := by
        have hpos : 0 ≤ delta / 2 := by linarith
        rw [abs_of_nonneg hpos] at *
        exact hx0
      exact sq_le_sq.mpr h71
    have h8 : (x 1) ^ 2 ≤ (delta / 2) ^ 2 := by
      have h81 : |x 1| ≤ |delta / 2| := by
        have hpos : 0 ≤ delta / 2 := by linarith
        rw [abs_of_nonneg hpos] at *
        exact hx1
      exact sq_le_sq.mpr h81
    have h6 : ‖x - (x 2) • e2‖ ^ 2 ≤ delta ^ 2 := by
      rw [h5]
      nlinarith
    have h9 : 0 ≤ ‖x - (x 2) • e2‖ := by positivity
    have h10 : ‖x - (x 2) • e2‖ ≤ delta := by
      have h11 :
          |‖x - (x 2) • e2‖| ≤ |delta| :=
        sq_le_sq.mp h6
      simpa [abs_of_nonneg h9, abs_of_pos hdelta] using h11
    have h_dist : dist (frame x) y ≤ delta := by
      rw [dist_eq_norm, h_norm]
      exact h10
    have h_carrier_def :
        T.carrier =
          Metric.cthickening delta
            (Kakeya.unitSegment T.base T.direction) := by
      rfl
    rw [h_carrier_def]
    exact Metric.mem_cthickening_of_dist_le
      (frame x) y delta
      (Kakeya.unitSegment T.base T.direction)
      hy_in_seg h_dist

  have hsegment :
      extendedSegment 1 T ⊆
        frame '' axisBox delta delta 1 := by
    rintro z ⟨y, hy, rfl⟩
    rcases hy with ⟨t, ht, rfl⟩
    let s : ℝ := t - 1 / 2
    let x : Point3 := s • e2
    have hs_abs : |s| ≤ 1 / 2 := by
      have h_eq : s = t - 1 / 2 := by rfl
      rw [h_eq, abs_le]
      constructor <;> linarith [ht.1, ht.2]
    have hx_box : x ∈ axisBox delta delta 1 := by
      constructor
      · simp [x, e2] <;> linarith
      constructor
      · simp [x, e2] <;> linarith
      · simpa [x, e2] using hs_abs
    refine ⟨x, hx_box, ?_⟩
    have hLx : L x = s • T.direction := by
      rw [show x = s • e2 by rfl, L.map_smul, hL_e2]
    change L x + midpoint =
      AffineMap.homothety midpoint 1
        (T.base + t • T.direction)
    rw [hLx, AffineMap.homothety_apply]
    ext i
    simp [midpoint, tubeMidpoint, s, vsub_eq_sub] <;> ring

  have h1 : T.carrier = dilatedTubeCarrier 1 T := by
    ext z
    simp [dilatedTubeCarrier]
    <;> abel
  have hdilated :
      dilatedTubeCarrier 1 T ⊆
        Metric.cthickening (1 * delta) (extendedSegment 1 T) :=
    dilatedTubeCarrier_subset_cthickening_extendedSegment
      (by norm_num) hdelta.le T
  have hthick_mono :
      Metric.cthickening (1 * delta) (extendedSegment 1 T) ⊆
        Metric.cthickening (1 * delta)
          (frame '' axisBox delta delta 1) :=
    Metric.cthickening_subset_of_subset (1 * delta) hsegment
  have hthick_frame :
      Metric.cthickening (1 * delta)
          (frame '' axisBox delta delta 1) =
        frame ''
          Metric.cthickening (1 * delta)
            (axisBox delta delta 1) :=
    (AffineIsometryEquiv.cthickening_image frame
      (axisBox delta delta 1) (1 * delta)).symm
  have hbox_raw :
      Metric.cthickening (1 * delta)
          (axisBox delta delta 1) ⊆
        axisBox
          (delta + 2 * (1 * delta))
          (delta + 2 * (1 * delta))
          (1 + 2 * (1 * delta)) :=
    cthickening_axisBox_subset
      delta delta 1 (1 * delta)
      hdelta hdelta (by norm_num) (by positivity)
  have h_eq1 :
      delta + 2 * (1 * delta) = 3 * delta := by
    ring
  have h_eq2 :
      1 + 2 * (1 * delta) = 1 + 2 * delta := by
    ring
  have hbox :
      Metric.cthickening (1 * delta)
          (axisBox delta delta 1) ⊆
        axisBox (3 * delta) (3 * delta) (1 + 2 * delta) := by
    rw [h_eq1, h_eq2] at hbox_raw
    exact hbox_raw
  have hfinal :
      axisBox (3 * delta) (3 * delta) (1 + 2 * delta) ⊆
        axisBox (3 * delta) (3 * delta) 3 := by
    intro z hz
    constructor
    · exact hz.1
    constructor
    · exact hz.2.1
    · calc
        |z 2| ≤ (1 + 2 * delta) / 2 := hz.2.2
        _ ≤ 3 / 2 := by linarith [hdelta1]
  have h_outer3 :
      T.carrier ⊆
        frame '' axisBox (3 * delta) (3 * delta) 3 := by
    rw [h1]
    calc
      dilatedTubeCarrier 1 T
          ⊆ Metric.cthickening (1 * delta)
              (extendedSegment 1 T) :=
        hdilated
      _ ⊆ Metric.cthickening (1 * delta)
            (frame '' axisBox delta delta 1) :=
        hthick_mono
      _ = frame ''
            Metric.cthickening (1 * delta)
              (axisBox delta delta 1) :=
        hthick_frame
      _ ⊆ frame ''
            axisBox (3 * delta) (3 * delta)
              (1 + 2 * delta) :=
        Set.image_mono hbox
      _ ⊆ frame '' axisBox (3 * delta) (3 * delta) 3 :=
        Set.image_mono hfinal
  have h_outer :
      T.carrier ⊆
        frame '' axisBox
          (3 * delta) (3 * delta) (3 * 1) := by
    have h31 : (3 * 1 : ℝ) = 3 := by ring
    simpa [h31] using h_outer3

  have h_carrier_eq : (tubeBody T).carrier = T.carrier := by
    rfl
  refine ⟨frame, ?_⟩
  exact
    ⟨hdelta, by linarith, hdelta1, by norm_num, h_inner, by
      rw [h_carrier_eq]
      exact h_outer⟩

/-- All bodies in a tube family are convex. -/
lemma tubeFamily_bodies_convex {delta : ℝ} (F : TubeFamily delta) :
    F.toBodyFamily.IsConvex := by
  intro i
  have h_seg :
      Convex ℝ
        (Kakeya.unitSegment
          (F.tube i).base (F.tube i).direction) :=
    unitSegment_convex
      (F.tube i).base (F.tube i).direction
  have h_tube_convex :
      Convex ℝ (F.tube i).carrier := by
    have h_eq :
        (F.tube i).carrier =
          Metric.cthickening delta
            (Kakeya.unitSegment
              (F.tube i).base (F.tube i).direction) := by
      rfl
    rw [h_eq]
    exact h_seg.cthickening delta
  have h_body_carrier :
      (F.toBodyFamily.body i).carrier =
        (F.tube i).carrier := by
    rfl
  simpa [Body.IsConvex, h_body_carrier] using h_tube_convex

end Kakeya.Streamlined.GeometricLemmas
