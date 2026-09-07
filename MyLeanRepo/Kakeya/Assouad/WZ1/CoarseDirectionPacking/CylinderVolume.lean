import MyLeanRepo.Kakeya.Assouad.TubeVolumeScaling
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Cylinder volume computation

Volume of a right circular cylinder in `Point3`.

Whiteprint node: `Kakeya/WZ1CoarseDirectionPacking/CylinderVolume`.
-/

noncomputable section

open MeasureTheory Metric Set

namespace Kakeya.Assouad

/-- Volume of a right circular cylinder: interval length × disk area. -/
lemma cylinder_volume (a b r : ℝ) (ha : a ≤ b) (hr : 0 ≤ r) :
    volume {x : Point3 | x 0 ∈ Icc a b ∧ (x 1)^2 + (x 2)^2 ≤ r^2} =
      ENNReal.ofReal ((b - a) * Real.pi * r^2) := by
  let e_ofLp : Point3 ≃ᵐ (Fin 3 → ℝ) :=
    (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.toMeasurableEquiv
  let e_split : (Fin 3 → ℝ) ≃ᵐ (ℝ × (Fin 2 → ℝ)) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0
  let e_toLp2 : (Fin 2 → ℝ) ≃ᵐ Point2 :=
    (EuclideanSpace.equiv (Fin 2) ℝ).symm.toHomeomorph.toMeasurableEquiv
  let e : Point3 ≃ᵐ (ℝ × Point2) :=
    e_ofLp.trans e_split |>.trans ((MeasurableEquiv.refl ℝ).prodCongr e_toLp2)

  have h1 : MeasurePreserving e_ofLp volume volume :=
    PiLp.volume_preserving_ofLp (ι := Fin 3)
  have h2 : MeasurePreserving e_split volume volume :=
    MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0
  have h_vol1 : (volume : Measure (ℝ × (Fin 2 → ℝ))) = Measure.prod volume volume :=
    Measure.volume_eq_prod ℝ (Fin 2 → ℝ)
  have h_vol2 : (volume : Measure (ℝ × Point2)) = Measure.prod volume volume :=
    Measure.volume_eq_prod ℝ Point2
  have h3 : MeasurePreserving
      ((MeasurableEquiv.refl ℝ).prodCongr e_toLp2) volume volume := by
    have h_toLp2 : MeasurePreserving e_toLp2 volume volume :=
      PiLp.volume_preserving_toLp (ι := Fin 2)
    have h_prod : MeasurePreserving
        ((MeasurableEquiv.refl ℝ).prodCongr e_toLp2)
        (Measure.prod volume volume) (Measure.prod volume volume) :=
      MeasurePreserving.prod (MeasurePreserving.id volume) h_toLp2
    refine' ⟨((MeasurableEquiv.refl ℝ).prodCongr e_toLp2).measurable, _⟩
    rw [h_vol1]
    exact h_prod.map_eq.trans h_vol2.symm
  have hpres : MeasurePreserving e volume volume :=
    h1.trans h2 |>.trans h3

  let D : Set Point2 := Metric.closedBall 0 r
  let S : Set Point3 := {x | x 0 ∈ Icc a b ∧ (x 1)^2 + (x 2)^2 ≤ r^2}

  have h_e_app : ∀ (x : Point3), e x = (x 0, WithLp.toLp 2 (fun i : Fin 2 => x i.succ)) := by
    intro x
    rfl
  have h_e_symm_app : ∀ (s : ℝ) (y : Point2),
      (e.symm (s, y) : Point3) 0 = s ∧
      (WithLp.toLp 2 (fun i : Fin 2 => (e.symm (s, y) : Point3) i.succ) : Point2) = y := by
    intro s y
    have h_ex : e (e.symm (s, y)) = (s, y) := e.apply_symm_apply (s, y)
    have h_first : (e.symm (s, y) : Point3) 0 = s := by
      have h : (e (e.symm (s, y))).1 = (e.symm (s, y) : Point3) 0 := by rfl
      rw [h_ex] at h
      exact h.symm
    have h_second : (WithLp.toLp 2 (fun i : Fin 2 => (e.symm (s, y) : Point3) i.succ) : Point2) = y := by
      have h : (e (e.symm (s, y))).2 = (WithLp.toLp 2 (fun i : Fin 2 => (e.symm (s, y) : Point3) i.succ)) := by rfl
      rw [h_ex] at h
      exact h
    exact ⟨h_first, h_second⟩

  have h_image : e '' S = (Icc a b) ×ˢ D := by
    ext ⟨s, y⟩
    simp only [Set.mem_image, Set.mem_prod, Set.mem_setOf_eq]
    constructor
    · rintro ⟨x, hx, h_eq⟩
      have h_e_x : e x = (s, y) := h_eq
      have h1 : x 0 ∈ Icc a b := hx.1
      have h2 : (x 1)^2 + (x 2)^2 ≤ r^2 := hx.2
      have h3 : ‖(WithLp.toLp 2 (fun i : Fin 2 => x i.succ) : Point2)‖ ≤ r := by
        rw [PiLp.norm_eq_of_L2]
        have h4 : ∑ i : Fin 2, ‖(WithLp.toLp 2 (fun i : Fin 2 => x i.succ) : Point2) i‖ ^ 2
            = (x 1)^2 + (x 2)^2 := by
          simp [Fin.sum_univ_succ] <;> ring
        rw [h4]
        rw [Real.sqrt_le_left (by positivity)]
        exact h2
      have h_s : x 0 = s := by
        have h : (e x).1 = x 0 := by rfl
        rw [h_e_x] at h
        exact h.symm
      have h_y : (WithLp.toLp 2 (fun i : Fin 2 => x i.succ) : Point2) = y := by
        have h : (e x).2 = (WithLp.toLp 2 (fun i : Fin 2 => x i.succ)) := by rfl
        rw [h_e_x] at h
        exact h.symm
      rw [h_y] at h3
      have h_s' : s = x 0 := h_s.symm
      exact ⟨by rwa [h_s'], by simpa [D, Metric.mem_closedBall] using h3⟩
    · rintro ⟨h1, h2⟩
      set x : Point3 := e.symm (s, y) with hx_def
      have h_ex : e x = (s, y) := e.apply_symm_apply (s, y)
      have h_symm := h_e_symm_app s y
      have hx0 : x 0 = s := h_symm.1
      have hxy : (WithLp.toLp 2 (fun i : Fin 2 => x i.succ) : Point2) = y := h_symm.2
      have h3 : ‖y‖ ≤ r := by simpa [D, Metric.mem_closedBall] using h2
      have h4 : (x 1)^2 + (x 2)^2 ≤ r^2 := by
        have h5 : ‖(WithLp.toLp 2 (fun i : Fin 2 => x i.succ) : Point2)‖ ≤ r := by
          rw [hxy] <;> exact h3
        rw [PiLp.norm_eq_of_L2] at h5
        have h6 : ∑ i : Fin 2, ‖(WithLp.toLp 2 (fun i : Fin 2 => x i.succ) : Point2) i‖ ^ 2
            = (x 1)^2 + (x 2)^2 := by
          simp [Fin.sum_univ_succ] <;> ring
        rw [h6] at h5
        have h7 : Real.sqrt ((x 1)^2 + (x 2)^2) ≤ r := h5
        have h8 : 0 ≤ (x 1)^2 + (x 2)^2 := by positivity
        have h10 : (x 1)^2 + (x 2)^2 ≤ r^2 := by
          calc
            (x 1)^2 + (x 2)^2 ≤ (Real.sqrt ((x 1)^2 + (x 2)^2)) ^ 2 := by
                rw [Real.sq_sqrt h8]
            _ ≤ r ^ 2 := by gcongr
        exact h10
      refine ⟨x, ⟨by rw [hx0] <;> exact h1, h4⟩, h_ex⟩

  have hS_closed : IsClosed S := by
    have h0 : Continuous (fun x : Point3 => x 0) := by fun_prop
    have h1 : Continuous (fun x : Point3 => x 1) := by fun_prop
    have h2 : Continuous (fun x : Point3 => x 2) := by fun_prop
    apply IsClosed.inter
    · exact isClosed_Icc.preimage h0
    · have h_cont : Continuous (fun x : Point3 => (x 1)^2 + (x 2)^2) :=
        h1.pow 2 |>.add (h2.pow 2)
      exact isClosed_Iic.preimage h_cont
  have hS_meas : MeasurableSet S := hS_closed.measurableSet
  have h_image_meas : MeasurableSet (e '' S) := e.measurableSet_image.mpr hS_meas
  have hvol_img : volume (e '' S) = volume S := by
    have h_map : Measure.map e volume = volume := hpres.map_eq
    have h_preimage : e ⁻¹' (e '' S) = S := e.preimage_image S
    have h1 : (Measure.map e volume) (e '' S) = volume S := by
      rw [Measure.map_apply e.measurable h_image_meas, h_preimage]
    have h2 : volume (e '' S) = (Measure.map e volume) (e '' S) := by
      rw [h_map]
    rw [h2]
    exact h1
  have hvol1 : volume S = volume ((Icc a b) ×ˢ D) := by
    rw [← hvol_img, h_image]
  rw [hvol1]
  have hvol2 : volume ((Icc a b) ×ˢ D) = volume (Icc a b) * volume D := by
    rw [h_vol2]
    exact Measure.prod_prod _ _
  rw [hvol2]
  have h_Icc : volume (Icc a b) = ENNReal.ofReal (b - a) := by
    rw [Real.volume_Icc] <;> simp [ha] <;> ring
  rw [h_Icc]
  have hD_vol : volume D = ENNReal.ofReal (Real.pi * r^2) := by
    have h_open : volume (Metric.ball (0 : Point2) r) =
        ENNReal.ofReal r ^ 2 * ENNReal.ofReal Real.pi := by
      rw [EuclideanSpace.volume_ball_fin_two] <;> ring
    have h_closed : volume D = volume (Metric.ball (0 : Point2) r) := by
      have h : D = Metric.closedBall (0 : Point2) r := by rfl
      rw [h]
      exact Measure.addHaar_closedBall_eq_addHaar_ball volume 0 r
    rw [h_closed, h_open]
    have h_r2 : ENNReal.ofReal r ^ 2 = ENNReal.ofReal (r ^ 2) := by
      rw [← ENNReal.ofReal_pow] <;> linarith
    rw [h_r2]
    have h_pos1 : 0 ≤ r ^ 2 := by positivity
    have h_pos2 : 0 ≤ Real.pi := Real.pi_nonneg
    have h : ENNReal.ofReal (r ^ 2 * Real.pi) =
        ENNReal.ofReal (r ^ 2) * ENNReal.ofReal Real.pi :=
      ENNReal.ofReal_mul (hp := h_pos1)
    rw [h.symm]
    have h_real : r ^ 2 * Real.pi = Real.pi * r ^ 2 := by ring
    rw [h_real]
  rw [hD_vol]
  have hpos1 : 0 ≤ b - a := by linarith
  have hpos2 : 0 ≤ Real.pi * r ^ 2 := by positivity
  have h_mul : ENNReal.ofReal (b - a) * ENNReal.ofReal (Real.pi * r^2) =
      ENNReal.ofReal ((b - a) * Real.pi * r^2) := by
    have h_eq : ENNReal.ofReal ((b - a) * (Real.pi * r^2)) =
        ENNReal.ofReal (b - a) * ENNReal.ofReal (Real.pi * r^2) :=
      ENNReal.ofReal_mul (hp := hpos1)
    have h_real : (b - a) * (Real.pi * r^2) = (b - a) * Real.pi * r^2 := by ring
    rw [h_real] at h_eq
    exact h_eq.symm
  exact h_mul

end Kakeya.Assouad
