import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.CapsuleVolume
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.CloseAxialTubes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Normed.Module.Ball.Pointwise

noncomputable section

open Kakeya.Streamlined MeasureTheory Metric

namespace Kakeya.Streamlined.GeometricLemmas

/-- Upper bound instantiation: direct from capsule_volume_upper. -/
lemma capsule_upper_bound_instantiation : CapsuleUpperBound := by
  intro r hr
  have h1 : Kakeya.deltaTubeVolume r = volume (capsule r) := by rfl
  rw [h1]
  exact capsule_volume_upper r hr

/-- infEDist scaling under positive scalar L for image sets. -/
lemma infEDist_scale_image {L : ℝ} (hL : 0 < L) {s : Set Point3} {y : Point3} :
    infEDist (L • y) ((fun x : Point3 => L • x) '' s) =
    ENNReal.ofReal L * infEDist y s := by
  let c : ENNReal := ENNReal.ofReal L
  have hc_ne0 : c ≠ 0 := (ENNReal.ofReal_pos.mpr hL).ne'
  have hc_ne_top : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have h_nnreal : (‖(L : ℝ)‖₊ : ENNReal) = c := by
    have h1 : (‖(L : ℝ)‖₊ : ENNReal) = ENNReal.ofReal (‖(L : ℝ)‖₊ : ℝ) := ENNReal.coe_nnreal_eq _
    have h2 : (‖(L : ℝ)‖₊ : ℝ) = L := by
      simp [Real.nnnorm_of_nonneg hL.le] <;> norm_num
    rw [h1, h2] <;> rfl
  have h_edist : ∀ (x : Point3), edist (L • y) (L • x) = c * edist y x := by
    intro x
    have h := edist_smul₀ (L : ℝ) y x
    rw [h]
    have h2 : ‖(L : ℝ)‖₊ • edist y x = (‖(L : ℝ)‖₊ : ENNReal) * edist y x := by rfl
    rw [h2, h_nnreal]
  have h_ge : c * infEDist y s ≤ infEDist (L • y) ((fun x : Point3 => L • x) '' s) := by
    rw [Metric.le_infEDist]
    intro z hz
    rcases hz with ⟨x, hx, rfl⟩
    have h5 : infEDist y s ≤ edist y x := infEDist_le_edist_of_mem hx
    calc c * infEDist y s ≤ c * edist y x := by gcongr
      _ = edist (L • y) (L • x) := (h_edist x).symm
  have h_le : infEDist (L • y) ((fun x : Point3 => L • x) '' s) ≤ c * infEDist y s := by
    have h5 : c⁻¹ * infEDist (L • y) ((fun x : Point3 => L • x) '' s) ≤ infEDist y s := by
      rw [Metric.le_infEDist]
      intro x hx
      have h6 : L • x ∈ (fun x : Point3 => L • x) '' s := ⟨x, hx, rfl⟩
      have h7 : infEDist (L • y) ((fun x : Point3 => L • x) '' s) ≤ edist (L • y) (L • x) :=
        infEDist_le_edist_of_mem h6
      have h7' : infEDist (L • y) ((fun x : Point3 => L • x) '' s) ≤ c * edist y x := by
        rw [h_edist x] at h7
        exact h7
      have h8 : c⁻¹ * infEDist (L • y) ((fun x : Point3 => L • x) '' s) ≤ c⁻¹ * (c * edist y x) := by gcongr
      have h9 : c⁻¹ * (c * edist y x) = edist y x := by
        rw [←mul_assoc, ENNReal.inv_mul_cancel hc_ne0 hc_ne_top] <;> simp
      rw [h9] at h8
      exact h8
    have h10 : c * (c⁻¹ * infEDist (L • y) ((fun x : Point3 => L • x) '' s)) =
        infEDist (L • y) ((fun x : Point3 => L • x) '' s) := by
      rw [←mul_assoc, ENNReal.mul_inv_cancel hc_ne0 hc_ne_top] <;> simp
    calc infEDist (L • y) ((fun x : Point3 => L • x) '' s)
      = c * (c⁻¹ * infEDist (L • y) ((fun x : Point3 => L • x) '' s)) := h10.symm
    _ ≤ c * infEDist y s := by gcongr
  exact le_antisymm h_le h_ge

/-- Scaling of cthickening under positive scalar multiplication. -/
lemma cthickening_smul_point3 {L : ℝ} (hL : 0 < L) {r : ℝ} {s : Set Point3} :
    Metric.cthickening r ((fun x : Point3 => L • x) '' s) =
    (fun x : Point3 => L • x) '' Metric.cthickening (r / L) s := by
  have hL_ne : L ≠ 0 := hL.ne'
  let scale : Point3 → Point3 := fun x => L • x
  let c : ENNReal := ENNReal.ofReal L
  have hc_ne0 : c ≠ 0 := (ENNReal.ofReal_pos.mpr hL).ne'
  have hc_ne_top : c ≠ ⊤ := ENNReal.ofReal_ne_top
  ext x
  simp only [Set.mem_image, Metric.mem_cthickening_iff]
  constructor
  · -- Forward
    intro hx
    let y := (1 / L) • x
    have hy_eq : scale y = x := by
      simp [scale, y, smul_smul, hL_ne] <;> field_simp [hL_ne] <;> ring
    have h5 : infEDist (scale y) (scale '' s) ≤ ENNReal.ofReal r := by
      rw [hy_eq] <;> exact hx
    rw [infEDist_scale_image hL] at h5
    have h6 : infEDist y s ≤ ENNReal.ofReal (r / L) := by
      have h7 : c * infEDist y s ≤ ENNReal.ofReal r := h5
      have h8 : c⁻¹ * (c * infEDist y s) ≤ c⁻¹ * ENNReal.ofReal r := by gcongr
      have h9 : c⁻¹ * (c * infEDist y s) = infEDist y s := by
        rw [←mul_assoc, ENNReal.inv_mul_cancel hc_ne0 hc_ne_top] <;> simp
      have h10 : c⁻¹ * ENNReal.ofReal r = ENNReal.ofReal (r / L) := by
        rw [←ENNReal.ofReal_inv_of_pos hL, ←ENNReal.ofReal_mul (by positivity)] <;> ring
      rw [h9] at h8
      rw [h10] at h8
      exact h8
    exact ⟨y, h6, hy_eq⟩
  · -- Backward
    rintro ⟨y, hy, rfl⟩
    have h10 : infEDist (scale y) (scale '' s) = c * infEDist y s := infEDist_scale_image hL
    rw [h10]
    have h11 : infEDist y s ≤ ENNReal.ofReal (r / L) := hy
    have h12 : c * infEDist y s ≤ c * ENNReal.ofReal (r / L) := by gcongr
    have h13 : c * ENNReal.ofReal (r / L) = ENNReal.ofReal r := by
      rw [←ENNReal.ofReal_mul (by positivity)]
      <;> congr 1 <;> field_simp [hL_ne]
    rw [h13] at h12
    exact h12

/-- Volume scaling under positive scalar L in dimension 3. -/
lemma volume_smul3 {s : Set Point3} {L : ℝ} (hL : 0 < L) :
    volume ((fun x : Point3 => L • x) '' s) = ENNReal.ofReal (L ^ 3) * volume s := by
  let scale_lm : Point3 →ₗ[ℝ] Point3 := L • LinearMap.id
  have h_apply : ∀ x, scale_lm x = L • x := by intro x; rfl
  have h_det : LinearMap.det scale_lm = L ^ 3 := by
    rw [LinearMap.det_smul L LinearMap.id]
    have h_finrank : Module.finrank ℝ Point3 = 3 := by simp
    rw [h_finrank, LinearMap.det_id] <;> ring
  let H : Point3 ≃L[ℝ] Point3 :=
    { toFun := scale_lm
      invFun := fun x => (1 / L) • x
      left_inv := by intro x; simp [h_apply, smul_smul, hL.ne'] <;> field_simp [hL.ne'] <;> ring
      right_inv := by intro x; simp [h_apply, smul_smul, hL.ne'] <;> field_simp [hL.ne'] <;> ring
      map_add' := scale_lm.map_add
      map_smul' := scale_lm.map_smul
      continuous_toFun := LinearMap.continuous_of_finiteDimensional scale_lm
      continuous_invFun := continuous_const_smul (1 / L) }
  have h_image : H '' s = (fun x : Point3 => L • x) '' s := by
    ext z; simp [h_apply] <;> aesop
  have h_main : volume (H '' s) = ENNReal.ofReal |LinearMap.det (H : Point3 →ₗ[ℝ] Point3)| * volume s :=
    MeasureTheory.Measure.addHaar_image_continuousLinearEquiv volume H s
  have h_coe : (H : Point3 →ₗ[ℝ] Point3) = scale_lm := by rfl
  have h_abs : |L ^ 3| = L ^ 3 := by rw [abs_of_pos] <;> positivity
  calc volume ((fun x : Point3 => L • x) '' s)
    = volume (H '' s) := by rw [h_image]
  _ = ENNReal.ofReal |LinearMap.det (H : Point3 →ₗ[ℝ] Point3)| * volume s := h_main
  _ = ENNReal.ofReal |LinearMap.det scale_lm| * volume s := by rw [h_coe]
  _ = ENNReal.ofReal |L ^ 3| * volume s := by rw [h_det]
  _ = ENNReal.ofReal (L ^ 3) * volume s := by rw [h_abs]

/-- Lower bound instantiation via scaling + isometry. -/
lemma capsule_lower_bound_instantiation : CapsuleLowerBound := by
  intro L r hL hr p u hu
  let e0 : Point3 := EuclideanSpace.single 0 1
  let scale : Point3 → Point3 := fun x => L • x

  -- Step 1: Construct orthonormal basis b with b 0 = u
  let b0 := EuclideanSpace.basisFun (Fin 3) ℝ
  have h_b0_0 : b0 0 = e0 := by
    simp [b0, EuclideanSpace.basisFun, e0] <;> rfl
  let v : Fin 3 → Point3 := fun i => if i = 0 then u else 0
  have h_v_0 : v 0 = u := by simp [v]
  let s0 : Set (Fin 3) := {0}
  let z0 : s0 := ⟨0, by simp [s0]⟩
  have h_orth : Orthonormal ℝ (s0.restrict v) := by
    rw [orthonormal_subsingleton_iff]
    intro i
    have h_i0 : i = z0 := Subsingleton.elim i z0
    have h_goal : ‖(s0.restrict v) i‖ = 1 := by
      have h_val : (s0.restrict v) i = u := by
        have h1 : (i : Fin 3) = 0 := by
          exact congr_arg (fun (x : s0) => (x : Fin 3)) h_i0
        simp [Set.restrict, h_v_0, h1]
      rw [h_val]
      exact hu
    exact h_goal
  have h_finrank : Module.finrank ℝ Point3 = Fintype.card (Fin 3) := by simp
  rcases Orthonormal.exists_orthonormalBasis_extension_of_card_eq h_finrank (s := s0) h_orth with ⟨b, hb⟩
  have hb_0 : b 0 = u := by
    have h : b 0 = (s0.restrict v) z0 := hb 0 (by simp [s0])
    have h2 : (s0.restrict v) z0 = u := by
      simp [Set.restrict, h_v_0] <;> rfl
    rw [h, h2]

  -- Step 2: Linear isometry e mapping e0 to u
  let e : Point3 ≃ₗᵢ[ℝ] Point3 :=
    OrthonormalBasis.equiv b0 b (Equiv.refl (Fin 3))
  have h_e_basis : ∀ i, e (b0 i) = b i := by intro i; exact PiLp.ext (congrFun rfl)
  have h_e_0 : e e0 = u := by
    have h := h_e_basis 0
    rw [h_b0_0] at h
    rw [h, hb_0]

  -- Step 3: e maps unitSegment0e0 to unitSegment 0 u
  have h_seg_eq : e '' unitSegment0e0 = unitSegment 0 u := by
    have h1 : ∀ (t : ℝ), e (0 + t • e0) = 0 + t • u := by
      intro t
      have h2 : e (0 + t • e0) = e (t • e0) := by abel
      rw [h2]
      have h3 : e (t • e0) = t • e e0 := e.map_smul t e0
      rw [h3, h_e_0] <;> abel
    calc e '' unitSegment0e0
      = e '' ((fun t : ℝ => 0 + t • e0) '' Set.Icc (0 : ℝ) 1) := by rfl
    _ = (fun t : ℝ => e (0 + t • e0)) '' Set.Icc (0 : ℝ) 1 := by rw [Set.image_image]
    _ = (fun t : ℝ => 0 + t • u) '' Set.Icc (0 : ℝ) 1 := by
      apply Set.image_congr
      intro t _
      exact h1 t
    _ = unitSegment 0 u := by rfl

  -- Step 4: Isometry preserves cthickening
  have h_comm : ∀ (r' : ℝ) (s' : Set Point3), e '' (cthickening r' s') = cthickening r' (e '' s') := by
    intro r' s'
    ext z
    simp only [Set.mem_image, Metric.mem_cthickening_iff]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have h_inf : infEDist (e x) (e '' s') = infEDist x s' :=
        Metric.infEDist_image (hΦ := e.isometry)
      rw [h_inf]; exact hx
    · intro hz
      refine ⟨e.symm z, ?_, e.apply_symm_apply z⟩
      have h_inf : infEDist (e (e.symm z)) (e '' s') = infEDist (e.symm z) s' :=
        Metric.infEDist_image (hΦ := e.isometry)
      have h3 : e (e.symm z) = z := e.apply_symm_apply z
      rw [h3] at h_inf
      rw [h_inf] at hz
      exact hz

  have h_e_thick : e '' (capsule (r / L)) = cthickening (r / L) (unitSegment 0 u) := by
    have h_capsule_def : capsule (r / L) = cthickening (r / L) unitSegment0e0 := by rfl
    have h : e '' (capsule (r / L)) = e '' (cthickening (r / L) unitSegment0e0) := by
      congr
    rw [h, h_comm (r / L) unitSegment0e0, h_seg_eq]

  -- Step 5: Volume equality
  have h_vol_eq : volume (cthickening (r / L) (unitSegment 0 u)) = volume (capsule (r / L)) := by
    have h_closed : IsClosed (capsule (r / L)) := Metric.isClosed_cthickening
    have h_meas : MeasurableSet (capsule (r / L)) := h_closed.measurableSet
    have h_eq : e '' (capsule (r / L)) = e.symm ⁻¹' (capsule (r / L)) := by
      ext z
      simp only [Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨x, hx, rfl⟩
        simpa using hx
      · intro hz
        refine ⟨e.symm z, hz, e.apply_symm_apply z⟩
    have h_map : Measure.map e.symm volume = volume := e.symm.measurePreserving.map_eq
    have h : volume (e '' (capsule (r / L))) = volume (capsule (r / L)) := by
      rw [h_eq]
      have h2 : Measure.map e.symm volume (capsule (r / L)) = volume (e.symm ⁻¹' (capsule (r / L))) :=
        Measure.map_apply e.symm.continuous.measurable h_meas
      rw [←h2, h_map]
    rw [←h_e_thick]
    exact h

  -- Step 6: Segment of length L = p +ᵥ (scale '' unitSegment 0 u)
  let seg_1 : Set Point3 := unitSegment 0 u
  let seg_L : Set Point3 := (fun t : ℝ => p + t • u) '' Set.Icc 0 L

  have h_seg_L_eq : seg_L = (fun x : Point3 => p + x) '' (scale '' seg_1) := by
    ext x
    simp only [seg_L, seg_1, Set.mem_image, scale]
    constructor
    · rintro ⟨t, ht, rfl⟩
      have ht1 : 0 ≤ t := ht.1
      have ht2 : t ≤ L := ht.2
      have h_t1 : 0 ≤ t / L := by
        exact div_nonneg ht1 (by linarith)
      have h_t2 : t / L ≤ 1 := by
        rw [div_le_one (by linarith)]
        exact ht2
      let z : Point3 := L • ((t / L) • u)
      have hz1 : z ∈ scale '' seg_1 := by
        refine ⟨(t / L) • u, ?_, rfl⟩
        exact ⟨t / L, ⟨h_t1, h_t2⟩, by abel⟩
      have hz2 : p + z = p + t • u := by
        simp [z, smul_smul] <;> field_simp [hL.ne'] <;> ring
      exact ⟨z, hz1, hz2⟩
    · rintro ⟨z, hz, rfl⟩
      rcases hz with ⟨y, hy, rfl⟩
      rcases hy with ⟨s, ⟨hs1, hs2⟩, rfl⟩
      let t : ℝ := L * s
      have ht1 : 0 ≤ t := by positivity
      have ht2 : t ≤ L := by
        calc t = L * s := by rfl
          _ ≤ L * 1 := by gcongr
          _ = L := by ring
      exact ⟨t, ⟨ht1, ht2⟩, by simp [t, smul_smul] <;> ring⟩

  -- Step 7: Translation and cthickening commute
  have h_dist_transl : ∀ (x y : Point3), dist (p + x) (p + y) = dist x y := by
    intro x y
    have h2 : (p + x) - (p + y) = x - y := by abel
    have h1 : dist (p + x) (p + y) = ‖(p + x) - (p + y)‖ := by
      rw [dist_eq_norm]
    have h3 : dist x y = ‖x - y‖ := by rw [dist_eq_norm]
    rw [h1, h3, h2]
  have h_edist_transl : ∀ (x y : Point3), edist (p + x) (p + y) = edist x y := by
    intro x y
    rw [edist_dist, edist_dist, h_dist_transl]
  have transl_iso : Isometry (fun x : Point3 => p + x) := h_edist_transl
  have h_transl_inf : ∀ (s' : Set Point3) (z : Point3),
      infEDist z ((fun x : Point3 => p + x) '' s') = infEDist (z - p) s' := by
    intro s' z
    have h : infEDist (p + (z - p)) ((fun x : Point3 => p + x) '' s') = infEDist (z - p) s' := by
      rw [Metric.infEDist_image (hΦ := transl_iso) (x := z - p) (t := s')]
      <;> rfl
    have h2 : p + (z - p) = z := by abel
    rw [h2] at h
    exact h
  have h_vadd_cthick : ∀ (r' : ℝ) (s' : Set Point3),
      cthickening r' ((fun x : Point3 => p + x) '' s') =
      (fun x : Point3 => p + x) '' cthickening r' s' := by
    intro r' s'
    ext z
    simp only [Set.mem_image, Metric.mem_cthickening_iff]
    constructor
    · intro hz
      refine ⟨z - p, ?_, ?_⟩
      · rw [h_transl_inf s' z] at hz
        exact hz
      · simp [sub_add_cancel]
    · rintro ⟨y, hy, rfl⟩
      rw [h_transl_inf s' (p + y)]
      <;> simpa using hy

  have h_transl_thick : cthickening r seg_L =
      (fun x : Point3 => p + x) '' cthickening r (scale '' seg_1) := by
    rw [h_seg_L_eq, h_vadd_cthick r (scale '' seg_1)]

  -- Step 8: Volume is translation-invariant
  have h_vol_transl : volume (cthickening r seg_L) = volume (cthickening r (scale '' seg_1)) := by
    rw [h_transl_thick]
    let s : Set Point3 := cthickening r (scale '' seg_1)
    have h_meas : MeasurableSet s := Metric.isClosed_cthickening.measurableSet
    let f : Point3 ≃ᵐ Point3 :=
      { toFun := fun x : Point3 => p + x
        invFun := fun x : Point3 => x - p
        left_inv := by intro x; simp [sub_add_cancel]
        right_inv := by intro x; simp [add_sub_cancel]
        measurable_toFun := (continuous_const.add continuous_id).measurable
        measurable_invFun := (continuous_id.sub continuous_const).measurable }
    have h_mp : MeasurePreserving f volume volume :=
      MeasureTheory.measurePreserving_add_left volume p
    have h_inj : Function.Injective f := f.injective
    have h4 : f ⁻¹' (f '' s) = s := by
      ext x; simp [Set.mem_preimage, Set.mem_image, h_inj] <;> tauto
    have h5 : volume (f ⁻¹' (f '' s)) = volume (f '' s) := h_mp.measure_preimage_equiv (f '' s)
    rw [h4] at h5
    exact h5.symm

  -- Step 9: Scaling of cthickening
  have h_thick_scale : cthickening r (scale '' seg_1) = scale '' cthickening (r / L) seg_1 :=
    cthickening_smul_point3 hL

  -- Step 10: Volume scaling
  have h_vol_scale : volume (scale '' cthickening (r / L) seg_1) =
      ENNReal.ofReal (L ^ 3) * volume (cthickening (r / L) seg_1) :=
    volume_smul3 hL

  -- Step 11: Combine
  calc volume (cthickening r seg_L)
    = volume (cthickening r (scale '' seg_1)) := h_vol_transl
  _ = volume (scale '' cthickening (r / L) seg_1) := by rw [h_thick_scale]
  _ = ENNReal.ofReal (L ^ 3) * volume (cthickening (r / L) seg_1) := h_vol_scale
  _ = ENNReal.ofReal (L ^ 3) * volume (capsule (r / L)) := by rw [h_vol_eq]
  _ ≥ ENNReal.ofReal (L ^ 3) * ENNReal.ofReal (Real.pi * (r / L) ^ 2 + (4 / 3 : ℝ) * Real.pi * (r / L) ^ 3) := by
      gcongr
      exact capsule_volume_lower (r / L) (by positivity)
  _ = ENNReal.ofReal (Real.pi * r ^ 2 * L + (4 / 3 : ℝ) * Real.pi * r ^ 3) := by
      have h_pos1 : 0 ≤ L ^ 3 := by positivity
      have h_pos2 : 0 ≤ Real.pi * (r / L) ^ 2 + (4 / 3 : ℝ) * Real.pi * (r / L) ^ 3 := by positivity
      rw [←ENNReal.ofReal_mul h_pos1]
      <;> congr 1 <;> ring_nf <;> field_simp [hL.ne'] <;> ring

end Kakeya.Streamlined.GeometricLemmas
