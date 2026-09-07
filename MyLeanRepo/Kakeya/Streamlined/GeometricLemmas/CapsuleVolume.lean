import MyLeanRepo.Kakeya.Streamlined.Geometry
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Capsule volume bounds

A capsule is the closed `r`-thickening of a unit line segment in `Point3`.

We prove:
- `capsule_volume_lower`: volume ≥ πr² + (4/3)πr³
- `capsule_volume_upper`: volume ≤ πr² + (8/3)πr³

## Key lemmas

- `cylinder_volume_aligned`: volume of axis-aligned cylinder = πr²
-/

noncomputable section

open MeasureTheory Metric Set

namespace Kakeya.Streamlined.GeometricLemmas

/-- The unit segment from 0 to e0. -/
def unitSegment0e0 : Set Point3 :=
  unitSegment 0 (EuclideanSpace.single 0 1)

/-- The capsule: closed r-thickening of the unit segment. -/
def capsule (r : ℝ) : Set Point3 :=
  Metric.cthickening r unitSegment0e0

/-- Cylinder region: 0 ≤ x0 ≤ 1 and x1²+x2² ≤ r². -/
def cylRegion (r : ℝ) : Set Point3 :=
  {x | 0 ≤ x 0 ∧ x 0 ≤ 1 ∧ (x 1) ^ 2 + (x 2) ^ 2 ≤ r ^ 2}

/-- Left half-ball region: x0 ≤ 0 and ‖x‖ ≤ r. -/
def leftHalfBall (r : ℝ) : Set Point3 :=
  {x | x 0 ≤ 0 ∧ ‖x‖ ≤ r}

/-- Right half-ball region: x0 ≥ 1 and ‖x - e0‖ ≤ r. -/
def rightHalfBall (r : ℝ) : Set Point3 :=
  {x | x 0 ≥ 1 ∧ ‖x - (EuclideanSpace.single 0 1)‖ ≤ r}

/-! ### Disk volume in Fin 2 → ℝ -/

/-- Volume of a disk in `Fin 2 → ℝ` is πr². -/
lemma disk_volume_fin2 (r : ℝ) (hr : 0 ≤ r) :
    MeasureTheory.volume {y : Fin 2 → ℝ | y 0 ^ 2 + y 1 ^ 2 ≤ r ^ 2} =
    ENNReal.ofReal (Real.pi * r ^ 2) := by
  let toLp2 : (Fin 2 → ℝ) → EuclideanSpace ℝ (Fin 2) := WithLp.toLp 2
  have h_mp2 : MeasurePreserving toLp2 volume volume :=
    PiLp.volume_preserving_toLp (ι := Fin 2)
  have h_inj2 : Function.Injective toLp2 :=
    fun a b h => by simpa [toLp2, WithLp.toLp_injective] using h
  let D2 : Set (EuclideanSpace ℝ (Fin 2)) := Metric.closedBall 0 r
  let S2 : Set (Fin 2 → ℝ) := {y | y 0 ^ 2 + y 1 ^ 2 ≤ r ^ 2}
  have h_cont : Continuous (fun y : Fin 2 → ℝ => y 0 ^ 2 + y 1 ^ 2) := by continuity
  have hS2_meas : MeasurableSet S2 :=
    (isClosed_Iic.preimage h_cont).measurableSet
  have h_norm_eq : ∀ (y : Fin 2 → ℝ), ‖toLp2 y‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 := by
    intro y
    have h1 : ‖toLp2 y‖ = Real.sqrt (∑ i : Fin 2, ‖y i‖ ^ 2) := by
      rw [EuclideanSpace.norm_eq] <;> rfl
    rw [h1]
    have h2 : 0 ≤ ∑ i : Fin 2, ‖y i‖ ^ 2 := by positivity
    rw [Real.sq_sqrt h2]
    have h3 : (∑ i : Fin 2, ‖y i‖ ^ 2) = y 0 ^ 2 + y 1 ^ 2 := by
      simp [Fin.sum_univ_succ] <;> ring
    rw [h3]
  have h_iff : ∀ (y : Fin 2 → ℝ), ‖toLp2 y‖ ≤ r ↔ y 0 ^ 2 + y 1 ^ 2 ≤ r ^ 2 := by
    intro y
    have h4 : 0 ≤ r := hr
    have h5 : 0 ≤ ‖toLp2 y‖ := by positivity
    constructor
    · intro h; have h6 : ‖toLp2 y‖ ^ 2 ≤ r ^ 2 := by nlinarith
      rw [h_norm_eq y] at h6; exact h6
    · intro h; have h6 : ‖toLp2 y‖ ^ 2 ≤ r ^ 2 := by
        rw [h_norm_eq y]; exact h
      nlinarith
  have h_image : toLp2 '' S2 = D2 := by
    ext z
    simp only [D2, S2, Set.mem_image, Metric.mem_closedBall]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have h_dist : dist (toLp2 y) 0 = ‖toLp2 y‖ := by simp [dist_zero_right]
      rw [h_dist]; exact (h_iff y).mpr hy
    · intro hz
      have h_dist : ‖z‖ ≤ r := by simpa [dist_zero_right] using hz
      refine ⟨z.ofLp, (h_iff z.ofLp).mp ?_, WithLp.toLp_ofLp (2 : ENNReal) z⟩
      have h6 : toLp2 z.ofLp = z := WithLp.toLp_ofLp (2 : ENNReal) z
      rw [h6]; exact h_dist
  have h_img_meas : MeasurableSet (toLp2 '' S2) := by
    rw [h_image]; exact isClosed_closedBall.measurableSet
  have h_pre : volume (toLp2 ⁻¹' (toLp2 '' S2)) = volume (toLp2 '' S2) :=
    h_mp2.measure_preimage ⟨toLp2 '' S2, h_img_meas, by simp⟩
  have h_eq : toLp2 ⁻¹' (toLp2 '' S2) = S2 := by
    ext x; simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · rintro ⟨y, hy, hxy⟩; have h_x_eq_y : x = y := h_inj2 hxy.symm; rw [h_x_eq_y]; exact hy
    · intro hx; exact ⟨x, hx, rfl⟩
  have h_vol : volume S2 = volume (toLp2 '' S2) := by
    have h : volume (toLp2 ⁻¹' (toLp2 '' S2)) = volume S2 := by rw [h_eq]
    exact h.symm.trans h_pre
  rw [h_vol, h_image]
  rw [EuclideanSpace.volume_closedBall_fin_two (0 : EuclideanSpace ℝ (Fin 2)) r]
  have h1 : ENNReal.ofReal r ^ 2 = ENNReal.ofReal (r ^ 2) := by
    simp [pow_two, ENNReal.ofReal_mul hr] <;> ring
  have h_final : ENNReal.ofReal r ^ 2 * ENNReal.ofReal Real.pi =
      ENNReal.ofReal (Real.pi * r ^ 2) := by
    rw [h1]
    rw [←ENNReal.ofReal_mul (by positivity)] <;> ring
  exact h_final

/-! ### Cylinder volume via Fubini -/

/-- Volume of axis-aligned cylinder (length 1, radius r) is πr². -/
theorem cylinder_volume_aligned (r : ℝ) (hr : 0 < r) :
    volume (cylRegion r) = ENNReal.ofReal (Real.pi * r ^ 2) := by
  let toLp3 : (Fin 3 → ℝ) → Point3 := WithLp.toLp 2
  have h_mp3 : MeasurePreserving toLp3 volume volume :=
    PiLp.volume_preserving_toLp (ι := Fin 3)
  have h_inj3 : Function.Injective toLp3 :=
    fun a b h => by simpa [toLp3, WithLp.toLp_injective] using h
  let S_raw : Set (Fin 3 → ℝ) :=
    {x | 0 ≤ x 0 ∧ x 0 ≤ 1 ∧ (x 1) ^ 2 + (x 2) ^ 2 ≤ r ^ 2}
  have h_cont0 : Continuous (fun x : Fin 3 → ℝ => x 0) := by fun_prop
  have h_cont12 : Continuous (fun x : Fin 3 → ℝ => (x 1) ^ 2 + (x 2) ^ 2) := by fun_prop
  have hS_raw_meas : MeasurableSet S_raw :=
    ((isClosed_Ici.preimage h_cont0).inter
      ((isClosed_Iic.preimage h_cont0).inter (isClosed_Iic.preimage h_cont12))).measurableSet
  have h_image : toLp3 '' S_raw = cylRegion r := by
    ext z
    simp only [cylRegion, S_raw, Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have h_coord : ∀ i : Fin 3, (toLp3 x) i = x i := by
        intro i; simp [toLp3]
      exact ⟨by rw [h_coord 0]; exact hx.1,
        by rw [h_coord 0]; exact hx.2.1,
        by rw [h_coord 1, h_coord 2]; exact hx.2.2⟩
    · intro hz
      refine ⟨z.ofLp, ?_, WithLp.toLp_ofLp (2 : ENNReal) z⟩
      have h_coord : ∀ i : Fin 3, z.ofLp i = z i := by
        intro i; simp [WithLp.ofLp_toLp]
      simpa [h_coord] using hz
  have h_cyl_meas : MeasurableSet (cylRegion r) := by
    have hc0 : Continuous (fun x : Point3 => x 0) := by fun_prop
    have hc12 : Continuous (fun x : Point3 => (x 1) ^ 2 + (x 2) ^ 2) := by fun_prop
    exact ((isClosed_Ici.preimage hc0).inter
      ((isClosed_Iic.preimage hc0).inter (isClosed_Iic.preimage hc12))).measurableSet
  have h_img_meas3 : MeasurableSet (toLp3 '' S_raw) := by
    rw [h_image]; exact h_cyl_meas
  have h_pre3 : volume (toLp3 ⁻¹' (toLp3 '' S_raw)) = volume (toLp3 '' S_raw) :=
    h_mp3.measure_preimage ⟨toLp3 '' S_raw, h_img_meas3, by simp⟩
  have h_eq3 : toLp3 ⁻¹' (toLp3 '' S_raw) = S_raw := by
    ext x; simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · rintro ⟨y, hy, hxy⟩; have h_x_eq_y : x = y := h_inj3 hxy.symm; rw [h_x_eq_y]; exact hy
    · intro hx; exact ⟨x, hx, rfl⟩
  have h_volS : volume (cylRegion r) = volume S_raw := by
    have h : volume (toLp3 ⁻¹' (toLp3 '' S_raw)) = volume S_raw := by rw [h_eq3]
    have h2 : volume S_raw = volume (toLp3 '' S_raw) := h.symm.trans h_pre3
    calc volume (cylRegion r) = volume (toLp3 '' S_raw) := by rw [h_image]
      _ = volume S_raw := h2.symm
  rw [h_volS]
  -- Split Fin 3 → ℝ as ℝ × (Fin 2 → ℝ) using piFinSuccAbove
  let split3 : (Fin 3 → ℝ) ≃ᵐ (ℝ × (Fin 2 → ℝ)) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0
  have h_mp_split : MeasurePreserving split3 volume volume :=
    MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0
  let D : Set (Fin 2 → ℝ) := {y | y 0 ^ 2 + y 1 ^ 2 ≤ r ^ 2}
  let T : Set (ℝ × (Fin 2 → ℝ)) := Set.Icc (0 : ℝ) 1 ×ˢ D
  have h_image2 : split3 '' S_raw = T := by
    ext ⟨t, y⟩
    simp only [T, S_raw, Set.mem_image, Set.mem_prod, Set.mem_Icc, Set.mem_setOf_eq]
    constructor
    · rintro ⟨x, hx, h_eq⟩
      have h_split : split3 x = (x 0, fun i : Fin 2 => x i.succ) := by
        rw [MeasurableEquiv.piFinSuccAbove_apply] <;> rfl
      have h_eq2 : (x 0, fun i : Fin 2 => x i.succ) = (t, y) := by
        rw [←h_split, h_eq]
      rcases Prod.ext_iff.mp h_eq2 with ⟨rfl, h_y⟩
      have h_y' : y = fun i : Fin 2 => x i.succ := h_y.symm
      subst h_y'
      exact ⟨⟨hx.1, hx.2.1⟩, hx.2.2⟩
    · rintro ⟨⟨ht0, ht1⟩, hy⟩
      let x : Fin 3 → ℝ := fun i =>
        match i with
        | 0 => t
        | 1 => y 0
        | 2 => y 1
      have hx1 : 0 ≤ x 0 := ht0
      have hx2 : x 0 ≤ 1 := ht1
      have h_y_in : y 0 ^ 2 + y 1 ^ 2 ≤ r ^ 2 := by simpa [D] using hy
      have hx3 : (x 1) ^ 2 + (x 2) ^ 2 ≤ r ^ 2 := by
        simpa [x] using h_y_in
      have h_apply : split3 x = (t, y) := by
        have h : split3 x = (x 0, fun i : Fin 2 => x i.succ) := by
          rw [MeasurableEquiv.piFinSuccAbove_apply] <;> rfl
        rw [h]
        have h1 : (x 0, fun i : Fin 2 => x i.succ) = (t, y) := by
          apply Prod.ext
          · simp [x]
          · funext i; fin_cases i <;> simp [x] <;> rfl
        exact h1
      exact ⟨x, ⟨hx1, hx2, hx3⟩, h_apply⟩
  have hD_meas : MeasurableSet D := by
    have h_cont : Continuous (fun y : Fin 2 → ℝ => y 0 ^ 2 + y 1 ^ 2) := by continuity
    exact (isClosed_Iic.preimage h_cont).measurableSet
  have hT_meas : MeasurableSet T := measurableSet_Icc.prod hD_meas
  have h_vol2 : volume S_raw = volume (split3 '' S_raw) := by
    have h_img_meas : MeasurableSet (split3 '' S_raw) := by
      rw [h_image2]; exact hT_meas
    have h_pre : volume (split3 ⁻¹' (split3 '' S_raw)) = volume (split3 '' S_raw) :=
      h_mp_split.measure_preimage ⟨split3 '' S_raw, h_img_meas, by simp⟩
    have h_eq : split3 ⁻¹' (split3 '' S_raw) = S_raw := by
      ext z; simp only [Set.mem_preimage, Set.mem_image]
      constructor
      · rintro ⟨y, hy, hxy⟩; have h : z = y := split3.injective hxy.symm; rw [h]; exact hy
      · intro hz; exact ⟨z, hz, rfl⟩
    have h : volume (split3 ⁻¹' (split3 '' S_raw)) = volume S_raw := by rw [h_eq]
    exact h.symm.trans h_pre
  rw [h_vol2, h_image2]
  have h_eq_prod : (volume : Measure (ℝ × (Fin 2 → ℝ))) =
      (volume : Measure ℝ).prod (volume : Measure (Fin 2 → ℝ)) :=
    Measure.volume_eq_prod ℝ (Fin 2 → ℝ)
  rw [h_eq_prod]
  have h_vol_T : (volume.prod volume) T = volume (Set.Icc (0 : ℝ) 1) * volume D :=
    MeasureTheory.Measure.prod_prod (Set.Icc (0 : ℝ) 1) D
  rw [h_vol_T]
  have h_vol_Icc : volume (Set.Icc (0 : ℝ) 1) = ENNReal.ofReal 1 := by
    rw [Real.volume_Icc] <;> norm_num
  rw [h_vol_Icc, disk_volume_fin2 r hr.le]
  have h_pos : 0 ≤ Real.pi * r ^ 2 := by positivity
  rw [←ENNReal.ofReal_mul (by positivity)] <;> ring

/-! ### Hyperplane measure zero -/

/-- Any hyperplane {x : Point3 | x 0 = c} has measure zero. -/
lemma plane_x0_eq_c_volume_zero (c : ℝ) : volume {x : Point3 | x 0 = c} = 0 := by
  let toLp3 : (Fin 3 → ℝ) → Point3 := WithLp.toLp 2
  have h_mp3 : MeasurePreserving toLp3 volume volume := PiLp.volume_preserving_toLp (ι := Fin 3)
  have h_inj3 : Function.Injective toLp3 := fun a b h => by simpa [toLp3, WithLp.toLp_injective] using h
  let S_plane : Set (Fin 3 → ℝ) := {x | x 0 = c}
  have h_image : toLp3 '' S_plane = {x : Point3 | x 0 = c} := by
    ext z
    simp only [S_plane, Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have h_coord : (toLp3 x) 0 = x 0 := by simp [toLp3]
      rw [h_coord]; exact hx
    · intro hz
      refine ⟨z.ofLp, ?_, WithLp.toLp_ofLp (2 : ENNReal) z⟩
      have h_coord : z.ofLp 0 = z 0 := by simp [WithLp.ofLp_toLp]
      rw [h_coord]; exact hz
  have h_img_meas : MeasurableSet (toLp3 '' S_plane) := by
    rw [h_image]
    have hc : Continuous (fun x : Point3 => x 0) := by fun_prop
    exact (isClosed_singleton.preimage hc).measurableSet
  have h_pre : volume (toLp3 ⁻¹' (toLp3 '' S_plane)) = volume (toLp3 '' S_plane) :=
    h_mp3.measure_preimage h_img_meas.nullMeasurableSet
  have h_eq : toLp3 ⁻¹' (toLp3 '' S_plane) = S_plane := by
    ext x; simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · rintro ⟨y, hy, hxy⟩; have h : x = y := h_inj3 hxy.symm; rw [h]; exact hy
    · intro hx; exact ⟨x, hx, rfl⟩
  have h_transfer : volume {x : Point3 | x 0 = c} = volume S_plane := by
    calc volume {x : Point3 | x 0 = c}
      = volume (toLp3 '' S_plane) := by rw [h_image]
    _ = volume (toLp3 ⁻¹' (toLp3 '' S_plane)) := h_pre.symm
    _ = volume S_plane := by rw [h_eq]
  rw [h_transfer]
  let split3 : (Fin 3 → ℝ) ≃ᵐ (ℝ × (Fin 2 → ℝ)) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0
  have h_mp_split : MeasurePreserving split3 volume volume :=
    MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 0
  let T_plane : Set (ℝ × (Fin 2 → ℝ)) := ({c} : Set ℝ) ×ˢ Set.univ
  have h_image2 : split3 '' S_plane = T_plane := by
    ext ⟨t, y⟩
    simp only [S_plane, T_plane, Set.mem_image, Set.mem_prod, Set.mem_singleton_iff, Set.mem_univ, true_and]
    constructor
    · rintro ⟨x, hx, h_eq⟩
      have h_split : split3 x = (x 0, fun i : Fin 2 => x i.succ) := by
        rw [MeasurableEquiv.piFinSuccAbove_apply] <;> rfl
      rw [h_split] at h_eq
      have ht : t = x 0 := (congr_arg Prod.fst h_eq).symm
      have h_tc : t = c := by
        rw [ht]
        simpa [S_plane] using hx
      exact ⟨h_tc, trivial⟩
    · intro ht
      let x : Fin 3 → ℝ := fun i => Fin.cases t y i
      have hx : x 0 = t := by simp [x, Fin.cases] <;> rfl
      have h_apply : split3 x = (t, y) := by
        rw [MeasurableEquiv.piFinSuccAbove_apply]
        apply Prod.ext
        · exact hx
        · funext j; fin_cases j <;> simp [x, Fin.cases] <;> rfl
      have h_tc : t = c := ht.1
      have h_x_in : x ∈ S_plane := by
        simpa [S_plane] using Eq.trans hx h_tc
      exact ⟨x, h_x_in, h_apply⟩
  have h_img_meas2 : MeasurableSet (split3 '' S_plane) := by
    rw [h_image2]; exact (measurableSet_singleton c).prod MeasurableSet.univ
  have h_pre2 : volume (split3 ⁻¹' (split3 '' S_plane)) = volume (split3 '' S_plane) :=
    h_mp_split.measure_preimage h_img_meas2.nullMeasurableSet
  have h_eq2 : split3 ⁻¹' (split3 '' S_plane) = S_plane := by
    ext z; simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · rintro ⟨y, hy, hxy⟩; have h : z = y := split3.injective hxy.symm; rw [h]; exact hy
    · intro hz; exact ⟨z, hz, rfl⟩
  have h_vol2 : volume S_plane = volume (split3 '' S_plane) := by
    rw [h_eq2] at h_pre2; exact h_pre2
  rw [h_vol2, h_image2]
  have h_eq_prod : (volume : Measure (ℝ × (Fin 2 → ℝ))) = volume.prod volume :=
    Measure.volume_eq_prod ℝ (Fin 2 → ℝ)
  rw [h_eq_prod, Measure.prod_prod ({c} : Set ℝ) (Set.univ : Set (Fin 2 → ℝ))]
  have h_singleton : volume ({c} : Set ℝ) = 0 := by simp
  rw [h_singleton] <;> simp

/-! ### Half-ball volumes via reflection symmetry -/

/-- Volume of left half-ball is (2/3)πr³. -/
theorem leftHalfBall_volume (r : ℝ) (hr : 0 < r) :
    volume (leftHalfBall r) = ENNReal.ofReal ((2 / 3 : ℝ) * Real.pi * r ^ 3) := by
  let neg_lin : Point3 ≃ₗᵢ[ℝ] Point3 :=
    { toFun := fun x => -x
      invFun := fun x => -x
      left_inv := by intro x; simp
      right_inv := by intro x; simp
      map_add' := by intro x y; simp [add_comm]
      map_smul' := by intro c x; simp
      norm_map' := by intro x; exact norm_neg x }
  have h_neg_mp : MeasurePreserving neg_lin volume volume := neg_lin.measurePreserving
  let R_half : Set Point3 := {x | x 0 ≥ 0 ∧ ‖x‖ ≤ r}
  have h_image : neg_lin '' (leftHalfBall r) = R_half := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxa : x 0 ≤ 0 := hx.1
      have hxb : ‖x‖ ≤ r := hx.2
      have h1 : (neg_lin x) 0 ≥ 0 := by simp [neg_lin] <;> linarith
      have h2 : ‖neg_lin x‖ ≤ r := by
        have h3 : ‖neg_lin x‖ = ‖x‖ := neg_lin.norm_map x
        rw [h3]; exact hxb
      exact ⟨h1, h2⟩
    · intro hz
      have hza : z 0 ≥ 0 := hz.1
      have hzb : ‖z‖ ≤ r := hz.2
      refine ⟨-z, ?_, by simp [neg_lin]⟩
      have h1 : (-z : Point3) 0 ≤ 0 := by simp <;> linarith
      have h2 : ‖(-z : Point3)‖ ≤ r := by simpa [norm_neg] using hzb
      exact ⟨h1, h2⟩
  have hc0 : Continuous (fun x : Point3 => x 0) := by fun_prop
  have h_L_meas : MeasurableSet (leftHalfBall r) := by
    have h1 : IsClosed {x : Point3 | x 0 ≤ 0} := isClosed_Iic.preimage hc0
    have h2 : IsClosed (Metric.closedBall (0 : Point3) r) := isClosed_closedBall
    have h3 : leftHalfBall r = {x | x 0 ≤ 0} ∩ Metric.closedBall (0 : Point3) r := by
      ext y; simp [leftHalfBall, Metric.mem_closedBall, dist_zero_right] <;> rfl
    rw [h3]; exact (h1.inter h2).measurableSet
  have h_R_meas : MeasurableSet R_half := by
    have h1 : IsClosed {x : Point3 | x 0 ≥ 0} := isClosed_Ici.preimage hc0
    have h2 : IsClosed (Metric.closedBall (0 : Point3) r) := isClosed_closedBall
    have h3 : R_half = {x | x 0 ≥ 0} ∩ Metric.closedBall (0 : Point3) r := by
      ext y; simp [R_half, Metric.mem_closedBall, dist_zero_right] <;> rfl
    rw [h3]; exact (h1.inter h2).measurableSet
  have h_vol_eq : volume (leftHalfBall r) = volume R_half := by
    have h_img_meas : MeasurableSet (neg_lin '' (leftHalfBall r)) := by
      rw [h_image]; exact h_R_meas
    have h_pre : volume (neg_lin ⁻¹' (neg_lin '' (leftHalfBall r))) = volume (neg_lin '' (leftHalfBall r)) :=
      h_neg_mp.measure_preimage h_img_meas.nullMeasurableSet
    have h_eq : neg_lin ⁻¹' (neg_lin '' (leftHalfBall r)) = leftHalfBall r := by
      ext z; simp only [Set.mem_preimage, Set.mem_image]
      constructor
      · rintro ⟨y, hy, hzy⟩; have h : z = y := neg_lin.injective hzy.symm; rw [h]; exact hy
      · intro hz; exact ⟨z, hz, rfl⟩
    rw [h_eq] at h_pre
    rw [h_image] at h_pre
    exact h_pre
  have h_union : leftHalfBall r ∪ R_half = Metric.closedBall (0 : Point3) r := by
    ext x
    simp only [leftHalfBall, R_half, Set.mem_union, Set.mem_setOf_eq, Metric.mem_closedBall, dist_zero_right]
    constructor
    · rintro (h | h) <;> exact h.2
    · intro h
      by_cases h0 : x 0 ≤ 0
      · exact Or.inl ⟨h0, h⟩
      · exact Or.inr ⟨by linarith, h⟩
  have h_inter_vol : volume (leftHalfBall r ∩ R_half) = 0 := by
    have h_sub : leftHalfBall r ∩ R_half ⊆ {x : Point3 | x 0 = 0} := by
      intro x hx
      have h1 : x 0 ≤ 0 := hx.1.1
      have h2 : x 0 ≥ 0 := hx.2.1
      have h3 : x 0 = 0 := by linarith
      simpa using h3
    have h4 : volume (leftHalfBall r ∩ R_half) ≤ volume {x : Point3 | x 0 = 0} := measure_mono h_sub
    rw [plane_x0_eq_c_volume_zero 0] at h4
    exact bot_unique h4
  have h_sum : volume (leftHalfBall r ∪ R_half) = volume (leftHalfBall r) + volume R_half := by
    have h_eq : volume (leftHalfBall r ∪ R_half) + volume (leftHalfBall r ∩ R_half) =
        volume (leftHalfBall r) + volume R_half := measure_union_add_inter (leftHalfBall r) h_R_meas
    rw [h_inter_vol] at h_eq; simpa using h_eq
  have h_ball : volume (Metric.closedBall (0 : Point3) r) =
      ENNReal.ofReal ((4 / 3 : ℝ) * Real.pi * r ^ 3) := by
    rw [EuclideanSpace.volume_closedBall_fin_three (0 : Point3) r]
    have h_pos : 0 ≤ r := by linarith
    have h2 : ENNReal.ofReal r ^ 3 = ENNReal.ofReal (r ^ 3) := (ENNReal.ofReal_pow h_pos 3).symm
    rw [h2]
    have h3 : 0 ≤ r ^ 3 := by positivity
    rw [←ENNReal.ofReal_mul h3]
    <;> congr 1 <;> ring
  rw [h_union] at h_sum
  rw [h_ball] at h_sum
  rw [←h_vol_eq] at h_sum
  have h_final2 : 2 * volume (leftHalfBall r) =
      ENNReal.ofReal ((4 / 3 : ℝ) * Real.pi * r ^ 3) := by
    have h_sum' : ENNReal.ofReal ((4 / 3 : ℝ) * Real.pi * r ^ 3) =
        volume (leftHalfBall r) + volume (leftHalfBall r) := h_sum
    have h : volume (leftHalfBall r) + volume (leftHalfBall r) = 2 * volume (leftHalfBall r) := by
      calc volume (leftHalfBall r) + volume (leftHalfBall r)
        = 1 * volume (leftHalfBall r) + 1 * volume (leftHalfBall r) := by simp
      _ = (1 + 1) * volume (leftHalfBall r) := by rw [add_mul]
      _ = 2 * volume (leftHalfBall r) := by norm_num
    rw [h] at h_sum'
    exact h_sum'.symm
  have h_pos2 : 0 ≤ (2 / 3 : ℝ) * Real.pi * r ^ 3 := by positivity
  have h_eq3 : (4 / 3 : ℝ) * Real.pi * r ^ 3 = 2 * ((2 / 3 : ℝ) * Real.pi * r ^ 3) := by ring
  have h4 : ENNReal.ofReal ((4 / 3 : ℝ) * Real.pi * r ^ 3) =
      2 * ENNReal.ofReal ((2 / 3 : ℝ) * Real.pi * r ^ 3) := by
    rw [h_eq3]
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    <;> norm_num
  have h5 : 2 * volume (leftHalfBall r) = 2 * ENNReal.ofReal ((2 / 3 : ℝ) * Real.pi * r ^ 3) := by
    rw [h_final2, h4]
  have h6 : volume (leftHalfBall r) = ENNReal.ofReal ((2 / 3 : ℝ) * Real.pi * r ^ 3) :=
    (ENNReal.mul_right_inj (show (2 : ENNReal) ≠ 0 from by norm_num)
      (show (2 : ENNReal) ≠ ⊤ from by norm_num)).mp h5
  exact h6

/-- Volume of right half-ball is (2/3)πr³. -/
theorem rightHalfBall_volume (r : ℝ) (hr : 0 < r) :
    volume (rightHalfBall r) = ENNReal.ofReal ((2 / 3 : ℝ) * Real.pi * r ^ 3) := by
  let e0 : Point3 := EuclideanSpace.single 0 1
  let neg_lin : Point3 ≃ₗᵢ[ℝ] Point3 :=
    { toFun := fun x => -x
      invFun := fun x => -x
      left_inv := by intro x; simp
      right_inv := by intro x; simp
      map_add' := by intro x y; simp [add_comm]
      map_smul' := by intro c x; simp
      norm_map' := by intro x; exact norm_neg x }
  have h_neg_mp : MeasurePreserving neg_lin volume volume := neg_lin.measurePreserving
  have h_trans_mp : MeasurePreserving (fun x : Point3 => x + e0) volume volume :=
    MeasureTheory.measurePreserving_add_right volume e0
  let f : Point3 → Point3 := fun x => neg_lin x + e0
  have h_f_mp : MeasurePreserving f volume volume := h_trans_mp.comp h_neg_mp
  have h_f_inj : Function.Injective f := by
    intro a b h
    have h' : neg_lin a + e0 = neg_lin b + e0 := h
    have h'' : neg_lin a = neg_lin b := add_right_cancel h'
    exact neg_lin.injective h''
  have h_image : f '' (leftHalfBall r) = rightHalfBall r := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxa : x 0 ≤ 0 := hx.1
      have hxb : ‖x‖ ≤ r := hx.2
      have h1 : (neg_lin x + e0) 0 = 1 - x 0 := by
        simp [neg_lin, e0, EuclideanSpace.single] <;> ring
      have h2 : ‖(neg_lin x + e0) - e0‖ = ‖x‖ := by
        simp [neg_lin] <;> rw [norm_neg]
      exact ⟨by rw [h1] <;> linarith, by rw [h2]; exact hxb⟩
    · intro hz
      have hza : z 0 ≥ 1 := hz.1
      have hzb : ‖z - e0‖ ≤ r := hz.2
      refine ⟨e0 - z, ?_, ?_⟩
      · have h1 : (e0 - z) 0 ≤ 0 := by
          simp [e0, EuclideanSpace.single] <;> linarith
        have h2 : ‖e0 - z‖ ≤ r := by
          have h3 : ‖e0 - z‖ = ‖z - e0‖ := by rw [norm_sub_rev]
          rw [h3]; exact hzb
        exact ⟨h1, h2⟩
      · simp [f, neg_lin] <;> abel
  have h_L_meas2 : MeasurableSet (leftHalfBall r) := by
    have hc0 : Continuous (fun x : Point3 => x 0) := by fun_prop
    have h1 : IsClosed {x : Point3 | x 0 ≤ 0} := isClosed_Iic.preimage hc0
    have h2 : IsClosed (Metric.closedBall (0 : Point3) r) := isClosed_closedBall
    have h3 : leftHalfBall r = {x | x 0 ≤ 0} ∩ Metric.closedBall (0 : Point3) r := by
      ext y; simp [leftHalfBall, Metric.mem_closedBall, dist_zero_right] <;> rfl
    rw [h3]; exact (h1.inter h2).measurableSet
  have h_C_meas2 : MeasurableSet (rightHalfBall r) := by
    have hc0 : Continuous (fun x : Point3 => x 0) := by fun_prop
    have h1 : IsClosed {x : Point3 | x 0 ≥ 1} := isClosed_Ici.preimage hc0
    have h2 : IsClosed (Metric.closedBall e0 r) := isClosed_closedBall
    have h3 : rightHalfBall r = {x | x 0 ≥ 1} ∩ Metric.closedBall e0 r := by
      ext y
      simp only [rightHalfBall, Set.mem_inter_iff, Set.mem_setOf_eq, Metric.mem_closedBall]
      <;> rw [dist_eq_norm]
    rw [h3]; exact (h1.inter h2).measurableSet
  have h_vol_eq : volume (rightHalfBall r) = volume (leftHalfBall r) := by
    have h_img_meas : MeasurableSet (f '' (leftHalfBall r)) := by
      rw [h_image]; exact h_C_meas2
    have h_pre : volume (f ⁻¹' (f '' (leftHalfBall r))) = volume (f '' (leftHalfBall r)) :=
      h_f_mp.measure_preimage h_img_meas.nullMeasurableSet
    have h_eq : f ⁻¹' (f '' (leftHalfBall r)) = leftHalfBall r := by
      ext z; simp only [Set.mem_preimage, Set.mem_image]
      constructor
      · rintro ⟨y, hy, hzy⟩; have h : z = y := h_f_inj hzy.symm; rw [h]; exact hy
      · intro hz; exact ⟨z, hz, rfl⟩
    rw [h_eq] at h_pre
    rw [h_image] at h_pre
    exact h_pre.symm
  rw [h_vol_eq]
  exact leftHalfBall_volume r hr

/-! ### Geometric containment lemmas -/

/-- The cylinder, left half-ball, and right half-ball are all contained in the capsule. -/
lemma capsule_contains_parts (r : ℝ) (hr : 0 < r) :
    cylRegion r ⊆ capsule r ∧
    leftHalfBall r ⊆ capsule r ∧
    rightHalfBall r ⊆ capsule r := by
  let e0 : Point3 := EuclideanSpace.single 0 1
  have h_e01 : ∀ (x : Point3), ‖x - (x 0) • e0‖ ^ 2 = (x 1) ^ 2 + (x 2) ^ 2 := by
    intro x
    let z := x - (x 0) • e0
    have hz0 : z 0 = 0 := by simp [z, e0, EuclideanSpace.single] <;> ring
    have hz1 : z 1 = x 1 := by simp [z, e0, EuclideanSpace.single] <;> ring
    have hz2 : z 2 = x 2 := by simp [z, e0, EuclideanSpace.single] <;> ring
    have h_norm : ‖z‖ ^ 2 = (z 0) ^ 2 + (z 1) ^ 2 + (z 2) ^ 2 := by
      have h : ‖z‖ ^ 2 = ∑ i : Fin 3, (z i) ^ 2 := by
        rw [←real_inner_self_eq_norm_sq, PiLp.inner_apply] <;> congr with i <;> simp
      rw [h]
      simp [Fin.sum_univ_succ] <;> ring
    rw [h_norm, hz0, hz1, hz2] <;> ring
  have h_cyl : cylRegion r ⊆ capsule r := by
    intro x hx
    let y : Point3 := (x 0) • e0
    have hy_in : y ∈ unitSegment0e0 := by
      refine ⟨x 0, ⟨hx.1, hx.2.1⟩, ?_⟩
      simp [y, e0, unitSegment0e0, unitSegment] <;> abel
    have h_dist : ‖x - y‖ ≤ r := by
      have h5 : ‖x - y‖ ^ 2 = (x 1) ^ 2 + (x 2) ^ 2 := h_e01 x
      have h6 : (x 1) ^ 2 + (x 2) ^ 2 ≤ r ^ 2 := hx.2.2
      have h7 : ‖x - y‖ ^ 2 ≤ r ^ 2 := by rw [h5]; exact h6
      have h8 : 0 ≤ ‖x - y‖ := by positivity
      nlinarith
    have h9 : infEDist x unitSegment0e0 ≤ edist x y := Metric.infEDist_le_edist_of_mem hy_in
    have h10 : edist x y = ENNReal.ofReal (dist x y) := by simp [edist_dist]
    rw [h10] at h9
    have h11 : dist x y = ‖x - y‖ := by rfl
    rw [h11] at h9
    exact h9.trans (ENNReal.ofReal_le_ofReal h_dist)
  have h_left : leftHalfBall r ⊆ capsule r := by
    intro x hx
    let y : Point3 := 0
    have hy_in : y ∈ unitSegment0e0 := by
      refine ⟨0, by norm_num, ?_⟩
      simp [y, e0, unitSegment0e0, unitSegment] <;> abel
    have h_dist : ‖x - y‖ ≤ r := by simpa [y] using hx.2
    have h9 : infEDist x unitSegment0e0 ≤ edist x y := Metric.infEDist_le_edist_of_mem hy_in
    have h10 : edist x y = ENNReal.ofReal (dist x y) := by simp [edist_dist]
    rw [h10] at h9
    have h11 : dist x y = ‖x - y‖ := by rfl
    rw [h11] at h9
    exact h9.trans (ENNReal.ofReal_le_ofReal h_dist)
  have h_right : rightHalfBall r ⊆ capsule r := by
    intro x hx
    let y : Point3 := e0
    have hy_in : y ∈ unitSegment0e0 := by
      refine ⟨1, by norm_num, ?_⟩
      simp [y, e0, unitSegment0e0, unitSegment] <;> abel
    have h_dist : ‖x - y‖ ≤ r := by simpa [y] using hx.2
    have h9 : infEDist x unitSegment0e0 ≤ edist x y := Metric.infEDist_le_edist_of_mem hy_in
    have h10 : edist x y = ENNReal.ofReal (dist x y) := by simp [edist_dist]
    rw [h10] at h9
    have h11 : dist x y = ‖x - y‖ := by rfl
    rw [h11] at h9
    exact h9.trans (ENNReal.ofReal_le_ofReal h_dist)
  exact ⟨h_cyl, h_left, h_right⟩

/-- The three regions have pairwise intersections of measure zero. -/
lemma capsule_regions_disjoint (r : ℝ) (hr : 0 < r) :
    volume (cylRegion r ∩ leftHalfBall r) = 0 ∧
    volume (cylRegion r ∩ rightHalfBall r) = 0 ∧
    volume (leftHalfBall r ∩ rightHalfBall r) = 0 := by
  have h1 : cylRegion r ∩ leftHalfBall r ⊆ {x : Point3 | x 0 = 0} := by
    intro x hx
    have hxa : 0 ≤ x 0 := hx.1.1
    have hxb : x 0 ≤ 0 := hx.2.1
    have hxc : x 0 = 0 := by linarith
    simpa using hxc
  have h2 : volume (cylRegion r ∩ leftHalfBall r) = 0 := by
    have h3 : volume (cylRegion r ∩ leftHalfBall r) ≤ volume {x : Point3 | x 0 = 0} := measure_mono h1
    rw [plane_x0_eq_c_volume_zero 0] at h3
    exact bot_unique h3
  have h4 : cylRegion r ∩ rightHalfBall r ⊆ {x : Point3 | x 0 = 1} := by
    intro x hx
    have hxa : x 0 ≤ 1 := hx.1.2.1
    have hxb : x 0 ≥ 1 := hx.2.1
    have hxc : x 0 = 1 := by linarith
    simpa using hxc
  have h5 : volume (cylRegion r ∩ rightHalfBall r) = 0 := by
    have h6 : volume (cylRegion r ∩ rightHalfBall r) ≤ volume {x : Point3 | x 0 = 1} := measure_mono h4
    rw [plane_x0_eq_c_volume_zero 1] at h6
    exact bot_unique h6
  have h7 : leftHalfBall r ∩ rightHalfBall r = (∅ : Set Point3) := by
    ext x
    simp only [leftHalfBall, rightHalfBall, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false]
    constructor
    · intro h; linarith [h.1.1, h.2.1]
    · intro h; exfalso; exact h
  have h8 : volume (leftHalfBall r ∩ rightHalfBall r) = 0 := by
    rw [h7] <;> simp
  exact ⟨h2, h5, h8⟩

/-- The capsule is contained in cylinder ∪ ball(0,r) ∪ ball(e0,r). -/
lemma capsule_subset_union (r : ℝ) (hr : 0 < r) :
    capsule r ⊆ cylRegion r ∪ Metric.closedBall 0 r ∪
      Metric.closedBall (EuclideanSpace.single 0 1) r := by
  let e0 : Point3 := EuclideanSpace.single 0 1
  have h_norm2 : ∀ (x : Point3) (t : ℝ), ‖x - t • e0‖ ^ 2 = (x 0 - t) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2 := by
    intro x t
    let z := x - t • e0
    have hz0 : z 0 = x 0 - t := by simp [z, e0, EuclideanSpace.single] <;> ring
    have hz1 : z 1 = x 1 := by simp [z, e0, EuclideanSpace.single] <;> ring
    have hz2 : z 2 = x 2 := by simp [z, e0, EuclideanSpace.single] <;> ring
    have h_norm : ‖z‖ ^ 2 = (z 0) ^ 2 + (z 1) ^ 2 + (z 2) ^ 2 := by
      have h : ‖z‖ ^ 2 = ∑ i : Fin 3, (z i) ^ 2 := by
        rw [←real_inner_self_eq_norm_sq, PiLp.inner_apply] <;> congr with i <;> simp
      rw [h]
      simp [Fin.sum_univ_succ] <;> ring
    rw [h_norm, hz0, hz1, hz2] <;> ring
  have h_seg_nonempty : unitSegment0e0.Nonempty := by
    refine ⟨0, ?_⟩
    refine ⟨0, by norm_num, ?_⟩
    simp [unitSegment0e0, unitSegment, e0, EuclideanSpace.single]
  have h_seg_form : ∀ z ∈ unitSegment0e0, ∃ (t : ℝ), 0 ≤ t ∧ t ≤ 1 ∧ z = t • e0 := by
    intro z hz
    rcases hz with ⟨t, ht, rfl⟩
    exact ⟨t, ht.1, ht.2, by simp [e0, EuclideanSpace.single] <;> ring⟩
  intro x hx
  have h_infEDist : infEDist x unitSegment0e0 ≤ ENNReal.ofReal r := hx
  have h_infDist_le : infDist x unitSegment0e0 ≤ r := by
    rw [Metric.infDist]
    have h_toReal : (ENNReal.ofReal r).toReal = r := ENNReal.toReal_ofReal (by linarith)
    have h : (infEDist x unitSegment0e0).toReal ≤ (ENNReal.ofReal r).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top h_infEDist
    rw [h_toReal] at h
    exact h
  by_cases h_left : x 0 < 0
  · have h_lower : ∀ z ∈ unitSegment0e0, ‖x‖ ≤ ‖x - z‖ := by
      intro z hz
      rcases h_seg_form z hz with ⟨t, ht0, ht1, rfl⟩
      have h : ‖x - t • e0‖ ^ 2 ≥ ‖x‖ ^ 2 := by
        rw [h_norm2 x t]
        have h4 : ‖x‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2 := by
          have h5 := h_norm2 x 0
          simpa using h5
        rw [h4] <;> nlinarith
      have h5 : 0 ≤ ‖x - t • e0‖ := by positivity
      have h6 : 0 ≤ ‖x‖ := by positivity
      nlinarith
    have h_infDist_ge : ‖x‖ ≤ infDist x unitSegment0e0 := by
      rw [Metric.le_infDist h_seg_nonempty]; exact h_lower
    have h_ball : ‖x‖ ≤ r := by linarith
    have h_ball' : x ∈ Metric.closedBall (0 : Point3) r := by
      simpa [Metric.mem_closedBall, dist_zero_right] using h_ball
    exact Or.inl (Or.inr h_ball')
  · by_cases h_right : 1 < x 0
    · have h_lower : ∀ z ∈ unitSegment0e0, ‖x - e0‖ ≤ ‖x - z‖ := by
        intro z hz
        rcases h_seg_form z hz with ⟨t, ht0, ht1, rfl⟩
        have h : ‖x - t • e0‖ ^ 2 ≥ ‖x - e0‖ ^ 2 := by
          rw [h_norm2 x t]
          have h4 : ‖x - e0‖ ^ 2 = (x 0 - 1) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2 := by
            have h5 := h_norm2 x 1
            simpa [e0, EuclideanSpace.single] using h5
          rw [h4] <;> nlinarith
        have h5 : 0 ≤ ‖x - t • e0‖ := by positivity
        have h6 : 0 ≤ ‖x - e0‖ := by positivity
        nlinarith
      have h_infDist_ge : ‖x - e0‖ ≤ infDist x unitSegment0e0 := by
        rw [Metric.le_infDist h_seg_nonempty]; exact h_lower
      have h_ball : ‖x - e0‖ ≤ r := by linarith
      have h_ball' : x ∈ Metric.closedBall e0 r := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using h_ball
      exact Or.inr h_ball'
    · have h_x0_in : 0 ≤ x 0 ∧ x 0 ≤ 1 := by constructor <;> linarith
      have h_lower : ∀ z ∈ unitSegment0e0, Real.sqrt ((x 1) ^ 2 + (x 2) ^ 2) ≤ ‖x - z‖ := by
        intro z hz
        rcases h_seg_form z hz with ⟨t, ht0, ht1, rfl⟩
        have h2 : (x 1) ^ 2 + (x 2) ^ 2 ≤ ‖x - t • e0‖ ^ 2 := by
          rw [h_norm2 x t] <;> nlinarith
        have h5 : 0 ≤ (x 1) ^ 2 + (x 2) ^ 2 := by positivity
        have h6 : 0 ≤ ‖x - t • e0‖ := by positivity
        exact (Real.sqrt_le_left h6).mpr h2
      have h_infDist_ge : Real.sqrt ((x 1) ^ 2 + (x 2) ^ 2) ≤ infDist x unitSegment0e0 := by
        rw [Metric.le_infDist h_seg_nonempty]; exact h_lower
      have h7 : Real.sqrt ((x 1) ^ 2 + (x 2) ^ 2) ≤ r := by linarith
      have h8 : (x 1) ^ 2 + (x 2) ^ 2 ≤ r ^ 2 := by
        have h9 : 0 ≤ r := by linarith
        nlinarith [Real.sqrt_le_iff.mp h7]
      have h_cyl : x ∈ cylRegion r := by
        simpa [cylRegion] using ⟨h_x0_in.1, h_x0_in.2, h8⟩
      exact Or.inl (Or.inl h_cyl)

/-! ### Main bounds -/

/-- Lower bound: capsule volume ≥ πr² + (4/3)πr³. -/
theorem capsule_volume_lower (r : ℝ) (hr : 0 < r) :
    volume (capsule r) ≥
      ENNReal.ofReal (Real.pi * r ^ 2 + (4 / 3 : ℝ) * Real.pi * r ^ 3) := by
  have h_contain := capsule_contains_parts r hr
  have h_disj := capsule_regions_disjoint r hr
  set A := cylRegion r with hA_def
  set B := leftHalfBall r with hB_def
  set C := rightHalfBall r with hC_def
  have hA_meas : MeasurableSet A := by
    have hc0 : Continuous (fun x : Point3 => x 0) := by fun_prop
    have hc12 : Continuous (fun x : Point3 => (x 1) ^ 2 + (x 2) ^ 2) := by fun_prop
    exact ((isClosed_Ici.preimage hc0).inter
      ((isClosed_Iic.preimage hc0).inter (isClosed_Iic.preimage hc12))).measurableSet
  have hB_meas : MeasurableSet B := by
    have hc0 : Continuous (fun x : Point3 => x 0) := by fun_prop
    have h1 : IsClosed {x : Point3 | x 0 ≤ 0} := isClosed_Iic.preimage hc0
    have h2 : IsClosed (Metric.closedBall (0 : Point3) r) := isClosed_closedBall
    have h3 : B = {x | x 0 ≤ 0} ∩ Metric.closedBall (0 : Point3) r := by
      ext y
      simp only [B, leftHalfBall, Set.mem_inter_iff, Set.mem_setOf_eq, Metric.mem_closedBall]
      <;> rw [dist_zero_right]
    rw [h3]; exact (h1.inter h2).measurableSet
  have hC_meas : MeasurableSet C := by
    have hc0 : Continuous (fun x : Point3 => x 0) := by fun_prop
    let e0 : Point3 := EuclideanSpace.single 0 1
    have h1 : IsClosed {x : Point3 | x 0 ≥ 1} := isClosed_Ici.preimage hc0
    have h2 : IsClosed (Metric.closedBall e0 r) := isClosed_closedBall
    have h3 : C = {x | x 0 ≥ 1} ∩ Metric.closedBall e0 r := by
      ext y
      simp only [C, rightHalfBall, Set.mem_inter_iff, Set.mem_setOf_eq, Metric.mem_closedBall]
      <;> rw [dist_eq_norm]
    rw [h3]; exact (h1.inter h2).measurableSet
  have hAB : volume (A ∩ B) = 0 := h_disj.1
  have hAC : volume (A ∩ C) = 0 := h_disj.2.1
  have hBC : volume (B ∩ C) = 0 := h_disj.2.2
  have h_union : A ∪ B ∪ C ⊆ capsule r := by
    intro x hx
    rcases hx with (h | h)
    · rcases h with (h | h)
      · exact h_contain.1 h
      · exact h_contain.2.1 h
    · exact h_contain.2.2 h
  have h1 : volume (A ∪ B) = volume A + volume B := by
    have h_eq : volume (A ∪ B) + volume (A ∩ B) = volume A + volume B :=
      measure_union_add_inter A hB_meas
    rw [hAB] at h_eq
    simpa using h_eq
  have h_inter2 : volume ((A ∪ B) ∩ C) = 0 := by
    have h_eq : (A ∪ B) ∩ C = (A ∩ C) ∪ (B ∩ C) := by
      ext x; simp [Set.mem_inter_iff, Set.mem_union] <;> tauto
    rw [h_eq]
    have h_le : volume ((A ∩ C) ∪ (B ∩ C)) ≤ volume (A ∩ C) + volume (B ∩ C) :=
      measure_union_le _ _
    have h_rhs : volume (A ∩ C) + volume (B ∩ C) = 0 := by
      rw [hAC, hBC] <;> simp
    have h_le0 : volume ((A ∩ C) ∪ (B ∩ C)) ≤ 0 := by
      rw [h_rhs] at h_le; exact h_le
    exact bot_unique h_le0
  have h2 : volume ((A ∪ B) ∪ C) = volume (A ∪ B) + volume C := by
    have h_eq : volume ((A ∪ B) ∪ C) + volume ((A ∪ B) ∩ C) = volume (A ∪ B) + volume C :=
      measure_union_add_inter (A ∪ B) hC_meas
    rw [h_inter2] at h_eq
    simpa using h_eq
  have h3 : A ∪ B ∪ C = (A ∪ B) ∪ C := by rw [Set.union_assoc]
  have h_vol_union : volume (A ∪ B ∪ C) = volume A + volume B + volume C := by
    rw [h3, h2, h1] <;> ring
  have h_main : volume (capsule r) ≥ volume (A ∪ B ∪ C) := measure_mono h_union
  have h_vol_union : volume (A ∪ B ∪ C) = volume A + volume B + volume C := by
    rw [h3, h2, h1] <;> ring
  have h_pos1 : 0 ≤ Real.pi * r ^ 2 := by positivity
  have h_pos2 : 0 ≤ (2 / 3 : ℝ) * Real.pi * r ^ 3 := by positivity
  have h_sum : ENNReal.ofReal ((2 / 3 : ℝ) * Real.pi * r ^ 3) +
      ENNReal.ofReal ((2 / 3 : ℝ) * Real.pi * r ^ 3) =
      ENNReal.ofReal ((4 / 3 : ℝ) * Real.pi * r ^ 3) := by
    rw [←ENNReal.ofReal_add h_pos2 h_pos2] <;> congr 1 <;> ring
  have h_goal : volume A + volume B + volume C ≥
      ENNReal.ofReal (Real.pi * r ^ 2 + (4 / 3 : ℝ) * Real.pi * r ^ 3) := by
    rw [cylinder_volume_aligned r hr, leftHalfBall_volume r hr, rightHalfBall_volume r hr]
    have h_assoc : ENNReal.ofReal (Real.pi * r ^ 2) +
        (ENNReal.ofReal ((2 / 3 : ℝ) * Real.pi * r ^ 3) +
          ENNReal.ofReal ((2 / 3 : ℝ) * Real.pi * r ^ 3)) =
        ENNReal.ofReal (Real.pi * r ^ 2) +
          ENNReal.ofReal ((2 / 3 : ℝ) * Real.pi * r ^ 3) +
          ENNReal.ofReal ((2 / 3 : ℝ) * Real.pi * r ^ 3) := by abel
    rw [←h_assoc]
    rw [h_sum]
    rw [←ENNReal.ofReal_add h_pos1 (by positivity)] <;> rfl
  calc volume (capsule r)
    ≥ volume (A ∪ B ∪ C) := h_main
  _ = volume A + volume B + volume C := h_vol_union
  _ ≥ ENNReal.ofReal (Real.pi * r ^ 2 + (4 / 3 : ℝ) * Real.pi * r ^ 3) := h_goal

/-- Upper bound: capsule volume ≤ πr² + (8/3)πr³. -/
theorem capsule_volume_upper (r : ℝ) (hr : 0 < r) :
    volume (capsule r) ≤
      ENNReal.ofReal (Real.pi * r ^ 2 + (8 / 3 : ℝ) * Real.pi * r ^ 3) := by
  have h_sub := capsule_subset_union r hr
  let e0 : Point3 := EuclideanSpace.single 0 1
  set A := cylRegion r with hA_def
  set B := Metric.closedBall (0 : Point3) r with hB_def
  set C := Metric.closedBall e0 r with hC_def
  have h1 : volume (A ∪ B) ≤ volume A + volume B := measure_union_le A B
  have h2 : volume ((A ∪ B) ∪ C) ≤ volume (A ∪ B) + volume C := measure_union_le (A ∪ B) C
  have h3 : volume ((A ∪ B) ∪ C) ≤ volume A + volume B + volume C := by
    calc volume ((A ∪ B) ∪ C)
      ≤ volume (A ∪ B) + volume C := h2
    _ ≤ (volume A + volume B) + volume C := add_le_add h1 le_rfl
    _ = volume A + volume B + volume C := by abel
  have h4 : A ∪ B ∪ C = (A ∪ B) ∪ C := by rw [Set.union_assoc]
  have h_bound : volume (capsule r) ≤ volume A + volume B + volume C := by
    calc volume (capsule r)
      ≤ volume (A ∪ B ∪ C) := measure_mono h_sub
    _ = volume ((A ∪ B) ∪ C) := by rw [h4]
    _ ≤ volume A + volume B + volume C := h3
  rw [cylinder_volume_aligned r hr,
    EuclideanSpace.volume_closedBall_fin_three (0 : Point3) r,
    EuclideanSpace.volume_closedBall_fin_three (EuclideanSpace.single 0 1) r] at h_bound
  have h_ball : ENNReal.ofReal r ^ 3 * ENNReal.ofReal (Real.pi * 4 / 3) =
      ENNReal.ofReal ((4 / 3 : ℝ) * Real.pi * r ^ 3) := by
    have h1 : ENNReal.ofReal r ^ 3 = ENNReal.ofReal (r ^ 3) := by
      have h2 : ENNReal.ofReal r ^ 2 = ENNReal.ofReal (r ^ 2) := by
        calc ENNReal.ofReal r ^ 2
          = ENNReal.ofReal r * ENNReal.ofReal r := by ring
        _ = ENNReal.ofReal (r * r) := by rw [←ENNReal.ofReal_mul hr.le]
        _ = ENNReal.ofReal (r ^ 2) := by ring
      calc ENNReal.ofReal r ^ 3
        = ENNReal.ofReal r ^ 2 * ENNReal.ofReal r := by ring
      _ = ENNReal.ofReal (r ^ 2) * ENNReal.ofReal r := by rw [h2]
      _ = ENNReal.ofReal (r ^ 2 * r) := by rw [←ENNReal.ofReal_mul (by positivity)]
      _ = ENNReal.ofReal (r ^ 3) := by ring
    rw [h1]
    rw [←ENNReal.ofReal_mul (by positivity)] <;> ring
  rw [h_ball] at h_bound
  have h_pos1 : 0 ≤ Real.pi * r ^ 2 := by positivity
  have h_pos2 : 0 ≤ (4 / 3 : ℝ) * Real.pi * r ^ 3 := by positivity
  have h_sum2 : ENNReal.ofReal ((4 / 3 : ℝ) * Real.pi * r ^ 3) +
      ENNReal.ofReal ((4 / 3 : ℝ) * Real.pi * r ^ 3) =
      ENNReal.ofReal ((8 / 3 : ℝ) * Real.pi * r ^ 3) := by
    rw [←ENNReal.ofReal_add h_pos2 h_pos2] <;> congr 1 <;> ring
  have h_final : ENNReal.ofReal (Real.pi * r ^ 2) +
      (ENNReal.ofReal ((4 / 3 : ℝ) * Real.pi * r ^ 3) +
        ENNReal.ofReal ((4 / 3 : ℝ) * Real.pi * r ^ 3)) ≤
      ENNReal.ofReal (Real.pi * r ^ 2 + (8 / 3 : ℝ) * Real.pi * r ^ 3) := by
    rw [h_sum2]
    rw [←ENNReal.ofReal_add h_pos1 (by positivity)] <;> rfl
  have h_assoc : ENNReal.ofReal (Real.pi * r ^ 2) +
      ENNReal.ofReal ((4 / 3 : ℝ) * Real.pi * r ^ 3) +
      ENNReal.ofReal ((4 / 3 : ℝ) * Real.pi * r ^ 3) =
      ENNReal.ofReal (Real.pi * r ^ 2) +
      (ENNReal.ofReal ((4 / 3 : ℝ) * Real.pi * r ^ 3) +
        ENNReal.ofReal ((4 / 3 : ℝ) * Real.pi * r ^ 3)) := by abel
  rw [h_assoc] at h_bound
  exact le_trans h_bound h_final

end Kakeya.Streamlined.GeometricLemmas
