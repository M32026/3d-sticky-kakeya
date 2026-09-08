import MyLeanRepo.Kakeya.Streamlined.Geometry
import MyLeanRepo.Kakeya.Streamlined.VolumeHelpers
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.CapsuleVolume
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv

/-!
# Tube volume estimates and auxiliary geometric facts
-/

noncomputable section

open MeasureTheory Metric

namespace Kakeya.Streamlined

private lemma norm_sq_eq_sum_sq (x : Point3) :
    ‖x‖ ^ 2 = ∑ i : Fin 3, (x i) ^ 2 := by
  have h : inner ℝ x x = ‖x‖ ^ 2 := real_inner_self_eq_norm_sq x
  rw [← h, PiLp.inner_apply]
  congr with i
  simp [pow_two]

/-! ### Volume of a general rectangular box -/

private theorem volume_rectBox (lo hi : Fin 3 → ℝ) (h : ∀ i, lo i ≤ hi i) :
    volume ((WithLp.toLp 2) '' Set.Icc lo hi) =
    ENNReal.ofReal ((hi 0 - lo 0) * (hi 1 - lo 1) * (hi 2 - lo 2)) := by
  let toLp : (Fin 3 → ℝ) → Point3 := WithLp.toLp 2
  have h_mp : MeasurePreserving toLp := PiLp.volume_preserving_toLp (ι := Fin 3)
  have h_inj : Function.Injective toLp := by
    intro a b h; simpa [toLp, WithLp.toLp_injective] using h
  have h_cont : Continuous toLp := PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 3 => ℝ)
  have h_meas : Measurable toLp := h_cont.measurable
  have h_S_meas : MeasurableSet (Set.Icc lo hi) := measurableSet_Icc
  have h_img_meas : MeasurableSet (toLp '' Set.Icc lo hi) := by
    have h_eq : toLp '' Set.Icc lo hi = (fun x : Point3 => x.ofLp) ⁻¹' Set.Icc lo hi := by
      ext y
      simp only [toLp, Set.mem_image, Set.mem_preimage]
      constructor
      · rintro ⟨x, hx, rfl⟩; simpa [WithLp.ofLp_toLp] using hx
      · intro hy; refine ⟨y.ofLp, hy, ?_⟩; simp [WithLp.ofLp_toLp]
    rw [h_eq]
    have h_cont2 : Continuous (fun x : Point3 => x.ofLp) :=
      PiLp.continuous_ofLp (p := 2) (β := fun _ : Fin 3 => ℝ)
    exact h_cont2.measurable h_S_meas
  have h_map : Measure.map toLp volume = volume := h_mp.map_eq
  have h_vol1 : volume (toLp '' Set.Icc lo hi) = volume (Set.Icc lo hi) := by
    calc volume (toLp '' Set.Icc lo hi)
      = Measure.map toLp volume (toLp '' Set.Icc lo hi) := by rw [h_map]
    _ = volume (toLp ⁻¹' (toLp '' Set.Icc lo hi)) := Measure.map_apply h_meas h_img_meas
    _ = volume (Set.Icc lo hi) := by rw [Set.preimage_image_eq (Set.Icc lo hi) h_inj]
  rw [h_vol1]
  have h_pi : volume (Set.Icc lo hi) = ∏ i : Fin 3, ENNReal.ofReal (hi i - lo i) :=
    Real.volume_Icc_pi
  rw [h_pi]
  have h_nonneg : ∀ i, 0 ≤ hi i - lo i := by
    intro i
    linarith [h i]
  have h_prod :
      (∏ i : Fin 3, ENNReal.ofReal (hi i - lo i)) =
        ENNReal.ofReal (hi 0 - lo 0) *
          ENNReal.ofReal (hi 1 - lo 1) *
            ENNReal.ofReal (hi 2 - lo 2) := by
    simp [Fin.prod_univ_succ]
    <;> ring
  rw [h_prod]
  rw [← ENNReal.ofReal_mul (h_nonneg 0)]
  rw [← ENNReal.ofReal_mul
    (mul_nonneg (h_nonneg 0) (h_nonneg 1))]

/-! ### 1. All δ-tubes have equal volume -/

theorem tube_volume_eq {δ : ℝ} (T U : DeltaTube δ) :
    T.volume = U.volume := by
  have hdir : ‖T.direction‖ = ‖U.direction‖ := by
    rw [T.direction_unit, U.direction_unit]
  let L : Point3 ≃ₗᵢ[ℝ] Point3 :=
    (Submodule.span ℝ {T.direction - U.direction})ᗮ.reflection
  have hL : L T.direction = U.direction := Submodule.reflection_sub hdir
  let e : Point3 ≃ᵃⁱ[ℝ] Point3 :=
    AffineIsometryEquiv.mk'
      (fun x : Point3 => U.base + L (x - T.base))
      L T.base
      (by
        intro x
        have h1 : (x -ᵥ T.base : Point3) = x - T.base :=
          PiLp.ext (congrFun rfl)
        simp [h1, vsub_eq_sub] <;> abel)
  have h_e_apply : ∀ x, e x = U.base + L (x - T.base) := by
    intro x
    rfl
  have h_seg : e '' unitSegment T.base T.direction = unitSegment U.base U.direction := by
    ext y
    simp only [unitSegment, Set.mem_image]
    constructor
    · rintro ⟨x, ⟨t, ht, rfl⟩, rfl⟩
      refine ⟨t, ht, ?_⟩
      have h_sub : T.base + t • T.direction - T.base = t • T.direction := by abel
      have hsm : L (t • T.direction) = t • U.direction := by rw [L.map_smul, hL]
      have h_goal : e (T.base + t • T.direction) =
          U.base + t • U.direction := by
        rw [h_e_apply, h_sub, hsm]
      exact h_goal.symm
    · rintro ⟨t, ht, rfl⟩
      refine ⟨T.base + t • T.direction, ⟨t, ht, rfl⟩, ?_⟩
      have h_sub : T.base + t • T.direction - T.base = t • T.direction := by abel
      have hsm : L (t • T.direction) = t • U.direction := by rw [L.map_smul, hL]
      have h_goal : e (T.base + t • T.direction) =
          U.base + t • U.direction := by
        rw [h_e_apply, h_sub, hsm]
      exact h_goal
  have h_carrier : e '' T.carrier = U.carrier := by
    have h1 : e '' T.carrier = e '' (cthickening δ (unitSegment T.base T.direction)) := rfl
    rw [h1]
    have h2 : e '' cthickening δ (unitSegment T.base T.direction) =
        cthickening δ (e '' unitSegment T.base T.direction) := by
      ext y
      simp only [Set.mem_image, cthickening_eq_preimage_infEDist, Set.mem_preimage, Set.mem_Iic]
      constructor
      · rintro ⟨x, hx, rfl⟩
        have h : infEDist (e x) (e '' unitSegment T.base T.direction) = infEDist x (unitSegment T.base T.direction) :=
          Metric.infEDist_image e.isometry
        rw [h]; exact hx
      · intro hy
        let x := e.symm y
        have h1 : e x = y := e.apply_symm_apply y
        have h2 : infEDist x (unitSegment T.base T.direction) = infEDist (e x) (e '' unitSegment T.base T.direction) :=
          (Metric.infEDist_image e.isometry).symm
        refine ⟨x, ?_, h1⟩
        rw [h2, h1]; exact hy
    rw [h2, h_seg] <;> rfl
  have h_meas : MeasurableSet T.carrier :=
    IsClosed.measurableSet (isClosed_Iic.preimage continuous_infEDist)
  have h_vol : volume (e '' T.carrier) = volume T.carrier :=
    AffineIsometryEquiv.volume_image e T.carrier h_meas
  rw [h_carrier] at h_vol
  exact h_vol.symm

/-! ### 2. Volume lower bound: 2δ² -/

theorem tube_volume_ge_two_delta_sq (δ : ℝ) (hδ : 0 < δ) :
    ENNReal.ofReal (2 * δ ^ 2) ≤ Kakeya.deltaTubeVolume δ := by
  let e0 : Point3 := EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
  let S : Set Point3 := unitSegment 0 e0
  let d := δ * Real.sqrt 2
  have hd_pos : 0 < d := by positivity
  let lo : Fin 3 → ℝ := fun i =>
    match i with
    | 0 => 0
    | 1 => -d / 2
    | 2 => -d / 2
  let hi : Fin 3 → ℝ := fun i =>
    match i with
    | 0 => 1
    | 1 => d / 2
    | 2 => d / 2
  let toLp : (Fin 3 → ℝ) → Point3 := WithLp.toLp 2
  let B : Set Point3 := toLp '' Set.Icc lo hi
  have h_lo_hi : ∀ i, lo i ≤ hi i := by
    intro i
    fin_cases i <;> dsimp only [lo, hi, d] <;>
      linarith [Real.sqrt_nonneg 2, hδ]
  have h_vol_B : volume B = ENNReal.ofReal (2 * δ ^ 2) := by
    rw [volume_rectBox lo hi h_lo_hi]
    have h_mul : (1 - 0) * (d / 2 - (-d / 2)) * (d / 2 - (-d / 2)) = 2 * δ ^ 2 := by
      dsimp only [d]
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    rw [h_mul]
  have h_sub : B ⊆ cthickening δ S := by
    intro x hx
    rcases hx with ⟨z, hz, rfl⟩
    have h_z0 : 0 ≤ z 0 ∧ z 0 ≤ 1 := ⟨hz.1 0, hz.2 0⟩
    have h_z1 : |z 1| ≤ d / 2 := by
      have h1 : lo 1 ≤ z 1 := hz.1 1
      have h2 : z 1 ≤ hi 1 := hz.2 1
      dsimp only [lo, hi] at h1 h2
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    have h_z2 : |z 2| ≤ d / 2 := by
      have h1 : lo 2 ≤ z 2 := hz.1 2
      have h2 : z 2 ≤ hi 2 := hz.2 2
      dsimp only [lo, hi] at h1 h2
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    let t : ℝ := z 0
    let y : Point3 := t • e0
    have hy_in : y ∈ S := by
      refine ⟨t, h_z0, ?_⟩
      simp [y]
    have h_dist : ‖toLp z - y‖ ≤ δ := by
      have h3 : ‖toLp z - y‖ ^ 2 = (z 1) ^ 2 + (z 2) ^ 2 := by
        rw [norm_sq_eq_sum_sq]
        have h_coord0 : (toLp z - y) 0 = z 0 - t := by
          dsimp only [toLp]
          simp [y, e0, WithLp.ofLp_toLp]
        have h_coord1 : (toLp z - y) 1 = z 1 := by
          dsimp only [toLp]
          simp [y, e0, WithLp.ofLp_toLp]
        have h_coord2 : (toLp z - y) 2 = z 2 := by
          dsimp only [toLp]
          simp [y, e0, WithLp.ofLp_toLp]
        have h_sum :
            (∑ i : Fin 3, ((toLp z - y) i) ^ 2) =
              ((toLp z - y) 0) ^ 2 +
                ((toLp z - y) 1) ^ 2 +
                  ((toLp z - y) 2) ^ 2 := by
          simp [Fin.sum_univ_succ]
          <;> ring
        rw [h_sum, h_coord0, h_coord1, h_coord2]
        dsimp only [t]
        ring
      have h4 : (z 1) ^ 2 ≤ (d / 2) ^ 2 := by
        have h5 := abs_le.mp h_z1
        nlinarith
      have h6 : (z 2) ^ 2 ≤ (d / 2) ^ 2 := by
        have h7 := abs_le.mp h_z2
        nlinarith
      have h8 : ‖toLp z - y‖ ^ 2 ≤ δ ^ 2 := by
        rw [h3]
        have h9 : (d / 2) ^ 2 = δ ^ 2 / 2 := by
          dsimp only [d]
          nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
        nlinarith
      have h10 : 0 ≤ ‖toLp z - y‖ := by positivity
      nlinarith
    have h11 : infEDist (toLp z) S ≤ edist (toLp z) y :=
      Metric.infEDist_le_edist_of_mem hy_in
    have h12 : edist (toLp z) y = ENNReal.ofReal (dist (toLp z) y) := by
      simp [edist_dist]
    rw [h12] at h11
    have h13 : dist (toLp z) y = ‖toLp z - y‖ := by rfl
    rw [h13] at h11
    exact le_trans h11 (ENNReal.ofReal_le_ofReal h_dist)
  have h : volume B ≤ volume (cthickening δ S) := measure_mono h_sub
  rw [h_vol_B] at h
  exact h

/-! ### 3. Volume lower bound: πδ² (via capsule decomposition) -/

/-- Any δ-tube has volume at least πδ².

Follows from `capsule_volume_lower`, which gives the sharper bound
`πδ² + (4/3)πδ³`, and `tube_volume_eq` to transfer from the canonical
capsule to an arbitrary tube. -/
theorem tube_volume_ge_pi_delta_sq {δ : ℝ} (hδ : 0 < δ) (T : DeltaTube δ) :
    ENNReal.ofReal (Real.pi * δ ^ 2) ≤ T.volume := by
  have h1 : T.volume = Kakeya.deltaTubeVolume δ :=
    tube_volume_eq T
      { base := 0
        direction := EuclideanSpace.single (0 : Fin 3) (1 : ℝ)
        direction_unit := by simp }
  rw [h1]
  have h2 := GeometricLemmas.capsule_volume_lower δ hδ
  have h4 : Real.pi * δ ^ 2 ≤ Real.pi * δ ^ 2 + (4 / 3 : ℝ) * Real.pi * δ ^ 3 := by
    have h5 : 0 ≤ (4 / 3 : ℝ) * Real.pi * δ ^ 3 := by positivity
    linarith
  have h6 : ENNReal.ofReal (Real.pi * δ ^ 2) ≤
      ENNReal.ofReal (Real.pi * δ ^ 2 + (4 / 3 : ℝ) * Real.pi * δ ^ 3) :=
    ENNReal.ofReal_le_ofReal h4
  exact le_trans h6 h2

end Kakeya.Streamlined
