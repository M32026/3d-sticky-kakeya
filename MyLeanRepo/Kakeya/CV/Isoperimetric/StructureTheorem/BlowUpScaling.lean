import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import Mathlib.Geometry.Euclidean.Volume.Measure
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Tactic

/-!
# Blow-Up Scaling Lemmmas

Volume scaling under the blow-up map `Φ_{x,r}(y) = (y - x)/r`.

## Main results

- `blow_up_volume`: `volume(S_{x,r} ∩ B(0,R)) = r^{-n} · volume(S ∩ B(x,rR))`

## References

- Maggi, *Sets of Finite Perimeter*, Lemma 15.11
-/

open MeasureTheory Metric Set ENNReal
open scoped MeasureTheory Pointwise

namespace Geometry.StructureTheorem

variable {n : ℕ}

/-- The blow-up map `Φ_{x,r}(y) = (y - x)/r`. -/
noncomputable def blowUpMap (x : E n) (r : ℝ) : E n → E n :=
  fun y => (1 / r) • (y - x)

/-- The blow-up of a set `S` at `x` with scale `r`: `S_{x,r} = (S - x)/r`. -/
noncomputable def blowUp (S : Set (E n)) (x : E n) (r : ℝ) : Set (E n) :=
  blowUpMap x r '' S

/-- The scaling map `z ↦ t • z` as a continuous linear equiv. -/
noncomputable def scalingEquiv (t : ℝ) (ht : t ≠ 0) : E n ≃L[ℝ] E n :=
  { toFun := fun z => t • z
    invFun := fun z => (1 / t) • z
    left_inv := fun z => by
      have h : (1 / t) • (t • z) = z := by
        rw [smul_smul]
        have h2 : (1 / t) * t = 1 := by field_simp [ht]
        rw [h2, one_smul]
      simpa using h
    right_inv := fun z => by
      have h : t • ((1 / t) • z) = z := by
        rw [smul_smul]
        have h2 : t * (1 / t) = 1 := by field_simp [ht]
        rw [h2, one_smul]
      simpa using h
    map_add' := fun z w => smul_add t z w
    map_smul' := fun c z => by
      simpa [smul_smul, mul_comm] using rfl
    continuous_toFun := continuous_id.const_smul t
    continuous_invFun := continuous_id.const_smul (1 / t) }

@[simp]
lemma scalingEquiv_apply (t : ℝ) (ht : t ≠ 0) (z : E n) :
    scalingEquiv t ht z = t • z := by
  exact rfl

lemma scalingEquiv_det (t : ℝ) (ht : t ≠ 0) :
    LinearMap.det ((scalingEquiv (n := n) t ht : E n ≃L[ℝ] E n) : E n →ₗ[ℝ] E n) = t ^ n := by
  have h_eq : ((scalingEquiv (n := n) t ht : E n ≃L[ℝ] E n) : E n →ₗ[ℝ] E n)
      = t • (1 : E n →ₗ[ℝ] E n) := by
    apply LinearMap.ext
    intro z
    have h1 : ((scalingEquiv (n := n) t ht : E n ≃L[ℝ] E n) : E n →ₗ[ℝ] E n) z
        = (scalingEquiv (n := n) t ht) z := by rfl
    rw [h1, scalingEquiv_apply]
    <;> simp
    <;> rfl
  rw [h_eq, LinearMap.det_smul]
  <;> simp

/-- `blowUpMap x r` is a homeomorphism when `r ≠ 0`. -/
noncomputable def blowUpMapHomeomorph (x : E n) {r : ℝ} (hr : r ≠ 0) : E n ≃ₜ E n :=
  { toFun := blowUpMap x r,
    invFun := fun z => x + r • z,
    left_inv := fun z => by
      simp [blowUpMap, smul_smul, hr] <;> abel,
    right_inv := fun z => by
      simp [blowUpMap, smul_smul, hr] <;> abel,
    continuous_toFun := by
      have h : (blowUpMap x r) = fun y : E n => (1 / r) • (y - x) := by
        funext y; simp [blowUpMap]
      rw [h]
      fun_prop,
    continuous_invFun := by fun_prop }

/-- `blowUpMap x r` is a measurable embedding when `r ≠ 0`. -/
lemma blowUpMap_measurableEmbedding (x : E n) {r : ℝ} (hr : r ≠ 0) :
    MeasurableEmbedding (blowUpMap x r) :=
  (blowUpMapHomeomorph x hr).measurableEmbedding

/-- Translation invariance of volume: `volume((S - x)) = volume S)` for measurable `S`. -/
lemma volume_translate_sub {S : Set (E n)} (hS : MeasurableSet S) (x : E n) :
    volume ((fun y : E n => y - x) '' S) = volume S := by
  let f : E n → E n := fun y => y - x
  let g : E n → E n := fun z => z + x
  have hfg : Function.LeftInverse g f := by intro y; simp [f, g]
  have h_mp_g : MeasurePreserving g volume volume :=
    measurePreserving_add_right volume x
  have h_image_eq : f '' S = g ⁻¹' S := by
    ext z
    simp only [Set.mem_image, Set.mem_preimage, f, g]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hz
      exact ⟨z + x, hz, by simp [f, g]⟩
  rw [h_image_eq]
  have h_map : Measure.map g volume = volume := h_mp_g.map_eq
  have h_apply : (Measure.map g volume) S = volume (g ⁻¹' S) :=
    Measure.map_apply h_mp_g.measurable hS
  rw [h_map] at h_apply
  exact h_apply.symm

/-- `S_{x,r} ∩ B(0,R) = (S ∩ B(x,rR))_{x,r}`. -/
lemma blowUp_inter_ball {S : Set (E n)} {x : E n} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) :
    blowUp S x r ∩ ball (0 : E n) R = blowUp (S ∩ ball x (r * R)) x r := by
  ext z
  simp only [Set.mem_inter_iff, Set.mem_image, blowUp]
  constructor
  · rintro ⟨⟨y, hyS, rfl⟩, hzball⟩
    have h_pos : 0 < (1 / r : ℝ) := by positivity
    have h_norm : ‖(1 / r : ℝ) • (y - x)‖ < R := by
      simpa [ball, dist_zero_right, blowUpMap] using hzball
    have h2 : ‖(1 / r : ℝ) • (y - x)‖ = (1 / r) * ‖y - x‖ := by
      calc ‖(1 / r : ℝ) • (y - x)‖
        = ‖(1 / r : ℝ)‖ * ‖y - x‖ := norm_smul (1 / r : ℝ) (y - x)
      _ = |(1 / r : ℝ)| * ‖y - x‖ := by rfl
      _ = (1 / r) * ‖y - x‖ := by rw [abs_of_pos h_pos]
    rw [h2] at h_norm
    have h3 : ‖y - x‖ < r * R := by
      calc ‖y - x‖
        = r * ((1 / r) * ‖y - x‖) := by field_simp [hr.ne'] <;> ring
      _ < r * R := by gcongr
    have h_yball : y ∈ ball x (r * R) := by
      simpa [ball, dist_eq_norm] using h3
    exact ⟨y, ⟨hyS, h_yball⟩, rfl⟩
  · rintro ⟨y, ⟨hyS, hyball⟩, rfl⟩
    have h_pos : 0 < (1 / r : ℝ) := by positivity
    have h2 : ‖y - x‖ < r * R := by simpa [ball, dist_eq_norm] using hyball
    have h3 : ‖(1 / r : ℝ) • (y - x)‖ < R := by
      have h4 : ‖(1 / r : ℝ) • (y - x)‖ = (1 / r) * ‖y - x‖ := by
        calc ‖(1 / r : ℝ) • (y - x)‖
          = ‖(1 / r : ℝ)‖ * ‖y - x‖ := norm_smul (1 / r : ℝ) (y - x)
        _ = |(1 / r : ℝ)| * ‖y - x‖ := by rfl
        _ = (1 / r) * ‖y - x‖ := by rw [abs_of_pos h_pos]
      rw [h4]
      have h5 : (1 / r) * ‖y - x‖ < (1 / r) * (r * R) := by gcongr
      have h6 : (1 / r) * (r * R) = R := by field_simp [hr.ne'] <;> ring
      rw [h6] at h5; exact h5
    have hzball : blowUpMap x r y ∈ ball (0 : E n) R := by
      simpa [ball, dist_zero_right, blowUpMap] using h3
    exact ⟨⟨y, hyS, rfl⟩, hzball⟩

/-- Volume scaling under blow-up:
`volume(S_{x,r} ∩ B(0,R)) = r^{-n} · volume(S ∩ B(x,rR))`. -/
lemma blow_up_volume {S : Set (E n)} (hS : MeasurableSet S) {x : E n} {r R : ℝ}
    (hr : 0 < r) (hR : 0 ≤ R) :
    volume (blowUp S x r ∩ ball (0 : E n) R) =
      ENNReal.ofReal (r ^ n)⁻¹ * volume (S ∩ ball x (r * R)) := by
  have hne : r ≠ 0 := hr.ne'
  have h_inv_ne : (1 / r : ℝ) ≠ 0 := by positivity
  set T : Set (E n) := S ∩ ball x (r * R) with hT_def
  have hT_meas : MeasurableSet T := hS.inter isOpen_ball.measurableSet
  set T_x : Set (E n) := (fun y => y - x) '' T with hTx_def
  set scl : E n ≃L[ℝ] E n := scalingEquiv (1 / r) h_inv_ne with hscl_def

  -- Translation preserves volume
  have h_trans_vol : volume T_x = volume T := volume_translate_sub hT_meas x

  -- Key equality: scl (y - x) = blowUpMap x r y
  have h_eq1 : ∀ (y : E n), scl (y - x) = blowUpMap x r y := by
    intro y
    rw [scalingEquiv_apply, blowUpMap]
    <;> ring

  -- Scaling image equals blow-up of T
  have h_scl_image : scl '' T_x = blowUp T x r := by
    ext z
    simp only [Set.mem_image, blowUp, hTx_def]
    constructor
    · rintro ⟨_, ⟨y, hyT, rfl⟩, rfl⟩
      exact ⟨y, hyT, (h_eq1 y).symm⟩
    · rintro ⟨y, hyT, rfl⟩
      exact ⟨y - x, ⟨y, hyT, by simp⟩, h_eq1 y⟩

  -- Volume scaling formula
  have hdet : LinearMap.det ((scl : E n ≃L[ℝ] E n) : E n →ₗ[ℝ] E n) = (1 / r) ^ n := by
    exact scalingEquiv_det (t := 1 / r) h_inv_ne
  have h_vol : volume (scl '' T_x) =
      ENNReal.ofReal |LinearMap.det ((scl : E n ≃L[ℝ] E n) : E n →ₗ[ℝ] E n)| * volume T_x :=
    MeasureTheory.Measure.addHaar_image_continuousLinearEquiv volume scl T_x

  have h_pos : 0 < r ^ n := pow_pos hr n
  have h_inv : (1 / r) ^ n = (r ^ n)⁻¹ := by
    have h9 : ∀ k : ℕ, (1 / r) ^ k = (r ^ k)⁻¹ := by
      intro k
      induction k with
      | zero => norm_num
      | succ k ih =>
        rw [pow_succ, pow_succ, ih]
        <;> field_simp [hne] <;> ring
    exact h9 n

  calc
    volume (blowUp S x r ∩ ball (0 : E n) R)
      = volume (blowUp T x r) := by
        rw [show blowUp T x r = blowUp S x r ∩ ball (0 : E n) R from
          (blowUp_inter_ball (S := S) (x := x) (r := r) (R := R) hr hR).symm]
    _ = volume (scl '' T_x) := by rw [h_scl_image]
    _ = ENNReal.ofReal |(1 / r) ^ n| * volume T_x := by rw [h_vol, hdet]
    _ = ENNReal.ofReal ((1 / r) ^ n) * volume T_x := by
      have h_abs : |(1 / r) ^ n| = (1 / r) ^ n := by
        rw [abs_pow, abs_of_pos (show (0 : ℝ) < 1 / r by positivity)]
      rw [h_abs]
    _ = ENNReal.ofReal (r ^ n)⁻¹ * volume T := by
      rw [h_inv]
      have h_eq1 : ENNReal.ofReal ((r ^ n)⁻¹) = (ENNReal.ofReal (r ^ n))⁻¹ :=
        ENNReal.ofReal_inv_of_pos h_pos
      rw [h_eq1, h_trans_vol]

/-- Blow-up preserves null sets: if `volume S = 0`, then `volume (blowUp S x r) = 0`. -/
lemma blowUp_null {S : Set (E n)} (hS : MeasurableSet S) (x : E n) {r : ℝ} (hr : r ≠ 0)
    (h_null : volume S = 0) : volume (blowUp S x r) = 0 := by
  set T_x : Set (E n) := (fun y => y - x) '' S with hTx_def
  have h_inv_ne : (1 / r : ℝ) ≠ 0 := by positivity
  set scl : E n ≃L[ℝ] E n := scalingEquiv (1 / r) h_inv_ne with hscl_def
  have h_trans_vol : volume T_x = volume S := volume_translate_sub hS x
  have h_eq1 : ∀ (y : E n), scl (y - x) = blowUpMap x r y := by
    intro y
    rw [scalingEquiv_apply, blowUpMap]
    <;> ring
  have h_scl_image : scl '' T_x = blowUp S x r := by
    ext z
    simp only [Set.mem_image, blowUp, hTx_def]
    constructor
    · rintro ⟨_, ⟨y, hyS, rfl⟩, rfl⟩
      exact ⟨y, hyS, (h_eq1 y).symm⟩
    · rintro ⟨y, hyS, rfl⟩
      exact ⟨y - x, ⟨y, hyS, by simp⟩, h_eq1 y⟩
  have h_vol : volume (scl '' T_x) =
      ENNReal.ofReal |LinearMap.det ((scl : E n →ₗ[ℝ] E n))| * volume T_x :=
    MeasureTheory.Measure.addHaar_image_continuousLinearEquiv volume scl T_x
  rw [←h_scl_image, h_vol, h_trans_vol, h_null]
  <;> simp

end Geometry.StructureTheorem
