/-
# Directional Variation Scaling Under Blow-Up

Translation invariance and blow-up scaling for local directional variation.

## Main results

- `directionalVariationIn_translation`: translation invariance
- `directionalVariationIn_blowUp_bound`: upper bound via scaling

These are used by `directionalVariation_blowUp_vanishing`.
-/

import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.Basic
import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.DirectionalVariationLemmas
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.BlowUpScaling
import Mathlib.Tactic

open MeasureTheory Metric Set ENNReal Filter
open scoped MeasureTheory ContDiff

namespace Geometry.StructureTheorem

variable {n : ℕ}

open Perimeter

/-- **Translation invariance of local directional variation.** -/
lemma directionalVariationIn_translation (S : Set (E n)) (w : E n) (v : E n) (Ω : Set (E n)) :
    directionalVariationIn (translateSet S v) w (translateSet Ω v) =
      directionalVariationIn S w Ω := by
  let τ : E n ≃ₜ E n :=
    { toFun := fun x => x + v
      invFun := fun x => x - v
      left_inv := by intro x; simp [sub_add_cancel]
      right_inv := by intro x; simp [add_sub_cancel]
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have h1 : directionalVariationIn (translateSet S v) w (translateSet Ω v) ≤
      directionalVariationIn S w Ω := by
    apply iSup_le
    intro φ
    let ψ : TestScalar :=
      { toFun := fun x => φ.val.toFun (x + v)
        smooth := φ.val.smooth.comp (by fun_prop : ContDiff ℝ ∞ (fun x : E n => x + v))
        compact := by
          have h_sub : Function.support (fun x : E n => φ.val.toFun (x + v)) ⊆
              (fun x : E n => x - v) '' tsupport φ.val.toFun := by
            intro x hx
            have h2 : φ.val.toFun (x + v) ≠ 0 := hx
            have h3 : x + v ∈ Function.support φ.val.toFun := h2
            have h4 : x + v ∈ tsupport φ.val.toFun := subset_closure h3
            refine ⟨x + v, h4, ?_⟩
            simp
          have h_img : IsCompact ((fun x : E n => x - v) '' tsupport φ.val.toFun) :=
            φ.val.compact.image (by fun_prop)
          have h_closed : IsClosed ((fun x : E n => x - v) '' tsupport φ.val.toFun) :=
            h_img.isClosed
          have h_ts : tsupport (fun x : E n => φ.val.toFun (x + v)) ⊆
              (fun x : E n => x - v) '' tsupport φ.val.toFun :=
            closure_minimal h_sub h_closed
          exact h_img.of_isClosed_subset (isClosed_tsupport _) h_ts
        bound := by intro x; exact φ.val.bound (x + v) }
    have h_support : Function.support ψ.toFun ⊆ Ω := by
      intro x hx
      have h2 : ψ.toFun x ≠ 0 := hx
      have h3 : φ.val.toFun (x + v) ≠ 0 := h2
      have h4 : x + v ∈ Function.support φ.val.toFun := h3
      have h5 : x + v ∈ translateSet Ω v := φ.property h4
      rcases h5 with ⟨z, hz, hz2⟩
      have h6 : z = x := by simpa using hz2
      rw [h6] at hz
      exact hz
    let ψ' : {φ : TestScalar // Function.support φ.toFun ⊆ Ω} := ⟨ψ, h_support⟩
    have h_fderiv : ∀ x, fderiv ℝ ψ.toFun x w = fderiv ℝ φ.val.toFun (x + v) w := by
      intro x
      have h_diff : DifferentiableAt ℝ φ.val.toFun (x + v) :=
        φ.val.smooth.differentiable (by norm_num) (x + v)
      have h_g_diff : DifferentiableAt ℝ (fun x : E n => x + v) x := by fun_prop
      have h_ψ_comp : ψ.toFun = φ.val.toFun ∘ (fun x : E n => x + v) := by funext z; rfl
      have h_eq1 : fderiv ℝ ψ.toFun x =
          (fderiv ℝ φ.val.toFun (x + v)).comp (fderiv ℝ (fun x : E n => x + v) x) := by
        rw [h_ψ_comp]
        exact fderiv_comp x h_diff h_g_diff
      have h_eq2 : fderiv ℝ (fun x : E n => x + v) x = ContinuousLinearMap.id ℝ (E n) := by
        have h : HasFDerivAt (fun x : E n => x + v) (ContinuousLinearMap.id ℝ (E n)) x :=
          (hasFDerivAt_id x).add_const v
        exact h.fderiv
      rw [h_eq1, h_eq2] <;> rfl
    have h_map : MeasurePreserving (fun x : E n => x + v) volume volume :=
      measurePreserving_add_right volume v
    have h_integral : ∫ y in translateSet S v, fderiv ℝ φ.val.toFun y w =
        ∫ x in S, fderiv ℝ ψ.toFun x w := by
      have h_iff : ∀ (g : E n → ℝ),
          ∫ y in translateSet S v, g y ∂volume = ∫ x in S, g (x + v) ∂volume := by
        intro g
        have h_img : (fun x : E n => x + v) '' S = translateSet S v := by rfl
        rw [← h_img]
        exact h_map.setIntegral_image_emb τ.measurableEmbedding g S
      rw [h_iff (fun y => fderiv ℝ φ.val.toFun y w)]
      have h_eq : (fun x : E n => fderiv ℝ φ.val.toFun (x + v) w) = fun x : E n => fderiv ℝ ψ.toFun x w := by
        funext x
        exact (h_fderiv x).symm
      rw [h_eq]
    rw [h_integral]
    exact le_iSup (fun (ψ' : {φ : TestScalar // Function.support φ.toFun ⊆ Ω}) =>
      ENNReal.ofReal |∫ x in S, fderiv ℝ ψ'.val.toFun x w|) ψ'
  have h2 : directionalVariationIn S w Ω ≤
      directionalVariationIn (translateSet S v) w (translateSet Ω v) := by
    apply iSup_le
    intro ψ
    let φ : TestScalar :=
      { toFun := fun x => ψ.val.toFun (x - v)
        smooth := ψ.val.smooth.comp (by fun_prop : ContDiff ℝ ∞ (fun x : E n => x - v))
        compact := by
          have h_sub : Function.support (fun x : E n => ψ.val.toFun (x - v)) ⊆
              (fun x : E n => x + v) '' tsupport ψ.val.toFun := by
            intro x hx
            have h2 : ψ.val.toFun (x - v) ≠ 0 := hx
            have h3 : x - v ∈ Function.support ψ.val.toFun := h2
            have h4 : x - v ∈ tsupport ψ.val.toFun := subset_closure h3
            refine ⟨x - v, h4, ?_⟩
            simp
          have h_img : IsCompact ((fun x : E n => x + v) '' tsupport ψ.val.toFun) :=
            ψ.val.compact.image (by fun_prop)
          have h_closed : IsClosed ((fun x : E n => x + v) '' tsupport ψ.val.toFun) :=
            h_img.isClosed
          have h_ts : tsupport (fun x : E n => ψ.val.toFun (x - v)) ⊆
              (fun x : E n => x + v) '' tsupport ψ.val.toFun :=
            closure_minimal h_sub h_closed
          exact h_img.of_isClosed_subset (isClosed_tsupport _) h_ts
        bound := by intro x; exact ψ.val.bound (x - v) }
    have h_support : Function.support φ.toFun ⊆ translateSet Ω v := by
      intro x hx
      have h2 : φ.toFun x ≠ 0 := hx
      have h3 : ψ.val.toFun (x - v) ≠ 0 := h2
      have h4 : x - v ∈ Function.support ψ.val.toFun := h3
      have h5 : x - v ∈ Ω := ψ.property h4
      exact ⟨x - v, h5, by simp⟩
    let φ' : {φ : TestScalar // Function.support φ.toFun ⊆ translateSet Ω v} := ⟨φ, h_support⟩
    have h_fderiv : ∀ y, fderiv ℝ ψ.val.toFun y w = fderiv ℝ φ.toFun (y + v) w := by
      intro y
      set z := (y + v) - v with hz
      have hz_y : z = y := by simp [z]
      have h_diff : DifferentiableAt ℝ ψ.val.toFun z :=
        ψ.val.smooth.differentiable (by norm_num) z
      have h_g_diff : DifferentiableAt ℝ (fun t : E n => t - v) (y + v) := by fun_prop
      have h_φ_comp : φ.toFun = ψ.val.toFun ∘ (fun t : E n => t - v) := by funext t; rfl
      have h_eq1 : fderiv ℝ φ.toFun (y + v) =
          (fderiv ℝ ψ.val.toFun z).comp (fderiv ℝ (fun t : E n => t - v) (y + v)) := by
        rw [h_φ_comp]
        exact fderiv_comp (y + v) h_diff h_g_diff
      have h_eq2 : fderiv ℝ (fun t : E n => t - v) (y + v) = ContinuousLinearMap.id ℝ (E n) := by
        have h : HasFDerivAt (fun t : E n => t - v) (ContinuousLinearMap.id ℝ (E n)) (y + v) :=
          (hasFDerivAt_id (y + v)).add_const (-v)
        exact h.fderiv
      have h_eq3 : fderiv ℝ ψ.val.toFun z = fderiv ℝ ψ.val.toFun y := by rw [hz_y]
      rw [h_eq1, h_eq2, h_eq3] <;> rfl
    have h_map : MeasurePreserving (fun x : E n => x + v) volume volume :=
      measurePreserving_add_right volume v
    have h_integral : ∫ x in S, fderiv ℝ ψ.val.toFun x w =
        ∫ y in translateSet S v, fderiv ℝ φ.toFun y w := by
      have h_iff2 : ∀ (g : E n → ℝ),
          ∫ x in S, g x ∂volume = ∫ y in translateSet S v, g (y - v) ∂volume := by
        intro g
        have h_img : (fun x : E n => x + v) '' S = translateSet S v := by rfl
        have h := h_map.setIntegral_image_emb τ.measurableEmbedding (fun y => g (y - v)) S
        rw [h_img] at h
        have h' : ∫ x in S, g ((x + v) - v) ∂volume = ∫ x in S, g x ∂volume := by
          congr with x <;> simp
        exact (h.trans h').symm
      rw [h_iff2 (fun x => fderiv ℝ ψ.val.toFun x w)]
      have h_eq : (fun y : E n => fderiv ℝ ψ.val.toFun (y - v) w) = fun y : E n => fderiv ℝ φ.toFun y w := by
        funext y
        have h4 := h_fderiv (y - v)
        have h5 : (y - v) + v = y := by abel
        rw [h5] at h4
        exact h4
      rw [h_eq]
    rw [h_integral]
    exact le_iSup (fun (φ' : {φ : TestScalar // Function.support φ.toFun ⊆ translateSet Ω v}) =>
      ENNReal.ofReal |∫ x in translateSet S v, fderiv ℝ φ'.val.toFun x w|) φ'
  exact le_antisymm h1 h2

/-- **Blow-up scaling bound for local directional variation.**

For `K ⊆ closedBall 0 R`,
`directionalVariationIn (blowUp U x r) w K ≤ r^{1-n} · directionalVariationIn U w (closedBall x (rR))`.
-/
lemma directionalVariationIn_blowUp_bound
    {U : Set (E n)} (hU : MeasurableSet U)
    {x : E n} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R)
    (hn : 1 ≤ n) (w : E n) (K : Set (E n)) (hK : K ⊆ closedBall (0 : E n) R) :
    directionalVariationIn (blowUp U x r) w K ≤
      ENNReal.ofReal ((1 / r) ^ (n - 1)) * directionalVariationIn U w (closedBall x (r * R)) := by
  let U' := (fun y : E n => y - x) '' U
  have hU'_meas : MeasurableSet U' := by
    let τ : E n ≃ₜ E n :=
      { toFun := fun y => y - x
        invFun := fun z => z + x
        left_inv := by intro y; simp [sub_add_cancel]
        right_inv := by intro z; simp [add_sub_cancel]
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
    exact τ.measurableEmbedding.measurableSet_image.mpr hU
  have h_blowUp_eq : blowUp U x r = scaleSet (1 / r) U' := by
    ext z
    simp only [blowUp, blowUpMap, scaleSet, Set.mem_image]
    <;> constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y - x, ⟨y, hy, by simp⟩, ?_⟩
      simp [smul_smul, hr.ne'] <;> ring
    · rintro ⟨z', ⟨y, hy, rfl⟩, rfl⟩
      refine ⟨y, hy, ?_⟩
      simp [smul_smul, hr.ne'] <;> ring
  have h_ball_eq : closedBall (0 : E n) R = scaleSet (1 / r) (closedBall (0 : E n) (r * R)) := by
    ext z
    simp only [mem_closedBall, scaleSet, Set.mem_image, dist_zero_right]
    constructor
    · intro hz
      refine ⟨r • z, ?_, ?_⟩
      · have h : ‖r • z‖ ≤ r * R := by
          rw [norm_smul]
          have h' : |r| * ‖z‖ ≤ r * R := by
            rw [abs_of_pos hr]
            exact mul_le_mul_of_nonneg_left hz (by positivity)
          exact h'
        simpa using h
      · simp [smul_smul, hr.ne'] <;> ring
    · rintro ⟨y, hy, rfl⟩
      have h : ‖(1 / r) • y‖ ≤ R := by
        rw [norm_smul]
        have h' : |1 / r| * ‖y‖ ≤ R := by
          rw [abs_of_pos (by positivity : 0 < 1 / r)]
          calc (1 / r) * ‖y‖
            ≤ (1 / r) * (r * R) := by gcongr
          _ = R := by
            field_simp [hr.ne'] <;> ring
        exact h'
      simpa using h
  have h1 : directionalVariationIn (blowUp U x r) w K ≤
      directionalVariationIn (blowUp U x r) w (closedBall (0 : E n) R) :=
    directionalVariationIn_mono (blowUp U x r) w hK
  have h_main : directionalVariationIn (blowUp U x r) w (closedBall (0 : E n) R) =
      ENNReal.ofReal ((1 / r) ^ (n - 1)) * directionalVariationIn U w (closedBall x (r * R)) := by
    rw [h_blowUp_eq, h_ball_eq]
    rw [directionalVariationIn_scaling U' hU'_meas (by positivity) hn w (closedBall (0 : E n) (r * R))]
    have h_trans : directionalVariationIn (translateSet U' x) w (translateSet (closedBall (0 : E n) (r * R)) x) =
        directionalVariationIn U' w (closedBall (0 : E n) (r * R)) :=
      directionalVariationIn_translation U' w x (closedBall (0 : E n) (r * R))
    have h_eq1 : translateSet U' x = U := by
      ext z
      simp only [U', translateSet, Set.mem_image]
      constructor
      · rintro ⟨y, ⟨w', hw', rfl⟩, rfl⟩
        have h_simp : w' - x + x = w' := by abel
        rw [h_simp]
        exact hw'
      · intro hz
        exact ⟨z - x, ⟨z, hz, by simp⟩, by simp⟩
    have h_eq2 : translateSet (closedBall (0 : E n) (r * R)) x = closedBall x (r * R) := by
      ext z
      simp [translateSet, dist_eq_norm]
      <;> abel
    rw [h_eq1, h_eq2] at h_trans
    exact congr_arg (fun z : ENNReal => ENNReal.ofReal ((1 / r) ^ (n - 1)) * z) h_trans.symm
  rw [h_main] at h1
  exact h1

end Geometry.StructureTheorem
