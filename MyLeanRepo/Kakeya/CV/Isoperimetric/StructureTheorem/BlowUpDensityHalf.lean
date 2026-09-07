/-
# Blow-Up Density Converges to 1/2

Proves that at a reduced boundary point, the blow-up density converges to 1/2,
conditional on explicit hypotheses (volume bounds, translation continuity,
local directional variation vanishing, two-sided density lower bound, orientation).

## Main result

- `blowUp_density_half_of_data`: `volume(blowUp S x r ∩ ball 0 1) → volume(ball 0 1)/2`

## Proof route

Subsequence principle → BV compactness → L¹_loc limit F → zero tangential variation
→ translation invariance → orientation inheritance → monotone factorization →
half-space characterization → two-sided bounds force α=0 → density 1/2.

## Dependencies

- `DirectionalVariationLemmas`: local directional variation + lower semicontinuity
- `HalfSpaceCharacterization`: orientation → monotone factorization → half-space
- `TranslationInvariance`: zero variation → translation invariance
- `DensityEstimates`: L¹ convergence of intersection volumes
- `BVCompactnessTranslation.SequenceCompactness`: BV compactness
- `RelativeIsoperimetric.Cutoff`: `volume_sphere_eq_zero`
-/

import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.Basic
import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.DirectionalVariationLemmas
import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.LowerSemicontinuity
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.BlowUpScaling
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.HalfSpaceCharacterization
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.DensityEstimates
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.ReducedBoundaryData
import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.BVCompactnessTranslation.SequenceCompactness
import MyLeanRepo.Kakeya.CV.Isoperimetric.RelativeIsoperimetric.Cutoff
import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import Mathlib.Tactic


open MeasureTheory Metric Set ENNReal Filter
open scoped MeasureTheory ContDiff

namespace Geometry.StructureTheorem

variable {n : ℕ}

/-- Complement blow-up scaling: `(ball 0 R) \\ blowUp S x r = blowUp ((ball x (r*R)) \\ S) x r`. -/
lemma blowUp_compl_inter_ball {S : Set (E n)} {x : E n} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) :
    (ball (0 : E n) R) \ blowUp S x r =
    blowUp ((ball x (r * R)) \ S) x r := by
  ext z
  simp only [Set.mem_diff, Set.mem_image, blowUp, blowUpMap]
  constructor
  · rintro ⟨hzball, hznot⟩
    have h_norm : ‖z‖ < R := by simpa [ball, dist_zero_right] using hzball
    let y := x + r • z
    have h_yball : y ∈ ball x (r * R) := by
      simpa [ball, dist_eq_norm] using by
        have h : ‖y - x‖ = r * ‖z‖ := by simp [y, norm_smul, abs_of_pos hr] <;> ring
        rw [h]; gcongr
    have h_ynotS : y ∉ S := by
      intro hys
      have h_goal : blowUpMap x r y = z := by
        dsimp only [blowUpMap, y]
        rw [add_sub_cancel_left, smul_smul]
        have h : (1 / r) * r = 1 := by field_simp [hr.ne']
        rw [h, one_smul]
      exact hznot ⟨y, hys, h_goal⟩
    exact ⟨y, ⟨h_yball, h_ynotS⟩, by
      dsimp only [blowUpMap, y]
      rw [add_sub_cancel_left, smul_smul]
      have h : (1 / r) * r = 1 := by field_simp [hr.ne']
      rw [h, one_smul]⟩
  · rintro ⟨y, ⟨hyball, hynotS⟩, rfl⟩
    have h_norm : ‖blowUpMap x r y‖ < R := by
      have h1 : ‖y - x‖ < r * R := by simpa [ball, dist_eq_norm] using hyball
      have h2 : ‖blowUpMap x r y‖ = (1 / r) * ‖y - x‖ := by
        simp [blowUpMap, norm_smul, abs_of_pos hr] <;> ring
      rw [h2]
      have h_pos : 0 < 1 / r := by positivity
      have h6 : (1 / r) * ‖y - x‖ < (1 / r) * (r * R) := mul_lt_mul_of_pos_left h1 h_pos
      have h7 : (1 / r) * (r * R) = R := by field_simp [hr.ne'] <;> ring
      rw [h7] at h6
      exact h6
    have hzball : blowUpMap x r y ∈ ball (0 : E n) R := by
      simpa [ball, dist_zero_right] using h_norm
    have hznot : blowUpMap x r y ∉ blowUp S x r := by
      intro h
      rcases h with ⟨y', hy'S, h_eq⟩
      have h_inj : y' = y := by
        simpa [blowUpMap, smul_smul, hr.ne'] using h_eq
      rw [h_inj] at hy'S
      exact hynotS hy'S
    exact ⟨hzball, hznot⟩

/-- Volume scaling for complement:
`volume((ball 0 R) \\ blowUp S x r) = r^{-n} · volume((ball x (rR)) \\ S)`. -/
lemma blow_up_compl_volume {S : Set (E n)} (hS : MeasurableSet S) {x : E n} {r R : ℝ}
    (hr : 0 < r) (hR : 0 ≤ R) :
    volume ((ball (0 : E n) R) \ blowUp S x r) =
      ENNReal.ofReal (r ^ n)⁻¹ * volume ((ball x (r * R)) \ S) := by
  let T := (ball x (r * R)) \ S
  have hT_meas : MeasurableSet T := isOpen_ball.measurableSet.diff hS
  have h_eq1 : (ball (0 : E n) R) \ blowUp S x r = blowUp T x r := by
    exact blowUp_compl_inter_ball hr hR
  rw [h_eq1]
  have h_eq2 : blowUp T x r ∩ ball (0 : E n) R = blowUp T x r := by
    ext z
    simp only [Set.mem_inter_iff]
    constructor
    · intro h; exact h.1
    · intro hz
      have hz' := hz
      rcases hz with ⟨y, hyT, rfl⟩
      have h2 : y ∈ ball x (r * R) := hyT.1
      have h3 : ‖blowUpMap x r y‖ < R := by
        have h4 : ‖y - x‖ < r * R := by simpa [ball, dist_eq_norm] using h2
        have h5 : ‖blowUpMap x r y‖ = (1 / r) * ‖y - x‖ := by
          simp [blowUpMap, norm_smul, abs_of_pos hr] <;> ring
        rw [h5]
        have h_pos : 0 < 1 / r := by positivity
        have h6 : (1 / r) * ‖y - x‖ < (1 / r) * (r * R) := mul_lt_mul_of_pos_left h4 h_pos
        have h7 : (1 / r) * (r * R) = R := by field_simp [hr.ne'] <;> ring
        rw [h7] at h6
        exact h6
      exact ⟨hz', by simpa [ball, dist_zero_right] using h3⟩
  have h_main : volume (blowUp T x r ∩ ball (0 : E n) R) =
      ENNReal.ofReal (r ^ n)⁻¹ * volume (T ∩ ball x (r * R)) :=
    blow_up_volume hT_meas hr hR
  have h_T_inter : T ∩ ball x (r * R) = T := by
    ext y; simp [T]; tauto
  have h_final : volume (blowUp T x r ∩ ball (0 : E n) R) =
      ENNReal.ofReal (r ^ n)⁻¹ * volume T := by
    rw [h_main, h_T_inter]
  have h_goal : volume (blowUp T x r) = ENNReal.ofReal (r ^ n)⁻¹ * volume T := by
    have h_eq3 : blowUp T x r = blowUp T x r ∩ ball (0 : E n) R := h_eq2.symm
    rw [h_eq3]
    exact h_final
  exact h_goal

/-- **Subsequence principle for convergence along `nhdsWithin 0 (Ioi 0)`**.

If every positive sequence `r_k → 0` has a subsequence along which `f(r_k) → l`,
then `f(r) → l` as `r → 0⁺`. -/
lemma tendsto_of_subsequence_principle {X : Type*} [TopologicalSpace X]
    {f : ℝ → X} {l : X} (h : ∀ (r_seq : ℕ → ℝ),
      (∀ k, 0 < r_seq k) → Tendsto r_seq atTop (nhds 0) →
      ∃ (subseq : ℕ → ℕ), StrictMono subseq ∧
        Tendsto (f ∘ (r_seq ∘ subseq)) atTop (nhds l)) :
    Tendsto f (nhdsWithin 0 (Set.Ioi 0)) (nhds l) := by
  have h_main : ∀ (ns : ℕ → ℝ), Tendsto ns atTop (nhdsWithin 0 (Set.Ioi 0)) →
      ∃ (ms : ℕ → ℕ), Tendsto (f ∘ (ns ∘ ms)) atTop (nhds l) := by
    intro ns hns
    have h1 : ∀ᶠ (k : ℕ) in Filter.atTop, 0 < ns k := by
      have h2 : Set.Ioi (0 : ℝ) ∈ nhdsWithin 0 (Set.Ioi 0) := self_mem_nhdsWithin
      exact hns h2
    rcases Filter.eventually_atTop.mp h1 with ⟨N, hN⟩
    let r_seq : ℕ → ℝ := fun k => ns (k + N)
    have hr_pos : ∀ k, 0 < r_seq k := by
      intro k; exact hN (k + N) (by linarith)
    have hr_tendsto : Tendsto r_seq atTop (nhds 0) := by
      have h3 : Tendsto ns atTop (nhds 0) := hns.mono_right nhdsWithin_le_nhds
      exact h3.comp (tendsto_add_atTop_nat N)
    rcases h r_seq hr_pos hr_tendsto with ⟨subseq, hsub_mono, hconv⟩
    let ms : ℕ → ℕ := fun k => subseq k + N
    have hms_mono : StrictMono ms := by
      intro i j h; simp [ms, hsub_mono h] <;> linarith
    have h_eq : f ∘ (ns ∘ ms) = f ∘ (r_seq ∘ subseq) := by
      funext k; simp [ms, r_seq] <;> rfl
    rw [h_eq] at *
    exact ⟨ms, hconv⟩
  haveI : (nhdsWithin 0 (Set.Ioi 0)).IsCountablyGenerated := by infer_instance
  exact Filter.tendsto_of_subseq_tendsto h_main

/-- **Blow-up density converges to 1/2** (conditional on explicit hypotheses). -/
theorem blowUp_density_half_of_data {S : Set (E n)} (hS : MeasurableSet S)
    (x : E n) (ν : E n) (hν_unit : ‖ν‖ = 1) (hn : 2 ≤ n)
    (h_vol_bound : ∀ (K : Set (E n)), IsCompact K →
      ∃ (C : ENNReal), ∀ (r : ℝ), 0 < r → r < 1 →
        volume (blowUp S x r ∩ K) ≤ C)
    (h_trans_bound : ∀ (K : Set (E n)), IsCompact K →
      ∃ (C : ℝ), ∀ (r : ℝ), 0 < r → r < 1 → ∀ (h : E n),
        volume (symmDiff (blowUp S x r) ((fun y => y + h) '' (blowUp S x r)) ∩ K) ≤
        ENNReal.ofReal (C * ‖h‖))
    (h_dir_vanish : ∀ (K : Set (E n)), IsCompact K → ∀ (w : E n), inner ℝ w ν = 0 →
      Tendsto (fun r : ℝ => Perimeter.directionalVariationIn (blowUp S x r) w K)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (h_nontrivial : ∃ (c : ℝ), 0 < c ∧ ∀ (r : ℝ), 0 < r → r < 1 →
      c * r ^ n ≤ (volume (S ∩ ball x r)).toReal ∧
      c * r ^ n ≤ (volume ((ball x r) \ S)).toReal)
    (h_orientation : ∀ (φ : E n → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∀ x, 0 ≤ φ x) → 0 < φ 0 →
        ∃ (r₀ : ℝ), 0 < r₀ ∧ ∀ (r : ℝ), 0 < r → r < r₀ →
          0 ≤ ∫ x in blowUp S x r, fderiv ℝ φ x ν) :
    Tendsto (fun r : ℝ => volume (blowUp S x r ∩ ball (0 : E n) 1))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (volume (ball (0 : E n) 1) / 2)) := by
  rcases h_nontrivial with ⟨c, hc_pos, hc⟩

  -- Lower bound for blow-up density at arbitrary radius R
  have h_blowup_bounds : ∀ (R : ℝ), 0 < R → ∀ (r : ℝ), 0 < r → r * R < 1 →
      ENNReal.ofReal (c * R ^ n) ≤ volume (blowUp S x r ∩ ball (0 : E n) R) ∧
      ENNReal.ofReal (c * R ^ n) ≤ volume ((ball (0 : E n) R) \ blowUp S x r) := by
    intro R hR r hr hrR
    have h9 := hc (r * R) (by positivity) hrR
    have h_pos_rn : 0 < r ^ n := pow_pos hr n
    have h_scale1 : volume (blowUp S x r ∩ ball (0 : E n) R) =
        ENNReal.ofReal (r ^ n)⁻¹ * volume (S ∩ ball x (r * R)) :=
      blow_up_volume hS hr (by linarith)
    have h_scale2 : volume ((ball (0 : E n) R) \ blowUp S x r) =
        ENNReal.ofReal (r ^ n)⁻¹ * volume ((ball x (r * R)) \ S) :=
      blow_up_compl_volume hS hr (by linarith)
    constructor
    · rw [h_scale1]
      have h10 : c * (r * R) ^ n ≤ (volume (S ∩ ball x (r * R))).toReal := by
        simpa [mul_pow] using h9.1
      have h_fin : volume (S ∩ ball x (r * R)) ≠ ⊤ :=
        ne_top_of_le_ne_top (measure_ball_lt_top.ne) (measure_mono (fun x hx => hx.2))
      have h12 : ENNReal.ofReal (c * (r * R) ^ n) ≤ volume (S ∩ ball x (r * R)) := by
        have h13 : ENNReal.ofReal (c * (r * R) ^ n) ≤ ENNReal.ofReal ((volume (S ∩ ball x (r * R))).toReal) :=
          ENNReal.ofReal_le_ofReal h10
        have h14 : ENNReal.ofReal ((volume (S ∩ ball x (r * R))).toReal) = volume (S ∩ ball x (r * R)) :=
          ENNReal.ofReal_toReal h_fin
        rw [h14] at h13
        exact h13
      have h_scale_eq : ENNReal.ofReal (r ^ n)⁻¹ * ENNReal.ofReal (c * (r * R) ^ n) =
          ENNReal.ofReal (c * R ^ n) := by
        have h15 : c * (r * R) ^ n = r ^ n * (c * R ^ n) := by simp [mul_pow] <;> ring
        rw [h15]
        have h16 : ENNReal.ofReal (r ^ n * (c * R ^ n)) =
            ENNReal.ofReal (r ^ n) * ENNReal.ofReal (c * R ^ n) := by
          rw [ENNReal.ofReal_mul] <;> positivity
        rw [h16]
        have h17 : ENNReal.ofReal (r ^ n) ≠ 0 := by positivity
        have h18 : ENNReal.ofReal (r ^ n) ≠ ⊤ := ENNReal.ofReal_ne_top
        have h_inv_eq : ENNReal.ofReal (r ^ n)⁻¹ = (ENNReal.ofReal (r ^ n))⁻¹ := by
          rw [ENNReal.ofReal_inv_of_pos (pow_pos hr n)]
        have h19 : ENNReal.ofReal (r ^ n)⁻¹ * ENNReal.ofReal (r ^ n) = 1 := by
          rw [h_inv_eq]
          exact ENNReal.inv_mul_cancel h17 h18
        rw [←mul_assoc, h19, one_mul]
      have h19 : ENNReal.ofReal (r ^ n)⁻¹ * ENNReal.ofReal (c * (r * R) ^ n) ≤
          ENNReal.ofReal (r ^ n)⁻¹ * volume (S ∩ ball x (r * R)) :=
        mul_le_mul_left' h12 _
      rw [h_scale_eq] at h19
      exact h19
    · rw [h_scale2]
      have h10 : c * (r * R) ^ n ≤ (volume ((ball x (r * R)) \ S)).toReal := by
        simpa [mul_pow] using h9.2
      have h_fin : volume ((ball x (r * R)) \ S) ≠ ⊤ :=
        ne_top_of_le_ne_top (measure_ball_lt_top.ne) (measure_mono (fun x hx => hx.1))
      have h12 : ENNReal.ofReal (c * (r * R) ^ n) ≤ volume ((ball x (r * R)) \ S) := by
        have h13 : ENNReal.ofReal (c * (r * R) ^ n) ≤ ENNReal.ofReal ((volume ((ball x (r * R)) \ S)).toReal) :=
          ENNReal.ofReal_le_ofReal h10
        have h14 : ENNReal.ofReal ((volume ((ball x (r * R)) \ S)).toReal) = volume ((ball x (r * R)) \ S) :=
          ENNReal.ofReal_toReal h_fin
        rw [h14] at h13
        exact h13
      have h_scale_eq : ENNReal.ofReal (r ^ n)⁻¹ * ENNReal.ofReal (c * (r * R) ^ n) =
          ENNReal.ofReal (c * R ^ n) := by
        have h15 : c * (r * R) ^ n = r ^ n * (c * R ^ n) := by simp [mul_pow] <;> ring
        rw [h15]
        have h16 : ENNReal.ofReal (r ^ n * (c * R ^ n)) =
            ENNReal.ofReal (r ^ n) * ENNReal.ofReal (c * R ^ n) := by
          rw [ENNReal.ofReal_mul] <;> positivity
        rw [h16]
        have h17 : ENNReal.ofReal (r ^ n) ≠ 0 := by positivity
        have h18 : ENNReal.ofReal (r ^ n) ≠ ⊤ := ENNReal.ofReal_ne_top
        have h_inv_eq : ENNReal.ofReal (r ^ n)⁻¹ = (ENNReal.ofReal (r ^ n))⁻¹ := by
          rw [ENNReal.ofReal_inv_of_pos (pow_pos hr n)]
        have h19 : ENNReal.ofReal (r ^ n)⁻¹ * ENNReal.ofReal (r ^ n) = 1 := by
          rw [h_inv_eq]
          exact ENNReal.inv_mul_cancel h17 h18
        rw [←mul_assoc, h19, one_mul]
      have h19 : ENNReal.ofReal (r ^ n)⁻¹ * ENNReal.ofReal (c * (r * R) ^ n) ≤
          ENNReal.ofReal (r ^ n)⁻¹ * volume ((ball x (r * R)) \ S) :=
        mul_le_mul_left' h12 _
      rw [h_scale_eq] at h19
      exact h19

  apply tendsto_of_subsequence_principle
  intro r_seq hr_pos hr_tendsto

  have h1 : ∀ᶠ k in atTop, r_seq k < 1 := hr_tendsto (Iio_mem_nhds (by norm_num))
  rcases Filter.eventually_atTop.mp h1 with ⟨N, hN⟩
  let E_seq : ℕ → Set (E n) := fun k => blowUp S x (r_seq (k + N))

  have h_meas_seq : ∀ k, MeasurableSet (E_seq k) := by
    intro k
    have hr_ne : r_seq (k + N) ≠ 0 := (hr_pos (k + N)).ne'
    let Φ : E n ≃ₜ E n :=
      { toFun := fun y => (r_seq (k + N))⁻¹ • (y - x)
        invFun := fun z => x + (r_seq (k + N)) • z
        left_inv := fun y => by simp [smul_smul, hr_ne] <;> abel
        right_inv := fun z => by simp [smul_smul, hr_ne] <;> abel
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
    have h_eq : Φ '' S = blowUp S x (r_seq (k + N)) := by
      ext z; simp [blowUp, blowUpMap, Φ]
    have h_E_seq : E_seq k = Φ '' S := by
      simp [E_seq, h_eq]
    rw [h_E_seq]
    exact Φ.measurableEmbedding.measurableSet_image.mpr hS

  have h_vol_seq : ∀ (K : Set (E n)), IsCompact K →
      ∃ (C : ENNReal), ∀ k, volume (E_seq k ∩ K) ≤ C := by
    intro K hK
    rcases h_vol_bound K hK with ⟨C, hC⟩
    refine ⟨C, fun k => hC (r_seq (k + N)) (hr_pos (k + N)) (hN (k + N) (by linarith))⟩

  have h_trans_seq : ∀ (K : Set (E n)), IsCompact K →
      ∃ (C : ℝ), ∀ k, ∀ (h : E n),
        volume (symmDiff (E_seq k) ((fun y => y + h) '' (E_seq k)) ∩ K) ≤
        ENNReal.ofReal (C * ‖h‖) := by
    intro K hK
    rcases h_trans_bound K hK with ⟨C, hC⟩
    refine ⟨C, fun k h => hC (r_seq (k + N)) (hr_pos (k + N)) (hN (k + N) (by linarith)) h⟩

  rcases bv_compactness_sequence_of_translation h_meas_seq h_vol_seq h_trans_seq with
    ⟨(F : Set (E n)), subseq', hsub_strict, hF_meas, h_conv⟩
  let subseq : ℕ → ℕ := fun k => subseq' k + N
  have hsub_strict' : StrictMono subseq := by
    intro a b hab
    have h : subseq' a < subseq' b := hsub_strict hab
    dsimp only [subseq]; exact add_lt_add_left h N
  have h_conv' : ∀ (K : Set (E n)), IsCompact K →
      Tendsto (fun k => volume (symmDiff (blowUp S x (r_seq (subseq k))) F ∩ K))
        atTop (nhds 0) := by
    intro K hK
    have h_final := h_conv K hK
    have h_func : (fun k : ℕ => volume (symmDiff (blowUp S x (r_seq (subseq k))) F ∩ K)) =
        (fun k : ℕ => volume (symmDiff (E_seq (subseq' k)) F ∩ K)) := by
      funext k
      have h1 : E_seq (subseq' k) = blowUp S x (r_seq (subseq k)) := by
        simp [E_seq, subseq] <;> rfl
      rw [h1]
    rwa [h_func]

  -- Sphere has measure zero
  have h_sphere_null : ∀ (x₀ : E n) (R : ℝ), R ≠ 0 → volume (sphere x₀ R) = 0 :=
    fun x₀ R hR => volume_sphere_eq_zero x₀ hR
  -- Transfer lower bounds to limit F for arbitrary R (using closedBall for compactness)
  have h_F_bounds : ∀ (R : ℝ), 0 < R →
      ENNReal.ofReal (c * R ^ n) ≤ volume (F ∩ closedBall (0 : E n) R) ∧
      ENNReal.ofReal (c * R ^ n) ≤ volume ((closedBall (0 : E n) R) \ F) := by
    intro R hR
    have hR1 : 0 ≤ R := by linarith
    have h_small : ∀ᶠ k in atTop, r_seq (subseq k) * R < 1 := by
      have h_tend : Tendsto (fun k => r_seq (subseq k)) atTop (nhds 0) :=
        hr_tendsto.comp hsub_strict'.tendsto_atTop
      have h : Tendsto (fun k => r_seq (subseq k) * R) atTop (nhds 0) := by
        simpa [mul_comm] using h_tend.const_mul R
      exact h (Iio_mem_nhds (by norm_num))
    let K_ball : Set (E n) := closedBall (0 : E n) R
    have hK_compact : IsCompact K_ball := isCompact_closedBall _ _
    have h_ball_ae : K_ball =ᵐ[volume] ball (0 : E n) R := by
      have h_sphere : volume (sphere (0 : E n) R) = 0 := h_sphere_null 0 R hR.ne'
      have h1 : (K_ball \ ball (0 : E n) R) = sphere (0 : E n) R := by
        ext z; simp [K_ball, mem_closedBall, mem_ball, mem_sphere, dist_zero_right]
        <;> constructor <;> intro h <;> linarith
      have h2 : (ball (0 : E n) R \ K_ball) = ∅ := by
        rw [Set.diff_eq_empty] <;> exact ball_subset_closedBall
      have h3 : volume (K_ball \ ball (0 : E n) R) = 0 := by rw [h1, h_sphere]
      have h4 : volume ((ball (0 : E n) R) \ K_ball) = 0 := by rw [h2] <;> simp
      have h5 : ∀ᵐ (x : E n) ∂volume, x ∉ (K_ball \ ball (0 : E n) R) :=
        MeasureTheory.measure_eq_zero_iff_ae_notMem.mp h3
      have h6 : ∀ᵐ (x : E n) ∂volume, x ∉ ((ball (0 : E n) R) \ K_ball) :=
        MeasureTheory.measure_eq_zero_iff_ae_notMem.mp h4
      filter_upwards [h5, h6] with y hy5 hy6
      have h_iff : y ∈ K_ball ↔ y ∈ ball (0 : E n) R := by
        constructor
        · intro hK
          by_cases hB : y ∈ ball (0 : E n) R
          · exact hB
          · exact False.elim (hy5 ⟨hK, hB⟩)
        · intro hB
          by_cases hK : y ∈ K_ball
          · exact hK
          · exact False.elim (hy6 ⟨hB, hK⟩)
      exact propext h_iff
    have h_eq_inter : ∀ (A : Set (E n)), MeasurableSet A →
        volume (A ∩ K_ball) = volume (A ∩ ball (0 : E n) R) := by
      intro A hA
      have h : (A ∩ K_ball : Set (E n)) =ᵐ[volume] (A ∩ ball (0 : E n) R : Set (E n)) := by
        filter_upwards [h_ball_ae] with y hy
        have h_iff : y ∈ K_ball ↔ y ∈ ball (0 : E n) R := by exact Iff.of_eq hy
        exact propext ⟨fun h => ⟨h.1, h_iff.mp h.2⟩, fun h => ⟨h.1, h_iff.mpr h.2⟩⟩
      exact measure_congr h
    have h_eq_compl : ∀ (A : Set (E n)), MeasurableSet A →
        volume (K_ball \ A) = volume ((ball (0 : E n) R) \ A) := by
      intro A hA
      have h : (K_ball \ A : Set (E n)) =ᵐ[volume] ((ball (0 : E n) R) \ A : Set (E n)) := by
        filter_upwards [h_ball_ae] with y hy
        have h_iff : y ∈ K_ball ↔ y ∈ ball (0 : E n) R := by exact Iff.of_eq hy
        exact propext ⟨fun h => ⟨h_iff.mp h.1, h.2⟩, fun h => ⟨h_iff.mpr h.1, h.2⟩⟩
      exact measure_congr h
    have h_conv_vol : Tendsto (fun k => volume (blowUp S x (r_seq (subseq k)) ∩ K_ball))
        atTop (nhds (volume (F ∩ K_ball))) :=
      tendsto_volume_inter_of_symmDiff hK_compact (h_conv' K_ball hK_compact)
    have h_conv_compl : Tendsto (fun k => volume (K_ball \ blowUp S x (r_seq (subseq k))))
        atTop (nhds (volume (K_ball \ F))) :=
      tendsto_volume_compl_of_symmDiff hK_compact (h_conv' K_ball hK_compact)
    have h6 : ∀ᶠ k in atTop, ENNReal.ofReal (c * R ^ n) ≤
        volume (blowUp S x (r_seq (subseq k)) ∩ K_ball) := by
      filter_upwards [h_small] with k hk
      have h9 := (h_blowup_bounds R hR (r_seq (subseq k)) (hr_pos (subseq k)) hk).1
      rw [h_eq_inter (blowUp S x (r_seq (subseq k))) (h_meas_seq (subseq' k))]
      exact h9
    have h7 : ∀ᶠ k in atTop, ENNReal.ofReal (c * R ^ n) ≤
        volume (K_ball \ blowUp S x (r_seq (subseq k))) := by
      filter_upwards [h_small] with k hk
      have h9 := (h_blowup_bounds R hR (r_seq (subseq k)) (hr_pos (subseq k)) hk).2
      rw [h_eq_compl (blowUp S x (r_seq (subseq k))) (h_meas_seq (subseq' k))]
      exact h9
    have h_const_tendsto : Tendsto (fun _ : ℕ => ENNReal.ofReal (c * R ^ n)) atTop (nhds (ENNReal.ofReal (c * R ^ n))) :=
      tendsto_const_nhds
    have h_result1 : ENNReal.ofReal (c * R ^ n) ≤ volume (F ∩ K_ball) :=
      le_of_tendsto_of_tendsto h_const_tendsto h_conv_vol h6
    have h_result2 : ENNReal.ofReal (c * R ^ n) ≤ volume (K_ball \ F) :=
      le_of_tendsto_of_tendsto h_const_tendsto h_conv_compl h7
    exact ⟨h_result1, h_result2⟩

  -- Zero directional variation for limit
  have h_zero_dv : ∀ (w : E n), inner ℝ w ν = 0 →
      Perimeter.directionalVariation F w = 0 := by
    intro w hw
    have h_local_zero : ∀ (K : Set (E n)), IsCompact K →
        Perimeter.directionalVariationIn F w K = 0 := by
      intro K hK
      have h_lsc : Perimeter.directionalVariationIn F w K ≤
          Filter.liminf (fun k => Perimeter.directionalVariationIn
            (blowUp S x (r_seq (subseq k))) w K) Filter.atTop :=
        Perimeter.directionalVariationIn_lowerSemicontinuity hF_meas
          (fun k => h_meas_seq (subseq' k)) h_conv' w K
      have h_eventually : ∀ᶠ k in atTop, r_seq (subseq k) ∈ Set.Ioi 0 := by
        filter_upwards with k; exact hr_pos (subseq k)
      have h2 : Tendsto (fun k => r_seq (subseq k)) atTop (Filter.principal (Set.Ioi 0)) := by
        simpa [Filter.tendsto_principal] using h_eventually
      have h3 : Tendsto (fun k => r_seq (subseq k)) atTop (nhdsWithin 0 (Set.Ioi 0)) := by
        have h4 : Tendsto (fun k => r_seq (subseq k)) atTop (nhds 0) :=
          hr_tendsto.comp hsub_strict'.tendsto_atTop
        simpa [nhdsWithin] using Filter.tendsto_inf.mpr ⟨h4, h2⟩
      have h_tendsto : Tendsto (fun k => Perimeter.directionalVariationIn
            (blowUp S x (r_seq (subseq k))) w K) atTop (nhds 0) :=
        (h_dir_vanish K hK w hw).comp h3
      have h_liminf_zero : Filter.liminf (fun k => Perimeter.directionalVariationIn
          (blowUp S x (r_seq (subseq k))) w K) Filter.atTop = 0 :=
        h_tendsto.liminf_eq
      rw [h_liminf_zero] at h_lsc
      simpa using h_lsc
    exact Perimeter.directionalVariationIn_all_compact_zero hF_meas w h_local_zero

  -- Translation invariance
  have h_transl : ∀ (w : E n), inner ℝ w ν = 0 →
      ∀ (t : ℝ), Perimeter.translateSet F (t • w) =ᵐ[volume] F := by
    intro w hw t
    exact Perimeter.zero_directionalVariation_translation_invariant hF_meas (h_zero_dv w hw) t

  -- Orientation inheritance (weak: only φ 0 > 0)
  have h_orientation_F_weak : ∀ (φ : E n → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∀ x, 0 ≤ φ x) → 0 < φ 0 → 0 ≤ ∫ x in F, fderiv ℝ φ x ν := by
    intro φ hφ hsupp φ_nonneg hφ0
    rcases h_orientation φ hφ hsupp φ_nonneg hφ0 with ⟨r₀, hr₀_pos, h_or⟩
    let ψ : E n → ℝ := fun x => fderiv ℝ φ x ν
    have hψ_cont : Continuous ψ := by
      have h1 : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by norm_num)
      fun_prop
    have hψ_supp : HasCompactSupport ψ := by
      have h1 : Function.support ψ ⊆ closure (Function.support φ) := by
        intro x hx
        by_contra h2
        have h3 : φ =ᶠ[nhds x] 0 := by
          have h4 : IsOpen (closure (Function.support φ))ᶜ := isClosed_closure.isOpen_compl
          exact Filter.eventually_of_mem (IsOpen.mem_nhds h4 h2)
            (fun y hy => by simpa [Function.mem_support] using fun h => hy (subset_closure h))
        have h41 : HasFDerivAt (fun (_ : E n) => (0 : ℝ)) (0 : (E n) →L[ℝ] ℝ) x :=
          hasFDerivAt_const (c := (0 : ℝ)) (x := x)
        have h42 : HasFDerivAt φ (0 : (E n) →L[ℝ] ℝ) x := h41.congr_of_eventuallyEq h3
        have h4 : fderiv ℝ φ x = 0 := h42.fderiv
        have h5 : ψ x = 0 := by
          simpa [ψ] using congr_arg (fun (f : (E n) →L[ℝ] ℝ) => f ν) h4
        exact hx h5
      have h2 : closure (Function.support ψ) ⊆ closure (Function.support φ) :=
        closure_minimal h1 isClosed_closure
      have h3 : IsCompact (closure (Function.support φ)) := hsupp
      exact h3.of_isClosed_subset isClosed_closure h2
    let K : Set (E n) := tsupport ψ
    have hK : IsCompact K := hψ_supp
    have h_bdd : ∃ (C : ℝ), 0 ≤ C ∧ ∀ x, |ψ x| ≤ C := by
      have h4 : BddAbove (Set.image (fun x => |ψ x|) K) :=
        hK.bddAbove_image ((continuous_abs.comp hψ_cont).continuousOn)
      rcases h4 with ⟨C0, hC0⟩
      let C := max C0 0
      have hC_nonneg : 0 ≤ C := by positivity
      have hC_on_K : ∀ x ∈ K, |ψ x| ≤ C := by
        intro x hx
        have h5 : |ψ x| ∈ Set.image (fun x => |ψ x|) K := ⟨x, hx, rfl⟩
        have h6 : |ψ x| ≤ C0 := hC0 h5
        exact le_trans h6 (le_max_left _ _)
      refine ⟨C, hC_nonneg, fun x => ?_⟩
      by_cases hx : x ∈ K
      · exact hC_on_K x hx
      · have h7 : ψ x = 0 := by
          have h8 : x ∉ Function.support ψ := fun h9 => hx (subset_closure h9)
          simpa [Function.mem_support] using h8
        rw [h7] <;> simp [hC_nonneg]
    rcases h_bdd with ⟨C, C_nonneg, hC⟩
    have hψ_int : Integrable ψ volume := hψ_cont.integrable_of_hasCompactSupport hψ_supp
    have h_conv_tsupport : Tendsto (fun k => volume (symmDiff F (blowUp S x (r_seq (subseq k))) ∩ tsupport ψ)) atTop (nhds 0) := by
      have h_eq : (fun k => volume (symmDiff F (blowUp S x (r_seq (subseq k))) ∩ tsupport ψ)) =
          (fun k => volume (symmDiff (blowUp S x (r_seq (subseq k))) F ∩ tsupport ψ)) := by
        funext k
        have h_comm : symmDiff F (blowUp S x (r_seq (subseq k))) =
            symmDiff (blowUp S x (r_seq (subseq k))) F := by
          ext y; simp [symmDiff, Set.mem_union, Set.mem_diff] <;> tauto
        rw [h_comm]
      rw [h_eq]
      exact h_conv' (tsupport ψ) hψ_supp
    have h_integral_conv : Tendsto (fun k => ∫ x in blowUp S x (r_seq (subseq k)), ψ x)
        atTop (nhds (∫ x in F, ψ x)) :=
      Perimeter.integral_set_convergence hψ_cont hψ_supp hF_meas
        (fun k => h_meas_seq (subseq' k))
        h_conv_tsupport
    have h5 : ∀ᶠ k in atTop, r_seq (subseq k) < r₀ := by
      have h6 : Tendsto (fun k => r_seq (subseq k)) atTop (nhds 0) :=
        hr_tendsto.comp hsub_strict'.tendsto_atTop
      exact h6 (Iio_mem_nhds hr₀_pos)
    have h7 : ∀ᶠ k in atTop, 0 ≤ ∫ x in blowUp S x (r_seq (subseq k)), ψ x := by
      filter_upwards [h5] with k hk
      have h8 : 0 < r_seq (subseq k) := hr_pos (subseq k)
      exact h_or (r_seq (subseq k)) h8 hk
    have h_zero_tendsto : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds (0 : ℝ)) := tendsto_const_nhds
    exact le_of_tendsto_of_tendsto h_zero_tendsto h_integral_conv h7

  -- Bridge weak orientation to strong orientation for F
  have h_orientation_F : ∀ (φ : E n → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∀ x, 0 ≤ φ x) → 0 ≤ ∫ x in F, fderiv ℝ φ x ν :=
    orientation_weak_to_strong hF_meas h_orientation_F_weak

  -- Half-space characterization
  have h_hn_pos : 0 < n := by linarith
  rcases Perimeter.orientation_to_monotone_factorization hF_meas hν_unit h_transl h_orientation_F with
    ⟨g, hg_meas, hg_values, hg_decr, h_factor⟩
  have h_hs := Perimeter.halfSpace_characterization hF_meas hν_unit g hg_meas hg_values hg_decr h_factor

  rcases h_hs with (h_half | h_empty | h_full)
  · -- Case: half-space {inner y ν < α}
    rcases h_half with ⟨α, h_ae⟩

    -- α = 0 from two-sided bounds at all radii
    have hα_eq_zero : α = 0 := by
      by_cases hα_pos : 0 < α
      · -- α > 0: choose R < α, then ball 0 R ⊆ half-space, complement = 0
        let R := α / 2
        have hR_pos : 0 < R := by positivity
        have hR_lt : R < α := by
          dsimp only [R]
          linarith
        have h_ball_subset : closedBall (0 : E n) R ⊆ {y | inner ℝ y ν < α} := by
          intro y hy
          have h_dist : ‖y‖ ≤ R := by simpa [closedBall, dist_zero_right] using hy
          have h_cs : |inner ℝ y ν| ≤ ‖y‖ * ‖ν‖ := abs_real_inner_le_norm y ν
          have h_inner : inner ℝ y ν ≤ ‖y‖ := by
            have h1 : inner ℝ y ν ≤ |inner ℝ y ν| := le_abs_self (inner ℝ y ν)
            rw [hν_unit] at h_cs
            linarith
          have h9 : inner ℝ y ν < α := by linarith
          exact h9
        have h10 : (closedBall (0 : E n) R) \ F =ᵐ[volume] (∅ : Set (E n)) := by
          filter_upwards [h_ae] with y hy
          have h14 : y ∉ (closedBall (0 : E n) R) \ F := by
            intro h1
            have h12 : inner ℝ y ν < α := h_ball_subset h1.1
            have h13 : y ∈ F := hy.mpr h12
            exact h1.2 h13
          exact propext ⟨h14, fun h => False.elim h⟩
        have h14 : volume ((closedBall (0 : E n) R) \ F) = 0 := by
          have h_eq : volume ((closedBall (0 : E n) R) \ F) = volume (∅ : Set (E n)) := measure_congr h10
          have h_empty : volume (∅ : Set (E n)) = 0 := by simp
          exact h_eq.trans h_empty
        have h15 := (h_F_bounds R hR_pos).2
        rw [h14] at h15
        have h16 : (0 : ENNReal) < ENNReal.ofReal (c * R ^ n) := by
          apply ENNReal.ofReal_pos.mpr
          have h17 : 0 < c := hc_pos
          have h18 : 0 < R ^ n := by positivity
          positivity
        have h17 : ENNReal.ofReal (c * R ^ n) = 0 := le_zero_iff.mp h15
        exact False.elim (h16.ne' h17)
      · -- ¬(0 < α)
        by_cases hα_neg : α < 0
        · -- α < 0: choose R < |α|, then ball 0 R is disjoint from half-space
          let R := (-α) / 2
          have hR_pos : 0 < R := by
            dsimp only [R]
            linarith
          have h_ball_disjoint : Disjoint (closedBall (0 : E n) R) {y | inner ℝ y ν < α} := by
            rw [Set.disjoint_left]
            intro y h1 h2
            have h_dist : ‖y‖ ≤ R := by simpa [closedBall, dist_zero_right] using h1
            have h_cs : |inner ℝ y ν| ≤ ‖y‖ * ‖ν‖ := abs_real_inner_le_norm y ν
            have h_inner_lower : -‖y‖ ≤ inner ℝ y ν := by
              have h_abs : -|inner ℝ y ν| ≤ inner ℝ y ν := by
                exact (abs_le.mp (show |inner ℝ y ν| ≤ |inner ℝ y ν| from le_refl _)).1
              rw [hν_unit] at h_cs
              linarith
            have h9 : inner ℝ y ν > α := by
              have hR_def : R = (-α) / 2 := by rfl
              have h_dist2 : ‖y‖ ≤ (-α) / 2 := by
                rw [hR_def] at h_dist
                exact h_dist
              have h1 : -((-α) / 2) ≤ -‖y‖ := neg_le_neg h_dist2
              have h2 : -((-α) / 2) = α / 2 := by ring
              have h3 : α / 2 ≤ -‖y‖ := by
                rw [←h2]
                exact h1
              have h4 : α / 2 ≤ inner ℝ y ν := by
                calc α / 2 ≤ -‖y‖ := h3
                  _ ≤ inner ℝ y ν := h_inner_lower
              have h5 : α < 0 := hα_neg
              have h6 : α / 2 > α := by
                have h7 : α / 2 - α = -α / 2 := by ring
                have h8 : -α / 2 > 0 := by linarith
                linarith
              exact lt_of_lt_of_le h6 h4
            have h_contra : False := by
              exact lt_asymm h2 h9
            exact h_contra
          have h10 : (F ∩ closedBall (0 : E n) R : Set (E n)) =ᵐ[volume] (∅ : Set (E n)) := by
            filter_upwards [h_ae] with y hy
            have h14 : y ∉ (F ∩ closedBall (0 : E n) R : Set (E n)) := by
              intro h1
              have h11 : y ∈ F := h1.1
              have h12 : inner ℝ y ν < α := hy.mp h11
              have h13 : y ∈ closedBall (0 : E n) R := h1.2
              exact Set.disjoint_left.mp h_ball_disjoint h13 h12
            exact propext ⟨h14, fun h => False.elim h⟩
          have h14 : volume (F ∩ closedBall (0 : E n) R) = 0 := by
            simpa using measure_congr h10
          have h15 := (h_F_bounds R hR_pos).1
          rw [h14] at h15
          have h16 : (0 : ENNReal) < ENNReal.ofReal (c * R ^ n) := by
            apply ENNReal.ofReal_pos.mpr
            have h17 : 0 < c := hc_pos
            have h18 : 0 < R ^ n := by positivity
            positivity
          have h17 : ENNReal.ofReal (c * R ^ n) = 0 := le_zero_iff.mp h15
          exact False.elim (h16.ne' h17)
        · -- ¬(α < 0), together with ¬(0 < α), gives α = 0
          have h1 : ¬(0 < α) := hα_pos
          have h2 : ¬(α < 0) := hα_neg
          linarith

    have hF_half : F =ᵐ[volume] {y | inner ℝ y ν < 0} := by
      filter_upwards [h_ae] with y hy
      have h_iff : y ∈ F ↔ inner ℝ y ν < 0 := by
        simpa [hα_eq_zero] using hy
      exact propext h_iff

    let K1 : Set (E n) := closedBall (0 : E n) 1
    let S0 : Set (E n) := {y | inner ℝ y ν < 0}
    let F_set : Set (E n) := F
    have hK1_compact : IsCompact K1 := isCompact_closedBall _ _
    have hK1_ball_ae : K1 =ᵐ[volume] ball (0 : E n) 1 := by
      have h_sphere : volume (sphere (0 : E n) 1) = 0 := h_sphere_null 0 1 (by norm_num)
      have h1 : (K1 \ ball (0 : E n) 1) = sphere (0 : E n) 1 := by
        ext z; simp [K1, mem_closedBall, mem_ball, mem_sphere, dist_zero_right]
        <;> constructor <;> intro h <;> linarith
      have h2 : (ball (0 : E n) 1 \ K1) = ∅ := by
        rw [Set.diff_eq_empty] <;> exact ball_subset_closedBall
      have h3 : volume (K1 \ ball (0 : E n) 1) = 0 := by rw [h1, h_sphere]
      have h4 : volume ((ball (0 : E n) 1) \ K1) = 0 := by rw [h2] <;> simp
      have h5 : ∀ᵐ (x : E n) ∂volume, x ∉ (K1 \ ball (0 : E n) 1) :=
        MeasureTheory.measure_eq_zero_iff_ae_notMem.mp h3
      have h6 : ∀ᵐ (x : E n) ∂volume, x ∉ ((ball (0 : E n) 1) \ K1) :=
        MeasureTheory.measure_eq_zero_iff_ae_notMem.mp h4
      filter_upwards [h5, h6] with y hy5 hy6
      have h_iff : y ∈ K1 ↔ y ∈ ball (0 : E n) 1 := by
        constructor
        · intro hK; by_cases hB : y ∈ ball (0 : E n) 1; exact hB; exact False.elim (hy5 ⟨hK, hB⟩)
        · intro hB; by_cases hK : y ∈ K1; exact hK; exact False.elim (hy6 ⟨hB, hK⟩)
      exact propext h_iff
    have hK1_vol_eq : volume K1 = volume (ball (0 : E n) 1) :=
      measure_congr hK1_ball_ae

    have h_half_vol : volume (S0 ∩ K1) =
        volume K1 / 2 := by
      have h1 : (S0 ∩ K1 : Set (E n)) =ᵐ[volume] (S0 ∩ ball (0 : E n) 1 : Set (E n)) := by
        filter_upwards [hK1_ball_ae] with y hy
        have h_iff : y ∈ K1 ↔ y ∈ ball (0 : E n) 1 := Iff.of_eq hy
        exact propext ⟨fun h => ⟨h.1, h_iff.mp h.2⟩, fun h => ⟨h.1, h_iff.mpr h.2⟩⟩
      rw [measure_congr h1, halfspace_volume_at_zero hν_unit, hK1_vol_eq]
    have h_eq_inter1 : ∀ (A : Set (E n)), MeasurableSet A →
        volume (A ∩ K1) = volume (A ∩ ball (0 : E n) 1) := by
      intro A hA
      have h : (A ∩ K1 : Set (E n)) =ᵐ[volume] (A ∩ ball (0 : E n) 1 : Set (E n)) := by
        filter_upwards [hK1_ball_ae] with y hy
        have h_iff : y ∈ K1 ↔ y ∈ ball (0 : E n) 1 := Iff.of_eq hy
        exact propext ⟨fun h => ⟨h.1, h_iff.mp h.2⟩, fun h => ⟨h.1, h_iff.mpr h.2⟩⟩
      exact measure_congr h
    have h_conv_vol : Tendsto (fun k => volume (blowUp S x (r_seq (subseq k)) ∩ K1))
        atTop (nhds (volume (F_set ∩ K1))) :=
      tendsto_volume_inter_of_symmDiff hK1_compact (h_conv' K1 hK1_compact)

    have hF_vol : volume (F_set ∩ K1) = volume (ball (0 : E n) 1) / 2 := by
      have h1 : (F_set ∩ K1 : Set (E n)) =ᵐ[volume] (S0 ∩ K1 : Set (E n)) := by
        filter_upwards [hF_half] with y hy
        have h_iff : y ∈ F ↔ y ∈ S0 := Iff.of_eq hy
        exact propext ⟨fun h => ⟨h_iff.mp h.1, h.2⟩, fun h => ⟨h_iff.mpr h.1, h.2⟩⟩
      have h2 : volume (F_set ∩ K1) = volume (S0 ∩ K1) :=
        measure_congr h1
      rw [h2, h_half_vol, hK1_vol_eq]

    have h_conv_ball : Tendsto (fun k => volume (blowUp S x (r_seq (subseq k)) ∩ ball (0 : E n) 1))
        atTop (nhds (volume (ball (0 : E n) 1) / 2)) := by
      have h3 : (fun k => volume (blowUp S x (r_seq (subseq k)) ∩ ball (0 : E n) 1)) =
          fun k => volume (blowUp S x (r_seq (subseq k)) ∩ K1) := by
        funext k
        exact (h_eq_inter1 (blowUp S x (r_seq (subseq k))) (h_meas_seq (subseq' k))).symm
      rw [h3]
      rw [hF_vol] at h_conv_vol
      exact h_conv_vol
    exact ⟨subseq, hsub_strict', h_conv_ball⟩

  · -- Case: F empty a.e.
    have h_F_lower := (h_F_bounds 1 (by norm_num)).1
    have h1 : (F ∩ closedBall (0 : E n) 1 : Set (E n)) =ᵐ[volume] (∅ : Set (E n)) := by
      filter_upwards [h_empty] with y hy
      have h14 : y ∉ (F ∩ closedBall (0 : E n) 1 : Set (E n)) := by
        intro h
        exact hy h.1
      exact propext ⟨h14, fun h => False.elim h⟩
    have h_F_empty : volume (F ∩ closedBall (0 : E n) 1) = 0 := by
      have h_eq : volume (F ∩ closedBall (0 : E n) 1) = volume (∅ : Set (E n)) := measure_congr h1
      have h_empty : volume (∅ : Set (E n)) = 0 := by simp
      exact h_eq.trans h_empty
    rw [h_F_empty] at h_F_lower
    have h16 : (0 : ENNReal) < ENNReal.ofReal (c * (1 : ℝ) ^ n) := by
      apply ENNReal.ofReal_pos.mpr; simpa using hc_pos
    have h17 : ENNReal.ofReal (c * (1 : ℝ) ^ n) = 0 := le_zero_iff.mp h_F_lower
    exact False.elim (h16.ne' h17)

  · -- Case: F full a.e.
    have h_F_compl_lower := (h_F_bounds 1 (by norm_num)).2
    have h1 : (closedBall (0 : E n) 1) \ F =ᵐ[volume] (∅ : Set (E n)) := by
      filter_upwards [h_full] with y hy
      have h14 : y ∉ (closedBall (0 : E n) 1) \ F := by
        intro h
        exact h.2 hy
      exact propext ⟨h14, fun h => False.elim h⟩
    have h_F_full : volume ((closedBall (0 : E n) 1) \ F) = 0 := by
      have h_eq : volume ((closedBall (0 : E n) 1) \ F) = volume (∅ : Set (E n)) := measure_congr h1
      have h_empty : volume (∅ : Set (E n)) = 0 := by simp
      exact h_eq.trans h_empty
    rw [h_F_full] at h_F_compl_lower
    have h16 : (0 : ENNReal) < ENNReal.ofReal (c * (1 : ℝ) ^ n) := by
      apply ENNReal.ofReal_pos.mpr; simpa using hc_pos
    have h17 : ENNReal.ofReal (c * (1 : ℝ) ^ n) = 0 := le_zero_iff.mp h_F_compl_lower
    exact False.elim (h16.ne' h17)

end Geometry.StructureTheorem
