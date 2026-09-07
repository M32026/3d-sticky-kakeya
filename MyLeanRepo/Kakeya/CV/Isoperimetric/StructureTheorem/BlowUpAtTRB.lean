import MyLeanRepo.Kakeya.CV.Isoperimetric.InnerMinkowski.Basic
import MyLeanRepo.Kakeya.CV.Isoperimetric.Perimeter.BVCompactnessTranslation.SequenceCompactness
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.BlowUpScaling
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.DirectionalVariationBlowUp
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.HalfSpaceCharacterization
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.TrueReducedBoundary
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.ReducedBoundaryData
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.DensityEstimates
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.OrientationFromComparability
import MyLeanRepo.Kakeya.CV.Isoperimetric.StructureTheorem.BlowUpTranslationBound
import Mathlib.Tactic

/-!
# Blow-Up Convergence at True Reduced Boundary Points

Phase A of the lower perimeter density proof.

Proves that at a true reduced boundary point (with upper density, Lebesgue
differentiation, and two-sided positive density), every sequence of blow-ups
has a subsequence converging in L¹_loc to some half-space `{y | inner(y, ν) < α}`.

## Proof route

1. Upper density → uniform perimeter bound on blow-ups → volume + translation bounds.
2. BV compactness → subsequential L¹_loc limit F.
3. `directionalVariation_blowUp_vanishing` + lower semicontinuity → directional
   variation of F is zero perpendicular to ν.
4. Translation invariance of F perpendicular to ν.
5. Orientation condition for F (from scalar comparability + Gauss-Green).
6. Monotone factorization → `halfSpace_characterization` → F is half-space,
   empty, or full.
7. Two-sided positive density rules out empty/full → F is a half-space.

## Supporting estimates

- Translation bound for blow-ups from upper density.
- Orientation condition for blow-up limit from scalar comparability.

## References

- Maggi, *Sets of Finite Perimeter*, Theorem 15.5
- Ambrosio-Fusco-Pallara, *Functions of BV*, Theorem 3.59
-/


open MeasureTheory Metric Set ENNReal Filter
open scoped MeasureTheory ContDiff

namespace Geometry.StructureTheorem

open Perimeter

variable {n : ℕ}


/-- **Subsequential blow-up limit is a half-space at a TRB point**. -/
theorem blowup_subsequential_halfspace_at_trb
    {U : Set (E n)} (hU : IsOpen U) (hU_reg : U = interior (closure U))
    (hBdd : Bornology.IsBounded U) (h_perim_finite : perimeter U < ⊤) (hn : 2 ≤ n)
    (x : E n) (ν : E n) (hx_trb : x ∈ trueReducedBoundary U)
    (hν : measureTheoreticNormal U x = ν)
    (hν_unit : ‖ν‖ = 1)
    (h_upper : ∃ (C : ℝ) (r0 : ℝ), 0 < C ∧ 0 < r0 ∧
        ∀ r, 0 < r → r < r0 →
          perimeterMeasure U (closedBall x r) ≤ ENNReal.ofReal (C * r ^ (n - 1)))
    (h_abs_lebesgue : ∀ (w : E n), inner ℝ w ν = 0 →
        Tendsto (fun r : ℝ =>
          (∫ y in closedBall x r, |inner ℝ w (measureTheoreticNormal U y)| ∂(perimeterMeasure U)) /
            (perimeterMeasure U (closedBall x r)).toReal)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0))
    (h_inner_lebesgue : Tendsto (fun r : ℝ =>
        (∫ y in closedBall x r, inner ℝ ν (measureTheoreticNormal U y) ∂(perimeterMeasure U)) /
          (perimeterMeasure U (closedBall x r)).toReal)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 1))
    (h_nontrivial : ∃ (c : ℝ) (R : ℝ), 0 < c ∧ 0 < R ∧
        ∀ r, 0 < r → r < R →
          volume (U ∩ ball x r) ≥ ENNReal.ofReal (c * r ^ n) ∧
          volume ((ball x r) \ U) ≥ ENNReal.ofReal (c * r ^ n))
    (r_seq : ℕ → ℝ) (hr_pos : ∀ k, 0 < r_seq k)
    (hr_tendsto : Tendsto r_seq atTop (nhds 0)) :
    ∃ (F : Set (E n)) (subseq : ℕ → ℕ) (α : ℝ),
      StrictMono subseq ∧
      MeasurableSet F ∧
      (∀ K, IsCompact K →
        Tendsto (fun k => volume (symmDiff (blowUp U x (r_seq (subseq k))) F ∩ K))
          atTop (nhds 0)) ∧
      F =ᵐ[volume] {y | inner ℝ y ν < α} := by
  rcases h_nontrivial with ⟨c_vol, R_vol, hc_vol_pos, hR_vol_pos, h_vol_two_sided⟩

  let E_seq := fun k => blowUp U x (r_seq k)

  have hE_meas : ∀ k, MeasurableSet (E_seq k) := by
    intro k
    have hr_ne : r_seq k ≠ 0 := (hr_pos k).ne'
    exact (blowUpMap_measurableEmbedding x hr_ne).measurableSet_image.mpr hU.measurableSet

  -- Step 1: Uniform volume bound on compact sets
  have h_vol : ∀ (K : Set (E n)), IsCompact K →
      ∃ (C : ENNReal), ∀ k, volume (E_seq k ∩ K) ≤ C := by
    intro K hK
    have hK_bdd : Bornology.IsBounded K := hK.isBounded
    rcases hK_bdd.subset_closedBall (0 : E n) with ⟨R, hR⟩
    refine ⟨volume (closedBall (0 : E n) R), fun k => ?_⟩
    have h_sub : E_seq k ∩ K ⊆ closedBall (0 : E n) R := by
      intro y hy; exact hR hy.2
    exact measure_mono h_sub

  -- Step 2: Translation bound for blow-ups
  have h_trans : ∀ (K : Set (E n)), IsCompact K →
      ∃ (C : ℝ), ∀ k, ∀ (h : E n),
        volume (symmDiff (E_seq k) ((fun y => y + h) '' (E_seq k)) ∩ K) ≤
        ENNReal.ofReal (C * ‖h‖) :=
    blow_up_translation_bound hU h_perim_finite hn x r_seq hr_pos h_upper hr_tendsto

  -- Step 3: BV compactness
  rcases bv_compactness_sequence_of_translation hE_meas h_vol h_trans with
    ⟨F, subseq, hsub_strict, hF_meas, h_conv⟩

  let r' := fun k => r_seq (subseq k)
  have hr'_pos : ∀ k, 0 < r' k := fun k => hr_pos (subseq k)
  have hr'_tendsto : Tendsto r' atTop (nhds 0) :=
    hr_tendsto.comp hsub_strict.tendsto_atTop

  -- h_conv already uses Geometry.symmDiff; lower semicontinuity expects the same
  have h_conv' : ∀ (K : Set (E n)), IsCompact K →
      Tendsto (fun k => volume (symmDiff (E_seq (subseq k)) F ∩ K)) atTop (nhds 0) :=
    h_conv

  -- Step 4: Directional variation vanishes perpendicular to ν
  have h_zero_dv : ∀ (w : E n), inner ℝ w ν = 0 →
      directionalVariation F w = 0 := by
    intro w hw
    have h_local_zero : ∀ (K : Set (E n)), IsCompact K →
        directionalVariationIn F w K = 0 := by
      intro K hK
      let E_subseq : ℕ → Set (E n) := fun k => E_seq (subseq k)
      have hE_subseq : ∀ k, MeasurableSet (E_subseq k) := fun k => hE_meas (subseq k)
      let a : ℕ → ENNReal := fun k => directionalVariationIn (E_subseq k) w K
      have h_lsc : directionalVariationIn F w K ≤ liminf a atTop :=
        directionalVariationIn_lowerSemicontinuity hF_meas hE_subseq
          (fun K' hK' => h_conv' K' hK') w K
      have hw' : inner ℝ w (measureTheoreticNormal U x) = 0 := by
        rw [hν] at *; exact hw
      have h_tendsto : Tendsto a atTop (nhds 0) :=
        directionalVariation_blowUp_vanishing
          hU.measurableSet h_perim_finite x hx_trb hn w hw' K hK
          h_upper (h_abs_lebesgue w hw)
        |>.comp (by
          have h1 : ∀ᶠ k in atTop, r' k ∈ Set.Ioi 0 := by filter_upwards with k; exact hr'_pos k
          exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within r' hr'_tendsto h1)
      have h_liminf_zero : liminf a atTop = 0 := h_tendsto.liminf_eq
      rw [h_liminf_zero] at h_lsc
      exact bot_unique h_lsc
    exact directionalVariationIn_all_compact_zero hF_meas w h_local_zero

  -- Step 5: Translation invariance perpendicular to ν
  have h_transl : ∀ (w : E n), inner ℝ w ν = 0 →
      ∀ (t : ℝ), translateSet F (t • w) =ᵐ[volume] F := by
    intro w hw t
    exact zero_directionalVariation_translation_invariant hF_meas (h_zero_dv w hw) t

  -- Step 6: Orientation condition
  have h_orientation_F : ∀ (φ : E n → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∀ x, 0 ≤ φ x) → 0 ≤ ∫ x in F, fderiv ℝ φ x ν :=
    orientation_from_scalar_comparability hn hU h_perim_finite x ν hx_trb hν h_upper
      h_inner_lebesgue hF_meas hr'_pos hr'_tendsto h_conv

  -- Step 7: Monotone factorization
  have h_mono_factor : ∃ (g : ℝ → ℝ), Measurable g ∧
      (∀ t, g t = 0 ∨ g t = 1) ∧
      (∀ s t, s ≤ t → g t ≤ g s) ∧
      (∀ᵐ (z : E n) ∂volume, z ∈ F ↔ g (inner ℝ z ν) = 1) :=
    Geometry.Perimeter.orientation_to_monotone_factorization hF_meas hν_unit h_transl h_orientation_F

  rcases h_mono_factor with ⟨g, hg_meas, hg_values, hg_decr, h_factor⟩

  -- Step 8: Half-space characterization
  have h_main : (∃ (α : ℝ), ∀ᵐ (z : E n) ∂volume, (z ∈ F ↔ inner ℝ z ν < α)) ∨
      (∀ᵐ (z : E n) ∂volume, z ∉ F) ∨ (∀ᵐ (z : E n) ∂volume, z ∈ F) :=
    Geometry.Perimeter.halfSpace_characterization hF_meas hν_unit g hg_meas hg_values hg_decr h_factor

  rcases h_main with (h_case | h_empty | h_full)

  -- Case 1: F is a half-space
  · rcases h_case with ⟨α, hα⟩
    have hF_halfspace : F =ᵐ[volume] {y | inner ℝ y ν < α} := by
      filter_upwards [hα] with z hz
      exact propext hz
    exact ⟨F, subseq, α, hsub_strict, hF_meas, h_conv, hF_halfspace⟩

  -- Case 2: F is empty a.e. — contradiction with interior positive density
  · have hF_null : ∀ᵐ (z : E n) ∂volume, z ∉ F := h_empty
    let B : Set (E n) := ball (0 : E n) 1
    let K_ball : Set (E n) := closedBall (0 : E n) 1
    have h_conv_vol : Tendsto (fun k => volume (E_seq (subseq k) ∩ K_ball)) atTop
        (nhds (volume (Set.inter F K_ball))) :=
      tendsto_volume_inter_of_symmDiff (K := K_ball) (isCompact_closedBall _ _)
        (h_conv' K_ball (isCompact_closedBall _ _))
    have hF_null_vol : volume F = 0 := by
      have h5 : F =ᵐ[volume] (∅ : Set (E n)) := by
        filter_upwards [hF_null] with z hz
        exact propext ⟨hz, False.elim⟩
      have h6 : volume F = volume (∅ : Set (E n)) := measure_congr h5
      exact h6.trans measure_empty
    have hF_inter_null : volume (Set.inter F K_ball) = 0 :=
      measure_mono_null (by exact Set.inter_subset_left) hF_null_vol
    rw [hF_inter_null] at h_conv_vol
    have h_small : ∀ᶠ k in atTop, volume (E_seq (subseq k) ∩ K_ball) < ENNReal.ofReal (c_vol / 2) :=
      h_conv_vol (Iio_mem_nhds (by positivity))
    have h_large : ∀ᶠ k in atTop, volume (E_seq (subseq k) ∩ K_ball) ≥ ENNReal.ofReal c_vol := by
      filter_upwards [hr'_tendsto (Iio_mem_nhds hR_vol_pos)] with k hk
      have h1 : volume (U ∩ ball x (r' k)) ≥ ENNReal.ofReal (c_vol * (r' k) ^ n) :=
        (h_vol_two_sided (r' k) (hr'_pos k) hk).1
      have hB_sub_K : B ⊆ K_ball := ball_subset_closedBall
      have h2 : volume (E_seq (subseq k) ∩ B) =
          ENNReal.ofReal ((r' k) ^ n)⁻¹ * volume (U ∩ ball x (r' k)) := by
        simpa [E_seq, B, mul_one] using blow_up_volume (S := U) (x := x) (r := r' k) (R := 1) hU.measurableSet (hr'_pos k) (by norm_num)
      have h_pos : 0 < (r' k) ^ n := pow_pos (hr'_pos k) n
      have h3 : ENNReal.ofReal ((r' k) ^ n)⁻¹ * ENNReal.ofReal (c_vol * (r' k) ^ n) = ENNReal.ofReal c_vol := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        <;> field_simp [h_pos.ne'] <;> ring
      have h4 : ENNReal.ofReal ((r' k) ^ n)⁻¹ * volume (U ∩ ball x (r' k)) ≥
          ENNReal.ofReal c_vol := by
        have h5 := mul_le_mul_left' h1 (ENNReal.ofReal ((r' k) ^ n)⁻¹)
        rw [h3] at h5
        exact h5
      have h7 : E_seq (subseq k) ∩ B ⊆ E_seq (subseq k) ∩ K_ball := by
        intro y hy; exact ⟨hy.1, hB_sub_K hy.2⟩
      have h6 : volume (E_seq (subseq k) ∩ K_ball) ≥ volume (E_seq (subseq k) ∩ B) :=
        measure_mono h7
      rw [h2] at h6
      exact le_trans h4 h6
    have h_both : ∀ᶠ k in atTop, volume (E_seq (subseq k) ∩ K_ball) < ENNReal.ofReal (c_vol / 2) ∧
        volume (E_seq (subseq k) ∩ K_ball) ≥ ENNReal.ofReal c_vol := h_small.and h_large
    rcases h_both.exists with ⟨k, hk1, hk2⟩
    have h6 : ENNReal.ofReal (c_vol / 2) < ENNReal.ofReal c_vol := by
      exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith)
    exact False.elim (not_le.mpr h6 (le_trans hk2 hk1.le))

  -- Case 3: F is full a.e. — contradiction with exterior positive density
  · have hF_full : ∀ᵐ (z : E n) ∂volume, z ∈ F := h_full
    let B : Set (E n) := ball (0 : E n) 1
    let K_ball : Set (E n) := closedBall (0 : E n) 1
    have h_conv_vol : Tendsto (fun k => volume (K_ball \ E_seq (subseq k))) atTop
        (nhds (volume (K_ball \ F))) :=
      tendsto_volume_compl_of_symmDiff (K := K_ball) (isCompact_closedBall _ _)
        (h_conv' K_ball (isCompact_closedBall _ _))
    have hF_compl_null : volume Fᶜ = 0 := by
      have h5 : Fᶜ =ᵐ[volume] (∅ : Set (E n)) := by
        filter_upwards [hF_full] with z hz
        exact propext ⟨fun h => h hz, False.elim⟩
      have h6 : volume Fᶜ = volume (∅ : Set (E n)) := measure_congr h5
      exact h6.trans measure_empty
    have hF_diff_null : volume (K_ball \ F) = 0 :=
      measure_mono_null (by intro x hx; exact hx.2) hF_compl_null
    rw [hF_diff_null] at h_conv_vol
    have h_small : ∀ᶠ k in atTop, volume (K_ball \ E_seq (subseq k)) < ENNReal.ofReal (c_vol / 2) :=
      h_conv_vol (Iio_mem_nhds (by positivity))
    have h_large : ∀ᶠ k in atTop, volume (K_ball \ E_seq (subseq k)) ≥ ENNReal.ofReal c_vol := by
      filter_upwards [hr'_tendsto (Iio_mem_nhds hR_vol_pos)] with k hk
      have h1 : volume ((ball x (r' k)) \ U) ≥ ENNReal.ofReal (c_vol * (r' k) ^ n) :=
        (h_vol_two_sided (r' k) (hr'_pos k) hk).2
      have hr_ne : (r' k) ≠ 0 := (hr'_pos k).ne'
      have hU_compl : MeasurableSet Uᶜ := hU.measurableSet.compl
      have hbc : blowUp Uᶜ x (r' k) = (E_seq (subseq k))ᶜ := by
        exact blowUp_compl hr_ne
      have hB_sub_K : B ⊆ K_ball := ball_subset_closedBall
      have h_eq2 : Set.inter (blowUp Uᶜ x (r' k)) B = B \ E_seq (subseq k) := by
        rw [hbc]; ext y; simp [Set.inter] <;> tauto
      have h_eq3 : Uᶜ ∩ ball x (r' k) = (ball x (r' k)) \ U := by
        ext y; simp [Set.compl_def] <;> tauto
      have h2 : volume (B \ E_seq (subseq k)) =
          ENNReal.ofReal ((r' k) ^ n)⁻¹ * volume ((ball x (r' k)) \ U) := by
        have h_tmp := blow_up_volume (S := Uᶜ) (x := x) (r := r' k) (R := 1) hU_compl (hr'_pos k) (by norm_num)
        have h_left : blowUp Uᶜ x (r' k) ∩ ball (0 : E n) 1 = B \ E_seq (subseq k) := by
          have h9 : Set.inter (blowUp Uᶜ x (r' k)) B = B \ E_seq (subseq k) := h_eq2
          exact h9
        have h_mul : (r' k) * 1 = (r' k) := by ring
        have h_right : Uᶜ ∩ ball x ((r' k) * 1) = (ball x (r' k)) \ U := by
          rw [h_mul]
          exact h_eq3
        rw [h_left, h_right] at h_tmp
        exact h_tmp
      have h_pos : 0 < (r' k) ^ n := pow_pos (hr'_pos k) n
      have h3 : ENNReal.ofReal ((r' k) ^ n)⁻¹ * ENNReal.ofReal (c_vol * (r' k) ^ n) = ENNReal.ofReal c_vol := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        <;> field_simp [h_pos.ne'] <;> ring
      have h4 : ENNReal.ofReal ((r' k) ^ n)⁻¹ * volume ((ball x (r' k)) \ U) ≥
          ENNReal.ofReal c_vol := by
        have h5 := mul_le_mul_left' h1 (ENNReal.ofReal ((r' k) ^ n)⁻¹)
        rw [h3] at h5
        exact h5
      have h7 : B \ E_seq (subseq k) ⊆ K_ball \ E_seq (subseq k) := by
        intro y hy; exact ⟨hB_sub_K hy.1, hy.2⟩
      have h6 : volume (K_ball \ E_seq (subseq k)) ≥ volume (B \ E_seq (subseq k)) :=
        measure_mono h7
      rw [h2] at h6
      exact le_trans h4 h6
    have h_both : ∀ᶠ k in atTop, volume (K_ball \ E_seq (subseq k)) < ENNReal.ofReal (c_vol / 2) ∧
        volume (K_ball \ E_seq (subseq k)) ≥ ENNReal.ofReal c_vol := h_small.and h_large
    rcases h_both.exists with ⟨k, hk1, hk2⟩
    have h6 : ENNReal.ofReal (c_vol / 2) < ENNReal.ofReal c_vol := by
      exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith)
    exact False.elim (not_le.mpr h6 (le_trans hk2 hk1.le))

end Geometry.StructureTheorem
