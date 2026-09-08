import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.SelfDilatedContainment
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.TranslateTubeGeometry

/-!
# Geometry helpers for rigid motion normalization

Helper lemmas used by MultiplicityBound:
- `dilatedTubeCarrier_translate`: commuting dilation with translation.
- `tube_point_dist_to_midpoint`: distance from any carrier point to midpoint.
-/

noncomputable section

open Kakeya.Streamlined
open Kakeya.Streamlined.GeometricLemmas
open Kakeya.Streamlined.RandomTranslation

namespace Kakeya.Streamlined.GeneralizedFrostman

/-- Dilating a translated tube about its new midpoint equals translating the
original dilated tube by the same vector. -/
lemma dilatedTubeCarrier_translate {δ : ℝ} (T : Kakeya.DeltaTube δ)
    (A : ℝ) (v : Point3) :
    dilatedTubeCarrier A (translateTube T v) =
      translateSet (dilatedTubeCarrier A T) v := by
  let mid := tubeMidpoint T
  let mid' := tubeMidpoint (translateTube T v)
  have h_mid : mid' = mid + v := by
    simp [tubeMidpoint, translateTube, mid, mid'] <;> abel
  have h_hom : ∀ (x : Point3),
      AffineMap.homothety mid' A (x + v) = AffineMap.homothety mid A x + v := by
    intro x
    rw [h_mid]
    simp [AffineMap.homothety_apply, mid] <;> abel
  have h_car : (translateTube T v).carrier = translateSet T.carrier v :=
    translateTube_carrier T v
  have h_step1 : dilatedTubeCarrier A (translateTube T v) =
      AffineMap.homothety mid' A '' (translateTube T v).carrier := by rfl
  rw [h_step1, h_car]
  have h_step2 : AffineMap.homothety mid' A '' (translateSet T.carrier v) =
      translateSet (AffineMap.homothety mid A '' T.carrier) v := by
    ext z
    simp only [translateSet, Set.mem_image]
    constructor
    · rintro ⟨y, ⟨x, hx, hy_eq⟩, hz⟩
      subst hy_eq
      have h2 : AffineMap.homothety mid' A (x + v) = AffineMap.homothety mid A x + v := h_hom x
      have h_goal : AffineMap.homothety mid A x + v = z := h2.symm.trans hz
      exact ⟨AffineMap.homothety mid A x, ⟨x, hx, rfl⟩, h_goal⟩
    · rintro ⟨w, ⟨x, hx, hw_eq⟩, hz⟩
      subst hw_eq
      have h2 : AffineMap.homothety mid' A (x + v) = AffineMap.homothety mid A x + v := h_hom x
      have h_goal : AffineMap.homothety mid' A (x + v) = z := h2.trans hz
      exact ⟨x + v, ⟨x, hx, rfl⟩, h_goal⟩
  rw [h_step2]
  <;> rfl

/-- Any point in a tube carrier is within 1/2+δ of the midpoint. -/
lemma tube_point_dist_to_midpoint {δ : ℝ} (hδ : 0 ≤ δ)
    (T : Kakeya.DeltaTube δ) (y : Point3) (hy : y ∈ T.carrier) :
    dist y (tubeMidpoint T) ≤ 1 / 2 + δ := by
  let S := Kakeya.unitSegment T.base T.direction
  have h1 : Metric.infEDist y S ≤ ENNReal.ofReal δ := by
    simpa [Kakeya.DeltaTube.carrier] using hy
  have h_compact : IsCompact S := by
    apply IsCompact.image
    · exact isCompact_Icc
    · exact continuous_const.add (continuous_id.smul continuous_const)
  have h_nonempty : S.Nonempty := by
    refine ⟨T.base, ?_⟩
    simp [S, Kakeya.unitSegment] <;> exact ⟨0, by norm_num, by simp⟩
  rcases h_compact.exists_infEDist_eq_edist h_nonempty y with ⟨z, hz, h_eq⟩
  have h2 : edist y z ≤ ENNReal.ofReal δ := by rw [← h_eq]; exact h1
  have h3 : dist y z ≤ δ := by
    have h4 : edist y z = ENNReal.ofReal (dist y z) := edist_dist y z
    rw [h4] at h2
    exact (ENNReal.ofReal_le_ofReal_iff hδ).mp h2
  rcases (Set.mem_image _ _ _).mp hz with ⟨t, ht, hz_eq⟩
  have h4 : t ∈ Set.Icc (0 : ℝ) 1 := ht
  have h5 : dist z (tubeMidpoint T) ≤ 1 / 2 := by
    rw [← hz_eq]
    have h6 : tubeMidpoint T = T.base + (1 / 2 : ℝ) • T.direction := by rfl
    rw [h6]
    have h71 : (T.base + t • T.direction) - (T.base + (1 / 2 : ℝ) • T.direction) =
        (t - 1 / 2) • T.direction := by simp [sub_smul] <;> abel
    have h7 : dist (T.base + t • T.direction) (T.base + (1 / 2 : ℝ) • T.direction) =
        |t - 1 / 2| := by
      rw [dist_eq_norm, h71, norm_smul, T.direction_unit]
      <;> simp [mul_one] <;> rfl
    rw [h7]
    have h8 : |t - 1 / 2| ≤ 1 / 2 := by
      rw [abs_le]; constructor <;> linarith [h4.1, h4.2]
    exact h8
  calc dist y (tubeMidpoint T)
    ≤ dist y z + dist z (tubeMidpoint T) := dist_triangle _ _ _
  _ ≤ δ + 1 / 2 := by linarith
  _ = 1 / 2 + δ := by ring

end Kakeya.Streamlined.GeneralizedFrostman
