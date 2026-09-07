import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.Bounds
import Mathlib.Tactic

/-!
# Frostman scaling and weakening

Provides arbitrary-dimensional Frostman transport under homothety, scale
weakening, and dimension boosting.  Exponent weakening is exposed as a
compatibility wrapper around the existing `frostman_exponent_reduction`.
-/

noncomputable section

open Classical Kakeya.Assouad

namespace Kakeya.Assouad

variable {n : ℕ}

def frostmanHomothety
    (c : ℝ) (center : Point n) (x : Point n) : Point n :=
  c • (x - center)

def frostmanHomothetyInv
    (c : ℝ) (center : Point n) (y : Point n) : Point n :=
  center + c⁻¹ • y

lemma frostmanHomothety_dist
    {c : ℝ} (hc : 0 < c) (center : Point n) (x y : Point n) :
    dist (frostmanHomothety c center x) (frostmanHomothety c center y) =
      c * dist x y := by
  have h1 :
      frostmanHomothety c center x - frostmanHomothety c center y =
        c • (x - y) := by
    simp [frostmanHomothety, smul_sub]
  calc
    dist (frostmanHomothety c center x)
        (frostmanHomothety c center y) =
        ‖frostmanHomothety c center x -
          frostmanHomothety c center y‖ := by
      rw [dist_eq_norm]
    _ = ‖c • (x - y)‖ := by rw [h1]
    _ = ‖c‖ * ‖x - y‖ := by rw [norm_smul]
    _ = c * ‖x - y‖ := by
      rw [Real.norm_eq_abs, abs_of_pos hc]
    _ = c * dist x y := by rw [dist_eq_norm]

lemma frostmanHomothety_injective
    {c : ℝ} (hc : 0 < c) (center : Point n) :
    Function.Injective (frostmanHomothety c center) := by
  intro x y h
  have h6 :
      dist (frostmanHomothety c center x)
        (frostmanHomothety c center y) = 0 := by
    rw [h]
    simp
  have h7 : c * dist x y = 0 := by
    rwa [frostmanHomothety_dist hc center x y] at h6
  exact dist_eq_zero.mp ((mul_eq_zero.mp h7).resolve_left hc.ne')

lemma frostmanHomothety_right_inv
    {c : ℝ} (hc : 0 < c) (center : Point n) (y : Point n) :
    frostmanHomothety c center (frostmanHomothetyInv c center y) = y := by
  simp [frostmanHomothetyInv, frostmanHomothety, smul_smul, hc.ne']

lemma frostman_ballCount_image
    {c : ℝ} (hc : 0 < c) (center : Point n)
    (A : DiscreteSet n) (y : Point n) (r : ℝ) :
    DiscreteSet.ballCount
        (A.image (frostmanHomothety c center)) y r =
      DiscreteSet.ballCount A
        (frostmanHomothetyInv c center y) (r / c) := by
  let z0 := frostmanHomothetyInv c center y
  have h17 : frostmanHomothety c center z0 = y :=
    frostmanHomothety_right_inv hc center y
  have h_iff : ∀ z : Point n,
      dist (frostmanHomothety c center z) y ≤ r ↔
        dist z z0 ≤ r / c := by
    intro z
    rw [show dist (frostmanHomothety c center z) y =
      dist (frostmanHomothety c center z)
        (frostmanHomothety c center z0) by rw [h17]]
    rw [frostmanHomothety_dist hc center]
    constructor
    · intro h
      calc
        dist z z0 = (c * dist z z0) / c := by
          field_simp [hc.ne']
        _ ≤ r / c := by gcongr
    · intro h
      have h9 : c * dist z z0 ≤ c * (r / c) := by gcongr
      have h10 : c * (r / c) = r := by
        field_simp [hc.ne']
        <;> ring
      rw [h10] at h9
      exact h9
  have h_filter :
      (A.image (frostmanHomothety c center)).filter
          (fun z' => dist z' y ≤ r) =
        (A.filter (fun z => dist z z0 ≤ r / c)).image
          (frostmanHomothety c center) := by
    ext z'
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hP⟩
      exact ⟨z, ⟨hz, (h_iff z).mp hP⟩, rfl⟩
    · rintro ⟨z, ⟨hz, hP⟩, rfl⟩
      exact ⟨⟨z, hz, rfl⟩, (h_iff z).mpr hP⟩
  rw [DiscreteSet.ballCount, h_filter,
    Finset.card_image_of_injective _
      (frostmanHomothety_injective hc center)]
  <;> rfl

lemma frostman_image_enncard
    {c : ℝ} (hc : 0 < c) (center : Point n) (A : DiscreteSet n) :
    DiscreteSet.enncard (A.image (frostmanHomothety c center)) =
      A.enncard := by
  simp [DiscreteSet.enncard,
    Finset.card_image_of_injective _
      (frostmanHomothety_injective hc center)]

/--
Under `x ↦ c • (x - center)`, a Frostman set at scale `w` becomes Frostman
at scale `w * c`, with constant multiplied by `c ^ (-s)`.
-/
lemma frostman_homothety_forward
    {A : DiscreteSet n} {w s : ℝ} {C : ENNReal}
    {c : ℝ} {center : Point n}
    (hF : A.IsFrostman w s C) (hw : 0 < w) (hc : 1 ≤ c) :
    DiscreteSet.IsFrostman
      (A.image (frostmanHomothety c center)) (w * c) s
      (C * Kakeya.realRpowENN c (-s)) := by
  have hc_pos : 0 < c := by linarith
  let A' := A.image (frostmanHomothety c center)
  intro y r hr1 hr2
  have hr_nonneg : 0 ≤ r := by
    have h : 0 ≤ w * c := by positivity
    linarith
  have hr_scale : w ≤ r / c := by
    calc
      w = (w * c) / c := by field_simp [hc_pos.ne']
      _ ≤ r / c := by gcongr
  have hr_le_one : r / c ≤ 1 := by
    calc
      r / c ≤ 1 / c := by gcongr
      _ ≤ 1 := (div_le_one (by positivity)).mpr hc
  rw [frostman_ballCount_image hc_pos center]
  have hF' := hF (frostmanHomothetyInv c center y)
    (r / c) hr_scale hr_le_one
  have h_c_nonneg : 0 ≤ c := by linarith
  have h_cinv_nonneg : 0 ≤ c⁻¹ := by positivity
  have h_real_div :
      Real.rpow (r / c) s =
        Real.rpow r s * Real.rpow c (-s) := by
    have h1 : r / c = r * c⁻¹ := by
      field_simp [hc_pos.ne']
      <;> ring
    rw [h1]
    have h2 :
        Real.rpow (r * c⁻¹) s =
          Real.rpow r s * Real.rpow (c⁻¹) s :=
      Real.mul_rpow hr_nonneg h_cinv_nonneg
    rw [h2]
    have h3 : Real.rpow (c⁻¹) s = Real.rpow c (-s) := by
      have h4 := Real.rpow_neg_eq_inv_rpow c s
      exact h4.symm
    rw [h3]
  have h_rpow :
      Kakeya.realRpowENN (r / c) s =
        Kakeya.realRpowENN r s * Kakeya.realRpowENN c (-s) := by
    simp only [Kakeya.realRpowENN, h_real_div]
    have h_nonneg1 : 0 ≤ Real.rpow r s :=
      Real.rpow_nonneg hr_nonneg s
    have h_nonneg2 : 0 ≤ Real.rpow c (-s) :=
      Real.rpow_nonneg h_c_nonneg (-s)
    rw [ENNReal.ofReal_mul h_nonneg1]
    <;> rfl
  rw [h_rpow] at hF'
  rw [frostman_image_enncard hc_pos center]
  calc
    A.ballCount (frostmanHomothetyInv c center y) (r / c) ≤
        C * (Kakeya.realRpowENN r s *
          Kakeya.realRpowENN c (-s)) * A.enncard := hF'
    _ = (C * Kakeya.realRpowENN c (-s)) *
        Kakeya.realRpowENN r s * A.enncard := by ring

/--
Compatibility wrapper for the already-established exponent reduction theorem.
-/
lemma frostman_exponent_weakening
    {A : DiscreteSet n} {w s s' : ℝ} {C : ENNReal}
    (hF : A.IsFrostman w s C) (hw : 0 < w)
    (hs'_nonneg : 0 ≤ s') (h_le : s' ≤ s) :
    A.IsFrostman w s' C :=
  frostman_exponent_reduction hF hw hs'_nonneg h_le

/-- Increasing the lower cutoff scale weakens a Frostman condition. -/
lemma frostman_scale_weakening
    {A : DiscreteSet n} {w w' s : ℝ} {C : ENNReal}
    (hF : A.IsFrostman w s C) (h_le : w ≤ w') :
    A.IsFrostman w' s C := by
  intro x r hr1 hr2
  exact hF x r (h_le.trans hr1) hr2

/--
Increase the Frostman dimension from `s` to `s'`, paying the constant
`w ^ (s - s')`.
-/
lemma frostman_dimension_boosting
    {A : DiscreteSet n} {w s s' : ℝ} {C : ENNReal}
    (hF : A.IsFrostman w s C)
    (hw_pos : 0 < w)
    (hs_nonneg : 0 ≤ s)
    (hs_lt : s < s') :
    A.IsFrostman w s'
      (C * Kakeya.realRpowENN w (s - s')) := by
  intro x r hr1 hr2
  have h_r_pos : 0 < r := hw_pos.trans_le hr1
  have hF' := hF x r hr1 hr2
  have h_r_nonneg : 0 ≤ r := by linarith
  have h2 : r ^ s = r ^ s' * r ^ (s - s') := by
    have h4 : s' + (s - s') = s := by ring
    have h3 :
        r ^ (s' + (s - s')) = r ^ s' * r ^ (s - s') := by
      rw [Real.rpow_add h_r_pos]
    rw [h4] at h3
    exact h3
  have h5 : r ^ (s - s') ≤ w ^ (s - s') := by
    have h6 : s - s' < 0 := by linarith
    have h_log1 : Real.log w ≤ Real.log r :=
      Real.log_le_log (by linarith) hr1
    have h9 :
        (s - s') * Real.log w ≥
          (s - s') * Real.log r := by
      nlinarith
    have h10 :
        Real.log (w ^ (s - s')) ≥
          Real.log (r ^ (s - s')) := by
      rw [Real.log_rpow hw_pos, Real.log_rpow h_r_pos]
      exact h9
    have h_pos1 : 0 < r ^ (s - s') :=
      Real.rpow_pos_of_pos h_r_pos (s - s')
    have h_pos2 : 0 < w ^ (s - s') :=
      Real.rpow_pos_of_pos hw_pos (s - s')
    exact (Real.log_le_log_iff h_pos1 h_pos2).mp h10
  have h_real : r ^ s ≤ r ^ s' * w ^ (s - s') := by
    rw [h2]
    gcongr
  have h1 :
      Kakeya.realRpowENN r s ≤
        Kakeya.realRpowENN r s' *
          Kakeya.realRpowENN w (s - s') := by
    have h_mul :
        Kakeya.realRpowENN r s' *
            Kakeya.realRpowENN w (s - s') =
          ENNReal.ofReal (r ^ s' * w ^ (s - s')) := by
      simp only [Kakeya.realRpowENN]
      have h_nonneg1 : 0 ≤ r ^ s' :=
        Real.rpow_nonneg h_r_nonneg _
      have h_nonneg2 : 0 ≤ w ^ (s - s') :=
        Real.rpow_nonneg hw_pos.le _
      rw [ENNReal.ofReal_mul h_nonneg1]
      <;> rfl
    have h_goal :
        ENNReal.ofReal (r ^ s) ≤
          ENNReal.ofReal (r ^ s' * w ^ (s - s')) :=
      ENNReal.ofReal_le_ofReal h_real
    have h_simp :
        Kakeya.realRpowENN r s = ENNReal.ofReal (r ^ s) := by
      simp [Kakeya.realRpowENN]
    rw [h_simp, h_mul]
    exact h_goal
  calc
    A.ballCount x r ≤
        C * Kakeya.realRpowENN r s * A.enncard := hF'
    _ ≤ C *
        (Kakeya.realRpowENN r s' *
          Kakeya.realRpowENN w (s - s')) * A.enncard := by
      gcongr
    _ = (C * Kakeya.realRpowENN w (s - s')) *
        Kakeya.realRpowENN r s' * A.enncard := by ring

end Kakeya.Assouad
