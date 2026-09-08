/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.TubeParentPacking

/-!
# Counting essentially distinct `δ`-tubes inside a `ρ`-tube

The Wang--Zahl leaf-density route
(`Kakeya.WangZahl.maxDensity_leaves_le_of_katzTaoEveryScale`) needs, as its only
geometric input, a bound on the number of members of a pairwise essentially distinct family
of `δ`-tubes of the unit ball that lie inside one single `ρ`-tube, `δ ≤ ρ ≤ 1`.

This file proves such a bound with an **absolute** constant and the exponent `6`:

* `Kakeya.Tube.tubeParamDist_gt_of_isEssentiallyDistinct` — essential distinctness of two
  `δ`-tubes forces their `Kakeya.tubeParamDist` to exceed `(2/15) δ`.  This is the
  converse-direction geometry the tree was missing: `Tube.endpoint_separated_of_ed`
  says that essentially distinct tubes cannot have *both* endpoints close, and the
  centre/direction coordinates of a tube turn that into a single parameter-distance
  separation, after reversing one of the two tubes when their directions are nearly
  antipodal.
* `Kakeya.card_le_of_EssDistinct_in_tube_six` — the packing count itself:
  `#{i : T i ⊆ V} ≤ edInTubeConst * (ρ/δ)^6`.

The count is not sharp: the honest exponent for `δ`-tubes inside a `ρ`-tube in `ℝ³` is `4`
(two direction and two transverse-position parameters, each with `≍ ρ/δ` choices).  The
exponent `6` here comes from `Kakeya.card_le_of_tubeParamDist_separated_of_ratio`, which
packs the *centre* in a three-dimensional ball rather than in the two-dimensional transverse
disc, and so pays one extra factor `ρ/δ` for the longitudinal slide together with one extra
factor from the crude direction cap count.  For the consumer this is immaterial: there
`ρ < K δ` with `K = δ^{-η}` and `η` is free, so `(ρ/δ)^6 ≤ δ^{-6η}` is as good as
`δ^{-4η}`.
-/

@[expose] public section

open MeasureTheory Metric Set Convexity ConvexSpaceBody
open scoped NNReal ENNReal RealInnerProductSpace

noncomputable section

namespace Kakeya

/-! ### Essential distinctness as a parameter separation -/

/-- **Essentially distinct `δ`-tubes are `(2/15)δ`-separated in parameter distance.**

`Tube.endpoint_separated_of_ed` says that two essentially distinct `δ`-tubes cannot have
both endpoints within `δ/5` of each other, because in dimension `3` a homothety of ratio
`1 - 1/5` would then embed one into the other with volume ratio `(4/5)^3 = 0.512 > 1/2`.
Reading the endpoints in centre/direction coordinates, `x = c - d/2` and `y = c + d/2`,
a parameter distance at most `(2/15) δ` gives endpoint distances at most
`(2/15) δ + (1/2)(2/15) δ = δ/5` — in the orientation selected by whichever of
`‖d₁ - d₂‖`, `‖d₁ + d₂‖` realises the projective distance.  Since `Tube.reverse` leaves the
carrier (hence essential distinctness) untouched, both orientations are available. -/
theorem Tube.tubeParamDist_gt_of_isEssentiallyDistinct
    {δ : ℝ≥0} (hδ : 0 < δ) (T₁ T₂ : Tube δ (EuclideanSpace ℝ (Fin 3)))
    (hED : _root_.IsEssentiallyDistinct (T₁.carrier : Set (EuclideanSpace ℝ (Fin 3)))
      (T₂.carrier : Set (EuclideanSpace ℝ (Fin 3)))) :
    (2 / 15 : ℝ) * (δ : ℝ) < tubeParamDist T₁ T₂ := by
  by_contra hcon
  rw [not_lt] at hcon
  have hδ0 : (0 : ℝ) < (δ : ℝ) := NNReal.coe_pos.mpr hδ
  have hrank : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 :=
    finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 3)
  have hσ_strong : (1 / 2 : ℝ) < (1 - (1 / 5 : ℝ)) ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) := by
    rw [hrank]; norm_num
  have hc : dist T₁.center T₂.center ≤ (2 / 15 : ℝ) * (δ : ℝ) :=
    le_trans (dist_center_le_tubeParamDist T₁ T₂) hcon
  have hd : min ‖T₁.direction - T₂.direction‖ ‖T₁.direction + T₂.direction‖
      ≤ (2 / 15 : ℝ) * (δ : ℝ) :=
    le_trans (projDist_le_tubeParamDist T₁ T₂) hcon
  have hcnorm : ‖T₁.center - T₂.center‖ ≤ (2 / 15 : ℝ) * (δ : ℝ) := by
    rwa [← dist_eq_norm]
  rcases le_total ‖T₁.direction - T₂.direction‖ ‖T₁.direction + T₂.direction‖ with hmin | hmin
  · -- Same orientation.
    have hdd : ‖T₁.direction - T₂.direction‖ ≤ (2 / 15 : ℝ) * (δ : ℝ) := by
      rwa [min_eq_left hmin] at hd
    have hx : ‖T₁.x - T₂.x‖ ≤ (1 / 5 : ℝ) * (δ : ℝ) := by
      have : T₁.x - T₂.x
          = (T₁.center - T₂.center) - (2⁻¹ : ℝ) • (T₁.direction - T₂.direction) := by
        rw [Tube.x_eq_center_sub T₁, Tube.x_eq_center_sub T₂]; module
      rw [this]
      calc ‖(T₁.center - T₂.center) - (2⁻¹ : ℝ) • (T₁.direction - T₂.direction)‖
          ≤ ‖T₁.center - T₂.center‖ + ‖(2⁻¹ : ℝ) • (T₁.direction - T₂.direction)‖ :=
            norm_sub_le _ _
        _ = ‖T₁.center - T₂.center‖ + 2⁻¹ * ‖T₁.direction - T₂.direction‖ := by
            rw [norm_smul]; norm_num
        _ ≤ (2 / 15 : ℝ) * (δ : ℝ) + 2⁻¹ * ((2 / 15 : ℝ) * (δ : ℝ)) := by
            gcongr
        _ = (1 / 5 : ℝ) * (δ : ℝ) := by ring
    have hy : ‖T₁.y - T₂.y‖ ≤ (1 / 5 : ℝ) * (δ : ℝ) := by
      have : T₁.y - T₂.y
          = (T₁.center - T₂.center) + (2⁻¹ : ℝ) • (T₁.direction - T₂.direction) := by
        rw [Tube.y_eq_center_add T₁, Tube.y_eq_center_add T₂]; module
      rw [this]
      calc ‖(T₁.center - T₂.center) + (2⁻¹ : ℝ) • (T₁.direction - T₂.direction)‖
          ≤ ‖T₁.center - T₂.center‖ + ‖(2⁻¹ : ℝ) • (T₁.direction - T₂.direction)‖ :=
            norm_add_le _ _
        _ = ‖T₁.center - T₂.center‖ + 2⁻¹ * ‖T₁.direction - T₂.direction‖ := by
            rw [norm_smul]; norm_num
        _ ≤ (2 / 15 : ℝ) * (δ : ℝ) + 2⁻¹ * ((2 / 15 : ℝ) * (δ : ℝ)) := by
            gcongr
        _ = (1 / 5 : ℝ) * (δ : ℝ) := by ring
    rcases Tube.endpoint_separated_of_ed hδ (by norm_num : (0:ℝ) ≤ 1/5)
        (by norm_num : (1/5:ℝ) ≤ 1) hσ_strong T₁ T₂ hED with h | h
    · exact absurd hx (not_le.mpr h)
    · exact absurd hy (not_le.mpr h)
  · -- Opposite orientation: compare `T₁` with `T₂.reverse`.
    have hdd : ‖T₁.direction + T₂.direction‖ ≤ (2 / 15 : ℝ) * (δ : ℝ) := by
      rwa [min_eq_right hmin] at hd
    have hED' : _root_.IsEssentiallyDistinct (T₁.carrier : Set (EuclideanSpace ℝ (Fin 3)))
        ((T₂.reverse).carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
      rwa [Tube.reverse_carrier]
    have hx : ‖T₁.x - (T₂.reverse).x‖ ≤ (1 / 5 : ℝ) * (δ : ℝ) := by
      have : T₁.x - (T₂.reverse).x
          = (T₁.center - T₂.center) - (2⁻¹ : ℝ) • (T₁.direction + T₂.direction) := by
        rw [Tube.reverse_x, Tube.x_eq_center_sub T₁, Tube.y_eq_center_add T₂]; module
      rw [this]
      calc ‖(T₁.center - T₂.center) - (2⁻¹ : ℝ) • (T₁.direction + T₂.direction)‖
          ≤ ‖T₁.center - T₂.center‖ + ‖(2⁻¹ : ℝ) • (T₁.direction + T₂.direction)‖ :=
            norm_sub_le _ _
        _ = ‖T₁.center - T₂.center‖ + 2⁻¹ * ‖T₁.direction + T₂.direction‖ := by
            rw [norm_smul]; norm_num
        _ ≤ (2 / 15 : ℝ) * (δ : ℝ) + 2⁻¹ * ((2 / 15 : ℝ) * (δ : ℝ)) := by
            gcongr
        _ = (1 / 5 : ℝ) * (δ : ℝ) := by ring
    have hy : ‖T₁.y - (T₂.reverse).y‖ ≤ (1 / 5 : ℝ) * (δ : ℝ) := by
      have : T₁.y - (T₂.reverse).y
          = (T₁.center - T₂.center) + (2⁻¹ : ℝ) • (T₁.direction + T₂.direction) := by
        rw [Tube.reverse_y, Tube.y_eq_center_add T₁, Tube.x_eq_center_sub T₂]; module
      rw [this]
      calc ‖(T₁.center - T₂.center) + (2⁻¹ : ℝ) • (T₁.direction + T₂.direction)‖
          ≤ ‖T₁.center - T₂.center‖ + ‖(2⁻¹ : ℝ) • (T₁.direction + T₂.direction)‖ :=
            norm_add_le _ _
        _ = ‖T₁.center - T₂.center‖ + 2⁻¹ * ‖T₁.direction + T₂.direction‖ := by
            rw [norm_smul]; norm_num
        _ ≤ (2 / 15 : ℝ) * (δ : ℝ) + 2⁻¹ * ((2 / 15 : ℝ) * (δ : ℝ)) := by
            gcongr
        _ = (1 / 5 : ℝ) * (δ : ℝ) := by ring
    rcases Tube.endpoint_separated_of_ed hδ (by norm_num : (0:ℝ) ≤ 1/5)
        (by norm_num : (1/5:ℝ) ≤ 1) hσ_strong T₁ T₂.reverse hED' with h | h
    · exact absurd hx (not_le.mpr h)
    · exact absurd hy (not_le.mpr h)

/-! ### The packing count -/

/-- The absolute constant of `Kakeya.card_le_of_EssDistinct_in_tube_six`.  Its value is
immaterial — only that it depends on nothing.  The first entry is the parameter-packing
branch `ρ ≤ 1/4`, the second the crude ball count on `1/4 < ρ ≤ 1`. -/
def edInTubeConst : ℝ :=
  max ((365 : ℝ) ^ 3 * (250 * 91 ^ 3 + 250))
    (4096 * Tube.card_le_of_EssDistinct.C 3)

theorem edInTubeConst_pos : 0 < edInTubeConst := by
  have h : (0:ℝ) < (365 : ℝ) ^ 3 * (250 * 91 ^ 3 + 250) := by norm_num
  exact lt_of_lt_of_le h (le_max_left _ _)

open Classical in
/-- **Essentially distinct `δ`-tubes inside a `ρ`-tube.**

A pairwise essentially distinct family of `δ`-tubes of the unit ball has at most
`edInTubeConst · (ρ/δ)^6` members inside any single `ρ`-tube, `δ ≤ ρ`.  (No upper bound on `ρ`
is needed: for `ρ` past `1/4` the crude ball count already suffices.)

Two regimes.  For `ρ ≤ 1/4` the members are `(2/15)δ`-separated in `Kakeya.tubeParamDist`
(`Kakeya.Tube.tubeParamDist_gt_of_isEssentiallyDistinct`) and all within `12 ρ` of each other
(`Kakeya.tubeParamDist_le_of_subset_common`), so
`Kakeya.card_le_of_tubeParamDist_separated_of_ratio` at ratio `N = ⌈90 ρ/δ⌉` applies.  For
`ρ > 1/4` the scale `ρ` is comparable to `1` and the crude ball count
`Tube.card_le_of_EssDistinct` already gives `(1/δ)^6 ≤ (4ρ/δ)^6`.

The exponent `6` is not sharp — see the module docstring — but the constant is absolute, which
is what the consumer needs. -/
theorem card_le_of_EssDistinct_in_tube_six
    {ι : Type*} {δ ρ : ℝ≥0} (hδ : 0 < δ) (hδρ : δ ≤ ρ)
    (s : Finset ι) (T : ι → Tube δ (EuclideanSpace ℝ (Fin 3)))
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (hED : (s : Set ι).Pairwise
      (fun i j => _root_.IsEssentiallyDistinct (T i).carrier (T j).carrier))
    (V : Tube ρ (EuclideanSpace ℝ (Fin 3))) :
    (((s.filter fun i => (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody).card : ℕ) : ℝ)
      ≤ edInTubeConst * ((ρ : ℝ) / (δ : ℝ)) ^ 6 := by
  classical
  set A := s.filter fun i => (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody with hA_def
  have hAs : A ⊆ s := Finset.filter_subset _ _
  have hCnn : (0 : ℝ) ≤ edInTubeConst := edInTubeConst_pos.le
  have hCnn : (0 : ℝ) ≤ edInTubeConst := edInTubeConst_pos.le
  have hδ0 : (0 : ℝ) < (δ : ℝ) := NNReal.coe_pos.mpr hδ
  have hρ0 : (0 : ℝ) < (ρ : ℝ) := lt_of_lt_of_le hδ0 (by exact_mod_cast hδρ)
  set t : ℝ := (ρ : ℝ) / (δ : ℝ) with ht_def
  have ht1 : (1 : ℝ) ≤ t := by
    rw [ht_def, le_div_iff₀ hδ0, one_mul]
    exact_mod_cast hδρ
  have ht0 : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht1
  have hEDA : (A : Set ι).Pairwise
      (fun i j => _root_.IsEssentiallyDistinct (T i).carrier (T j).carrier) :=
    hED.mono (by exact_mod_cast hAs)
  have hsub : ∀ i ∈ A, (T i).carrier ⊆ (V.carrier : Set (EuclideanSpace ℝ (Fin 3))) := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  by_cases hρsmall : (ρ : ℝ) ≤ 1 / 4
  · -- Parameter packing branch.
    rcases A.eq_empty_or_nonempty with hAe | ⟨k₀, hk₀⟩
    · rw [hAe]
      simp only [Finset.card_empty, Nat.cast_zero]
      exact mul_nonneg hCnn (by positivity)
    · set N : ℕ := ⌈90 * t⌉₊ with hN_def
      have hNge : 90 * t ≤ (N : ℝ) := Nat.le_ceil _
      have hNlt : (N : ℝ) < 90 * t + 1 := Nat.ceil_lt_add_one (by positivity)
      have hN1 : 1 ≤ N := by
        by_contra h
        push_neg at h
        interval_cases N
        · simp only [Nat.cast_zero] at hNge; nlinarith
      have hNt : (N : ℝ) ≤ 91 * t := by nlinarith
      have hsep : (0 : ℝ) < 2 / 15 * (δ : ℝ) := by positivity
      have hRsep : 12 * (ρ : ℝ) ≤ (N : ℝ) * (2 / 15 * (δ : ℝ)) := by
        have h1 : (90 * t) * (2 / 15 * (δ : ℝ)) ≤ (N : ℝ) * (2 / 15 * (δ : ℝ)) := by
          exact mul_le_mul_of_nonneg_right hNge hsep.le
        have h2 : (90 * t) * (2 / 15 * (δ : ℝ)) = 12 * (ρ : ℝ) := by
          rw [ht_def]; field_simp; ring
        linarith
      have hAsep : ∀ k ∈ A, ∀ k' ∈ A, k ≠ k' →
          2 / 15 * (δ : ℝ) < tubeParamDist (T k) (T k') := by
        intro k hk k' hk' hne
        exact Tube.tubeParamDist_gt_of_isEssentiallyDistinct hδ (T k) (T k')
          (hEDA (by exact_mod_cast hk) (by exact_mod_cast hk') hne)
      have hAdist : ∀ k ∈ A, tubeParamDist (T k) (T k₀) ≤ 12 * (ρ : ℝ) := by
        intro k hk
        exact tubeParamDist_le_of_subset_common (T k) (T k₀) V (hsub k hk) (hsub k₀ hk₀) hρsmall
      have hcard := card_le_of_tubeParamDist_separated_of_ratio (T := T) (A := A)
        hN1 hsep hRsep hAsep k₀ hAdist
      refine hcard.trans ?_
      have key : (4 * (N : ℝ) + 1) ^ 3 * (250 * (N : ℝ) ^ 3 + 250) ≤ edInTubeConst * t ^ 6 := by
        have h4N : (4 * (N : ℝ) + 1) ≤ 365 * t := by nlinarith
        have hcube : (4 * (N : ℝ) + 1) ^ 3 ≤ (365 * t) ^ 3 :=
          pow_le_pow_left₀ (by positivity) h4N 3
        have hN3 : (250 * (N : ℝ) ^ 3 + 250) ≤ (250 * 91 ^ 3 + 250) * t ^ 3 := by
          have hNc : (N : ℝ) ^ 3 ≤ (91 * t) ^ 3 := pow_le_pow_left₀ (by positivity) hNt 3
          have ht3 : (1 : ℝ) ≤ t ^ 3 := one_le_pow₀ ht1
          nlinarith
        have hstep : (4 * (N : ℝ) + 1) ^ 3 * (250 * (N : ℝ) ^ 3 + 250)
            ≤ (365 * t) ^ 3 * ((250 * 91 ^ 3 + 250) * t ^ 3) :=
          mul_le_mul hcube hN3 (by positivity) (by positivity)
        refine hstep.trans ?_
        have hmax : (365 : ℝ) ^ 3 * (250 * 91 ^ 3 + 250) ≤ edInTubeConst := by
          rw [edInTubeConst]; exact le_max_left _ _
        calc (365 * t) ^ 3 * ((250 * 91 ^ 3 + 250) * t ^ 3)
            = (365 : ℝ) ^ 3 * (250 * 91 ^ 3 + 250) * t ^ 6 := by ring
          _ ≤ edInTubeConst * t ^ 6 :=
              mul_le_mul_of_nonneg_right hmax (by positivity)
      rw [tubeParamPackingConstOf]
      push_cast
      exact key
  · -- Crude ball branch.
    push_neg at hρsmall
    have hcard := Tube.card_le_of_EssDistinct (E := EuclideanSpace ℝ (Fin 3)) hδ 1 A T
      (fun i hi => hball i (hAs hi)) hEDA
    have hrank : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 :=
      finrank_euclideanSpace_fin (𝕜 := ℝ) (n := 3)
    rw [hrank] at hcard
    have hCpos : (0:ℝ) < Tube.card_le_of_EssDistinct.C 3 := Tube.card_le_of_EssDistinct.C_pos
    have hkey : (1 / (δ:ℝ)) ^ (2 * 3) ≤ 4096 * t ^ 6 := by
      have h4 : (1 : ℝ) / (δ : ℝ) ≤ 4 * t := by
        rw [ht_def, div_le_iff₀ hδ0]
        have : (1:ℝ) ≤ 4 * (ρ:ℝ) := by linarith
        field_simp
        linarith [mul_pos hρ0 hδ0]
      have h40 : (0:ℝ) ≤ 1 / (δ:ℝ) := by positivity
      have := pow_le_pow_left₀ h40 h4 6
      calc (1 / (δ:ℝ)) ^ (2 * 3) = (1 / (δ:ℝ)) ^ 6 := by norm_num
        _ ≤ (4 * t) ^ 6 := this
        _ = 4096 * t ^ 6 := by ring
    calc ((A.card : ℕ) : ℝ) ≤ Tube.card_le_of_EssDistinct.C 3 * (1 / (δ:ℝ)) ^ (2*3) := by
          simpa using hcard
      _ ≤ Tube.card_le_of_EssDistinct.C 3 * (4096 * t ^ 6) := by
          exact mul_le_mul_of_nonneg_left hkey hCpos.le
      _ = (4096 * Tube.card_le_of_EssDistinct.C 3) * t ^ 6 := by ring
      _ ≤ edInTubeConst * t ^ 6 := by
          have hmax : 4096 * Tube.card_le_of_EssDistinct.C 3 ≤ edInTubeConst := by
            rw [edInTubeConst]; exact le_max_right _ _
          exact mul_le_mul_of_nonneg_right hmax (by positivity)

end Kakeya

end

end
