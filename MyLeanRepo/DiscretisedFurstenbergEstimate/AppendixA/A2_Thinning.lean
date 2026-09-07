module

/-
  A2 Thinning: Partition dyadic coarse tubes into 44×44 color classes
  to obtain AffineLine separation at scale Δ.

  Uses the 22-co-Lipschitz bound from DyadicToAffineAdapters:
    paramDistLinf ≤ 22 * dist(toAffineLine)

  Within a color class, L∞ parameter distance ≥ 44Δ, so AffineLine dist ≥ 2Δ ≥ Δ.
  Largest color class has ≥ 1/1936 of the tubes.

  Whiteprint node: appendix_a_alternative / a2_thinning
-/

public import MyLeanRepo.DiscretisedFurstenbergEstimate.Base
public import MyLeanRepo.DiscretisedFurstenbergEstimate.AppendixA.A2DyadicAdapter
public import MyLeanRepo.DiscretisedFurstenbergEstimate.DyadicToAffineAdapters
public import MyLeanRepo.OSWPrelude

@[expose] public section

open scoped ENNReal NNReal

attribute [local instance] Classical.propDecidable

noncomputable section

namespace DirecretisedFurstenbergEstimate.AppendixA.A2Thinning

open DiscretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate
open DirecretisedFurstenbergEstimate.AppendixA (tubeSlope tubeIntercept)
open DirecretisedFurstenbergEstimate.AppendixA.A2DyadicAdapter (dyadicTubeToA2)
open CoordinatePartition (swapLine_isometry)
open DyadicCardToNcover (toAffineLine)

abbrev Plane := EuclideanPlane

/-- Thin a finite set of dyadic coarse tubes to a subset whose AffineLine images
    are Δ-separated. Uses 44×44 = 1936 coloring of the integer parameter grid.
    Within each color class, L∞ parameter distance ≥ 44Δ, and the 22-co-Lipschitz
    bound gives AffineLine distance ≥ 2Δ ≥ Δ. -/
lemma thin_coarse_tubes_affine_separated {m : ℕ} (hm_pos : 1 ≤ m)
    (C : Finset (DyadicTube m))
    (h_slope : ∀ U ∈ C, |U.slope| ≤ 1)
    (h_intercept : ∀ U ∈ C, |U.intercept| ≤ 3) :
    ∃ (C_thin : Finset (DyadicTube m)),
      C_thin ⊆ C ∧
      (C.card : ℝ) ≤ 1936 * (C_thin.card : ℝ) ∧
      SeparatedAt (dyadicDelta m) (C_thin.image dyadicTubeToA2 : Set AffineLine) := by
  let colorOf (U : DyadicTube m) : ℕ × ℕ := ((U.a % 44).toNat, (U.b % 44).toNat)
  let colors : Finset (ℕ × ℕ) := (Finset.range 44) ×ˢ (Finset.range 44)
  have h_color_range : ∀ U ∈ C, colorOf U ∈ colors := by
    intro U _
    have h1 : 0 ≤ U.a % 44 := Int.emod_nonneg U.a (by norm_num)
    have h2 : U.a % 44 < 44 := Int.emod_lt_of_pos U.a (by norm_num)
    have h3 : 0 ≤ U.b % 44 := Int.emod_nonneg U.b (by norm_num)
    have h4 : U.b % 44 < 44 := Int.emod_lt_of_pos U.b (by norm_num)
    simp only [colors, colorOf, Finset.mem_product, Finset.mem_range] <;> omega
  let fiber (c : ℕ × ℕ) : Finset (DyadicTube m) := C.filter (fun U => colorOf U = c)
  have h_union : C = Finset.biUnion colors fiber := by
    ext U
    simp only [Finset.mem_biUnion]
    constructor
    · intro hU
      exact ⟨colorOf U, h_color_range U hU, by
        simp only [fiber, Finset.mem_filter] <;> exact ⟨hU, by simp⟩⟩
    · rintro ⟨c, _, hc⟩
      simp only [fiber, Finset.mem_filter] at hc
      exact hc.1
  have h_disj : ∀ c1 ∈ colors, ∀ c2 ∈ colors, c1 ≠ c2 → Disjoint (fiber c1) (fiber c2) := by
    intro c1 _ c2 _ hne
    simp only [fiber, Finset.disjoint_left, Finset.mem_filter]
    intro U h1 h2
    have h : c1 = c2 := h1.2.symm.trans h2.2
    exact hne h
  have h_card : C.card = ∑ c ∈ colors, (fiber c).card := by
    rw [h_union, Finset.card_biUnion h_disj]
  have h_colors_nonempty : colors.Nonempty := by
    exact ⟨(0, 0), by simp [colors]⟩
  rcases Finset.exists_max_image colors (fun c => (fiber c).card) h_colors_nonempty
    with ⟨c0, hc0, hmax⟩
  let C_thin := fiber c0
  have h_sub : C_thin ⊆ C := by
    simp only [C_thin, fiber, Finset.filter_subset]
  have h1936 : colors.card = 1936 := by
    simp [colors, Finset.card_product] <;> norm_num
  have h_card_bound : (C.card : ℝ) ≤ 1936 * (C_thin.card : ℝ) := by
    calc (C.card : ℝ)
      = ∑ c ∈ colors, ((fiber c).card : ℝ) := by exact_mod_cast h_card
    _ ≤ ∑ c ∈ colors, ((C_thin.card : ℝ)) := by
      apply Finset.sum_le_sum
      intro j _
      exact_mod_cast hmax j ‹_›
    _ = colors.card * (C_thin.card : ℝ) := by
      rw [Finset.sum_const] <;> ring
    _ = 1936 * (C_thin.card : ℝ) := by rw [h1936] <;> ring
  have h_sep : SeparatedAt (dyadicDelta m) (C_thin.image dyadicTubeToA2 : Set AffineLine) := by
    intro ℓ1 hℓ1 ℓ2 hℓ2 hne
    rcases Finset.mem_image.mp hℓ1 with ⟨U1, hU1, rfl⟩
    rcases Finset.mem_image.mp hℓ2 with ⟨U2, hU2, rfl⟩
    have h_same_color : colorOf U1 = colorOf U2 := by
      have h1 : U1 ∈ C_thin := hU1
      have h2 : U2 ∈ C_thin := hU2
      simp only [C_thin, fiber, Finset.mem_filter] at h1 h2
      exact h1.2.trans h2.2.symm
    have hU1C : U1 ∈ C := h_sub hU1
    have hU2C : U2 ∈ C := h_sub hU2
    have h_ne : U1 ≠ U2 := by
      intro h
      apply hne
      rw [h]
    have h_parts : (U1.a % 44).toNat = (U2.a % 44).toNat ∧
        (U1.b % 44).toNat = (U2.b % 44).toNat := by
      have h_eq : colorOf U1 = colorOf U2 := h_same_color
      simpa [colorOf, Prod.ext_iff] using h_eq
    have h_mod_a : U1.a % 44 = U2.a % 44 := by
      have h5 : 0 ≤ U1.a % 44 := Int.emod_nonneg U1.a (by norm_num)
      have h6 : 0 ≤ U2.a % 44 := Int.emod_nonneg U2.a (by norm_num)
      have h8 : (↑((U1.a % 44).toNat) : ℤ) = U1.a % 44 := Int.toNat_of_nonneg h5
      have h9 : (↑((U2.a % 44).toNat) : ℤ) = U2.a % 44 := Int.toNat_of_nonneg h6
      have h10 : (↑((U1.a % 44).toNat) : ℤ) = (↑((U2.a % 44).toNat) : ℤ) := by
        rw [h_parts.1]
      linarith
    have h_mod_b : U1.b % 44 = U2.b % 44 := by
      have h5 : 0 ≤ U1.b % 44 := Int.emod_nonneg U1.b (by norm_num)
      have h6 : 0 ≤ U2.b % 44 := Int.emod_nonneg U2.b (by norm_num)
      have h8 : (↑((U1.b % 44).toNat) : ℤ) = U1.b % 44 := Int.toNat_of_nonneg h5
      have h9 : (↑((U2.b % 44).toNat) : ℤ) = U2.b % 44 := Int.toNat_of_nonneg h6
      have h10 : (↑((U1.b % 44).toNat) : ℤ) = (↑((U2.b % 44).toNat) : ℤ) := by
        rw [h_parts.2]
      linarith
    have h_coord_diff : |U1.a - U2.a| ≥ 44 ∨ |U1.b - U2.b| ≥ 44 := by
      by_cases h_a : U1.a = U2.a
      · have h_b : U1.b ≠ U2.b := by
          intro h
          apply h_ne
          have h_ext : U1 = U2 := by
            cases U1 <;> cases U2 <;> congr <;> tauto
          exact h_ext
        have hdiv : (44 : ℤ) ∣ U1.b - U2.b := by
          rw [Int.emod_eq_emod_iff_emod_sub_eq_zero] at h_mod_b
          simpa using h_mod_b
        rcases hdiv with ⟨q, hq⟩
        have hq' : U1.b - U2.b = 44 * q := by linarith
        have hq_ne : q ≠ 0 := by
          intro h5; rw [h5] at hq'; omega
        have h6 : |q| ≥ 1 := Int.one_le_abs hq_ne
        right
        calc |U1.b - U2.b| = |44 * q| := by rw [hq']
          _ = 44 * |q| := by simp [abs_mul] <;> norm_num
          _ ≥ 44 := by
            have h7 : 44 * |q| ≥ 44 * 1 := by gcongr
            simpa using h7
      · have hdiv : (44 : ℤ) ∣ U1.a - U2.a := by
          rw [Int.emod_eq_emod_iff_emod_sub_eq_zero] at h_mod_a
          simpa using h_mod_a
        rcases hdiv with ⟨q, hq⟩
        have hq' : U1.a - U2.a = 44 * q := by linarith
        have hq_ne : q ≠ 0 := by
          intro h5; rw [h5] at hq'; omega
        have h6 : |q| ≥ 1 := Int.one_le_abs hq_ne
        left
        calc |U1.a - U2.a| = |44 * q| := by rw [hq']
          _ = 44 * |q| := by simp [abs_mul] <;> norm_num
          _ ≥ 44 := by
            have h7 : 44 * |q| ≥ 44 * 1 := by gcongr
            simpa using h7
    have h_slope1 : |U1.slope| ≤ 1 := h_slope U1 hU1C
    have h_slope2 : |U2.slope| ≤ 1 := h_slope U2 hU2C
    have h_intercept2 : |U2.intercept| ≤ 3 := h_intercept U2 hU2C
    have h_colip : DyadicToAffineAdapters.paramDistLinf U1 U2 ≤
        22 * dist (toAffineLine U1) (toAffineLine U2) :=
      DyadicToAffineAdapters.toAffineLine_co_lipschitz U1 U2 h_slope1 h_slope2 h_intercept2
    have h_linf_ge : DyadicToAffineAdapters.paramDistLinf U1 U2 ≥ 44 * dyadicDelta m := by
      dsimp only [DyadicToAffineAdapters.paramDistLinf]
      rcases h_coord_diff with (h_a | h_b)
      · have h_slope_diff : |U1.slope - U2.slope| ≥ 44 * dyadicDelta m := by
          have h_eq : U1.slope - U2.slope = (U1.a - U2.a : ℝ) * dyadicDelta m := by
            simp [DyadicTube.slope] <;> ring
          rw [h_eq]
          have h10 : 0 < dyadicDelta m := dyadicDelta_pos m
          have h9 : |(U1.a - U2.a : ℝ) * dyadicDelta m| = |(U1.a - U2.a : ℝ)| * dyadicDelta m := by
            rw [abs_mul, abs_of_pos h10]
          rw [h9]
          have h11 : |(U1.a - U2.a : ℝ)| ≥ 44 := by exact_mod_cast h_a
          have h12 : |(U1.a - U2.a : ℝ)| * dyadicDelta m ≥ 44 * dyadicDelta m := by
            exact mul_le_mul_of_nonneg_right h11 (by linarith)
          exact h12
        exact le_max_of_le_left h_slope_diff
      · have h_int_diff : |U1.intercept - U2.intercept| ≥ 44 * dyadicDelta m := by
          have h_eq : U1.intercept - U2.intercept = (U1.b - U2.b : ℝ) * dyadicDelta m := by
            simp [DyadicTube.intercept] <;> ring
          rw [h_eq]
          have h10 : 0 < dyadicDelta m := dyadicDelta_pos m
          have h9 : |(U1.b - U2.b : ℝ) * dyadicDelta m| = |(U1.b - U2.b : ℝ)| * dyadicDelta m := by
            rw [abs_mul, abs_of_pos h10]
          rw [h9]
          have h11 : |(U1.b - U2.b : ℝ)| ≥ 44 := by exact_mod_cast h_b
          have h12 : |(U1.b - U2.b : ℝ)| * dyadicDelta m ≥ 44 * dyadicDelta m := by
            exact mul_le_mul_of_nonneg_right h11 (by linarith)
          exact h12
        exact le_max_of_le_right h_int_diff
    have h_iso : dist (dyadicTubeToA2 U1) (dyadicTubeToA2 U2) =
        dist (toAffineLine U1) (toAffineLine U2) :=
      swapLine_isometry.dist_eq (toAffineLine U1) (toAffineLine U2)
    have h_dist_ge : dist (dyadicTubeToA2 U1) (dyadicTubeToA2 U2) ≥ dyadicDelta m := by
      rw [h_iso]
      have h12 : 44 * dyadicDelta m ≤ 22 * dist (toAffineLine U1) (toAffineLine U2) := by
        linarith [h_colip, h_linf_ge]
      have h13 : 0 < dyadicDelta m := dyadicDelta_pos m
      linarith
    exact h_dist_ge
  exact ⟨C_thin, h_sub, h_card_bound, h_sep⟩

end DirecretisedFurstenbergEstimate.AppendixA.A2Thinning
