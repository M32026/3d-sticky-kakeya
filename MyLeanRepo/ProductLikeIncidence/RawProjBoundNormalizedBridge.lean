module

/-
# Raw Projection Bound Normalized Bridge

Transfers the raw projection bound from original point sets to normalized
(translated) point sets, replacing Pbar_param with Pbar_param'.

## Proof

1. `raw_proj_translation_bound` gives Nδ(π_y(T_y')) ≤ 2·Nδ(π_y(T_y))
2. Original bound gives Nδ(π_y(T_y)) ≤ δ^(-L_exp·η) · sqrt(Nplane δ Pbar)
3. Reverse translation bound: Nplane δ Pbar ≤ 4·Nplane δ Pbar'
4. Therefore sqrt(Nplane δ Pbar) ≤ 2·sqrt(Nplane δ Pbar')
5. Combine: Nδ(π_y(T_y')) ≤ 4·δ^(-L_exp·η)·sqrt(Nplane δ Pbar')

## Whiteprint node
`raw_proj_bound_normalized_bridge`
-/

public import MyLeanRepo.ProductLikeIncidence.TranslationBounds
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open Set ENNReal Bornology

namespace ProductLikeIncidence.ProductReduction

/-- **Raw projection bound normalized bridge**: Transfer the raw projection
bound from original to translated (normalized) point sets. -/
lemma raw_proj_bound_normalized_bridge
    {δ y L_exp η : ℝ}
    (hδ_pos : 0 < δ)
    {T_y T_y' Pbar Pbar' : Set (EuclideanSpace ℝ (Fin 2))}
    (v : EuclideanSpace ℝ (Fin 2))
    (hT'_eq : T_y' = (fun p : EuclideanSpace ℝ (Fin 2) => p + v) '' T_y)
    (hPbar'_eq : Pbar' = (fun p : EuclideanSpace ℝ (Fin 2) => p + v) '' Pbar)
    (hT_bdd : IsBounded T_y)
    (hPbar_bdd : IsBounded Pbar)
    (hPbar'_ne_top : ENat.toENNReal (dyadicCoveringNumber δ Pbar') ≠ ⊤)
    (h_raw_proj_bound : Nreal δ (Set.image (fun q : EuclideanSpace ℝ (Fin 2) => q 0 * y + q 1) T_y) ≤
        ENNReal.ofReal (δ ^ (-(L_exp * η))) *
          ENNReal.ofReal (Real.sqrt ((ENat.toENNReal (dyadicCoveringNumber δ Pbar)).toReal))) :
    Nreal δ (Set.image (fun q : EuclideanSpace ℝ (Fin 2) => q 0 * y + q 1) T_y') ≤
      ENNReal.ofReal (4 : ℝ) * ENNReal.ofReal (δ ^ (-(L_exp * η))) *
        ENNReal.ofReal (Real.sqrt ((ENat.toENNReal (dyadicCoveringNumber δ Pbar')).toReal)) := by
  let π_y : EuclideanSpace ℝ (Fin 2) → ℝ := fun q => q 0 * y + q 1
  let Nbar := ENat.toENNReal (dyadicCoveringNumber δ Pbar)
  let Nbar' := ENat.toENNReal (dyadicCoveringNumber δ Pbar')

  -- Step 1: Projection translation bound (factor 2)
  have h1 : Nreal δ (Set.image π_y T_y') ≤ (2 : ENNReal) * Nreal δ (Set.image π_y T_y) :=
    raw_proj_translation_bound hδ_pos v hT'_eq hT_bdd

  -- Step 2: Reverse Pbar translation bound: Nbar ≤ 4 * Nbar'
  have hPbar_eq_rev : Pbar = (fun p : EuclideanSpace ℝ (Fin 2) => p - v) '' Pbar' := by
    have h_set_eq : (fun p : EuclideanSpace ℝ (Fin 2) => p - v) '' ((fun p => p + v) '' Pbar) = Pbar := by
      ext z
      simp only [Set.mem_image]
      constructor
      · rintro ⟨w, ⟨p, hp, rfl⟩, rfl⟩
        simpa using hp
      · intro hz
        refine ⟨z + v, ⟨z, hz, by simp⟩, by simp⟩
    rw [hPbar'_eq]
    exact h_set_eq.symm
  have hPbar'_bdd : IsBounded Pbar' := by
    rw [hPbar'_eq]
    have h_lip : LipschitzWith 1 (fun p : EuclideanSpace ℝ (Fin 2) => p + v) := by
      intro x y
      have h : dist (x + v) (y + v) = dist x y := by
        simp [dist_eq_norm]
      rw [edist_dist, edist_dist, h]
      simp
    exact h_lip.isBounded_image hPbar_bdd
  have h2_nat : dyadicCoveringNumber δ Pbar ≤ 4 * dyadicCoveringNumber δ Pbar' := by
    rw [hPbar_eq_rev]
    exact dyadic_cover_translate2d_le_four hδ_pos (-v) hPbar'_bdd
  have hPbar'_nat_ne_top : dyadicCoveringNumber δ Pbar' ≠ ⊤ := by
    intro h
    have h' : Nbar' = ⊤ := by
      simp only [Nbar', h]
      <;> simp
    exact hPbar'_ne_top h'
  have h_exists : ∃ (m : ℕ), (m : ℕ∞) = dyadicCoveringNumber δ Pbar' :=
    ENat.ne_top_iff_exists.mp hPbar'_nat_ne_top
  rcases h_exists with ⟨n, hn'⟩
  have hn : dyadicCoveringNumber δ Pbar' = (n : ℕ∞) := hn'.symm
  have h2 : Nbar ≤ (4 : ENNReal) * Nbar' := by
    have h21 : Nbar ≤ ENat.toENNReal (4 * dyadicCoveringNumber δ Pbar') :=
      ENat.toENNReal_mono h2_nat
    have h22 : ENat.toENNReal (4 * dyadicCoveringNumber δ Pbar') = (4 : ENNReal) * Nbar' := by
      rw [hn]
      have h221 : (4 * (n : ℕ∞)) = ↑(4 * n) := by norm_cast
      rw [h221]
      have h222 : ENat.toENNReal (↑(4 * n)) = (↑(4 * n) : ENNReal) := by simp
      rw [h222]
      have h223 : Nbar' = (↑n : ENNReal) := by
        unfold Nbar'
        rw [hn]
        <;> simp
      rw [h223]
      <;> norm_cast
    rw [h22] at h21
    exact h21

  -- Step 3: Convert to Real and take sqrt
  have hNbar'_ne_top : Nbar' ≠ ⊤ := hPbar'_ne_top
  have hNbar_ne_top : Nbar ≠ ⊤ := by
    have h : Nbar ≤ (4 : ENNReal) * Nbar' := h2
    have h5 : (4 : ENNReal) * Nbar' ≠ ⊤ := mul_ne_top (by norm_num) hNbar'_ne_top
    exact ne_top_of_le_ne_top h5 h

  have h3 : Nbar.toReal ≤ ((4 : ENNReal) * Nbar').toReal :=
    (ENNReal.toReal_le_toReal hNbar_ne_top (mul_ne_top (by norm_num) hNbar'_ne_top)).mpr h2
  have h3' : ((4 : ENNReal) * Nbar').toReal = (4 : ℝ) * Nbar'.toReal := by
    have h_mul : ((4 : ENNReal) * Nbar').toReal = (4 : ENNReal).toReal * Nbar'.toReal := by
      rw [ENNReal.toReal_mul]
    rw [h_mul]
    have h4 : (4 : ENNReal).toReal = (4 : ℝ) := by simp
    rw [h4]
  have h3'' : Nbar.toReal ≤ (4 : ℝ) * Nbar'.toReal := by
    rw [h3'] at h3
    exact h3
  have h4 : Real.sqrt Nbar.toReal ≤ 2 * Real.sqrt Nbar'.toReal := by
    have h7 : Real.sqrt Nbar.toReal ≤ Real.sqrt ((4 : ℝ) * Nbar'.toReal) := Real.sqrt_le_sqrt h3''
    have h8 : Real.sqrt ((4 : ℝ) * Nbar'.toReal) = 2 * Real.sqrt Nbar'.toReal := by
      rw [Real.sqrt_mul (by positivity)] <;> norm_num
    rw [h8] at h7
    exact h7

  -- Step 4: Combine all bounds
  have h_pos2 : 0 ≤ (2 : ℝ) := by positivity
  have h_ofReal_mul2 : ENNReal.ofReal (2 * Real.sqrt Nbar'.toReal) =
      (2 : ENNReal) * ENNReal.ofReal (Real.sqrt Nbar'.toReal) := by
    have h9 : ENNReal.ofReal ((2 : ℝ) * Real.sqrt Nbar'.toReal) =
        ENNReal.ofReal (2 : ℝ) * ENNReal.ofReal (Real.sqrt Nbar'.toReal) :=
      ENNReal.ofReal_mul h_pos2
    rw [h9]
    norm_cast

  have h7 : ENNReal.ofReal (Real.sqrt Nbar.toReal) ≤
      (2 : ENNReal) * ENNReal.ofReal (Real.sqrt Nbar'.toReal) := by
    have h71 : ENNReal.ofReal (Real.sqrt Nbar.toReal) ≤
        ENNReal.ofReal (2 * Real.sqrt Nbar'.toReal) := ENNReal.ofReal_le_ofReal h4
    rw [h_ofReal_mul2] at h71
    exact h71

  have h5 : Nreal δ (Set.image π_y T_y') ≤
      (2 : ENNReal) * (ENNReal.ofReal (δ ^ (-(L_exp * η))) *
        ENNReal.ofReal (Real.sqrt Nbar.toReal)) := by
    calc Nreal δ (Set.image π_y T_y')
      ≤ (2 : ENNReal) * Nreal δ (Set.image π_y T_y) := h1
    _ ≤ (2 : ENNReal) * (ENNReal.ofReal (δ ^ (-(L_exp * η))) *
          ENNReal.ofReal (Real.sqrt Nbar.toReal)) := by gcongr

  have h6 : (2 : ENNReal) * (ENNReal.ofReal (δ ^ (-(L_exp * η))) *
        ENNReal.ofReal (Real.sqrt Nbar.toReal)) ≤
      ENNReal.ofReal (4 : ℝ) * ENNReal.ofReal (δ ^ (-(L_exp * η))) *
        ENNReal.ofReal (Real.sqrt Nbar'.toReal) := by
    let A := ENNReal.ofReal (δ ^ (-(L_exp * η)))
    let B1 := ENNReal.ofReal (Real.sqrt Nbar.toReal)
    let B2 := ENNReal.ofReal (Real.sqrt Nbar'.toReal)
    have h_alg1 : (2 : ENNReal) * (A * B1) = A * ((2 : ENNReal) * B1) := by ac_rfl
    have h_alg2 : A * ((2 : ENNReal) * ((2 : ENNReal) * B2)) =
        (4 : ENNReal) * A * B2 := by
      have h10 : (2 : ENNReal) * (2 : ENNReal) = (4 : ENNReal) := by norm_num
      have h : A * ((2 : ENNReal) * ((2 : ENNReal) * B2)) = A * (((2 : ENNReal) * (2 : ENNReal)) * B2) := by ac_rfl
      rw [h, h10]
      ac_rfl
    rw [h_alg1]
    have h7 : B1 ≤ (2 : ENNReal) * B2 := by
      have h71 : B1 ≤ ENNReal.ofReal (2 * Real.sqrt Nbar'.toReal) := ENNReal.ofReal_le_ofReal h4
      rw [h_ofReal_mul2] at h71
      exact h71
    have h8 : A * ((2 : ENNReal) * B1) ≤ A * ((2 : ENNReal) * ((2 : ENNReal) * B2)) := by
      gcongr
    rw [h_alg2] at h8
    have h9 : (4 : ENNReal) = ENNReal.ofReal (4 : ℝ) := by simp
    rw [h9] at h8
    exact h8

  exact le_trans h5 h6

end ProductLikeIncidence.ProductReduction
