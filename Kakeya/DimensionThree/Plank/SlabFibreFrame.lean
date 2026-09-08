/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.SlabTubeEssentialDistinctness

/-!
# Anisotropic frame confinement of two fibre prisms

The six off-diagonal frame entries of one fibre prism against another, in the symmetric
anisotropic form that `Plank.card_le_of_anisotropicConfined_pairwiseED` consumes.

The input is a *slab profile* for the comparison vector `v = Q.basis 2 - t • Q₀.basis 2`: its
components in the frame of the ambient slab `S` are bounded by `(A θ b, A b, A b)`, and the
comparison scalar satisfies `|t⁻¹| ≤ T`. Together with the tangency of both prisms to `S` this
pins every off-diagonal entry at the right anisotropic scale.

Split off from `Kakeya.DimensionThree.Plank.SlabTubeEssentialDistinctness` purely for build granularity; the
generic ingredients (`Plank.abs_inner_short_long_le`, `Plank.abs_inner_short_profile_le`,
`Plank.abs_inner_ref_longAxis_le`, `Plank.inner_longAxis_eq_of_orthogonal`,
`Plank.norm_le_of_slab_profile`, `Plank.frame_confined_of_entries`) all live there.
-/

@[expose] public section

open MeasureTheory Kakeya
open scoped NNReal Real Classical

noncomputable section

namespace Plank

variable {θ b : ℝ≥0} {hθ1 : θ ≤ 1} {hb1 : b ≤ 1} (S : Slab θ hθ1)
  (Q Q₀ : ThickenedPlank θ b hθ1 hb1) {Ctan A T t : ℝ}

/-- The `(0,1)` entry: `Q`'s short axis against `Q₀`'s first long axis. -/
theorem entry01_le (hCtan : 0 ≤ Ctan)
    (htanQ : ∀ j : Fin 3, j ≠ 0 → |inner ℝ (Q.basis 0) (S.basis j)| ≤ Ctan * (θ : ℝ))
    (hnrmQ₀ : ∀ j : Fin 3, j ≠ 0 → |inner ℝ (S.basis 0) (Q₀.basis j)| ≤ Ctan * (θ : ℝ)) :
    |inner ℝ (Q.basis 0) (Q₀.basis 1)| ≤ 3 * Ctan * (θ : ℝ) :=
  abs_inner_short_long_le S hCtan (Q.basis 0) (Q₀.basis 1)
    (Q.basis.norm_eq_one 0) (Q₀.basis.norm_eq_one 1)
    (htanQ 1 (by decide)) (htanQ 2 (by decide)) (hnrmQ₀ 1 (by decide))

/-- The `(1,0)` entry: `Q`'s first long axis against `Q₀`'s short axis. -/
theorem entry10_le (hCtan : 0 ≤ Ctan)
    (htanQ₀ : ∀ j : Fin 3, j ≠ 0 → |inner ℝ (Q₀.basis 0) (S.basis j)| ≤ Ctan * (θ : ℝ))
    (hnrmQ : ∀ j : Fin 3, j ≠ 0 → |inner ℝ (S.basis 0) (Q.basis j)| ≤ Ctan * (θ : ℝ)) :
    |inner ℝ (Q.basis 1) (Q₀.basis 0)| ≤ 3 * Ctan * (θ : ℝ) := by
  rw [real_inner_comm]
  exact abs_inner_short_long_le S hCtan (Q₀.basis 0) (Q.basis 1)
    (Q₀.basis.norm_eq_one 0) (Q.basis.norm_eq_one 1)
    (htanQ₀ 1 (by decide)) (htanQ₀ 2 (by decide)) (hnrmQ 1 (by decide))

/-- The `(0,2)` entry: `Q`'s short axis against `Q₀`'s long axis, obtained by inverting the
comparison scalar. -/
theorem entry02_le (hCtan : 0 ≤ Ctan) (hA : 0 ≤ A) (ht0 : t ≠ 0) (htinv : |t⁻¹| ≤ T)
    (htanQ : ∀ j : Fin 3, j ≠ 0 → |inner ℝ (Q.basis 0) (S.basis j)| ≤ Ctan * (θ : ℝ))
    (hv0 : |inner ℝ (S.basis 0) (Q.basis 2 - t • Q₀.basis 2)| ≤ A * (θ : ℝ) * (b : ℝ))
    (hv1 : |inner ℝ (S.basis 1) (Q.basis 2 - t • Q₀.basis 2)| ≤ A * (b : ℝ))
    (hv2 : |inner ℝ (S.basis 2) (Q.basis 2 - t • Q₀.basis 2)| ≤ A * (b : ℝ)) :
    |inner ℝ (Q.basis 0) (Q₀.basis 2)| ≤ T * (A * (1 + 2 * Ctan) * (θ : ℝ) * (b : ℝ)) := by
  have horth : inner ℝ (Q.basis 0) (Q.basis 2) = (0 : ℝ) := Q.basis.orthonormal.2 (by decide)
  exact abs_inner_ref_longAxis_le Q Q₀ ht0 htinv (Q.basis 0) horth
    (abs_inner_short_profile_le S hCtan hA (Q.basis 0) (Q.basis 2 - t • Q₀.basis 2)
      (Q.basis.norm_eq_one 0) (htanQ 1 (by decide)) (htanQ 2 (by decide)) hv0 hv1 hv2)

/-- The `(2,0)` entry: `Q`'s long axis against `Q₀`'s short axis. -/
theorem entry20_le (hCtan : 0 ≤ Ctan) (hA : 0 ≤ A)
    (htanQ₀ : ∀ j : Fin 3, j ≠ 0 → |inner ℝ (Q₀.basis 0) (S.basis j)| ≤ Ctan * (θ : ℝ))
    (hv0 : |inner ℝ (S.basis 0) (Q.basis 2 - t • Q₀.basis 2)| ≤ A * (θ : ℝ) * (b : ℝ))
    (hv1 : |inner ℝ (S.basis 1) (Q.basis 2 - t • Q₀.basis 2)| ≤ A * (b : ℝ))
    (hv2 : |inner ℝ (S.basis 2) (Q.basis 2 - t • Q₀.basis 2)| ≤ A * (b : ℝ)) :
    |inner ℝ (Q.basis 2) (Q₀.basis 0)| ≤ A * (1 + 2 * Ctan) * (θ : ℝ) * (b : ℝ) := by
  have horth : inner ℝ (Q₀.basis 2) (Q₀.basis 0) = (0 : ℝ) := Q₀.basis.orthonormal.2 (by decide)
  rw [inner_longAxis_eq_of_orthogonal Q Q₀ t (Q₀.basis 0) horth,
    real_inner_comm (Q₀.basis 0) (Q.basis 2 - t • Q₀.basis 2)]
  exact abs_inner_short_profile_le S hCtan hA (Q₀.basis 0) (Q.basis 2 - t • Q₀.basis 2)
    (Q₀.basis.norm_eq_one 0) (htanQ₀ 1 (by decide)) (htanQ₀ 2 (by decide)) hv0 hv1 hv2

/-- The `(1,2)` entry: `Q`'s first long axis against `Q₀`'s long axis. -/
theorem entry12_le (hA : 0 ≤ A) (ht0 : t ≠ 0) (htinv : |t⁻¹| ≤ T)
    (hv0 : |inner ℝ (S.basis 0) (Q.basis 2 - t • Q₀.basis 2)| ≤ A * (θ : ℝ) * (b : ℝ))
    (hv1 : |inner ℝ (S.basis 1) (Q.basis 2 - t • Q₀.basis 2)| ≤ A * (b : ℝ))
    (hv2 : |inner ℝ (S.basis 2) (Q.basis 2 - t • Q₀.basis 2)| ≤ A * (b : ℝ)) :
    |inner ℝ (Q.basis 1) (Q₀.basis 2)| ≤ T * (3 * A * (b : ℝ)) := by
  have hnv : ‖Q.basis 2 - t • Q₀.basis 2‖ ≤ 3 * A * (b : ℝ) :=
    norm_le_of_slab_profile S hA _ hv0 hv1 hv2
  have hCS : |inner ℝ (Q.basis 1) (Q.basis 2 - t • Q₀.basis 2)| ≤ 3 * A * (b : ℝ) := by
    refine le_trans ?_ hnv
    have h := abs_real_inner_le_norm (Q.basis 1) (Q.basis 2 - t • Q₀.basis 2)
    rwa [OrthonormalBasis.norm_eq_one Q.basis 1, one_mul] at h
  have horth : inner ℝ (Q.basis 1) (Q.basis 2) = (0 : ℝ) := Q.basis.orthonormal.2 (by decide)
  exact abs_inner_ref_longAxis_le Q Q₀ ht0 htinv (Q.basis 1) horth hCS

/-- The `(2,1)` entry: `Q`'s long axis against `Q₀`'s first long axis. -/
theorem entry21_le (hA : 0 ≤ A)
    (hv0 : |inner ℝ (S.basis 0) (Q.basis 2 - t • Q₀.basis 2)| ≤ A * (θ : ℝ) * (b : ℝ))
    (hv1 : |inner ℝ (S.basis 1) (Q.basis 2 - t • Q₀.basis 2)| ≤ A * (b : ℝ))
    (hv2 : |inner ℝ (S.basis 2) (Q.basis 2 - t • Q₀.basis 2)| ≤ A * (b : ℝ)) :
    |inner ℝ (Q.basis 2) (Q₀.basis 1)| ≤ 3 * A * (b : ℝ) := by
  have horth : inner ℝ (Q₀.basis 2) (Q₀.basis 1) = (0 : ℝ) := Q₀.basis.orthonormal.2 (by decide)
  rw [inner_longAxis_eq_of_orthogonal Q Q₀ t (Q₀.basis 1) horth]
  have hnv : ‖Q.basis 2 - t • Q₀.basis 2‖ ≤ 3 * A * (b : ℝ) :=
    norm_le_of_slab_profile S hA _ hv0 hv1 hv2
  refine le_trans ?_ hnv
  have h := abs_real_inner_le_norm (Q.basis 2 - t • Q₀.basis 2) (Q₀.basis 1)
  rwa [OrthonormalBasis.norm_eq_one Q₀.basis 1, mul_one] at h

/-- **Anisotropic frame confinement from a slab profile.** Two fibre prisms tangential to `S`,
whose long axes differ by a vector `v = Q.basis 2 - t • Q₀.basis 2` with the anisotropic profile
`(A θ b, A b, A b)` in the `S` frame and with `|t⁻¹| ≤ T`, satisfy the symmetric anisotropic
confinement of `Plank.card_le_of_anisotropicConfined_pairwiseED` at the weights `(θ b, b, 1)`.

The six off-diagonal entries split into three kinds.
* `(0,1)` and `(1,0)` need only tangency: both are `O(Ctan θ)`, and the weight ratio there is
  `min / max = θ b / b = θ`.
* `(0,2)` and `(2,0)` are `O(A (1 + 2 Ctan) θ b)`, using `⟪Q.basis 0, Q.basis 2⟫ = 0` resp.
  `⟪Q₀.basis 2, Q₀.basis 0⟫ = 0` to replace the long axis by `v`; the weight ratio is `θ b / 1`.
* `(1,2)` and `(2,1)` are `O(A b)` by Cauchy–Schwarz and `‖v‖ ≤ 3 A b`; the weight ratio is
  `b / 1`. -/
theorem frame_confined_of_slab_profile (hb0 : 0 < b)
    (hCtan : 0 ≤ Ctan) (hA : 0 ≤ A) (hT : 1 ≤ T)
    (htanQ : ∀ j : Fin 3, j ≠ 0 → |inner ℝ (Q.basis 0) (S.basis j)| ≤ Ctan * (θ : ℝ))
    (htanQ₀ : ∀ j : Fin 3, j ≠ 0 → |inner ℝ (Q₀.basis 0) (S.basis j)| ≤ Ctan * (θ : ℝ))
    (hnrmQ : ∀ j : Fin 3, j ≠ 0 → |inner ℝ (S.basis 0) (Q.basis j)| ≤ Ctan * (θ : ℝ))
    (hnrmQ₀ : ∀ j : Fin 3, j ≠ 0 → |inner ℝ (S.basis 0) (Q₀.basis j)| ≤ Ctan * (θ : ℝ))
    (ht0 : t ≠ 0) (htinv : |t⁻¹| ≤ T)
    (hv0 : |inner ℝ (S.basis 0) (Q.basis 2 - t • Q₀.basis 2)| ≤ A * (θ : ℝ) * (b : ℝ))
    (hv1 : |inner ℝ (S.basis 1) (Q.basis 2 - t • Q₀.basis 2)| ≤ A * (b : ℝ))
    (hv2 : |inner ℝ (S.basis 2) (Q.basis 2 - t • Q₀.basis 2)| ≤ A * (b : ℝ)) :
    ∀ j k : Fin 3, j ≠ k →
      max ((![θ * b, b, 1] j : ℝ≥0) : ℝ) ((![θ * b, b, 1] k : ℝ≥0) : ℝ)
          * |inner ℝ (Q.basis j) (Q₀.basis k)|
        ≤ (3 * Ctan + 4 * T * A * (1 + 2 * Ctan) + 4 * T * A)
            * min ((![θ * b, b, 1] j : ℝ≥0) : ℝ) ((![θ * b, b, 1] k : ℝ≥0) : ℝ) := by
  have hθ0 : (0:ℝ) ≤ (θ : ℝ) := (θ : ℝ≥0).coe_nonneg
  have hb0' : (0:ℝ) ≤ (b : ℝ) := (b : ℝ≥0).coe_nonneg
  have hT0 : (0:ℝ) ≤ T := le_trans zero_le_one hT
  let R : ℝ := 3 * Ctan + 4 * T * A * (1 + 2 * Ctan) + 4 * T * A
  have hR0 : (0:ℝ) ≤ R := by
    dsimp [R]
    positivity
  have h3C_le_R : 3 * Ctan ≤ R := by
    dsimp [R]
    nlinarith [show (0:ℝ) ≤ 4 * T * A * (1 + 2 * Ctan) by positivity,
      show (0:ℝ) ≤ 4 * T * A by positivity]
  have hTA1C_le_R : T * A * (1 + 2 * Ctan) ≤ R := by
    dsimp [R]
    nlinarith [show (0:ℝ) ≤ 3 * Ctan by positivity,
      show (0:ℝ) ≤ 3 * T * A * (1 + 2 * Ctan) by positivity,
      show (0:ℝ) ≤ 4 * T * A by positivity]
  have hA1C_le_R : A * (1 + 2 * Ctan) ≤ R := by
    dsimp [R]
    nlinarith [show (0:ℝ) ≤ 3 * Ctan by positivity,
      show (0:ℝ) ≤ 4 * T * A by positivity,
      mul_nonneg (by nlinarith : (0:ℝ) ≤ 4 * T - 1)
        (by positivity : (0:ℝ) ≤ A * (1 + 2 * Ctan))]
  have h3TA_le_R : 3 * T * A ≤ R := by
    dsimp [R]
    nlinarith [show (0:ℝ) ≤ 3 * Ctan by positivity,
      show (0:ℝ) ≤ 4 * T * A * (1 + 2 * Ctan) by positivity,
      show (0:ℝ) ≤ T * A by positivity]
  have h3A_le_R : 3 * A ≤ R := by
    dsimp [R]
    nlinarith [show (0:ℝ) ≤ 3 * Ctan by positivity,
      show (0:ℝ) ≤ 4 * T * A * (1 + 2 * Ctan) by positivity,
      mul_nonneg (by nlinarith : (0:ℝ) ≤ 4 * T - 3) hA]
  refine frame_confined_of_entries Q Q₀ hb0 hR0 ?_ ?_ ?_ ?_ ?_ ?_
  · have h := entry01_le S Q Q₀ hCtan htanQ hnrmQ₀
    refine le_trans h ?_
    simpa [R] using mul_le_mul_of_nonneg_right h3C_le_R hθ0
  · have h := entry10_le S Q Q₀ hCtan htanQ₀ hnrmQ
    refine le_trans h ?_
    simpa [R] using mul_le_mul_of_nonneg_right h3C_le_R hθ0
  · have h := entry02_le S Q Q₀ hCtan hA ht0 htinv htanQ hv0 hv1 hv2
    refine le_trans h ?_
    simpa [R, mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_right hTA1C_le_R (mul_nonneg hθ0 hb0')
  · have h := entry20_le S Q Q₀ hCtan hA htanQ₀ hv0 hv1 hv2
    refine le_trans h ?_
    simpa [R, mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_right hA1C_le_R (mul_nonneg hθ0 hb0')
  · have h := entry12_le S Q Q₀ hA ht0 htinv hv0 hv1 hv2
    refine le_trans h ?_
    simpa [R, mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_right h3TA_le_R hb0'
  · have h := entry21_le S Q Q₀ hA hv0 hv1 hv2
    refine le_trans h ?_
    simpa [R, mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_right h3A_le_R hb0'

end Plank

end
