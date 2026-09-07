module

/-
# S_pre Shift Bridge Lemma

Connects the normalized `S_pre'` (using translated point sets `T_y_points'`)
to the original `S_pre_orig` (using `T_y_points`) via the Resolution A
translation shift.

This is one of the two H5→H6 bridge inputs needed by `glue_H5_to_H6`.

## Key result

Given Resolution A data `(v_resA, k, j)` and point sets related by
`T_y_points' y = (fun q => q - v_resA) '' T_y_points y`, the thickened
scaled projections satisfy:

`S_pre' y = {z | z + k*x(y) + j ∈ S_pre_orig y}`

for all `y`, where both are `Set.univ` at the pole `y = θ2`.

## Proof

- Case `y = θ2`: both sides are `Set.univ` by definition.
- Case `y ≠ θ2`:
  1. `resolutionA_projection_identity` shifts the scaled projection set
     by `k*x(y) + j`.
  2. `intervalThicken_translate_sub` commutes thickening with translation.
-/

public import MyLeanRepo.ProductLikeIncidence.Phase7ScaledProjections
public import MyLeanRepo.ProductLikeIncidence.ThickeningCovering
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open Set

namespace ProductLikeIncidence.ProductReduction

/-- Thickening commutes with translation by `-shift`:
`intervalThicken ε (image (w ↦ w - shift) S) = {z | z + shift ∈ intervalThicken ε S}`. -/
lemma intervalThicken_translate_sub (ε shift : ℝ) (S : Set ℝ) :
    intervalThicken ε ((fun w : ℝ => w - shift) '' S) =
      {z : ℝ | z + shift ∈ intervalThicken ε S} := by
  have h_main : intervalThicken ε ((fun w : ℝ => w - shift) '' S) =
      (fun w : ℝ => w - shift) '' intervalThicken ε S := by
    ext z
    simp only [intervalThicken, thickenSet, mem_image, mem_setOf_eq]
    constructor
    · rintro ⟨a, ⟨b, hb, rfl⟩, hz⟩
      refine ⟨z + shift, ⟨b, hb, ?_⟩, by ring⟩
      have h_eq : (z + shift) - b = z - (b - shift) := by ring
      rw [h_eq]; exact hz
    · rintro ⟨y, ⟨a, ha, hya⟩, hz⟩
      refine ⟨a - shift, ⟨a, ha, rfl⟩, ?_⟩
      have h_z_eq : z = y - shift := hz.symm
      rw [h_z_eq]
      have h_eq : (y - shift) - (a - shift) = y - a := by ring
      rw [h_eq]; exact hya
  rw [h_main]
  ext z
  simp only [mem_image, mem_setOf_eq]
  constructor
  · rintro ⟨y, hy, rfl⟩
    have h : (y - shift) + shift = y := by ring
    rw [h]; exact hy
  · intro hz
    refine ⟨z + shift, hz, ?_⟩
    ring

/-- S_pre shift bridge: relates normalized thickened projection to original.

Given `T_y_points' y = (fun q => q - v_resA) '' T_y_points y`, define:
- `S_pre_orig y = if y = θ2 then univ else intervalThicken (r y) (proj y (T_y_points y))`
- `S_pre y = if y = θ2 then univ else intervalThicken (r y) (proj y (T_y_points' y))`

Then `S_pre y = {z | z + k*x(y) + j ∈ S_pre_orig y}` for all `y`. -/
lemma spre_shift_bridge
    {θ1 θ2 θ3 : ℝ} (h_ord13 : θ1 < θ3) (h_ord32 : θ3 < θ2)
    {k j : ℝ}
    {v_resA : EuclideanSpace ℝ (Fin 2)}
    (hv0 : v_resA 0 = k / (θ3 - θ1) - j / (θ2 - θ3))
    (hv1 : v_resA 1 = -k * θ1 / (θ3 - θ1) + j * θ2 / (θ2 - θ3))
    {x : ℝ → ℝ}
    (hx_formula : ∀ y, x y = ((θ2 - θ3) * (y - θ1)) / ((θ3 - θ1) * (θ2 - y)))
    (T_y_points : ℝ → Set (EuclideanSpace ℝ (Fin 2)))
    (T_y_points' : ℝ → Set (EuclideanSpace ℝ (Fin 2)))
    (hT'_eq : ∀ y, T_y_points' y = (fun q => q - v_resA) '' T_y_points y)
    (r : ℝ → ℝ) :
    ∀ y : ℝ,
      (if y = θ2 then Set.univ
       else intervalThicken (r y) (phase7ScaledProjection y θ2 θ3 (T_y_points' y))) =
      {z : ℝ | z + k * x y + j ∈
        (if y = θ2 then Set.univ
         else intervalThicken (r y) (phase7ScaledProjection y θ2 θ3 (T_y_points y)))} := by
  intro y
  by_cases hy_theta : y = θ2
  · -- Case y = θ2: both sides are Set.univ
    subst hy_theta
    simp
  · -- Case y ≠ θ2
    have h_y_ne : y ≠ θ2 := hy_theta
    have h_if1 : (if y = θ2 then Set.univ
       else intervalThicken (r y) (phase7ScaledProjection y θ2 θ3 (T_y_points' y))) =
      intervalThicken (r y) (phase7ScaledProjection y θ2 θ3 (T_y_points' y)) := by
      rw [if_neg h_y_ne]
    have h_if2 : (if y = θ2 then Set.univ
       else intervalThicken (r y) (phase7ScaledProjection y θ2 θ3 (T_y_points y))) =
      intervalThicken (r y) (phase7ScaledProjection y θ2 θ3 (T_y_points y)) := by
      rw [if_neg h_y_ne]
    rw [h_if1, h_if2]
    -- Translate the scaled projection using Resolution A identity
    have h_proj : phase7ScaledProjection y θ2 θ3 (T_y_points' y) =
        (fun w : ℝ => w - (k * x y + j)) ''
          phase7ScaledProjection y θ2 θ3 (T_y_points y) := by
      rw [hT'_eq y]
      have h := resolutionA_projection_identity h_ord13 h_ord32 h_y_ne
        v_resA hv0 hv1 (T_y_points y)
      -- h has shift = k * formula + j; rewrite formula → x y
      rw [← hx_formula y] at h
      exact h
    rw [h_proj]
    -- Commute thickening with translation
    have h_thicken := intervalThicken_translate_sub (r y) (k * x y + j)
      (phase7ScaledProjection y θ2 θ3 (T_y_points y))
    -- Goal has z + k * x y + j (= (z + k*x y) + j), h_thicken has z + (k*x y + j)
    have h_assoc : {z : ℝ | z + k * x y + j ∈ intervalThicken (r y) (phase7ScaledProjection y θ2 θ3 (T_y_points y))} =
        {z : ℝ | z + (k * x y + j) ∈ intervalThicken (r y) (phase7ScaledProjection y θ2 θ3 (T_y_points y))} := by
      ext z
      simp only [Set.mem_setOf_eq]
      have h_eq : (z + k * x y + j) = z + (k * x y + j) := by ring
      rw [h_eq]
    rw [h_assoc]
    exact h_thicken

end ProductLikeIncidence.ProductReduction
