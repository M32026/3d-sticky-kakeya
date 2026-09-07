module

/-
# Chart Full Lambda — Sector-wise Projective Scaling Coefficients

After the projective cross-ratio transform, the raw projection is:
  `p 0 * x(y) + p 1 = λ(y) * (q 0 * y + q 1)`
where `λ(y) = (θ2-θ3)/(θ2-y)`.

The four-sector chart absorbs the coefficient into the sector map:
- Sector 0 (0 ≤ x ≤ 1):   effective coeff = λ(y)
- Sector 1 (x ≥ 1):       effective coeff = λ(y)/x(y) = (θ3-θ1)/(y-θ1)
- Sector 2 (-1 ≤ x ≤ 0):  effective coeff = λ(y)
- Sector 3 (x ≤ -1):      effective coeff = λ(y)/x(y) = (θ3-θ1)/(y-θ1)

For `y ∈ [θ1, θ2)` (the natural cross-ratio domain), only sectors 0 and 1
are non-empty, and both coefficients satisfy `0 < c ≤ 1`.

For `y < θ1`, sector 2 has `0 < λ(y) < 1`.
For `y > θ2`, sector 3 has `0 < λ(y)/x(y) < 1`.

## Main results

1. `chartFullLambda` — piecewise definition by sector
2. `chartFullLambda_bound_sector0` — `0 < λ(y) ≤ 1` for `θ1 ≤ y ≤ θ3`
3. `chartFullLambda_bound_sector1` — `0 < λ/x ≤ 1` for `θ3 ≤ y < θ2`
4. `chartFullLambda_bound_sector2_below` — `0 < λ(y) < 1` for `y < θ1`
5. `chartFullLambda_bound_sector3_above` — `0 < λ/x < 1` for `y > θ2`
6. `sector_projection_nreal_bound` — covering number bound for scaled fiber
-/

public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.CoveringNumberScaling
public import MyLeanRepo.ProductLikeIncidence.Phase7ScaledProjections
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open Set ENNReal Bornology Classical

namespace ProductLikeIncidence.ProductReduction

/-- The effective projective scaling coefficient after sector chart absorption.

- Sector 0 (0 ≤ x ≤ 1):   `λ(y) = (θ2-θ3)/(θ2-y)`
- Sector 1 (x ≥ 1):       `λ(y)/x(y) = (θ3-θ1)/(y-θ1)`
- Sector 2 (-1 ≤ x ≤ 0):  `λ(y) = (θ2-θ3)/(θ2-y)`
- Sector 3 (x ≤ -1):      `λ(y)/x(y) = (θ3-θ1)/(y-θ1)`
-/
def chartFullLambda (i : Fin 4) (y _θ1 θ3 θ2 : ℝ)
    (x : ℝ → ℝ) : ℝ :=
  match i with
  | 0 => (θ2 - θ3) / (θ2 - y)
  | 1 => ((θ2 - θ3) / (θ2 - y)) / x y
  | 2 => (θ2 - θ3) / (θ2 - y)
  | 3 => ((θ2 - θ3) / (θ2 - y)) / x y

/-- Sector projection set: `chartFullLambda(i,y) · π_y(T_y_points)`.

`π_y(T_y_points) = {q 0 * y + q 1 | q ∈ T_y_points}`. -/
def sectorProjectionSet (i : Fin 4) (y θ1 θ3 θ2 : ℝ)
    (x : ℝ → ℝ)
    (T_y_points : Set (EuclideanSpace ℝ (Fin 2))) : Set ℝ :=
  let c := chartFullLambda i y θ1 θ3 θ2 x
  scaleSet c (Set.image (fun q : EuclideanSpace ℝ (Fin 2) => q 0 * y + q 1) T_y_points)

/-! ========================================================================
   Sector coefficient bounds
   ======================================================================== -/

/-- Sector 0 bound: if `θ1 ≤ y ≤ θ3`, then `0 < chartFullLambda(0,y) ≤ 1`. -/
lemma chartFullLambda_bound_sector0
    {θ1 θ3 θ2 y : ℝ} (h13 : θ1 < θ3) (h32 : θ3 < θ2)
    (hy1 : θ1 ≤ y) (hy3 : y ≤ θ3)
    (x : ℝ → ℝ) :
    0 < chartFullLambda 0 y θ1 θ3 θ2 x ∧
        chartFullLambda 0 y θ1 θ3 θ2 x ≤ 1 := by
  simpa [chartFullLambda] using
    phase7_lambda_le_one_on_lower_sector h13 h32 hy1 hy3

/-- Sector 1 bound: if `θ3 ≤ y < θ2`, then `0 < chartFullLambda(1,y) ≤ 1`. -/
lemma chartFullLambda_bound_sector1
    {θ1 θ3 θ2 y : ℝ} (h13 : θ1 < θ3) (h32 : θ3 < θ2)
    (hy3 : θ3 ≤ y) (hy2 : y < θ2)
    (x : ℝ → ℝ)
    (hx_formula : ∀ y, x y = ((θ2 - θ3) * (y - θ1)) / ((θ3 - θ1) * (θ2 - y))) :
    0 < chartFullLambda 1 y θ1 θ3 θ2 x ∧
        chartFullLambda 1 y θ1 θ3 θ2 x ≤ 1 := by
  simpa [chartFullLambda] using
    phase7_lambda_over_x_le_one_on_upper_sector h13 h32 hy3 hy2 x hx_formula

/-- Sector 2 bound for `y < θ1`: `0 < chartFullLambda(2,y) < 1`.

Note: For `y > θ2`, the bound `|λ(y)| ≤ 1` does NOT follow from the sector
condition `-1 ≤ x(y) ≤ 0` alone. Restrict to `y < θ1` or ensure `y ≥ 2θ2-θ3`. -/
lemma chartFullLambda_bound_sector2_below
    {θ1 θ3 θ2 y : ℝ} (h13 : θ1 < θ3) (h32 : θ3 < θ2)
    (hy : y < θ1)
    (x : ℝ → ℝ) :
    0 < chartFullLambda 2 y θ1 θ3 θ2 x ∧
        chartFullLambda 2 y θ1 θ3 θ2 x < 1 := by
  simpa [chartFullLambda] using
    phase7_lambda_lt_one_below_θ1 h13 h32 hy

/-- Sector 3 bound for `y > θ2`: `0 < chartFullLambda(3,y) < 1`.

Note: For `y < θ1`, the bound `|λ(y)/x(y)| ≤ 1` does NOT follow from the
sector condition `x(y) ≤ -1` alone. Restrict to `y > θ2` or ensure
`y ≤ 2θ1-θ3`. -/
lemma chartFullLambda_bound_sector3_above
    {θ1 θ3 θ2 y : ℝ} (h13 : θ1 < θ3) (h32 : θ3 < θ2)
    (hy : θ2 < y)
    (x : ℝ → ℝ)
    (hx_formula : ∀ y, x y = ((θ2 - θ3) * (y - θ1)) / ((θ3 - θ1) * (θ2 - y))) :
    0 < chartFullLambda 3 y θ1 θ3 θ2 x ∧
        chartFullLambda 3 y θ1 θ3 θ2 x < 1 := by
  simpa [chartFullLambda] using
    phase7_lambda_over_x_lt_one_above_θ2 h13 h32 hy x hx_formula



/-! ========================================================================
   Covering number bound for sector projections
   ======================================================================== -/

/-- Covering number bound for a sector projection set.

If `0 < chartFullLambda(i,y) ≤ 1` and the raw fiber projection is bounded,
then `Nreal δ (sectorProjectionSet i ...) ≤ 3 * Nreal δ (raw fiber)`.

The constant 3 comes from `Nreal_scale_bounded` with `C_max = 1`:
`⌈1⌉ + 2 = 3`. -/
lemma sectorProjection_nreal_bound
    {δ : ℝ} (hδ : 0 < δ)
    {i : Fin 4} {y θ1 θ3 θ2 : ℝ} {x : ℝ → ℝ}
    {T_y_points : Set (EuclideanSpace ℝ (Fin 2))}
    (h_coeff_pos : 0 < chartFullLambda i y θ1 θ3 θ2 x)
    (h_coeff_le_one : chartFullLambda i y θ1 θ3 θ2 x ≤ 1)
    (h_fiber_bdd : IsBounded (Set.image (fun q : EuclideanSpace ℝ (Fin 2) => q 0 * y + q 1) T_y_points)) :
    Nreal δ (sectorProjectionSet i y θ1 θ3 θ2 x T_y_points) ≤
        3 * Nreal δ (Set.image (fun q : EuclideanSpace ℝ (Fin 2) => q 0 * y + q 1) T_y_points) := by
  let c := chartFullLambda i y θ1 θ3 θ2 x
  let A := Set.image (fun q : EuclideanSpace ℝ (Fin 2) => q 0 * y + q 1) T_y_points
  have hc_pos : 0 < c := h_coeff_pos
  have hc_le_one : c ≤ 1 := h_coeff_le_one
  have h_main : Nreal δ (scaleSet c A) ≤ (Nat.ceil (1 : ℝ) + 2 : ENNReal) * Nreal δ A :=
    Nreal_scale_bounded hδ hc_pos (by norm_num) hc_le_one h_fiber_bdd
  have h_const : (Nat.ceil (1 : ℝ) + 2 : ENNReal) = (3 : ENNReal) := by
    norm_num
  rw [h_const] at h_main
  exact h_main

end ProductLikeIncidence.ProductReduction
