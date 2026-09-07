module

/-
# Phase7 Scaled Projections

Provides scaled projection sets `S(y)` and sector-specific scaling bounds
for the Phase7 wiring.

The projective identity states:
  `p 0 * x y + p 1 = λ(y) * (q 0 * y + q 1)`
where `p = F q`, `λ(y) = (θ2 - θ3) / (θ2 - y)`, and
`x(y) = ((θ2-θ3)*(y-θ1))/((θ3-θ1)*(θ2-y))`.

After four-sector decomposition, the effective scaling coefficient is:
- Sectors 1,3 (|x| ≤ 1): `λ(y)`
- Sectors 2,4 (|x| ≥ 1): `λ(y)/x(y) = (θ3-θ1)/(y-θ1)`

For `y ∈ [θ1, θ2)`, both coefficients are positive and ≤ 1 on their
respective sectors.

## Main results

1. `Nreal_scale_bounded` — covering bound for `scaleSet c A`
2. `phase7_proj_incidence` — projective incidence algebra identity
3. `phase7_lambda_le_one_on_lower_sector` — `0 < λ(y) ≤ 1` when `θ1 ≤ y ≤ θ3`
4. `phase7_lambda_over_x_le_one_on_upper_sector` — `0 < λ(y)/x(y) ≤ 1` when `θ3 ≤ y < θ2`
5. `phase7_sector_effective_coeff_bound` — combined: effective coefficient in (0,1]
-/

public import MyLeanRepo.ProjectionBasic
public import MyLeanRepo.CoveringNumberScaling
public import MyLeanRepo.ProductLikeIncidence.DeltaSetTranslation
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open Set ENNReal Bornology Classical

namespace ProductLikeIncidence.ProductReduction

/-- Scaled projection set for direction `y`.

`S(y) = c(y) · {q 0 * y + q 1 | q ∈ T_y_points y}`
where `c(y) = (θ2 - θ3) / (θ2 - y)` is the projective scaling factor. -/
def phase7ScaledProjection (y θ2 θ3 : ℝ)
    (T_y_points : Set (EuclideanSpace ℝ (Fin 2))) : Set ℝ :=
  let c : ℝ := (θ2 - θ3) / (θ2 - y)
  scaleSet c (Set.image (fun q : EuclideanSpace ℝ (Fin 2) => q 0 * y + q 1) T_y_points)

/-- Covering number bound for a scaled projection.

If `0 < c ≤ C_max`, then `Nreal δ (scaleSet c A) ≤ (⌈C_max⌉ + 2) * Nreal δ A`.
For `c ≥ 1`, uses `Nreal_scale_up_upper`.
For `c < 1`, uses exact scaling + `Nreal_refining` (factor ≤ 2). -/
lemma Nreal_scale_bounded {δ c C_max : ℝ}
    (hδ : 0 < δ) (hc_pos : 0 < c) (hC_max_pos : 0 < C_max) (hc_le : c ≤ C_max)
    {A : Set ℝ} (hA : IsBounded A) :
    Nreal δ (scaleSet c A) ≤ (Nat.ceil C_max + 2 : ENNReal) * Nreal δ A := by
  by_cases h : c ≥ 1
  · -- c ≥ 1: use scale-up bound
    have h1 : Nreal δ (scaleSet c A) ≤ (Nat.ceil c + 1 : ENNReal) * Nreal δ A :=
      WeakTwoEndsSumProduct.Nreal_scale_up_upper hδ h hA
    have h2 : (Nat.ceil c + 1 : ENNReal) ≤ (Nat.ceil C_max + 2 : ENNReal) := by
      have h3 : Nat.ceil c ≤ Nat.ceil C_max := Nat.ceil_mono hc_le
      exact_mod_cast by linarith
    exact le_trans h1 (mul_le_mul_of_nonneg_right h2 (by positivity))
  · -- c < 1: N(δ, c·A) = N(δ/c, A) ≤ 2 * N(δ, A) by refining
    have hc_lt_one : c < 1 := by linarith
    have h1 : Nreal δ (scaleSet c A) = Nreal (δ / c) A :=
      WeakTwoEndsSumProduct.Nreal_scaling hδ hc_pos hA
    rw [h1]
    have h2 : 0 < δ / c := by positivity
    have h3 : δ ≤ δ / c := by
      have h4 : c < 1 := hc_lt_one
      have h5 : 0 < c := hc_pos
      calc δ / c ≥ δ / 1 := by gcongr
           _ = δ := by ring
    have h4 : Nreal (δ / c) A ≤ 2 * Nreal δ A :=
      WeakTwoEndsSumProduct.Nreal_refining hδ h2 h3 hA
    have h5 : (2 : ENNReal) ≤ (Nat.ceil C_max + 2 : ENNReal) := by
      have h6 : 0 ≤ Nat.ceil C_max := by positivity
      exact_mod_cast by linarith
    exact le_trans h4 (mul_le_mul_of_nonneg_right h5 (by positivity))

/-! ========================================================================
   Sector-specific scaling coefficient bounds
   ======================================================================== -/

/-- On the lower sector (`θ1 ≤ y ≤ θ3`), the projective scaling factor
`λ(y) = (θ2-θ3)/(θ2-y)` satisfies `0 < λ(y) ≤ 1`. -/
lemma phase7_lambda_le_one_on_lower_sector
    {θ1 θ3 θ2 y : ℝ} (_h13 : θ1 < θ3) (h32 : θ3 < θ2)
    (_hy1 : θ1 ≤ y) (hy3 : y ≤ θ3) :
    0 < (θ2 - θ3) / (θ2 - y) ∧ (θ2 - θ3) / (θ2 - y) ≤ 1 := by
  have h_denom_pos : 0 < θ2 - y := by linarith
  have h_num_pos : 0 < θ2 - θ3 := by linarith
  have h_pos : 0 < (θ2 - θ3) / (θ2 - y) := by positivity
  have h_le : (θ2 - θ3) / (θ2 - y) ≤ 1 := by
    rw [div_le_one (by linarith)]
    ; linarith
  exact ⟨h_pos, h_le⟩

/-- On the upper sector (`θ3 ≤ y < θ2`), the ratio
`λ(y)/x(y) = (θ3-θ1)/(y-θ1)` satisfies `0 < λ(y)/x(y) ≤ 1`. -/
lemma phase7_lambda_over_x_le_one_on_upper_sector
    {θ1 θ3 θ2 y : ℝ} (h13 : θ1 < θ3) (h32 : θ3 < θ2)
    (hy3 : θ3 ≤ y) (hy2 : y < θ2)
    (x : ℝ → ℝ)
    (hx_formula : ∀ y, x y = ((θ2 - θ3) * (y - θ1)) / ((θ3 - θ1) * (θ2 - y))) :
    0 < ((θ2 - θ3) / (θ2 - y)) / x y ∧
        ((θ2 - θ3) / (θ2 - y)) / x y ≤ 1 := by
  have h_y_sub_θ1_pos : 0 < y - θ1 := by linarith
  have h_θ3_sub_θ1_pos : 0 < θ3 - θ1 := by linarith
  have h_denom_pos : 0 < θ2 - y := by linarith
  have h_x_pos : 0 < x y := by
    rw [hx_formula y]
    have h1 : 0 < (θ2 - θ3) * (y - θ1) := by positivity
    have h2 : 0 < (θ3 - θ1) * (θ2 - y) := by positivity
    positivity
  have h_ratio_eq : ((θ2 - θ3) / (θ2 - y)) / x y = (θ3 - θ1) / (y - θ1) := by
    rw [hx_formula y]
    have h_num_pos : 0 < θ2 - θ3 := by linarith
    field_simp [h_denom_pos.ne', h_y_sub_θ1_pos.ne', h_θ3_sub_θ1_pos.ne', h_num_pos.ne']
  rw [h_ratio_eq]
  have h_pos : 0 < (θ3 - θ1) / (y - θ1) := by positivity
  have h_le : (θ3 - θ1) / (y - θ1) ≤ 1 := by
    rw [div_le_one (by linarith)]
    ; linarith
  exact ⟨h_pos, h_le⟩

/-- Below θ1, `λ(y) = (θ2-θ3)/(θ2-y)` satisfies `0 < λ(y) < 1`. -/
lemma phase7_lambda_lt_one_below_θ1
    {θ1 θ3 θ2 y : ℝ} (h13 : θ1 < θ3) (h32 : θ3 < θ2)
    (hy : y < θ1) :
    0 < (θ2 - θ3) / (θ2 - y) ∧ (θ2 - θ3) / (θ2 - y) < 1 := by
  have h_denom_pos : 0 < θ2 - y := by linarith
  have h_pos : 0 < (θ2 - θ3) / (θ2 - y) := by positivity
  have h_lt : (θ2 - θ3) / (θ2 - y) < 1 := by
    rw [div_lt_one (by linarith)]
    ; linarith
  exact ⟨h_pos, h_lt⟩

/-- Above θ2, `λ(y)/x(y) = (θ3-θ1)/(y-θ1)` satisfies `0 < λ(y)/x(y) < 1`. -/
lemma phase7_lambda_over_x_lt_one_above_θ2
    {θ1 θ3 θ2 y : ℝ} (h13 : θ1 < θ3) (h32 : θ3 < θ2)
    (hy : θ2 < y)
    (x : ℝ → ℝ)
    (hx_formula : ∀ y, x y = ((θ2 - θ3) * (y - θ1)) / ((θ3 - θ1) * (θ2 - y))) :
    0 < ((θ2 - θ3) / (θ2 - y)) / x y ∧
        ((θ2 - θ3) / (θ2 - y)) / x y < 1 := by
  have h_y_sub_θ1_pos : 0 < y - θ1 := by linarith
  have h_θ3_sub_θ1_pos : 0 < θ3 - θ1 := by linarith
  have h_denom_neg : θ2 - y < 0 := by linarith
  have h_x_neg : x y < 0 := by
    rw [hx_formula y]
    have h1 : 0 < (θ2 - θ3) * (y - θ1) := by positivity
    have h2 : (θ3 - θ1) * (θ2 - y) < 0 := by nlinarith
    exact div_neg_of_pos_of_neg h1 h2
  have h_lambda_neg : (θ2 - θ3) / (θ2 - y) < 0 := by
    apply div_neg_of_pos_of_neg
    · linarith
    · linarith
  have h_ratio_pos : 0 < ((θ2 - θ3) / (θ2 - y)) / x y := by
    exact div_pos_of_neg_of_neg h_lambda_neg h_x_neg
  have h_ratio_eq : ((θ2 - θ3) / (θ2 - y)) / x y = (θ3 - θ1) / (y - θ1) := by
    rw [hx_formula y]
    have h_num_pos : 0 < θ2 - θ3 := by linarith
    field_simp [h_denom_neg.ne, h_y_sub_θ1_pos.ne', h_θ3_sub_θ1_pos.ne', h_num_pos.ne']
  have h_ratio_pos2 : 0 < (θ3 - θ1) / (y - θ1) := by positivity
  have h_lt : (θ3 - θ1) / (y - θ1) < 1 := by
    rw [div_lt_one (by linarith)]
    ; linarith
  have h_final : 0 < ((θ2 - θ3) / (θ2 - y)) / x y ∧ ((θ2 - θ3) / (θ2 - y)) / x y < 1 := by
    rw [h_ratio_eq]
    exact ⟨h_ratio_pos2, h_lt⟩
  exact h_final

/-- Combined sector bound for `y ∈ [θ1, θ2)`.

If `y ∈ [θ1, θ3]` (lower sector, |x(y)| ≤ 1), then `0 < λ(y) ≤ 1`.
If `y ∈ [θ3, θ2)` (upper sector, |x(y)| ≥ 1), then `0 < λ(y)/x(y) ≤ 1`.

This is the key bound needed for Phase7: the effective sector scaling
coefficient always lies in `(0, 1]`. -/
lemma phase7_sector_effective_coeff_bound
    {θ1 θ3 θ2 y : ℝ} (h13 : θ1 < θ3) (h32 : θ3 < θ2)
    (hy1 : θ1 ≤ y) (hy2 : y < θ2)
    (x : ℝ → ℝ)
    (hx_formula : ∀ y, x y = ((θ2 - θ3) * (y - θ1)) / ((θ3 - θ1) * (θ2 - y))) :
    ((y ≤ θ3 → 0 < (θ2 - θ3) / (θ2 - y) ∧ (θ2 - θ3) / (θ2 - y) ≤ 1) ∧
     (θ3 ≤ y → 0 < ((θ2 - θ3) / (θ2 - y)) / x y ∧
                     ((θ2 - θ3) / (θ2 - y)) / x y ≤ 1)) := by
  constructor
  · -- y ≤ θ3
    intro h_y_le_θ3
    exact phase7_lambda_le_one_on_lower_sector h13 h32 hy1 h_y_le_θ3
  · -- θ3 ≤ y
    intro h_θ3_le_y
    exact phase7_lambda_over_x_le_one_on_upper_sector h13 h32 h_θ3_le_y hy2 x hx_formula

/-! ========================================================================
   Projective incidence identity
   ======================================================================== -/

/-- Projective incidence condition: if `p = F q` and `q ∈ T_y_points y`,
then `p 0 * x y + p 1 ∈ S(y)`.

Uses direct algebra from the cross-ratio and projective transform formulas. -/
lemma phase7_proj_incidence
    {y θ1 θ2 θ3 : ℝ}
    (hy_ne_θ2 : y ≠ θ2)
    (h_ord13 : θ1 < θ3)
    (h_ord32 : θ3 < θ2)
    (x : ℝ → ℝ)
    (hx_formula : ∀ y, x y = ((θ2 - θ3) * (y - θ1)) / ((θ3 - θ1) * (θ2 - y)))
    (F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
    (hF_formula : ∀ p, (F p) 0 = ((θ3 - θ1) / (θ2 - θ1)) * (p 0 * θ2 + p 1) ∧
                          (F p) 1 = ((θ2 - θ3) / (θ2 - θ1)) * (p 0 * θ1 + p 1))
    {T_y_points : Set (EuclideanSpace ℝ (Fin 2))}
    {q : EuclideanSpace ℝ (Fin 2)}
    (hq_in : q ∈ T_y_points) :
    (F q) 0 * x y + (F q) 1 ∈ phase7ScaledProjection y θ2 θ3 T_y_points := by
  set c : ℝ := (θ2 - θ3) / (θ2 - y) with hc_def
  set a : ℝ := θ3 - θ1 with ha_def
  set b : ℝ := θ2 - θ1 with hb_def
  set d : ℝ := θ2 - θ3 with hd_def
  set e : ℝ := θ2 - y with he_def
  have ha_pos : 0 < a := by linarith
  have hb_pos : 0 < b := by linarith
  have hd_pos : 0 < d := by linarith
  have he_ne : e ≠ 0 := by
    simp only [he_def]
    intro h
    have : y = θ2 := by linarith
    exact hy_ne_θ2 this
  have hF1 : (F q) 0 = (a / b) * (q 0 * θ2 + q 1) := by
    simpa [ha_def, hb_def] using (hF_formula q).1
  have hF2 : (F q) 1 = (d / b) * (q 0 * θ1 + q 1) := by
    simpa [hd_def, hb_def] using (hF_formula q).2
  have hxy : x y = d * (y - θ1) / (a * e) := hx_formula y
  have h_main_alg : (a / b) * (q 0 * θ2 + q 1) * (d * (y - θ1) / (a * e)) + (d / b) * (q 0 * θ1 + q 1) =
      (d / e) * (q 0 * y + q 1) := by
    have h : (q 0 * θ2 + q 1) * (y - θ1) + e * (q 0 * θ1 + q 1) = b * (q 0 * y + q 1) := by
      simp only [hb_def, he_def]
      ; ring
    field_simp [ha_pos.ne', hb_pos.ne', hd_pos.ne', he_ne]
    ; rw [← mul_right_inj' hb_pos.ne']
    ; ring_nf at *
    ; linarith
  have h1 : (F q) 0 * x y + (F q) 1 = c * (q 0 * y + q 1) := by
    rw [hF1, hF2, hxy]
    have hc : c = d / e := by
      simp [hc_def, hd_def, he_def]
    rw [hc]
    exact h_main_alg
  rw [h1]
  exact ⟨q 0 * y + q 1, ⟨q, hq_in, rfl⟩, rfl⟩

/-- Core algebraic identity for Resolution A:
`k*x(y) + j = λ(y) * (a*y + b)` where `a,b` are the translation coefficients. -/
lemma resolutionA_core_identity
    {θ1 θ3 θ2 y k j : ℝ}
    (h13 : θ1 < θ3) (h32 : θ3 < θ2) (hy_ne : y ≠ θ2) :
    k * ((θ2 - θ3) * (y - θ1) / ((θ3 - θ1) * (θ2 - y))) + j =
    ((θ2 - θ3) / (θ2 - y)) *
      ((k / (θ3 - θ1) - j / (θ2 - θ3)) * y +
       (-k * θ1 / (θ3 - θ1) + j * θ2 / (θ2 - θ3))) := by
  have h_denom1 : θ3 - θ1 ≠ 0 := by linarith
  have h_denom2 : θ2 - θ3 ≠ 0 := by linarith
  have h_denom3 : θ2 - y ≠ 0 := by intro h; exact hy_ne (by linarith)
  have h1 : (k / (θ3 - θ1) - j / (θ2 - θ3)) * y +
        (-k * θ1 / (θ3 - θ1) + j * θ2 / (θ2 - θ3)) =
      k * (y - θ1) / (θ3 - θ1) + j * (θ2 - y) / (θ2 - θ3) := by
    field_simp [h_denom1, h_denom2] <;> ring
  rw [h1]
  have h2 : ((θ2 - θ3) / (θ2 - y)) *
      (k * (y - θ1) / (θ3 - θ1) + j * (θ2 - y) / (θ2 - θ3)) =
      k * (((θ2 - θ3) * (y - θ1)) / ((θ3 - θ1) * (θ2 - y))) + j := by
    field_simp [h_denom1, h_denom2, h_denom3] <;> ring
  rw [h2] <;> rfl

/-- Scaled projection identity under constant 2D translation (Resolution A).

If `T' = translateSet2D v T` where `v` is the Resolution A translation vector,
then the scaled projection shifts by exactly `k*x(y) + j`. -/
lemma resolutionA_projection_identity
    {θ1 θ3 θ2 y : ℝ} {k j : ℝ}
    (h13 : θ1 < θ3) (h32 : θ3 < θ2) (hy_ne : y ≠ θ2)
    (v : EuclideanSpace ℝ (Fin 2))
    (hv0 : v 0 = k / (θ3 - θ1) - j / (θ2 - θ3))
    (hv1 : v 1 = -k * θ1 / (θ3 - θ1) + j * θ2 / (θ2 - θ3))
    (T : Set (EuclideanSpace ℝ (Fin 2))) :
    phase7ScaledProjection y θ2 θ3 ((fun q => q - v) '' T) =
    (fun w : ℝ => w - (k * ((θ2 - θ3) * (y - θ1) / ((θ3 - θ1) * (θ2 - y))) + j)) ''
      (phase7ScaledProjection y θ2 θ3 T) := by
  set x := (θ2 - θ3) * (y - θ1) / ((θ3 - θ1) * (θ2 - y)) with hx_def
  set lam := (θ2 - θ3) / (θ2 - y) with hlam_def
  set a := v 0 with ha_def
  set b := v 1 with hb_def
  have h_core : k * x + j = lam * (a * y + b) := by
    have h := resolutionA_core_identity h13 h32 hy_ne (k := k) (j := j)
    have ha : a = k / (θ3 - θ1) - j / (θ2 - θ3) := by exact ha_def.trans hv0
    have hb : b = -k * θ1 / (θ3 - θ1) + j * θ2 / (θ2 - θ3) := by exact hb_def.trans hv1
    rw [ha, hb] at *; exact h
  have h1 : Set.image (fun q : EuclideanSpace ℝ (Fin 2) => q 0 * y + q 1) ((fun q => q - v) '' T) =
      (fun w : ℝ => w - (a * y + b)) ''
        (Set.image (fun q : EuclideanSpace ℝ (Fin 2) => q 0 * y + q 1) T) := by
    ext z
    simp only [Set.mem_image]
    constructor
    · rintro ⟨q', ⟨q, hq, rfl⟩, rfl⟩
      refine ⟨q 0 * y + q 1, ⟨q, hq, rfl⟩, by simp [sub_mul] <;> ring⟩
    · rintro ⟨w, ⟨q, hq, rfl⟩, hz⟩
      refine ⟨q - v, ⟨q, hq, rfl⟩, ?_⟩
      have h_sub : (q - v) 0 * y + (q - v) 1 = q 0 * y + q 1 - (a * y + b) := by
        have h0 : (q - v) 0 = q 0 - a := by simp [ha_def]
        have h1 : (q - v) 1 = q 1 - b := by simp [hb_def]
        rw [h0, h1] <;> ring
      rw [h_sub]; exact hz
  rw [phase7ScaledProjection, h1]
  have h2 : scaleSet lam ((fun w : ℝ => w - (a * y + b)) ''
        (Set.image (fun q : EuclideanSpace ℝ (Fin 2) => q 0 * y + q 1) T)) =
      (fun w : ℝ => w - (lam * (a * y + b))) ''
        (scaleSet lam (Set.image (fun q : EuclideanSpace ℝ (Fin 2) => q 0 * y + q 1) T)) := by
    ext z
    simp only [scaleSet, Set.mem_image]
    constructor
    · rintro ⟨w, ⟨u, hu, rfl⟩, rfl⟩
      refine ⟨lam * u, ⟨u, hu, rfl⟩, by ring⟩
    · rintro ⟨w, ⟨u, hu, rfl⟩, hz⟩
      refine ⟨u - (a * y + b), ⟨u, hu, rfl⟩, ?_⟩
      have h_distrib : lam * (u - (a * y + b)) = lam * u - lam * (a * y + b) := by rw [mul_sub]
      rw [h_distrib]; exact hz
  rw [h2, h_core] <;> rfl

end ProductLikeIncidence.ProductReduction
