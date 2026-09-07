module

/-
# Original-Space Multiplicity Bridge Lemma

Proves `h_mult_orig`: the original Gamma multiplicity lower bound needed by
the H5→H6 bridge (`glue_H5_to_H6`).

For each `g ∈ Gamma`, we show that `g` is incident to `S_pre_orig y` for
at least `c_mult_dir · |Y|` values of `y`.

## Witness chain

`g ∈ Gamma` → `z ∈ E3''` (with `g = round(z)`) → `r ∈ E3` (with `z = F(r)`)
→ `r ∈ Pbar_param` → Phase0 multiplicity gives `|{y | r ∈ T_y_points y}| ≥ c · |Y|`.

For each such `y`:
- If `y = θ2`: `S_pre_orig θ2 = Set.univ`, trivial.
- If `y ≠ θ2`: `phase7_proj_incidence` gives exact projection incidence for `F(r)`,
  and rounding error (`≤ δ/2` per coordinate) gives `g` within the thickening radius.
-/

public import MyLeanRepo.ProductLikeIncidence.Phase7ScaledProjections
public import MyLeanRepo.ProductLikeIncidence.ThickeningCovering
public import MyLeanRepo.OSWPrelude

@[expose] public section

noncomputable section

open Set Finset Classical

attribute [local instance] Classical.propDecidable

namespace ProductLikeIncidence.ProductReduction

/-- Original-space multiplicity bridge: for each `g ∈ Gamma`, the number of
`y ∈ Y` such that `g 0 * x y + g 1 ∈ S_pre_orig y` is at least `c_mult_dir · |Y|`.

This is the `h_mult_orig` input required by `glue_H5_to_H6`. -/
lemma mult_orig_bridge
    {δ : ℝ} (_hδ_pos : 0 < δ)
    {Y : Set ℝ} (hY_fin : Y.Finite)
    {x : ℝ → ℝ}
    {θ1 θ2 θ3 : ℝ} (h_ord13 : θ1 < θ3) (h_ord32 : θ3 < θ2)
    (hx_formula : ∀ y, x y = ((θ2 - θ3) * (y - θ1)) / ((θ3 - θ1) * (θ2 - y)))
    {F : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)}
    (hF_formula : ∀ p, (F p) 0 = ((θ3 - θ1) / (θ2 - θ1)) * (p 0 * θ2 + p 1) ∧
                          (F p) 1 = ((θ2 - θ3) / (θ2 - θ1)) * (p 0 * θ1 + p 1))
    {round : ℝ → ℝ} (h_round_near : ∀ t : ℝ, |round t - t| ≤ δ / 2)
    {T_y_points : ℝ → Set (EuclideanSpace ℝ (Fin 2))}
    {Pbar_param : Set (EuclideanSpace ℝ (Fin 2))}
    {E3 : Set (EuclideanSpace ℝ (Fin 2))}
    {E3'' : Set (EuclideanSpace ℝ (Fin 2))}
    {Gamma : Set (EuclideanSpace ℝ (Fin 2))}
    (c_mult_dir : ℝ) (hc_mult_dir_pos : 0 < c_mult_dir)
    -- Witness chain hypotheses
    (hGamma_witness : ∀ g ∈ Gamma,
      ∃ (z : EuclideanSpace ℝ (Fin 2)), z ∈ E3'' ∧ g 0 = round (z 0) ∧ g 1 = round (z 1))
    (hE3''_sub_F : E3'' ⊆ F '' E3)
    (hE3_sub_Pbar : E3 ⊆ Pbar_param)
    -- Phase 0 multiplicity
    (h_multiplicity_points : ∀ p ∈ Pbar_param,
      ENat.toENNReal {y ∈ Y | p ∈ T_y_points y}.encard ≥
        ENNReal.ofReal c_mult_dir * ENat.toENNReal Y.encard)
    -- S_pre_orig definition
    (S_pre_orig : ℝ → Set ℝ)
    (hS_pre_orig_def : ∀ y, S_pre_orig y =
      if y = θ2 then Set.univ
      else intervalThicken (δ * (1 + |x y|) / 2)
        (phase7ScaledProjection y θ2 θ3 (T_y_points y))) :
    ∀ g ∈ Gamma,
      ({y ∈ hY_fin.toFinset | g 0 * x y + g 1 ∈ S_pre_orig y}.card : ℝ) ≥
        c_mult_dir * hY_fin.toFinset.card := by
  intro g hg
  -- Step 1: Witness chain g → z ∈ E3'' → r ∈ E3 → r ∈ Pbar_param
  rcases hGamma_witness g hg with ⟨z, hz_E3'', h_round0, h_round1⟩
  rcases hE3''_sub_F hz_E3'' with ⟨r, hr_E3, hz_F⟩
  have hz_eq : z = F r := hz_F.symm
  have hr_Pbar : r ∈ Pbar_param := hE3_sub_Pbar hr_E3

  -- Step 2: Phase 0 multiplicity
  have h_mult : ENat.toENNReal {y ∈ Y | r ∈ T_y_points y}.encard ≥
      ENNReal.ofReal c_mult_dir * ENat.toENNReal Y.encard :=
    h_multiplicity_points r hr_Pbar

  -- Convert to finset card
  have hYfin_eq : (hY_fin.toFinset : Set ℝ) = Y := hY_fin.coe_toFinset
  let S_r : Finset ℝ := {y ∈ hY_fin.toFinset | r ∈ T_y_points y}
  have h2 : {y ∈ Y | r ∈ T_y_points y} = (S_r : Set ℝ) := by
    ext y
    simp only [S_r, mem_filter, mem_coe]
    constructor
    · rintro ⟨hyY, hry⟩
      have h_y_in_fin : y ∈ hY_fin.toFinset := by
        have h : y ∈ (hY_fin.toFinset : Set ℝ) := hYfin_eq.symm ▸ hyY
        exact_mod_cast h
      exact ⟨h_y_in_fin, hry⟩
    · rintro ⟨hyfin, hry⟩
      have h_y_in_Y : y ∈ Y := by
        have h : y ∈ (hY_fin.toFinset : Set ℝ) := by exact_mod_cast hyfin
        exact hYfin_eq ▸ h
      exact ⟨h_y_in_Y, hry⟩
  have h1 : ENat.toENNReal {y ∈ Y | r ∈ T_y_points y}.encard =
      ENNReal.ofReal (S_r.card : ℝ) := by
    rw [h2]
    rw [encard_coe_eq_coe_finsetCard S_r]
    <;> norm_cast
  have hY_encard : Y.encard = ↑hY_fin.toFinset.card :=
    Finite.encard_eq_coe_toFinset_card hY_fin
  have hY_card : ENat.toENNReal Y.encard = ENNReal.ofReal (hY_fin.toFinset.card : ℝ) := by
    rw [hY_encard] <;> norm_cast
  rw [h1, hY_card] at h_mult
  have h_mul : ENNReal.ofReal c_mult_dir * ENNReal.ofReal (hY_fin.toFinset.card : ℝ) =
      ENNReal.ofReal (c_mult_dir * hY_fin.toFinset.card) := by
    rw [← ENNReal.ofReal_mul] <;> positivity
  rw [h_mul] at h_mult
  have h_nonneg2 : 0 ≤ c_mult_dir * hY_fin.toFinset.card := by positivity
  have h_mult' : ENNReal.ofReal (c_mult_dir * hY_fin.toFinset.card) ≤ ENNReal.ofReal (S_r.card : ℝ) := h_mult
  have h_mult_card : (S_r.card : ℝ) ≥ c_mult_dir * hY_fin.toFinset.card := by
    have h := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp h_mult'
    exact h

  -- Step 3: For each y with r ∈ T_y_points y, prove g incidence in S_pre_orig y
  have h_inc : ∀ y ∈ hY_fin.toFinset, r ∈ T_y_points y → g 0 * x y + g 1 ∈ S_pre_orig y := by
    intro y hyfin hry
    by_cases hy_theta : y = θ2
    · -- y = θ2: S_pre_orig θ2 = Set.univ
      have h : S_pre_orig y = Set.univ := by
        rw [hS_pre_orig_def y, if_pos hy_theta]
      rw [h] <;> trivial
    · -- y ≠ θ2: projective incidence + rounding error
      have h_y_in_Y : y ∈ Y := by
        have h : y ∈ (hY_fin.toFinset : Set ℝ) := by exact_mod_cast hyfin
        exact hYfin_eq ▸ h
      have h1 : (F r) 0 * x y + (F r) 1 ∈
          phase7ScaledProjection y θ2 θ3 (T_y_points y) :=
        phase7_proj_incidence hy_theta h_ord13 h_ord32 x hx_formula F hF_formula hry
      have hg0 : g 0 = round ((F r) 0) := by
        rw [h_round0, hz_eq]
      have hg1 : g 1 = round ((F r) 1) := by
        rw [h_round1, hz_eq]
      have h_round_err : |(g 0 * x y + g 1) - ((F r) 0 * x y + (F r) 1)| ≤
          δ * (1 + |x y|) / 2 := by
        rw [hg0, hg1]
        have h_alg : |(round ((F r) 0) * x y + round ((F r) 1)) -
            ((F r) 0 * x y + (F r) 1)| =
            |(round ((F r) 0) - (F r) 0) * x y + (round ((F r) 1) - (F r) 1)| := by ring_nf
        rw [h_alg]
        have h_tri : |(round ((F r) 0) - (F r) 0) * x y + (round ((F r) 1) - (F r) 1)| ≤
            |round ((F r) 0) - (F r) 0| * |x y| + |round ((F r) 1) - (F r) 1| := by
          set a : ℝ := (round ((F r) 0) - (F r) 0) * x y with ha_def
          set b : ℝ := round ((F r) 1) - (F r) 1 with hb_def
          have h_abs : |a + b| ≤ |a| + |b| := abs_add_le a b
          have h_abs_a : |a| = |round ((F r) 0) - (F r) 0| * |x y| := by
            rw [ha_def, abs_mul]
          rw [h_abs_a] at h_abs
          exact h_abs
        have h12 : |round ((F r) 0) - (F r) 0| ≤ δ / 2 := h_round_near ((F r) 0)
        have h13 : |round ((F r) 1) - (F r) 1| ≤ δ / 2 := h_round_near ((F r) 1)
        have h_bound : |round ((F r) 0) - (F r) 0| * |x y| + |round ((F r) 1) - (F r) 1| ≤
            δ * (1 + |x y|) / 2 := by
          calc
            |round ((F r) 0) - (F r) 0| * |x y| + |round ((F r) 1) - (F r) 1|
              ≤ (δ / 2) * |x y| + (δ / 2) := by gcongr
            _ = δ * (1 + |x y|) / 2 := by ring
        exact le_trans h_tri h_bound
      have hS : S_pre_orig y = intervalThicken (δ * (1 + |x y|) / 2)
          (phase7ScaledProjection y θ2 θ3 (T_y_points y)) := by
        rw [hS_pre_orig_def y, if_neg hy_theta]
      rw [hS]
      exact ⟨(F r) 0 * x y + (F r) 1, h1, h_round_err⟩

  -- Step 4: Cardinality transfer via finset subset
  let S_g : Finset ℝ := {y ∈ hY_fin.toFinset | g 0 * x y + g 1 ∈ S_pre_orig y}
  have h_sub : S_r ⊆ S_g := by
    intro y hy
    have h_y_in_fin : y ∈ hY_fin.toFinset := (mem_filter.mp hy).1
    have h_ry : r ∈ T_y_points y := (mem_filter.mp hy).2
    exact mem_filter.mpr ⟨h_y_in_fin, h_inc y h_y_in_fin h_ry⟩
  have h4 : S_r.card ≤ S_g.card := Finset.card_le_card h_sub
  have h5 : (S_r.card : ℝ) ≤ (S_g.card : ℝ) := by exact_mod_cast h4
  exact le_trans h_mult_card h5

end ProductLikeIncidence.ProductReduction
