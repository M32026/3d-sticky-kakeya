/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Tube.Basic
public import Kakeya.Thickness.Basic
public import Kakeya.Thickness.Cthickening
public import Kakeya.Thickness.Volume
public import Mathlib.Geometry.Euclidean.Projection
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Body-ratio Fubini identity for tube cthickenings

This file states the geometric Fubini-type identity that underlies the
body-independent absolute constant `C(n)` in GWZ Lemma 7.4
(blueprint `section7.tex`, equation block L83-85, proof of
`lemmasubmultD`).

## Paper statement

The relevant step in the paper's proof of Lemma 7.4 is:

> `|K_m ∩ T_{ρ_{m-1}}| / |T_{ρ_{m-1}}| = |K_m| / |K_{m-1}|`

where:
* `T` is a `δ`-tube contained in a convex body `K ⊆ B_1`;
* `K_m` denotes the `ρ_m`-thickening (cthickening) of `K`;
* `T_{ρ_k}` denotes the `ρ_k`-thickening of `T`;
* `δ = ρ_M ≤ … ≤ ρ_0 = 1` is a chain of scales.

This identity is what lets the body-dependent factor `1 / volume K`
cancel pairwise inside the volume telescope of `Kakeya/Uniform/ParentBodyDensity/Telescope.lean`.
Without it the existential constant
produced by Lemma 7.4 carries a `1 / volume K_t` factor that blows up like
`δ^(-(n-1))`, contradicting the deterministic `C(n)` claim in the paper.

## Rigorous form

The paper writes the identity as an `=`, but rigorously it holds only up to
a dimension-only constant.  The formal statement provided here is therefore

  `volume (cthickening ρ' K ∩ cthickening ρ T) · volume (cthickening ρ K)`
    `≤ C(n) · volume (cthickening ρ T) · volume (cthickening ρ' K)`

with `C(n)` depending only on `n = Module.finrank ℝ E`.

The only hypotheses are `ρ' ≤ ρ` and positivity of `vol (K_ρ)` and `vol (T_ρ)`.  In particular
nothing is assumed about `δ`, about a bounding ball for `K` or `T`, or about `K_ρ' ∩ T_ρ` being
nonempty: the flag-box upper bound `volume_le_prod_thickness` needs only boundedness, and the
per-direction comparison never sees the tube's own scale.  The two positivity hypotheses are what
make the two divisions meaningful, and they also supply the strict positivity of the rank-wise
thicknesses of `K_ρ` and `T_ρ` that the argument divides by.

## Plan and status

The proof avoids Brunn-Minkowski / Prékopa-Leindler by reducing to
directional `Metric.thickness` instead of an axis-aligned box.  The
ingredients (formerly in `Kakeya/Fubini/{Scalar, ThickeningGrowth,
TubeThickness, VolumeThicknessUpper}.lean`, now all inlined in this file)
are:

* `Fubini.min_le_three_mul_div_of_le_add_two` — the per-direction
  comparison `min(a,b) ≤ 3 a b / c` whenever `c ≤ a + 2b`.
* `Metric.thickness_cthickening_le` — thickness grows by at
  most `R` under `R`-cthickening.
* `Fubini.Tube.le_two_mul_thickness_cthickening` — uniform tube
  lower bound `ρ ≤ 2 · thickness (T_ρ) j`.
* `volume_le_prod_thickness` (in `Kakeya.Thickness.Volume`) — general upper bound
  `vol S ≤ C · ∏ thickness S j` via the flag-box construction.

Combined with `convex_body_volume_thickness_lower_bound` (in
`Kakeya/Thickness/Volume.lean`) the assembly is:

  `s_j ≤ min(a_j, b_j) ≤ 3 a_j b_j / c_j`, then product, then sandwich
  `vol S · vol K_ρ ≤ C(n) · vol K_{ρ'} · vol T_ρ`.

## Downstream consumer

The single consumer is the volume telescope
`Tube.volume_thickening_telescope_paper_four` in
`Kakeya/Uniform/ParentBodyDensity/Telescope.lean`, which uses this lemma per step so that the
constant it produces is dimension-only; that is what lets the Lemma 7.4 engine
`Tube.ParentBodyDensity.maxDensity_le_prod_of_uniform_at_scales`, and in turn
`Kakeya.StickyKakeya.subStickyFrostmanLemma` (Lemma 7.5), carry a deterministic `C(n)`.

-/

open MeasureTheory ENNReal Metric EuclideanGeometry

@[expose] public section

namespace Tube

lemma min_le_three_mul_div_of_le_add_two
    {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 < c) (hc_le : c ≤ a + 2 * b) :
    min a b ≤ 3 * a * b / c := by
  rw [le_div_iff₀ hc]
  by_cases hab : a ≤ b
  · rw [min_eq_left hab]
    have hc3b : c ≤ 3 * b := by linarith
    have := mul_le_mul_of_nonneg_left hc3b ha
    linarith
  · push Not at hab
    rw [min_eq_right hab.le]
    have hc3a : c ≤ 3 * a := by linarith
    have := mul_le_mul_of_nonneg_left hc3a hb
    linarith

section TubeThickness
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E]
    [MeasurableSpace E] [BorelSpace E]

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **Tube thickness lower bound.**  For a `δ`-tube `T : Tube δ E` and `0 ≤ ρ ≤ 1`, every rank-`j`
thickness of `cthickening ρ T.carrier` satisfies `ρ ≤ 2 * thickness`.  The factor `2` comes from the
axial direction, where the cthickened tube has length `≥ 1` and so the smallest covering ball has
radius `≥ 1/2`. -/
lemma le_two_mul_thickness_cthickening
    {δ : NNReal} (T : _root_.Tube δ E) {ρ : ℝ} (hρ : 0 ≤ ρ)
    {j : ℕ} (hj : j < Module.finrank ℝ E) :
    ρ ≤ 2 * Metric.thickness ℝ (Metric.cthickening ρ T.carrier) j := by
  have hT_x_mem : T.x ∈ T.carrier := by
    rw [T.carrier_eq]
    refine Set.mem_iUnion₂.mpr ⟨T.x, left_mem_segment ℝ T.x T.y, ?_⟩
    exact Metric.mem_closedBall_self δ.coe_nonneg
  have h_ball_sub : Metric.closedBall T.x ρ ⊆ Metric.cthickening ρ T.carrier :=
    Metric.closedBall_subset_cthickening hT_x_mem ρ
  have h_bdd : Bornology.IsBounded (Metric.cthickening ρ T.carrier) :=
    T.isCompact'.isBounded.cthickening
  have h_mono : Metric.thickness ℝ (Metric.closedBall T.x ρ) j
      ≤ Metric.thickness ℝ (Metric.cthickening ρ T.carrier) j :=
    Metric.thickness_monotone h_bdd h_ball_sub j
  have h_ball_thick : ρ ≤ Metric.thickness ℝ (Metric.closedBall T.x ρ) j :=
    Metric.thickness_closedBall_ge hρ hj
  have h_main : ρ ≤ Metric.thickness ℝ (Metric.cthickening ρ T.carrier) j :=
    h_ball_thick.trans h_mono
  linarith [Metric.thickness_nonneg (𝕜 := ℝ) (Metric.cthickening ρ T.carrier) j]

end TubeThickness



/-- **Body-ratio Fubini bound** (GWZ Lemma 7.4 proof step, paper `section7.tex` L83-85), division
form.  For every dimension `n` there is `C(n) > 0` such that for every `δ`-tube `T` and convex body
`K` inside `B_R` with `R ≥ 1`, all scales `0 ≤ ρ' ≤ ρ` with `δ ≤ ρ ≤ 1`, and the non-degeneracy
hypotheses, `vol (K_ρ' ∩ T_ρ) / vol (T_ρ) ≤ C(n) · vol (K_ρ') / vol (K_ρ)`.  This is what makes
Lemma 7.4's existential constant depend only on `n`. -/
theorem cthickening_inter_body_ratio_div_le_toReal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E]
    [MeasurableSpace E] [BorelSpace E] :
    ∃ C : ℝ, 0 < C ∧ ∀ {δ : NNReal} (T : _root_.Tube δ E) (K : ConvexSpaceBody E)
      {ρ ρ' : NNReal}, ρ' ≤ ρ →
      0 < (MeasureTheory.volume (Metric.cthickening (ρ : ℝ) K.carrier)).toReal →
      0 < (MeasureTheory.volume (Metric.cthickening (ρ : ℝ) T.carrier)).toReal →
      (MeasureTheory.volume
            (Metric.cthickening (ρ' : ℝ) K.carrier
              ∩ Metric.cthickening (ρ : ℝ) T.carrier)).toReal
          / (MeasureTheory.volume (Metric.cthickening (ρ : ℝ) T.carrier)).toReal
        ≤ C
            * (MeasureTheory.volume
                (Metric.cthickening (ρ' : ℝ) K.carrier)).toReal
            / (MeasureTheory.volume
                (Metric.cthickening (ρ : ℝ) K.carrier)).toReal := by
  classical
  set n : ℕ := Module.finrank ℝ E with hn_def
  have hn_pos : 0 < n := Module.finrank_pos
  have hC₁_pos : (0 : NNReal) < 2 ^ n := by positivity
  have hC₁ : ∀ (S : Set E), Bornology.IsBounded S →
      MeasureTheory.volume S
        ≤ ((2 : NNReal) ^ n : ENNReal) * ∏ j : Fin n,
            ENNReal.ofReal (Metric.thickness ℝ S j.val) := by
    intro S hS_bdd
    have h := _root_.volume_le_prod_thickness hS_bdd
    rw [← hn_def] at h
    rw [← Fin.prod_univ_eq_prod_range
      (fun i : ℕ => ENNReal.ofReal (Metric.thickness ℝ S i)) n] at h
    exact h
  set C₁ : NNReal := 2 ^ n with hC₁_def
  have hC₁_real : ∀ (S : Set E), Bornology.IsBounded S →
      volume.real S ≤ (C₁ : ℝ) * ∏ j : Fin n, Metric.thickness ℝ S j.val := by
    intro S hS_bdd
    have h := hC₁ S hS_bdd
    have hRHS_ne_top : (C₁ : ENNReal) *
        ∏ j : Fin n, ENNReal.ofReal (Metric.thickness ℝ S j.val) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.coe_ne_top
        (ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top)
    have hreal := ENNReal.toReal_mono hRHS_ne_top h
    simpa [Measure.real, ENNReal.toReal_mul, ENNReal.toReal_prod,
      ENNReal.toReal_ofReal (Metric.thickness_nonneg S _)] using hreal
  obtain ⟨c_K, hc_K_pos, hc_K⟩ := convex_body_volume_thickness_lower_bound (E := E)
  refine ⟨C₁ * C₁ * (3 : ℝ) ^ n / (c_K * c_K), by positivity, ?_⟩
  intro δ T K ρ ρ' hρ'_le_ρ hKρ_vol_pos hTρ_vol_pos
  simp only [← MeasureTheory.measureReal_def] at hKρ_vol_pos hTρ_vol_pos ⊢
  set Kρ'  : Set E := Metric.cthickening (ρ' : ℝ) K.carrier with hKρ'_def
  set Kρ   : Set E := Metric.cthickening (ρ  : ℝ) K.carrier with hKρ_def
  set Tρ   : Set E := Metric.cthickening (ρ  : ℝ) T.carrier with hTρ_def
  set S    : Set E := Kρ' ∩ Tρ with hS_def
  have hρ_nn : (0 : ℝ) ≤ (ρ : ℝ) := ρ.coe_nonneg
  have hρ'_nn : (0 : ℝ) ≤ (ρ' : ℝ) := ρ'.coe_nonneg
  have hρ'_le_ρ_real : (ρ' : ℝ) ≤ (ρ : ℝ) := by exact_mod_cast hρ'_le_ρ
  have hK_compact : IsCompact K.carrier := K.isCompact
  have hK_conv : Convex ℝ K.carrier := K.convex
  have hK_ne : K.carrier.Nonempty := K.nonempty
  have hT_compact : IsCompact T.carrier := T.isCompact'
  have hT_conv : Convex ℝ T.carrier := T.convex
  have hT_ne : T.carrier.Nonempty := T.nonempty
  have hKρ'_compact : IsCompact Kρ' := hK_compact.cthickening
  have hKρ_compact : IsCompact Kρ := hK_compact.cthickening
  have hTρ_compact : IsCompact Tρ := hT_compact.cthickening
  have hKρ'_conv : Convex ℝ Kρ' := hK_conv.cthickening _
  have hTρ_conv : Convex ℝ Tρ := hT_conv.cthickening _
  have hKρ'_bdd : Bornology.IsBounded Kρ' := hKρ'_compact.isBounded
  have hKρ_bdd : Bornology.IsBounded Kρ := hKρ_compact.isBounded
  have hTρ_bdd : Bornology.IsBounded Tρ := hTρ_compact.isBounded
  have hKρ'_ne : Kρ'.Nonempty := hK_ne.mono (Metric.self_subset_cthickening _)
  have hTρ_ne : Tρ.Nonempty := hT_ne.mono (Metric.self_subset_cthickening _)
  have hS_sub_Kρ' : S ⊆ Kρ' := Set.inter_subset_left
  have hS_sub_Tρ : S ⊆ Tρ := Set.inter_subset_right
  have hS_bdd : Bornology.IsBounded S := hKρ'_bdd.subset hS_sub_Kρ'
  have hS_compact : IsCompact S :=
    hKρ'_compact.of_isClosed_subset
      (hKρ'_compact.isClosed.inter hTρ_compact.isClosed) hS_sub_Kρ'
  have hKρ_sub : Kρ ⊆ Metric.cthickening ((ρ : ℝ) - (ρ' : ℝ)) Kρ' := by
    have hdiff_nn : (0 : ℝ) ≤ (ρ : ℝ) - (ρ' : ℝ) := sub_nonneg.mpr hρ'_le_ρ_real
    have h_eq : Metric.cthickening ((ρ : ℝ) - (ρ' : ℝ)) Kρ'
        = Metric.cthickening ((ρ : ℝ)) K.carrier := by
      simp only [hKρ'_def]
      rw [cthickening_cthickening hdiff_nn hρ'_nn]
      congr 1
      linarith
    rw [h_eq]
  let a : Fin n → ℝ := fun j => Metric.thickness ℝ Kρ' j.val
  let b : Fin n → ℝ := fun j => Metric.thickness ℝ Tρ j.val
  let c : Fin n → ℝ := fun j => Metric.thickness ℝ Kρ j.val
  let s : Fin n → ℝ := fun j => Metric.thickness ℝ S j.val
  have ha_nn : ∀ j, 0 ≤ a j := fun j => Metric.thickness_nonneg _ _
  have hb_nn : ∀ j, 0 ≤ b j := fun j => Metric.thickness_nonneg _ _
  have hc_nn : ∀ j, 0 ≤ c j := fun j => Metric.thickness_nonneg _ _
  have hs_nn : ∀ j, 0 ≤ s j := fun j => Metric.thickness_nonneg _ _
  have hs_le_a : ∀ j, s j ≤ a j := fun j =>
    Metric.thickness_monotone hKρ'_bdd hS_sub_Kρ' j.val
  have hs_le_b : ∀ j, s j ≤ b j := fun j =>
    Metric.thickness_monotone hTρ_bdd hS_sub_Tρ j.val
  have hs_le_min : ∀ j, s j ≤ min (a j) (b j) := fun j => le_min (hs_le_a j) (hs_le_b j)
  have hc_le : ∀ j, c j ≤ a j + ((ρ : ℝ) - (ρ' : ℝ)) := by
    intro j
    have hdiff_nn : (0 : ℝ) ≤ (ρ : ℝ) - (ρ' : ℝ) := sub_nonneg.mpr hρ'_le_ρ_real
    have h_cth_bdd : Bornology.IsBounded
        (Metric.cthickening ((ρ : ℝ) - (ρ' : ℝ)) Kρ') := hKρ'_bdd.cthickening
    have h_thick_mono : c j ≤
        Metric.thickness ℝ (Metric.cthickening ((ρ : ℝ) - (ρ' : ℝ)) Kρ') j.val :=
      Metric.thickness_monotone h_cth_bdd hKρ_sub j.val
    have h_growth :
        Metric.thickness ℝ (Metric.cthickening ((ρ : ℝ) - (ρ' : ℝ)) Kρ') j.val
        ≤ a j + ((ρ : ℝ) - (ρ' : ℝ)) :=
      Metric.thickness_cthickening_le hKρ'_bdd hKρ'_ne hdiff_nn j.val
    linarith
  have hρ_le_two_b : ∀ j, (ρ : ℝ) ≤ 2 * b j := fun j =>
    le_two_mul_thickness_cthickening T hρ_nn j.isLt
  have hc_le_add : ∀ j, c j ≤ a j + 2 * b j := by
    intro j
    have := hc_le j
    have h2 := hρ_le_two_b j
    linarith
  have hKρ_vol_le : MeasureTheory.volume.real Kρ ≤ C₁ * ∏ j : Fin n, c j :=
    hC₁_real Kρ hKρ_bdd
  have hc_pos : ∀ j, 0 < c j := by
    intro j
    by_contra h_neg
    rw [not_lt] at h_neg
    have hc_zero : c j = 0 := le_antisymm h_neg (hc_nn j)
    have hprod_zero : ∏ k : Fin n, c k = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ j) hc_zero
    have hbound : MeasureTheory.volume.real Kρ ≤ 0 := by
      rw [hprod_zero, mul_zero] at hKρ_vol_le
      exact hKρ_vol_le
    linarith [hKρ_vol_pos]
  have hTρ_vol_le : MeasureTheory.volume.real Tρ ≤ C₁ * ∏ j : Fin n, b j :=
    hC₁_real Tρ hTρ_bdd
  have hb_pos : ∀ j, 0 < b j := by
    intro j
    by_contra h_neg
    rw [not_lt] at h_neg
    have hb_zero : b j = 0 := le_antisymm h_neg (hb_nn j)
    have hprod_zero : ∏ k : Fin n, b k = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) hb_zero
    have hbound : MeasureTheory.volume.real Tρ ≤ 0 := by
      rw [hprod_zero, mul_zero] at hTρ_vol_le
      exact hTρ_vol_le
    linarith [hTρ_vol_pos]
  have h_per_dir : ∀ j, s j ≤ 3 * a j * b j / c j := fun j =>
    (hs_le_min j).trans
      (min_le_three_mul_div_of_le_add_two (ha_nn j) (hb_nn j)
        (hc_pos j) (hc_le_add j))
  have hS_vol_le : MeasureTheory.volume.real S ≤ C₁ * ∏ j : Fin n, s j :=
    hC₁_real S hS_bdd
  have hKρ'_vol_ge : c_K * (∏ j : Fin n, a j) ≤ MeasureTheory.volume.real Kρ' :=
    hc_K Kρ' hKρ'_conv hKρ'_compact hKρ'_ne
  have hTρ_vol_ge : c_K * (∏ j : Fin n, b j) ≤ MeasureTheory.volume.real Tρ :=
    hc_K Tρ hTρ_conv hTρ_compact hTρ_ne
  have hprod_a_nn : 0 ≤ ∏ j : Fin n, a j := Finset.prod_nonneg (fun j _ => ha_nn j)
  have hprod_b_pos : 0 < ∏ j : Fin n, b j := Finset.prod_pos (fun j _ => hb_pos j)
  have hprod_c_pos : 0 < ∏ j : Fin n, c j := Finset.prod_pos (fun j _ => hc_pos j)
  have hprod_s_nn : 0 ≤ ∏ j : Fin n, s j := Finset.prod_nonneg (fun j _ => hs_nn j)
  have hKρ'_vol_nn : 0 ≤ MeasureTheory.volume.real Kρ' :=
    MeasureTheory.measureReal_nonneg
  have h_prod_s :
      ∏ j : Fin n, s j
        ≤ (3 : ℝ) ^ n * (∏ j : Fin n, a j) * (∏ j : Fin n, b j) / ∏ j : Fin n, c j := by
    have h_prod_le :
        ∏ j : Fin n, s j ≤ ∏ j : Fin n, (3 * a j * b j / c j) := by
      apply Finset.prod_le_prod
      · intro j _; exact hs_nn j
      · intro j _; exact h_per_dir j
    have h_prod_eq :
        ∏ j : Fin n, (3 * a j * b j / c j)
          = (3 : ℝ) ^ n * (∏ j : Fin n, a j) * (∏ j : Fin n, b j) / ∏ j : Fin n, c j := by
      rw [Finset.prod_div_distrib]
      congr 1
      rw [show (fun j : Fin n => 3 * a j * b j) =
        (fun j : Fin n => (3 * a j) * b j) from rfl,
        Finset.prod_mul_distrib]
      have h2 : ∏ j : Fin n, (3 * a j) = (3 : ℝ) ^ n * ∏ j : Fin n, a j := by
        rw [Finset.prod_mul_distrib]
        simp [Finset.card_univ]
      rw [h2]
    linarith [h_prod_le, h_prod_eq ▸ le_refl (∏ j : Fin n, (3 * a j * b j / c j))]
  rw [div_le_div_iff₀ hTρ_vol_pos hKρ_vol_pos]
  have hC : 0 < (C₁ : ℝ) := by exact_mod_cast hC₁_pos
  have hcK := hc_K_pos
  have hS_bound : MeasureTheory.volume.real S
      ≤ C₁ * ((3 : ℝ) ^ n * (∏ j : Fin n, a j)
              * (∏ j : Fin n, b j) / ∏ j : Fin n, c j) := by
    calc MeasureTheory.volume.real S
        ≤ C₁ * ∏ j : Fin n, s j := hS_vol_le
      _ ≤ C₁ * ((3 : ℝ) ^ n * (∏ j : Fin n, a j)
                * (∏ j : Fin n, b j) / ∏ j : Fin n, c j) :=
          mul_le_mul_of_nonneg_left h_prod_s hC.le
  have hLHS_le :
      MeasureTheory.volume.real S * MeasureTheory.volume.real Kρ
      ≤ C₁ * C₁ * (3 : ℝ) ^ n * (∏ j : Fin n, a j) * (∏ j : Fin n, b j) := by
    have hbound1 :
        MeasureTheory.volume.real S * MeasureTheory.volume.real Kρ
          ≤ (C₁ * ((3 : ℝ) ^ n * (∏ j : Fin n, a j)
                  * (∏ j : Fin n, b j) / ∏ j : Fin n, c j))
            * (C₁ * ∏ j : Fin n, c j) := by
      apply mul_le_mul hS_bound hKρ_vol_le MeasureTheory.measureReal_nonneg
      positivity
    have heq :
        (C₁ * ((3 : ℝ) ^ n * (∏ j : Fin n, a j)
              * (∏ j : Fin n, b j) / ∏ j : Fin n, c j))
          * (C₁ * ∏ j : Fin n, c j)
          = C₁ * C₁ * (3 : ℝ) ^ n * (∏ j : Fin n, a j) * (∏ j : Fin n, b j) := by
      field_simp
    linarith
  have hRHS_ge :
      C₁ * C₁ * (3 : ℝ) ^ n * (∏ j : Fin n, a j) * (∏ j : Fin n, b j)
      ≤ C₁ * C₁ * (3 : ℝ) ^ n / (c_K * c_K)
        * MeasureTheory.volume.real Kρ' * MeasureTheory.volume.real Tρ := by
    have hprod :
        (c_K * ∏ j : Fin n, a j) * (c_K * ∏ j : Fin n, b j)
        ≤ MeasureTheory.volume.real Kρ' * MeasureTheory.volume.real Tρ := by
      apply mul_le_mul hKρ'_vol_ge hTρ_vol_ge
        (mul_nonneg hcK.le (Finset.prod_nonneg (fun j _ => hb_nn j))) hKρ'_vol_nn
    have heq :
        C₁ * C₁ * (3 : ℝ) ^ n / (c_K * c_K)
          * ((c_K * ∏ j : Fin n, a j) * (c_K * ∏ j : Fin n, b j))
          = C₁ * C₁ * (3 : ℝ) ^ n * (∏ j : Fin n, a j) * (∏ j : Fin n, b j) := by
      have hck_ne : c_K ≠ 0 := ne_of_gt hc_K_pos
      field_simp
    have hcoef_nn : 0 ≤ C₁ * C₁ * (3 : ℝ) ^ n / (c_K * c_K) := by positivity
    calc C₁ * C₁ * (3 : ℝ) ^ n * (∏ j : Fin n, a j) * (∏ j : Fin n, b j)
        = C₁ * C₁ * (3 : ℝ) ^ n / (c_K * c_K)
          * ((c_K * ∏ j : Fin n, a j) * (c_K * ∏ j : Fin n, b j)) := heq.symm
      _ ≤ C₁ * C₁ * (3 : ℝ) ^ n / (c_K * c_K)
          * (MeasureTheory.volume.real Kρ' * MeasureTheory.volume.real Tρ) :=
          mul_le_mul_of_nonneg_left hprod hcoef_nn
      _ = C₁ * C₁ * (3 : ℝ) ^ n / (c_K * c_K)
          * MeasureTheory.volume.real Kρ' * MeasureTheory.volume.real Tρ := by ring
  exact hLHS_le.trans hRHS_ge

end Tube
