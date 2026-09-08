/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Uniform.ParentBodyDensity
public import Kakeya.Tube.ChainScale

/-!
# GWZ Lemma 7.4: submultiplicativity of `Δ_max` along a multiscale hierarchy

Blueprint `lemmasubmultD` (`blueprint/src/GWZAdapted/section7.tex`).

## Divergence from the blueprint: the factor-4 scale gap

The blueprint's multiscale hierarchy (`section7.tex:116`) only asks the scales to *decrease*,
`ρ_m ≤ ρ_{m-1}`.  `Kakeya.MultiScaleSubmult.maxDensity_le_prod_fibreDeltaMax` asks for the
strictly stronger `4 · ρ_{m+1} ≤ ρ_m`; `Kakeya.MultiScaleSubmult.antitone_not_imp_four_gap`
exhibits `ρ ≡ 1` as a compiler-checked witness that the two are different.

**The factor `4` is not slack, and it is not removable here.** It is consumed by the
*neighbourhood step* of the volume telescope: `Kakeya/Uniform/ParentBodyDensity/Telescope.lean`,
inside `Tube.volume_thickening_telescope_paper_four`, needs

```
Metric.cthickening (4 * ρ m.succ) (par m).carrier ⊆ Metric.cthickening (ρ m.castSucc) (par m).carrier
```

(`Telescope.lean:208-211`, `Metric.cthickening_mono (hsep_r m)`), i.e. the `4ρ_{m+1}`-neighbourhood
of the parent tube must fit inside the parent tube's own thickness `ρ_m`.  That is exactly
`4ρ_{m+1} ≤ ρ_m`.  (By contrast, the hypothesis *is* dead in the counting engine
`card_le_prod_density_volume_div_parent_level`, where it is bound as `_hscale_gap`; the volume
telescope is the only real consumer.)

## What this costs the Section-9 consumer, exactly

`section9.tex:184` applies Lemma 7.4 at the scales `σ ∈ [δ̃^{1-ε₂}, δ̃^{ε₂}]` with `b ≥ δ̃^{ε₂}`,
so at the top endpoint `σ = b` and `4σ ≤ b` fails.  The window must be shrunk by the factor `4`.
`Kakeya.MultiScaleSubmult.exists_threshold_four_mul_rpow_le` prices that shrink: for **any**
`ε₂' > ε₂` there is a threshold `δ₀ = (1/4)^{1/(ε₂' - ε₂)}` such that
`4 · δ̃^{ε₂'} ≤ δ̃^{ε₂}` for every `δ̃ ≤ δ₀`.  So the cost is

* an arbitrarily small increase of the exponent, `ε₂ ⤳ ε₂'`, at the **top** endpoint of the
  `σ`-window only (the bottom endpoint `δ̃^{1-ε₂}` is untouched), and
* one extra smallness threshold on `δ̃`, depending only on `ε₂' - ε₂`.

Both are free in Section 9: `ε₂` is chosen at the end of the parameter chain subject to upper
bounds only (`eps₂_le_everyScale`, `eps₂_le_vnsWindow`, `ε₂ ≤ exscalb/2`), so it may be replaced
by any slightly larger admissible value, and `δ̃`-thresholds are already ubiquitous there.
`Kakeya.MultiScaleSubmult.four_mul_le_of_window` states the resulting hypothesis in the `σ`/`b`
form the call site uses, and `Kakeya.MultiScaleSubmult.maxDensity_le_two_fibreDeltaMax` is the
`M = 2` interface it feeds, with the two required gaps `4b ≤ ρ₀` and `4σ ≤ b` spelled out.
-/

@[expose] public section

open MeasureTheory Metric ConvexSpaceBody Kakeya

namespace Kakeya.MultiScaleSubmult

universe u

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

open scoped Classical in
/-- `D_m = max_{j ∈ s_{m-1}} Δ_max(𝕋_m[j])` of GWZ Lemma 7.4. -/
noncomputable def fibreDeltaMax {α β : Type*} (u : Finset α) (W : α → ConvexSpaceBody E)
    (v : Finset β) (par : α → β) : ENNReal :=
  v.sup fun j => maxDensity {i ∈ u | par i = j} W

open scoped Classical in
omit [Nontrivial E] in
theorem fibreDeltaMax_ne_top {α β : Type*} (u : Finset α) (W : α → ConvexSpaceBody E)
    (v : Finset β) (par : α → β) : fibreDeltaMax u W v par ≠ ⊤ := by
  have : fibreDeltaMax u W v par < ⊤ := by
    rw [fibreDeltaMax]
    refine (Finset.sup_lt_iff (by simp : (⊥ : ENNReal) < ⊤)).mpr fun j _ => ?_
    exact lt_top_iff_ne_top.mpr (maxDensity_ne_top _ _)
  exact this.ne

open scoped Classical in
omit [Nontrivial E] in
theorem maxDensity_fibre_le_fibreDeltaMax {α β : Type*} (u : Finset α) (W : α → ConvexSpaceBody E)
    {v : Finset β} {par : α → β} {j : β} (hj : j ∈ v) :
    maxDensity {i ∈ u | par i = j} W ≤ fibreDeltaMax u W v par :=
  Finset.le_sup (f := fun j => maxDensity {i ∈ u | par i = j} W) hj

open scoped Classical in
/-- **GWZ Lemma 7.4 (blueprint `lemmasubmultD`), stated over `Δ_max` on both sides.**

The constant is the blueprint's: `C(n)^M ∏_m D_m`, with `C` bound *before* `∀ M` and depending
only on `A` and `C_box`.

Two divergences from `lemmasubmultD`, both documented in the module header:

* the scale hypothesis is `4 · ρ_{m+1} ≤ ρ_m`, not merely `ρ_{m+1} ≤ ρ_m` — see
  `Kakeya.MultiScaleSubmult.antitone_not_imp_four_gap` for the witness that these differ, and the
  module header for why the factor `4` is forced by the neighbourhood step of the volume
  telescope and for what shrinking the Section-9 `σ`-window by `4` costs;
* `ρ_0 = 1` is relaxed to `1 ≤ ρ_0 ≤ 4`, at the price of the extra hypothesis
  `|Q 0| ≤ C_box · (A+3)^{2n}` (the blueprint gets it free from hierarchy uniformity, which this
  statement drops — a net strengthening). -/
theorem maxDensity_le_prod_fibreDeltaMax (A : ℝ) (hA : 1 ≤ A) (C_box : ℝ) (hC_box : 0 < C_box) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ℕ), 0 < M → ∀ (ρ : Fin (M + 1) → NNReal),
      1 ≤ ρ 0 → ρ 0 ≤ 4 → 0 < ρ (Fin.last M) → Antitone ρ →
      (∀ m : Fin M, 4 * ρ m.succ ≤ ρ m.castSucc) →
      ∀ {κ : Fin (M + 1) → Type u} (tb : ∀ k : Fin (M + 1), κ k → Tube (ρ k) E)
        (Q : ∀ k : Fin (M + 1), Finset (κ k))
        (proj : ∀ m : Fin M, κ m.succ → κ m.castSucc),
      (∀ m : Fin M, ∀ w ∈ Q m.succ, proj m w ∈ Q m.castSucc) →
      (∀ m : Fin M, ∀ w ∈ Q m.succ,
          (tb m.succ w).toConvexSpaceBody ≤ (tb m.castSucc (proj m w)).toConvexSpaceBody) →
      (((Q 0).card : ℝ) ≤ C_box * (A + 3) ^ (2 * Module.finrank ℝ E)) →
      (∀ k : Fin (M + 1), ∀ t ∈ Q k, (tb k t).carrier ⊆ Metric.closedBall (0 : E) A) →
      (∀ m : Fin M, (Q m.castSucc).Nonempty) →
      maxDensity (Q (Fin.last M)) (fun w => (tb (Fin.last M) w).toConvexSpaceBody)
        ≤ ENNReal.ofReal C ^ M
            * ∏ m : Fin M, fibreDeltaMax (Q m.succ)
                (fun w => (tb m.succ w).toConvexSpaceBody) (Q m.castSucc) (proj m) := by
  obtain ⟨C, hC, h⟩ :=
    Tube.ParentBodyDensity.maxDensity_le_prod_of_uniform_at_scales (E := E) A hA C_box hC_box
  refine ⟨C, hC, ?_⟩
  intro M hM ρ hρ0 hρ04 hρpos hanti hgap κ tb Q proj hpm hpl hcard hball hne
  have hδ1 : ((ρ (Fin.last M) : NNReal) : ℝ) ≤ 1 := by
    have hm0 : (⟨0, hM⟩ : Fin M).castSucc = (0 : Fin (M + 1)) := by
      simp
    have hstep := hgap ⟨0, hM⟩
    rw [hm0] at hstep
    have h1 : (4 : NNReal) * ρ (⟨0, hM⟩ : Fin M).succ ≤ 4 := hstep.trans hρ04
    have h2 : ρ (⟨0, hM⟩ : Fin M).succ ≤ 1 := by
      by_contra hcon
      rw [not_le] at hcon
      exact absurd h1 (by
        have : (4 : NNReal) < 4 * ρ (⟨0, hM⟩ : Fin M).succ := by
          nlinarith [hcon, (show (0:NNReal) < 4 by norm_num)]
        exact not_le.mpr this)
    have h3 : ρ (Fin.last M) ≤ ρ (⟨0, hM⟩ : Fin M).succ :=
      hanti (by simp [Fin.le_def, Fin.succ]; omega)
    exact_mod_cast h3.trans h2
  have hball' : ∀ k : Fin (M + 1), ∀ t ∈ Q k,
      (tb k t).carrier ⊆ Metric.closedBall (0 : E) (A + 3) := fun k t ht =>
    (hball k t ht).trans (Metric.closedBall_subset_closedBall (by linarith))
  exact h hρpos hδ1 (Q (Fin.last M)) (tb (Fin.last M))
    (fun i hi => hball (Fin.last M) i hi) M hM ρ hρ0 hρ04 rfl hanti hgap
    tb Q proj hpm hpl hcard hball' hne id (fun i hi => hi) (fun _ _ => le_rfl)
    Function.injective_id.injOn _
    (fun m => fibreDeltaMax_ne_top _ _ _ _)
    (fun m p hp => maxDensity_fibre_le_fibreDeltaMax _ _ hp)


/-! ### The factor-4 scale gap: witness that it is stronger, and what it costs -/

/-- **The Lean hierarchy hypothesis is strictly stronger than the blueprint's.**

`ρ ≡ 1` is antitone, satisfies `1 ≤ ρ 0 ≤ 4` and `0 < ρ (Fin.last 2)`, and fails
`4 · ρ_{m+1} ≤ ρ_m`.  So `Kakeya.MultiScaleSubmult.maxDensity_le_prod_fibreDeltaMax` is *not*
a formalization of `lemmasubmultD` at face value; see the module header. -/
theorem antitone_not_imp_four_gap :
    ∃ ρ : Fin 3 → NNReal, Antitone ρ ∧ 1 ≤ ρ 0 ∧ ρ 0 ≤ 4 ∧ 0 < ρ (Fin.last 2) ∧
      ¬ (∀ m : Fin 2, 4 * ρ m.succ ≤ ρ m.castSucc) := by
  refine ⟨fun _ => 1, fun i j _ => le_rfl, le_rfl, by norm_num, by norm_num, fun h => ?_⟩
  have h0 := h 0
  norm_num at h0

/-- **The exact price of the factor-4 gap at the Section-9 call site.**

For every pair of exponents `ε < ε'` there is a threshold `δ₀ = (1/4)^{1/(ε' - ε)}` below which
`4 · δ^{ε'} ≤ δ^{ε}`.  Read at the call site of `section9.tex:184`: the `σ`-window's top endpoint
must move from `δ̃^{ε₂}` to `δ̃^{ε₂'}` for some `ε₂' > ε₂`, and once `δ̃ ≤ δ₀` the hierarchy
hypothesis `4σ ≤ b` holds throughout the shrunken window.  Nothing else is lost: the bottom
endpoint `δ̃^{1-ε₂}` and the constant `C(n)^M` are untouched. -/
theorem exists_threshold_four_mul_rpow_le {ε ε' : ℝ} (hεε' : ε < ε') :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → 4 * δ ^ ε' ≤ δ ^ ε := by
  have hd : 0 < ε' - ε := sub_pos.mpr hεε'
  refine ⟨(1 / 4 : ℝ) ^ (1 / (ε' - ε)), Real.rpow_pos_of_pos (by norm_num) _,
    Real.rpow_le_one (by norm_num) (by norm_num) (by positivity), ?_⟩
  intro δ hδ hδ0
  have hinv : ((1 / 4 : ℝ) ^ (1 / (ε' - ε)))⁻¹ ≤ δ⁻¹ := by
    simpa [one_div] using one_div_le_one_div_of_le hδ hδ0
  have hkey : (4 : ℝ) ≤ δ ^ (ε - ε') := by
    have h1 : ((1 / 4 : ℝ) ^ (1 / (ε' - ε)))⁻¹ = (4 : ℝ) ^ (1 / (ε' - ε)) := by
      rw [← Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 1 / 4)]
      norm_num
    have h2 : ((4 : ℝ) ^ (1 / (ε' - ε))) ^ (ε' - ε) ≤ (δ⁻¹) ^ (ε' - ε) := by
      refine Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) _) ?_ hd.le
      rw [← h1]
      exact hinv
    rw [← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ hd.ne', Real.rpow_one] at h2
    calc (4 : ℝ) ≤ (δ⁻¹) ^ (ε' - ε) := h2
      _ = δ ^ (ε - ε') := by
          rw [Real.inv_rpow hδ.le, ← Real.rpow_neg hδ.le, neg_sub]
  have hpow : δ ^ ε = δ ^ ε' * δ ^ (ε - ε') := by
    rw [← Real.rpow_add hδ]
    ring_nf
  rw [hpow, mul_comm (δ ^ ε')]
  exact mul_le_mul_of_nonneg_right hkey (Real.rpow_nonneg hδ.le _)

/-- **The shrunken window, in the `σ`/`b` form of `section9.tex:184`.**

If `σ ≤ δ̃^{ε'}` (the shrunken top endpoint) and `δ̃^{ε} ≤ b` (what the call site knows about
`b`), then `4σ ≤ b`, provided `δ̃` is below the threshold of
`Kakeya.MultiScaleSubmult.exists_threshold_four_mul_rpow_le`. -/
theorem four_mul_le_of_window {ε ε' : ℝ} (hεε' : ε < ε') :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 ∧
      ∀ dt σ b : ℝ, 0 < dt → dt ≤ δ₀ → σ ≤ dt ^ ε' → dt ^ ε ≤ b → 4 * σ ≤ b := by
  obtain ⟨δ₀, hδ₀pos, hδ₀one, h⟩ := exists_threshold_four_mul_rpow_le hεε'
  refine ⟨δ₀, hδ₀pos, hδ₀one, fun dt σ b hdt hdt0 hσ hb => ?_⟩
  calc 4 * σ ≤ 4 * dt ^ ε' := by linarith
    _ ≤ dt ^ ε := h dt hdt hdt0
    _ ≤ b := hb

open scoped Classical in
/-- **GWZ Lemma 7.4 at `M = 2`: the Section-9 two-scale interface.**

The two hierarchy gaps that `Kakeya.MultiScaleSubmult.maxDensity_le_prod_fibreDeltaMax` hides
behind `∀ m : Fin M` are spelled out here as `4 · ρ₁ ≤ ρ₀` and `4 · ρ₂ ≤ ρ₁`.  At the Section-9
call site `ρ₀ ∈ [1, 4]` is the ambient ball, `ρ₁ = b` and `ρ₂ = σ`; the first gap is
`4b ≤ ρ₀`, satisfiable at `ρ₀ = 4`, `b ≤ 1`, and the second is the `4σ ≤ b` supplied by
`Kakeya.MultiScaleSubmult.four_mul_le_of_window`.

`Antitone ρ` is *derived* here, not assumed: `ρ₂ ≤ 4ρ₂ ≤ ρ₁ ≤ 4ρ₁ ≤ ρ₀`. -/
theorem maxDensity_le_two_fibreDeltaMax (A : ℝ) (hA : 1 ≤ A) (C_box : ℝ) (hC_box : 0 < C_box) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ρ : Fin 3 → NNReal),
      1 ≤ ρ 0 → ρ 0 ≤ 4 → 0 < ρ 2 → 4 * ρ 1 ≤ ρ 0 → 4 * ρ 2 ≤ ρ 1 →
      ∀ {κ : Fin 3 → Type u} (tb : ∀ k : Fin 3, κ k → Tube (ρ k) E)
        (Q : ∀ k : Fin 3, Finset (κ k))
        (proj : ∀ m : Fin 2, κ m.succ → κ m.castSucc),
      (∀ m : Fin 2, ∀ w ∈ Q m.succ, proj m w ∈ Q m.castSucc) →
      (∀ m : Fin 2, ∀ w ∈ Q m.succ,
          (tb m.succ w).toConvexSpaceBody ≤ (tb m.castSucc (proj m w)).toConvexSpaceBody) →
      (((Q 0).card : ℝ) ≤ C_box * (A + 3) ^ (2 * Module.finrank ℝ E)) →
      (∀ k : Fin 3, ∀ t ∈ Q k, (tb k t).carrier ⊆ Metric.closedBall (0 : E) A) →
      (∀ m : Fin 2, (Q m.castSucc).Nonempty) →
      maxDensity (Q 2) (fun w => (tb 2 w).toConvexSpaceBody)
        ≤ ENNReal.ofReal C ^ 2
            * ∏ m : Fin 2, fibreDeltaMax (Q m.succ)
                (fun w => (tb m.succ w).toConvexSpaceBody) (Q m.castSucc) (proj m) := by
  obtain ⟨C, hC, h⟩ := maxDensity_le_prod_fibreDeltaMax (E := E) A hA C_box hC_box
  refine ⟨C, hC, ?_⟩
  intro ρ hρ0 hρ04 hρ2 hg1 hg2 κ tb Q proj hpm hpl hcard hball hne
  have h10 : ρ 1 ≤ ρ 0 :=
    le_trans (le_mul_of_one_le_left zero_le (by norm_num)) hg1
  have h21 : ρ 2 ≤ ρ 1 :=
    le_trans (le_mul_of_one_le_left zero_le (by norm_num)) hg2
  have hanti : Antitone ρ := by
    rw [Fin.antitone_iff_succ_le]
    intro m
    fin_cases m
    · simpa using h10
    · simpa using h21
  have hgap : ∀ m : Fin 2, 4 * ρ m.succ ≤ ρ m.castSucc := by
    intro m
    fin_cases m
    · simpa using hg1
    · simpa using hg2
  have hlast : (Fin.last 2 : Fin 3) = 2 := rfl
  have := h 2 (by norm_num) ρ hρ0 hρ04 (by rw [hlast]; exact hρ2) hanti hgap
    tb Q proj hpm hpl hcard hball hne
  rw [hlast] at this
  exact this

/-! ### Geometric preliminaries for the two-scale corollary -/

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- The base point of a tube lies in the tube. -/
theorem tube_x_mem_carrier {ρ : NNReal} (T : Tube ρ E) : T.x ∈ T.carrier := by
  rw [T.carrier_eq]
  exact Set.mem_biUnion (left_mem_segment ℝ T.x T.y) (Metric.mem_closedBall_self ρ.coe_nonneg)

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- The far endpoint of a tube lies in the tube. -/
theorem tube_y_mem_carrier {ρ : NNReal} (T : Tube ρ E) : T.y ∈ T.carrier := by
  rw [T.carrier_eq]
  exact Set.mem_biUnion (right_mem_segment ℝ T.x T.y) (Metric.mem_closedBall_self ρ.coe_nonneg)

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- **The unit ball fits inside any `r`-rescale, `r ≥ 2`, of a tube contained in the unit ball.**
This supplies the single level-`0` node `B_1` of the two-scale hierarchy. -/
theorem closedBall_subset_rescale_carrier {ρ : NNReal} (T : Tube ρ E)
    (hT : T.carrier ⊆ Metric.closedBall (0 : E) 1) {r : NNReal} (hr : (2 : ℝ) ≤ (r : ℝ)) :
    Metric.closedBall (0 : E) 1 ⊆ (T.rescale r).carrier := by
  have hxnorm : ‖T.x‖ ≤ 1 := by
    have hx := hT (tube_x_mem_carrier T)
    rwa [Metric.mem_closedBall, dist_zero_right] at hx
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right] at hz
  rw [(T.rescale r).carrier_eq]
  refine Set.mem_biUnion (left_mem_segment ℝ (T.rescale r).x (T.rescale r).y) ?_
  rw [Metric.mem_closedBall, dist_eq_norm]
  show ‖z - T.x‖ ≤ (r : ℝ)
  calc ‖z - T.x‖ ≤ ‖z‖ + ‖T.x‖ := norm_sub_le _ _
    _ ≤ 2 := by linarith
    _ ≤ (r : ℝ) := hr

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
/-- An `r`-rescale of a tube contained in the unit ball stays in the ball of radius `1 + r`. -/
theorem rescale_carrier_subset_closedBall {ρ : NNReal} (T : Tube ρ E)
    (hT : T.carrier ⊆ Metric.closedBall (0 : E) 1) (r : NNReal) :
    (T.rescale r).carrier ⊆ Metric.closedBall (0 : E) (1 + (r : ℝ)) := by
  have hxnorm : ‖T.x‖ ≤ 1 := by
    have hx := hT (tube_x_mem_carrier T)
    rwa [Metric.mem_closedBall, dist_zero_right] at hx
  have hynorm : ‖T.y‖ ≤ 1 := by
    have hy := hT (tube_y_mem_carrier T)
    rwa [Metric.mem_closedBall, dist_zero_right] at hy
  have hseg : segment ℝ T.x T.y ⊆ Metric.closedBall (0 : E) 1 := by
    refine (convex_closedBall (0 : E) 1).segment_subset ?_ ?_
    · rwa [Metric.mem_closedBall, dist_zero_right]
    · rwa [Metric.mem_closedBall, dist_zero_right]
  intro z hz
  rw [(T.rescale r).carrier_eq] at hz
  obtain ⟨w, hw, hzw⟩ := Set.mem_iUnion₂.mp hz
  have hwnorm : ‖w‖ ≤ 1 := by
    have := hseg hw
    rwa [Metric.mem_closedBall, dist_zero_right] at this
  have hzwnorm : ‖z - w‖ ≤ (r : ℝ) := by
    rw [Metric.mem_closedBall, dist_eq_norm] at hzw
    exact hzw
  rw [Metric.mem_closedBall, dist_zero_right]
  calc ‖z‖ = ‖(z - w) + w‖ := by rw [sub_add_cancel]
    _ ≤ ‖z - w‖ + ‖w‖ := norm_add_le _ _
    _ ≤ (r : ℝ) + 1 := add_le_add hzwnorm hwnorm
    _ = 1 + (r : ℝ) := by ring

end Kakeya.MultiScaleSubmult
