/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineDeltaMaxFloor

/-!
# The corrected canonical-cover route: essential distinctness at bounded ED-multiplicity

Blueprint: `blueprint/src/GWZAdapted/section9.tex`, the non-eccentric case, the invocation of
GWZ Lemma 9.1 at `ζ = η_j/2`.

`Kakeya.ML2Reduction.not_upstairs_bundle_at` (in
`Reduction/SpineDeltaMaxFloor.lean`) refutes the route that buys essential distinctness of the
pushed-down `ρ`-cover with a maximal-density bound: `Δ_max ≥ |t| ρ² / 3` for any family of
`ρ`-tubes in the unit ball, so `Kakeya.Tube.refineToEssDistinctLeaves`'s certificate
`|t| / (C₃ Δ_max)` never exceeds `(3/C₃) ρ^{-2}`, while Lemma 9.1's count clause needs
`ρ^{-2-ζ}`.

**This file replaces the price.**  The extraction is the same maximal essentially distinct
subfamily (`Kakeya.Tube.exists_maximal_essDistinct`), but priced by the family's own
**ED-multiplicity**

```
M  such that  ∀ i ∈ t, #{ j ∈ t | ¬ IsEssentiallyDistinct (V j) (V i) } ≤ M
```

— how many members of the family can be essentially the same tube as one given member.  For a
family that is already essentially distinct `M = 1`.  `M` is a *multiplicity*, not a density: it
is not bounded below by any power of `ρ`, so the count budget `M · Λ ≤ ρ^{-(ζ'-ζ)}` is
satisfiable, in contrast with the `Δ_max` version, which forces the constant inequality
`C₃ ≤ 3` and hence `False`.

## Essential distinctness is not the obstruction

`IsEssentiallyDistinct U V` is the *volume* condition `|U ∩ V| ≤ ½ max(|U|,|V|)`
(`Kakeya/ConvexBody.lean:79`), and `Kakeya.Tube.card_le_of_EssDistinct` caps an essentially
distinct family of `ρ`-tubes in the unit ball at `C · (1/ρ)^{2·3} = C ρ^{-6}` in dimension `3`
(crude; the geometric truth is `ρ^{-4}` — two direction and two position parameters).  The count
clause's `ρ^{-2-ζ}` is far below that for `ζ ≤ 4`
(`rpow_count_le_essDistinct_ceiling`).  **There is no statement-level problem with Lemma 9.1's
count clause**: the `ρ^{-2}` cap is a property of one lemma's certificate, not of essentially
distinct families.

## The interface

`canonicalCover_of_upstairs_edMult`'s `hup` is the corrected per-scale bundle, and its conclusion
is the `hcanon` binder of
`Kakeya.ML2Reduction.multiplicity_le_of_lemma91At_outer_of_canonicalCover` character for
character.  Compared with  it has **six** clauses instead of seven: the two clauses
`Δ_max ≤ D` and `C₃ · D ≤ Ced` are replaced by the single ED-multiplicity clause, and `0 < Ced`
becomes `0 < M`.  `multiplicity_le_of_lemma91At_outer_of_upstairs_edMult` is step 10 over that
interface, feeding the existing consumer.

## The window reading

`IsKatzTaoDividingWindow.le_window_maxDensity` is stated on the window cut at `ε_div = e`, while
the blueprint reads it on the narrower window cut at `ε₂ ≥ 5 e`; `mem_divWindow_of_mem_eps₂Window`
is the inclusion, so no existing statement has to move.  `spine_windowExponent_div_le` shows the
`ε_div` reading of the *upper* `Δ_max` bound gives `a = η_{j-1}/e ≤ η_j/480`, which closes the
count budget `ζ' - ζ = η_j/4` with a factor-`120` margin — **retracting the caveat in
**, which used the blueprint ladder `η_k ≤ e η_{k+1}` instead of the far stronger
`Kakeya.ML2Spine.IsSpine.sep_le`.

## What is still owed

Exactly one thing: a bound on `M`.  It is a bounded-multiplicity statement about the cover, of the
kind `Kakeya.Tube.UniformTubeSet.boundedOverlap` is designed to carry, and it cannot come from a
volume or density estimate — a fibre bound derived from `maxDensity` reproduces
`refineToEssDistinctLeaves` and is capped as above.

## Main declarations

* `Kakeya.ML2Reduction.not_isEssentiallyDistinct_tube_self`,
  `Kakeya.ML2Reduction.one_le_edMult` — a tube is not essentially distinct from itself, so
  `0 < M` is free for a nonempty family.
* `Kakeya.ML2Reduction.exists_essDistinct_of_edMult` — the extraction, at the loss `M`.
* `Kakeya.ML2Reduction.canonicalCoverAt_of_used_of_edMult` — the drop-in replacement for
  `Kakeya.ML2Reduction.canonicalCoverAt_of_used_of_maxDensity`.
* `Kakeya.ML2Reduction.edCount_budget_of_slack` — the count-budget arithmetic at the new price.
* `Kakeya.ML2Reduction.canonicalCoverAt_of_upstairs_edMult`,
  `Kakeya.ML2Reduction.canonicalCover_of_upstairs_edMult` — the datum at one scale and over the
  window; the latter's conclusion is the `hcanon` binder verbatim.
* `Kakeya.ML2Reduction.multiplicity_le_of_lemma91At_outer_of_upstairs_edMult` — step 10.
* `Kakeya.ML2Reduction.rpow_count_le_essDistinct_ceiling` — the count clause is below the
  essential-distinctness ceiling.
* `Kakeya.ML2Reduction.spine_windowExponent_div_le`,
  `Kakeya.ML2Reduction.spine_count_budget_closes_div`,
  `Kakeya.ML2Reduction.mem_divWindow_of_mem_eps₂Window` — the window reading.
* `Kakeya.ML2Reduction.essDistinct_pushdown_of_edMult` — 's isolation theorem,
  discharged.
-/

@[expose] public section

open MeasureTheory Metric Set ConvexSpaceBody
open scoped NNReal ENNReal

namespace Kakeya.ML2Reduction

universe u

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The `ε_div` window reading. -/
theorem spine_windowExponent_div_le {β ϖ ε₁ ε₂ e : ℝ} {gain dens : ℝ → ℝ} {N : ℕ} {η : ℕ → ℝ}
    (h : ML2Spine.IsSpine β ϖ ε₁ gain dens ε₂ e N η) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    {k : ℕ} (hk : k < N) :
    η k / e ≤ η (k + 1) / 480 := by
  have he : 0 < e := h.div_pos
  have he5 : e ≤ ε₂ / 5 := h.div_le
  have hε2 : 0 < ε₂ := h.eps₂_pos
  have hεh : ε₂ ≤ 1 / 2 := h.eps₂_le_half
  have hsep : 12 * η k / (e * β) ≤ e * η (k + 1) / 4 := h.sep_le k hk
  have hk0 : 0 < η k := h.rung_pos k
  have hk10 : 0 < η (k + 1) := h.rung_pos (k + 1)
  have heb : 0 < e * β := mul_pos he hβ0
  have hA : η k ≤ e ^ 2 * β * η (k + 1) / 48 := by
    have h' := (div_le_iff₀ heb).mp hsep
    nlinarith [h']
  have he10 : e ≤ 1 / 10 := by nlinarith [he5, hεh]
  have h10eb : 10 * e * β ≤ 1 := by nlinarith [he10, hβ1, hβ0, he]
  have h1 : 480 * η k ≤ 10 * e ^ 2 * β * η (k + 1) := by nlinarith [hA]
  have h2 : 10 * e ^ 2 * β * η (k + 1) ≤ e * η (k + 1) := by
    have hp : (10 * e * β) * (e * η (k + 1)) ≤ 1 * (e * η (k + 1)) :=
      mul_le_mul_of_nonneg_right h10eb (by positivity)
    nlinarith [hp]
  rw [div_le_div_iff₀ he (by norm_num : (0 : ℝ) < 480)]
  linarith

/-! ### The corrected extraction: bounded ED-multiplicity, not `Δ_max` -/

/-- A `ρ`-tube with `ρ > 0` has positive finite volume, so it is not essentially distinct from
itself.  This is what makes a family's ED-multiplicity at least `1`. -/
theorem not_isEssentiallyDistinct_tube_self [Nontrivial E] {ρ : NNReal} (hρ0 : 0 < ρ)
    (T : Tube ρ E) : ¬ _root_.IsEssentiallyDistinct T.carrier T.carrier := by
  refine not_isEssentiallyDistinct_self ?_ T.toConvexSpaceBody.isCompact.measure_ne_top
  have h := T.le_volume
  have hpos : (0 : ENNReal) < (Tube.le_volume.c (Module.finrank ℝ E) : ENNReal)
      * (ρ : ENNReal) ^ (Module.finrank ℝ E - 1) := by
    refine ENNReal.mul_pos ?_ (pow_ne_zero _ (by exact_mod_cast hρ0.ne'))
    exact_mod_cast (Tube.le_volume.c_pos (Module.finrank ℝ E)).ne'
  exact (lt_of_lt_of_le hpos (by exact_mod_cast h)).ne'

/-- **`0 < M` is free.**  A nonempty family has ED-multiplicity at least `1`, since each member
lies in its own fibre. -/
theorem one_le_edMult [Nontrivial E] {ρ : NNReal} (hρ0 : 0 < ρ) {κ : Type*} {t : Finset κ}
    (V : κ → Tube ρ E) {M : ℕ} (hne : t.Nonempty)
    (hM : ∀ i ∈ t, (open scoped Classical in t.filter (fun j ↦
      ¬ _root_.IsEssentiallyDistinct (V j).carrier (V i).carrier)).card ≤ M) : 1 ≤ M := by
  classical
  obtain ⟨i, hi⟩ := hne
  refine le_trans ?_ (hM i hi)
  refine Finset.card_pos.mpr ⟨i, ?_⟩
  simp only [Finset.mem_filter]
  exact ⟨hi, not_isEssentiallyDistinct_tube_self hρ0 (V i)⟩

/-- **A maximal essentially distinct subfamily, at the family's own ED-multiplicity.**

`Kakeya.Tube.refineToEssDistinctLeaves` extracts an essentially distinct subfamily at the loss
`C_n · Δ_max`, and `Kakeya.ML2Reduction.not_count_budget_of_unitBall` shows that loss is fatal at
the cardinality Lemma 9.1 asks for.  This is the same extraction priced differently: by the
**ED-multiplicity** `M` of the family — how many of its members can be essentially the same tube as
one given member.  For a family that is already essentially distinct `M = 1`, whereas `Δ_max` is
`≥ |t| ρ² / 3` no matter what. -/
theorem exists_essDistinct_of_edMult [Nontrivial E] {ρ : NNReal} (hρ0 : 0 < ρ)
    {κ : Type*} (t : Finset κ) (V : κ → Tube ρ E) {M : ℕ}
    (hM : ∀ i ∈ t, (open scoped Classical in t.filter (fun j ↦
      ¬ _root_.IsEssentiallyDistinct (V j).carrier (V i).carrier)).card ≤ M) :
    ∃ u ⊆ t,
      ((u : Set κ).Pairwise
        fun i j ↦ _root_.IsEssentiallyDistinct (V i).carrier (V j).carrier) ∧
      t.card ≤ M * u.card := by
  classical
  obtain ⟨u, hut, hED, hmax⟩ := Kakeya.Tube.exists_maximal_essDistinct t V
  refine ⟨u, hut, hED, ?_⟩
  have hchoice : ∀ j ∈ t, ∃ i, i ∈ u ∧
      ¬ _root_.IsEssentiallyDistinct (V j).carrier (V i).carrier := by
    intro j hj
    by_cases hju : j ∈ u
    · exact ⟨j, hju, not_isEssentiallyDistinct_tube_self hρ0 (V j)⟩
    · obtain ⟨i, hi, hnot⟩ := hmax j hj hju
      exact ⟨i, hi, fun hcon ↦ hnot (isEssentiallyDistinct_symm hcon)⟩
  choose! f hfu hfnot using hchoice
  rw [Finset.card_eq_sum_card_fiberwise hfu]
  calc ∑ i ∈ u, (t.filter fun j ↦ f j = i).card
      ≤ ∑ _i ∈ u, M := by
        refine Finset.sum_le_sum fun i hi ↦ ?_
        refine le_trans (Finset.card_le_card ?_) (hM i (hut hi))
        intro j hj
        simp only [Finset.mem_filter] at hj ⊢
        exact ⟨hj.1, hj.2 ▸ hfnot j hj.1⟩
    _ = u.card * M := by rw [Finset.sum_const, smul_eq_mul]
    _ = M * u.card := Nat.mul_comm _ _

/-! ### The canonical-cover datum, at the corrected price -/

variable {θ τ : NNReal}

/-- **The essential-distinctness half of the canonical-cover datum, at the ED-multiplicity price.**

This is `Kakeya.ML2Reduction.canonicalCoverAt_of_used_of_maxDensity` with the loss
`refineToEssDistinctLeaves.C 3 · Δ_max` replaced by the ED-multiplicity `M`.  Everything else —
the "used" clause, the index type, the conclusion — is character for character the same, so the
two are drop-in alternatives at the call site. -/
theorem canonicalCoverAt_of_used_of_edMult
    {R : ℝ} (hθ : 0 < θ) (T₀ : Tube θ (EuclideanSpace ℝ (Fin 3))) {hR : 0 < R}
    {α : Type u} {s : Finset α} (𝕋 : α → ShadedTube τ (EuclideanSpace ℝ (Fin 3)))
    {ρ : NNReal} (hρ0 : 0 < ρ)
    {κ₀ : Type u} (t : Finset κ₀) (V : κ₀ → Tube ρ (EuclideanSpace ℝ (Fin 3)))
    {M : ℕ} (hM0 : 0 < M)
    (hM : ∀ i ∈ t, (open scoped Classical in t.filter (fun j ↦
      ¬ _root_.IsEssentiallyDistinct (V j).carrier (V i).carrier)).card ≤ M)
    (hused : ∀ j ∈ t, ∃ i ∈ s,
      (spineFamily (spineRescaleUnit hθ T₀ hR) 𝕋 i).toConvexSpaceBody ≤ (V j).toConvexSpaceBody)
    {c : ℝ} (hlow : (M : ℝ) * c ≤ (t.card : ℝ)) :
    ∃ (κ₁ : Type u) (u : Finset κ₁) (W : κ₁ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
      ((u : Set κ₁).Pairwise
        fun j k ↦ _root_.IsEssentiallyDistinct (W j).carrier (W k).carrier) ∧
      (∀ j ∈ u, ∃ i ∈ s,
        (spineFamily (spineRescaleUnit hθ T₀ hR) 𝕋 i).toConvexSpaceBody
          ≤ (W j).toConvexSpaceBody) ∧
      c ≤ (u.card : ℝ) := by
  classical
  obtain ⟨u, hut, hED, hcard⟩ := exists_essDistinct_of_edMult hρ0 t V hM
  refine ⟨κ₀, u, V, hED, fun j hj ↦ hused j (hut hj), ?_⟩
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM0
  have hreal : (t.card : ℝ) ≤ (M : ℝ) * (u.card : ℝ) := by exact_mod_cast hcard
  nlinarith [hlow, hreal]

/-! ### The count budget at the corrected price -/

/-- The count-budget arithmetic with the ED-multiplicity `M` in place of
`refineToEssDistinctLeaves.C 3 · Δ_max`.  Unlike the `Δ_max` version this is satisfiable: `M` is
not bounded below by any power of `ρ`. -/
theorem edCount_budget_of_slack {ρ : NNReal} (hρ0 : 0 < ρ) {ζ ζ' : ℝ} {M Lam : ℝ}
    (hslack : M * Lam ≤ (ρ : ℝ) ^ (-(ζ' - ζ)))
    {n : ℕ} (hcard : (ρ : ℝ) ^ (-2 - ζ') ≤ (n : ℝ)) :
    M * (Lam * (ρ : ℝ) ^ (-2 - ζ)) ≤ (n : ℝ) := by
  have hρR : (0 : ℝ) < (ρ : ℝ) := by exact_mod_cast hρ0
  have hsplit : (ρ : ℝ) ^ (-(ζ' - ζ)) * (ρ : ℝ) ^ (-2 - ζ) = (ρ : ℝ) ^ (-2 - ζ') := by
    rw [← Real.rpow_add hρR]; ring_nf
  calc M * (Lam * (ρ : ℝ) ^ (-2 - ζ)) = (M * Lam) * (ρ : ℝ) ^ (-2 - ζ) := by ring
    _ ≤ (ρ : ℝ) ^ (-(ζ' - ζ)) * (ρ : ℝ) ^ (-2 - ζ) :=
        mul_le_mul_of_nonneg_right hslack (Real.rpow_nonneg hρR.le _)
    _ = (ρ : ℝ) ^ (-2 - ζ') := hsplit
    _ ≤ (n : ℝ) := hcard

/-- **The canonical-cover datum at one scale, from the upstairs family, at the ED-multiplicity
price.**  This is 's `canonicalCoverAt_of_upstairs` with the two clauses `Δ_max ≤ D`
and `C₃ · D ≤ Ced` replaced by the single clause `hM`, and it is the version that is not
self-contradictory. -/
theorem canonicalCoverAt_of_upstairs_edMult {σ : NNReal} {R ζ ζ' : ℝ}
    (hsit : Tube.IsRescalingSituation θ τ σ R 3) (hR : 0 < R)
    (T₀ : Tube θ (EuclideanSpace ℝ (Fin 3)))
    {α : Type u} {s : Finset α} (𝕋 : α → ShadedTube τ (EuclideanSpace ℝ (Fin 3)))
    {ρ : NNReal} (hρ0 : 0 < ρ) (hρ4 : (ρ : ℝ) ≤ 1 / 4)
    {κ₀ : Type u} (t : Finset κ₀) (W : κ₀ → Tube (ρ * θ) (EuclideanSpace ℝ (Fin 3)))
    (hsubW : ∀ k ∈ t, (W k).carrier ⊆ T₀.carrier)
    (hused : ∀ k ∈ t, ∃ i ∈ s, (𝕋 i).carrier ⊆ (W k).carrier)
    {M : ℕ} (hM0 : 0 < M)
    (hM : ∀ i ∈ t, (open scoped Classical in t.filter (fun j ↦
      ¬ _root_.IsEssentiallyDistinct
          (outerTube hsit.pos_ambient T₀ hR ρ (W j)).carrier
          (outerTube hsit.pos_ambient T₀ hR ρ (W i)).carrier)).card ≤ M)
    (hslack : (M : ℝ) * (spineOuterCountLoss R : ℝ) ≤ (ρ : ℝ) ^ (-(ζ' - ζ)))
    (hcard : (ρ : ℝ) ^ (-2 - ζ') ≤ (t.card : ℝ)) :
    ∃ (κ₁ : Type u) (u : Finset κ₁) (V : κ₁ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
      ((u : Set κ₁).Pairwise
        fun j k ↦ _root_.IsEssentiallyDistinct (V j).carrier (V k).carrier) ∧
      (∀ j ∈ u, ∃ i ∈ s,
        (spineFamily (spineRescaleUnit hsit.pos_ambient T₀ hR) 𝕋 i).toConvexSpaceBody
          ≤ (V j).toConvexSpaceBody) ∧
      (spineOuterCountLoss R : ℝ) * (ρ : ℝ) ^ (-2 - ζ) ≤ (u.card : ℝ) := by
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have hsit2 := isRescalingSituation_scaledUp hsit hρ0 hρ4
  have hused' := outerTube_used_of_used hfr hsit2 hR (ratio_scaledUp hsit.pos_ambient ρ)
    T₀ 𝕋 W hsubW hused
  exact canonicalCoverAt_of_used_of_edMult hsit.pos_ambient T₀ (hR := hR) 𝕋 hρ0 t
    (fun k ↦ outerTube hsit.pos_ambient T₀ hR ρ (W k)) hM0 hM hused'
    (edCount_budget_of_slack hρ0 hslack hcard)

/-- **The canonical-cover datum over Lemma 9.1's window, at the ED-multiplicity price.**

The conclusion is the `hcanon` binder of
`Kakeya.ML2Reduction.multiplicity_le_of_lemma91At_outer_of_canonicalCover` character for
character. -/
theorem canonicalCover_of_upstairs_edMult {σ : NNReal} {R ϖ ζ ζ' : ℝ}
    (hsit : Tube.IsRescalingSituation θ τ σ R 3) (hR : 0 < R)
    (T₀ : Tube θ (EuclideanSpace ℝ (Fin 3)))
    {α : Type u} {s : Finset α} (𝕋 : α → ShadedTube τ (EuclideanSpace ℝ (Fin 3)))
    (hσ0 : 0 < σ) (hwin4 : ((σ ^ ϖ : NNReal) : ℝ) ≤ 1 / 4)
    (hup : ∀ ρ : NNReal, ρ ∈ Set.Icc (σ ^ (1 - ϖ)) (σ ^ ϖ) →
      ∃ (κ₀ : Type u) (t : Finset κ₀) (W : κ₀ → Tube (ρ * θ) (EuclideanSpace ℝ (Fin 3))) (M : ℕ),
        0 < M ∧
        (∀ k ∈ t, (W k).carrier ⊆ T₀.carrier) ∧
        (∀ k ∈ t, ∃ i ∈ s, (𝕋 i).carrier ⊆ (W k).carrier) ∧
        (∀ i ∈ t, (open scoped Classical in t.filter (fun j ↦
          ¬ _root_.IsEssentiallyDistinct
              (outerTube hsit.pos_ambient T₀ hR ρ (W j)).carrier
              (outerTube hsit.pos_ambient T₀ hR ρ (W i)).carrier)).card ≤ M) ∧
        (M : ℝ) * (spineOuterCountLoss R : ℝ) ≤ (ρ : ℝ) ^ (-(ζ' - ζ)) ∧
        (ρ : ℝ) ^ (-2 - ζ') ≤ (t.card : ℝ)) :
    ∀ ρ : NNReal, ρ ∈ Set.Icc (σ ^ (1 - ϖ)) (σ ^ ϖ) →
      ∃ (κ₁ : Type u) (u : Finset κ₁) (V : κ₁ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
        ((u : Set κ₁).Pairwise
          fun j k ↦ _root_.IsEssentiallyDistinct (V j).carrier (V k).carrier) ∧
        (∀ j ∈ u, ∃ i ∈ s,
          (spineFamily (spineRescaleUnit hsit.pos_ambient T₀ hR) 𝕋 i).toConvexSpaceBody
            ≤ (V j).toConvexSpaceBody) ∧
        (spineOuterCountLoss R : ℝ) * (ρ : ℝ) ^ (-2 - ζ) ≤ (u.card : ℝ) := by
  intro ρ hρ
  obtain ⟨κ₀, t, W, M, hM0, hsubW, hused, hM, hslack, hcard⟩ := hup ρ hρ
  have hρ4 : (ρ : ℝ) ≤ 1 / 4 := le_trans (by exact_mod_cast hρ.2) hwin4
  have hρ0 : 0 < ρ := lt_of_lt_of_le (NNReal.rpow_pos hσ0) hρ.1
  exact canonicalCoverAt_of_upstairs_edMult hsit hR T₀ 𝕋 hρ0 hρ4 t W hsubW hused hM0 hM
    hslack hcard

/-! ### Step 10, over the corrected interface -/

/-- **Step 10 of the non-eccentric case, fed by the ED-multiplicity interface.**

The existing consumer `Kakeya.ML2Reduction.multiplicity_le_of_lemma91At_outer_of_canonicalCover`,
with its `hcanon` binder discharged by `canonicalCover_of_upstairs_edMult`.  Every binder other
than `hup` is inherited verbatim from that theorem; `huni`'s pinning caveat is unchanged. -/
theorem multiplicity_le_of_lemma91At_outer_of_upstairs_edMult
    {β ϖ ζ ζ' ν ηd cst : ℝ} {σ : NNReal} {R : ℝ}
    (hL : Lemma91At.{u} β ϖ ζ ν ηd σ)
    -- the exact negation of the vacuity condition
    -- `Kakeya.VeryNotSticky.lemma91Binders_vacuous_of_exponents` (cited by name only — this is a
    -- hypothesis, not a consumed term, so the witness leaf is NOT imported): Lemma 9.1's binder
    -- list is jointly unsatisfiable whenever `2 + ηd < (1 - ϖ) * (2 + ζ)`, and `hζ` is exactly
    -- its negation, so it is what keeps `hL` above from being vacuously true.  Corroborated
    -- caller-side by the source's own `ζ ≤ (4/5) ζ_*` (refined l.2831–2834).  Symbol-indexed
    --: the same text in this statement's own `ζ`, `ϖ`, `ηd`.
    -- The criterion's derivation needs the scale `< 1` (monotonicity of `s^{-x}` in `x`).
    -- MEASURED: available here, and strictly stronger — `hsit.out_le_quarter` gives
    -- `(σ : ℝ) ≤ 1/4` (`Kakeya/Tube/Rescale.lean:2627`), and this statement carries `hsit`.
    -- So `σ ≤ 1` is a citation, not an added binder.
    (hζ : ζ * (1 - ϖ) ≤ ηd + 2 * ϖ)
    (hsit : Tube.IsRescalingSituation θ τ σ R 3) (hR : 0 < R) (hR1 : 1 ≤ R)
    (hτσ : (τ : ℝ) / (θ : ℝ) ≤ 4 * (σ : ℝ)) (hσ0 : 0 < σ) (hϖ : 0 ≤ ϖ)
    (hwin4 : ((σ ^ ϖ : NNReal) : ℝ) ≤ 1 / 4)
    (T₀ : Tube θ (EuclideanSpace ℝ (Fin 3))) {α : Type u} (s : Finset α)
    (𝕋 : α → ShadedTube τ (EuclideanSpace ℝ (Fin 3)))
    (hsub : ∀ i ∈ s, (𝕋 i).carrier ⊆ T₀.carrier)
    (hloss : outerLoss R ≤ σ ^ (-cst))
    (hmax : Kakeya.maxDensity s (fun i ↦ (𝕋 i).toConvexSpaceBody)
      ≤ (σ : ENNReal) ^ (-(ηd - cst)))
    (hfull : σ ^ (ηd - cst) ≤ ShadedBody.fullness s (fun i ↦ (𝕋 i).toShadedBody))
    (hcen : ∀ i ∈ s, (outerFamily hsit.pos_ambient T₀ hR σ 𝕋 i).toTube.IsCentred)
    (huni : ∃ C : NNReal, 1 ≤ C ∧ (C : ENNReal) ≤ (σ : ENNReal) ^ (-ηd) ∧
      Nonempty (ShadedTube.ShadedUniformTubeSet s
        (outerFamily hsit.pos_ambient T₀ hR σ 𝕋) (Tube.ssfGridLen σ) C))
    (hup : ∀ ρ : NNReal, ρ ∈ Set.Icc (σ ^ (1 - ϖ)) (σ ^ ϖ) →
      ∃ (κ₀ : Type u) (t : Finset κ₀) (W : κ₀ → Tube (ρ * θ) (EuclideanSpace ℝ (Fin 3))) (M : ℕ),
        0 < M ∧
        (∀ k ∈ t, (W k).carrier ⊆ T₀.carrier) ∧
        (∀ k ∈ t, ∃ i ∈ s, (𝕋 i).carrier ⊆ (W k).carrier) ∧
        (∀ i ∈ t, (open scoped Classical in t.filter (fun j ↦
          ¬ _root_.IsEssentiallyDistinct
              (outerTube hsit.pos_ambient T₀ hR ρ (W j)).carrier
              (outerTube hsit.pos_ambient T₀ hR ρ (W i)).carrier)).card ≤ M) ∧
        (M : ℝ) * (spineOuterCountLoss R : ℝ) ≤ (ρ : ℝ) ^ (-(ζ' - ζ)) ∧
        (ρ : ℝ) ^ (-2 - ζ') ≤ (t.card : ℝ)) :
    ShadedBody.multiplicity s (fun i ↦ (𝕋 i).toShadedBody)
      ≤ (σ : ENNReal) ^ ν * (s.card : ENNReal) ^ β :=
  multiplicity_le_of_lemma91At_outer_of_canonicalCover hL hζ hsit hR hR1 hτσ hσ0 hϖ T₀ s 𝕋 hsub
    hloss hmax hfull hcen huni
    (canonicalCover_of_upstairs_edMult hsit hR T₀ 𝕋 hσ0 hwin4 hup)

/-! ### Essential distinctness does not obstruct the count -/

/-- **The count clause sits below the essential-distinctness ceiling.**

`Kakeya.Tube.card_le_of_EssDistinct` caps a pairwise essentially distinct family of `ρ`-tubes in
the unit ball at `C · (1/ρ)^{2·3} = C ρ^{-6}` in dimension `3` (crude; the geometric truth is
`ρ^{-4}`).  The count clause asks for `ρ^{-2-ζ}`, which for `ζ ≤ 4` is below that ceiling at every
`ρ ≤ 1`.  **So there is no statement-level problem with Lemma 9.1's count clause**: the `ρ^{-2}`
cap found in  is a property of `Kakeya.Tube.refineToEssDistinctLeaves`'s *certificate*
`|t| / (C₃ Δ_max)`, not of essentially distinct families. -/
theorem rpow_count_le_essDistinct_ceiling {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : (ρ : ℝ) ≤ 1)
    {ζ : ℝ} (hζ4 : ζ ≤ 4) :
    (ρ : ℝ) ^ (-2 - ζ) ≤ (1 / (ρ : ℝ)) ^ (2 * 3) := by
  have hρR : (0 : ℝ) < (ρ : ℝ) := by exact_mod_cast hρ0
  have hrw : (1 / (ρ : ℝ)) ^ (2 * 3) = (ρ : ℝ) ^ (-6 : ℝ) := by
    rw [Real.rpow_neg hρR.le, show ((6 : ℝ)) = ((6 : ℕ) : ℝ) by norm_num,
      Real.rpow_natCast, one_div, ← inv_pow]
  rw [hrw]
  exact Real.rpow_le_rpow_of_exponent_ge hρR hρ1 (by linarith)

/-! ### The `ε_div` reading of the window, and the budget it closes -/

/-- **The count budget closes for the fine family read on the `ε_div` window too.**

 recorded a caveat that reading the `Δ_max` bound on the `ε_div = e` window rather
than on the `ε₂`/`ϖ` window loses the budget.  **That caveat was wrong**: it used the blueprint
ladder `η_k ≤ e · η_{k+1}`, whereas `Kakeya.ML2Spine.IsSpine.sep_le` gives the far stronger
`η_k ≤ e² β η_{k+1} / 48`.  On the `ε_div` window the exponent is `a = η_k / e ≤ η_{k+1}/480`,
which fits `ζ' - ζ = η_{k+1}/4` with a factor-`120` margin — better than the `ϖ(1-ε₂)` reading's
factor of `60`.  Both readings close; the caveat is retracted. -/
theorem spine_count_budget_closes_div {β ϖ ε₁ ε₂ e : ℝ} {gain dens : ℝ → ℝ} {N : ℕ} {η : ℕ → ℝ}
    (h : ML2Spine.IsSpine β ϖ ε₁ gain dens ε₂ e N η) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    {k : ℕ} (hk : k < N) {c : ℝ} (hc : c ≤ 119 * η (k + 1) / 480) :
    η k / e + c ≤ η (k + 1) / 2 - η (k + 1) / 4 := by
  have := spine_windowExponent_div_le h hβ0 hβ1 hk
  linarith

/-- **GWZ's `ε₂`-window sits inside the existing `ε_div` window.**

`Kakeya.ML2Reduction.IsKatzTaoDividingWindow.le_window_maxDensity` is stated on the window cut at
`ε_div = e`; the blueprint's `tildeDeltaLargeDeltamax` and the count clause are read on the
narrower window cut at `ε₂ ≥ 5e`.  This is the inclusion, so a consumer may restrict to the
narrower window and still use the existing field — no existing statement has to move. -/
theorem mem_divWindow_of_mem_eps₂Window {δt : NNReal} (hδ0 : 0 < δt) (hδ1 : δt ≤ 1)
    {e ε₂ : ℝ} (heε : e ≤ ε₂) {ρ : NNReal}
    (h : ρ ∈ Set.Icc (δt ^ (1 - ε₂)) (δt ^ ε₂)) :
    ρ ∈ Set.Icc (δt ^ (1 - e)) (δt ^ e) :=
  ⟨le_trans (NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (by linarith)) h.1,
    le_trans h.2 (NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 heε)⟩

/-- **'s isolation theorem, discharged.**

`Kakeya.ML2Reduction.canonicalCover_of_essDistinct_pushdown` reduced the canonical-cover datum to
one missing input, pairwise essential distinctness of the pushed-down family.  Here that input is
produced from the ED-multiplicity `M`, so the datum is no longer owed anything. -/
theorem essDistinct_pushdown_of_edMult {R ζ : ℝ} (hθ : 0 < θ)
    (T₀ : Tube θ (EuclideanSpace ℝ (Fin 3))) (hR : 0 < R)
    {α : Type u} {s : Finset α} (𝕋 : α → ShadedTube τ (EuclideanSpace ℝ (Fin 3)))
    {ρ : NNReal} (hρ0 : 0 < ρ) {κ₀ : Type u} (t : Finset κ₀)
    (V : κ₀ → Tube ρ (EuclideanSpace ℝ (Fin 3)))
    {M : ℕ} (hM0 : 0 < M)
    (hM : ∀ i ∈ t, (open scoped Classical in t.filter (fun j ↦
      ¬ _root_.IsEssentiallyDistinct (V j).carrier (V i).carrier)).card ≤ M)
    (hused : ∀ j ∈ t, ∃ i ∈ s,
      (spineFamily (spineRescaleUnit hθ T₀ hR) 𝕋 i).toConvexSpaceBody ≤ (V j).toConvexSpaceBody)
    (hlow : (M : ℝ) * ((spineOuterCountLoss R : ℝ) * (ρ : ℝ) ^ (-2 - ζ)) ≤ (t.card : ℝ)) :
    ∃ (κ₁ : Type u) (u : Finset κ₁) (W : κ₁ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
      ((u : Set κ₁).Pairwise
        fun j k ↦ _root_.IsEssentiallyDistinct (W j).carrier (W k).carrier) ∧
      (∀ j ∈ u, ∃ i ∈ s,
        (spineFamily (spineRescaleUnit hθ T₀ hR) 𝕋 i).toConvexSpaceBody
          ≤ (W j).toConvexSpaceBody) ∧
      (spineOuterCountLoss R : ℝ) * (ρ : ℝ) ^ (-2 - ζ) ≤ (u.card : ℝ) := by
  obtain ⟨u, hut, hED, hcard⟩ := exists_essDistinct_of_edMult hρ0 t V hM
  refine canonicalCover_of_essDistinct_pushdown hθ T₀ hR 𝕋 u V hED
    (fun j hj ↦ hused j (hut hj)) ?_
  have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM0
  have hreal : (t.card : ℝ) ≤ (M : ℝ) * (u.card : ℝ) := by exact_mod_cast hcard
  nlinarith [hlow, hreal]

end Kakeya.ML2Reduction

end
