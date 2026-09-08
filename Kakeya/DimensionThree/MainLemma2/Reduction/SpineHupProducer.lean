/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineEDMultBound

/-!
# The producer of `hup`: step 8's count carried onto an essentially distinct cover

Blueprint: `blueprint/src/GWZAdapted/section9.tex`, the non-eccentric case, step 8 into step 10.

`Reduction/SpineEDMultBound.lean` states step 10 over an interface whose only geometric input is
**pairwise essential distinctness of the upstairs parents**.  This file produces that interface
from what step 8 actually delivers.

## The one loss, and where it is spent

`Kakeya.ML2Spine.spine_tube_card_lower` delivers `ρ^{-2-ζ'} ≤ |t₈|` on a family that is *not*
essentially distinct.  `Kakeya.Tube.exists_maximal_essDistinct` extracts a maximal essentially
distinct subfamily, and the extraction costs that family's **ED-multiplicity** `M`.  Writing
`M ≤ ρ^{-m}`, the surviving count is `ρ^{-2-(ζ'-m)} ≤ |t|` (`exists_edCover_of_count`): the
extraction spends exactly `m` of the reading gap.  Everything downstream — the push-down, the
constant `M` of `edMult_le_of_upstairs_essDistinct`, the outer transport `spineOuterCountLoss R` —
is already paid for, so **the whole non-eccentric count chain closes iff `m < ζ' - ζ`**, and on the
spine an `m` as large as the step-3 density exponent `η_k/e` is affordable with a factor-`120`
margin (`spine_hup_gap_of_div`).

`m` is the *upstairs* ED-multiplicity exponent.  It is not the constant of
`Reduction/SpineEDMultBound.lean`: that one bounds the ED-multiplicity of the **pushed-down**
family *given* upstairs essential distinctness, and `Tube.essDistinctTubesInSelfDilate` — which is
what makes it a constant — has nothing to start from upstairs.  It is carried here as a
parameter, exactly as `w256gen`'s assembly carries it.

## What is produced and what is not

Produced: all five clauses of `hup` (`hup_of_step8`), the window-truncation threshold `hwin4`
(`exists_threshold_hwin4`), and the budget clause as a threshold on `ρ`
(`exists_threshold_hup_budget`); then `hcanon` (`canonicalCover_of_step8`) and step 10
(`multiplicity_le_of_lemma91At_outer_of_step8`).

**Not produced: `huni`.**  The binder of
`Kakeya.ML2Reduction.multiplicity_le_of_lemma91At_outer_of_canonicalCover` asks for
`ShadedTube.ShadedUniformTubeSet s (outerFamily …) (Tube.ssfGridLen σ) C` — uniformity on the
**whole** index set `s`, with the **unrefined** outer family.  The tree's uniformiser
`Kakeya.ML2Reduction.exists_outerShadedUniformTubeSet` returns instead a subfamily `s' ⊆ s` and a
shade-shrunk `U'`, with uniformity on `(s', U')`.  Passing from `(s', U')` back to
`(s, outerFamily)` is an **extension**, not a restriction, and it is false in general — the
uniformiser had to refine precisely because the whole family need not be uniform.  So this is not
a missing hereditary lemma: the restriction direction is already available in the tree
(`Kakeya.ml1Boot.ShadedTube.ShadedUniformTubeSet.restrict_of_shadeClass_dense`,
`restrict_of_shade_eq_empty`, `MainLemma1/AliveBand.lean:440–460`, read not imported), and it is
the wrong direction.  The route is the one  identified: bypass the wrapper and apply
`Kakeya.ML2Reduction.Lemma91At` at `(s', U')` directly, which is what `w256gen`'s
`count_clause_at_uniformised_of_canonicalCover` does.  `huni` is therefore left as an inherited
binder here, unproduced and flagged.

## Main declarations

* `Kakeya.ML2Reduction.exists_edCover_of_count` — the extraction with the count ledger.
* `Kakeya.ML2Reduction.hup_of_step8` — **the producer of `hup`**.
* `Kakeya.ML2Reduction.exists_threshold_hwin4`,
  `Kakeya.ML2Reduction.exists_threshold_hup_budget` — the two thresholds.
* `Kakeya.ML2Reduction.spine_hup_gap_of_div` — the single remaining inequality, on the spine.
* `Kakeya.ML2Reduction.canonicalCover_of_step8`,
  `Kakeya.ML2Reduction.multiplicity_le_of_lemma91At_outer_of_step8` — `hcanon`, and step 10.
-/

@[expose] public section

open MeasureTheory Metric Set ConvexSpaceBody
open scoped NNReal ENNReal

namespace Kakeya.ML2Reduction

universe u

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

variable {θ τ σ : NNReal}

/-- **The essential-distinctness extraction, with the count ledger.**

Step 8 delivers a count `ρ^{-2-ζ'} ≤ |t₈|` on a family that is *not* essentially distinct.
Extracting a maximal essentially distinct subfamily costs the family's ED-multiplicity `M`, and if
`M ≤ ρ^{-m}` the surviving count is `ρ^{-2-(ζ'-m)} ≤ |t|`: **the extraction spends exactly `m` of
the reading gap `ζ' - ζ`.** -/
theorem exists_edCover_of_count [Nontrivial E] {ρ : NNReal} (hρ0 : 0 < ρ) (hθ0 : 0 < θ)
    {ζ' m : ℝ} {κ₀ : Type*} {t₈ : Finset κ₀} (W : κ₀ → Tube (ρ * θ) E) {M : ℕ}
    (hM : ∀ i ∈ t₈, (open scoped Classical in t₈.filter (fun j ↦
      ¬ _root_.IsEssentiallyDistinct (W j).carrier (W i).carrier)).card ≤ M)
    (hMρ : (M : ℝ) ≤ (ρ : ℝ) ^ (-m))
    (hcard : (ρ : ℝ) ^ (-2 - ζ') ≤ (t₈.card : ℝ)) :
    ∃ t ⊆ t₈,
      ((t : Set κ₀).Pairwise
        fun j k ↦ _root_.IsEssentiallyDistinct (W j).carrier (W k).carrier) ∧
      (ρ : ℝ) ^ (-2 - (ζ' - m)) ≤ (t.card : ℝ) := by
  classical
  have hρR : (0 : ℝ) < (ρ : ℝ) := by exact_mod_cast hρ0
  have hδ0 : 0 < ρ * θ := mul_pos hρ0 hθ0
  obtain ⟨t, hts, hED, hle⟩ := exists_essDistinct_of_edMult hδ0 t₈ W hM
  refine ⟨t, hts, hED, ?_⟩
  have hreal : (t₈.card : ℝ) ≤ (M : ℝ) * (t.card : ℝ) := by exact_mod_cast hle
  have hchain : (ρ : ℝ) ^ (-2 - ζ') ≤ (ρ : ℝ) ^ (-m) * (t.card : ℝ) := by
    refine hcard.trans (hreal.trans ?_)
    exact mul_le_mul_of_nonneg_right hMρ (Nat.cast_nonneg _)
  have hmul := mul_le_mul_of_nonneg_right hchain (Real.rpow_nonneg hρR.le m)
  have hL : (ρ : ℝ) ^ (-2 - ζ') * (ρ : ℝ) ^ m = (ρ : ℝ) ^ (-2 - (ζ' - m)) := by
    rw [← Real.rpow_add hρR]; ring_nf
  have hR : (ρ : ℝ) ^ (-m) * (t.card : ℝ) * (ρ : ℝ) ^ m = (t.card : ℝ) := by
    have : (ρ : ℝ) ^ (-m) * (ρ : ℝ) ^ m = 1 := by
      rw [← Real.rpow_add hρR]; simp
    calc (ρ : ℝ) ^ (-m) * (t.card : ℝ) * (ρ : ℝ) ^ m
        = ((ρ : ℝ) ^ (-m) * (ρ : ℝ) ^ m) * (t.card : ℝ) := by ring
      _ = (t.card : ℝ) := by rw [this, one_mul]
  rwa [hL, hR] at hmul

/-! ### The `hup` bundle, produced -/

/-- **The producer of `hup`.**

From step 8's count on Lemma 9.1's window — already bridged from the spine's `σ`-window by
`window_count_of_spine_window`, so the shape here is the post-bridge one — together with the
parent containment, the all-used clause, and an ED-multiplicity bound `M ≤ ρ^{-m}` on step 8's
family, this produces the `hup` bundle of
`Kakeya.ML2Reduction.canonicalCover_of_upstairs_essDistinct` **at the reduced reading exponent
`ζ' - m`**.  The extraction is `Kakeya.Tube.exists_maximal_essDistinct` (through
`exists_edCover_of_count`), and its loss is the only one spent. -/
theorem hup_of_step8 [Nontrivial E] {ϖ ζ ζ' m : ℝ} (hθ0 : 0 < θ)
    (hσ0 : 0 < σ) (T₀ : Tube θ E) {α : Type u} {s : Finset α} (𝕋 : α → ShadedTube τ E)
    {Lam : ℝ}
    (hstep8 : ∀ ρ : NNReal, ρ ∈ Set.Icc (σ ^ (1 - ϖ)) (σ ^ ϖ) →
      ∃ (κ₀ : Type u) (t₈ : Finset κ₀) (W : κ₀ → Tube (ρ * θ) E) (M : ℕ),
        (∀ k ∈ t₈, (W k).carrier ⊆ T₀.carrier) ∧
        (∀ k ∈ t₈, ∃ i ∈ s, (𝕋 i).carrier ⊆ (W k).carrier) ∧
        (∀ i ∈ t₈, (open scoped Classical in t₈.filter (fun j ↦
          ¬ _root_.IsEssentiallyDistinct (W j).carrier (W i).carrier)).card ≤ M) ∧
        (M : ℝ) ≤ (ρ : ℝ) ^ (-m) ∧
        (ρ : ℝ) ^ (-2 - ζ') ≤ (t₈.card : ℝ))
    (hbudget : ∀ ρ : NNReal, ρ ∈ Set.Icc (σ ^ (1 - ϖ)) (σ ^ ϖ) →
      Lam ≤ (ρ : ℝ) ^ (-((ζ' - m) - ζ))) :
    ∀ ρ : NNReal, ρ ∈ Set.Icc (σ ^ (1 - ϖ)) (σ ^ ϖ) →
      ∃ (κ₀ : Type u) (t : Finset κ₀) (W : κ₀ → Tube (ρ * θ) E),
        (∀ k ∈ t, (W k).carrier ⊆ T₀.carrier) ∧
        (∀ k ∈ t, ∃ i ∈ s, (𝕋 i).carrier ⊆ (W k).carrier) ∧
        ((t : Set κ₀).Pairwise
          fun j k ↦ _root_.IsEssentiallyDistinct (W j).carrier (W k).carrier) ∧
        Lam ≤ (ρ : ℝ) ^ (-((ζ' - m) - ζ)) ∧
        (ρ : ℝ) ^ (-2 - (ζ' - m)) ≤ (t.card : ℝ) := by
  intro ρ hρ
  have hρ0 : 0 < ρ := lt_of_lt_of_le (NNReal.rpow_pos hσ0) hρ.1
  obtain ⟨κ₀, t₈, W, M, hsubW, hused, hM, hMρ, hcard⟩ := hstep8 ρ hρ
  obtain ⟨t, hts, hED, hcnt⟩ := exists_edCover_of_count hρ0 hθ0 W hM hMρ hcard
  exact ⟨κ₀, t, W, fun k hk ↦ hsubW k (hts hk), fun k hk ↦ hused k (hts hk), hED,
    hbudget ρ hρ, hcnt⟩

/-! ### The two thresholds the producer still needs -/

/-- **`hwin4` is a threshold on `σ`.**  For `ϖ > 0` the window-truncation hypothesis
`(σ^ϖ : ℝ) ≤ 1/4` holds at every `σ ≤ (1/4)^{1/ϖ}`, hence for all sufficiently small `σ`. -/
theorem exists_threshold_hwin4 {ϖ : ℝ} (hϖ : 0 < ϖ) :
    ∃ σ₀ : NNReal, 0 < σ₀ ∧ ∀ σ : NNReal, σ ≤ σ₀ → ((σ ^ ϖ : NNReal) : ℝ) ≤ 1 / 4 := by
  refine ⟨(1 / 4 : NNReal) ^ (1 / ϖ), NNReal.rpow_pos (by norm_num), ?_⟩
  intro σ hσ
  have hstep : (σ : NNReal) ^ ϖ ≤ ((1 / 4 : NNReal) ^ (1 / ϖ)) ^ ϖ :=
    NNReal.rpow_le_rpow hσ hϖ.le
  have hcalc : ((1 / 4 : NNReal) ^ (1 / ϖ)) ^ ϖ = (1 / 4 : NNReal) := by
    rw [← NNReal.rpow_mul, one_div_mul_cancel hϖ.ne', NNReal.rpow_one]
  rw [hcalc] at hstep
  calc ((σ ^ ϖ : NNReal) : ℝ) ≤ ((1 / 4 : NNReal) : ℝ) := by exact_mod_cast hstep
    _ = 1 / 4 := by norm_num

/-- **The budget clause is a threshold on `ρ`, provided `m < ζ' - ζ`.**  This is the whole
arithmetic content of the producer: the ED-multiplicity exponent `m` of step 8's family must be
strictly below the reading gap, and then every constant fits. -/
theorem exists_threshold_hup_budget {ζ ζ' m : ℝ} (hgap : 0 < (ζ' - m) - ζ) (A : ℝ) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ρ₀ ≤ 1 ∧
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → A ≤ ρ ^ (-((ζ' - m) - ζ)) :=
  exists_threshold_const_le_rpow hgap

/-- **The single remaining inequality, on the spine.**  At `ζ' = η_{k+1}/2` (what
`Kakeya.ML2Spine.spine_tube_card_lower` delivers) and `ζ = η_{k+1}/4` (the recommended reading of
Lemma 9.1), an ED-multiplicity exponent `m` as large as the step-3 density exponent `η_k/e` is
still affordable — with a factor-`120` margin, by `spine_windowExponent_div_le`. -/
theorem spine_hup_gap_of_div {β ϖ ε₁ ε₂ e : ℝ} {gain dens : ℝ → ℝ} {N : ℕ} {η : ℕ → ℝ}
    (h : ML2Spine.IsSpine β ϖ ε₁ gain dens ε₂ e N η) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    {k : ℕ} (hk : k < N) {m : ℝ} (hm : m ≤ η k / e) :
    0 < (η (k + 1) / 2 - m) - η (k + 1) / 4 := by
  have hdiv := spine_windowExponent_div_le h hβ0 hβ1 hk
  have hpos := h.rung_pos (k + 1)
  linarith

/-! ### The composition: step 8 ⟹ `hcanon` ⟹ step 10 -/

/-- **The canonical-cover datum, from step 8.**  `hup_of_step8` feeding
`canonicalCover_of_upstairs_essDistinct`, at the reduced reading exponent `ζ' - m`. -/
theorem canonicalCover_of_step8 {R ϖ ζ ζ' m : ℝ}
    (hsit : Tube.IsRescalingSituation θ τ σ R 3) (hR : 0 < R)
    (T₀ : Tube θ (EuclideanSpace ℝ (Fin 3)))
    {α : Type u} {s : Finset α} (𝕋 : α → ShadedTube τ (EuclideanSpace ℝ (Fin 3)))
    (hσ0 : 0 < σ) (hwin4 : ((σ ^ ϖ : NNReal) : ℝ) ≤ 1 / 4)
    (hstep8 : ∀ ρ : NNReal, ρ ∈ Set.Icc (σ ^ (1 - ϖ)) (σ ^ ϖ) →
      ∃ (κ₀ : Type u) (t₈ : Finset κ₀)
        (W : κ₀ → Tube (ρ * θ) (EuclideanSpace ℝ (Fin 3))) (M : ℕ),
        (∀ k ∈ t₈, (W k).carrier ⊆ T₀.carrier) ∧
        (∀ k ∈ t₈, ∃ i ∈ s, (𝕋 i).carrier ⊆ (W k).carrier) ∧
        (∀ i ∈ t₈, (open scoped Classical in t₈.filter (fun j ↦
          ¬ _root_.IsEssentiallyDistinct (W j).carrier (W i).carrier)).card ≤ M) ∧
        (M : ℝ) ≤ (ρ : ℝ) ^ (-m) ∧
        (ρ : ℝ) ^ (-2 - ζ') ≤ (t₈.card : ℝ))
    (hbudget : ∀ ρ : NNReal, ρ ∈ Set.Icc (σ ^ (1 - ϖ)) (σ ^ ϖ) →
      (⌈((_root_.Tube.essDistinctTubesInSelfDilate.C 3
            (4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C 3) : NNReal) : ℝ)⌉₊ : ℝ)
          * (spineOuterCountLoss R : ℝ) ≤ (ρ : ℝ) ^ (-((ζ' - m) - ζ))) :
    ∀ ρ : NNReal, ρ ∈ Set.Icc (σ ^ (1 - ϖ)) (σ ^ ϖ) →
      ∃ (κ₁ : Type u) (u : Finset κ₁) (V : κ₁ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
        ((u : Set κ₁).Pairwise
          fun j k ↦ _root_.IsEssentiallyDistinct (V j).carrier (V k).carrier) ∧
        (∀ j ∈ u, ∃ i ∈ s,
          (spineFamily (spineRescaleUnit hsit.pos_ambient T₀ hR) 𝕋 i).toConvexSpaceBody
            ≤ (V j).toConvexSpaceBody) ∧
        (spineOuterCountLoss R : ℝ) * (ρ : ℝ) ^ (-2 - ζ) ≤ (u.card : ℝ) :=
  canonicalCover_of_upstairs_essDistinct hsit hR T₀ 𝕋 hσ0 hwin4
    (hup_of_step8 hsit.pos_ambient hσ0 T₀ 𝕋 hstep8 hbudget)

/-- **Step 10, from step 8.**  The whole non-eccentric count chain in one statement: step 8's
count, the essential-distinctness extraction, the push-down, the outer transport and the existing
`Kakeya.ML2Reduction.multiplicity_le_of_lemma91At_outer_of_canonicalCover`. -/
theorem multiplicity_le_of_lemma91At_outer_of_step8
    {β ϖ ζ ζ' m ν ηd cst : ℝ} {R : ℝ}
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
    (hstep8 : ∀ ρ : NNReal, ρ ∈ Set.Icc (σ ^ (1 - ϖ)) (σ ^ ϖ) →
      ∃ (κ₀ : Type u) (t₈ : Finset κ₀)
        (W : κ₀ → Tube (ρ * θ) (EuclideanSpace ℝ (Fin 3))) (M : ℕ),
        (∀ k ∈ t₈, (W k).carrier ⊆ T₀.carrier) ∧
        (∀ k ∈ t₈, ∃ i ∈ s, (𝕋 i).carrier ⊆ (W k).carrier) ∧
        (∀ i ∈ t₈, (open scoped Classical in t₈.filter (fun j ↦
          ¬ _root_.IsEssentiallyDistinct (W j).carrier (W i).carrier)).card ≤ M) ∧
        (M : ℝ) ≤ (ρ : ℝ) ^ (-m) ∧
        (ρ : ℝ) ^ (-2 - ζ') ≤ (t₈.card : ℝ))
    (hbudget : ∀ ρ : NNReal, ρ ∈ Set.Icc (σ ^ (1 - ϖ)) (σ ^ ϖ) →
      (⌈((_root_.Tube.essDistinctTubesInSelfDilate.C 3
            (4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C 3) : NNReal) : ℝ)⌉₊ : ℝ)
          * (spineOuterCountLoss R : ℝ) ≤ (ρ : ℝ) ^ (-((ζ' - m) - ζ))) :
    ShadedBody.multiplicity s (fun i ↦ (𝕋 i).toShadedBody)
      ≤ (σ : ENNReal) ^ ν * (s.card : ENNReal) ^ β :=
  multiplicity_le_of_lemma91At_outer_of_canonicalCover hL hζ hsit hR hR1 hτσ hσ0 hϖ T₀ s 𝕋 hsub
    hloss hmax hfull hcen huni
    (canonicalCover_of_step8 hsit hR T₀ 𝕋 hσ0 hwin4 hstep8 hbudget)

end Kakeya.ML2Reduction

end
