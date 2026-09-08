/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineMiddleFactor
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineLineEDMiddle
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineMiddleProducer
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineHupProducer
public import Kakeya.DimensionThree.MainLemma2.VeryNotStickyClosed

/-!
# The middle-factor sites' scalar and threshold rows, from existing material

 and the `SpineCentredHandBackWire` seam closed four rows per site
(`hcb`, `hct`, `huni`, `hfull`).  This leaf closes five more, and it closes them by **reaching**:
every ingredient is existing, and the only new content is the plumbing plus one monotonicity lemma
that was missing.

## `hL` / `hL91` — GWZ Lemma 9.1 is already in the tree, and nothing was reading it

`Kakeya.multiplicity_le_of_card_isEssDistinct_ge` (`MainLemma2/VeryNotStickyClosed.lean`) is GWZ
Lemma 9.1, closed.  `Kakeya.ML2Reduction.Lemma91At` is the same body with the `∀ᶠ δ` stripped, and
`exists_threshold_lemma91At` turns the eventual form into a threshold.  **The link between them
was never written.**  Measured, and stated exactly, because the looser claim is false: the closed
lemma does have five consumers already (`AssemblyPointwise:125`, `BandSqueeze:2289`,
`SpineSiteWitness:843` and twice inside its own file), but **`exists_threshold_lemma91At` had zero
uses tree-wide**, and no declaration anywhere concluded `Lemma91At` from anything other than
another `Lemma91At` (`Lemma91At.mono_dens`) or from an assumed eventual form.  So the sites' `hL`
binder had no producer reaching down to GWZ Lemma 9.1.  `lemma91At_of_closed` is that producer,
and it is `exact` — the two statements are definitionally the same, which is the strongest form
the claim can take.

`Lemma91At_mono_exp` is the missing companion of the existing `Lemma91At.mono_dens`: `Lemma91At` is
**antitone in the multiplicity exponent `ν`**, since `δ ≤ 1` makes a bound at a larger `ν`
stronger.  It is needed because the four nested sites fix `ν` to their own spine expression while
Lemma 9.1 delivers `ν` existentially; with it, `hL91` at those sites reduces to one named scalar
comparison and no further geometry.

## `hwin4`, `hloss`, `hbudget`, `hcntbudget` — one threshold, four rows

All four are `δ'`-thresholds, and all four already have their existing engine
(`exists_threshold_hwin4`, `exists_threshold_outerLoss`, `exists_threshold_hup_budget`).  What was
missing is that the budgets are stated **over the window** `[δ'^{1-ϖ}, δ'^{ϖ}]` while the engine
gives a threshold in `ρ`; `exists_threshold_rpow_le` converts the one into the other, and
`exists_threshold_siteRows` returns all of them, `hL` included, under a **single** `δ₀`.
`exists_threshold_siteRows_zero` is its `m = 0` reading, which is the shape the five sites that do
not carry an ED-multiplicity ledger bind.

## A measurement, not a proof: `hsplit` at the four nested sites is degenerate

`mult_le_of_one_le_mul` records it.  At those sites `hsplit` reads

`μ(fib, outerFamily) ≤ L * (μ(t', Zρ) * μ(fib, outerFamily))`

— the **same** multiplicity on both sides — so it follows from `1 ≤ L * μ(t', Zρ)` alone and
carries no multiplicativity content.  The generic three-variable form at
`SpineMiddleProducer.lean:694` is `mu ≤ L * (mub * muf)`; the instantiation collapses `muf` onto
`mu`.  This row reads step 9's split, i.e. the `(a,b)` seam, so it is reported and **not** repaired
here.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Kakeya Kakeya.ML2Reduction
open scoped NNReal ENNReal

namespace Kakeya.ML2Reduction

universe u

/-- `exists_threshold_hwin4` at a free positive bound: `(δ^ϖ : ℝ) ≤ c` below an explicit
threshold, for any `c > 0`.  This is what turns a threshold in the *window variable* `ρ` into a
threshold in the *scale* `δ'`, since every `ρ` of the window is `≤ δ'^ϖ`. -/
theorem exists_threshold_rpow_le {ϖ : ℝ} (hϖ : 0 < ϖ) {c : ℝ} (hc : 0 < c) :
    ∃ δ₀ : NNReal, 0 < δ₀ ∧ ∀ δ : NNReal, δ ≤ δ₀ → ((δ ^ ϖ : NNReal) : ℝ) ≤ c := by
  refine ⟨(c.toNNReal) ^ (1 / ϖ), NNReal.rpow_pos (by simpa using hc), ?_⟩
  intro δ hδ
  have hstep : (δ : NNReal) ^ ϖ ≤ ((c.toNNReal) ^ (1 / ϖ)) ^ ϖ := NNReal.rpow_le_rpow hδ hϖ.le
  have hcalc : ((c.toNNReal) ^ (1 / ϖ)) ^ ϖ = c.toNNReal := by
    rw [← NNReal.rpow_mul, one_div_mul_cancel hϖ.ne', NNReal.rpow_one]
  rw [hcalc] at hstep
  have : ((δ ^ ϖ : NNReal) : ℝ) ≤ ((c.toNNReal : NNReal) : ℝ) := by exact_mod_cast hstep
  simpa [Real.coe_toNNReal _ hc.le] using this

/-- **Any constant is below `ρ^{-g}` throughout the window, below a threshold on the scale.**

The engine is the existing `Kakeya.ML2Reduction.exists_threshold_hup_budget`; what this adds is the
passage from a threshold in `ρ` to a threshold in `δ'`, using `ρ ≤ δ'^ϖ` on the window.  The
constant `A` is free, which is what lets the same row serve the two different budget constants the
six sites carry (`⌈essDistinctTubesInSelfDilate.C 3 …⌉₊ · spineOuterCountLoss R` at five of them,
`A · lineEDPushConstant R · spineOuterCountLoss R` at the line-ED site). -/
theorem exists_threshold_window_const_le {ϖ g : ℝ} (hϖ : 0 < ϖ) (hg : 0 < g) (A : ℝ) :
    ∃ δ₀ : NNReal, 0 < δ₀ ∧ ∀ δ' : NNReal, 0 < δ' → δ' ≤ δ₀ →
      ∀ ρ : NNReal, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) → A ≤ (ρ : ℝ) ^ (-g) := by
  obtain ⟨ρ₀, hρ₀0, -, hbud⟩ := exists_threshold_hup_budget (ζ := 0) (ζ' := g) (m := 0)
    (by simpa using hg) A
  obtain ⟨δ₀, hδ₀0, hδ₀⟩ := exists_threshold_rpow_le hϖ hρ₀0
  refine ⟨δ₀, hδ₀0, fun δ' h0 hle ρ hρ ↦ ?_⟩
  have hρ0 : (0:ℝ) < (ρ : ℝ) := by
    have : (0:NNReal) < ρ := lt_of_lt_of_le (NNReal.rpow_pos h0) hρ.1
    exact_mod_cast this
  have hρle : (ρ : ℝ) ≤ ρ₀ := le_trans (by exact_mod_cast hρ.2) (hδ₀ δ' hle)
  simpa using hbud _ hρ0 hρle

/-- **GWZ Lemma 9.1, as `Lemma91At`.**  `Kakeya.multiplicity_le_of_card_isEssDistinct_ge` is
`Kakeya.ML2Reduction.Lemma91At` at the parameters it produces — definitionally, hence `exact`.
This is the link that was missing: the closed lemma had no consumer in the reduction. -/
theorem lemma91At_of_closed {β : ℝ} (hβ : 0 < β) (hβ1 : β ≤ 1) :
    ∃ ϖ > (0:ℝ), ∀ ζ > (0:ℝ), ∃ ν > (0:ℝ), ∃ ηd > (0:ℝ),
      KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
      FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
      ∀ᶠ (δ : NNReal) in 𝓝[>] 0, Lemma91At.{u} β ϖ ζ ν ηd δ :=
  Kakeya.multiplicity_le_of_card_isEssDistinct_ge hβ hβ1

/-- **`Lemma91At` is ANTITONE in its multiplicity exponent `ν`** — the companion of the existing
`Kakeya.ML2Reduction.Lemma91At.mono_dens`.  A bound `μ ≤ δ^ν |s|^β` at a larger `ν` is stronger,
because `δ ≤ 1`. -/
theorem Lemma91At_mono_exp {β ϖ ζ ν ν' ηd : ℝ} {δ : NNReal} (hδ1 : δ ≤ 1)
    (h : Lemma91At.{u} β ϖ ζ ν ηd δ) (hle : ν' ≤ ν) :
    Lemma91At.{u} β ϖ ζ ν' ηd δ := by
  have hδE1 : (δ : ENNReal) ≤ 1 := by exact_mod_cast hδ1
  intro α s T hball hcen huni hmax hfull hcount
  exact le_trans (h s T hball hcen huni hmax hfull hcount)
    (mul_le_mul' (ENNReal.rpow_le_rpow_of_exponent_ge hδE1 hle) le_rfl)

/-- **The pack's `ν` meets the four nested sites' `ν`, under one named scalar comparison.**

Those sites fix `ν` to `gain (spineRung β ϖ ε₁ gain dens (k+1) / 2) + 3 qc`, their own spine
expression, while GWZ Lemma 9.1 delivers `ν` existentially.  `Lemma91At_mono_exp` bridges the two
and this states the bridge **at the sites' own expression**, so the match is the elaborator's
finding.  `hnu` is a scalar budget row and is not discharged here. -/
theorem lemma91At_siteNu {β ϖ ζ ν ηd ε₁ qc : ℝ} {gain dens : ℝ → ℝ} {k : ℕ} {δ' : NNReal}
    (hδ'1 : δ' ≤ 1) (hL91 : Lemma91At.{u} β ϖ ζ ν ηd δ')
    (hnu : gain (ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2) + 3 * qc ≤ ν) :
    Lemma91At.{u} β ϖ ζ
      (gain (ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2) + 3 * qc) ηd δ' :=
  Lemma91At_mono_exp hδ'1 hL91 hnu

theorem exists_threshold_siteRows {β ϖ ζ ζ' m ν ηd cst R : ℝ}
    (hϖ : 0 < ϖ) (hcst : 0 < cst) (hR1 : 1 ≤ R) (hgap0 : 0 < (ζ' - m) - ζ)
    (hL91 : KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
      FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
      ∀ᶠ (δ : NNReal) in 𝓝[>] 0, Lemma91At.{u} β ϖ ζ ν ηd δ)
    (hKT : KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β)
    (hF : FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β) :
    ∃ δ₀ : NNReal, 0 < δ₀ ∧ ∀ δ' : NNReal, 0 < δ' → δ' ≤ δ₀ →
      Lemma91At.{u} β ϖ ζ ν ηd δ' ∧
      ((δ' ^ ϖ : NNReal) : ℝ) ≤ 1 / 4 ∧
      outerLoss R ≤ δ' ^ (-cst) ∧
      (∀ ρ : NNReal, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) →
        (⌈((_root_.Tube.essDistinctTubesInSelfDilate.C 3
              (4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C 3) : NNReal) : ℝ)⌉₊ : ℝ)
            * (spineOuterCountLoss R : ℝ) ≤ (ρ : ℝ) ^ (-((ζ' - m) - ζ))) ∧
      (∀ ρ : NNReal, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) →
        (Kakeya.VeryNotSticky.centringCountLossConstant R : ℝ)
          * (⌈((_root_.Tube.essDistinctTubesInSelfDilate.C 3
                (4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C 3) : NNReal) : ℝ)⌉₊ : ℝ)
            * (spineOuterCountLoss R : ℝ) ≤ (ρ : ℝ) ^ (-((ζ' - m) - ζ))) := by
  classical
  obtain ⟨δ₁, hδ₁0, hLat⟩ := exists_threshold_lemma91At hL91 hKT hF
  obtain ⟨δ₂, hδ₂0, hwin⟩ := exists_threshold_hwin4 hϖ
  obtain ⟨δ₃, hδ₃0, hloss⟩ := exists_threshold_outerLoss hR1 hcst
  set A : ℝ := (⌈((_root_.Tube.essDistinctTubesInSelfDilate.C 3
      (4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C 3) : NNReal) : ℝ)⌉₊ : ℝ)
      * (spineOuterCountLoss R : ℝ) with hA
  set B : ℝ := (Kakeya.VeryNotSticky.centringCountLossConstant R : ℝ)
      * (⌈((_root_.Tube.essDistinctTubesInSelfDilate.C 3
            (4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C 3) : NNReal) : ℝ)⌉₊ : ℝ)
      * (spineOuterCountLoss R : ℝ) with hB
  obtain ⟨ρ₁, hρ₁0, -, hbud⟩ := exists_threshold_hup_budget hgap0 (max A B)
  obtain ⟨δ₄, hδ₄0, hδ₄⟩ := exists_threshold_rpow_le hϖ hρ₁0
  refine ⟨min (min δ₁ δ₂) (min δ₃ δ₄), by positivity, ?_⟩
  intro δ' hδ'0 hle
  have h1 : δ' ≤ δ₁ := le_trans hle (le_trans (min_le_left _ _) (min_le_left _ _))
  have h2 : δ' ≤ δ₂ := le_trans hle (le_trans (min_le_left _ _) (min_le_right _ _))
  have h3 : δ' ≤ δ₃ := le_trans hle (le_trans (min_le_right _ _) (min_le_left _ _))
  have h4 : δ' ≤ δ₄ := le_trans hle (le_trans (min_le_right _ _) (min_le_right _ _))
  have hbudρ : ∀ ρ : NNReal, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) →
      max A B ≤ (ρ : ℝ) ^ (-((ζ' - m) - ζ)) := by
    intro ρ hρ
    have hρ0 : (0:ℝ) < (ρ : ℝ) := by
      have : (0:NNReal) < ρ := lt_of_lt_of_le (NNReal.rpow_pos hδ'0) hρ.1
      exact_mod_cast this
    have hρle : (ρ : ℝ) ≤ ρ₁ := le_trans (by exact_mod_cast hρ.2) (hδ₄ δ' h4)
    exact hbud _ hρ0 hρle
  exact ⟨hLat δ' hδ'0 h1, hwin δ' h2, hloss δ' hδ'0 h3,
    fun ρ hρ ↦ le_trans (le_max_left _ _) (hbudρ ρ hρ),
    fun ρ hρ ↦ le_trans (le_max_right _ _) (hbudρ ρ hρ)⟩

/-- **The `m = 0` reading of the pack**, which is the shape the five sites without an
ED-multiplicity ledger bind: the two budgets at `-(ζ' - ζ)` rather than at `-((ζ' - 0) - ζ)`. -/
theorem exists_threshold_siteRows_zero {β ϖ ζ ζ' ν ηd cst R : ℝ}
    (hϖ : 0 < ϖ) (hcst : 0 < cst) (hR1 : 1 ≤ R) (hgap0 : 0 < ζ' - ζ)
    (hL91 : KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
      FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
      ∀ᶠ (δ : NNReal) in 𝓝[>] 0, Lemma91At.{u} β ϖ ζ ν ηd δ)
    (hKT : KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β)
    (hF : FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β) :
    ∃ δ₀ : NNReal, 0 < δ₀ ∧ ∀ δ' : NNReal, 0 < δ' → δ' ≤ δ₀ →
      Lemma91At.{u} β ϖ ζ ν ηd δ' ∧
      ((δ' ^ ϖ : NNReal) : ℝ) ≤ 1 / 4 ∧
      outerLoss R ≤ δ' ^ (-cst) ∧
      (∀ ρ : NNReal, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) →
        (⌈((_root_.Tube.essDistinctTubesInSelfDilate.C 3
              (4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C 3) : NNReal) : ℝ)⌉₊ : ℝ)
            * (spineOuterCountLoss R : ℝ) ≤ (ρ : ℝ) ^ (-(ζ' - ζ))) ∧
      (∀ ρ : NNReal, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) →
        (Kakeya.VeryNotSticky.centringCountLossConstant R : ℝ)
          * (⌈((_root_.Tube.essDistinctTubesInSelfDilate.C 3
                (4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C 3) : NNReal) : ℝ)⌉₊ : ℝ)
            * (spineOuterCountLoss R : ℝ) ≤ (ρ : ℝ) ^ (-(ζ' - ζ))) := by
  obtain ⟨δ₀, hδ₀0, h⟩ :=
    exists_threshold_siteRows (m := 0) hϖ hcst hR1 (by simpa using hgap0) hL91 hKT hF
  refine ⟨δ₀, hδ₀0, fun δ' h0 hle ↦ ?_⟩
  obtain ⟨hLat, hwin, hloss, hbud, hcbud⟩ := h δ' h0 hle
  exact ⟨hLat, hwin, hloss, fun ρ hρ ↦ by simpa using hbud ρ hρ,
    fun ρ hρ ↦ by simpa using hcbud ρ hρ⟩

end Kakeya.ML2Reduction

namespace Kakeya.ML2Core

/-- **The `hsplit` measurement** (see the module docstring).  `μ ≤ L * (μ_b * μ)` follows from
`1 ≤ L * μ_b`, with no finiteness and no multiplicativity.  Recorded so that the shape of the row
is on the record rather than in prose; the repair is step 9's, not this leaf's. -/
theorem mult_le_of_one_le_mul {mu mub L : ENNReal} (h : 1 ≤ L * mub) :
    mu ≤ L * (mub * mu) := by
  calc mu = 1 * mu := (one_mul mu).symm
    _ ≤ (L * mub) * mu := by gcongr
    _ = L * (mub * mu) := by rw [mul_assoc]

end Kakeya.ML2Core


/-! ## The six sites, tied by the elaborator

Each `example` feeds the pack's rows into that site's slots **by name**, alongside the seam's four. Ten rows per site at sites 1–2, nine at sites 3–6. -/

section Ties

variable {b δt δ' : NNReal} {R : ℝ}
  {hsit : Tube.IsRescalingSituation b δt δ' R 3} {hR : 0 < R}
  {T₀ : Tube b (EuclideanSpace ℝ (Fin 3))}
  {A : Type u} {fib s'' : Finset A} {qc ϖ ζ ηd β ζ' m ν cst ε₁ w ηc : ℝ}
  {gain dens : ℝ → ℝ} {k : ℕ} {δ θ τ : ℝ≥0} {Rout : ℝ}
  {hsitOut : Tube.IsRescalingSituation θ τ δt Rout 3} {hRout : 0 < Rout}
  {Tθ : Tube θ (EuclideanSpace ℝ (Fin 3))} {Y : A → ShadedTube τ (EuclideanSpace ℝ (Fin 3))}
  {κc : Type u} {t' : Finset κc} {Zρ : κc → ShadedTube b (EuclideanSpace ℝ (Fin 3))}
  {L Cf Cu : ENNReal} {Nm Alev : ℕ} {κ : ℝ}
  {Z' : A → ShadedTube δt (EuclideanSpace ℝ (Fin 3))}
  {U'' : A → ShadedTube δ' (EuclideanSpace ℝ (Fin 3))}

/-- The seam's four rows, restated as a local abbreviation of the tie's hypotheses. -/
private theorem tie_hfull (hδ'0 : 0 < δ') (hδ'1 : δ' ≤ 1) (h3qc : 3 * qc ≤ ηd)
    (hcb : Kakeya.VeryNotSticky.CentredHandBack hsit hR T₀ 0 qc fib s'' Z' U'') :
    ShadedBody.fullness s'' (fun i ↦ (U'' i).toShadedBody) ≥ δ' ^ ηd := by
  have hmono : δ' ^ ηd ≤ δ' ^ (3 * qc) := NNReal.rpow_le_rpow_of_exponent_ge hδ'0 hδ'1 h3qc
  have h := hcb.fullness_ge
  rw [← ENNReal.coe_rpow_of_ne_zero (ne_of_gt hδ'0)] at h
  exact le_trans hmono (by exact_mod_cast h)


-- TIE 1 : Kakeya.ML2Core.fine_factor_of_lemma91At_of_step8  (10 rows)
example
    (hcb : Kakeya.VeryNotSticky.CentredHandBack hsit hR T₀ 0 qc fib s'' Z' U'')
    (hct : Kakeya.VeryNotSticky.CountTransport hsit hR T₀ 0 ϖ ζ s'' Z' U'')
    (hstruct : Nonempty (ShadedTube.ShadedUniformTubeSet s'' U'' (Tube.ssfGridLen δ')
      (ShadedTube.ssfUniformConst 3)))
    (habs : ((ShadedTube.ssfUniformConst 3 : NNReal) : ENNReal) ≤ (δ' : ENNReal) ^ (-ηd))
    (hδ'0 : 0 < δ') (hδ'1 : δ' ≤ 1) (h3qc : 3 * qc ≤ ηd)
    (hL : Lemma91At.{u} β ϖ ζ ν ηd δ')
    (hwin4 : ((δ' ^ ϖ : NNReal) : ℝ) ≤ 1 / 4)
    (hloss : outerLoss R ≤ δ' ^ (-cst))
    (hbudget : ∀ ρ : NNReal, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) →
      (⌈((_root_.Tube.essDistinctTubesInSelfDilate.C 3
            (4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C 3) : NNReal) : ℝ)⌉₊ : ℝ)
          * (spineOuterCountLoss R : ℝ) ≤ (ρ : ℝ) ^ (-((ζ' - m) - ζ)))
    (hcntbudget : ∀ ρ : NNReal, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) →
      (Kakeya.VeryNotSticky.centringCountLossConstant R : ℝ)
        * (⌈((_root_.Tube.essDistinctTubesInSelfDilate.C 3
              (4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C 3) : NNReal) : ℝ)⌉₊ : ℝ)
          * (spineOuterCountLoss R : ℝ) ≤ (ρ : ℝ) ^ (-((ζ' - m) - ζ)))
    (hgap0 : 0 < (ζ' - m) - ζ) : True := by
  have _tie := Kakeya.ML2Core.fine_factor_of_lemma91At_of_step8
    (mm := 0) (β := β) (ζ' := ζ') (m := m) (ν := ν) (cst := cst)
    (hcb := hcb) (hct := hct) (huni := ⟨habs, hstruct⟩)
    (hfull := tie_hfull hδ'0 hδ'1 h3qc hcb) (h3qc := h3qc)
    (hL := hL) (hwin4 := hwin4) (hloss := hloss)
    (hbudget := hbudget) (hcntbudget := hcntbudget) (hgap := by linarith) (hδ'0 := hδ'0)
  trivial

-- TIE 2 : Kakeya.ML2Core.fine_factor_of_lemma91At_of_edCover  (10 rows)
example
    (hcb : Kakeya.VeryNotSticky.CentredHandBack hsit hR T₀ 0 qc fib s'' Z' U'')
    (hct : Kakeya.VeryNotSticky.CountTransport hsit hR T₀ 0 ϖ ζ s'' Z' U'')
    (hstruct : Nonempty (ShadedTube.ShadedUniformTubeSet s'' U'' (Tube.ssfGridLen δ')
      (ShadedTube.ssfUniformConst 3)))
    (habs : ((ShadedTube.ssfUniformConst 3 : NNReal) : ENNReal) ≤ (δ' : ENNReal) ^ (-ηd))
    (hδ'0 : 0 < δ') (hδ'1 : δ' ≤ 1) (h3qc : 3 * qc ≤ ηd)
    (hL : Lemma91At.{u} β ϖ ζ ν ηd δ')
    (hwin4 : ((δ' ^ ϖ : NNReal) : ℝ) ≤ 1 / 4)
    (hloss : outerLoss R ≤ δ' ^ (-cst))
    (hbudget : ∀ ρ : NNReal, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) →
      (⌈((_root_.Tube.essDistinctTubesInSelfDilate.C 3
            (4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C 3) : NNReal) : ℝ)⌉₊ : ℝ)
          * (spineOuterCountLoss R : ℝ) ≤ (ρ : ℝ) ^ (-(ζ' - ζ)))
    (hcntbudget : ∀ ρ : NNReal, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) →
      (Kakeya.VeryNotSticky.centringCountLossConstant R : ℝ)
        * (⌈((_root_.Tube.essDistinctTubesInSelfDilate.C 3
              (4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C 3) : NNReal) : ℝ)⌉₊ : ℝ)
          * (spineOuterCountLoss R : ℝ) ≤ (ρ : ℝ) ^ (-(ζ' - ζ)))
    (hgapz : ζ ≤ ζ')
    : True := by
  have _tie := Kakeya.ML2Core.fine_factor_of_lemma91At_of_edCover
    (mm := 0) (β := β) (ζ' := ζ') (ν := ν) (cst := cst)
    (hcb := hcb) (hct := hct) (huni := ⟨habs, hstruct⟩)
    (hfull := tie_hfull hδ'0 hδ'1 h3qc hcb) (h3qc := h3qc)
    (hL := hL) (hwin4 := hwin4) (hloss := hloss)
    (hbudget := hbudget) (hcntbudget := hcntbudget) (hgap := hgapz) (hδ'0 := hδ'0)
  trivial

set_option maxHeartbeats 1600000 in
-- TIE 3 : Kakeya.ML2Core.middle_factor_of_edNodes_sharp'  (9 rows)
example
    (hcb : Kakeya.VeryNotSticky.CentredHandBack hsit hR T₀ 0 qc fib s''
      (Kakeya.ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y) U'')
    (hct : Kakeya.VeryNotSticky.CountTransport hsit hR T₀ 0 ϖ ζ s''
      (Kakeya.ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y) U'')
    (hstruct : Nonempty (ShadedTube.ShadedUniformTubeSet s'' U'' (Tube.ssfGridLen δ')
      (ShadedTube.ssfUniformConst 3)))
    (habs : ((ShadedTube.ssfUniformConst 3 : NNReal) : ENNReal) ≤ (δ' : ENNReal) ^ (-ηd))
    (hδ'0 : 0 < δ') (hδ'1 : δ' ≤ 1) (h3qc : 3 * qc ≤ ηd)
    (hL91 : Lemma91At.{u} β ϖ ζ
      (gain (ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2) + 3 * qc) ηd δ')
    (hwin4 : ((δ' ^ ϖ : NNReal) : ℝ) ≤ 1 / 4)
    (hloss : outerLoss R ≤ δ' ^ (-cst))
    (hbudget : ∀ ρ : NNReal, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) →
      (⌈((_root_.Tube.essDistinctTubesInSelfDilate.C 3
            (4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C 3) : NNReal) : ℝ)⌉₊ : ℝ)
          * (spineOuterCountLoss R : ℝ) ≤ (ρ : ℝ) ^ (-(ζ' - ζ)))
    (hcntbudget : ∀ ρ : NNReal, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) →
      (Kakeya.VeryNotSticky.centringCountLossConstant R : ℝ)
        * (⌈((_root_.Tube.essDistinctTubesInSelfDilate.C 3
              (4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C 3) : NNReal) : ℝ)⌉₊ : ℝ)
          * (spineOuterCountLoss R : ℝ) ≤ (ρ : ℝ) ^ (-(ζ' - ζ)))
    (hgapz : ζ ≤ ζ')
    (hLmub : (1 : ENNReal) ≤ L * ShadedBody.multiplicity t' (fun j ↦ (Zρ j).toShadedBody))
    : True := by
  have _tie := Kakeya.ML2Core.middle_factor_of_edNodes_sharp'
    (mm := 0) (hsitOut := hsitOut) (β := β) (ε₁ := ε₁) (gain := gain) (dens := dens) (k := k)
    (δ := δ) (w := w) (κc := κc) (t' := t') (Zρ := Zρ) (ηc := ηc)
    (cst := cst) (ζ := ζ) (ζ' := ζ') (ϖ := ϖ) (ηd := ηd) (qc := qc) (L := L)
    (Cf := Cf) (Cu := Cu) (Nm := Nm) (κ := κ)
    (hcb := hcb) (hct := hct) (huni := ⟨habs, hstruct⟩)
    (hfull := tie_hfull hδ'0 hδ'1 h3qc hcb) (h3qc := h3qc)
    (hL91 := hL91)
    (hwin4 := hwin4) (hloss := hloss) (hgap := hgapz)
    (hbudget := hbudget) (hcntbudget := hcntbudget) (hδ'0 := hδ'0)
    (hsplit := Kakeya.ML2Core.mult_le_of_one_le_mul hLmub)
  trivial

set_option maxHeartbeats 1600000 in
-- TIE 4 : Kakeya.ML2Core.middle_factor_of_lineEDNodes_sharp  (9 rows)
example
    (hcb : Kakeya.VeryNotSticky.CentredHandBack hsit hR T₀ 0 qc fib s''
      (Kakeya.ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y) U'')
    (hct : Kakeya.VeryNotSticky.CountTransport hsit hR T₀ 0 ϖ ζ s''
      (Kakeya.ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y) U'')
    (hstruct : Nonempty (ShadedTube.ShadedUniformTubeSet s'' U'' (Tube.ssfGridLen δ')
      (ShadedTube.ssfUniformConst 3)))
    (habs : ((ShadedTube.ssfUniformConst 3 : NNReal) : ENNReal) ≤ (δ' : ENNReal) ^ (-ηd))
    (hδ'0 : 0 < δ') (hδ'1 : δ' ≤ 1) (h3qc : 3 * qc ≤ ηd)
    (hL91 : Lemma91At.{u} β ϖ ζ
      (gain (ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2) + 3 * qc) ηd δ')
    (hwin4 : ((δ' ^ ϖ : NNReal) : ℝ) ≤ 1 / 4)
    (hloss : outerLoss R ≤ δ' ^ (-cst))
    (hbudget : ∀ ρ : NNReal, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) →
      (Alev : ℝ) * (lineEDPushConstant R : ℝ)
          * (spineOuterCountLoss R : ℝ) ≤ (ρ : ℝ) ^ (-(ζ' - ζ)))
    (hcntbudget : ∀ ρ : NNReal, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) →
      (Kakeya.VeryNotSticky.centringCountLossConstant R : ℝ)
        * (Alev : ℝ) * (lineEDPushConstant R : ℝ)
          * (spineOuterCountLoss R : ℝ) ≤ (ρ : ℝ) ^ (-(ζ' - ζ)))
    (hgapz : ζ ≤ ζ')
    (hLmub : (1 : ENNReal) ≤ L * ShadedBody.multiplicity t' (fun j ↦ (Zρ j).toShadedBody))
    : True := by
  have _tie := Kakeya.ML2Core.middle_factor_of_lineEDNodes_sharp
    (mm := 0) (hsitOut := hsitOut) (β := β) (ε₁ := ε₁) (gain := gain) (dens := dens) (k := k)
    (δ := δ) (w := w) (κc := κc) (t' := t') (Zρ := Zρ) (ηc := ηc)
    (cst := cst) (ζ := ζ) (ζ' := ζ') (ϖ := ϖ) (ηd := ηd) (qc := qc) (L := L)
    (Cf := Cf) (Cu := Cu) (Nm := Nm) (κ := κ) (A := Alev)
    (hcb := hcb) (hct := hct) (huni := ⟨habs, hstruct⟩)
    (hfull := tie_hfull hδ'0 hδ'1 h3qc hcb) (h3qc := h3qc)
    (hL91 := hL91)
    (hwin4 := hwin4) (hloss := hloss) (hgap := hgapz)
    (hbudget := hbudget) (hcntbudget := hcntbudget) (hδ'0 := hδ'0)
    (hsplit := Kakeya.ML2Core.mult_le_of_one_le_mul hLmub)
  trivial

set_option maxHeartbeats 1600000 in
-- TIE 5 : Kakeya.ML2Core.middle_factor_of_edNodes  (9 rows)
example
    (hcb : Kakeya.VeryNotSticky.CentredHandBack hsit hR T₀ 0 qc fib s''
      (Kakeya.ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y) U'')
    (hct : Kakeya.VeryNotSticky.CountTransport hsit hR T₀ 0 ϖ ζ s''
      (Kakeya.ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y) U'')
    (hstruct : Nonempty (ShadedTube.ShadedUniformTubeSet s'' U'' (Tube.ssfGridLen δ')
      (ShadedTube.ssfUniformConst 3)))
    (habs : ((ShadedTube.ssfUniformConst 3 : NNReal) : ENNReal) ≤ (δ' : ENNReal) ^ (-ηd))
    (hδ'0 : 0 < δ') (hδ'1 : δ' ≤ 1) (h3qc : 3 * qc ≤ ηd)
    (hL91 : Lemma91At.{u} β ϖ ζ
      (gain (ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2) + 3 * qc) ηd δ')
    (hwin4 : ((δ' ^ ϖ : NNReal) : ℝ) ≤ 1 / 4)
    (hloss : outerLoss R ≤ δ' ^ (-cst))
    (hbudget : ∀ ρ : NNReal, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) →
      (⌈((_root_.Tube.essDistinctTubesInSelfDilate.C 3
            (4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C 3) : NNReal) : ℝ)⌉₊ : ℝ)
          * (spineOuterCountLoss R : ℝ) ≤ (ρ : ℝ) ^ (-(ζ' - ζ)))
    (hcntbudget : ∀ ρ : NNReal, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) →
      (Kakeya.VeryNotSticky.centringCountLossConstant R : ℝ)
        * (⌈((_root_.Tube.essDistinctTubesInSelfDilate.C 3
              (4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C 3) : NNReal) : ℝ)⌉₊ : ℝ)
          * (spineOuterCountLoss R : ℝ) ≤ (ρ : ℝ) ^ (-(ζ' - ζ)))
    (hgapz : ζ ≤ ζ')
    (hLmub : (1 : ENNReal) ≤ L * ShadedBody.multiplicity t' (fun j ↦ (Zρ j).toShadedBody))
    : True := by
  have _tie := Kakeya.ML2Core.middle_factor_of_edNodes
    (mm := 0) (hsitOut := hsitOut) (β := β) (ε₁ := ε₁) (gain := gain) (dens := dens) (k := k)
    (δ := δ) (w := w) (κc := κc) (t' := t') (Zρ := Zρ) (ηc := ηc)
    (cst := cst) (ζ := ζ) (ζ' := ζ') (ϖ := ϖ) (ηd := ηd) (qc := qc) (L := L)
    (Cf := Cf) (Cu := Cu) (Nm := Nm) (κ := κ)
    (hcb := hcb) (hct := hct) (huni := ⟨habs, hstruct⟩)
    (hfull := tie_hfull hδ'0 hδ'1 h3qc hcb) (h3qc := h3qc)
    (hL91 := hL91)
    (hwin4 := hwin4) (hloss := hloss) (hgap := hgapz)
    (hbudget := hbudget) (hcntbudget := hcntbudget) (hδ'0 := hδ'0)
    (hsplit := Kakeya.ML2Core.mult_le_of_one_le_mul hLmub)
  trivial

set_option maxHeartbeats 1600000 in
-- TIE 6 : Kakeya.ML2Core.middle_factor_of_edNodes_sharp  (9 rows)
example
    (hcb : Kakeya.VeryNotSticky.CentredHandBack hsit hR T₀ 0 qc fib s''
      (Kakeya.ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y) U'')
    (hct : Kakeya.VeryNotSticky.CountTransport hsit hR T₀ 0 ϖ ζ s''
      (Kakeya.ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y) U'')
    (hstruct : Nonempty (ShadedTube.ShadedUniformTubeSet s'' U'' (Tube.ssfGridLen δ')
      (ShadedTube.ssfUniformConst 3)))
    (habs : ((ShadedTube.ssfUniformConst 3 : NNReal) : ENNReal) ≤ (δ' : ENNReal) ^ (-ηd))
    (hδ'0 : 0 < δ') (hδ'1 : δ' ≤ 1) (h3qc : 3 * qc ≤ ηd)
    (hL91 : Lemma91At.{u} β ϖ ζ
      (gain (ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2) + 3 * qc) ηd δ')
    (hwin4 : ((δ' ^ ϖ : NNReal) : ℝ) ≤ 1 / 4)
    (hloss : outerLoss R ≤ δ' ^ (-cst))
    (hbudget : ∀ ρ : NNReal, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) →
      (⌈((_root_.Tube.essDistinctTubesInSelfDilate.C 3
            (4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C 3) : NNReal) : ℝ)⌉₊ : ℝ)
          * (spineOuterCountLoss R : ℝ) ≤ (ρ : ℝ) ^ (-(ζ' - ζ)))
    (hcntbudget : ∀ ρ : NNReal, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) →
      (Kakeya.VeryNotSticky.centringCountLossConstant R : ℝ)
        * (⌈((_root_.Tube.essDistinctTubesInSelfDilate.C 3
              (4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C 3) : NNReal) : ℝ)⌉₊ : ℝ)
          * (spineOuterCountLoss R : ℝ) ≤ (ρ : ℝ) ^ (-(ζ' - ζ)))
    (hgapz : ζ ≤ ζ')
    (hLmub : (1 : ENNReal) ≤ L * ShadedBody.multiplicity t' (fun j ↦ (Zρ j).toShadedBody))
    : True := by
  have _tie := Kakeya.ML2Core.middle_factor_of_edNodes_sharp
    (mm := 0) (hsitOut := hsitOut) (β := β) (ε₁ := ε₁) (gain := gain) (dens := dens) (k := k)
    (δ := δ) (w := w) (κc := κc) (t' := t') (Zρ := Zρ) (ηc := ηc)
    (cst := cst) (ζ := ζ) (ζ' := ζ') (ϖ := ϖ) (ηd := ηd) (qc := qc) (L := L)
    (Cf := Cf) (Cu := Cu) (Nm := Nm) (κ := κ)
    (hcb := hcb) (hct := hct) (huni := ⟨habs, hstruct⟩)
    (hfull := tie_hfull hδ'0 hδ'1 h3qc hcb) (h3qc := h3qc)
    (hL91 := hL91)
    (hwin4 := hwin4) (hloss := hloss) (hgap := hgapz)
    (hbudget := hbudget) (hcntbudget := hcntbudget) (hδ'0 := hδ'0)
    (hsplit := Kakeya.ML2Core.mult_le_of_one_le_mul hLmub)
  trivial

end Ties

end
