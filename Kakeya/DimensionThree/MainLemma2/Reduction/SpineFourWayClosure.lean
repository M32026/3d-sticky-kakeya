/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineNewParentFactor
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCentredHandBackWire

/-!
# Closing the four-way producer's own rows: the translate, the `a = 0` case, and `hfullπ`

Three rows, and one correction to a measurement of mine.

## 0. Correction: the translation invariance was existing all along

I reported that the tree had no translation-invariance lemma for `ShadedBody.multiplicity`,
on a `grep` for `multiplicity_translate` / `translate_multiplicity` restricted to `theorem`.
**That was wrong twice over**: the declaration is `ShadedBody.multiplicity_translate_const`
(`Kakeya/Multiplicity.lean:661`) and it is a `lemma`, not a `theorem`.  The row was never open.
Recorded because the failure mode — a name-shaped grep with a keyword filter — is the one this run
has a standing caution about.

`Kakeya.ML2Core.multiplicity_eq_of_shade_translate` below is the same fact phrased on **shade
equalities** rather than on a named translate operation, which is what the split needs:
`Tube.translate`
is a preimage by `-v`, `ShadedTube.translate` an image by `+v`, and the existing rows
(`Kakeya.ML2Core.CoarseStructRow`, `CoarseBallRow`) speak of `((T i).translate v).toTube`.  Phrasing
the bridge on shades avoids committing to either.

## 1. The translated split — and with it `hcoarse` / R2b

`Kakeya.ML2Core.exists_spineThreeScale_ofChain_translated` runs the four-way split on the
**translated** node families, so its shading identities are
`(Yτ' j).toTube = (𝒞.tube b j).translate v` and `(Yθ l).toTube = (𝒞.tube a l).translate v` —
exactly the form `Kakeya.ML2Core.CoarseStructRow` and `Kakeya.ML2Core.CoarseBallRow` state, and
exactly the form `Kakeya.ML2Core.exists_newParent_factor_at` consumes.  Its `hprod` is on the
**untranslated** leaf family, which is the form `Kakeya.ML2Core.HfacPostDropFour` reads, the two
being reconciled by §0's bridge.  So the shading-translate row and `hcoarse`/R2b close together, as
measured: they were one row.

## 2. `a = 0`: a case split in the producer, not a request on the window

The source *allows* `a = 0`; l.4447 gives the outer factor there as `n_a = 1`, the single ambient
cell.  So the faithful move is a branch, not a `1 ≤ a` field:
`Kakeya.ML2Core.outer_factor_at_zero_of_card_le_one` closes the outer factor at `a = 0` from
`ShadedBody.multiplicity_le_card` with **no defect estimate invoked** and no threshold — the
threshold `gridScale δ N a ≤ θ₀` is exactly what fails there
(`Kakeya.ML2Core.outer_threshold_fails_at_zero_newParent_lives`, `FCTLB` beside it), and this branch
never asks for it.

**What the `a = 0` branch needs and the `a ≥ 1` branch does not:** `tθ'.card ≤ 1`, i.e. the
source's `n_a = 1`.  It is a fact about the *cover* at level `0`, not about grid scales — `gridScale
δ N 0 = 1` bounds the thickness, not the index set — so it is named, not assumed silently.
`Kakeya.ML2Core.outer_factor_at_zero_of_card_le_δpow` is the unconditional alternative, at the price
of one scalar, `4 * (1 - β) ≤ εc`.

## 3. `hfullπ`: the share is the sites' `hfull`, and the bridge is a hand-back at level `p`

`Kakeya.VeryNotSticky.fullness_ge_of_centredHandBack`  delivers a fullness **lower bound** for
a hand-back's produced family, not a mass share; so `hfullπ` is supplied by it exactly when the
`(a, p)` fibre *is* such a family, at the grid scale `ρ_p`.
`Kakeya.ML2Core.newParent_fullness_of_centredHandBack` is that composition, and its hypotheses name
the bridge precisely: a `CentredHandBack` whose produced family and scale are the fibre's.

**Family / shading / level pair** for everything below: family `(s, V)` under the chain `𝒞`;
shadings as the split produces them, translated by the seam's `v`; level pairs leaf → `b`,
`(p, b)`, `(a, p)`, and level `a`.
-/

@[expose] public section

open MeasureTheory Metric ConvexSpaceBody ShadedBody Tube
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

universe u

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

section Translate

variable {ι : Type u}

omit [Nontrivial E] in
/-- **Multiplicity is blind to a common translation, phrased on shades.**

`ShadedBody.multiplicity_translate_const` is the existing statement at the named translate; this is
the same fact for any two families whose shades differ by `(v + ·)`, which is what a split run on
translated tubes hands back.  `volume` is translation invariant, and multiplicity is a ratio of
volumes of shades. -/
theorem multiplicity_eq_of_shade_translate (s : Finset ι) (V V' : ι → ShadedBody E) (v : E)
    (h : ∀ i, (V' i).shade = (v + ·) '' (V i).shade) :
    ShadedBody.multiplicity s V' = ShadedBody.multiplicity s V := by
  have hsum : ∑ i ∈ s, volume (V' i).shade = ∑ i ∈ s, volume (V i).shade :=
    Finset.sum_congr rfl fun i _ => by rw [h i]; exact measure_image_add volume v (V i).shade
  have huni : volume (⋃ i ∈ s, (V' i).shade) = volume (⋃ i ∈ s, (V i).shade) := by
    have : (⋃ i ∈ s, (V' i).shade) = (v + ·) '' (⋃ i ∈ s, (V i).shade) := by
      simp only [h, Set.image_iUnion₂]
    rw [this]
    exact measure_image_add volume v _
  rw [ShadedBody.multiplicity_eq_div, ShadedBody.multiplicity_eq_div, hsum, huni]

end Translate

section OuterAtZero

variable {δ : NNReal} {ι : Type u}

omit [Nontrivial E] in
/-- **The outer factor at `a = 0`, the source's `n_a = 1`** (l.4447).

No defect estimate, no threshold: the single ambient cell has multiplicity at most its
cardinality, which is `1`.  This is the branch that makes `1 ≤ a` a *case split in the producer*
rather than a request on the window — the window's order fields admit `a = 0` and are left alone.

**Family:** the retained level-`a` family `tθ'`; **shading:** `Yθ`.  **Level:** `a = 0`. -/
theorem outer_factor_at_zero_of_card_le_one {tθ' : Finset ι} {Yθ : ι → ShadedTube δ E}
    {β εc : ℝ} (hcard : tθ'.card ≤ 1) (hne : tθ'.Nonempty) (hεc : 0 ≤ εc)
    (hδ1 : (δ : ENNReal) ≤ 1) :
    ShadedBody.multiplicity tθ' (fun l => (Yθ l).toShadedBody)
      ≤ (δ : ENNReal) ^ (-εc) * ((tθ'.card : ℕ) : ENNReal) ^ β := by
  have hcard1 : tθ'.card = 1 := le_antisymm hcard (Finset.card_pos.mpr hne)
  have h1 : ShadedBody.multiplicity tθ' (fun l => (Yθ l).toShadedBody) ≤ 1 := by
    refine le_trans (ShadedBody.multiplicity_le_card tθ' _) ?_
    rw [hcard1]
    simp
  refine h1.trans ?_
  have hpow : (1 : ENNReal) ≤ (δ : ENNReal) ^ (-εc) := by
    simpa using ENNReal.rpow_le_rpow_of_exponent_ge hδ1 (by linarith : -εc ≤ 0)
  have hcardE : (((tθ'.card : ℕ) : ENNReal)) ^ β = 1 := by
    rw [hcard1]
    simp
  rw [hcardE, mul_one]
  exact hpow

omit [Nontrivial E] in
/-- **The `a = 0` branch's fallback, with its scalar named.**

`Tube.GridCoverSystem` has **no field constraining `indexSet 0`** — its fields are `assign_mem`,
`le_tube_assign`, `nested`, `tube_nested` — so the source's `n_a = 1` is a property of the
*canonical* cover, not of every hierarchy.  The tree has a existing witness that a canonical cover
has it (`Kakeya.ML2Reduction.wShaded`'s `((wShaded δ hδ).tubeUniform.cover.indexSet 0).card = 1`,
`MainLemma2/LooseUniform.lean:1174`), which is what
`Kakeya.ML2Core.outer_factor_at_zero_of_card_le_one` consumes.

For a hierarchy where it is not available, this is the fallback and it costs exactly one scalar:
`multiplicity ≤ card` (existing) and `card ^ (1 - β) ≤ δ ^ (-εc)`, whose content at the crude ceiling
`card ≤ δ ^ (-4)` is **`4 (1 - β) ≤ εc`**.

**Family:** `tθ'`; **shading:** `Yθ`.  **Level:** `a = 0`. -/
theorem outer_factor_at_zero_of_card_le_rpow {tθ' : Finset ι} {Yθ : ι → ShadedTube δ E}
    {β εc : ℝ} (_hβ0 : 0 ≤ β) (_hβ1 : β ≤ 1) (hne : tθ'.Nonempty)
    (hpow : (((tθ'.card : ℕ) : ENNReal)) ^ (1 - β) ≤ (δ : ENNReal) ^ (-εc)) :
    ShadedBody.multiplicity tθ' (fun l => (Yθ l).toShadedBody)
      ≤ (δ : ENNReal) ^ (-εc) * ((tθ'.card : ℕ) : ENNReal) ^ β := by
  have hc0 : (((tθ'.card : ℕ) : ENNReal)) ≠ 0 := by
    have : 0 < tθ'.card := Finset.card_pos.mpr hne
    simpa using this.ne'
  have hctop : (((tθ'.card : ℕ) : ENNReal)) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hsplit : (((tθ'.card : ℕ) : ENNReal))
      = (((tθ'.card : ℕ) : ENNReal)) ^ (1 - β) * (((tθ'.card : ℕ) : ENNReal)) ^ β := by
    rw [← ENNReal.rpow_add _ _ hc0 hctop]
    simp
  refine le_trans (ShadedBody.multiplicity_le_card tθ' _) ?_
  calc (((tθ'.card : ℕ) : ENNReal))
      = (((tθ'.card : ℕ) : ENNReal)) ^ (1 - β) * (((tθ'.card : ℕ) : ENNReal)) ^ β := hsplit
    _ ≤ (δ : ENNReal) ^ (-εc) * ((tθ'.card : ℕ) : ENNReal) ^ β := mul_le_mul' hpow le_rfl

end OuterAtZero

section TranslatedSplit

variable {δ : NNReal} {ι : Type u}

open Classical in
/-- **The four-way split on the translated family** — the shape the existing rows speak, and the
shape `Kakeya.ML2Core.HfacPostDropFour` needs.

The node families are translated by the seam's `v`, so the returned shadings satisfy
`(Yτ' j).toTube = (𝒞.tube b j).translate v` and `(Yθ l).toTube = (𝒞.tube a l).translate v` — the
identities `Kakeya.ML2Core.CoarseStructRow` and `Kakeya.ML2Core.CoarseBallRow` state, and the ones
`Kakeya.ML2Core.exists_newParent_factor_at` consumes.  The ball rows it asks are the translated
ones `hfac` supplies.  And its `hprod` is on the **untranslated** leaf family, by §0's bridge, which
is the form `hfac` reads.

So one theorem closes the shading-translate row and `hcoarse` / R2b at once.

**Family:** `(s, V)` under `𝒞`, read through the translated shading `V'`; **shadings:** the split's
four, all translated.  **Level pairs:** leaf → `b`, `(p, b)`, `(a, p)`, level `a`. -/
theorem exists_spineThreeScale_ofChain_translated {s : Finset ι} {V : ι → ShadedTube δ E} {N : ℕ}
    {σ : ℕ → ℝ≥0} (hδ : 0 < δ) (𝒞 : Tube.ChainCoverSystem s (fun i => (V i).toTube) N σ)
    {a p b : ℕ} (hap : a ≤ p) (hpb : p ≤ b) (haN : a ≤ N) (hpN : p ≤ N) (hbN : b ≤ N)
    (hδτ : δ ≤ σ b) (hτπ : σ b ≤ σ p) (hπθ : σ p ≤ σ a) (hθ1 : σ a ≤ 1) (v : E)
    (V' : ι → ShadedTube δ E)
    (hV'tube : ∀ i, (V' i).toTube = ((V i).toTube).translate v)
    (hV'shade : ∀ i, (V' i).shade = (v + ·) '' (V i).shade)
    (hball : ∀ i ∈ s, (V' i).carrier ⊆ Metric.closedBall (0 : E) 1)
    (hballτ : ∀ j ∈ ML2Reduction.activeNodes 𝒞 b,
      ((𝒞.tube b j).translate v).carrier ⊆ Metric.closedBall (0 : E) 1)
    (hballπ : ∀ k ∈ ML2Reduction.activeNodes 𝒞 p,
      ((𝒞.tube p k).translate v).carrier ⊆ Metric.closedBall (0 : E) 1) :
    ∃ tτ' ⊆ ML2Reduction.activeNodes 𝒞 b, ∃ tp' ⊆ ML2Reduction.activeNodes 𝒞 p,
      ∃ tθ' ⊆ 𝒞.indexSet a,
      ∃ (Yτ' : ι → ShadedTube (σ b) E) (Ypo Yp : ι → ShadedTube (σ p) E)
        (Yθ : ι → ShadedTube (σ a) E) (Y' : ι → ShadedTube δ E),
        (∀ j, (Yτ' j).toTube = (𝒞.tube b j).translate v) ∧
        (∀ k, (Ypo k).toTube = (𝒞.tube p k).translate v) ∧
        (∀ k, (Yp k).toTube = (𝒞.tube p k).translate v) ∧
        (∀ l, (Yθ l).toTube = (𝒞.tube a l).translate v) ∧
        (∀ i, (Y' i).toTube = (V' i).toTube) ∧
        (0 < ∑ i ∈ s, volume (V' i).shade →
          tτ'.Nonempty ∧ tp'.Nonempty ∧ tθ'.Nonempty) ∧
        (∀ jτ ∈ tτ', ∀ jp ∈ tp', ∀ jθ ∈ tθ',
          ShadedBody.multiplicity s (fun i => (V i).toShadedBody)
            ≤ ((ML2Reduction.spineScaleLoss (Module.finrank ℝ E) s.card δ *
                  ML2Reduction.spineScaleLoss (Module.finrank ℝ E) tτ'.card (σ b) *
                  ML2Reduction.spineScaleLoss (Module.finrank ℝ E) tp'.card (σ p) : ℝ≥0) : ENNReal)
              * ShadedBody.multiplicity {i ∈ s | 𝒞.assign b i = jτ}
                  (fun i => (Y' i).toShadedBody)
              * ShadedBody.multiplicity {j ∈ tτ' | ML2Reduction.coarseNode 𝒞 p b j = jp}
                  (fun j => (Yτ' j).toShadedBody)
              * ShadedBody.multiplicity {k ∈ tp' | ML2Reduction.coarseNode 𝒞 a p k = jθ}
                  (fun k => (Yp k).toShadedBody)
              * ShadedBody.multiplicity tθ' (fun l => (Yθ l).toShadedBody)) := by
  classical
  have hbody : ∀ i, (V' i).toConvexSpaceBody = (((V i).toTube).translate v).toConvexSpaceBody :=
    fun i => congrArg (fun T : Tube δ E => T.toConvexSpaceBody) (hV'tube i)
  obtain ⟨tτ', htτ', tp', htp', tθ', htθ', Yτ', Ypo, Yp, Yθ, Y', hYτ', hYpo, hYp, hYθ, hY'tube,
      _hY'shade, _hYpshade, hne, _hfull, hprod⟩ :=
    ML2Reduction.exists_spineThreeScale (E := E) hδ hδτ hτπ hπθ hθ1 V'
      (fun j => (𝒞.tube b j).translate v) (fun k => (𝒞.tube p k).translate v)
      (fun l => (𝒞.tube a l).translate v)
      (𝒞.assign b) (ML2Reduction.coarseNode 𝒞 p b) (ML2Reduction.coarseNode 𝒞 a p)
      hball hballτ hballπ
      (fun i hi => ML2Reduction.assign_mem_activeNodes 𝒞 hbN hi)
      (fun i hi => by
        rw [hbody i]
        exact tube_translate_le_translate _ _ v (𝒞.le_tube_assign b hbN i hi))
      (fun j hj => coarseNode_mem_activeNodes 𝒞 hpb hbN hj)
      (fun j hj => tube_translate_le_translate _ _ v
        (ML2Reduction.tube_le_coarseNode 𝒞 hpb hbN hj))
      (fun k hk => ML2Reduction.coarseNode_mem 𝒞 haN hk)
      (fun k hk => tube_translate_le_translate _ _ v
        (ML2Reduction.tube_le_coarseNode 𝒞 hap hpN hk))
  refine ⟨tτ', htτ', tp', htp', tθ', htθ', Yτ', Ypo, Yp, Yθ, Y', hYτ', hYpo, hYp, hYθ, hY'tube,
    hne, ?_⟩
  intro jτ hjτ jp hjp jθ hjθ
  have hbridge : ShadedBody.multiplicity s (fun i => (V' i).toShadedBody)
      = ShadedBody.multiplicity s (fun i => (V i).toShadedBody) :=
    multiplicity_eq_of_shade_translate s (fun i => (V i).toShadedBody)
      (fun i => (V' i).toShadedBody) v hV'shade
  rw [← hbridge]
  exact hprod jτ hjτ jp hjp jθ hjθ

end TranslatedSplit

section ParentFullness

open Classical in
/-- **`hfullπ`, consumed by name from the site seam.**

`Kakeya.VeryNotSticky.fullness_ge_of_centredHandBack`  is a fullness **lower bound** for a
hand-back's produced family, not a mass share; so it supplies the new-parent factor's fullness row
exactly when the `(a, p)` fibre *is* that family.  This is that composition, and its hypotheses name
the bridge with nothing hidden:

* `hcb` — a `Kakeya.VeryNotSticky.CentredHandBack` whose produced family `s'` **is** the fibre and
  whose produced shading `U'` **is** the split's level-`p` shading, at the hand-back's scale `δ'`;
* `hscale` — the one scalar comparison `δ ^ η ≤ δ' ^ ηd` between the ambient scale the defect
  estimate reads and the rescaled scale the hand-back delivers at.

**The share is therefore not a new object**: it is the sites' own `hfull`, moved to the
genuine-parent level.  What is *not* free is that the hand-back must be taken at that level; the
site wiring currently produces it at the sites' own scale, and `hcb` is where that shows.

**Family:** the `(a, p)` fibre; **shading:** `U' = Yp`.  **Level pair:** `(a, p)`. -/
theorem newParent_fullness_of_centredHandBack {δ δ' bq δt : NNReal} {R : ℝ}
    {hsit : Tube.IsRescalingSituation bq δt δ' R 3} {hR : 0 < R}
    {T₀ : Tube bq (EuclideanSpace ℝ (Fin 3))} {mc : EuclideanSpace ℝ (Fin 3)} {qc ηd η : ℝ}
    {A : Type u} {fib s' : Finset A}
    {Z' : A → ShadedTube δt (EuclideanSpace ℝ (Fin 3))}
    {U' : A → ShadedTube δ' (EuclideanSpace ℝ (Fin 3))}
    (hδ'0 : 0 < δ') (hδ'1 : δ' ≤ 1) (h3qc : 3 * qc ≤ ηd)
    (hcb : Kakeya.VeryNotSticky.CentredHandBack hsit hR T₀ mc qc fib s' Z' U')
    (hscale : (δ : NNReal) ^ η ≤ (δ' : NNReal) ^ ηd) :
    (δ : NNReal) ^ η ≤ ShadedBody.fullness s' (fun k => (U' k).toShadedBody) :=
  le_trans hscale
    (Kakeya.VeryNotSticky.fullness_ge_of_centredHandBack hδ'0 hδ'1 h3qc hcb)

end ParentFullness

section FibreIsFamily

variable {δ : NNReal} {ι : Type u}

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
open Classical in
/-- **Inside one coarse cell the `(a, p)` fibre *is* the retained level-`p` family.**

The hand-back producer `Kakeya.VeryNotSticky.exists_centredHandBack_uniform_and_countTransport`
is **scale-generic** — its `δ'` is a parameter of a `Tube.IsRescalingSituation`, not the sites'
own scale — but it *chooses* its retained family `s''`; it cannot be told to hand back a
prescribed set.  What removes the mismatch is that the producer works inside a **single** coarse
tube `T₀`, so every member of what it hands back has the same `(a, p)`-parent, and then the fibre
over that parent is the whole family.

So `hfullπ` needs no share and no prescribed-family variant of the producer: take `tp'` to be the
hand-back's retained family inside one coarse cell and the fibre is `tp'` itself.

**Family:** the retained level-`p` set `tp'`.  **Level pair:** `(a, p)`. -/
theorem newParentFibre_eq_self_of_common_parent {s : Finset ι} {T : ι → Tube δ E} {N : ℕ}
    {σ : ℕ → ℝ≥0} (𝒞 : Tube.ChainCoverSystem s T N σ) {a p : ℕ} {tp' : Finset ι} {jθ : ι}
    (hcommon : ∀ k ∈ tp', ML2Reduction.coarseNode 𝒞 a p k = jθ) :
    ({k ∈ tp' | ML2Reduction.coarseNode 𝒞 a p k = jθ} : Finset ι) = tp' :=
  Finset.filter_true_of_mem hcommon

omit [Nontrivial E] in
open Classical in
/-- **`hfullπ`, discharged inside one coarse cell.**

`Kakeya.VeryNotSticky.fullness_ge_of_centredHandBack` on the retained family, transported to the
fibre by `Kakeya.ML2Core.newParentFibre_eq_self_of_common_parent`.  The two named inputs are the
hand-back itself and the one scalar `δ ^ η ≤ δ' ^ ηd`; the *share* is gone. -/
theorem newParent_fullness_of_common_parent {s : Finset ι} {T : ι → Tube δ E} {N : ℕ}
    {σ : ℕ → ℝ≥0} (𝒞 : Tube.ChainCoverSystem s T N σ) {a p : ℕ} {tp' : Finset ι} {jθ : ι}
    {ρ : NNReal} {Yp : ι → ShadedTube ρ E} {c : NNReal} {η : ℝ}
    (hcommon : ∀ k ∈ tp', ML2Reduction.coarseNode 𝒞 a p k = jθ)
    (hfull : (c : NNReal) ^ η ≤ ShadedBody.fullness tp' (fun k => (Yp k).toShadedBody)) :
    (c : NNReal) ^ η ≤ ShadedBody.fullness
        ({k ∈ tp' | ML2Reduction.coarseNode 𝒞 a p k = jθ} : Finset ι)
        (fun k => (Yp k).toShadedBody) := by
  rw [newParentFibre_eq_self_of_common_parent 𝒞 hcommon]
  exact hfull

omit [Nontrivial E] in
open Classical in
/-- **`hfullπ` in one name: the hand-back at the genuine-parent level, applied.**

The combined construction is stated here.  `hcb` is the existing producer's output
(`Kakeya.VeryNotSticky.exists_centredHandBack_uniform_and_countTransport`, which is
**scale-generic**
— see the module docstring), taken at a rescaling situation whose rescaled scale is the
genuine-parent grid scale; `hcommon` is what a hand-back inside one coarse tube gives for free; and
`hscale` is the one scalar comparison.  Nothing else is needed, and in particular **no mass share**.

**Family:** the hand-back's retained family, which is the `(a, p)` fibre by `hcommon`;
**shading:** `U'`.  **Level pair:** `(a, p)`. -/
theorem hfullPi_of_handBack_at_parent {ι : Type u} {δ δ' bq δt : NNReal} {R : ℝ}
    {hsit : Tube.IsRescalingSituation bq δt δ' R 3} {hR : 0 < R}
    {T₀ : Tube bq (EuclideanSpace ℝ (Fin 3))} {mc : EuclideanSpace ℝ (Fin 3)} {qc ηd η : ℝ}
    {fib tp' : Finset ι}
    {Z' : ι → ShadedTube δt (EuclideanSpace ℝ (Fin 3))}
    {U' : ι → ShadedTube δ' (EuclideanSpace ℝ (Fin 3))}
    {s : Finset ι} {T : ι → Tube δ (EuclideanSpace ℝ (Fin 3))} {N : ℕ} {σ : ℕ → ℝ≥0}
    (𝒞 : Tube.ChainCoverSystem s T N σ) {a p : ℕ} {jθ : ι}
    (hδ'0 : 0 < δ') (hδ'1 : δ' ≤ 1) (h3qc : 3 * qc ≤ ηd)
    (hcb : Kakeya.VeryNotSticky.CentredHandBack hsit hR T₀ mc qc fib tp' Z' U')
    (hcommon : ∀ k ∈ tp', ML2Reduction.coarseNode 𝒞 a p k = jθ)
    (hscale : (δ : NNReal) ^ η ≤ (δ' : NNReal) ^ ηd) :
    (δ : NNReal) ^ η ≤ ShadedBody.fullness
        ({k ∈ tp' | ML2Reduction.coarseNode 𝒞 a p k = jθ} : Finset ι)
        (fun k => (U' k).toShadedBody) :=
  newParent_fullness_of_common_parent 𝒞 hcommon
    (newParent_fullness_of_centredHandBack hδ'0 hδ'1 h3qc hcb hscale)

end FibreIsFamily

end Kakeya.ML2Core

end
