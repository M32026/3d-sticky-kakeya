/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineThreeScale

/-!
# The producer of `Kakeya.ML2Core.HfacPostDropFour`, stated — and its split discharged

The four-way re-cut of `hfac`  turned the fourth conjunct into a
**named supplier row**.  This file states the producer of that row as the composition the source
prescribes, and discharges the half of it that is combinatorial.

## Which site produces which factor

The source's four families (l.4445-4452) and their estimators (l.4663-4666):

| factor | scale | level pair | estimated by |
|---|---|---|---|
| inner / fine | `δ/(2ρ_b)` | leaf → `b` | defect |
| **middle** | `ρ_b/(2ρ_p)` | **`(p, b)`** | **VNS** |
| **new parent** | `ρ_p/(2ρ_a)` | **`(a, p)`** | defect |
| outer | `ρ_a` | level `a` | defect |

Producers, by name:

* fine — `Kakeya.ML2Core.fine_factor_of_lemma91At_of_step8` **(site 1)** and
  `Kakeya.ML2Core.fine_factor_of_lemma91At_of_edCover` **(site 2)**,
  `Reduction/SpineMiddleFactor.lean`;
* middle — `Kakeya.ML2Core.middle_factor_of_edNodes_sharp'` **(site 3)** and
  `Kakeya.ML2Core.middle_factor_of_lineEDNodes_sharp` **(site 4)**,
  `Reduction/SpineLineEDMiddle.lean`; `Kakeya.ML2Core.middle_factor_of_edNodes` **(site 5)** and
  `Kakeya.ML2Core.middle_factor_of_edNodes_sharp` **(site 6)**,
  `Reduction/SpineMiddleProducer.lean`;
* new parent — `Kakeya.ML2Core.exists_coarse_factor_at_window` (`Reduction/SpineFactors.lean`)
  read at the pair `(a, p)` instead of at level `a`.  **The one factor with no site of its own.**
* outer — `Kakeya.ML2Core.exists_coarse_factor_at_window`, unchanged.

All six sites run at `Cu₀ = max C 4`, the constant the site hand's wiring
(`Reduction/SpineCentredHandBackWire.lean`, `Reduction/SpineSiteRowPack.lean`) fixes; the
`hcb`/`hct`/`huni`/`hfull` block comes from **one** `U''` and the elaborator enforces that
(`CTL_tie_two_families`), and `hL91` is reached for free from the closed Lemma 9.1 through
`Kakeya.ML2Core.lemma91At_of_closed`.

## What this file discharges

`Kakeya.ML2Core.exists_hfacFourConclusion_of_factors` builds the whole of the re-cut `hfac`'s
conclusion — the three retained sets, the four shadings, the three witnesses, the memberships, the
two nonemptiness rows and **`hprod` with its three `spineScaleLoss` factors** — from
`Kakeya.ML2Reduction.exists_spineThreeScale_ofChain` plus the four factor bounds.  Nothing about
the split is owed any more: the seam is at `(p, b)`, the new parent at `(a, p)`, the levels
telescope, and no `a ≠ 0` guard appears.

## What is still owed, and by whom

The producer's remaining hypotheses **are** the owed list, and each is named:

* `hfine` — sites 1-2.  Owed at the site: `hED`'s floor (the covering bridge, owner `w359h`).
* `hmid` — sites 3-6.  Owed at the site: `hnu` (specified a charging error, owner `w359h`, repair:
  move `3 q_c` to its own multiplicity-ledger factor).
* `hpar` — the new-parent factor at `(a, p)`.  **Nobody's yet**: it is the coarse/ambient block
  (`hcoarse`, `hCf1`, `hcard`, `hLoss`, `hκ`) re-stated at the pair `(a, p)`; the site hand stopped
  there because that block read the old `(a, b)` seam.  It is this hand's.
* `hcoarse` — the outer factor at level `a`, unchanged from the three-way split.
* `hballπ` — the level-`p` ball row.  New with the third level, and cheap: it is the level-`p`
  member of the seam's ball block.

`hsplit`'s degenerate instantiation is **not** among them: the split above supplies a genuine fine
factor, and `Kakeya.ML2Core.collapsed_four_split_of_one_le` with its firing control is the record
of what the collapsed form cost.

**Family / shading / level pair** for every declaration here: family `(s, V)` under the chain `𝒞`;
shadings `Y'`, `Yτ'`, `Yp`, `Yθ` as the split produces them; level pairs leaf → `b`, `(p, b)`,
`(a, p)`, and level `a`.
-/

@[expose] public section

open MeasureTheory Metric ConvexSpaceBody ShadedBody
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

universe u

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

open Classical in
/-- **The re-cut `hfac`'s conclusion, produced.**

Everything the four-way split owes is here except the four factor bounds, which are the sites'
and are named `hfine`, `hmid`, `hpar`, `hcoarse`.  The split itself —
`Kakeya.ML2Reduction.exists_spineThreeScale_ofChain` — supplies the three retained sets at the
right index sets, the four shadings, the two nonemptiness rows and `hprod` with **three**
`spineScaleLoss` factors, at the seam `(p, b)` and the new parent `(a, p)`.

**Level pairs:** leaf → `b`; `(p, b)`; `(a, p)`; level `a`.  **No `a ≠ 0` guard.** -/
theorem exists_hfacFourConclusion_of_factors
    {δ : ℝ≥0} {ι : Type u} {s : Finset ι} {V : ι → ShadedTube δ E} {N : ℕ} {σ : ℕ → ℝ≥0}
    (hδ : 0 < δ) (𝒞 : Tube.ChainCoverSystem s (fun i => (V i).toTube) N σ)
    {a p b : ℕ} (hap : a ≤ p) (hpb : p ≤ b) (haN : a ≤ N) (hpN : p ≤ N) (hbN : b ≤ N)
    (hδτ : δ ≤ σ b) (hτπ : σ b ≤ σ p) (hπθ : σ p ≤ σ a) (hθ1 : σ a ≤ 1)
    (hball : ∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall (0 : E) 1)
    (hballτ : ∀ j ∈ ML2Reduction.activeNodes 𝒞 b,
      (𝒞.tube b j).carrier ⊆ Metric.closedBall (0 : E) 1)
    (hballπ : ∀ k ∈ ML2Reduction.activeNodes 𝒞 p,
      (𝒞.tube p k).carrier ⊆ Metric.closedBall (0 : E) 1)
    (hmass : 0 < ∑ i ∈ s, volume (V i).shade)
    {β εf gmv εp εc : ℝ}
    -- sites 1-2: the fine factor, leaf inside a level-`b` node
    (hfine : ∀ (Y' : ι → ShadedTube δ E), (∀ i, (Y' i).toTube = (V i).toTube) →
      ∀ jτ : ι, ShadedBody.multiplicity {i ∈ s | 𝒞.assign b i = jτ}
          (fun i => (Y' i).toShadedBody)
        ≤ (δ : ENNReal) ^ (-εf)
          * ((({i ∈ s | 𝒞.assign b i = jτ} : Finset ι).card : ENNReal)) ^ β)
    -- sites 3-6: the middle (VNS) factor, at the pair `(p, b)`
    (hmid : ∀ (tτ' : Finset ι), tτ' ⊆ ML2Reduction.activeNodes 𝒞 b →
      ∀ (Yτ' : ι → ShadedTube (σ b) E), (∀ j, (Yτ' j).toTube = 𝒞.tube b j) →
      ∀ jp : ι, ShadedBody.multiplicity
          {j ∈ tτ' | ML2Reduction.coarseNode 𝒞 p b j = jp} (fun j => (Yτ' j).toShadedBody)
        ≤ (δ : ENNReal) ^ gmv
          * ((({j ∈ tτ' | ML2Reduction.coarseNode 𝒞 p b j = jp} : Finset ι).card : ENNReal)) ^ β)
    -- the new-parent factor, at the pair `(a, p)`, in defect shape
    (hpar : ∀ (tp' : Finset ι), tp' ⊆ ML2Reduction.activeNodes 𝒞 p →
      ∀ (Yp : ι → ShadedTube (σ p) E), (∀ k, (Yp k).toTube = 𝒞.tube p k) →
      ∀ jθ : ι, ShadedBody.multiplicity
          {k ∈ tp' | ML2Reduction.coarseNode 𝒞 a p k = jθ} (fun k => (Yp k).toShadedBody)
        ≤ (δ : ENNReal) ^ (-εp)
          * ((({k ∈ tp' | ML2Reduction.coarseNode 𝒞 a p k = jθ} : Finset ι).card : ENNReal)) ^ β)
    -- the outer factor at level `a`, unchanged from the three-way split
    (hcoarse : ∀ (tθ' : Finset ι), tθ' ⊆ 𝒞.indexSet a →
      ∀ (Yθ : ι → ShadedTube (σ a) E), (∀ l, (Yθ l).toTube = 𝒞.tube a l) →
      ShadedBody.multiplicity tθ' (fun l => (Yθ l).toShadedBody)
        ≤ (δ : ENNReal) ^ (-εc) * ((tθ'.card : ℕ) : ENNReal) ^ β) :
    ∃ (tτ' tp' tθ' : Finset ι)
      (Yτ' : ι → ShadedTube (σ b) E) (Yp : ι → ShadedTube (σ p) E)
      (Yθ : ι → ShadedTube (σ a) E) (Y' : ι → ShadedTube δ E) (jτ jp jθ : ι),
      tτ' ⊆ ML2Reduction.activeNodes 𝒞 b ∧
      tp' ⊆ ML2Reduction.activeNodes 𝒞 p ∧
      tθ' ⊆ 𝒞.indexSet a ∧ jθ ∈ tθ' ∧ tτ'.Nonempty ∧ tp'.Nonempty ∧
      (∀ i, (Y' i).toTube = (V i).toTube) ∧ (∀ i, (Y' i).shade ⊆ (V i).shade) ∧
      ShadedBody.multiplicity s (fun i => (V i).toShadedBody)
          ≤ ((ML2Reduction.spineScaleLoss (Module.finrank ℝ E) s.card δ *
                ML2Reduction.spineScaleLoss (Module.finrank ℝ E) tτ'.card (σ b) *
                ML2Reduction.spineScaleLoss (Module.finrank ℝ E) tp'.card (σ p) : ℝ≥0) : ENNReal)
            * ShadedBody.multiplicity {i ∈ s | 𝒞.assign b i = jτ} (fun i => (Y' i).toShadedBody)
            * ShadedBody.multiplicity {j ∈ tτ' | ML2Reduction.coarseNode 𝒞 p b j = jp}
                (fun j => (Yτ' j).toShadedBody)
            * ShadedBody.multiplicity {k ∈ tp' | ML2Reduction.coarseNode 𝒞 a p k = jθ}
                (fun k => (Yp k).toShadedBody)
            * ShadedBody.multiplicity tθ' (fun l => (Yθ l).toShadedBody) ∧
      ShadedBody.multiplicity {i ∈ s | 𝒞.assign b i = jτ} (fun i => (Y' i).toShadedBody)
          ≤ (δ : ENNReal) ^ (-εf)
            * ((({i ∈ s | 𝒞.assign b i = jτ} : Finset ι).card : ENNReal)) ^ β ∧
      ShadedBody.multiplicity {j ∈ tτ' | ML2Reduction.coarseNode 𝒞 p b j = jp}
            (fun j => (Yτ' j).toShadedBody)
          ≤ (δ : ENNReal) ^ gmv
            * ((({j ∈ tτ' | ML2Reduction.coarseNode 𝒞 p b j = jp} : Finset ι).card : ENNReal)) ^ β ∧
      ShadedBody.multiplicity {k ∈ tp' | ML2Reduction.coarseNode 𝒞 a p k = jθ}
            (fun k => (Yp k).toShadedBody)
          ≤ (δ : ENNReal) ^ (-εp)
            * ((({k ∈ tp' | ML2Reduction.coarseNode 𝒞 a p k = jθ} : Finset ι).card : ENNReal)) ^ β ∧
      ShadedBody.multiplicity tθ' (fun l => (Yθ l).toShadedBody)
          ≤ (δ : ENNReal) ^ (-εc) * ((tθ'.card : ℕ) : ENNReal) ^ β := by
  classical
  obtain ⟨tτ', htτ', tp', htp', tθ', htθ', Yτ', _Ypo, Yp, Yθ, Y', hYτ'tube, _hYpotube,
      hYptube, hYθtube, hY'tube, hY'shade, _hYpshade, hne, _hfullp, hprod⟩ :=
    ML2Reduction.exists_spineThreeScale_ofChain (E := E) hδ V 𝒞 hap hpb haN hpN hbN
      hδτ hτπ hπθ hθ1 hball hballτ hballπ
  obtain ⟨hτne, hpne, hθne⟩ := hne hmass
  obtain ⟨jτ, hjτ⟩ := hτne
  obtain ⟨jp, hjp⟩ := hpne
  obtain ⟨jθ, hjθ⟩ := hθne
  exact ⟨tτ', tp', tθ', Yτ', Yp, Yθ, Y', jτ, jp, jθ, htτ', htp', htθ', hjθ,
    ⟨jτ, hjτ⟩, ⟨jp, hjp⟩, hY'tube, hY'shade,
    hprod jτ hjτ jp hjp jθ hjθ,
    hfine Y' hY'tube jτ,
    hmid tτ' htτ' Yτ' hYτ'tube jp,
    hpar tp' htp' Yp hYptube jθ,
    hcoarse tθ' htθ' Yθ hYθtube⟩

end Kakeya.ML2Core

end
