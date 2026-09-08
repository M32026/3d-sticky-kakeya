/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.Geometry
public import Kakeya.DimensionThree.Plank.TypicalAngleIncidence
public import Kakeya.DimensionThree.Plank.PlankReduction

/-!
# Statement of GWZ Lemma 6.13

Only the theorem statement and the definitions it directly uses are included, so the imports are
deliberately minimal and nothing in the repository imports this file except the module index.

The proof route that discharges it is assembled elsewhere and is layered
`RepresentativeSelection` (witness) → `Refinement` (preassembly) → final reduction;
proving `reduction_to_slab` therefore means importing
`Kakeya.DimensionThree.Plank.RepresentativeShading`,
`Kakeya.DimensionThree.Plank.LocalDensity`
and `Kakeya.DimensionThree.Plank.Refinement` here.
-/

@[expose] public section

open MeasureTheory Metric
open scoped NNReal Real

noncomputable section

namespace ShadedPlank

variable {a b : NNReal} {hab : a ≤ b} {hb1 : b ≤ 1}

/-- The fixed ball-dilation factor in Item 1 of GWZ Lemma 6.13.

It is the literal `3` of the triangle inequality, and it is the only dilation of a *ball*
anywhere in the conclusion.  Item 1 is proved from a grid of `θb`-balls: the retained
shading is supported on a
union of balls `B̄(c, θb)` on each of which the density bound holds, so for an arbitrary centre `x`
with `U ∩ B̄(x, θb) ≠ ∅` one picks a dense grid ball `B̄(c, θb)` meeting it and uses
`B̄(c, θb) ⊆ B̄(x, 3 · θb)`.

**The paper's same-radius reading is false as literally quantified, so this is a correction
and not a weakening.**  Suppose `U` were a single ball `B̄(c, θb)`, the densest possible
configuration, and take `x` with `dist x c` close to `2 · θb`.  Then `U ∩ B̄(x, θb)` is a
nonempty lens whose volume tends to
`0` relative to `volume (B̄(x, θb))`, so no bound `κ · volume (B̄(x, θb)) ≤ volume (U ∩ B̄(x, θb))`
can hold uniformly in `x` for any positive `κ`.  A density statement at an arbitrary centre is only
available on a dilate, which is what the grid argument gives and what the downstream
covering/Vitali consumers need. -/
def redPlankTube.ballDilation : ℝ≥0 := 3

open Classical in
/-- **GWZ Lemma 6.13**, in the fixed-comparability condition used by the Section 6 API
(blueprint `lemmaredplanktube`).

## What the reduction produces

From a family `(𝒫, Y)` of pairwise essentially distinct `a × b × 1` planks in the unit ball with
`λ(𝒫, Y) ≥ a ^ η` and `μ(𝒫, Y) ≥ a ^ (-η)`, the lemma returns one shared tuple of data — *not*
four
independent sets of witnesses — and four conclusions about it:

* a refinement `(s', Y')` of `(s, Y)`, with the two retention bounds;
* the **typical plank angle** `θ ∈ [a/b, 1]`.  It is not an input: internally it is the
  stopping-time output of GWZ Lemma 6.11
  (`Kakeya.findingTypicalAngleOfIntersection_stable_reserve`), the angle at
  which the planks through a typical point of `U(s', Y')` meet;
* the **thickened representatives** `R`.  `R.repr` groups the refined planks into `θb × b × 1`
  representatives, `R.indexSet` (written `𝒯`) is the active representative family, and the
  fibre-cardinality clause is the paper's "each `P_θ` contains `∼ N` planks of `𝒫'_S`";
* the **slab assignment** `slabOf`, grouping representatives into controlled `θ × 1 × 1` slabs;
  `𝒮 = 𝒯.image slabOf`;
* the **thickened shading** `Yθ` on `𝒯`, the paper's `Y_{θ,S}`.

## Reading the four items

*Item 1* is a local density statement for `U(s', Y')` on `θb`-balls, at the fixed outer dilation
`redPlankTube.ballDilation = 3`; see that definition for why the same-radius reading of the paper's
prose is not a consequence of the hypotheses here but false as literally quantified.

*Item 2* is an **average** fullness statement: `ShadedBody.fullness` of the slab-local family is the
ratio `(∑ |Yθ t|) / (∑ |carrier t|)` over the whole fibre, not a termwise density bound at each
representative.  The termwise form is strictly stronger and is deliberately not asserted.  The
carrier clause immediately above Item 1 is what makes the ratio meaningful: without pinning
`(Yθ Q).carrier` to the `Cbox`-dilate of `Q`, a shading with a tiny carrier would satisfy any
fullness bound vacuously.

*Item 3* is the aggregate mass comparison, and it is proved from bounded overlap of the slab-local
unions: each point lies in at most an absolute number of them, so their volumes may be summed
against `volume (⋃ i ∈ s, (Y i).shade)`.

*Item 4* is the multiplicity reduction.  Its coefficient `a * N / (b * θ)` is the ratio between the
volume of a representative's carrier and that of a plank, and the fibre size `∼ N` is what converts
the multiplicity of the thickened family back into that of `(s, Y)`.  The `∃ S ∈ 𝒮` is the paper's
`max_{S ∈ 𝒮}`.

## Faithfulness to the paper

Writing `⪆` for the convention of blueprint `def:leApprox` at `ρ = a` (`X ⪆ Y` iff
`c · a ^ ε · Y ≤ X` for a constant depending only on `ε`), four of the five approximate clauses are
**exactly** paper-strength: the fullness retention `λ(s', Y') ⪆ λ(s, Y)`, Item 2's
`λ(𝒯_S, Yθ) ⪆ a ^ (4 * η)`, Item 3, and Item 4's `a ^ (-(4 * η))`.  Two clauses differ, both
deliberately and both documented:

* the **cardinality** retention is `|s'| ⪆ a ^ η * |s|`, one factor of `a ^ η` weaker than the
  paper's `|𝒫'| ⪆ |𝒫|`.  The factor is the input density: the retained family here is produced by
  *mass* pigeonholes, and converting a mass refinement to a count costs the fullness of the ambient
  family (`Kakeya.card_le_of_isCRefinement_of_fullness`), of which the hypotheses only guarantee
  `a ^ η`.  Recovering `⪆ |𝒫|` needs a count-based refinement route, i.e. genuinely new
  geometry, so
  the clause is left honest rather than asserted;
* **Item 1** carries the fixed dilation `3` discussed above.

The remaining differences from the paper's prose are the two *controlled* relaxations of
`𝒫_S = {P ∈ 𝒫 : P ⊆ S ∧ ∠(TP, TS) ≤ θ}` (blueprint `def:PS`), both of which enlarge the family and
so weaken the clauses that mention it.  `Plank.inSlabFamilyC Cset Cang` asks instead that the plank
lie in the `Cset`-dilate of the slab and make angle at most `Cang · θ` with it; `Cset = Cang = 1` is
the exact family.  Both constants are needed and neither implies the other: they relax the two
independent conjuncts of `def:PS`, and exact containment is unavailable in this construction because
a plank is only located inside a `cThk`-dilate of its thickened representative, which is itself only
inside a dilate of the slab.  The two clauses that mention `inSlabFamilyC` are the slab-membership
clause — the paper's `𝒫' = ⋃_{S ∈ 𝒮} 𝒫'_S`, the reverse inclusion being automatic — and Item 2's
`Yθ Q ⊆ U(𝒫'_S, Y')`.

The working window is recorded by the centre bound `dist (Y i).center 0 ≤ 1`.  It replaces the
paper's auxiliary parameters `C₀`, `N_exp` and the hypothesis `|𝒫| ≤ C₀ · a ^ (-N_exp)`: the
window bounds the number of pairwise essentially distinct planks outright
(`Plank.card_le_of_windowed_essentiallyDistinct_shaded`), which is what GWZ Lemma 6.11 needs, so
none of them and no smallness threshold on `a` occur here.  The paper's auxiliary scale `δ` is
`a` throughout — that was a typo in the source — so no separate parameter appears anywhere on the
Lemma 6.11/6.13 path.

Every constant is quantified before the data it must be uniform in: the geometric block
`cN, cThk, Cbox, Cset, Cang` before `η` and `ε`, and the analytic block `cP, cLam, c1, …, c4` before
the index type and the configuration.  The reserve-scale, box-grid, dense-ball and stopping-time
machinery that produces them stays internal to
`Kakeya.refinement_preassembly_uniform` and `Kakeya.plankReduction`. -/
theorem reduction_to_slab :
    ∃ cN cThk Cbox Cset Cang : ℝ≥0,
      1 ≤ cN ∧ 1 ≤ cThk ∧ cThk ≤ Cbox ∧ 1 ≤ Cset ∧ 1 ≤ Cang ∧
    ∀ {η ε : ℝ}, 0 < η → 0 < ε →
    ∃ cP cLam c1 c2 c3 c4 : ℝ≥0,
      0 < cP ∧ 0 < cLam ∧ 0 < c1 ∧ 0 < c2 ∧ 0 < c3 ∧ 1 ≤ c4 ∧
    ∀ {ι : Type*} (s : Finset ι)
      {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}
      (Y : ι → ShadedPlank a b hab hb1),
      0 < a → a < 1 →
      (∀ i ∈ s,
        dist (Y i).center (0 : EuclideanSpace ℝ (Fin 3)) ≤ 1) →
      (s : Set ι).Pairwise
        (fun i j => IsEssentiallyDistinct (Y i).carrier (Y j).carrier) →
      a ^ η ≤ ShadedBody.fullness s (ShadedPlank.bodies Y) →
      (a : ENNReal) ^ (-η) ≤ ShadedBody.multiplicity s (ShadedPlank.bodies Y) →
    ∃ (s' : Finset ι)
      (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
      (N : ℕ) (θ : ℝ≥0) (hθ1 : θ ≤ 1)
      (R : Plank.ThickenedRepr s' (ShadedPlank.planks Y) θ hθ1 cThk)
      (slabOf : Plank.ThickenedPlank θ b hθ1 hb1 → Slab θ hθ1)
      (Yθ : Plank.ThickenedPlank θ b hθ1 hb1 → ShadedBody (EuclideanSpace ℝ (Fin 3))),
      -- the active representative family and the slabs it occupies
      let 𝒯 := R.indexSet
      let 𝒮 := 𝒯.image slabOf
      -- the refinement and its two retention bounds
      ShadedBody.IsRefinement s' Y' s (ShadedPlank.bodies Y) ∧
      ((cP * a ^ η) * a ^ ε) * (s.card : ℝ≥0) ≤ (s'.card : ℝ≥0) ∧
      (cLam * a ^ ε) * ShadedBody.fullness s (ShadedPlank.bodies Y) ≤
        ShadedBody.fullness s' Y' ∧
      -- the common fibre size and the typical angle
      1 ≤ N ∧ a / b ≤ θ ∧
      -- every refined plank lies in the family of the slab of its representative
      (∀ i ∈ s', i ∈ Plank.inSlabFamilyC Cset Cang s'
          (ShadedPlank.planks Y) (slabOf (R.repr i))) ∧
      -- the carrier of the thickened shading is pinned to a dilate of the representative
      (∀ Q ∈ 𝒯,
        ((Yθ Q).carrier : Set (EuclideanSpace ℝ (Fin 3))) =
          ((Q.toPrismNDim.dilation Cbox).carrier : Set (EuclideanSpace ℝ (Fin 3)))) ∧
      -- every representative fibre has cardinality comparable to `N`
      (∀ Q ∈ 𝒯,
        (N : ℝ) / (cN : ℝ) ≤
          (((s'.filter fun i => R.repr i = Q).card : ℕ) : ℝ) ∧
        (((s'.filter fun i => R.repr i = Q).card : ℕ) : ℝ) ≤
          (cN : ℝ) * (N : ℝ)) ∧
      -- Item 1
      (∀ x,
        ((⋃ i ∈ s', (Y' i).shade) ∩ Metric.closedBall x ((θ * b) : ℝ)).Nonempty →
        (c1 : ENNReal) * a ^ (4 * η) * a ^ ε *
            volume (Metric.closedBall x (θ * b)) ≤
          volume ((⋃ i ∈ s', (Y' i).shade) ∩
            Metric.closedBall x
              (redPlankTube.ballDilation * θ * b))) ∧
      -- Item 2
      (∀ S ∈ 𝒮,
        c2 * a ^ (4 * η) * a ^ ε ≤
          ShadedBody.fullness (𝒯.filter (fun Q => slabOf Q = S)) Yθ ∧
        ∀ Q ∈ 𝒯.filter (fun Q => slabOf Q = S),
          (Yθ Q).shade ⊆
            ⋃ i ∈ Plank.inSlabFamilyC Cset Cang s' (ShadedPlank.planks Y) S,
              (Y' i).shade) ∧
      -- Item 3
      (((c3 * a ^ ε : ℝ≥0) : ENNReal) *
          ∑ S ∈ 𝒮,
            volume (⋃ Q ∈ 𝒯.filter (fun Q => slabOf Q = S), (Yθ Q).shade) ≤
        volume (⋃ i ∈ s, (Y i).shade)) ∧
      -- Item 4
      ∃ S ∈ 𝒮,
        ShadedBody.multiplicity s (ShadedPlank.bodies Y) ≤
          (c4 : ENNReal) * a ^ (-ε) * a ^ (-(4 * η)) *
            (((a * N) / (b * θ) : ℝ≥0) : ENNReal) *
            ShadedBody.multiplicity (𝒯.filter (fun Q => slabOf Q = S)) Yθ := by
  obtain ⟨cN, cThk, Cbox, Cset, Cang, h1cN, h1cThk, hcThkBox, h1Cset, h1Cang, hmain⟩ :=
    Kakeya.plankReduction_of_center_le_one
  refine ⟨cN, cThk, Cbox, Cset, Cang, h1cN, h1cThk, hcThkBox, h1Cset, h1Cang, ?_⟩
  intro η ε hη hε
  obtain ⟨cP, cLam, c1, c2, c3, c4, hcP, hcLam, hc1, hc2, hc3, hc4, hconfig⟩ := hmain hη hε
  refine ⟨cP, cLam, c1, c2, c3, c4, hcP, hcLam, hc1, hc2, hc3, hc4, ?_⟩
  intro ι s a b hab hb1 Y ha ha1 hcenter hED hfull hmult
  exact hconfig s Y ha ha1 hcenter hED hfull hmult

end ShadedPlank

end
