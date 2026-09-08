/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineRefinedFloor
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineMiddleProducer
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineEDExtraction
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineEDMultBound
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCountClause
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCanonicalCover

/-!
# GC-1 — the line-based ED twin of the GeometricCore middle factor, and the covering bridge

Source of record: the professor's refined proof
`260115_kakeyadetailedproofv3_revised_detailed.tex`; map
, §3, §4.1 row **GC-1**; condition   Stacked on  (`Reduction/SpineRefinedFloor.lean`, the `hfloor`/`hmid` split)
and on **E0** (`MainLemma2/LineEssDistinct.lean`, the line-ED notion, the non-ED degree and the
bridge), both of which this leaf **consumes**; nothing here restates them.

## What the refined text asks for, and what is done with it

The refined proof runs every level of its towers at **line-based `A`-essential distinctness**
(l.153–163): `#{T ∈ 𝕋 : T ⊂ N_{5δ}(L)} ≤ A` for every complete line `L`, with the absolute
constants `A₀ = 2·223⁶` (the canonical cover, l.4784) and `A₁ = 2·641⁶` (the centred canonical
cover, l.4900–4901).  The tree's Section-9 interfaces — above all the count clause of the
protected Lemma 9.1 — consume the *pairwise* volume notion `IsEssentiallyDistinct`.  The bridge
between them is E0's

`IsLineEssDistinctAt C_n A 𝕋  ⇒  edDegree ≤ A − 1  ⇒  a pairwise-ED subfamily of ≥ 1/A of the count`

(`Kakeya.VeryNotSticky.edDegree_le_of_isLineEssDistinctAt`,
`Kakeya.VeryNotSticky.exists_pairwise_of_isLineEssDistinctAt`), a **theorem**, never an axiom.
Its radius is the tree's two-tube overlap constant `C_n = Kakeya.Tube.tubeOverlapCoreClose.C 3`
(`≈ 101`), not the refined `5`: that is the one gap E0 measured and did not paper over, and every
statement below therefore reads `IsLineEssDistinctAt (Tube.tubeOverlapCoreClose.C 3)`, a
**stronger** hypothesis than the refined `IsLineEssDistinct` (`IsLineEssDistinctAt.mono_radius`
runs the other way).  `Kakeya.VeryNotSticky.LineEDLevelsAt` is
the level datum at that radius, with `Kakeya.VeryNotSticky.LineEDLevels` its refined `K = 5`
instance.

## What this buys: `SpineEDExtraction`'s `M` price becomes an absolute constant

`Kakeya.ML2Reduction.canonicalCoverAt_of_upstairs_edMult` prices the canonical cover by the
family's own ED-multiplicity `M`, and the only existing producer of `M`
(`Kakeya.ML2Reduction.edMultNat_le_of_upstairs_essDistinct`) needs the upstairs family to be
**pairwise** essentially distinct.  `canonicalCoverAt_of_upstairs_lineED` below replaces that
hypothesis by line-based `A`-ED and the price by the product of two absolutes,
`A · ⌈C₃(R)⌉` — so the budget clause is a *threshold on the scale*, not a competition between
`δ`-powers (`exists_threshold_lineED_budget`).  This is the refined covering bridge's charge
"line-based ED charges at most `A₁` surviving `m`-cells to one `W`" (l.5651–5656) in the tree's
vocabulary.

## Main declarations

* `Kakeya.ML2Core.lineEDLevelConstant` — `A₁ = 2·641⁶` (refined l.4900–4901), a named absolute.
* E0's `Kakeya.VeryNotSticky.LineEDLevelsAt`, `lineEDLevels_iff_at` (repointed here) — the level
  datum at a
  general neighbourhood radius, and the refined `K = 5` reading.
* `Kakeya.ML2Reduction.canonicalCoverAt_of_upstairs_lineED`,
  `Kakeya.ML2Reduction.canonicalCover_of_upstairs_lineED` — **the covering bridge**: the
  canonical-cover datum from line-ED upstairs, at the absolute price.
* `Kakeya.ML2Core.canonicalCover_of_lineEDNodes` — the additive twin of
  `Kakeya.ML2Core.canonicalCover_of_edNodes`.
* `Kakeya.ML2Core.middle_factor_of_canonicalCover_sharp` — the sharp middle factor with the
  canonical-cover datum factored out of `Kakeya.ML2Core.middle_factor_of_edNodes_sharp` (which is
  **not** re-cut;  forbids that, and it is re-derived below as
  `middle_factor_of_edNodes_sharp'` as a control that the factorisation is faithful).
* `Kakeya.ML2Core.middle_factor_of_lineEDNodes_sharp` — **the additive twin**: the same
  conclusion, the same exponent `47 η_k/5`, with the line-based ED clause and the `A₁`-loaded
  budget.
* `Kakeya.ML2Core.geometricCoreAt_of_lineEDLevels` — the wiring: `GeometricCoreAt` from the
  refined count floor, a middle factor that may read the line-ED levels, and a producer of those
  levels (U1's output at the wiring level).
-/

@[expose] public section

open MeasureTheory Metric Set Topology Filter ConvexSpaceBody ShadedBody
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

universe u

/-! ## The refined absolute constant `A₁`, and the level datum at a general radius -/

section Constants

/-- **`A₁ = 2·641⁶`** — the line-ED constant of the refined text's *centred* canonical cover
(l.4900–4901, l.4852–4855); the plain canonical cover's constant is `A₀ = 2·223⁶`, carried by E0
as `Kakeya.VeryNotSticky.edMultiplicityConstant`.  Both are `δ`-free absolutes: they enter the
count budget as constants, not as exponents (`exists_threshold_lineED_budget`). -/
def lineEDLevelConstant : ℕ := 2 * 641 ^ 6

theorem one_le_lineEDLevelConstant : 1 ≤ lineEDLevelConstant := by
  unfold lineEDLevelConstant; norm_num

theorem lineEDLevelConstant_pos : 0 < lineEDLevelConstant := one_le_lineEDLevelConstant

end Constants

section LevelsAt

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*}

/-- The levels of a hierarchy that is line-ED at the tree's two-tube radius have non-ED degree
`≤ A − 1` at every level — E0's bridge, read on the hierarchy. -/
theorem edDegree_le_of_lineEDLevelsAt {δ : NNReal}
    {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {C : NNReal}
    [MeasurableSpace E] [BorelSpace E] [Nontrivial E]
    {𝒰 : Tube.UniformTubeSet s T N C} {A : ℕ}
    (h : Kakeya.VeryNotSticky.LineEDLevelsAt
      (Kakeya.Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E)) A 𝒰)
    {k : ℕ} (hk : k < N)
    (hk0 : 0 < Tube.gridScale δ N k) (hk1 : Tube.gridScale δ N k ≤ 1)
    {i : ι} (hi : i ∈ 𝒰.cover.indexSet k) :
    Kakeya.VeryNotSticky.edDegree (𝒰.cover.indexSet k)
        (fun j ↦ (𝒰.cover.tube k j).carrier) i ≤ A - 1 :=
  Kakeya.VeryNotSticky.edDegree_le_of_isLineEssDistinctAt hk0 hk1 (h k hk) hi

/-! ### Spelling bridge for the line's neighbourhood

E0's existing `Kakeya.VeryNotSticky.IsLineEssDistinctAt` reads the line's neighbourhood as
`lineNbhd p d r = Metric.cthickening r (lineSet p d)` with `lineSet p d = {y | ∃ t : ℝ,
y = p + t • d}` (the C6-a spelling).  The other rendering in circulation is the inline
`Metric.cthickening r (Set.range fun t ↦ p + t • d)`.  The two sets are equal but **not**
definitionally so — `Set.range f = {y | ∃ t, f t = y}` and `lineSet` is `{y | ∃ t, y = f t}`, the
defining equation the other way round — so a `rfl` between the two readings of the predicate does
not typecheck.  `range_line_eq_setOf` is the rewrite, E0's own form of it is
`Kakeya.VeryNotSticky.lineNbhd_eq_cthickening_range`, and `isLineEssDistinctAt_iff_range` states
the predicate in the inline spelling so that either reading can be consumed here.

Nothing else in this file touches either spelling: every declaration below consumes
`IsLineEssDistinct` / `IsLineEssDistinctAt` abstractly (measured: no `cthickening`, no
`Set.range`, no `lineNbhd` outside this block), so the choice costs this leaf nothing. -/

omit [FiniteDimensional ℝ E] in
theorem range_line_eq_setOf (p d : E) :
    (Set.range fun t : ℝ ↦ p + t • d) = {y | ∃ t : ℝ, y = p + t • d} := by
  ext y
  exact ⟨fun h ↦ h.imp fun _ ht ↦ ht.symm, fun h ↦ h.imp fun _ ht ↦ ht.symm⟩

omit [FiniteDimensional ℝ E] in
theorem cthickening_line_eq (p d : E) (r : ℝ) :
    Metric.cthickening r (Set.range fun t : ℝ ↦ p + t • d)
      = Metric.cthickening r {y | ∃ t : ℝ, y = p + t • d} := by
  rw [range_line_eq_setOf]

open scoped Classical in
/-- **The spelling bridge**: E0's `IsLineEssDistinctAt`, whose neighbourhood is
`Kakeya.VeryNotSticky.lineNbhd`, read in the inline `Set.range` spelling.  This is the rewrite that
makes the two renderings of the predicate interchangeable at a call site. -/
theorem isLineEssDistinctAt_iff_range {K : ℝ} {A : ℕ} {δ : NNReal} {s : Finset ι}
    {T : ι → Tube δ E} :
    Kakeya.VeryNotSticky.IsLineEssDistinctAt K A s T ↔
      ∀ p d : E, ‖d‖ = 1 →
        (s.filter fun i ↦ (T i).carrier
          ⊆ Metric.cthickening (K * (δ : ℝ)) (Set.range fun t : ℝ ↦ p + t • d)).card ≤ A := by
  simp only [Kakeya.VeryNotSticky.IsLineEssDistinctAt,
    Kakeya.VeryNotSticky.lineNbhd_eq_cthickening_range]

end LevelsAt

end Kakeya.ML2Core

namespace Kakeya.ML2Reduction

universe u

variable {θ τ : NNReal}

/-! ## The covering bridge: the canonical-cover datum from line-ED upstairs -/

section CoveringBridge

/-- **The push-up price** `⌈C₃(R)⌉` of
`Kakeya.ML2Reduction.edMultNat_le_of_upstairs_essDistinct`, named once so the budget clauses
below read as a product of two absolutes. -/
noncomputable def lineEDPushConstant (R : ℝ) : ℕ :=
  ⌈((_root_.Tube.essDistinctTubesInSelfDilate.C 3
      (4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C 3) : NNReal) : ℝ)⌉₊

/-- **The covering bridge at one scale.**

`Kakeya.ML2Reduction.canonicalCoverAt_of_upstairs_edMult` needs the ED-multiplicity `M` of the
*pushed-up* family, and its only existing producer needs the upstairs family to be **pairwise**
essentially distinct.  Here the upstairs hypothesis is the refined line-based one and the price
is the product of two absolutes, `A · ⌈C₃(R)⌉`:

* E0's `Kakeya.VeryNotSticky.exists_pairwise_of_isLineEssDistinctAt` extracts a pairwise-ED
  subfamily `t' ⊆ t` with `#t ≤ A · #t'` (the refined charge "at most `A₁` surviving cells to one
  `W`", l.5651–5656);
* `Kakeya.ML2Reduction.edMultNat_le_of_upstairs_essDistinct` then prices `t'`'s push-up by
  `⌈C₃(R)⌉`;
* the two losses multiply into the single budget clause `hslack`, and the count survives at the
  reading exponent `ζ` — **no `ρ`-power is spent** (contrast
  `Kakeya.ML2Reduction.hup_of_step8`, whose `M ≤ ρ^{-m}` spends `m` of the reading gap). -/
theorem canonicalCoverAt_of_upstairs_lineED {σ : NNReal} {R ζ ζ' : ℝ}
    (hsit : Tube.IsRescalingSituation θ τ σ R 3) (hR : 0 < R)
    (T₀ : Tube θ (EuclideanSpace ℝ (Fin 3)))
    {α : Type u} {s : Finset α} (𝕋 : α → ShadedTube τ (EuclideanSpace ℝ (Fin 3)))
    {ρ : NNReal} (hρ0 : 0 < ρ) (hρ4 : (ρ : ℝ) ≤ 1 / 4)
    {κ₀ : Type u} (t : Finset κ₀) (W : κ₀ → Tube (ρ * θ) (EuclideanSpace ℝ (Fin 3)))
    (hsubW : ∀ k ∈ t, (W k).carrier ⊆ T₀.carrier)
    (hused : ∀ k ∈ t, ∃ i ∈ s, (𝕋 i).carrier ⊆ (W k).carrier)
    {A : ℕ} (hA0 : 0 < A)
    (hline : Kakeya.VeryNotSticky.IsLineEssDistinctAt (Tube.tubeOverlapCoreClose.C 3) A t W)
    (hslack : (A : ℝ) * (lineEDPushConstant R : ℝ) * (spineOuterCountLoss R : ℝ)
      ≤ (ρ : ℝ) ^ (-(ζ' - ζ)))
    (hcard : (ρ : ℝ) ^ (-2 - ζ') ≤ (t.card : ℝ)) :
    ∃ (κ₁ : Type u) (u : Finset κ₁) (V : κ₁ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
      ((u : Set κ₁).Pairwise
        fun j k ↦ _root_.IsEssentiallyDistinct (V j).carrier (V k).carrier) ∧
      (∀ j ∈ u, ∃ i ∈ s,
        (spineFamily (spineRescaleUnit hsit.pos_ambient T₀ hR) 𝕋 i).toConvexSpaceBody
          ≤ (V j).toConvexSpaceBody) ∧
      (spineOuterCountLoss R : ℝ) * (ρ : ℝ) ^ (-2 - ζ) ≤ (u.card : ℝ) := by
  classical
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have hρθ0 : 0 < ρ * θ := mul_pos hρ0 hsit.pos_ambient
  have hρ1 : ρ ≤ 1 := by
    have : (ρ : ℝ) ≤ 1 := by linarith
    exact_mod_cast this
  have hρθ1 : ρ * θ ≤ 1 := by
    calc ρ * θ ≤ 1 * 1 := by gcongr; exact hsit.ambient_le_one
      _ = 1 := one_mul 1
  have hline' : Kakeya.VeryNotSticky.IsLineEssDistinctAt
      (Tube.tubeOverlapCoreClose.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))) A t W := by
    rwa [hfr]
  obtain ⟨t', ht's, hpair, -, hret⟩ :=
    Kakeya.VeryNotSticky.exists_pairwise_of_isLineEssDistinctAt hρθ0 hρθ1 hline' (fun _ ↦ 0)
  have hAeq : A - 1 + 1 = A := Nat.succ_pred_eq_of_pos hA0
  rw [hAeq] at hret
  have hsubW' : ∀ k ∈ t', (W k).carrier ⊆ T₀.carrier := fun k hk ↦ hsubW k (ht's hk)
  have hused'0 : ∀ k ∈ t', ∃ i ∈ s, (𝕋 i).carrier ⊆ (W k).carrier := fun k hk ↦ hused k (ht's hk)
  have hM : ∀ i ∈ t', (t'.filter (fun j ↦
      ¬ _root_.IsEssentiallyDistinct
          (outerTube hsit.pos_ambient T₀ hR ρ (W j)).carrier
          (outerTube hsit.pos_ambient T₀ hR ρ (W i)).carrier)).card
      ≤ lineEDPushConstant R :=
    fun i hi ↦ edMultNat_le_of_upstairs_essDistinct hsit hR hfr T₀ hρ0 hρ4 W hsubW' hpair hi
  have hsit2 := isRescalingSituation_scaledUp hsit hρ0 hρ4
  have hused' := outerTube_used_of_used hfr hsit2 hR (ratio_scaledUp hsit.pos_ambient ρ)
    T₀ 𝕋 (t := t') W hsubW' hused'0
  have hρR : (0 : ℝ) < (ρ : ℝ) := by exact_mod_cast hρ0
  have hAR : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA0
  have hne' : t'.Nonempty := by
    rw [← Finset.card_pos]
    have hpos : (0 : ℝ) < (ρ : ℝ) ^ (-2 - ζ') := Real.rpow_pos_of_pos hρR _
    have h1 : (0 : ℝ) < (t.card : ℝ) := lt_of_lt_of_le hpos hcard
    have h2 : 0 < t.card := by exact_mod_cast h1
    have h3 : t.card ≤ A * t'.card := hret
    rcases Nat.eq_zero_or_pos t'.card with hz | hp
    · rw [hz, Nat.mul_zero] at h3; omega
    · exact hp
  have hM0 : 0 < lineEDPushConstant R :=
    lt_of_lt_of_le zero_lt_one
      (one_le_edMult hρ0 (fun k ↦ outerTube hsit.pos_ambient T₀ hR ρ (W k)) hne' hM)
  refine canonicalCoverAt_of_used_of_edMult hsit.pos_ambient T₀ (hR := hR) 𝕋 hρ0 t'
    (fun k ↦ outerTube hsit.pos_ambient T₀ hR ρ (W k)) hM0 hM hused' ?_
  have hLam : (0 : ℝ) ≤ (spineOuterCountLoss R : ℝ) := (spineOuterCountLoss R).coe_nonneg
  have hsplit : (ρ : ℝ) ^ (-(ζ' - ζ)) * (ρ : ℝ) ^ (-2 - ζ) = (ρ : ℝ) ^ (-2 - ζ') := by
    rw [← Real.rpow_add hρR]; ring_nf
  have hstep : (A : ℝ) * ((lineEDPushConstant R : ℝ)
      * ((spineOuterCountLoss R : ℝ) * (ρ : ℝ) ^ (-2 - ζ))) ≤ (A : ℝ) * (t'.card : ℝ) := by
    calc (A : ℝ) * ((lineEDPushConstant R : ℝ)
            * ((spineOuterCountLoss R : ℝ) * (ρ : ℝ) ^ (-2 - ζ)))
        = ((A : ℝ) * (lineEDPushConstant R : ℝ) * (spineOuterCountLoss R : ℝ))
            * (ρ : ℝ) ^ (-2 - ζ) := by ring
      _ ≤ (ρ : ℝ) ^ (-(ζ' - ζ)) * (ρ : ℝ) ^ (-2 - ζ) :=
          mul_le_mul_of_nonneg_right hslack (Real.rpow_nonneg hρR.le _)
      _ = (ρ : ℝ) ^ (-2 - ζ') := hsplit
      _ ≤ (t.card : ℝ) := hcard
      _ ≤ (A : ℝ) * (t'.card : ℝ) := by exact_mod_cast hret
  exact le_of_mul_le_mul_left hstep hAR

/-- **`canonicalCoverAt_of_upstairs_lineED` at a named count constant**
Identical to its sibling above except that the count is read
at `Kc` rather than at `Kakeya.ML2Reduction.spineOuterCountLoss R`; the count is a free parameter
of `Kakeya.ML2Reduction.canonicalCoverAt_of_used_of_edMult`, so nothing about the extraction
changes.  The centring transport needs the `Kakeya.VeryNotSticky.centringCountLossConstant R` form. -/
theorem canonicalCoverAt_of_upstairs_lineED_const {σ : NNReal} {R ζ ζ' Kc : ℝ}
    (hKc0 : 0 ≤ Kc)
    (hsit : Tube.IsRescalingSituation θ τ σ R 3) (hR : 0 < R)
    (T₀ : Tube θ (EuclideanSpace ℝ (Fin 3)))
    {α : Type u} {s : Finset α} (𝕋 : α → ShadedTube τ (EuclideanSpace ℝ (Fin 3)))
    {ρ : NNReal} (hρ0 : 0 < ρ) (hρ4 : (ρ : ℝ) ≤ 1 / 4)
    {κ₀ : Type u} (t : Finset κ₀) (W : κ₀ → Tube (ρ * θ) (EuclideanSpace ℝ (Fin 3)))
    (hsubW : ∀ k ∈ t, (W k).carrier ⊆ T₀.carrier)
    (hused : ∀ k ∈ t, ∃ i ∈ s, (𝕋 i).carrier ⊆ (W k).carrier)
    {A : ℕ} (hA0 : 0 < A)
    (hline : Kakeya.VeryNotSticky.IsLineEssDistinctAt (Tube.tubeOverlapCoreClose.C 3) A t W)
    (hslack : (A : ℝ) * (lineEDPushConstant R : ℝ) * Kc
      ≤ (ρ : ℝ) ^ (-(ζ' - ζ)))
    (hcard : (ρ : ℝ) ^ (-2 - ζ') ≤ (t.card : ℝ)) :
    ∃ (κ₁ : Type u) (u : Finset κ₁) (V : κ₁ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
      ((u : Set κ₁).Pairwise
        fun j k ↦ _root_.IsEssentiallyDistinct (V j).carrier (V k).carrier) ∧
      (∀ j ∈ u, ∃ i ∈ s,
        (spineFamily (spineRescaleUnit hsit.pos_ambient T₀ hR) 𝕋 i).toConvexSpaceBody
          ≤ (V j).toConvexSpaceBody) ∧
      Kc * (ρ : ℝ) ^ (-2 - ζ) ≤ (u.card : ℝ) := by
  classical
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have hρθ0 : 0 < ρ * θ := mul_pos hρ0 hsit.pos_ambient
  have hρ1 : ρ ≤ 1 := by
    have : (ρ : ℝ) ≤ 1 := by linarith
    exact_mod_cast this
  have hρθ1 : ρ * θ ≤ 1 := by
    calc ρ * θ ≤ 1 * 1 := by gcongr; exact hsit.ambient_le_one
      _ = 1 := one_mul 1
  have hline' : Kakeya.VeryNotSticky.IsLineEssDistinctAt
      (Tube.tubeOverlapCoreClose.C (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))) A t W := by
    rwa [hfr]
  obtain ⟨t', ht's, hpair, -, hret⟩ :=
    Kakeya.VeryNotSticky.exists_pairwise_of_isLineEssDistinctAt hρθ0 hρθ1 hline' (fun _ ↦ 0)
  have hAeq : A - 1 + 1 = A := Nat.succ_pred_eq_of_pos hA0
  rw [hAeq] at hret
  have hsubW' : ∀ k ∈ t', (W k).carrier ⊆ T₀.carrier := fun k hk ↦ hsubW k (ht's hk)
  have hused'0 : ∀ k ∈ t', ∃ i ∈ s, (𝕋 i).carrier ⊆ (W k).carrier := fun k hk ↦ hused k (ht's hk)
  have hM : ∀ i ∈ t', (t'.filter (fun j ↦
      ¬ _root_.IsEssentiallyDistinct
          (outerTube hsit.pos_ambient T₀ hR ρ (W j)).carrier
          (outerTube hsit.pos_ambient T₀ hR ρ (W i)).carrier)).card
      ≤ lineEDPushConstant R :=
    fun i hi ↦ edMultNat_le_of_upstairs_essDistinct hsit hR hfr T₀ hρ0 hρ4 W hsubW' hpair hi
  have hsit2 := isRescalingSituation_scaledUp hsit hρ0 hρ4
  have hused' := outerTube_used_of_used hfr hsit2 hR (ratio_scaledUp hsit.pos_ambient ρ)
    T₀ 𝕋 (t := t') W hsubW' hused'0
  have hρR : (0 : ℝ) < (ρ : ℝ) := by exact_mod_cast hρ0
  have hAR : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA0
  have hne' : t'.Nonempty := by
    rw [← Finset.card_pos]
    have hpos : (0 : ℝ) < (ρ : ℝ) ^ (-2 - ζ') := Real.rpow_pos_of_pos hρR _
    have h1 : (0 : ℝ) < (t.card : ℝ) := lt_of_lt_of_le hpos hcard
    have h2 : 0 < t.card := by exact_mod_cast h1
    have h3 : t.card ≤ A * t'.card := hret
    rcases Nat.eq_zero_or_pos t'.card with hz | hp
    · rw [hz, Nat.mul_zero] at h3; omega
    · exact hp
  have hM0 : 0 < lineEDPushConstant R :=
    lt_of_lt_of_le zero_lt_one
      (one_le_edMult hρ0 (fun k ↦ outerTube hsit.pos_ambient T₀ hR ρ (W k)) hne' hM)
  refine canonicalCoverAt_of_used_of_edMult hsit.pos_ambient T₀ (hR := hR) 𝕋 hρ0 t'
    (fun k ↦ outerTube hsit.pos_ambient T₀ hR ρ (W k)) hM0 hM hused' ?_
  have hLam : (0 : ℝ) ≤ Kc := hKc0
  have hsplit : (ρ : ℝ) ^ (-(ζ' - ζ)) * (ρ : ℝ) ^ (-2 - ζ) = (ρ : ℝ) ^ (-2 - ζ') := by
    rw [← Real.rpow_add hρR]; ring_nf
  have hstep : (A : ℝ) * ((lineEDPushConstant R : ℝ)
      * (Kc * (ρ : ℝ) ^ (-2 - ζ))) ≤ (A : ℝ) * (t'.card : ℝ) := by
    calc (A : ℝ) * ((lineEDPushConstant R : ℝ)
            * (Kc * (ρ : ℝ) ^ (-2 - ζ)))
        = ((A : ℝ) * (lineEDPushConstant R : ℝ) * Kc)
            * (ρ : ℝ) ^ (-2 - ζ) := by ring
      _ ≤ (ρ : ℝ) ^ (-(ζ' - ζ)) * (ρ : ℝ) ^ (-2 - ζ) :=
          mul_le_mul_of_nonneg_right hslack (Real.rpow_nonneg hρR.le _)
      _ = (ρ : ℝ) ^ (-2 - ζ') := hsplit
      _ ≤ (t.card : ℝ) := hcard
      _ ≤ (A : ℝ) * (t'.card : ℝ) := by exact_mod_cast hret
  exact le_of_mul_le_mul_left hstep hAR

/-- **the `Kc`-form IS the `Λ`-form.**  Upgraded from the one-way derivation this replaced:
an implication does not rule out the two spellings drifting, an equation at the same stated type
does.  Both sides must elaborate at that type, so if either statement moves, this stops
compiling. -/
theorem canonicalCoverAt_of_upstairs_lineED_of_const {σ : NNReal} {R ζ ζ' : ℝ}
    (hsit : Tube.IsRescalingSituation θ τ σ R 3) (hR : 0 < R)
    (T₀ : Tube θ (EuclideanSpace ℝ (Fin 3)))
    {α : Type u} {s : Finset α} (𝕋 : α → ShadedTube τ (EuclideanSpace ℝ (Fin 3)))
    {ρ : NNReal} (hρ0 : 0 < ρ) (hρ4 : (ρ : ℝ) ≤ 1 / 4)
    {κ₀ : Type u} (t : Finset κ₀) (W : κ₀ → Tube (ρ * θ) (EuclideanSpace ℝ (Fin 3)))
    (hsubW : ∀ k ∈ t, (W k).carrier ⊆ T₀.carrier)
    (hused : ∀ k ∈ t, ∃ i ∈ s, (𝕋 i).carrier ⊆ (W k).carrier)
    {A : ℕ} (hA0 : 0 < A)
    (hline : Kakeya.VeryNotSticky.IsLineEssDistinctAt (Tube.tubeOverlapCoreClose.C 3) A t W)
    (hslack : (A : ℝ) * (lineEDPushConstant R : ℝ) * (spineOuterCountLoss R : ℝ)
      ≤ (ρ : ℝ) ^ (-(ζ' - ζ)))
    (hcard : (ρ : ℝ) ^ (-2 - ζ') ≤ (t.card : ℝ)) :
    canonicalCoverAt_of_upstairs_lineED_const (Kc := (spineOuterCountLoss R : ℝ))
        (spineOuterCountLoss R).coe_nonneg hsit hR T₀ 𝕋 hρ0 hρ4 t W hsubW hused hA0 hline
        hslack hcard
      = canonicalCoverAt_of_upstairs_lineED hsit hR T₀ 𝕋 hρ0 hρ4 t W hsubW hused hA0 hline
          hslack hcard := rfl

/-- **The covering bridge over Lemma 9.1's window.**  The conclusion is the `hcanon` binder of
`Kakeya.ML2Reduction.fine_factor_of_lemma91At_of_canonicalCover` character for character; the
hypothesis is `Kakeya.ML2Reduction.canonicalCover_of_upstairs_essDistinct`'s with **pairwise**
essential distinctness replaced by line-based `A`-ED and the price loaded with `A`. -/
theorem canonicalCover_of_upstairs_lineED {σ : NNReal} {R ϖ ζ ζ' : ℝ}
    (hsit : Tube.IsRescalingSituation θ τ σ R 3) (hR : 0 < R)
    (T₀ : Tube θ (EuclideanSpace ℝ (Fin 3)))
    {α : Type u} {s : Finset α} (𝕋 : α → ShadedTube τ (EuclideanSpace ℝ (Fin 3)))
    (hσ0 : 0 < σ) (hwin4 : ((σ ^ ϖ : NNReal) : ℝ) ≤ 1 / 4)
    {A : ℕ} (hA0 : 0 < A)
    (hup : ∀ ρ : NNReal, ρ ∈ Set.Icc (σ ^ (1 - ϖ)) (σ ^ ϖ) →
      ∃ (κ₀ : Type u) (t : Finset κ₀) (W : κ₀ → Tube (ρ * θ) (EuclideanSpace ℝ (Fin 3))),
        (∀ k ∈ t, (W k).carrier ⊆ T₀.carrier) ∧
        (∀ k ∈ t, ∃ i ∈ s, (𝕋 i).carrier ⊆ (W k).carrier) ∧
        Kakeya.VeryNotSticky.IsLineEssDistinctAt (Tube.tubeOverlapCoreClose.C 3) A t W ∧
        (A : ℝ) * (lineEDPushConstant R : ℝ) * (spineOuterCountLoss R : ℝ)
            ≤ (ρ : ℝ) ^ (-(ζ' - ζ)) ∧
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
  obtain ⟨κ₀, t, W, hsubW, hused, hline, hslack, hcard⟩ := hup ρ hρ
  have hρ4 : (ρ : ℝ) ≤ 1 / 4 := le_trans (by exact_mod_cast hρ.2) hwin4
  have hρ0 : 0 < ρ := lt_of_lt_of_le (NNReal.rpow_pos hσ0) hρ.1
  exact canonicalCoverAt_of_upstairs_lineED hsit hR T₀ 𝕋 hρ0 hρ4 t W hsubW hused hA0 hline
    hslack hcard

/-- **The `A₁`-loaded budget is a threshold on the scale, not an exponent.**  `A` and
`⌈C₃(R)⌉` are `δ`-free, so for any positive reading gap `ζ' − ζ` the budget clause of
`canonicalCoverAt_of_upstairs_lineED` holds at every scale below an explicit `ρ₀` — the point of
replacing `SpineEDExtraction`'s family-level `M` (bounded only by `ρ^{-m}`, spending `m` of the
gap) by an absolute constant. -/
theorem exists_threshold_lineED_budget {ζ ζ' : ℝ} (hgap : 0 < ζ' - ζ) (A : ℕ) (R : ℝ) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ρ₀ ≤ 1 ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
      (A : ℝ) * (lineEDPushConstant R : ℝ) * (spineOuterCountLoss R : ℝ) ≤ ρ ^ (-(ζ' - ζ)) :=
  exists_threshold_const_le_rpow hgap

/-- **Step 10 of the non-eccentric case, with the upstairs pairwise-ED hypothesis REMOVED.**

The twin of `Kakeya.ML2Reduction.multiplicity_le_of_lemma91At_outer_of_upstairs_essDistinct`.
That theorem's `hup` asks the upstairs `ρ`-parent family to be **pairwise** essentially distinct —
the hypothesis  showed cannot be bought downstairs and that the refined text does not
have (its levels are line-ED by construction, l.4085–4092, and a net-based cover is *far* from
pairwise-ED, source map §1.4).  Here it is replaced by line-based `A`-ED, at the price of the
factor `A` in the same budget clause.

**Measured answer to the GC-1 question** "does the covering bridge remove the upstairs-ED
hypothesis of step 10 entirely when the levels are line-ED?": **yes**, and the residue it leaves
is one absolute constant in the budget, not a hypothesis. -/
theorem multiplicity_le_of_lemma91At_outer_of_upstairs_lineED
    {β ϖ ζ ζ' ν ηd cst : ℝ} {R : ℝ} {σ : NNReal}
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
    {A : ℕ} (hA0 : 0 < A)
    (hup : ∀ ρ : NNReal, ρ ∈ Set.Icc (σ ^ (1 - ϖ)) (σ ^ ϖ) →
      ∃ (κ₀ : Type u) (t : Finset κ₀) (W : κ₀ → Tube (ρ * θ) (EuclideanSpace ℝ (Fin 3))),
        (∀ k ∈ t, (W k).carrier ⊆ T₀.carrier) ∧
        (∀ k ∈ t, ∃ i ∈ s, (𝕋 i).carrier ⊆ (W k).carrier) ∧
        Kakeya.VeryNotSticky.IsLineEssDistinctAt (Tube.tubeOverlapCoreClose.C 3) A t W ∧
        (A : ℝ) * (lineEDPushConstant R : ℝ) * (spineOuterCountLoss R : ℝ)
            ≤ (ρ : ℝ) ^ (-(ζ' - ζ)) ∧
        (ρ : ℝ) ^ (-2 - ζ') ≤ (t.card : ℝ)) :
    ShadedBody.multiplicity s (fun i ↦ (𝕋 i).toShadedBody)
      ≤ (σ : ENNReal) ^ ν * (s.card : ENNReal) ^ β :=
  multiplicity_le_of_lemma91At_outer_of_canonicalCover hL hζ hsit hR hR1 hτσ hσ0 hϖ T₀ s 𝕋 hsub
    hloss hmax hfull hcen huni
    (canonicalCover_of_upstairs_lineED (ζ' := ζ') hsit hR T₀ 𝕋 hσ0 hwin4 hA0 hup)

end CoveringBridge

end Kakeya.ML2Reduction

namespace Kakeya.ML2Core

universe u

/-! ## The middle factor with the canonical-cover datum factored out -/

section Factored

open Classical in
/-- **The sharp middle factor, with the canonical-cover datum as a binder.**

`Kakeya.ML2Core.middle_factor_of_edNodes_sharp` (existing, unchanged, and **not** re-cut — see
) reaches step 10 through one intermediate object, the canonical-cover
datum `hcanon` of `Kakeya.ML2Reduction.fine_factor_of_lemma91At_of_canonicalCover`.  Everything
between the ED-node clause and `hcanon` is the producer's business; everything after it is the
same for every producer.  This theorem is that theorem with `hED`, `hbudget` and `hwin4` replaced
by `hcanon` itself; the existing theorem is re-derived from it below
(`middle_factor_of_edNodes_sharp'`) as a control that the factorisation is faithful, and the
line-based twin is derived from it through the covering bridge. -/
theorem middle_factor_of_canonicalCover_sharp
    {β ϖ ε₁ : ℝ} {gain dens : ℝ → ℝ} {k : ℕ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    (hk : k < ML2Spine.spineCount ϖ ε₁)
    -- the ambient window and the transport 
    {δ θ τ δt : NNReal} {Rout : ℝ} {w : ℝ}
    (hsitOut : Tube.IsRescalingSituation θ τ δt Rout 3) (hRout : 0 < Rout)
    (hτθ : (τ : ℝ) / (θ : ℝ) ≤ 4 * (δt : ℝ))
    (Tθ : Tube θ (EuclideanSpace ℝ (Fin 3)))
    {α : Type u} {fib : Finset α}
    (Y : α → ShadedTube τ (EuclideanSpace ℝ (Fin 3)))
    (hsubOut : ∀ j ∈ fib, (Y j).carrier ⊆ Tθ.carrier)
    (hw : 0 ≤ w) (hsep : δt ≤ δ ^ w)
    -- the rescaled world 
    {b δ' : NNReal} {R : ℝ}
    (hδ0 : 0 < δt) (hδ1 : δt ≤ 1) (hδ'0 : 0 < δ') (hb1 : b ≤ 1) (hδtb : δt ≤ b)
    (hbw : δt ^ ML2Spine.spineEps₂ ϖ ε₁ ≤ b) (hprod : δ' * b = δt)
    {κc : Type u} {t' : Finset κc} {Zρ : κc → ShadedTube b (EuclideanSpace ℝ (Fin 3))} {ηc : ℝ}
    (hcoarse : ∀ (dt : NNReal), dt ≠ 0 → dt ≤ b → b ≤ 1 →
      ∀ {ι : Type u} (t : Finset ι) (T : ι → ShadedTube b (EuclideanSpace ℝ (Fin 3))),
        (∀ i, (T i).carrier ⊆ closedBall 0 1) →
        (ShadedBody.fullness t (fun i ↦ (T i).toShadedBody) : ℝ) ≥ (b : ℝ) ^ ηc →
        Kakeya.maxDensity t (fun i ↦ (T i).toConvexSpaceBody)
          ≤ (dt : ENNReal) ^ (-(12 * ML2Spine.spineRung β ϖ ε₁ gain dens k
              / (ML2Spine.spineDiv ϖ ε₁ * β))) →
        ShadedBody.multiplicity t (fun i ↦ (T i).toShadedBody)
          ≤ (dt : ENNReal) ^ (-(2 * (12 * ML2Spine.spineRung β ϖ ε₁ gain dens k
              / (ML2Spine.spineDiv ϖ ε₁ * β)))) * (t.card : ENNReal) ^ β)
    (hballb : ∀ j, (Zρ j).carrier ⊆ closedBall 0 1)
    (hfullb : (ShadedBody.fullness t' (fun j ↦ (Zρ j).toShadedBody) : ℝ) ≥ (b : ℝ) ^ ηc)
    (hDb : Kakeya.maxDensity t' (fun j ↦ (Zρ j).toConvexSpaceBody)
      ≤ (δt : ENNReal) ^ (-(12 * ML2Spine.spineRung β ϖ ε₁ gain dens k
          / (ML2Spine.spineDiv ϖ ε₁ * β))))
    {s' : Finset α} (hs' : s' ⊆ fib)
    {U' : α → ShadedTube δ' (EuclideanSpace ℝ (Fin 3))}
    (hsit : Tube.IsRescalingSituation b δt δ' R 3) (hR : 0 < R) (hR1 : 1 ≤ R)
    (hτσ : (δt : ℝ) / (b : ℝ) ≤ 4 * (δ' : ℝ))
    (T₀ : Tube b (EuclideanSpace ℝ (Fin 3)))
    (hsubfib : ∀ i ∈ fib,
      (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y i).carrier ⊆ T₀.carrier)
    {cst ζ ηd : ℝ}
    (mm : EuclideanSpace ℝ (Fin 3)) {qc : ℝ} (hqc0 : 0 < qc) (h3qc : 3 * qc ≤ ηd)
    (hcb : Kakeya.VeryNotSticky.CentredHandBack hsit hR T₀ mm qc fib s'
      (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y) U')
    (hL91 : ML2Reduction.Lemma91At.{u} β ϖ ζ
      (gain (ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2) + 3 * qc) ηd δ')
    -- the exact negation of the vacuity condition
    -- `Kakeya.VeryNotSticky.lemma91Binders_vacuous_of_exponents` (cited by name only — this is a
    -- hypothesis, not a consumed term, so the witness leaf is NOT imported): Lemma 9.1's binder
    -- list is jointly unsatisfiable whenever `2 + ηd < (1 - ϖ) * (2 + ζ)`, and `hζ` is exactly
    -- its negation, so it is what keeps `hL91` above from being vacuously true.  Corroborated
    -- caller-side by the source's own `ζ ≤ (4/5) ζ_*` (refined l.2831–2834).
    (hζ : ζ * (1 - ϖ) ≤ ηd + 2 * ϖ)
    (hloss : ML2Reduction.outerLoss R ≤ δ' ^ (-cst))
    (hmax : Kakeya.maxDensity fib (fun i ↦
        (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y i).toConvexSpaceBody)
      ≤ (δ' : ENNReal) ^ (-(ηd - cst)))
    (hfull : ShadedBody.fullness s' (fun i ↦ (U' i).toShadedBody) ≥ δ' ^ ηd)
    (huni : ∃ C : NNReal, 1 ≤ C ∧ (C : ENNReal) ≤ (δ' : ENNReal) ^ (-ηd) ∧
      Nonempty (ShadedTube.ShadedUniformTubeSet s' U' (Tube.ssfGridLen δ') C))
    -- step 10's datum, factored out: the count clause at the CENTRED representatives, which is
    -- `Kakeya.ML2Reduction.Lemma91At`'s clause verbatim.  A caller holding the canonical cover on
    -- the *rescaled bodies* reaches this through `Kakeya.VeryNotSticky.CountTransport`.
    (hcnt : ∀ ρ : NNReal, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) →
      ∃ (κ₁ : Type u) (tρ : Finset κ₁) (Tρ : κ₁ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
        (tρ : Set κ₁).Pairwise
          (fun j l ↦ _root_.IsEssentiallyDistinct (Tρ j).carrier (Tρ l).carrier) ∧
        (∀ j ∈ tρ, ∃ i ∈ s', (U' i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) ∧
        (ρ : ℝ) ^ (-2 - ζ) ≤ (tρ.card : ℝ))
    -- step 9, the cardinality multiplicativity and the loss ledger
    {Cf L Cu : ENNReal} {Nm : ℕ} {κ : ℝ}
    (hCf1 : (1 : ENNReal) ≤ Cf)
    (hsplit : ShadedBody.multiplicity fib (fun i ↦
        (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y i).toShadedBody)
      ≤ L * (ShadedBody.multiplicity t' (fun j ↦ (Zρ j).toShadedBody)
        * ShadedBody.multiplicity fib (fun i ↦
            (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y i).toShadedBody)))
    (hcard : (t'.card : ENNReal) * (fib.card : ENNReal) ≤ Cu * (Nm : ENNReal))
    (hLoss : L * Cf * Cu ^ β ≤ (δt : ENNReal) ^ (-κ))
    (hκ : κ ≤ ML2Spine.spineRung β ϖ ε₁ gain dens k / (20 * ML2Spine.spineDiv ϖ ε₁)) :
    ShadedBody.multiplicity fib (fun j ↦ (Y j).toShadedBody)
      ≤ (δ : ENNReal) ^ (w * (47 * ML2Spine.spineRung β ϖ ε₁ gain dens k
          / (5 * ML2Spine.spineDiv ϖ ε₁))) * (Nm : ENNReal) ^ β := by
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have hsp := ML2Spine.spineRung_isSpine (β := β) (ϖ := ϖ) (ε₁ := ε₁) (gain := gain)
    (dens := dens) hβ0 hβ1 hϖ hε₁ hgain hdens
  have hgm : 0 ≤ 47 * ML2Spine.spineRung β ϖ ε₁ gain dens k / (5 * ML2Spine.spineDiv ϖ ε₁) := by
    have h1 := hsp.rung_pos k
    have h2 := hsp.div_pos
    positivity
  refine middle_factor_of_rescaled hsitOut hRout hτθ Tθ Y hsubOut hgm hw hsep ?_
  set Z' : α → ShadedTube δt (EuclideanSpace ℝ (Fin 3)) :=
    ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y with hZ'
  have hb4 := hcoarse δt (ne_of_gt hδ0) hδtb hb1 t' Zρ hballb hfullb hDb
  -- Step 10 on the REPRESENTED family.  The hand-back's transport is *inside* the eliminator, so
  -- the `3 qc` is charged exactly once — in `hL91`'s gain (V-3).  `hU`, `hUshade`, `hret` and
  -- `hretm` are gone: the centred representative is the `normalise` image of the rescaled body,
  -- not the rescaled body, so `hU`/`hUshade` are false and `Cf` needs only `1 ≤ Cf`.
  have h10 := ML2Reduction.fine_factor_of_lemma91At_of_canonicalCover
    (ν := gain (ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2))
    hL91 hζ hsit hR hR1 hτσ hδ'0 hϖ.le hβ0.le hqc0 le_rfl h3qc T₀ mm hs' Z' U' hcb hsubfib hloss
    huni hcnt
  have h10' : ShadedBody.multiplicity fib (fun i ↦ (Z' i).toShadedBody)
      ≤ (δ' : ENNReal) ^ (gain (ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2))
        * (fib.card : ENNReal) ^ β := by
    rw [← ML2Reduction.outerFamily_multiplicity hn hsit hR hτσ hsubfib]
    exact h10
  have hsplit2 : ShadedBody.multiplicity fib (fun i ↦ (Z' i).toShadedBody)
      ≤ (L * Cf) * (ShadedBody.multiplicity t' (fun j ↦ (Zρ j).toShadedBody)
        * ShadedBody.multiplicity fib (fun i ↦ (Z' i).toShadedBody)) := by
    refine hsplit.trans (mul_le_mul' ?_ le_rfl)
    calc L = L * 1 := (mul_one L).symm
      _ ≤ L * Cf := by gcongr
  exact spine_multiplicity_le_two_factors_sharp hβ0 hβ1 hϖ hε₁ hgain hdens hk hδ0 hδ1 hbw hprod
    hsplit2 hb4 h10' hcard hLoss hκ

end Factored


/-! ## Control: the existing theorem, re-derived from the factored one -/

section FactorisationControl

open Classical in
/-- **`Kakeya.ML2Core.middle_factor_of_edNodes_sharp`, re-derived.**  Binder for binder the existing
theorem, proved as `middle_factor_of_canonicalCover_sharp ∘ canonicalCover_of_edNodes`.  It is a
**control**, not a replacement: the existing theorem is untouched (
forbids re-cutting it), and this re-derivation is what certifies that the factorisation above
lost nothing — the only thing the factored theorem asks for that the existing one did not is the
canonical-cover datum the existing one built. -/
theorem middle_factor_of_edNodes_sharp'
    {β ϖ ε₁ : ℝ} {gain dens : ℝ → ℝ} {k : ℕ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    (hk : k < ML2Spine.spineCount ϖ ε₁)
    -- the ambient window and the transport 
    {δ θ τ δt : NNReal} {Rout : ℝ} {w : ℝ}
    (hsitOut : Tube.IsRescalingSituation θ τ δt Rout 3) (hRout : 0 < Rout)
    (hτθ : (τ : ℝ) / (θ : ℝ) ≤ 4 * (δt : ℝ))
    (Tθ : Tube θ (EuclideanSpace ℝ (Fin 3)))
    {α : Type u} {fib : Finset α}
    (Y : α → ShadedTube τ (EuclideanSpace ℝ (Fin 3)))
    (hsubOut : ∀ j ∈ fib, (Y j).carrier ⊆ Tθ.carrier)
    (hw : 0 ≤ w) (hsep : δt ≤ δ ^ w)
    -- the rescaled world 
    {b δ' : NNReal} {R : ℝ}
    (hδ0 : 0 < δt) (hδ1 : δt ≤ 1) (hδ'0 : 0 < δ') (hb1 : b ≤ 1) (hδtb : δt ≤ b)
    (hbw : δt ^ ML2Spine.spineEps₂ ϖ ε₁ ≤ b) (hprod : δ' * b = δt)
    {κc : Type u} {t' : Finset κc} {Zρ : κc → ShadedTube b (EuclideanSpace ℝ (Fin 3))} {ηc : ℝ}
    (hcoarse : ∀ (dt : NNReal), dt ≠ 0 → dt ≤ b → b ≤ 1 →
      ∀ {ι : Type u} (t : Finset ι) (T : ι → ShadedTube b (EuclideanSpace ℝ (Fin 3))),
        (∀ i, (T i).carrier ⊆ closedBall 0 1) →
        (ShadedBody.fullness t (fun i ↦ (T i).toShadedBody) : ℝ) ≥ (b : ℝ) ^ ηc →
        Kakeya.maxDensity t (fun i ↦ (T i).toConvexSpaceBody)
          ≤ (dt : ENNReal) ^ (-(12 * ML2Spine.spineRung β ϖ ε₁ gain dens k
              / (ML2Spine.spineDiv ϖ ε₁ * β))) →
        ShadedBody.multiplicity t (fun i ↦ (T i).toShadedBody)
          ≤ (dt : ENNReal) ^ (-(2 * (12 * ML2Spine.spineRung β ϖ ε₁ gain dens k
              / (ML2Spine.spineDiv ϖ ε₁ * β)))) * (t.card : ENNReal) ^ β)
    (hballb : ∀ j, (Zρ j).carrier ⊆ closedBall 0 1)
    (hfullb : (ShadedBody.fullness t' (fun j ↦ (Zρ j).toShadedBody) : ℝ) ≥ (b : ℝ) ^ ηc)
    (hDb : Kakeya.maxDensity t' (fun j ↦ (Zρ j).toConvexSpaceBody)
      ≤ (δt : ENNReal) ^ (-(12 * ML2Spine.spineRung β ϖ ε₁ gain dens k
          / (ML2Spine.spineDiv ϖ ε₁ * β))))
    {s' : Finset α} (hs' : s' ⊆ fib)
    {U' : α → ShadedTube δ' (EuclideanSpace ℝ (Fin 3))}
    (hsit : Tube.IsRescalingSituation b δt δ' R 3) (hR : 0 < R) (hR1 : 1 ≤ R)
    (hτσ : (δt : ℝ) / (b : ℝ) ≤ 4 * (δ' : ℝ))
    (T₀ : Tube b (EuclideanSpace ℝ (Fin 3)))
    (hsubfib : ∀ i ∈ fib,
      (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y i).carrier ⊆ T₀.carrier)
    {cst ζ ζ' ηd : ℝ}
    (mm : EuclideanSpace ℝ (Fin 3)) {qc : ℝ} (hqc0 : 0 < qc) (h3qc : 3 * qc ≤ ηd)
    (hcb : Kakeya.VeryNotSticky.CentredHandBack hsit hR T₀ mm qc fib s'
      (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y) U')
    (hct : Kakeya.VeryNotSticky.CountTransport hsit hR T₀ mm ϖ ζ s'
      (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y) U')
    (hL91 : ML2Reduction.Lemma91At.{u} β ϖ ζ
      (gain (ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2) + 3 * qc) ηd δ')
    -- the exact negation of the vacuity condition
    -- `Kakeya.VeryNotSticky.lemma91Binders_vacuous_of_exponents` (cited by name only — this is a
    -- hypothesis, not a consumed term, so the witness leaf is NOT imported): Lemma 9.1's binder
    -- list is jointly unsatisfiable whenever `2 + ηd < (1 - ϖ) * (2 + ζ)`, and `hζ` is exactly
    -- its negation, so it is what keeps `hL91` above from being vacuously true.  Corroborated
    -- caller-side by the source's own `ζ ≤ (4/5) ζ_*` (refined l.2831–2834).
    (hζ : ζ * (1 - ϖ) ≤ ηd + 2 * ϖ)
    (hloss : ML2Reduction.outerLoss R ≤ δ' ^ (-cst))
    (hmax : Kakeya.maxDensity fib (fun i ↦
        (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y i).toConvexSpaceBody)
      ≤ (δ' : ENNReal) ^ (-(ηd - cst)))
    (hfull : ShadedBody.fullness s' (fun i ↦ (U' i).toShadedBody) ≥ δ' ^ ηd)
    -- AA/AB: tightened to the constant the producer actually returns
    -- (`ShadedTube.ssfUniformConst 3`, `Kakeya/ShadedUniform.lean:895`), with the threshold the
    -- loose bracket used to quantify away carried explicitly.  Discharged at wiring time by
    -- `exists_outerShadedUniformTubeSet_ssf` + `exists_threshold_coe_const_le_rpow_neg`.
    -- this binder is ALSO where the line-ED levels row is sourced.  The witness carries
    -- a uniform hierarchy, and `Kakeya.VeryNotSticky.lineEDLevelsAt_C3_of_huni` turns it (with
    -- `hcb`'s `centred`/`contained`/`small` rows and the uniformiser's own grid threshold) into
    -- `LineEDLevelsAt C₃ lineEDLevelsConstant _` at the NAMED constant (
    -- ): the datum is DERIVED here, never an ambient field.
    (huni : ((ShadedTube.ssfUniformConst 3 : NNReal) : ENNReal) ≤ (δ' : ENNReal) ^ (-ηd) ∧
      Nonempty (ShadedTube.ShadedUniformTubeSet s' U' (Tube.ssfGridLen δ')
        (ShadedTube.ssfUniformConst 3)))
    -- the ONE open input
    (hwin4 : ((δ' ^ ϖ : NNReal) : ℝ) ≤ 1 / 4)
    -- CONTRACTED-bottom window `[δ'^{1-ϖ}/C, δ'^{ϖ}]` — the hand-back reads the cover
    -- at `ρ/C`.  A producer must supply this clause on the wide
    -- window.  `hbudget` below did NOT move: `Kakeya.ML2Reduction.budget_descends` carries
    -- it from `ρ` down to `ρ/C`, at the cost of the reading gap `hgap`.
    (hED : ∀ ρ : NNReal, ρ ∈ Set.Icc
        (δ' ^ (1 - ϖ) / Kakeya.VeryNotSticky.edWindowContractionConstant) (δ' ^ ϖ) →
      ∃ (κ₀ : Type u) (t : Finset κ₀)
        (W : κ₀ → Tube (ρ * b) (EuclideanSpace ℝ (Fin 3))),
        ((t : Set κ₀).Pairwise
          fun j l ↦ _root_.IsEssentiallyDistinct (W j).carrier (W l).carrier) ∧
        (∀ l ∈ t, (W l).carrier ⊆ T₀.carrier) ∧
        (∀ l ∈ t, ∃ i ∈ s',
          (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y i).carrier
            ⊆ (W l).carrier) ∧
        (ρ : ℝ) ^ (-2 - ζ') ≤ (t.card : ℝ))
    (hbudget : ∀ ρ : NNReal, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) →
      (⌈((_root_.Tube.essDistinctTubesInSelfDilate.C 3
            (4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C 3) : NNReal) : ℝ)⌉₊ : ℝ)
          * (ML2Reduction.spineOuterCountLoss R : ℝ) ≤ (ρ : ℝ) ^ (-(ζ' - ζ)))
    -- this is `hbudget` with `centringCountLossConstant R ·` at the head of the left-hand
    -- side, so it IMPLIES `hbudget`; `hbudget` is retained only because keeps its text
    -- tree-wide.  Discharged by `exists_threshold_hup_budget`'s argument at the
    -- new constant, never assumed; `ζ < ζ'` (`hgap`) is its side condition.
    (hcntbudget : ∀ ρ : NNReal, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) →
      (Kakeya.VeryNotSticky.centringCountLossConstant R : ℝ)
        * (⌈((_root_.Tube.essDistinctTubesInSelfDilate.C 3
              (4 * (2 + 2) * R * Tube.tubeOverlapCoreClose.C 3) : NNReal) : ℝ)⌉₊ : ℝ)
          * (ML2Reduction.spineOuterCountLoss R : ℝ) ≤ (ρ : ℝ) ^ (-(ζ' - ζ)))
    (hgap : ζ ≤ ζ')
    -- step 9, the cardinality multiplicativity and the loss ledger
    {Cf L Cu : ENNReal} {Nm : ℕ} {κ : ℝ}
    (hCf1 : (1 : ENNReal) ≤ Cf)
    (hsplit : ShadedBody.multiplicity fib (fun i ↦
        (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y i).toShadedBody)
      ≤ L * (ShadedBody.multiplicity t' (fun j ↦ (Zρ j).toShadedBody)
        * ShadedBody.multiplicity fib (fun i ↦
            (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y i).toShadedBody)))
    (hcard : (t'.card : ENNReal) * (fib.card : ENNReal) ≤ Cu * (Nm : ENNReal))
    (hLoss : L * Cf * Cu ^ β ≤ (δt : ENNReal) ^ (-κ))
    (hκ : κ ≤ ML2Spine.spineRung β ϖ ε₁ gain dens k / (20 * ML2Spine.spineDiv ϖ ε₁)) :
    ShadedBody.multiplicity fib (fun j ↦ (Y j).toShadedBody)
      ≤ (δ : ENNReal) ^ (w * (47 * ML2Spine.spineRung β ϖ ε₁ gain dens k
          / (5 * ML2Spine.spineDiv ϖ ε₁))) * (Nm : ENNReal) ^ β :=
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have hsp := ML2Spine.spineRung_isSpine (β := β) (ϖ := ϖ) (ε₁ := ε₁) (gain := gain)
    (dens := dens) hβ0 hβ1 hϖ hε₁ hgain hdens
  middle_factor_of_canonicalCover_sharp hβ0 hβ1 hϖ hε₁ hgain hdens hk hsitOut hRout hτθ Tθ Y
    hsubOut hw hsep hδ0 hδ1 hδ'0 hb1 hδtb hbw hprod hcoarse hballb hfullb hDb hs' hsit hR hR1
    hτσ T₀ hsubfib mm hqc0 h3qc hcb hL91 hζ hloss hmax hfull
    (Kakeya.VeryNotSticky.huni_loose_of_tight huni)
    (fun ρ hρ ↦ hct ρ hρ
      (by
        -- the cover is read at the CONTRACTED radius; `hED` moved, `hbudget` did NOT —
        -- `Kakeya.ML2Reduction.budget_descends` carries it from `ρ` down to `ρ/C` 
        have hmem := Kakeya.VeryNotSticky.mem_widened_window_of_mem hρ
        have hc0 : 0 < ρ / Kakeya.VeryNotSticky.centringCoverRadiusConstant :=
          lt_of_lt_of_le (div_pos (NNReal.rpow_pos hδ'0)
            Kakeya.VeryNotSticky.edWindowContractionConstant_pos) hmem.1
        obtain ⟨κ₀, t, W, hEDt, hsubW, hused, hcard⟩ := hED _ hmem
        obtain ⟨κ₁, t₈, W', M, hsubW', hused', hM', hMρ', hcard'⟩ :=
          hstep8_of_essDistinct t W hEDt hsubW hused hcard
        exact ML2Reduction.canonicalCoverAt_of_step8_const (m := 0) (ζ' := ζ')
          (Kc := (Kakeya.VeryNotSticky.centringCountLossConstant R : ℝ))
          hsit hR T₀ _ hc0
          (le_trans (by exact_mod_cast hmem.2) hwin4) t₈ W' hsubW' hused' hM' hMρ' hcard'
          (ML2Reduction.budget_descends
            (h := ML2Reduction.hbud_of_hcntbudget (NNReal.coe_nonneg _)
              (by simpa using hcntbudget ρ hρ))
            (hρ'0 := by exact_mod_cast hc0)
            (hle := by exact_mod_cast Kakeya.VeryNotSticky.div_centringCoverRadiusConstant_le ρ)
            (he := by linarith))))
    hCf1 hsplit hcard hLoss hκ

end FactorisationControl


/-! ## The additive twin: the ED-node clause, line-based -/

section LineEDTwin

open Classical in
/-- **The twin of `Kakeya.ML2Core.canonicalCover_of_edNodes`.**  Same conclusion, character for
character; the pairwise ED clause is replaced by line-based `A`-ED at the tree's two-tube radius,
and the budget clause gains the factor `A`.  The
proof is the covering bridge `Kakeya.ML2Reduction.canonicalCover_of_upstairs_lineED`; unlike
`canonicalCover_of_edNodes` it does **not** route through
`Kakeya.ML2Reduction.canonicalCover_of_step8`, because that interface prices the extraction as a
`ρ`-power `ρ^{-m}` and the whole point of the line-based datum is that the price is absolute. -/
theorem canonicalCover_of_lineEDNodes {ϖ ζ ζ' : ℝ} {b δt δ' : NNReal} {R : ℝ}
    (hsit : Tube.IsRescalingSituation b δt δ' R 3) (hR : 0 < R) (hδ'0 : 0 < δ')
    (hwin4 : ((δ' ^ ϖ : NNReal) : ℝ) ≤ 1 / 4)
    (T₀ : Tube b (EuclideanSpace ℝ (Fin 3)))
    {α : Type u} {s' : Finset α} (Z' : α → ShadedTube δt (EuclideanSpace ℝ (Fin 3)))
    {A : ℕ} (hA0 : 0 < A)
    (hEDline : ∀ ρ : NNReal, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) →
      ∃ (κ₀ : Type u) (t : Finset κ₀)
        (W : κ₀ → Tube (ρ * b) (EuclideanSpace ℝ (Fin 3))),
        Kakeya.VeryNotSticky.IsLineEssDistinctAt (Tube.tubeOverlapCoreClose.C 3) A t W ∧
        (∀ k ∈ t, (W k).carrier ⊆ T₀.carrier) ∧
        (∀ k ∈ t, ∃ i ∈ s', (Z' i).carrier ⊆ (W k).carrier) ∧
        (ρ : ℝ) ^ (-2 - ζ') ≤ (t.card : ℝ))
    (hbudget : ∀ ρ : NNReal, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) →
      (A : ℝ) * (ML2Reduction.lineEDPushConstant R : ℝ)
          * (ML2Reduction.spineOuterCountLoss R : ℝ) ≤ (ρ : ℝ) ^ (-(ζ' - ζ))) :
    ∀ ρ : NNReal, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) →
      ∃ (κ₁ : Type u) (t : Finset κ₁) (W : κ₁ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
        ((t : Set κ₁).Pairwise
          fun j k ↦ _root_.IsEssentiallyDistinct (W j).carrier (W k).carrier) ∧
        (∀ j ∈ t, ∃ i ∈ s',
          (ML2Reduction.spineFamily
              (ML2Reduction.spineRescaleUnit hsit.pos_ambient T₀ hR) Z' i).toConvexSpaceBody
            ≤ (W j).toConvexSpaceBody) ∧
        (ML2Reduction.spineOuterCountLoss R : ℝ) * (ρ : ℝ) ^ (-2 - ζ) ≤ (t.card : ℝ) :=
  ML2Reduction.canonicalCover_of_upstairs_lineED (ζ' := ζ') hsit hR T₀ Z' hδ'0 hwin4 hA0
    (fun ρ hρ ↦ by
      obtain ⟨κ₀, t, W, hline, hsubW, hused, hcard⟩ := hEDline ρ hρ
      exact ⟨κ₀, t, W, hsubW, hused, hline, hbudget ρ hρ, hcard⟩)

open Classical in
/-- **The additive twin of `Kakeya.ML2Core.middle_factor_of_edNodes_sharp`**
Binder for binder the existing theorem, **which is not touched**, with two changes:

* `hED`'s pairwise `IsEssentiallyDistinct` clause becomes line-based `A`-ED at the tree's two-tube
  radius `Kakeya.Tube.tubeOverlapCoreClose.C 3` — the refined notion of l.153–163, at the radius
  E0's bridge is proved for rather than the refined `5` (E0 §1.3: the tree's only route from
  `¬ IsEssentiallyDistinct` to a line neighbourhood has constant `≈ 101`, and the hypothesis at
  the larger radius is the *stronger* one);
* `hbudget`'s left factor gains `A` — the bridge's retention `1/A`, paid out of the reading gap
  `ζ' − ζ` exactly as `SpineCanonicalCover`'s docstring prices `Ced·Λ` today.

**The conclusion is unchanged**, so every downstream budget statement applies verbatim: the
ambient gain is still `47 η_k/5` (`Kakeya.ML2Core.ambient_sharp_gain_ge`) and the rung ledger
still closes (`Kakeya.ML2Core.rung_budget_closes_of_overhead_le_four`, composed below as
`lineED_twin_rung_budget_closes`).  The twin costs the budget exactly the constant `A`, and a
constant is a threshold on the scale, not an exponent
(`Kakeya.ML2Reduction.exists_threshold_lineED_budget`). -/
theorem middle_factor_of_lineEDNodes_sharp
    {β ϖ ε₁ : ℝ} {gain dens : ℝ → ℝ} {k : ℕ}
    (hβ0 : 0 < β) (hβ1 : β ≤ 1) (hϖ : 0 < ϖ) (hε₁ : 0 < ε₁)
    (hgain : ∀ ζ, 0 < ζ → 0 < gain ζ) (hdens : ∀ ζ, 0 < ζ → 0 < dens ζ)
    (hk : k < ML2Spine.spineCount ϖ ε₁)
    -- the ambient window and the transport 
    {δ θ τ δt : NNReal} {Rout : ℝ} {w : ℝ}
    (hsitOut : Tube.IsRescalingSituation θ τ δt Rout 3) (hRout : 0 < Rout)
    (hτθ : (τ : ℝ) / (θ : ℝ) ≤ 4 * (δt : ℝ))
    (Tθ : Tube θ (EuclideanSpace ℝ (Fin 3)))
    {α : Type u} {fib : Finset α}
    (Y : α → ShadedTube τ (EuclideanSpace ℝ (Fin 3)))
    (hsubOut : ∀ j ∈ fib, (Y j).carrier ⊆ Tθ.carrier)
    (hw : 0 ≤ w) (hsep : δt ≤ δ ^ w)
    -- the rescaled world 
    {b δ' : NNReal} {R : ℝ}
    (hδ0 : 0 < δt) (hδ1 : δt ≤ 1) (hδ'0 : 0 < δ') (hb1 : b ≤ 1) (hδtb : δt ≤ b)
    (hbw : δt ^ ML2Spine.spineEps₂ ϖ ε₁ ≤ b) (hprod : δ' * b = δt)
    {κc : Type u} {t' : Finset κc} {Zρ : κc → ShadedTube b (EuclideanSpace ℝ (Fin 3))} {ηc : ℝ}
    (hcoarse : ∀ (dt : NNReal), dt ≠ 0 → dt ≤ b → b ≤ 1 →
      ∀ {ι : Type u} (t : Finset ι) (T : ι → ShadedTube b (EuclideanSpace ℝ (Fin 3))),
        (∀ i, (T i).carrier ⊆ closedBall 0 1) →
        (ShadedBody.fullness t (fun i ↦ (T i).toShadedBody) : ℝ) ≥ (b : ℝ) ^ ηc →
        Kakeya.maxDensity t (fun i ↦ (T i).toConvexSpaceBody)
          ≤ (dt : ENNReal) ^ (-(12 * ML2Spine.spineRung β ϖ ε₁ gain dens k
              / (ML2Spine.spineDiv ϖ ε₁ * β))) →
        ShadedBody.multiplicity t (fun i ↦ (T i).toShadedBody)
          ≤ (dt : ENNReal) ^ (-(2 * (12 * ML2Spine.spineRung β ϖ ε₁ gain dens k
              / (ML2Spine.spineDiv ϖ ε₁ * β)))) * (t.card : ENNReal) ^ β)
    (hballb : ∀ j, (Zρ j).carrier ⊆ closedBall 0 1)
    (hfullb : (ShadedBody.fullness t' (fun j ↦ (Zρ j).toShadedBody) : ℝ) ≥ (b : ℝ) ^ ηc)
    (hDb : Kakeya.maxDensity t' (fun j ↦ (Zρ j).toConvexSpaceBody)
      ≤ (δt : ENNReal) ^ (-(12 * ML2Spine.spineRung β ϖ ε₁ gain dens k
          / (ML2Spine.spineDiv ϖ ε₁ * β))))
    {s' : Finset α} (hs' : s' ⊆ fib)
    {U' : α → ShadedTube δ' (EuclideanSpace ℝ (Fin 3))}
    (hsit : Tube.IsRescalingSituation b δt δ' R 3) (hR : 0 < R) (hR1 : 1 ≤ R)
    (hτσ : (δt : ℝ) / (b : ℝ) ≤ 4 * (δ' : ℝ))
    (T₀ : Tube b (EuclideanSpace ℝ (Fin 3)))
    (hsubfib : ∀ i ∈ fib,
      (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y i).carrier ⊆ T₀.carrier)
    {cst ζ ζ' ηd : ℝ}
    (mm : EuclideanSpace ℝ (Fin 3)) {qc : ℝ} (hqc0 : 0 < qc) (h3qc : 3 * qc ≤ ηd)
    (hcb : Kakeya.VeryNotSticky.CentredHandBack hsit hR T₀ mm qc fib s'
      (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y) U')
    (hct : Kakeya.VeryNotSticky.CountTransport hsit hR T₀ mm ϖ ζ s'
      (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y) U')
    (hL91 : ML2Reduction.Lemma91At.{u} β ϖ ζ
      (gain (ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2) + 3 * qc) ηd δ')
    -- the exact negation of the vacuity condition
    -- `Kakeya.VeryNotSticky.lemma91Binders_vacuous_of_exponents` (cited by name only — this is a
    -- hypothesis, not a consumed term, so the witness leaf is NOT imported): Lemma 9.1's binder
    -- list is jointly unsatisfiable whenever `2 + ηd < (1 - ϖ) * (2 + ζ)`, and `hζ` is exactly
    -- its negation, so it is what keeps `hL91` above from being vacuously true.  Corroborated
    -- caller-side by the source's own `ζ ≤ (4/5) ζ_*` (refined l.2831–2834).
    (hζ : ζ * (1 - ϖ) ≤ ηd + 2 * ϖ)
    (hloss : ML2Reduction.outerLoss R ≤ δ' ^ (-cst))
    (hmax : Kakeya.maxDensity fib (fun i ↦
        (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y i).toConvexSpaceBody)
      ≤ (δ' : ENNReal) ^ (-(ηd - cst)))
    (hfull : ShadedBody.fullness s' (fun i ↦ (U' i).toShadedBody) ≥ δ' ^ ηd)
    -- AA/AB: tightened to the constant the producer actually returns
    -- (`ShadedTube.ssfUniformConst 3`, `Kakeya/ShadedUniform.lean:895`), with the threshold the
    -- loose bracket used to quantify away carried explicitly.  Discharged at wiring time by
    -- `exists_outerShadedUniformTubeSet_ssf` + `exists_threshold_coe_const_le_rpow_neg`.
    -- this binder is ALSO where the line-ED levels row is sourced.  The witness carries
    -- a uniform hierarchy, and `Kakeya.VeryNotSticky.lineEDLevelsAt_C3_of_huni` turns it (with
    -- `hcb`'s `centred`/`contained`/`small` rows and the uniformiser's own grid threshold) into
    -- `LineEDLevelsAt C₃ lineEDLevelsConstant _` at the NAMED constant (
    -- ): the datum is DERIVED here, never an ambient field.
    (huni : ((ShadedTube.ssfUniformConst 3 : NNReal) : ENNReal) ≤ (δ' : ENNReal) ^ (-ηd) ∧
      Nonempty (ShadedTube.ShadedUniformTubeSet s' U' (Tube.ssfGridLen δ')
        (ShadedTube.ssfUniformConst 3)))
    -- the ONE open input, line-based
    (hwin4 : ((δ' ^ ϖ : NNReal) : ℝ) ≤ 1 / 4)
    {A : ℕ} (hA0 : 0 < A)
    -- CONTRACTED-bottom window `[δ'^{1-ϖ}/C, δ'^{ϖ}]` — the hand-back reads the cover
    -- at `ρ/C`.  A producer must supply this clause on the wide
    -- window.  `hbudget` below did NOT move: `Kakeya.ML2Reduction.budget_descends` carries
    -- it from `ρ` down to `ρ/C`, at the cost of the reading gap `hgap`.
    (hEDline : ∀ ρ : NNReal, ρ ∈ Set.Icc
        (δ' ^ (1 - ϖ) / Kakeya.VeryNotSticky.edWindowContractionConstant) (δ' ^ ϖ) →
      ∃ (κ₀ : Type u) (t : Finset κ₀)
        (W : κ₀ → Tube (ρ * b) (EuclideanSpace ℝ (Fin 3))),
        Kakeya.VeryNotSticky.IsLineEssDistinctAt (Tube.tubeOverlapCoreClose.C 3) A t W ∧
        (∀ l ∈ t, (W l).carrier ⊆ T₀.carrier) ∧
        (∀ l ∈ t, ∃ i ∈ s',
          (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y i).carrier
            ⊆ (W l).carrier) ∧
        (ρ : ℝ) ^ (-2 - ζ') ≤ (t.card : ℝ))
    (hbudget : ∀ ρ : NNReal, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) →
      (A : ℝ) * (ML2Reduction.lineEDPushConstant R : ℝ)
          * (ML2Reduction.spineOuterCountLoss R : ℝ) ≤ (ρ : ℝ) ^ (-(ζ' - ζ)))
    -- this is `hbudget` with `centringCountLossConstant R ·` at the head of the left-hand
    -- side, so it IMPLIES `hbudget`; `hbudget` is retained only because keeps its text
    -- tree-wide.  Discharged by `exists_threshold_hup_budget`'s argument at the
    -- new constant, never assumed; `ζ < ζ'` (`hgap`) is its side condition.  The `A` here is
    -- `hEDline`'s carried line-ED constant — the same `A` that `hbudget` above already prices,
    -- not a fresh variable: the twin's whole price is that constant (`A₁ = 2·641⁶` at the
    -- refined reading), and it is a threshold on the scale, not an exponent.  This is the one
    -- site whose left-hand side is `A · lineEDPushConstant R · spineOuterCountLoss R` rather
    -- than the `⌈…⌉₊` form, so it is the first threshold to check.
    (hcntbudget : ∀ ρ : NNReal, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) →
      (Kakeya.VeryNotSticky.centringCountLossConstant R : ℝ)
        * (A : ℝ) * (ML2Reduction.lineEDPushConstant R : ℝ)
          * (ML2Reduction.spineOuterCountLoss R : ℝ) ≤ (ρ : ℝ) ^ (-(ζ' - ζ)))
    (hgap : ζ ≤ ζ')
    -- step 9, the cardinality multiplicativity and the loss ledger
    {Cf L Cu : ENNReal} {Nm : ℕ} {κ : ℝ}
    (hCf1 : (1 : ENNReal) ≤ Cf)
    (hsplit : ShadedBody.multiplicity fib (fun i ↦
        (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y i).toShadedBody)
      ≤ L * (ShadedBody.multiplicity t' (fun j ↦ (Zρ j).toShadedBody)
        * ShadedBody.multiplicity fib (fun i ↦
            (ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y i).toShadedBody)))
    (hcard : (t'.card : ENNReal) * (fib.card : ENNReal) ≤ Cu * (Nm : ENNReal))
    (hLoss : L * Cf * Cu ^ β ≤ (δt : ENNReal) ^ (-κ))
    (hκ : κ ≤ ML2Spine.spineRung β ϖ ε₁ gain dens k / (20 * ML2Spine.spineDiv ϖ ε₁)) :
    ShadedBody.multiplicity fib (fun j ↦ (Y j).toShadedBody)
      ≤ (δ : ENNReal) ^ (w * (47 * ML2Spine.spineRung β ϖ ε₁ gain dens k
          / (5 * ML2Spine.spineDiv ϖ ε₁))) * (Nm : ENNReal) ^ β :=
  middle_factor_of_canonicalCover_sharp hβ0 hβ1 hϖ hε₁ hgain hdens hk hsitOut hRout hτθ Tθ Y
    hsubOut hw hsep hδ0 hδ1 hδ'0 hb1 hδtb hbw hprod hcoarse hballb hfullb hDb hs' hsit hR hR1
    hτσ T₀ hsubfib mm hqc0 h3qc hcb hL91 hζ hloss hmax hfull
    (Kakeya.VeryNotSticky.huni_loose_of_tight huni)
    (fun ρ hρ ↦ hct ρ hρ
      (by
        -- as above, through the LINE-based pointwise cover
        have hmem := Kakeya.VeryNotSticky.mem_widened_window_of_mem hρ
        have hc0 : 0 < ρ / Kakeya.VeryNotSticky.centringCoverRadiusConstant :=
          lt_of_lt_of_le (div_pos (NNReal.rpow_pos hδ'0)
            Kakeya.VeryNotSticky.edWindowContractionConstant_pos) hmem.1
        obtain ⟨κ₀, t, W, hline, hsubW, hused, hcard⟩ := hEDline _ hmem
        exact ML2Reduction.canonicalCoverAt_of_upstairs_lineED_const (ζ' := ζ')
          (Kc := (Kakeya.VeryNotSticky.centringCountLossConstant R : ℝ))
          (NNReal.coe_nonneg _) hsit hR T₀ _ hc0
          (le_trans (by exact_mod_cast hmem.2) hwin4) t W hsubW hused hA0 hline
          (ML2Reduction.budget_descends
            (h := by
              have h1 := ML2Reduction.le_of_mul_spineOuterCountLoss (R := R)
                (x := (Kakeya.VeryNotSticky.centringCountLossConstant R : ℝ) * (A : ℝ)
                  * (ML2Reduction.lineEDPushConstant R : ℝ)) (by positivity)
                (hcntbudget ρ hρ)
              have hEq : (A : ℝ) * (ML2Reduction.lineEDPushConstant R : ℝ)
                    * (Kakeya.VeryNotSticky.centringCountLossConstant R : ℝ)
                  = (Kakeya.VeryNotSticky.centringCountLossConstant R : ℝ) * (A : ℝ)
                    * (ML2Reduction.lineEDPushConstant R : ℝ) := by ring
              rw [hEq]; exact h1)
            (hρ'0 := by exact_mod_cast hc0)
            (hle := by exact_mod_cast Kakeya.VeryNotSticky.div_centringCoverRadiusConstant_le ρ)
            (he := by linarith)) hcard))
    hCf1 hsplit hcard hLoss hκ

/-- **The twin at the refined constant `A₁ = 2·641⁶`** — 's condition
text with `A` instantiated at the source's own absolute (l.4900–4901).  This is the datum U1's
centred canonical cover produces. -/
theorem canonicalCover_of_lineEDLevelNodes {ϖ ζ ζ' : ℝ} {b δt δ' : NNReal} {R : ℝ}
    (hsit : Tube.IsRescalingSituation b δt δ' R 3) (hR : 0 < R) (hδ'0 : 0 < δ')
    (hwin4 : ((δ' ^ ϖ : NNReal) : ℝ) ≤ 1 / 4)
    (T₀ : Tube b (EuclideanSpace ℝ (Fin 3)))
    {α : Type u} {s' : Finset α} (Z' : α → ShadedTube δt (EuclideanSpace ℝ (Fin 3)))
    (hEDline : ∀ ρ : NNReal, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) →
      ∃ (κ₀ : Type u) (t : Finset κ₀)
        (W : κ₀ → Tube (ρ * b) (EuclideanSpace ℝ (Fin 3))),
        Kakeya.VeryNotSticky.IsLineEssDistinctAt (Tube.tubeOverlapCoreClose.C 3)
            lineEDLevelConstant t W ∧
        (∀ k ∈ t, (W k).carrier ⊆ T₀.carrier) ∧
        (∀ k ∈ t, ∃ i ∈ s', (Z' i).carrier ⊆ (W k).carrier) ∧
        (ρ : ℝ) ^ (-2 - ζ') ≤ (t.card : ℝ))
    (hbudget : ∀ ρ : NNReal, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) →
      (lineEDLevelConstant : ℝ) * (ML2Reduction.lineEDPushConstant R : ℝ)
          * (ML2Reduction.spineOuterCountLoss R : ℝ) ≤ (ρ : ℝ) ^ (-(ζ' - ζ))) :
    ∀ ρ : NNReal, ρ ∈ Set.Icc (δ' ^ (1 - ϖ)) (δ' ^ ϖ) →
      ∃ (κ₁ : Type u) (t : Finset κ₁) (W : κ₁ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
        ((t : Set κ₁).Pairwise
          fun j k ↦ _root_.IsEssentiallyDistinct (W j).carrier (W k).carrier) ∧
        (∀ j ∈ t, ∃ i ∈ s',
          (ML2Reduction.spineFamily
              (ML2Reduction.spineRescaleUnit hsit.pos_ambient T₀ hR) Z' i).toConvexSpaceBody
            ≤ (W j).toConvexSpaceBody) ∧
        (ML2Reduction.spineOuterCountLoss R : ℝ) * (ρ : ℝ) ^ (-2 - ζ) ≤ (t.card : ℝ) :=
  canonicalCover_of_lineEDNodes (ζ' := ζ') hsit hR hδ'0 hwin4 T₀ Z' lineEDLevelConstant_pos
    hEDline hbudget

end LineEDTwin

/-! ## The budget: what the twin costs, measured -/

section Budget

/-- **The twin's budget clause implies the existing one, by exactly the factor `A`.**  Setting
`A = 1` recovers `Kakeya.ML2Core.canonicalCover_of_edNodes`'s budget; every `A ≥ 1` is that clause
times `A`.  This is the whole price of the line-based reading. -/
theorem edNodes_budget_of_lineED_budget {A : ℕ} (hA : 1 ≤ A) {R : ℝ} {ρ g : ℝ}
    (h : (A : ℝ) * (ML2Reduction.lineEDPushConstant R : ℝ)
        * (ML2Reduction.spineOuterCountLoss R : ℝ) ≤ ρ ^ g) :
    (ML2Reduction.lineEDPushConstant R : ℝ)
        * (ML2Reduction.spineOuterCountLoss R : ℝ) ≤ ρ ^ g := by
  refine le_trans ?_ h
  have hA1 : (1 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have h0 : (0 : ℝ) ≤ (ML2Reduction.lineEDPushConstant R : ℝ)
      * (ML2Reduction.spineOuterCountLoss R : ℝ) := by positivity
  nlinarith [h0, hA1]

/-- **`A₁ = 2·641⁶` is a threshold on the scale, not an exponent.**  At any positive reading gap
`ζ' − ζ` the twin's budget clause holds at every `ρ ≤ ρ₀`, with `ρ₀` explicit — because both
`A₁` and the push-up constant `⌈C₃(R)⌉` are `δ`-free.  Contrast
`Kakeya.ML2Reduction.hup_of_step8`, whose `M ≤ ρ^{-m}` spends `m` of the gap, and
`Kakeya.ML2Core.spine_hup_gap_of_div`, the inequality that spending forces on the spine. -/
theorem exists_threshold_lineEDLevelConstant_budget {ζ ζ' : ℝ} (hgap : 0 < ζ' - ζ) (R : ℝ) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ρ₀ ≤ 1 ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
      (lineEDLevelConstant : ℝ) * (ML2Reduction.lineEDPushConstant R : ℝ)
        * (ML2Reduction.spineOuterCountLoss R : ℝ) ≤ ρ ^ (-(ζ' - ζ)) :=
  ML2Reduction.exists_threshold_lineED_budget hgap lineEDLevelConstant R

/-- **The rung-level budget still closes for the twin.**  The twin's conclusion exponent is the
existing one, `w · 47 X/(5 e)`, so `Kakeya.ML2Core.ambient_sharp_gain_ge` and
`Kakeya.ML2Core.rung_budget_closes_of_overhead_le_four` compose unchanged: the line-based reading
costs the ledger **nothing**, since its price is a constant and the ledger is an inequality
between exponents. -/
theorem lineED_twin_rung_budget_closes {ν X gmA Ω ε κc κ' w e : ℝ}
    (he : 0 < e) (hw : e ≤ w) (hX0 : 0 ≤ X) (hX : ν ≤ X)
    (hgmA : w * (47 * X / (5 * e)) ≤ gmA)
    (hΩ : Ω ≤ 4 * ν) (hsmall : 2 * ε + κc + κ' ≤ 2 * ν / 5) :
    Ω + 4 * ν + ε + (ε + κc + X) + κ' ≤ gmA :=
  rung_budget_closes_of_overhead_le_four hX
    (le_trans (ambient_sharp_gain_ge he hw hX0) hgmA) hΩ hsmall

end Budget

/-! ## The wiring: `GeometricCoreAt` with the line-ED levels as a named producer obligation -/

section Wiring

open Classical in
/-- **[DEAD ROUTE — see `Kakeya.ML2Core.SpineCountFloorObstruction`.]**

**`GeometricCoreAt` from the refined count floor, a middle factor that may read the line-ED
levels, and a producer of those levels.**

`Kakeya.ML2Core.geometricCoreAt_of_floor_middleFactor` (GC-FINAL-2) closes `GeometricCoreAt` from
two hypotheses, `hfloor` (the refined count floor, GC-2's obligation) and `hmid` (the middle
factor at the window's rung).  This theorem splits `hmid` into the two pieces the refined proof
actually has:

* `hlevels` — **U1's output at the wiring level**: the window's own hierarchy `𝒰` is line-ED at
  every level, at the absolute `A` (`A = lineEDLevelConstant = 2·641⁶` for the refined centred
  canonical cover, l.4900–4901).  This is exactly what  measured
  cannot be assumed of the *existing* uniformiser's grid-net nodes and must come from the
  centred-net uniformiser; carrying it as a separate `∀ᶠ` hypothesis is what makes the wiring
  compile **before** U1 lands, and names the obligation instead of hiding it.
* `hmidline` — `hmid` with the line-ED levels as an extra binder, i.e. the middle factor a
  producer may prove *using* them (through `middle_factor_of_lineEDNodes_sharp` and the covering
  bridge).

The radius is the tree's two-tube constant, not the refined `5`: see the file docstring and E0
§1.3.  Nothing here weakens `geometricCoreAt_of_floor_middleFactor` — instantiating `hlevels` with
a proof and `hmidline` with an `hmid` that ignores it recovers it exactly. -/
theorem geometricCoreAt_of_lineEDLevels
    (hSFE : StickyKakeya.StickyFrostmanEstimate.{0, 0}
      (E := EuclideanSpace ℝ (Fin 3)))
    {η' : ℝ} {A : ℕ}
    (hlevels : ∀ (β ϖ : ℝ) (gain dens : ℝ → ℝ), 0 < β → β ≤ 1 →
      ML2Assembly.Lemma91ParamsAt.{u} β ϖ gain dens →
      KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
      FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
      ∀ ε₁ : ℝ, 0 < ε₁ →
      ∀ ηin : ℝ, 0 < ηin → ηin ≤ ML2Spine.spineNu β ϖ ε₁ gain dens →
      ∀ _Cu₀ : NNReal,
      ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} (u : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (Cu _lam :
          NNReal)
        (𝒰 : Tube.UniformTubeSet u (fun i ↦ (T i).toTube) (Tube.ssfGridLen δ) Cu)
        (Cstar : ENNReal) (a b m : ℕ),
        ML2Reduction.IsKatzTaoDividingWindow 𝒰 Cstar (ML2Spine.spineRung β ϖ ε₁ gain dens)
          (ML2Spine.spineDiv ϖ ε₁) (ML2Spine.spineCount ϖ ε₁) a b m →
        Kakeya.VeryNotSticky.LineEDLevelsAt (Kakeya.Tube.tubeOverlapCoreClose.C 3) A 𝒰)
    (hfloor : ∀ (β ϖ : ℝ) (gain dens : ℝ → ℝ), 0 < β → β ≤ 1 →
      ML2Assembly.Lemma91ParamsAt.{u} β ϖ gain dens →
      KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
      FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
      ∀ ε₁ : ℝ, 0 < ε₁ →
      ∀ ηin : ℝ, 0 < ηin → ηin ≤ ML2Spine.spineNu β ϖ ε₁ gain dens →
      ∀ Cu₀ : NNReal,
      ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} (u : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (Cu lam :
          NNReal)
        (𝒰 : Tube.UniformTubeSet u (fun i ↦ (T i).toTube) (Tube.ssfGridLen δ) Cu)
        (Cstar : ENNReal) (a b m : ℕ),
        ML2Reduction.IsKatzTaoDividingWindow 𝒰 Cstar (ML2Spine.spineRung β ϖ ε₁ gain dens)
          (ML2Spine.spineDiv ϖ ε₁) (ML2Spine.spineCount ϖ ε₁) a b m →
        (∀ i ∈ u, (T i).carrier ⊆ Metric.closedBall (0 : (EuclideanSpace ℝ (Fin 3))) 1) →
        u.Nonempty →
        Kakeya.maxDensity u (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-ηin) →
        ML2Shaded.HasDenseShading lam u (fun i ↦ (T i).toShadedBody) →
        ML2Shaded.HasComparableDensities lam⁻¹ u (fun i ↦ (T i).toShadedBody) →
        (δ : NNReal) ^ ηin / 2 ≤ lam →
        (u.card : NNReal) ≤ δ ^ (-(4 : ℝ)) →
        Cstar ≤ (δ : ENNReal) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens / 20)) →
        Cu ≤ Cu₀ →
        ∃ p : ℕ, a ≤ p ∧
          (∀ m' : ℕ, a < m' → m' < b →
            ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ (1 - ML2Spine.spineDiv ϖ ε₁)
              ≤ (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ) →
            (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ)
              ≤ ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ ML2Spine.spineDiv ϖ ε₁ →
            p < m') ∧
          (∀ jθ ∈ 𝒰.cover.indexSet a,
            Kakeya.maxDensity (𝒰.nodesUnder p a jθ) (fun j ↦ (𝒰.cover.tube p j).toConvexSpaceBody)
              ≤ (δ : ENNReal) ^ (-(2 * η'))) ∧
          (∀ jθ ∈ 𝒰.cover.indexSet a, ∀ jp ∈ 𝒰.nodesUnder p a jθ, ∀ m' : ℕ, a < m' → m' < b →
            ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ (1 - ML2Spine.spineDiv ϖ ε₁)
              ≤ (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ) →
            (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ)
              ≤ ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ ML2Spine.spineDiv ϖ ε₁ →
            p < m' →
            ((Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ))
                  ^ (2 + 4 * (ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1) / 16))
              ≤ ((𝒰.nodesUnder m' p jp).card : ℝ)))
    (hmidline : ∀ (β ϖ : ℝ) (gain dens : ℝ → ℝ), 0 < β → β ≤ 1 →
      ML2Assembly.Lemma91ParamsAt.{u} β ϖ gain dens →
      KatzTaoEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
      FrostmanEstimate.{u} (EuclideanSpace ℝ (Fin 3)) β →
      ∀ ε₁ : ℝ, 0 < ε₁ →
      ∀ ηin : ℝ, 0 < ηin → ηin ≤ ML2Spine.spineNu β ϖ ε₁ gain dens →
      ∀ Cu₀ : NNReal,
      ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type u} (u : Finset ι) (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (Cu lam :
          NNReal)
        (𝒰 : Tube.UniformTubeSet u (fun i ↦ (T i).toTube) (Tube.ssfGridLen δ) Cu)
        (Cstar : ENNReal) (a b m : ℕ),
        ML2Reduction.IsKatzTaoDividingWindow 𝒰 Cstar (ML2Spine.spineRung β ϖ ε₁ gain dens)
          (ML2Spine.spineDiv ϖ ε₁) (ML2Spine.spineCount ϖ ε₁) a b m →
        Kakeya.VeryNotSticky.LineEDLevelsAt (Kakeya.Tube.tubeOverlapCoreClose.C 3) A 𝒰 →
      ∀ (v : (EuclideanSpace ℝ (Fin 3))) (t₀ t₁ : Finset ι),
        t₁ ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain b →
        (∀ j ∈ t₁, ((𝒰.cover.tube b j).translate v).carrier ⊆ Metric.closedBall (0 :
            (EuclideanSpace ℝ (Fin 3))) 1) →
        (∀ i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι), ((T i).translate v).carrier ⊆
            Metric.closedBall (0 : (EuclideanSpace ℝ (Fin 3))) 1) →
        (a ≠ 0 → t₀ ⊆ ML2Reduction.activeNodes 𝒰.cover.toChain a) →
        (a ≠ 0 → ∀ j ∈ t₁, ML2Reduction.coarseNode 𝒰.cover.toChain a b j ∈ t₀) →
        (a ≠ 0 → ∀ k ∈ t₀,
          ((𝒰.cover.tube a k).translate v).carrier ⊆ Metric.closedBall (0 : (EuclideanSpace ℝ (Fin
              3))) 1) →
        (∀ i ∈ u, (T i).carrier ⊆ Metric.closedBall (0 : (EuclideanSpace ℝ (Fin 3))) 1) →
        u.Nonempty →
        Kakeya.maxDensity u (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-ηin) →
        ML2Shaded.HasDenseShading lam u (fun i ↦ (T i).toShadedBody) →
        ML2Shaded.HasComparableDensities lam⁻¹ u (fun i ↦ (T i).toShadedBody) →
        (δ : NNReal) ^ ηin / 2 ≤ lam →
        (u.card : NNReal) ≤ δ ^ (-(4 : ℝ)) →
        Cstar ≤ (δ : ENNReal) ^ (-(ML2Spine.spineNu β ϖ ε₁ gain dens / 20)) →
        Cu ≤ Cu₀ →
        0 < ∑ i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι), volume (T i).shade →
        δ ≤ Tube.gridScale δ (Tube.ssfGridLen δ) b →
        Tube.gridScale δ (Tube.ssfGridLen δ) b ≤ Tube.gridScale δ (Tube.ssfGridLen δ) a →
        Tube.gridScale δ (Tube.ssfGridLen δ) a ≤ 1 →
        -- the refined (F): the genuine parent level, its density, and the count floor
        ∀ p : ℕ, a ≤ p →
          (∀ m' : ℕ, a < m' → m' < b →
            ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ (1 - ML2Spine.spineDiv ϖ ε₁)
              ≤ (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ) →
            (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ)
              ≤ ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ ML2Spine.spineDiv ϖ ε₁ →
            p < m') →
          (∀ jθ ∈ 𝒰.cover.indexSet a,
            Kakeya.maxDensity (𝒰.nodesUnder p a jθ) (fun j ↦ (𝒰.cover.tube p j).toConvexSpaceBody)
              ≤ (δ : ENNReal) ^ (-(2 * η'))) →
          (∀ jθ ∈ 𝒰.cover.indexSet a, ∀ jp ∈ 𝒰.nodesUnder p a jθ, ∀ m' : ℕ, a < m' → m' < b →
            ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ (1 - ML2Spine.spineDiv ϖ ε₁)
              ≤ (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ) →
            (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ)
              ≤ ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ ML2Spine.spineDiv ϖ ε₁ →
            p < m' →
            ((Tube.gridScale δ (Tube.ssfGridLen δ) p : ℝ)
                / (Tube.gridScale δ (Tube.ssfGridLen δ) m' : ℝ))
                  ^ (2 + 4 * (ML2Spine.spineRung β ϖ ε₁ gain dens (m + 1) / 16))
              ≤ ((𝒰.nodesUnder m' p jp).card : ℝ)) →
      ∃ tτ' ⊆ t₁, ∃ tθ' ⊆ 𝒰.cover.indexSet a,
        ∃ (Yτ' : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) b) (EuclideanSpace ℝ (Fin 3)))
          (Yθ : ι → ShadedTube (Tube.gridScale δ (Tube.ssfGridLen δ) a) (EuclideanSpace ℝ (Fin 3)))
          (Y' : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (jθ : ι),
          (∀ j, (Yτ' j).toTube = (𝒰.cover.tube b j).translate v) ∧
          (∀ k, (Yθ k).toTube = (𝒰.cover.tube a k).translate v) ∧
          (∀ i, (Y' i).toTube = ((T i).translate v).toTube) ∧
          (a ≠ 0 → ∀ k ∈ tθ', (Yθ k).carrier ⊆ Metric.closedBall (0 : (EuclideanSpace ℝ (Fin 3)))
              1) ∧
          tτ'.Nonempty ∧ tθ'.Nonempty ∧
          ShadedBody.IsCRefinement
            ({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) | 𝒰.cover.assign b i ∈ tτ'} :
                Finset ι)
            (fun i ↦ (Y' i).toShadedBody) ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)
            (fun i ↦ ((T i).translate v).toShadedBody)
            (ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) (({i ∈ u |
                𝒰.cover.assign b i ∈ t₁} : Finset ι)).card δ)⁻¹ ∧
          (ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) (({i ∈ u |
              𝒰.cover.assign b i ∈ t₁} : Finset ι)).card δ *
              ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) tτ'.card
                (Tube.gridScale δ (Tube.ssfGridLen δ) b))⁻¹ *
              ShadedBody.fullness ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) (fun i ↦ (T
                  i).toShadedBody)
            ≤ ShadedBody.fullness tθ' (fun k ↦ (Yθ k).toShadedBody) ∧
          (∀ jτ ∈ tτ', ∀ jθ ∈ tθ',
            ShadedBody.multiplicity ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) (fun i ↦ (T
                i).toShadedBody)
              ≤ ((ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) (({i ∈
                  u | 𝒰.cover.assign b i ∈ t₁} : Finset ι)).card δ *
                    ML2Reduction.spineScaleLoss (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))
                        tτ'.card
                      (Tube.gridScale δ (Tube.ssfGridLen δ) b) : NNReal) : ENNReal)
                * ShadedBody.multiplicity
                    ({i ∈ ({i ∈ u | 𝒰.cover.assign b i ∈ t₁} : Finset ι) | 𝒰.cover.assign b i =
                        jτ} : Finset ι)
                    (fun i ↦ (Y' i).toShadedBody)
                * ShadedBody.multiplicity
                    ({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain a b j = jθ} : Finset ι)
                    (fun j ↦ (Yτ' j).toShadedBody)
                * ShadedBody.multiplicity tθ' (fun k ↦ (Yθ k).toShadedBody)) ∧
          jθ ∈ tθ' ∧
          ShadedBody.multiplicity ({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain a b j = jθ}
              : Finset ι) (fun j ↦ (Yτ' j).toShadedBody)
            ≤ (δ : ENNReal) ^ (47 * ML2Spine.spineRung β ϖ ε₁ gain dens m / 5)
              * ((({j ∈ tτ' | ML2Reduction.coarseNode 𝒰.cover.toChain a b j = jθ} : Finset
                  ι)).card : ENNReal) ^ β) :
    ML2Assembly.GeometricCoreAt.{u} := by
  classical
  refine geometricCoreAt_of_floor_middleFactor hSFE (η' := η') hfloor ?_
  intro β ϖ gain dens hβ0 hβ1 hp hKT hF ε₁ hε₁ ηin hηin0 hηinν Cu₀
  filter_upwards [hlevels β ϖ gain dens hβ0 hβ1 hp hKT hF ε₁ hε₁ ηin hηin0 hηinν Cu₀,
    hmidline β ϖ gain dens hβ0 hβ1 hp hKT hF ε₁ hε₁ ηin hηin0 hηinν Cu₀] with δ hlv hmd
  intro ι u T Cu lam 𝒰 Cstar a b m hwin
  exact hmd u T Cu lam 𝒰 Cstar a b m hwin (hlv u T Cu lam 𝒰 Cstar a b m hwin)

end Wiring

end Kakeya.ML2Core

end
