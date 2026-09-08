/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineMiddleFactor
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineLineEDMiddle
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineMiddleProducer
public import Kakeya.DimensionThree.MainLemma2.Reduction.BandSqueeze
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineEDPackingCeiling
public import Kakeya.DimensionThree.MainLemma2.Reduction.AssemblyPointwise

/-!
# `hED` / `hstep8`, split into a family and a floor — and where the floor is not

The last open row at all six middle-factor sites is an essentially distinct family of `ρb`-tubes
inside `T₀`, all-used over `s'`, of cardinality at least `ρ^{-2-ζ'}`.  This leaf separates the two
things that row asks for and measures which of them the large-family reading of Main Lemma 2
supplies.

## The split

`edCover_of_supplier_of_floor` factors the row into

* a **supplier** — for each `ρ` of the widened window, an essentially distinct family of
  `ρb`-tubes inside `T₀`, all-used over `s'`, with *whatever* count `N ρ` it happens to have; and
* a **floor** — `ρ^{-2-ζ'} ≤ N ρ`, a scalar row on the supplier's own count.

`hstep8_of_supplier_of_floor` composes that with the existing
`Kakeya.ML2Core.hstep8_of_essDistinct`, so the same two inputs give `hstep8` at `m = 0`, which is
the shape the step-8 site binds.  Neither half is proved here; the point of the split is that they
have different owners and only one of them is geometry.

## The floor is NOT supplied by the large-family reading — measured

The run's target is the large-family Main Lemma 2, whose export
`Kakeya.KKTResidual.KatzTaoEstimateStrict` carries `δ^{-2} ≤ |𝕋|`.  Three measurements, and the
conclusion is negative:

1. `Kakeya.ML2Assembly.Dichotomy` — what `GeometricCoreAt` actually asks a producer to prove —
   carries `(δ : ℝ)⁻¹ ≤ |𝕋|`, **`δ^{-1}`, not `δ^{-2}`**.  `cardFloor_strict_le_dichotomy` shows
   the strict clause implies it, which is exactly how
   `Kakeya.ML2Large.strict_drop_of_geometricCoreAt` gets from one to the other; and
   `not_cardFloor_dichotomy_le_strict` refutes the converse at `δ = 1/4`, so the two are genuinely
   different hypotheses and the stronger one is *spent* at that step, not carried.
2. The six middle-factor sites bind **no** cardinality lower bound of their own.  The only such
   bound anywhere in their signatures is the one inside `hED`/`hstep8` itself — i.e. the floor is
   part of what is owed, not part of what is given.
3. Even granting `δ^{-2} ≤ |𝕋|` at the outer scale, it is a bound on `|𝕋|`, and the floor is a
   bound on the cardinality of a **different** family — a cover by `ρb`-tubes.  The all-used row
   gives a map from the cover to `s'`, and that map is not injective for essentially distinct
   covers (two essentially distinct `ρb`-tubes may both contain the same much thinner `δt`-tube),
   so no comparison between the two cardinalities exists in the tree.

So the floor is an open row with a named owner elsewhere, not a hypothesis this run may help
itself to.  What the tree *does* prove about it is the **ceiling**:
`Kakeya.VeryNotSticky.exists_threshold_exponent_le_four`  says a family meeting the floor
at `ζ'` inside the unit ball forces `ζ' ≤ 4` below an explicit threshold.  Floor and ceiling meet
only in `ζ' ∈ (0, 4]`, which is §AD's band; nothing here reintroduces `ζ' > 4`.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Kakeya Kakeya.ML2Reduction
open scoped NNReal ENNReal

namespace Kakeya.ML2Core

universe u

theorem edCover_of_supplier_of_floor {b δt δ' : NNReal} {ϖ ζ' : ℝ} {N : NNReal → ℝ}
    {α : Type u} {s' : Finset α}
    (T₀ : Tube b (EuclideanSpace ℝ (Fin 3)))
    (𝕋 : α → ShadedTube δt (EuclideanSpace ℝ (Fin 3)))
    (hsup : ∀ ρ : NNReal, ρ ∈ Set.Icc
        (δ' ^ (1 - ϖ) / Kakeya.VeryNotSticky.edWindowContractionConstant) (δ' ^ ϖ) →
      ∃ (κ₀ : Type u) (t : Finset κ₀)
        (W : κ₀ → Tube (ρ * b) (EuclideanSpace ℝ (Fin 3))),
        ((t : Set κ₀).Pairwise
          fun j k ↦ _root_.IsEssentiallyDistinct (W j).carrier (W k).carrier) ∧
        (∀ k ∈ t, (W k).carrier ⊆ T₀.carrier) ∧
        (∀ k ∈ t, ∃ i ∈ s', (𝕋 i).carrier ⊆ (W k).carrier) ∧
        N ρ ≤ (t.card : ℝ))
    (hfloor : ∀ ρ : NNReal, ρ ∈ Set.Icc
        (δ' ^ (1 - ϖ) / Kakeya.VeryNotSticky.edWindowContractionConstant) (δ' ^ ϖ) →
      (ρ : ℝ) ^ (-2 - ζ') ≤ N ρ) :
    ∀ ρ : NNReal, ρ ∈ Set.Icc
        (δ' ^ (1 - ϖ) / Kakeya.VeryNotSticky.edWindowContractionConstant) (δ' ^ ϖ) →
      ∃ (κ₀ : Type u) (t : Finset κ₀)
        (W : κ₀ → Tube (ρ * b) (EuclideanSpace ℝ (Fin 3))),
        ((t : Set κ₀).Pairwise
          fun j k ↦ _root_.IsEssentiallyDistinct (W j).carrier (W k).carrier) ∧
        (∀ k ∈ t, (W k).carrier ⊆ T₀.carrier) ∧
        (∀ k ∈ t, ∃ i ∈ s', (𝕋 i).carrier ⊆ (W k).carrier) ∧
        (ρ : ℝ) ^ (-2 - ζ') ≤ (t.card : ℝ) := by
  intro ρ hρ
  obtain ⟨κ₀, t, W, hED, hsubW, hused, hcard⟩ := hsup ρ hρ
  exact ⟨κ₀, t, W, hED, hsubW, hused, le_trans (hfloor ρ hρ) hcard⟩

theorem hstep8_of_supplier_of_floor {b δt δ' : NNReal} {ϖ ζ' : ℝ} {N : NNReal → ℝ}
    {α : Type u} {s' : Finset α}
    (T₀ : Tube b (EuclideanSpace ℝ (Fin 3)))
    (𝕋 : α → ShadedTube δt (EuclideanSpace ℝ (Fin 3)))
    (hsup : ∀ ρ : NNReal, ρ ∈ Set.Icc
        (δ' ^ (1 - ϖ) / Kakeya.VeryNotSticky.edWindowContractionConstant) (δ' ^ ϖ) →
      ∃ (κ₀ : Type u) (t : Finset κ₀)
        (W : κ₀ → Tube (ρ * b) (EuclideanSpace ℝ (Fin 3))),
        ((t : Set κ₀).Pairwise
          fun j k ↦ _root_.IsEssentiallyDistinct (W j).carrier (W k).carrier) ∧
        (∀ k ∈ t, (W k).carrier ⊆ T₀.carrier) ∧
        (∀ k ∈ t, ∃ i ∈ s', (𝕋 i).carrier ⊆ (W k).carrier) ∧
        N ρ ≤ (t.card : ℝ))
    (hfloor : ∀ ρ : NNReal, ρ ∈ Set.Icc
        (δ' ^ (1 - ϖ) / Kakeya.VeryNotSticky.edWindowContractionConstant) (δ' ^ ϖ) →
      (ρ : ℝ) ^ (-2 - ζ') ≤ N ρ) :
    ∀ ρ : NNReal, ρ ∈ Set.Icc
        (δ' ^ (1 - ϖ) / Kakeya.VeryNotSticky.edWindowContractionConstant) (δ' ^ ϖ) →
      ∃ (κ₀ : Type u) (t₈ : Finset κ₀)
        (W : κ₀ → Tube (ρ * b) (EuclideanSpace ℝ (Fin 3))) (M : ℕ),
        (∀ k ∈ t₈, (W k).carrier ⊆ T₀.carrier) ∧
        (∀ k ∈ t₈, ∃ i ∈ s', (𝕋 i).carrier ⊆ (W k).carrier) ∧
        (∀ i ∈ t₈, (open scoped Classical in t₈.filter (fun j ↦
          ¬ _root_.IsEssentiallyDistinct (W j).carrier (W i).carrier)).card ≤ M) ∧
        (M : ℝ) ≤ (ρ : ℝ) ^ (-(0 : ℝ)) ∧
        (ρ : ℝ) ^ (-2 - ζ') ≤ (t₈.card : ℝ) := by
  intro ρ hρ
  obtain ⟨κ₀, t, W, hED, hsubW, hused, hcard⟩ :=
    edCover_of_supplier_of_floor (ζ' := ζ') T₀ 𝕋 hsup hfloor ρ hρ
  exact Kakeya.ML2Core.hstep8_of_essDistinct t W hED hsubW hused hcard


/-- **Site 4's row, separately.**  `Kakeya.ML2Core.middle_factor_of_lineEDNodes_sharp` asks for a
*line*-essentially-distinct family at level count `A`, not a pairwise essentially distinct one, so
it is its own row and not an instance of `edCover_of_supplier_of_floor`.  The split is the same:
a supplier with whatever count it has, and the floor on that count. -/
theorem lineEDCover_of_supplier_of_floor {b δt δ' : NNReal} {ϖ ζ' : ℝ} {N : NNReal → ℝ} {A : ℕ}
    {α : Type u} {s' : Finset α}
    (T₀ : Tube b (EuclideanSpace ℝ (Fin 3)))
    (𝕋 : α → ShadedTube δt (EuclideanSpace ℝ (Fin 3)))
    (hsup : ∀ ρ : NNReal, ρ ∈ Set.Icc
        (δ' ^ (1 - ϖ) / Kakeya.VeryNotSticky.edWindowContractionConstant) (δ' ^ ϖ) →
      ∃ (κ₀ : Type u) (t : Finset κ₀)
        (W : κ₀ → Tube (ρ * b) (EuclideanSpace ℝ (Fin 3))),
        Kakeya.VeryNotSticky.IsLineEssDistinctAt (Tube.tubeOverlapCoreClose.C 3) A t W ∧
        (∀ l ∈ t, (W l).carrier ⊆ T₀.carrier) ∧
        (∀ l ∈ t, ∃ i ∈ s', (𝕋 i).carrier ⊆ (W l).carrier) ∧
        N ρ ≤ (t.card : ℝ))
    (hfloor : ∀ ρ : NNReal, ρ ∈ Set.Icc
        (δ' ^ (1 - ϖ) / Kakeya.VeryNotSticky.edWindowContractionConstant) (δ' ^ ϖ) →
      (ρ : ℝ) ^ (-2 - ζ') ≤ N ρ) :
    ∀ ρ : NNReal, ρ ∈ Set.Icc
        (δ' ^ (1 - ϖ) / Kakeya.VeryNotSticky.edWindowContractionConstant) (δ' ^ ϖ) →
      ∃ (κ₀ : Type u) (t : Finset κ₀)
        (W : κ₀ → Tube (ρ * b) (EuclideanSpace ℝ (Fin 3))),
        Kakeya.VeryNotSticky.IsLineEssDistinctAt (Tube.tubeOverlapCoreClose.C 3) A t W ∧
        (∀ l ∈ t, (W l).carrier ⊆ T₀.carrier) ∧
        (∀ l ∈ t, ∃ i ∈ s', (𝕋 i).carrier ⊆ (W l).carrier) ∧
        (ρ : ℝ) ^ (-2 - ζ') ≤ (t.card : ℝ) := by
  intro ρ hρ
  obtain ⟨κ₀, t, W, hline, hsubW, hused, hcard⟩ := hsup ρ hρ
  exact ⟨κ₀, t, W, hline, hsubW, hused, le_trans (hfloor ρ hρ) hcard⟩


/-- **The supplier's three geometric rows carry no cardinality information at all** — the empty
cover satisfies every one of them, for any `T₀`, any family and any `ρ`.

This is the sharp form of the split: essential distinctness, containment in `T₀` and the all-used
row are *vacuous* on `∅`, so the floor `ρ^{-2-ζ'} ≤ #t` is not a consequence of the geometry the
supplier provides — it is an independent quantitative demand.  Any producer of the row must
therefore carry a cardinality source, and §"The floor is NOT supplied…" above measures that the
tree has none on the path from `Kakeya.ML2Assembly.Dichotomy` to the sites. -/
theorem edSupplier_rows_vacuous_at_empty {b δt ρ : NNReal} {α : Type u} (s' : Finset α)
    (T₀ : Tube b (EuclideanSpace ℝ (Fin 3)))
    (𝕋 : α → ShadedTube δt (EuclideanSpace ℝ (Fin 3)))
    (W : α → Tube (ρ * b) (EuclideanSpace ℝ (Fin 3))) :
    ((((∅ : Finset α) : Set α)).Pairwise
      fun j k ↦ _root_.IsEssentiallyDistinct (W j).carrier (W k).carrier) ∧
    (∀ k ∈ (∅ : Finset α), (W k).carrier ⊆ T₀.carrier) ∧
    (∀ k ∈ (∅ : Finset α), ∃ i ∈ s', (𝕋 i).carrier ⊆ (W k).carrier) ∧
    ((∅ : Finset α).card : ℝ) = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp


/-- **The only existing relation between the two objects points the wrong way.**

`Kakeya.ML2Squeeze.scaleCount_forces_band` (W-era `BandSqueeze.lean`) proves that the floor on the
**cover** forces a lower bound on the **family**: `ScaleCount ϖ ζ s T → δ⁻¹ ≤ C · #s`, through the
comparison `#tρ ≤ Tube.coverCountLoss 3 · #s`.  Its contrapositive
`Kakeya.ML2Squeeze.not_scaleCount_of_card_lt_delta_inv` says the floor is **false** below the band.

So the implication available in the tree is *cover ⟹ family*, and the direction a producer of
`hED` would need is *family ⟹ cover*.  The comparison lemma is an upper bound on `#tρ`, so a lower
bound on `#s` — including the large-family `δ^{-2} ≤ #𝕋` — yields nothing about `#tρ`.  This is the
precise form of the non-injectivity of the all-used map, and it is existing, not conjectured. -/
theorem scaleCount_direction_is_cover_to_family {ϖ ζ : ℝ} (hϖ : ϖ ≤ 1 / 2) (hζ : 0 ≤ ζ)
    {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {ι : Type u} (s : Finset ι)
    (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
    (hcount : Kakeya.ML2Squeeze.ScaleCount.{u} ϖ ζ s T) :
    ((δ : ℝ))⁻¹ ≤ (Tube.coverCountLoss 3 : ℝ) * (s.card : ℝ) :=
  Kakeya.ML2Squeeze.scaleCount_forces_band hϖ hζ hδ0 hδ1 s T hcount


/-- **On `Dichotomy`'s own domain, `ScaleCount` is invisible.**

`Kakeya.ML2Assembly.Dichotomy` binds `δ⁻¹ ≤ #s`.  The *only* consequence the tree draws from
`ScaleCount` is `Kakeya.ML2Squeeze.scaleCount_forces_band`'s `δ⁻¹ ≤ C · #s`, and that is already
free from `Dichotomy`'s own antecedent whenever `1 ≤ C` — as it is at
`C = Tube.coverCountLoss 3`.  So a producer of `Dichotomy` learns nothing from the very-not-sticky
condition, and cannot case-split on it: there is no `by_cases` on `ScaleCount` anywhere in the tree
(measured; the same scan sees the Cap band's own `by_cases hlarge : (L.scale)⁻¹ ≤ #s`).

The Cap band is therefore entered by a **different criterion** — the `δ^{-1}` cardinality band on
the family `s` (`Cap/CapLemma.lean:348, :410`) — and not by `ScaleCount`.  `GeometricCoreAt` is a
standalone producer of `Dichotomy` for *every* family in that band, with no very-not-sticky
hypothesis anywhere in its statement. -/
theorem scaleCount_band_free_on_dichotomy_domain {δ : NNReal} {C N : ℝ}
    (hC : 1 ≤ C) (hN : 0 ≤ N) (h : ((δ : ℝ))⁻¹ ≤ N) : ((δ : ℝ))⁻¹ ≤ C * N := by
  refine h.trans ?_
  nlinarith

/-- **`hnu` is not implied by what GWZ Lemma 9.1 delivers.**

The four nested sites bind `hL91` at the fixed exponent
`gain (spineRung β ϖ ε₁ gain dens (k+1) / 2) + 3 qc`, and `Lemma91At_mono_exp` reduces it to
`hnu : gain (…) + 3 qc ≤ ν`.  But `ν` comes from
`Kakeya.multiplicity_le_of_card_isEssDistinct_ge`'s existential, whose statement **does not mention
`gain`** — all it delivers is `0 < ν`.  Positivity is not enough: here is a parameter tuple meeting
every positivity row the sites carry, with `hnu` false.  So `hnu` needs a link between the
delivered `ν` and the site's `gain`, and no such link exists in the tree.

This is a *non-implication*, not a refutation of `hnu` at every instance: an instance that also
satisfies `Kakeya.ML2Assembly.Lemma91ParamsAt` may still meet it.  The missing input is named, not
guessed. -/
theorem hnu_not_implied_by_nu_pos :
    ∃ (β ϖ ε₁ qc ν : ℝ) (gain dens : ℝ → ℝ) (k : ℕ),
      0 < β ∧ β ≤ 1 ∧ 0 < ϖ ∧ 0 < ε₁ ∧ 0 < qc ∧ 0 < ν ∧
      (∀ ζ, 0 < ζ → 0 < gain ζ) ∧ (∀ ζ, 0 < ζ → 0 < dens ζ) ∧
      ¬ (gain (ML2Spine.spineRung β ϖ ε₁ gain dens (k + 1) / 2) + 3 * qc ≤ ν) := by
  refine ⟨1, 1, 1, 1, 1, fun _ => 2, fun _ => 1, 0, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num, fun _ _ => by norm_num, fun _ _ => by norm_num, ?_⟩
  norm_num

/-- The strict large-family floor implies the dichotomy's floor, and is strictly stronger. -/
theorem cardFloor_strict_le_dichotomy {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {c : ℝ}
    (h : (δ : ℝ) ^ (-2 : ℝ) ≤ c) : ((δ : ℝ))⁻¹ ≤ c := by
  refine le_trans ?_ h
  have h0 : (0:ℝ) < (δ : ℝ) := hδ0
  have h1 : (δ : ℝ) ≤ 1 := hδ1
  rw [show ((δ:ℝ))⁻¹ = (δ:ℝ) ^ (-1 : ℝ) by
    rw [Real.rpow_neg_one]]
  exact Real.rpow_le_rpow_of_exponent_ge h0 h1 (by norm_num)

/-- …and the converse fails: at `δ = 1/4` a family of `4` tubes clears the dichotomy's floor and
not the strict one.  So the two clauses are genuinely different hypotheses. -/
theorem not_cardFloor_dichotomy_le_strict :
    ¬ (∀ (δ : NNReal), 0 < δ → δ ≤ 1 → ∀ c : ℝ, ((δ : ℝ))⁻¹ ≤ c → (δ : ℝ) ^ (-2 : ℝ) ≤ c) := by
  intro h
  have hle1 : (1/4 : NNReal) ≤ 1 := by
    rw [← NNReal.coe_le_coe]; push_cast; norm_num
  have hc : (((1/4 : NNReal)) : ℝ) = (1/4 : ℝ) := by push_cast; norm_num
  have h4 : (((1/4 : NNReal)) : ℝ)⁻¹ ≤ 4 := by rw [hc]; norm_num
  have := h (1/4 : NNReal) (by rw [← NNReal.coe_lt_coe]; push_cast; norm_num) hle1 4 h4
  rw [hc, show (-2 : ℝ) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast] at this
  norm_num at this

/-! ## The source's covering bridge: shape, absorption, tie

 The floor has a producer after all — the source's
`lem:defect-covering-bridge` (l.4596–4617), which the GC route owes as VNS's *caller*.  Its
conclusion is **not** the sites' slot: the source concludes `θ · σ^{-2-2ζ} ≤ #𝕎`, with a `θ`
prefactor and exponent `2+2ζ`, while the site slot is the bare `σ^{-2-ζ} ≤ #t`.  The three
declarations below keep those apart, in the order source required: shape, then absorption
with its ordering explicit, then the tie.  The bridge's own five inputs are **not** proved here —
one of them is R0b, `w325gen`'s `goodMassSet` leaf, and is not mine. -/

/-- **The absorption, named and isolated**: the source's prefactor is absorbed into the site's
exponent exactly when `σ^ζ ≤ θ`.  This is the whole of the shape difference; nothing else in the
bridge's conclusion moves. -/
theorem floor_absorb_of_rpow_le {σ : NNReal} (hσ0 : 0 < σ) {ζ θ : ℝ}
    (hθ : (σ : ℝ) ^ ζ ≤ θ) :
    (σ : ℝ) ^ (-2 - ζ) ≤ θ * (σ : ℝ) ^ (-2 - 2 * ζ) := by
  have h0 : (0:ℝ) < (σ : ℝ) := hσ0
  have hpow : (0:ℝ) < (σ : ℝ) ^ (-2 - 2 * ζ) := Real.rpow_pos_of_pos h0 _
  calc (σ : ℝ) ^ (-2 - ζ)
      = (σ : ℝ) ^ ζ * (σ : ℝ) ^ (-2 - 2 * ζ) := by
        rw [← Real.rpow_add h0]; ring_nf
    _ ≤ θ * (σ : ℝ) ^ (-2 - 2 * ζ) := mul_le_mul_of_nonneg_right hθ hpow.le

/-- **The absorption is not free** — without the ordering `σ^ζ ≤ θ` it fails, at `σ = 1/2`,
`ζ = 1`, `θ = 1/4`.  So a tie that drops the prefactor is a real defect, not a notation change;
this is the control source asked for before any tie to the bare slot. -/
theorem not_floor_absorb_without_ordering :
    ¬ (∀ (σ : NNReal), 0 < σ → ∀ ζ θ : ℝ, 0 < θ →
        (σ : ℝ) ^ (-2 - ζ) ≤ θ * (σ : ℝ) ^ (-2 - 2 * ζ)) := by
  intro h
  have := h (1/2 : NNReal) (by rw [← NNReal.coe_lt_coe]; push_cast; norm_num) 1 (1/4) (by norm_num)
  rw [show (((1/2 : NNReal)) : ℝ) = (1/2 : ℝ) by push_cast; norm_num] at this
  rw [show (-2 - (1:ℝ)) = ((-3 : ℤ) : ℝ) by norm_num,
    show (-2 - 2 * (1:ℝ)) = ((-4 : ℤ) : ℝ) by norm_num,
    Real.rpow_intCast, Real.rpow_intCast] at this
  norm_num at this

/-- **The tie, at the source's shape.**  A supplier whose count row is the source's
`θ ρ · ρ^{-2-2ζ'} ≤ #t`, together with the ordering `ρ^{ζ'} ≤ θ ρ` on the window, fills the sites'
bare floor slot through `edCover_of_supplier_of_floor`.  The prefactor is carried, never dropped:
`hord` is a hypothesis of this theorem and `not_floor_absorb_without_ordering` shows it cannot be
omitted. -/
theorem edCover_of_sourceBridge {b δt δ' : NNReal} {ϖ ζ' : ℝ} {θ : NNReal → ℝ}
    {α : Type u} {s' : Finset α}
    (T₀ : Tube b (EuclideanSpace ℝ (Fin 3)))
    (𝕋 : α → ShadedTube δt (EuclideanSpace ℝ (Fin 3)))
    (hsup : ∀ ρ : NNReal, ρ ∈ Set.Icc
        (δ' ^ (1 - ϖ) / Kakeya.VeryNotSticky.edWindowContractionConstant) (δ' ^ ϖ) →
      ∃ (κ₀ : Type u) (t : Finset κ₀)
        (W : κ₀ → Tube (ρ * b) (EuclideanSpace ℝ (Fin 3))),
        ((t : Set κ₀).Pairwise
          fun j k ↦ _root_.IsEssentiallyDistinct (W j).carrier (W k).carrier) ∧
        (∀ k ∈ t, (W k).carrier ⊆ T₀.carrier) ∧
        (∀ k ∈ t, ∃ i ∈ s', (𝕋 i).carrier ⊆ (W k).carrier) ∧
        θ ρ * (ρ : ℝ) ^ (-2 - 2 * ζ') ≤ (t.card : ℝ))
    (hρ0 : ∀ ρ : NNReal, ρ ∈ Set.Icc
        (δ' ^ (1 - ϖ) / Kakeya.VeryNotSticky.edWindowContractionConstant) (δ' ^ ϖ) → 0 < ρ)
    (hord : ∀ ρ : NNReal, ρ ∈ Set.Icc
        (δ' ^ (1 - ϖ) / Kakeya.VeryNotSticky.edWindowContractionConstant) (δ' ^ ϖ) →
      (ρ : ℝ) ^ ζ' ≤ θ ρ) :
    ∀ ρ : NNReal, ρ ∈ Set.Icc
        (δ' ^ (1 - ϖ) / Kakeya.VeryNotSticky.edWindowContractionConstant) (δ' ^ ϖ) →
      ∃ (κ₀ : Type u) (t : Finset κ₀)
        (W : κ₀ → Tube (ρ * b) (EuclideanSpace ℝ (Fin 3))),
        ((t : Set κ₀).Pairwise
          fun j k ↦ _root_.IsEssentiallyDistinct (W j).carrier (W k).carrier) ∧
        (∀ k ∈ t, (W k).carrier ⊆ T₀.carrier) ∧
        (∀ k ∈ t, ∃ i ∈ s', (𝕋 i).carrier ⊆ (W k).carrier) ∧
        (ρ : ℝ) ^ (-2 - ζ') ≤ (t.card : ℝ) :=
  edCover_of_supplier_of_floor (N := fun ρ ↦ θ ρ * (ρ : ℝ) ^ (-2 - 2 * ζ')) T₀ 𝕋 hsup
    (fun ρ hρ ↦ floor_absorb_of_rpow_le (hρ0 ρ hρ) (hord ρ hρ))

/-- **`gain` IS Lemma 9.1's delivered `ν`, and that is what inverts at `hnu`.**

`Kakeya.ML2Assembly.Lemma91ParamsAt.body` is `∀ ζ > 0, VNSBody β ϖ ζ (gain ζ) (dens ζ)`, and
`Kakeya.ML2Assembly.VNSBody`'s fourth argument is the multiplicity exponent `ν`
(`Reduction/Assembly.lean:78`).  So at tolerance `ζ` Lemma 9.1 delivers `ν = gain ζ` — the site's
own `gain`, not an unrelated exponent.  Read at the tolerance the sites' `hL91` expression names,
`hnu` is therefore `gain x + 3 qc ≤ gain x`, which is false for every positive `qc`.  The inversion
is not between `ν` and `gain`; it is that the sites demand `3 qc` of headroom at the **same**
tolerance where Lemma 9.1 has already spent it. -/
theorem hnu_false_at_matched_tolerance (g : ℝ → ℝ) (x qc : ℝ) (hqc : 0 < qc) :
    ¬ (g x + 3 * qc ≤ g x) := by intro h; linarith


end Kakeya.ML2Core


/-! ## The two ties: the split fills the sites' slots by name -/

section Ties

variable {b δt δ' : NNReal} {R : ℝ}
  {hsit : Tube.IsRescalingSituation b δt δ' R 3} {hR : 0 < R}
  {T₀ : Tube b (EuclideanSpace ℝ (Fin 3))}
  {A : Type u} {s s' : Finset A} {qc ϖ ζ ηd β ζ' ν cst : ℝ} {N : NNReal → ℝ}
  {𝕋 : A → ShadedTube δt (EuclideanSpace ℝ (Fin 3))}
  {U' : A → ShadedTube δ' (EuclideanSpace ℝ (Fin 3))}

-- TIE A : the split fills `hstep8` at `Kakeya.ML2Core.fine_factor_of_lemma91At_of_step8`, m := 0
example
    (hsup : ∀ ρ : NNReal, ρ ∈ Set.Icc
        (δ' ^ (1 - ϖ) / Kakeya.VeryNotSticky.edWindowContractionConstant) (δ' ^ ϖ) →
      ∃ (κ₀ : Type u) (t : Finset κ₀)
        (W : κ₀ → Tube (ρ * b) (EuclideanSpace ℝ (Fin 3))),
        ((t : Set κ₀).Pairwise
          fun j k ↦ _root_.IsEssentiallyDistinct (W j).carrier (W k).carrier) ∧
        (∀ k ∈ t, (W k).carrier ⊆ T₀.carrier) ∧
        (∀ k ∈ t, ∃ i ∈ s', (𝕋 i).carrier ⊆ (W k).carrier) ∧
        N ρ ≤ (t.card : ℝ))
    (hfloor : ∀ ρ : NNReal, ρ ∈ Set.Icc
        (δ' ^ (1 - ϖ) / Kakeya.VeryNotSticky.edWindowContractionConstant) (δ' ^ ϖ) →
      (ρ : ℝ) ^ (-2 - ζ') ≤ N ρ) : True := by
  have _tie := Kakeya.ML2Core.fine_factor_of_lemma91At_of_step8
    (mm := 0) (β := β) (ζ' := ζ') (m := 0) (ν := ν) (cst := cst) (s := s) (s' := s')
    (qc := qc) (ηd := ηd) (ζ := ζ) (ϖ := ϖ)
    (𝕋 := 𝕋) (U' := U') (T₀ := T₀) (hsit := hsit) (hR := hR)
    (hstep8 := Kakeya.ML2Core.hstep8_of_supplier_of_floor (ζ' := ζ') T₀ 𝕋 hsup hfloor)
  trivial

-- TIE B : the split fills `hED` at `Kakeya.ML2Core.fine_factor_of_lemma91At_of_edCover`
example
    (hsup : ∀ ρ : NNReal, ρ ∈ Set.Icc
        (δ' ^ (1 - ϖ) / Kakeya.VeryNotSticky.edWindowContractionConstant) (δ' ^ ϖ) →
      ∃ (κ₀ : Type u) (t : Finset κ₀)
        (W : κ₀ → Tube (ρ * b) (EuclideanSpace ℝ (Fin 3))),
        ((t : Set κ₀).Pairwise
          fun j k ↦ _root_.IsEssentiallyDistinct (W j).carrier (W k).carrier) ∧
        (∀ k ∈ t, (W k).carrier ⊆ T₀.carrier) ∧
        (∀ k ∈ t, ∃ i ∈ s', (𝕋 i).carrier ⊆ (W k).carrier) ∧
        N ρ ≤ (t.card : ℝ))
    (hfloor : ∀ ρ : NNReal, ρ ∈ Set.Icc
        (δ' ^ (1 - ϖ) / Kakeya.VeryNotSticky.edWindowContractionConstant) (δ' ^ ϖ) →
      (ρ : ℝ) ^ (-2 - ζ') ≤ N ρ) : True := by
  have _tie := Kakeya.ML2Core.fine_factor_of_lemma91At_of_edCover
    (mm := 0) (β := β) (ζ' := ζ') (ν := ν) (cst := cst) (s := s) (s' := s')
    (qc := qc) (ηd := ηd) (ζ := ζ) (ϖ := ϖ)
    (𝕋 := 𝕋) (U' := U') (T₀ := T₀) (hsit := hsit) (hR := hR)
    (hED := Kakeya.ML2Core.edCover_of_supplier_of_floor (ζ' := ζ') T₀ 𝕋 hsup hfloor)
  trivial

set_option maxHeartbeats 1600000 in
-- TIE C : the line-ED split fills `hEDline` at `Kakeya.ML2Core.middle_factor_of_lineEDNodes_sharp`
example {ε₁ w ηc : ℝ} {gain dens : ℝ → ℝ} {kk : ℕ} {δ θ τ : NNReal} {Rout : ℝ} {Alev : ℕ}
    {hsitOut : Tube.IsRescalingSituation θ τ δt Rout 3} {hRout : 0 < Rout}
    {Tθ : Tube θ (EuclideanSpace ℝ (Fin 3))} {Y : A → ShadedTube τ (EuclideanSpace ℝ (Fin 3))}
    {κc : Type u} {t' : Finset κc} {Zρ : κc → ShadedTube b (EuclideanSpace ℝ (Fin 3))}
    {Lc Cf Cu : ENNReal} {Nm : ℕ} {kap : ℝ}
    (hsup : ∀ ρ : NNReal, ρ ∈ Set.Icc
        (δ' ^ (1 - ϖ) / Kakeya.VeryNotSticky.edWindowContractionConstant) (δ' ^ ϖ) →
      ∃ (κ₀ : Type u) (t : Finset κ₀)
        (W : κ₀ → Tube (ρ * b) (EuclideanSpace ℝ (Fin 3))),
        Kakeya.VeryNotSticky.IsLineEssDistinctAt (Tube.tubeOverlapCoreClose.C 3) Alev t W ∧
        (∀ l ∈ t, (W l).carrier ⊆ T₀.carrier) ∧
        (∀ l ∈ t, ∃ i ∈ s',
          (Kakeya.ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y i).carrier
            ⊆ (W l).carrier) ∧
        N ρ ≤ (t.card : ℝ))
    (hfloor : ∀ ρ : NNReal, ρ ∈ Set.Icc
        (δ' ^ (1 - ϖ) / Kakeya.VeryNotSticky.edWindowContractionConstant) (δ' ^ ϖ) →
      (ρ : ℝ) ^ (-2 - ζ') ≤ N ρ) : True := by
  have _tie := Kakeya.ML2Core.middle_factor_of_lineEDNodes_sharp
    (mm := 0) (hsitOut := hsitOut) (β := β) (ε₁ := ε₁) (gain := gain) (dens := dens) (k := kk)
    (δ := δ) (w := w) (κc := κc) (t' := t') (Zρ := Zρ) (ηc := ηc) (A := Alev)
    (cst := cst) (ζ := ζ) (ζ' := ζ') (ϖ := ϖ) (ηd := ηd) (qc := qc)
    (L := Lc) (Cf := Cf) (Cu := Cu) (Nm := Nm) (κ := kap) (s' := s') (U' := U') (T₀ := T₀)
    (fib := s)
    (hsit := hsit) (hR := hR)
    (hEDline := Kakeya.ML2Core.lineEDCover_of_supplier_of_floor (ζ' := ζ') T₀
      (Kakeya.ML2Reduction.outerFamily hsitOut.pos_ambient Tθ hRout δt Y) hsup hfloor)
  trivial

end Ties

end
