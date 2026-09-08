/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Tube.Dilate
public import Kakeya.Tube.Rescale

/-!
# Comparing two `ρ`-tube covers of one family of bodies

GWZ writes `|𝕋_ρ|` for "the number of `ρ`-tubes needed to cover `𝕋`", a quantity well defined only
*up to constants*.  The Lean rendering of the count clause of GWZ Lemma 9.1
(`Kakeya.ML2Reduction.Lemma91At`, third bullet) takes it literally and asks for the lower bound
`ρ^{-2-ζ} ≤ |t'|` for **every** essentially distinct `ρ`-tube cover `t'`, whereas
`Kakeya.ML2Spine.spine_tube_card_lower` proves it for the *canonical* cover carried by the tube
hierarchy.  The bridge is the comparison of two covers at the same scale, which this file supplies.

## The residual input, and its repair

`Kakeya.ML2Reduction.CoverCountComparable` (w08's `Reduction/SpineOuterTubes.lean`) is the exact
shape of the missing input.  It is restated here verbatim as `Tube.CoverCountComparableSpec` — and
it is **false at every loss `Λ`** (`Tube.not_coverCountComparableSpec`): nothing in it forbids the
covered bodies `V i` from being *points*, and `n` pairwise disjoint `ρ`-tubes may all meet one
`ρ`-tube of the competitor cover in `n` distinct points.  So the covered bodies need a
nondegeneracy hypothesis, and it is the only thing they need:

`Tube.CoverCountComparableChord` is `Tube.CoverCountComparableSpec` with **three** hypotheses
added — `0 < ρ`, `ρ ≤ 1`, and `hnd`: every `V i` contains two points at distance `≥ 2/5`.
`Tube.coverCountComparableChord_of_spec` is the compiler-checked record that this is a *weakening*
and not a different statement, `Tube.coverCountComparableChord` proves it at the explicit loss
`Λ = 1 + Tube.essDistinctTubesInSelfDilate.C 3 32`, and
`Tube.one_le_of_coverCountComparableChord` certifies that the repaired predicate is **not
vacuous** (its hypotheses are satisfiable with a nonempty reference cover, whence `1 ≤ Λ`).

`hnd` is free at the call site: the bodies of Lemma 9.1's count clause are shaded `δ`-tubes, whose
cores have length exactly `1` (`Tube.exists_chord_of_shadedTube`).  The threshold `2/5` is not
arbitrary: it is where the chord-angle bound of `Tube.norm_perp_direction_le_of_chord` meets the
`15 K ρ` that `Tube.subset_dilate_of_norm_perp_direction_le` demands, at `K = 1`.

## The geometry, and where it already lived

The "one missing geometric lemma" — *two coarse tubes sharing a fine tube are comparable* — is
`Tube.subset_dilate_of_common_chord`, and it is a two-line composition of lemmas that were already
in the tree.  `Tube.tubeOverlapCoreClose` is indeed not applicable (it needs overlap `> |T|/2`),
but it is not needed:

* `Tube.norm_perp_direction_le_of_chord` (`Kakeya/Tube/Dilate.lean`, blueprint
  `lem:chordAngleBound`) turns a *shared chord of length `d`* into the direction bound
  `(2ρ + 4δ)/d`.  At `δ = ρ` and `d = 2/5` this is exactly `15 ρ`.
* `Tube.subset_dilate_of_norm_perp_direction_le` (blueprint `lem:thinTubeInFatDilate`) turns that
  direction bound, plus one shared point, into `W ⊆ 32 · W'`.
* `Tube.essDistinctTubesInSelfDilate` (`Kakeya/Tube/Rescale.lean`, blueprint
  `lem:essDistinctTubesInSelfDilate`) then bounds each fibre of `j ↦ j'`.  **Its docstrings in
  `Kakeya/Tube/Rescale.lean` still call it "the single open leaf"; that is stale.  It is proved,
  and `#print axioms` on it returns `[propext, Classical.choice, Quot.sound]`.**

The fibre map is `j ↦ j'` where `j' ∈ t'` is any competitor tube containing the body that
witnesses `j`'s being used; `Finset.card_eq_sum_card_fiberwise` assembles the fibres.  Note that
the *reference-cover* hypothesis `href` is never used: `Tube.card_le_mul_card_of_chordCover` needs
only `hED`, `hused` and `hcov`.

## The chord length is a parameter

The comparison runs at any chord threshold `2/(5K)` with `K ≥ 1`, at the dilation ratio `32 K` and
the loss `Tube.coverCountLossAt n K`; `K = 1` is the `2/5` case.  This is not decoration: the
*weaker* form of the count clause, the one
`Kakeya.ML2Reduction.outerFamily_count_of_spineFamily_count` reduces to, is stated on the
**rescaled bodies**, whose diameter is `≈ 1/(4R) = 1/256` rather than `1`.
`Tube.count_of_canonicalCover_of_diam` takes the diameter `d > 0` directly and picks
`K = max 1 (2/(5d))`.

## Main declarations

* `Tube.subset_dilate_of_common_chord_at` / `Tube.subset_dilate_of_common_chord` — two `ρ`-tubes
  sharing a chord of length `≥ 2/(5K)` satisfy `W ⊆ 32 K · W'`; and its `K = 1` case.
* `Tube.card_fibre_le` — the fibre bound.
* `Tube.card_le_mul_card_of_chordCover` — `|t| ≤ Λ |t'|`, the general-`E` theorem.
* `Tube.card_used_le_mul_card_of_chordCover` — the same with the `hused` hypothesis removed,
  bounding the *used* part of the reference cover.
* `Tube.CoverCountComparableSpec`, `Tube.exists_pointBody_cover_config`,
  `Tube.not_coverCountComparableSpec` — the literal statement, the counterexample configuration and
  the refutation.
* `Tube.CoverCountComparableChord`, `Tube.coverCountComparableChord`,
  `Tube.coverCountComparableChord_of_spec`, `Tube.one_le_of_coverCountComparableChord` — the
  repaired statement, its proof, the record that it is a weakening, and its non-vacuity.
* `Tube.count_of_coverCountComparableChord` — the analogue of
  `Kakeya.ML2Reduction.count_of_coverCountComparable`.
* `Tube.count_of_canonicalCover`, `Tube.count_of_canonicalCover_of_diam`,
  `Tube.count_of_canonicalCover_tube`, `Tube.count_of_canonicalCover_shadedTube` — the same
  conclusion with no abstract `Prop` in the way; the last two are the forms the count clause should
  cite.
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped NNReal ENNReal

namespace Tube

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ### Step 1 — two `ρ`-tubes sharing a chord are comparable -/

/-- **Two `ρ`-tubes sharing a chord are comparable**: if two points at distance at least `2/(5K)`
lie in both `W` and `W'`, then `W ⊆ 32 K · W'`.

This is the geometric input the count clause needed.  `Tube.tubeOverlapCoreClose` does **not**
apply — it requires an overlap of more than half the volume of a tube, and a shared body of
thickness `τ ≪ ρ` gives only `≈ τ² ρ`.  What replaces it is the pair
`Tube.norm_perp_direction_le_of_chord` (the chord pins the *direction*, at `(2ρ + 4ρ)/(2/5) = 15ρ`)
and `Tube.subset_dilate_of_norm_perp_direction_le` at `K = 1` (a pinned direction plus one shared
point pins the *tube*, inside the `32 K`-dilate).  The threshold `2/(5K)` is exactly the `d` at
which the first lemma's output `6ρ/d` meets the second lemma's `15 K ρ` hypothesis; anything larger
also works, and the tube call sites have `d = 1`, i.e. `K = 1`. -/
theorem subset_dilate_of_common_chord_at [Nontrivial E] {ρ : NNReal} (hρ1 : (ρ : ℝ) ≤ 1)
    {K : ℝ} (hK : 1 ≤ K) (W W' : Tube ρ E) {p q : E}
    (hpW : p ∈ W.carrier) (hqW : q ∈ W.carrier)
    (hpW' : p ∈ W'.carrier) (hqW' : q ∈ W'.carrier)
    (hpq : 2 / (5 * K) ≤ dist p q) :
    W.carrier ⊆ (Kakeya.Tube.dilate W' (32 * K)).carrier := by
  have hK0 : (0 : ℝ) < K := lt_of_lt_of_le zero_lt_one hK
  have hd0 : (0 : ℝ) < 2 / (5 * K) := by positivity
  have hρ0 : (0 : ℝ) ≤ (ρ : ℝ) := NNReal.coe_nonneg ρ
  have hpb : p ∈ (Kakeya.Tube.dilate W 2).carrier := subset_dilate W (by norm_num) hpW
  have hqb : q ∈ (Kakeya.Tube.dilate W 2).carrier := subset_dilate W (by norm_num) hqW
  have hchord := norm_perp_direction_le_of_chord W' W (d := 2 / (5 * K)) hd0 hpq
    hpW' hqW' hpb hqb
  have hS : ‖W.direction - inner ℝ W'.direction W.direction • W'.direction‖
      ≤ 15 * K * (ρ : ℝ) := by
    refine hchord.trans ?_
    rw [div_le_iff₀ hd0]
    have : 15 * K * (ρ : ℝ) * (2 / (5 * K)) = 6 * (ρ : ℝ) := by
      field_simp
      ring
    rw [this]
    linarith
  exact subset_dilate_of_norm_perp_direction_le W' W (K := K) hK hρ1
    (by nlinarith) hpW' hpb hS

/-- `Tube.subset_dilate_of_common_chord_at` at `K = 1`: a chord of length `≥ 2/5` gives
`W ⊆ 32 · W'`.  This is the form the call sites of Lemma 9.1's count clause use, their bodies
being tubes of core length `1`. -/
theorem subset_dilate_of_common_chord [Nontrivial E] {ρ : NNReal} (hρ1 : (ρ : ℝ) ≤ 1)
    (W W' : Tube ρ E) {p q : E}
    (hpW : p ∈ W.carrier) (hqW : q ∈ W.carrier)
    (hpW' : p ∈ W'.carrier) (hqW' : q ∈ W'.carrier)
    (hpq : (2 / 5 : ℝ) ≤ dist p q) :
    W.carrier ⊆ (Kakeya.Tube.dilate W' 32).carrier := by
  have h := subset_dilate_of_common_chord_at hρ1 (K := 1) le_rfl W W' hpW hqW hpW' hqW'
    (by norm_num at hpq ⊢; linarith)
  simpa using h

/-! ### Step 2 — the fibre bound -/

/-- The comparability loss of `Tube.card_le_mul_card_of_chordCover`: the packing constant of
`Tube.essDistinctTubesInSelfDilate` read at the dilation ratio `32 K` produced by
`Tube.subset_dilate_of_common_chord_at`, padded by `1` so that `1 ≤ Λ` is free.  It depends only
on the ambient dimension and on `K`: not on the scale, not on the tubes, not on the family. -/
noncomputable abbrev coverCountLossAt (n : ℕ) (K : ℝ) : NNReal :=
  1 + Tube.essDistinctTubesInSelfDilate.C n (32 * K)

/-- The comparability loss at chord threshold `2/5`, i.e. `Tube.coverCountLossAt n 1`. -/
noncomputable abbrev coverCountLoss (n : ℕ) : NNReal := coverCountLossAt n 1

/-- The `1 +` in `Tube.coverCountLoss` makes `1 ≤ Λ` free.  This is not cosmetic: the consumer
divides by `Λ`, and `Tube.essDistinctTubesInSelfDilate.C` carries no positivity lemma of its own.
`Tube.one_le_of_coverCountComparableChord` shows `1 ≤ Λ` is in any case necessary. -/
theorem one_le_coverCountLossAt (n : ℕ) (K : ℝ) : (1 : NNReal) ≤ coverCountLossAt n K :=
  le_self_add

/-- `Tube.one_le_coverCountLossAt` over `ℝ`. -/
theorem one_le_coverCountLossAt_real (n : ℕ) (K : ℝ) : (1 : ℝ) ≤ (coverCountLossAt n K : ℝ) := by
  exact_mod_cast one_le_coverCountLossAt n K

/-- **The fibre bound.**  A family of pairwise essentially distinct `ρ`-tubes all contained in the
`32`-dilate of one `ρ`-tube has at most `Tube.coverCountLoss (finrank ℝ E)` members.  This is
`Tube.essDistinctTubesInSelfDilate` at ratio `32`, converted from `ENNReal` to `ℝ`.

Note the scales agree: the counted tubes and the containing tube are both at scale `ρ`, which is
why `Tube.essDistinctTubesInDilate` (thin tubes `C⁻¹ρ` in a dilate of a `ρ`-tube) is *not* the
lemma to cite here. -/
theorem card_fibre_le [Nontrivial E] {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    {K : ℝ} (hK : 1 ≤ K) {κ : Type*} (a : Finset κ) (W : κ → Tube ρ E) (W' : Tube ρ E)
    (hED : (↑a : Set κ).Pairwise fun j k => IsEssentiallyDistinct (W j).carrier (W k).carrier)
    (hsub : ∀ j ∈ a, (W j).carrier ⊆ (Kakeya.Tube.dilate W' (32 * K)).carrier) :
    (a.card : ℝ) ≤ (coverCountLossAt (Module.finrank ℝ E) K : ℝ) := by
  have h := Tube.essDistinctTubesInSelfDilate (E := E) (ι := κ) (δ := ρ) (c := 32 * K)
    (by nlinarith) hρ0 hρ1 W' a W hED hsub
  have hcast : ((a.card : NNReal) : ENNReal)
      ≤ ((Tube.essDistinctTubesInSelfDilate.C (Module.finrank ℝ E) (32 * K) : NNReal)
          : ENNReal) := by
    simpa using h
  have h2 : (a.card : ℝ)
      ≤ ((Tube.essDistinctTubesInSelfDilate.C (Module.finrank ℝ E) (32 * K) : NNReal) : ℝ) := by
    exact_mod_cast ENNReal.coe_le_coe.mp hcast
  refine h2.trans ?_
  have hle : (Tube.essDistinctTubesInSelfDilate.C (Module.finrank ℝ E) (32 * K) : NNReal)
      ≤ coverCountLossAt (Module.finrank ℝ E) K := le_add_self
  exact_mod_cast hle

/-! ### Step 3 — the cover comparison -/

/-- **Two `ρ`-tube covers of the same family are comparable in cardinality**, at a loss depending
only on the ambient dimension.

`t` is the reference cover: pairwise essentially distinct, and every member *used* (it contains
some `V i` with `i ∈ s`).  `t'` is an arbitrary competitor cover.  Each used `W j` contains a body
`V i` which the competitor puts inside some `W' j'`; the two `ρ`-tubes then share a chord of length
`≥ 2/5`, so `W j ⊆ 32 · W' j'` (`Tube.subset_dilate_of_common_chord`), and the fibres of
`j ↦ j'` are bounded by `Tube.card_fibre_le`.

The loss is the closed term `Tube.coverCountLoss (Module.finrank ℝ E)`: it is fixed **before** `ρ`,
`V`, `s`, `t`, `W`, `t'`, `W'`, so it is uniform in all of them.  The hypothesis that `t` *covers*
the family is not needed — only `hED`, `hused` and `hcov`. -/
theorem card_le_mul_card_of_chordCover [Nontrivial E] {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    {K : ℝ} (hK : 1 ≤ K)
    {α κ κ' : Type*} (V : α → ConvexSpaceBody E) (s : Finset α)
    (t : Finset κ) (W : κ → Tube ρ E) (t' : Finset κ') (W' : κ' → Tube ρ E)
    (hnd : ∀ i ∈ s, ∃ p ∈ (V i).carrier, ∃ q ∈ (V i).carrier, 2 / (5 * K) ≤ dist p q)
    (hED : (↑t : Set κ).Pairwise fun j k => IsEssentiallyDistinct (W j).carrier (W k).carrier)
    (hused : ∀ j ∈ t, ∃ i ∈ s, V i ≤ (W j).toConvexSpaceBody)
    (hcov : ∀ i ∈ s, ∃ j ∈ t', V i ≤ (W' j).toConvexSpaceBody) :
    (t.card : ℝ) ≤ (coverCountLossAt (Module.finrank ℝ E) K : ℝ) * (t'.card : ℝ) := by
  classical
  have hρ1' : (ρ : ℝ) ≤ 1 := by exact_mod_cast hρ1
  have key : ∀ j ∈ t,
      ∃ j' ∈ t', (W j).carrier ⊆ (Kakeya.Tube.dilate (W' j') (32 * K)).carrier := by
    intro j hj
    obtain ⟨i, hi, hle⟩ := hused j hj
    obtain ⟨j', hj', hle'⟩ := hcov i hi
    obtain ⟨p, hp, q, hq, hpq⟩ := hnd i hi
    exact ⟨j', hj', subset_dilate_of_common_chord_at hρ1' hK (W j) (W' j')
      (hle hp) (hle hq) (hle' hp) (hle' hq) hpq⟩
  rcases t.eq_empty_or_nonempty with rfl | ⟨j₀, hj₀⟩
  · rw [Finset.card_empty, Nat.cast_zero]
    positivity
  obtain ⟨j₀', hj₀', -⟩ := key j₀ hj₀
  haveI : Nonempty κ' := ⟨j₀'⟩
  choose! f hf hfsub using key
  have hfibre : ∀ j' ∈ t', ((t.filter fun j => f j = j').card : ℝ)
      ≤ (coverCountLossAt (Module.finrank ℝ E) K : ℝ) := by
    intro j' _
    refine card_fibre_le hρ0 hρ1 hK _ W (W' j') ?_ ?_
    · exact hED.mono (by exact_mod_cast Finset.filter_subset _ _)
    · intro j hj
      rw [Finset.mem_filter] at hj
      exact hj.2 ▸ hfsub j hj.1
  calc (t.card : ℝ) = ((∑ j' ∈ t', (t.filter fun j => f j = j').card : ℕ) : ℝ) := by
        rw [← Finset.card_eq_sum_card_fiberwise hf]
    _ = ∑ j' ∈ t', ((t.filter fun j => f j = j').card : ℝ) := by push_cast; ring
    _ ≤ ∑ _j' ∈ t', (coverCountLossAt (Module.finrank ℝ E) K : ℝ) := Finset.sum_le_sum hfibre
    _ = (coverCountLossAt (Module.finrank ℝ E) K : ℝ) * (t'.card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- **`hused` removed.**  Only the *used* part of the reference cover can be bounded — an unused
`ρ`-tube of `t` is constrained by nothing at all — and this is that statement, with no hypothesis
on `t` beyond essential distinctness.

This is the form an assembler should prefer: it replaces the obligation "every member of the
canonical cover is used" by the obligation "the canonical lower bound holds for the used
sub-cover", which is what the geometry can actually deliver.
`Tube.card_le_mul_card_of_chordCover` is the special case where the filter is all of `t`. -/
theorem card_used_le_mul_card_of_chordCover [Nontrivial E] {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    {K : ℝ} (hK : 1 ≤ K)
    {α κ κ' : Type*} (V : α → ConvexSpaceBody E) (s : Finset α)
    (t : Finset κ) (W : κ → Tube ρ E) (t' : Finset κ') (W' : κ' → Tube ρ E)
    (hnd : ∀ i ∈ s, ∃ p ∈ (V i).carrier, ∃ q ∈ (V i).carrier, 2 / (5 * K) ≤ dist p q)
    (hED : (↑t : Set κ).Pairwise fun j k => IsEssentiallyDistinct (W j).carrier (W k).carrier)
    (hcov : ∀ i ∈ s, ∃ j ∈ t', V i ≤ (W' j).toConvexSpaceBody) :
    (((t.filter fun j => ∃ i ∈ s, V i ≤ (W j).toConvexSpaceBody)).card : ℝ)
      ≤ (coverCountLossAt (Module.finrank ℝ E) K : ℝ) * (t'.card : ℝ) := by
  classical
  refine card_le_mul_card_of_chordCover hρ0 hρ1 hK V s _ W t' W' hnd
    (hED.mono (by exact_mod_cast Finset.filter_subset _ _)) ?_ hcov
  intro j hj
  exact (Finset.mem_filter.mp hj).2

/-! ### The literal statement, restated -/

universe u

/-- **The literal statement of `Kakeya.ML2Reduction.CoverCountComparable`**, restated here
verbatim so that it can be refuted (house pattern). -/
def CoverCountComparableSpec (Λ : ℝ) : Prop :=
  ∀ {α κ κ' : Type u} {ρ : NNReal} (V : α → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
    (s : Finset α) (t : Finset κ) (W : κ → Tube ρ (EuclideanSpace ℝ (Fin 3)))
    (t' : Finset κ') (W' : κ' → Tube ρ (EuclideanSpace ℝ (Fin 3))),
    (∀ i ∈ s, ∃ j ∈ t, V i ≤ (W j).toConvexSpaceBody) →
    (t : Set κ).Pairwise
      (fun j k ↦ _root_.IsEssentiallyDistinct (W j).carrier (W k).carrier) →
    (∀ j ∈ t, ∃ i ∈ s, V i ≤ (W j).toConvexSpaceBody) →
    (∀ i ∈ s, ∃ j ∈ t', V i ≤ (W' j).toConvexSpaceBody) →
    (t.card : ℝ) ≤ Λ * (t'.card : ℝ)

/-! ### The counterexample construction -/

section Cross

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [ProperSpace F]

/-- The `ρ`-tube whose core runs from `a • u` in the direction `v`. -/
noncomputable def crossTube (ρ : NNReal) (u v : F) (hv : ‖v‖ = 1) (a : ℝ) : Tube ρ F :=
  Tube.mk' ρ (x := a • u) (y := a • u + v)
    (by rw [dist_eq_norm, show a • u - (a • u + v) = -v from by module, norm_neg, hv])

/-- The `u`-coordinate of every point of `crossTube ρ u v hv a` is within `ρ` of `a`. -/
theorem abs_inner_sub_le_of_mem_crossTube {ρ : NNReal} {u v : F} (hu : ‖u‖ = 1)
    (hv : ‖v‖ = 1) (huv : inner ℝ u v = (0 : ℝ)) (a : ℝ) {x : F}
    (hx : x ∈ (crossTube ρ u v hv a).carrier) :
    |inner ℝ u x - a| ≤ (ρ : ℝ) := by
  rw [crossTube, Tube.mk'_carrier, Set.mem_iUnion₂] at hx
  obtain ⟨z, hz, hxz⟩ := hx
  rw [Metric.mem_closedBall] at hxz
  rw [segment_eq_image' ℝ] at hz
  obtain ⟨θ, _, hzθ⟩ := hz
  have hzu : inner ℝ u z = a := by
    rw [← hzθ]
    have : a • u + v - a • u = v := by module
    rw [inner_add_right, this, real_inner_smul_right, real_inner_smul_right, huv,
      real_inner_self_eq_norm_sq, hu]
    ring
  have h1 : inner ℝ u x - a = inner ℝ u (x - z) := by
    rw [inner_sub_right, hzu]
  rw [h1]
  calc |inner ℝ u (x - z)| ≤ ‖u‖ * ‖x - z‖ := abs_real_inner_le_norm u (x - z)
    _ = dist x z := by rw [hu, one_mul, dist_eq_norm]
    _ ≤ (ρ : ℝ) := hxz

/-- Two cross tubes whose parameters differ by more than `2 ρ` are disjoint. -/
theorem crossTube_disjoint {ρ : NNReal} {u v : F} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huv : inner ℝ u v = (0 : ℝ)) {a b : ℝ} (hab : 2 * (ρ : ℝ) < |a - b|) :
    (crossTube ρ u v hv a).carrier ∩ (crossTube ρ u v hv b).carrier = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro x ⟨hxa, hxb⟩
  have ha := abs_inner_sub_le_of_mem_crossTube hu hv huv a hxa
  have hb := abs_inner_sub_le_of_mem_crossTube hu hv huv b hxb
  have : |a - b| ≤ 2 * (ρ : ℝ) := by
    have h := abs_sub_abs_le_abs_sub (inner ℝ u x - b) (inner ℝ u x - a)
    have h2 : |(inner ℝ u x - b) - (inner ℝ u x - a)| = |a - b| := by
      rw [show (inner ℝ u x - b) - (inner ℝ u x - a) = a - b from by ring]
    calc |a - b| = |(inner ℝ u x - a) - (inner ℝ u x - b)| := by
          rw [show (inner ℝ u x - a) - (inner ℝ u x - b) = b - a from by ring, abs_sub_comm]
      _ ≤ |inner ℝ u x - a| + |inner ℝ u x - b| := abs_sub _ _
      _ ≤ 2 * (ρ : ℝ) := by linarith
  linarith

end Cross

/-- Disjoint sets are essentially distinct. -/
theorem isEssentiallyDistinct_of_inter_eq_empty {X : Type*} [MeasureSpace X] {A B : Set X}
    (h : A ∩ B = ∅) : _root_.IsEssentiallyDistinct A B := by
  rw [_root_.IsEssentiallyDistinct, h]
  simp

section Cross2

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [ProperSpace F]

/-- The base point `a • u` lies in `crossTube ρ u v hv a`. -/
theorem base_mem_crossTube {ρ : NNReal} {u v : F} (hv : ‖v‖ = 1) (a : ℝ) :
    a • u ∈ (crossTube ρ u v hv a).carrier := by
  rw [crossTube, Tube.mk'_carrier]
  exact Set.mem_biUnion (left_mem_segment ℝ _ _)
    (Metric.mem_closedBall_self (NNReal.coe_nonneg ρ))

/-- Every point `θ • u` with `θ ∈ [0,1]` lies in the reference tube `crossTube ρ v u hu 0`,
whose core is the segment from `0` to `u`. -/
theorem smul_mem_crossTube_zero {ρ : NNReal} {u v : F} (hu : ‖u‖ = 1) {θ : ℝ}
    (hθ : θ ∈ Set.Icc (0 : ℝ) 1) : θ • u ∈ (crossTube ρ v u hu 0).carrier := by
  rw [crossTube, Tube.mk'_carrier]
  refine Set.mem_biUnion ?_ (Metric.mem_closedBall_self (NNReal.coe_nonneg ρ))
  rw [segment_eq_image' ℝ]
  exact ⟨θ, hθ, by module⟩

end Cross2

private lemma one_le_abs_sub_natCast {a b : ℕ} (h : a ≠ b) : (1 : ℝ) ≤ |(a : ℝ) - (b : ℝ)| := by
  rcases lt_or_gt_of_ne h with h' | h'
  · have hh : (a : ℝ) + 1 ≤ (b : ℝ) := by exact_mod_cast Nat.succ_le_of_lt h'
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  · have hh : (b : ℝ) + 1 ≤ (a : ℝ) := by exact_mod_cast Nat.succ_le_of_lt h'
    rw [abs_of_nonneg (by linarith)]
    linarith

/-! ### The refutation of the literal statement -/

/-- **The counterexample configuration**, isolated so that the refutation below cannot be blamed
on a degenerate *scale*: the produced `ρ` satisfies `0 < ρ ≤ 1`, and the tubes are honest
`ρ`-tubes with `n` of them pairwise essentially distinct.

Take `n` singleton bodies `{p_j}` at the points `p_j = (j/n) • u` of the core of one `ρ`-tube
`W₀`, and let the reference cover consist of the `n` tubes `W_j` whose cores run from `p_j` in the
*orthogonal* direction `v`.  With `ρ = 1/(4n)` the `W_j` lie in `n` pairwise disjoint slabs
`|⟪u, ·⟫ - j/n| ≤ ρ`, hence are pairwise disjoint, hence pairwise essentially distinct for free;
every one of them contains its own `{p_j}` (so every one is *used*); and every `{p_j}` lies in the
single tube `W₀`.

The only degeneracy is in the **bodies**, which are points.  That is exactly the freedom the
literal statement forgot to exclude. -/
theorem exists_pointBody_cover_config (n : ℕ) (hn : 0 < n) :
    ∃ (ρ : NNReal) (V : ULift.{u} (Fin n) → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
      (W : ULift.{u} (Fin n) → Tube ρ (EuclideanSpace ℝ (Fin 3)))
      (W₀ : Tube ρ (EuclideanSpace ℝ (Fin 3))),
      0 < ρ ∧ ρ ≤ 1 ∧
      (∀ i, V i ≤ (W i).toConvexSpaceBody) ∧
      (∀ i, V i ≤ W₀.toConvexSpaceBody) ∧
      (Set.univ : Set (ULift.{u} (Fin n))).Pairwise
        fun j k => _root_.IsEssentiallyDistinct (W j).carrier (W k).carrier := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  set u : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single 0 (1 : ℝ) with hu_def
  set v : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single 1 (1 : ℝ) with hv_def
  have hu : ‖u‖ = 1 := by rw [hu_def, PiLp.norm_single]; simp
  have hv : ‖v‖ = 1 := by rw [hv_def, PiLp.norm_single]; simp
  have huv : inner ℝ u v = (0 : ℝ) := by
    rw [hu_def, hv_def, EuclideanSpace.inner_single_left]; simp
  set ρ : NNReal := (4 * (n : NNReal))⁻¹ with hρ_def
  have hρc : (ρ : ℝ) = 1 / (4 * (n : ℝ)) := by
    rw [hρ_def]; push_cast; rw [one_div]
  have hρ0 : 0 < ρ := by
    rw [← NNReal.coe_pos, hρc]; positivity
  have hρ1 : ρ ≤ 1 := by
    rw [← NNReal.coe_le_coe, hρc, NNReal.coe_one, div_le_one (by linarith)]
    linarith
  set p : Fin n → EuclideanSpace ℝ (Fin 3) := fun j => ((j : ℝ) / (n : ℝ)) • u with hp_def
  refine ⟨ρ, fun i => ⟨{p i.down}, (convex_singleton _).isConvexSet, isCompact_singleton,
      Set.singleton_nonempty _⟩,
    fun j => crossTube ρ u v hv (((j.down : ℕ) : ℝ) / (n : ℝ)), crossTube ρ v u hu 0,
    hρ0, hρ1, ?_, ?_, ?_⟩
  · exact fun i => SetLike.coe_subset_coe.mp
      (Set.singleton_subset_iff.mpr (base_mem_crossTube hv _))
  · intro i
    refine SetLike.coe_subset_coe.mp (Set.singleton_subset_iff.mpr ?_)
    refine smul_mem_crossTube_zero hu ⟨by positivity, ?_⟩
    rw [div_le_one hnpos]
    exact_mod_cast i.down.isLt.le
  · intro j _ k _ hjk
    refine isEssentiallyDistinct_of_inter_eq_empty (crossTube_disjoint hu hv huv ?_)
    have hne : ((j.down : Fin n) : ℕ) ≠ ((k.down : Fin n) : ℕ) := fun hcon =>
      hjk (ULift.down_injective (Fin.val_injective hcon))
    have h1 := one_le_abs_sub_natCast hne
    have hdiv : |(((j.down : Fin n) : ℕ) : ℝ) / (n : ℝ) - (((k.down : Fin n) : ℕ) : ℝ) / (n : ℝ)|
        = |(((j.down : Fin n) : ℕ) : ℝ) - (((k.down : Fin n) : ℕ) : ℝ)| / (n : ℝ) := by
      rw [div_sub_div_same, abs_div, abs_of_pos hnpos]
    rw [hdiv, hρc, lt_div_iff₀ hnpos]
    have hhalf : 2 * (1 / (4 * (n : ℝ))) * (n : ℝ) = 1 / 2 := by field_simp; norm_num
    rw [hhalf]
    linarith

/-- **`Kakeya.ML2Reduction.CoverCountComparable` is false as stated, at every loss `Λ`.**

`Tube.exists_pointBody_cover_config` at any `n > Λ` supplies a configuration satisfying every
hypothesis with `|t| = n` and `|t'| = 1`, so the conclusion would give `n ≤ Λ`.  Since that
configuration also satisfies `0 < ρ ≤ 1`, **no hypothesis on the scale can repair the statement**;
what is missing is a nondegeneracy hypothesis on the covered bodies, which is what
`Tube.CoverCountComparableChord` adds. -/
theorem not_coverCountComparableSpec (Λ : ℝ) : ¬ CoverCountComparableSpec.{u} Λ := by
  intro h
  obtain ⟨n, hn⟩ := exists_nat_gt (max Λ 1)
  have hn1 : (1 : ℝ) < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hn
  have hnΛ : Λ < (n : ℝ) := lt_of_le_of_lt (le_max_left _ _) hn
  have hn0 : 0 < n := by exact_mod_cast lt_trans zero_lt_one hn1
  obtain ⟨ρ, V, W, W₀, -, -, hleW, hleW', hED⟩ := exists_pointBody_cover_config.{u} n hn0
  have hres := h V Finset.univ Finset.univ W (Finset.univ : Finset (ULift.{u} Unit))
    (fun _ => W₀)
    (fun i _ => ⟨i, Finset.mem_univ _, hleW i⟩)
    (by rw [Finset.coe_univ]; exact hED)
    (fun j _ => ⟨j, Finset.mem_univ _, hleW j⟩)
    (fun i _ => ⟨⟨()⟩, Finset.mem_univ _, hleW' i⟩)
  rw [show (Finset.univ : Finset (ULift.{u} (Fin n))).card = n from by simp,
    show (Finset.univ : Finset (ULift.{u} Unit)).card = 1 from by simp] at hres
  simp only [Nat.cast_one, mul_one] at hres
  linarith

/-! ### The repaired statement, and its proof -/

/-- Every tube carries a chord of length `1`, so the nondegeneracy hypothesis of
`Tube.CoverCountComparableChord` is free for a family of tubes. -/
theorem exists_chord_of_tube {τ : NNReal} (T : Tube τ E) :
    ∃ p ∈ T.carrier, ∃ q ∈ T.carrier, (2 / 5 : ℝ) ≤ dist p q :=
  ⟨T.x, x_mem_carrier T, T.y, y_mem_carrier T, by rw [T.dist_eq_one]; norm_num⟩

/-- **The repaired form of `Kakeya.ML2Reduction.CoverCountComparable`.**

Exactly `Tube.CoverCountComparableSpec` with three hypotheses added — `0 < ρ`, `ρ ≤ 1`, and the
nondegeneracy `hnd` of the covered bodies.  `Tube.coverCountComparableChord_of_spec` checks
mechanically that this is a *weakening* of the literal statement. -/
def CoverCountComparableChord (Λ : ℝ) : Prop :=
  ∀ {α κ κ' : Type u} {ρ : NNReal} (V : α → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
    (s : Finset α) (t : Finset κ) (W : κ → Tube ρ (EuclideanSpace ℝ (Fin 3)))
    (t' : Finset κ') (W' : κ' → Tube ρ (EuclideanSpace ℝ (Fin 3))),
    0 < ρ → ρ ≤ 1 →
    (∀ i ∈ s, ∃ p ∈ (V i).carrier, ∃ q ∈ (V i).carrier, (2 / 5 : ℝ) ≤ dist p q) →
    (∀ i ∈ s, ∃ j ∈ t, V i ≤ (W j).toConvexSpaceBody) →
    (t : Set κ).Pairwise
      (fun j k ↦ _root_.IsEssentiallyDistinct (W j).carrier (W k).carrier) →
    (∀ j ∈ t, ∃ i ∈ s, V i ≤ (W j).toConvexSpaceBody) →
    (∀ i ∈ s, ∃ j ∈ t', V i ≤ (W' j).toConvexSpaceBody) →
    (t.card : ℝ) ≤ Λ * (t'.card : ℝ)

/-- **`Tube.CoverCountComparableChord` is a weakening of `Tube.CoverCountComparableSpec`** — the
compiler-checked record that nothing was changed except by adding hypotheses. -/
theorem coverCountComparableChord_of_spec {Λ : ℝ} (h : CoverCountComparableSpec.{u} Λ) :
    CoverCountComparableChord.{u} Λ := fun V s t W t' W' _ _ _ href hED hused hcov =>
  h V s t W t' W' href hED hused hcov

/-- **The repaired statement is TRUE**, at the explicit loss
`Λ = 1 + Tube.essDistinctTubesInSelfDilate.C 3 32`. -/
theorem coverCountComparableChord :
    CoverCountComparableChord.{u} ((coverCountLoss 3 : NNReal) : ℝ) := by
  intro α κ κ' ρ V s t W t' W' hρ0 hρ1 hnd _href hED hused hcov
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have := card_le_mul_card_of_chordCover (E := EuclideanSpace ℝ (Fin 3)) hρ0 hρ1
    (K := 1) le_rfl V s t W t' W'
    (fun i hi => by simpa using hnd i hi) hED hused hcov
  rwa [hfr] at this

/-! ### The consumer -/

/-- **The exact analogue of `Kakeya.ML2Reduction.count_of_coverCountComparable`** for the repaired
statement: comparability at loss `Λ` turns a lower bound `Λ c ≤ |t|` on the canonical cover into
the bound `c ≤ |t'|` for every competitor cover, which is Lemma 9.1's count clause verbatim. -/
theorem count_of_coverCountComparableChord {Λ c : ℝ} (hΛ : 0 < Λ)
    (h : CoverCountComparableChord.{u} Λ)
    {α : Type u} {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (V : α → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))) (s : Finset α)
    (hnd : ∀ i ∈ s, ∃ p ∈ (V i).carrier, ∃ q ∈ (V i).carrier, (2 / 5 : ℝ) ≤ dist p q)
    {κ : Type u} (t : Finset κ) (W : κ → Tube ρ (EuclideanSpace ℝ (Fin 3)))
    (href : ∀ i ∈ s, ∃ j ∈ t, V i ≤ (W j).toConvexSpaceBody)
    (hED : (t : Set κ).Pairwise
      fun j k ↦ _root_.IsEssentiallyDistinct (W j).carrier (W k).carrier)
    (hused : ∀ j ∈ t, ∃ i ∈ s, V i ≤ (W j).toConvexSpaceBody)
    (hlow : Λ * c ≤ (t.card : ℝ))
    {κ' : Type u} (t' : Finset κ') (W' : κ' → Tube ρ (EuclideanSpace ℝ (Fin 3)))
    (hcov : ∀ i ∈ s, ∃ j ∈ t', V i ≤ (W' j).toConvexSpaceBody) :
    c ≤ (t'.card : ℝ) :=
  le_of_mul_le_mul_left
    (hlow.trans (h V s t W t' W' hρ0 hρ1 hnd href hED hused hcov)) hΛ

/-- **The count clause, with no abstract `Prop` in the way and no `href`**: the form a consumer
should cite.  The `V i` are arbitrary bodies carrying a chord of length `≥ 2/5`; the version for a
family of tubes is `Tube.count_of_canonicalCover_tube`. -/
theorem count_of_canonicalCover [Nontrivial E] {c : ℝ} {α : Type*} {ρ : NNReal}
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) {K : ℝ} (hK : 1 ≤ K)
    (V : α → ConvexSpaceBody E) (s : Finset α)
    (hnd : ∀ i ∈ s, ∃ p ∈ (V i).carrier, ∃ q ∈ (V i).carrier, 2 / (5 * K) ≤ dist p q)
    {κ : Type*} (t : Finset κ) (W : κ → Tube ρ E)
    (hED : (t : Set κ).Pairwise
      fun j k ↦ _root_.IsEssentiallyDistinct (W j).carrier (W k).carrier)
    (hused : ∀ j ∈ t, ∃ i ∈ s, V i ≤ (W j).toConvexSpaceBody)
    (hlow : (coverCountLossAt (Module.finrank ℝ E) K : ℝ) * c ≤ (t.card : ℝ))
    {κ' : Type*} (t' : Finset κ') (W' : κ' → Tube ρ E)
    (hcov : ∀ i ∈ s, ∃ j ∈ t', V i ≤ (W' j).toConvexSpaceBody) :
    c ≤ (t'.card : ℝ) := by
  refine le_of_mul_le_mul_left (hlow.trans ?_) ?_
  · exact card_le_mul_card_of_chordCover hρ0 hρ1 hK V s t W t' W' hnd hED hused hcov
  · exact lt_of_lt_of_le zero_lt_one (one_le_coverCountLossAt_real _ _)

/-- The tube-family form: the nondegeneracy hypothesis is discharged by
`Tube.exists_chord_of_tube`. -/
theorem count_of_canonicalCover_tube [Nontrivial E] {c : ℝ} {α : Type*} {ρ τ : NNReal}
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (V : α → Tube τ E) (s : Finset α)
    {κ : Type*} (t : Finset κ) (W : κ → Tube ρ E)
    (hED : (t : Set κ).Pairwise
      fun j k ↦ _root_.IsEssentiallyDistinct (W j).carrier (W k).carrier)
    (hused : ∀ j ∈ t, ∃ i ∈ s, (V i).toConvexSpaceBody ≤ (W j).toConvexSpaceBody)
    (hlow : (coverCountLoss (Module.finrank ℝ E) : ℝ) * c ≤ (t.card : ℝ))
    {κ' : Type*} (t' : Finset κ') (W' : κ' → Tube ρ E)
    (hcov : ∀ i ∈ s, ∃ j ∈ t', (V i).toConvexSpaceBody ≤ (W' j).toConvexSpaceBody) :
    c ≤ (t'.card : ℝ) :=
  count_of_canonicalCover hρ0 hρ1 (K := 1) le_rfl (fun i => (V i).toConvexSpaceBody) s
    (fun i _ => by simpa using exists_chord_of_tube (V i)) t W hED hused hlow t' W' hcov

/-! ### Non-vacuity, and the consumer's nondegeneracy witness -/

/-- Every shaded tube's body carries a chord of length `1`, so the nondegeneracy hypothesis is
free for the family of `Kakeya.ML2Reduction.Lemma91At`'s count clause, whose bodies are
`(T i).toConvexSpaceBody` for `T i : ShadedTube δ _`. -/
theorem exists_chord_of_shadedTube {τ : NNReal} (T : ShadedTube τ E) :
    ∃ p ∈ (T.toConvexSpaceBody).carrier, ∃ q ∈ (T.toConvexSpaceBody).carrier,
      (2 / 5 : ℝ) ≤ dist p q :=
  exists_chord_of_tube T.toTube

/-- **Non-vacuity of `Tube.CoverCountComparableChord`.**

The hypotheses of its inner `∀` are simultaneously satisfiable with a **nonempty** reference
cover — one tube covering its own body is such a configuration — so the predicate is not
vacuously true, and any valid loss is at least `1`.  (This is the check that the three
`SpineInheritance` adapters of `STATUS-S9` failed.) -/
theorem one_le_of_coverCountComparableChord {Λ : ℝ} (h : CoverCountComparableChord.{u} Λ) :
    1 ≤ Λ := by
  have hu : ‖(EuclideanSpace.single 0 (1 : ℝ) : EuclideanSpace ℝ (Fin 3))‖ = 1 := by
    rw [PiLp.norm_single]; simp
  set W₀ : Tube (1 / 2 : NNReal) (EuclideanSpace ℝ (Fin 3)) :=
    crossTube (1 / 2) (EuclideanSpace.single 0 (1 : ℝ)) (EuclideanSpace.single 0 (1 : ℝ)) hu 0
    with hW₀
  have hres := h (fun _ : ULift.{u} Unit => W₀.toConvexSpaceBody)
    (Finset.univ : Finset (ULift.{u} Unit)) (Finset.univ : Finset (ULift.{u} Unit))
    (fun _ => W₀) (Finset.univ : Finset (ULift.{u} Unit)) (fun _ => W₀)
    (by norm_num) (by norm_num)
    (fun _ _ => exists_chord_of_tube W₀)
    (fun i _ => ⟨i, Finset.mem_univ _, le_refl _⟩)
    (fun j _ k _ hjk => absurd (Subsingleton.elim j k) hjk)
    (fun j _ => ⟨j, Finset.mem_univ _, le_refl _⟩)
    (fun i _ => ⟨i, Finset.mem_univ _, le_refl _⟩)
  rw [show (Finset.univ : Finset (ULift.{u} Unit)).card = 1 from by simp] at hres
  simpa using hres

/-- **The form the count clause of `Kakeya.ML2Reduction.Lemma91At` should cite.**

The bodies are the shaded tubes of the family itself, so the nondegeneracy hypothesis is
discharged internally by `Tube.exists_chord_of_shadedTube` and no hypothesis beyond `0 < ρ`,
`ρ ≤ 1` is added to what `Kakeya.ML2Reduction.count_of_coverCountComparable` already asked for. -/
theorem count_of_canonicalCover_shadedTube [Nontrivial E] {c : ℝ} {α : Type*} {ρ τ : NNReal}
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (T : α → ShadedTube τ E) (s : Finset α)
    {κ : Type*} (t : Finset κ) (W : κ → Tube ρ E)
    (hED : (t : Set κ).Pairwise
      fun j k ↦ _root_.IsEssentiallyDistinct (W j).carrier (W k).carrier)
    (hused : ∀ j ∈ t, ∃ i ∈ s, (T i).toConvexSpaceBody ≤ (W j).toConvexSpaceBody)
    (hlow : (coverCountLoss (Module.finrank ℝ E) : ℝ) * c ≤ (t.card : ℝ))
    {κ' : Type*} (t' : Finset κ') (W' : κ' → Tube ρ E)
    (hcov : ∀ i ∈ s, ∃ j ∈ t', (T i).toConvexSpaceBody ≤ (W' j).toConvexSpaceBody) :
    c ≤ (t'.card : ℝ) :=
  count_of_canonicalCover hρ0 hρ1 (K := 1) le_rfl (fun i => (T i).toConvexSpaceBody) s
    (fun i _ => by simpa using exists_chord_of_shadedTube (T i)) t W hED hused hlow t' W' hcov

/-- **The count clause for bodies of an arbitrary positive diameter `d`.**

The chord threshold of `Tube.count_of_canonicalCover` is `2/(5K)`, so a family whose bodies only
carry a chord of length `≥ d` is handled at `K = max 1 (2/(5d))`, i.e. at the dilation ratio
`32 max(1, 2/(5d))`.  This matters: the *weaker* form of the count clause that
`Kakeya.ML2Reduction.outerFamily_count_of_spineFamily_count` reduces to is stated on the
**rescaled bodies**, whose diameter is `≈ 1/(4R) = 1/256` and not `1`.  With `d = 1/256` the ratio
is `32 · 512/5`, still a constant independent of `ρ`, of the tubes and of the family. -/
theorem count_of_canonicalCover_of_diam [Nontrivial E] {c d : ℝ} {α : Type*} {ρ : NNReal}
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hd0 : 0 < d)
    (V : α → ConvexSpaceBody E) (s : Finset α)
    (hnd : ∀ i ∈ s, ∃ p ∈ (V i).carrier, ∃ q ∈ (V i).carrier, d ≤ dist p q)
    {κ : Type*} (t : Finset κ) (W : κ → Tube ρ E)
    (hED : (t : Set κ).Pairwise
      fun j k ↦ _root_.IsEssentiallyDistinct (W j).carrier (W k).carrier)
    (hused : ∀ j ∈ t, ∃ i ∈ s, V i ≤ (W j).toConvexSpaceBody)
    (hlow : (coverCountLossAt (Module.finrank ℝ E) (max 1 (2 / (5 * d))) : ℝ) * c ≤ (t.card : ℝ))
    {κ' : Type*} (t' : Finset κ') (W' : κ' → Tube ρ E)
    (hcov : ∀ i ∈ s, ∃ j ∈ t', V i ≤ (W' j).toConvexSpaceBody) :
    c ≤ (t'.card : ℝ) := by
  set K : ℝ := max 1 (2 / (5 * d)) with hK_def
  have hK : 1 ≤ K := le_max_left _ _
  have hK0 : (0 : ℝ) < K := lt_of_lt_of_le zero_lt_one hK
  have hthr : 2 / (5 * K) ≤ d := by
    have h2 : 2 / (5 * d) ≤ K := le_max_right _ _
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ (by positivity)] at h2
    nlinarith
  exact count_of_canonicalCover hρ0 hρ1 hK V s
    (fun i hi => by
      obtain ⟨p, hp, q, hq, hpq⟩ := hnd i hi
      exact ⟨p, hp, q, hq, hthr.trans hpq⟩)
    t W hED hused hlow t' W' hcov

end Tube
