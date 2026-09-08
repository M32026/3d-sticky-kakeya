/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.FibreCompletion
public import Kakeya.MultiScaleFac
public import Kakeya.Tube.Dilate

/-!
# Main Lemma 1, Case (ii), Step 5a item (a): a producer for `IsEnlargementCover`

Blueprint `subsec:ml1bootEnlargementCover`, split there over
`GWZAdapted/section8_step5a_cover.tex`, `section8_step5a_cover_net.tex` and
`section8_step5a_cover_producer.tex`.

`Kakeya.ml1Boot.exists_cover_of_subset_rescale` builds the covering family from `W`, `θ` and
`Kakeya.ml1Boot.enlargementCoverNet` alone and covers **every** `δ`-tube of the container, of which
there are a continuum; `Kakeya.ml1Boot.isEnlargementCover_rescale` is its quantifier-order
weakening and is **the first producer of `Kakeya.ml1Boot.IsEnlargementCover` in this
development**.  Until it was written every result of
the covering route — `Kakeya.ml1Boot.card_neighbouringParents_le_of_cover`,
`Kakeya.ml1Boot.card_completedFibreParents_le`, `Kakeya.ml1Boot.card_completedFibre_le` and
`Kakeya.ml1Boot.densityIn_le_of_neighbouringParents` — was a proved implication whose antecedent
nothing supplied.  The count it produces is `Kakeya.ml1Boot.enlargementCoverConstant E Λ`, which
depends on the ambient space `E` and on the enlargement factor `Λ` and **on nothing else**: not on
`θ`, not on `δ`, not on the tube `W`, not on the family and not on the index set.  That is the
whole content of blueprint `def:ml1bootNeighbouringParentsConstant`'s informal half, and what
carries it is that `Kakeya.ml1Boot.enlargementCoverConstant E Λ` is a *term* mentioning `E` and
`Λ` alone — the binder order below merely displays it and is not itself the assertion.

## The container is a concentric rescaling and *not* a homothety

Every statement here is read at `W.rescale (Λ * θ)`, the concentric rescaling of blueprint
`note:ml1bootTwoDilates`: it keeps the unit core of `W` and replaces the radius, so its
longitudinal extent is `1 + 2 Λ θ`.  The shape may **not** be traded for a homothety `c · V`.
`Kakeya.Tube.norm_midpoint_sub_center_le_of_norm_chord_eq_one`, the step that pins a leaf
longitudinally, is false at a homothety with `c > 1` fixed: the sliding configuration of blueprint
`note:ml1bootHomothetyOverlapInsufficient` is a family of unit segments inside such a container
whose midpoints are spread over a distance `Θ(c - 1)` and not `O(θ)`.  So nothing here closes the
longitudinal gap of blueprint `note:ml1bootEnlargementTubeStatus`, and nothing here bears on
hypothesis (R1) of `Kakeya.ml1Boot.card_neighbouringParents_le_of_essDistinct`.

## The edge to the consumers, and what it costs

The four consumers listed above keep their statements, which continue to take
`Kakeya.ml1Boot.IsEnlargementCover` as a bare hypothesis; alongside each of them there now stands
an **unconditional** variant in the final section of this file, whose covering hypothesis is
discharged at `Kakeya.ml1Boot.isEnlargementCover_rescale` and whose count is therefore the term
`Kakeya.ml1Boot.enlargementCoverConstant E Λ * Cu`.  The price is a genuine hypothesis on the
scales, not a technicality: the producer needs `2 δ ≤ ρ_a`, which **fails at `a = N`**, where the
coarse grid scale is `δ` itself.  So every statement in that section carries `a < N` explicitly,
together with the smallness `δ ≤ 16 ^ (-N)` the rest of this development already uses
(`Tube.exists_uniformTubeSet_subfamily`); the two together give `2 δ ≤ ρ_a` through
`Kakeya.ml1Boot.two_mul_le_gridScale_of_le_pow`.  At the Case (ii) call sites `a < N` is free:
`StickyKakeya.IsFrostmanDividingBlock` asserts `a < b` and `b ≤ N`.

## Placement of the generic lemmas, and a split this file still owes

The scalar lemma `Kakeya.abs_add_add_abs_sub_le_of_abs_le`, the net lemmas
`Kakeya.exists_finset_nonempty_forall_exists_norm_sub_le`,
`Kakeya.exists_mem_norm_sub_add_smul_le`, the normalization `Kakeya.normalizeWith` and its two
lemmas, and the generic tube lemmas of the `Kakeya.Tube` namespace below all live in **this** file,
and **they should not.**  Only the last three declarations — `Kakeya.ml1Boot.enlargementCoverNet`,
`Kakeya.ml1Boot.enlargementCoverConstant` and the two producers
`Kakeya.ml1Boot.exists_cover_of_subset_rescale` and
`Kakeya.ml1Boot.isEnlargementCover_rescale` — are about Step 5a at all; everything before the
`Kakeya.ml1Boot` namespace is generic normed-space, net or tube material that mentions neither
Main Lemma 1 nor `Kakeya.ml1Boot.IsEnlargementCover`, and belongs in `Kakeya/Mathlib/Analysis/` and
`Kakeya/Tube/` respectively.  Being this file's only consumer is not a reason to keep it here: the
file is past a thousand lines, well over the project's guidance of about five hundred, and the two
blocks are separable at the `end Tube` / `namespace ml1Boot` boundary because every reference across
that boundary runs the same way: the Step 5a block cites the generic one and nothing in the generic
block cites anything after it.  The split is deliberately **not** made in the same pass as the
mathematics, because it is a move of some six hundred lines across new modules and would have to be
existing together with a regenerated `Kakeya.lean` import index and a fresh `lake shake`, none of
which can be checked without a build.  It is recorded here as owed rather than presented as a
design choice.

## Statements that already exist elsewhere, and are cited rather than reproved

* blueprint `lem:dilatePointBoundsGeneral` is `Tube.abs_inner_and_perp_le_of_mem_dilate`
  (`Kakeya/Tube/Dilate.lean`) read at dilation ratio `1` of the tube `W.rescale r`;
* the transverse and quadratic-defect chord estimates are the two
  halves of blueprint `lem:ml1bootUnitChordTilt`, already proved as
  `Kakeya.Tube.norm_chord_transverse_le_of_endpoints_mem_dilate` and
  `Kakeya.Tube.one_sub_abs_inner_chord_le_of_endpoints_mem_dilate` (`Kakeya/Tube/Dilate.lean`),
  read at ratio `1` of a tube of radius `r`, where the two right-hand sides `2 c δ` and
  `4 c ^ 2 δ ^ 2` become `2 r` and `4 r ^ 2`; entering the `1`-dilate from the tube itself is
  `Tube.subset_dilate` at `c = 1` — which is the *root* `Tube` namespace of
  `Kakeya/Tube/Dilate.lean` and not `Kakeya.Tube`, where only the last group of that file's
  declarations sits — and `dist p q = 1` is `‖q - p‖ = 1` through `dist_eq_norm'`.  **So they have
  no declaration of their own here** and the confinement lemmas below cite them directly.  The intermediate `1 - 4 r ^ 2 ≤ ⟪u, e⟫ ^ 2` of the first of those two
  halves is likewise not stated: it is one application of
  `Kakeya.inner_sq_add_norm_transverse_sq_eq`, and the only consequence used downstream is the
  linear form `1 - 4 r ^ 2 ≤ |⟪u, e⟫|`, which *is* the second declaration named above;
* the first sentence of blueprint `lem:ml1bootCoverRescaleBall` is
  `Kakeya.Tube.carrier_subset_closedBall_midpoint` (`Kakeya/Tube/Basic.lean`); only its second
  sentence, `Kakeya.Tube.norm_midpoint_sub_center_le_of_mem_carrier`, is written here;
* the covering half of blueprint `lem:ml1bootCoverFiniteNet` is
  `Kakeya.closedBall_finite_closedBall_cover` (`Kakeya/Mathlib/Topology/Metric.lean`); only the
  adjunction of the centre that makes the net nonempty is owed, and
  `Kakeya.exists_finset_nonempty_forall_exists_norm_sub_le` is the statement carrying it;
* blueprint `lem:segmentEndpointCthickening` is
  `Metric.cthickening_segment_subset_cthickening_segment` (`Kakeya/Tube/Dilate.lean`) read at
  thickening radius `0`, and so has **no declaration of its own here**.  Blueprint
  `lem:ml1bootCoverTubeFromCore` — `Kakeya.Tube.subset_of_core_subset_cthickening` below — is that
  same lemma composed with `Kakeya.Tube.carrier_eq_cthickening` and one `Metric.cthickening_mono`,
  and it *is* kept, because it is the shape
  `Kakeya.Tube.subset_ofMidpointDirection_of_dist_params_le` consumes.

## Why `[MeasurableSpace E]` and `[BorelSpace E]` are carried

No statement in this file needs a measure on `E`, and several need neither an inner product nor a
dimension. They are nonetheless stated in the full context above, because every declaration they
are to be proved from — `Tube.abs_inner_and_perp_le_of_mem_dilate`,
`Kakeya.Tube.norm_chord_transverse_le_of_endpoints_mem_dilate`,
`Kakeya.Tube.one_sub_abs_inner_chord_le_of_endpoints_mem_dilate`, `Tube.subset_dilate`,
`Tube.x_mem_carrier`, `Tube.y_mem_carrier` and
`Metric.cthickening_segment_subset_cthickening_segment` — stands under one of the two variable
blocks of `Kakeya/Tube/Dilate.lean` (the root-`Tube` one and the `Kakeya.Tube` one), each of which
carries `[FiniteDimensional ℝ E]`, `[MeasurableSpace E]` and `[BorelSpace E]` with no `omit`
before any of them. `[ProperSpace E]`, which
`Tube` requires, is an instance of `[FiniteDimensional ℝ E]` and so is never written. The one
declaration that does omit all three is
`Kakeya.Tube.norm_midpoint_sub_center_le_of_mem_carrier`, whose single input
`Kakeya.Tube.carrier_subset_closedBall_midpoint` already stands under an `omit`. `[Nontrivial E]`
is omitted throughout, nothing here using it.

## Recorded adjustments to the blueprint display

* The confinement lemmas are stated at a tube `V : Tube r E` rather than at `W.rescale r` for a
  tube `W` of some unrelated radius.  Blueprint `lem:dilatePointBoundsGeneral` records that
  the radius of `W` itself does not occur, so a second radius would be a binder naming nothing;
  the displayed statements are the instances `V = W.rescale r`, at which `V.center = W.center` and
  `V.direction = W.direction`.
* `Kakeya.exists_mem_norm_sub_add_smul_le` (blueprint `lem:ml1bootCoverScaledNet`) omits the
  blueprint's `0 ≤ R` and `0 < ε`: neither is used, the whole argument being the case split on
  `θ = 0`.
* `Kakeya.exists_finset_nonempty_forall_exists_norm_sub_le` (blueprint
  `lem:ml1bootCoverFiniteNet`) omits the blueprint's `0 ≤ R`.  That entry justifies the hypothesis
  by nonemptiness of the net, and the justification is wrong: the net is made nonempty by
  adjoining the centre, which is available at every `R`, and at `R < 0` the covering clause is
  vacuous.  No sign condition on `R` is needed for either clause.
* `Kakeya.norm_sub_normalizeWith_le` (blueprint `lem:ml1bootCoverUnitNetPoint`) omits the
  blueprint's `0 ≤ s`, which follows from `‖e - w‖ ≤ s`.
* Blueprint `lem:ml1bootCoverTubeFromCore` and `lem:ml1bootCoverLeafContainment` are displayed
  there at the typeclasses of `def:deltaTube` alone; here they carry the inner-product and measure
  context of the rest of the file, for the reason recorded above.  The blueprint writes those
  typeclasses as `[SeminormedAddCommGroup E]`, which is the class the structure `Tube` is declared
  over; the `Tube` API these two statements use — `Tube.carrier_eq_cthickening`, `Tube.rescale`
  and `Tube.ofMidpointDirection` — is stated one class up, at `[NormedAddCommGroup E]`.
-/

@[expose] public section

open Metric Set

namespace Kakeya

/-! ### One statement of `ℝ` alone, and three of a bare normed space -/

/-- **Mean and spread of two bounded reals** (blueprint `lem:ml1bootCoverMeanSpreadScalar`).

The left-hand side is in fact *equal* to `max |a| |b|`; only the inequality is used, and only it is
asserted.  This is the whole of the two-sided bookkeeping of
`Kakeya.Tube.abs_inner_midpoint_sub_center_le_of_norm_chord_eq_one`, separated out so that no
orientation of the chord has to be chosen there.  A statement of `ℝ` alone: no space, no norm and
no tube occurs. -/
theorem abs_add_add_abs_sub_le_of_abs_le {a b K : ℝ} (ha : |a| ≤ K) (hb : |b| ≤ K) :
    (1 / 2 : ℝ) * |a + b| + (1 / 2 : ℝ) * |b - a| ≤ K := by
  rcases abs_cases (a + b) with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;>
    rcases abs_cases (b - a) with ⟨h2, h2'⟩ | ⟨h2, h2'⟩ <;>
    rcases abs_cases a <;> rcases abs_cases b <;> nlinarith

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Scaling a net** (blueprint `lem:ml1bootCoverScaledNet`).

A net of the ball of radius `R` about the origin, translated to `a` and scaled by `θ`, is a net of
the ball of radius `θ R` about `a` with spacing `θ ε`.  This is the step that makes the count of
`Kakeya.ml1Boot.enlargementCoverConstant` independent of `θ`: **one** net, fixed once at the
`θ`-free radius `R`, serves every scale, the scaling being absorbed into the net points rather than
into their number.

The net property is carried as a hypothesis rather than referred to as "the set furnished by
`Kakeya.exists_finset_nonempty_forall_exists_norm_sub_le`": that lemma's output is existentially
quantified, so there is no such set to refer to.  Finiteness of `N` is not used here at all, which
is why `N` is a `Set` and not a `Finset`.

The degenerate value `θ = 0` is admitted and is not vacuous — it is the case the producer meets at
a zero grid radius, where the hypothesis forces `z = a` and the conclusion holds for every
`v ∈ N`.  That is the only use of `hN`. -/
theorem exists_mem_norm_sub_add_smul_le {R ε θ : ℝ} (hθ : 0 ≤ θ) {N : Set E} (hN : N.Nonempty)
    (hnet : ∀ y : E, ‖y‖ ≤ R → ∃ v ∈ N, ‖y - v‖ ≤ ε) {a z : E} (hz : ‖z - a‖ ≤ θ * R) :
    ∃ v ∈ N, ‖z - (a + θ • v)‖ ≤ θ * ε := by
  by_cases hθ0 : θ = 0
  · have hz' : z = a := by
      have hza : z - a = 0 := by
        apply norm_le_zero_iff.mp
        simpa [hθ0] using hz
      exact sub_eq_zero.mp hza
    obtain ⟨v, hvN⟩ := hN
    refine ⟨v, hvN, ?_⟩
    simp [hθ0, hz']
  · have hθgt : 0 < θ := lt_of_le_of_ne hθ (Ne.symm hθ0)
    let y : E := θ⁻¹ • (z - a)
    have hy : ‖y‖ ≤ R := by
      calc
        ‖y‖ = θ⁻¹ * ‖z - a‖ := by
          rw [show y = θ⁻¹ • (z - a) by rfl]
          rw [norm_smul]
          rw [Real.norm_eq_abs]
          rw [abs_of_nonneg]
          exact inv_nonneg.mpr (le_of_lt hθgt)
        _ ≤ θ⁻¹ * (θ * R) :=
          mul_le_mul_of_nonneg_left hz (inv_nonneg.mpr (le_of_lt hθgt))
        _ = R := by
          field_simp [ne_of_gt hθgt]
    obtain ⟨v, hvN, hv⟩ := hnet y hy
    refine ⟨v, hvN, ?_⟩
    have hθy : θ • y = z - a := by
      rw [show y = θ⁻¹ • (z - a) by rfl]
      rw [smul_smul θ θ⁻¹ (z - a)]
      rw [mul_inv_cancel₀ (ne_of_gt hθgt)]
      rw [one_smul]
    have hmain : z - (a + θ • v) = θ • (y - v) := by
      calc
        z - (a + θ • v) = (z - a) - θ • v := by abel
        _ = θ • y - θ • v := by rw [hθy]
        _ = θ • (y - v) := by rw [smul_sub]
    rw [hmain]
    calc
      ‖θ • (y - v)‖ = θ * ‖y - v‖ := by
        rw [norm_smul]
        rw [Real.norm_eq_abs]
        rw [abs_of_nonneg (le_of_lt hθgt)]
      _ ≤ θ * ε := by
        exact mul_le_mul_of_nonneg_left hv (le_of_lt hθgt)

/-- **A net point, normalized to a unit vector**: `‖w‖⁻¹ • w`, with the fallback `u` at `w = 0`.

The normalization is needed because a `θ`-tube is built from a core of length exactly `1`, so a net
point of `E` cannot be used as a direction until it is rescaled to unit length (blueprint
`lem:ml1bootCoverUnitNetPoint`).  The case `w = 0` is not excluded by hypothesis at the call site
and is handled rather than assumed away. -/
noncomputable def normalizeWith (u w : E) : E :=
  open scoped Classical in
  if w = 0 then u else ‖w‖⁻¹ • w

/-- **A normalized net point is a unit vector** (blueprint `lem:ml1bootCoverUnitNetPoint`, first
conclusion).

This is what lets `Kakeya.normalizeWith` be fed to `Tube.ofMidpointDirection` in
`Kakeya.ml1Boot.isEnlargementCover_rescale`. -/
theorem norm_normalizeWith {u : E} (hu : ‖u‖ = 1) (w : E) : ‖normalizeWith u w‖ = 1 := by
  classical
  unfold normalizeWith
  split_ifs with hw
  · exact hu
  · exact norm_smul_inv_norm (𝕜 := ℝ) hw

/-- **Normalizing a net point costs a factor two** (blueprint `lem:ml1bootCoverUnitNetPoint`,
second conclusion).

The factor `2` is what the producer pays for netting the direction parameter in the ambient space
rather than on the sphere, and it is why the net spacing of
`Kakeya.ml1Boot.enlargementCoverNet` is `1/16` where the prose of blueprint
`def:ml1bootNeighbouringParentsConstant` has `1/8`.

The blueprint's hypothesis `0 ≤ s` is omitted: it follows from `‖e - w‖ ≤ s`. -/
theorem norm_sub_normalizeWith_le {e u w : E} (he : ‖e‖ = 1) (hu : ‖u‖ = 1) {s : ℝ}
    (hew : ‖e - w‖ ≤ s) : ‖e - normalizeWith u w‖ ≤ 2 * s := by
  classical
  unfold normalizeWith
  split_ifs with hwn0
  · have hs : (1 : ℝ) ≤ s := by
      rw [← he]
      calc
        ‖e‖ = ‖e - (0 : E)‖ := by simp
        _ ≤ s := by simpa [hwn0] using hew
    have hnorm : ‖e - u‖ ≤ (2 : ℝ) := by
      calc
        ‖e - u‖ ≤ ‖e‖ + ‖u‖ := norm_sub_le e u
        _ = 2 := by norm_num [he, hu]
    exact le_trans hnorm (by nlinarith [hs])
  · have hw0 : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hwn0
    have hfield : (1 - ‖w‖⁻¹ : ℝ) * ‖w‖ = ‖w‖ - 1 := by
      field_simp [hw0]
    have hnm : |1 - ‖w‖⁻¹| * ‖w‖ = |‖w‖ - 1| := by
      calc
        |1 - ‖w‖⁻¹| * ‖w‖ = |1 - ‖w‖⁻¹| * |‖w‖| := by
          rw [abs_of_nonneg (norm_nonneg w)]
        _ = |(1 - ‖w‖⁻¹) * ‖w‖| := by rw [abs_mul]
        _ = |‖w‖ - 1| := by rw [hfield]
    have hnorm_wm : ‖w - ‖w‖⁻¹ • w‖ = |‖w‖ - 1| := by
      calc
        ‖w - ‖w‖⁻¹ • w‖ = ‖(1 - ‖w‖⁻¹ : ℝ) • w‖ := by
          congr 1
          rw [sub_smul, one_smul]
        _ = |1 - ‖w‖⁻¹| * ‖w‖ := by rw [norm_smul, Real.norm_eq_abs]
        _ = |‖w‖ - 1| := hnm
    have hnorm1 : ‖w - ‖w‖⁻¹ • w‖ ≤ s := by
      calc
        ‖w - ‖w‖⁻¹ • w‖ = |‖w‖ - 1| := hnorm_wm
        _ = |‖w‖ - ‖e‖| := by rw [he]
        _ ≤ ‖w - e‖ := abs_norm_sub_norm_le w e
        _ = ‖e - w‖ := by rw [norm_sub_rev]
        _ ≤ s := hew
    have hmain : ‖e - ‖w‖⁻¹ • w‖ ≤ 2 * s := by
      calc
        ‖e - ‖w‖⁻¹ • w‖ = ‖(e - w) + (w - ‖w‖⁻¹ • w)‖ := by
          congr 1
          abel
        _ ≤ ‖e - w‖ + ‖w - ‖w‖⁻¹ • w‖ := norm_add_le _ _
        _ ≤ s + s := add_le_add hew hnorm1
        _ = 2 * s := by ring
    simpa [hwn0] using hmain

end NormedSpace

/-- **A finite nonempty net of a ball** (blueprint `lem:ml1bootCoverFiniteNet`).

The covering half is `Kakeya.closedBall_finite_closedBall_cover` of
`Kakeya/Mathlib/Topology/Metric.lean`, which is already proved; what this statement adds is that
the net is **nonempty**, obtained by adjoining the centre.  Nonemptiness is genuinely used, at
`Kakeya.exists_mem_norm_sub_add_smul_le` in the degenerate case `θ = 0`.

**No hypothesis `0 ≤ R`.**  Blueprint `lem:ml1bootCoverFiniteNet` carries one and justifies it by
nonemptiness; that justification is wrong, adjoining the centre being available at every `R`, and
at `R < 0` the covering clause is vacuous because no `z` satisfies `‖z‖ ≤ R`.  So the hypothesis
would be a binder naming nothing and it is dropped.

**No cardinality bound is asserted.**  Nothing downstream needs a formula for `N.card`, only that
some finite `N` exists, and the deliberate consequence is that
`Kakeya.ml1Boot.enlargementCoverConstant` is not an explicit numeral.  That is the same status the
quantity `M(n,Λ)` has in blueprint `def:ml1bootNeighbouringParentsConstant`, whose prose likewise
counts net points only up to `O_{n,Λ}(1)`. -/
theorem exists_finset_nonempty_forall_exists_norm_sub_le (E : Type*) [NormedAddCommGroup E]
    [ProperSpace E] {R ε : ℝ} (hε : 0 < ε) :
    ∃ N : Finset E, N.Nonempty ∧ ∀ z : E, ‖z‖ ≤ R → ∃ v ∈ N, ‖z - v‖ ≤ ε := by
  classical
  obtain ⟨t, htmem, hsub⟩ := closedBall_finite_closedBall_cover (E := E) R hε (0 : E)
  refine ⟨insert (0 : E) t, Finset.insert_nonempty (0 : E) t, ?_⟩
  intro z hz
  have hzball : z ∈ Metric.closedBall (0 : E) R := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hz
  rcases (Set.mem_iUnion₂.mp (hsub hzball)) with ⟨y, hyt, hyz⟩
  refine ⟨y, Finset.mem_insert_of_mem hyt, ?_⟩
  exact (show ‖z - y‖ ≤ ε by simpa [dist_eq_norm] using (Metric.mem_closedBall.mp hyz))

namespace Tube

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

/-! ### From a containment of cores to a containment of tubes

The two statements of this block are the only ones in the file that mention no inner product, no
orthogonal projection and no dimension, and blueprint `lem:ml1bootCoverTubeFromCore` and
`lem:ml1bootCoverLeafContainment` are displayed at the typeclasses of the structure `Tube` alone.
They are nonetheless stated in the inner-product context of the rest of the file, because the
declaration they are to be proved from — `Metric.cthickening_segment_subset_cthickening_segment`
of `Kakeya/Tube/Dilate.lean` — stands under that file's variable block and carries
`[InnerProductSpace ℝ E]`, `[FiniteDimensional ℝ E]`, `[MeasurableSpace E]` and `[BorelSpace E]`
with no `omit`; a statement at the weaker typeclasses could not cite it.  `[ProperSpace E]`, which
`Tube` requires, is an instance of `[FiniteDimensional ℝ E]` and so is not written.  They are
grouped first, out of the order in which the producer uses them.
-/

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
/-- **Containment of tubes from proximity of their cores** (blueprint
`lem:ml1bootCoverTubeFromCore`).

By blueprint `lem:segmentEndpointCthickening` this is
`Metric.cthickening_segment_subset_cthickening_segment` composed with
`Tube.carrier_eq_cthickening` and one `Metric.cthickening_mono`; it need not be proved directly. -/
theorem subset_of_core_subset_cthickening {δ ρ : NNReal} {s : ℝ} (hs : 0 ≤ s)
    (hsum : (δ : ℝ) + s ≤ (ρ : ℝ)) (T : Tube δ E) (V : Tube ρ E)
    (hcore : segment ℝ T.x T.y ⊆ cthickening s (segment ℝ V.x V.y)) :
    T.carrier ⊆ V.carrier := by
  rw [T.carrier_eq_cthickening, V.carrier_eq_cthickening]
  calc
    cthickening (δ : ℝ) (segment ℝ T.x T.y)
        ⊆ cthickening (δ : ℝ) (cthickening s (segment ℝ V.x V.y)) := by
          exact cthickening_subset_of_subset (δ : ℝ) hcore
    _ ⊆ cthickening ((δ : ℝ) + s) (segment ℝ V.x V.y) := by
          exact cthickening_cthickening_subset δ.coe_nonneg hs (segment ℝ V.x V.y)
    _ ⊆ cthickening (ρ : ℝ) (segment ℝ V.x V.y) := by
          exact cthickening_mono hsum (segment ℝ V.x V.y)

omit [Nontrivial E] in
/-- **Nesting a leaf in the tube built from its net parameters** (blueprint
`lem:ml1bootCoverLeafContainment`).

The two tolerances are exactly those produced by `Kakeya.Tube.exists_net_parameters`, and the scale
hypothesis is the weak form `8 δ ≤ 7 θ` actually used rather than the `2 δ ≤ θ` of blueprint
`def:ml1bootNeighbouringParentsConstant`, which implies it.

The core of `T` is given as a segment `[p, q]` **as a set**, so either labelling of its two
endpoints is admitted; that is the shape `Kakeya.Tube.exists_core_endpoints_of_subset` produces. -/
theorem subset_ofMidpointDirection_of_dist_params_le {δ θ : NNReal} (hδθ : 8 * (δ : ℝ) ≤ 7 * θ)
    (T : Tube δ E) {p q : E} (hcore : segment ℝ p q = segment ℝ T.x T.y) {m' e' : E}
    (he' : ‖e'‖ = 1) (hm : ‖midpoint ℝ p q - m'‖ ≤ (θ : ℝ) / 16)
    (he : ‖q - p - e'‖ ≤ (θ : ℝ) / 8) :
    T.carrier ⊆ (Tube.ofMidpointDirection θ m' e' he').carrier := by
  let V' : Tube θ E := Tube.ofMidpointDirection θ m' e' he'
  have hbtn : ‖(2⁻¹ : ℝ) • ((q - p) - e')‖ ≤ (2⁻¹ : ℝ) * ((θ : ℝ) / 8) := by
    have h20 : (0 : ℝ) ≤ (2⁻¹ : ℝ) := by norm_num
    calc
      ‖(2⁻¹ : ℝ) • ((q - p) - e')‖ = (2⁻¹ : ℝ) * ‖(q - p) - e'‖ := by
        rw [norm_smul]
        norm_num
      _ ≤ (2⁻¹ : ℝ) * ((θ : ℝ) / 8) := mul_le_mul_of_nonneg_left he h20
  have hnorm_x : ‖p - V'.x‖ ≤ (θ : ℝ) / 8 := by
    calc
      ‖p - V'.x‖ = ‖(midpoint ℝ p q - m') - (2⁻¹ : ℝ) • ((q - p) - e')‖ := by
        congr 1
        rw [Tube.ofMidpointDirection_x]
        rw [midpoint_eq_smul_add]
        rw [show (⅟ 2 : ℝ) = (2⁻¹ : ℝ) by norm_num]
        module
      _ ≤ ‖midpoint ℝ p q - m'‖ + ‖(2⁻¹ : ℝ) • ((q - p) - e')‖ := norm_sub_le _ _
      _ ≤ (θ : ℝ) / 16 + (2⁻¹ : ℝ) * ((θ : ℝ) / 8) := add_le_add hm hbtn
      _ = (θ : ℝ) / 8 := by ring
  have hnorm_y : ‖q - V'.y‖ ≤ (θ : ℝ) / 8 := by
    calc
      ‖q - V'.y‖ = ‖(midpoint ℝ p q - m') + (2⁻¹ : ℝ) • ((q - p) - e')‖ := by
        congr 1
        rw [Tube.ofMidpointDirection_y]
        rw [midpoint_eq_smul_add]
        rw [show (⅟ 2 : ℝ) = (2⁻¹ : ℝ) by norm_num]
        module
      _ ≤ ‖midpoint ℝ p q - m'‖ + ‖(2⁻¹ : ℝ) • ((q - p) - e')‖ := norm_add_le _ _
      _ ≤ (θ : ℝ) / 16 + (2⁻¹ : ℝ) * ((θ : ℝ) / 8) := add_le_add hm hbtn
      _ = (θ : ℝ) / 8 := by ring
  have hpx : dist p V'.x ≤ (θ : ℝ) / 8 := by simpa [dist_eq_norm] using hnorm_x
  have hqy : dist q V'.y ≤ (θ : ℝ) / 8 := by simpa [dist_eq_norm] using hnorm_y
  have hsumδ : (δ : ℝ) + (θ : ℝ) / 8 ≤ (θ : ℝ) := by
    nlinarith [hδθ]
  rw [T.carrier_eq_cthickening, V'.carrier_eq_cthickening]
  rw [← hcore]
  calc
    cthickening (δ : ℝ) (segment ℝ p q)
        ⊆ cthickening ((δ : ℝ) + (θ : ℝ) / 8) (segment ℝ V'.x V'.y) :=
      Metric.cthickening_segment_subset_cthickening_segment (p₁ := p) (q₁ := q)
        (p₂ := V'.x) (q₂ := V'.y) (ε := (θ : ℝ) / 8) (r := (δ : ℝ))
        (by positivity) (NNReal.coe_nonneg δ) hpx hqy
    _ ⊆ cthickening (θ : ℝ) (segment ℝ V'.x V'.y) := by
      exact Metric.cthickening_mono hsumδ (segment ℝ V'.x V'.y)

/-! ### Longitudinal and angular confinement of a unit segment in a concentric rescaling

Each statement below is read at a tube `V` of radius exactly `r`.  The displayed instance is
`V = W.rescale r` for a tube `W`, the concentric rescaling of blueprint
`note:ml1bootTwoDilates`, at which `V.center = W.center` and `V.direction = W.direction`; the
radius of `W` itself does not occur, so it is not a binder here.

The two chord estimates are **not** among the statements below: they are the two halves of
blueprint `lem:ml1bootUnitChordTilt`, already proved as
`Kakeya.Tube.norm_chord_transverse_le_of_endpoints_mem_dilate` and
`Kakeya.Tube.one_sub_abs_inner_chord_le_of_endpoints_mem_dilate`, and are cited at ratio `1`
through `Kakeya.Tube.subset_dilate`.
-/

omit [MeasurableSpace E] [BorelSpace E] [Nontrivial E] in
/-- **The midpoint of two points of a tube lies near its centre** (blueprint
`lem:ml1bootCoverRescaleBall`, second sentence).

The first sentence, `V ⊆ closedBall V.center (1/2 + r)`, is already proved as
`Kakeya.Tube.carrier_subset_closedBall_midpoint`; this is the consequence for midpoints, which is
convexity of a closed ball.

This crude bound is what carries the large-`r` regime of
`Kakeya.Tube.norm_midpoint_sub_center_le_of_norm_chord_eq_one`; it says nothing useful when `r` is
small, the whole difficulty there being that `r + 1/2` is then not `O(r)`. -/
theorem norm_midpoint_sub_center_le_of_mem_carrier {r : NNReal} (V : Tube r E) {p q : E}
    (hp : p ∈ V.carrier) (hq : q ∈ V.carrier) :
    ‖midpoint ℝ p q - V.center‖ ≤ (r : ℝ) + 1 / 2 := by
  have hV : V.center = midpoint ℝ V.x V.y := rfl
  have hpc : p ∈ closedBall V.center (1 / 2 + (r : ℝ)) := by
    simpa [hV] using (carrier_subset_closedBall_midpoint (E := E) V) hp
  have hqc : q ∈ closedBall V.center (1 / 2 + (r : ℝ)) := by
    simpa [hV] using (carrier_subset_closedBall_midpoint (E := E) V) hq
  have hm : midpoint ℝ p q ∈ closedBall V.center (1 / 2 + (r : ℝ)) :=
    (convex_closedBall V.center (1 / 2 + (r : ℝ))).midpoint_mem hpc hqc
  rw [mem_closedBall, dist_eq_norm] at hm
  ring_nf at hm ⊢
  exact hm

omit [Nontrivial E] in
/-- **Longitudinal confinement: the axial coordinate of the midpoint** (blueprint
`lem:ml1bootCoverMidpointLongitudinal`).

**This is the step that spends the container's longitudinal room, and the one place in this file
where the container's being a concentric rescaling rather than a homothety is used.**  The axis
offers room `1/2 + r` on either side of the centre; the segment's own axial extent
`|⟪u, e⟫| / 2` is subtracted from it, and the second half of blueprint `lem:ml1bootUnitChordTilt`
— that is, `Kakeya.Tube.one_sub_abs_inner_chord_le_of_endpoints_mem_dilate` read at ratio `1`, which
gives `1 - 4 r ^ 2 ≤ |⟪u, e⟫|` — is what makes that extent nearly `1/2`, so what is left for the
midpoint to move in is `O(r)` and not `O(1)`.

At a homothety container the room is `Θ(c)` instead and **no analogue holds**: the sliding family
of blueprint `note:ml1bootHomothetyOverlapInsufficient` is exactly a family of unit segments whose
midpoints exhaust that room, and that is the longitudinal gap of blueprint
`note:ml1bootEnlargementTubeStatus`.

The hypothesis `2 r ≤ 1` is used only in the final step `2 r ^ 2 ≤ r` and is genuinely needed —
the bound `r + 2 r ^ 2` the argument produces is not `O(r)` without it — which is why
`Kakeya.Tube.norm_midpoint_sub_center_le_of_norm_chord_eq_one` has a second regime rather than
citing this lemma outright.  **No orientation choice is made**, the absolute values and
`Kakeya.abs_add_add_abs_sub_le_of_abs_le` doing that work. -/
theorem abs_inner_midpoint_sub_center_le_of_norm_chord_eq_one {r : NNReal} (V : Tube r E)
    (hr : 2 * (r : ℝ) ≤ 1) {p q : E} (hp : p ∈ V.carrier) (hq : q ∈ V.carrier)
    (hpq : ‖q - p‖ = 1) :
    |inner ℝ V.direction (midpoint ℝ p q - V.center)| ≤ 2 * (r : ℝ) := by
  let u : E := V.direction
  let c : E := V.center
  let a : ℝ := inner ℝ u (p - c)
  let b : ℝ := inner ℝ u (q - c)
  have hp1 : p ∈ (Kakeya.Tube.dilate V 1).carrier := Tube.subset_dilate V (by norm_num) hp
  have hq1 : q ∈ (Kakeya.Tube.dilate V 1).carrier := Tube.subset_dilate V (by norm_num) hq
  have hpcoord : |inner ℝ (p - V.center) V.direction| ≤ 1 / 2 + (r : ℝ) := by
    have h := (Tube.abs_inner_and_perp_le_of_mem_dilate V (c := 1) (by norm_num) hp1).1
    simpa using h
  have hqcoord : |inner ℝ (q - V.center) V.direction| ≤ 1 / 2 + (r : ℝ) := by
    have h := (Tube.abs_inner_and_perp_le_of_mem_dilate V (c := 1) (by norm_num) hq1).1
    simpa using h
  have ha : |a| ≤ 1 / 2 + (r : ℝ) := by
    dsimp [a, u, c]
    rw [real_inner_comm]
    exact hpcoord
  have hb : |b| ≤ 1 / 2 + (r : ℝ) := by
    dsimp [b, u, c]
    rw [real_inner_comm]
    exact hqcoord
  have hscalar := abs_add_add_abs_sub_le_of_abs_le ha hb
  have hxy : dist p q = 1 := by
    rw [dist_eq_norm']
    exact hpq
  have hba : b - a = inner ℝ u (q - p) := by
    dsimp [b, a]
    rw [← inner_sub_right]
    congr 1
    abel
  have hchord : 1 - |b - a| ≤ 4 * (r : ℝ) ^ 2 := by
    have h := Tube.one_sub_abs_inner_chord_le_of_endpoints_mem_dilate V (c := 1) (by norm_num) hxy hp1 hq1
    rw [hba]
    dsimp [u]
    simpa using h
  have hmid : inner ℝ u (midpoint ℝ p q - c) = (a + b) / 2 := by
    rw [midpoint_eq_smul_add, inner_sub_right, inner_smul_right, inner_add_right]
    dsimp [a, b]
    rw [inner_sub_right, inner_sub_right]
    norm_num
    ring
  have habe : |(a + b) / 2| = |a + b| / 2 := by
    rw [div_eq_mul_inv, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)]
    rfl
  have hfin' : |a + b| / 2 ≤ 2 * (r : ℝ) := by
    nlinarith [hscalar, hchord, hr, NNReal.coe_nonneg r]
  have hfin : |inner ℝ u (midpoint ℝ p q - c)| ≤ 2 * (r : ℝ) := by
    rw [hmid, habe]
    exact hfin'
  simpa [u, c] using hfin

omit [Nontrivial E] in
/-- **Longitudinal confinement: the midpoint of a unit segment in a rescaling** (blueprint
`lem:ml1bootCoverMidpointConfined`).

**This is the load-bearing statement of the file**, being what pins a leaf's midpoint to a
`θ`-scale neighbourhood of the axis midpoint and so makes the count of
`Kakeya.ml1Boot.enlargementCoverConstant` finite.  The conclusion is `O(r)` and **not** `O(1)`; the
place where the container's shape is spent is its axial half,
`Kakeya.Tube.abs_inner_midpoint_sub_center_le_of_norm_chord_eq_one`, whose docstring records why no
analogue holds at a homothety container.  What this lemma adds is the second regime `2 r > 1`,
where `Kakeya.Tube.norm_midpoint_sub_center_le_of_mem_carrier` gives `r + 1/2 < 2 r`, and the
assembly of the two halves through `Kakeya.inner_sq_add_norm_transverse_sq_eq`.

The numeral `4` is not sharp and is chosen so that one numeral serves here and at
`Kakeya.Tube.min_norm_chord_sub_direction_le`: the argument gives `√5 r` in the small regime. -/
theorem norm_midpoint_sub_center_le_of_norm_chord_eq_one {r : NNReal} (V : Tube r E) {p q : E}
    (hp : p ∈ V.carrier) (hq : q ∈ V.carrier) (hpq : ‖q - p‖ = 1) :
    ‖midpoint ℝ p q - V.center‖ ≤ 4 * (r : ℝ) := by
  rcases le_or_gt (2 * (r : ℝ)) 1 with hr | hr
  · -- small regime: 2 * r ≤ 1
    let z : E := midpoint ℝ p q - V.center
    set u : E := V.direction
    have hu : ‖u‖ = 1 := by simpa [u] using V.norm_direction
    have hax : |inner ℝ u z| ≤ 2 * (r : ℝ) := by
      have h0 := abs_inner_midpoint_sub_center_le_of_norm_chord_eq_one V hr hp hq hpq
      simpa [u, z] using h0
    -- transverse components at p and at q, via the 1-dilate of V
    have hpp : ‖(p - V.center) - inner ℝ u (p - V.center) • u‖ ≤ (r : ℝ) := by
      have hp1 : p ∈ (Kakeya.Tube.dilate V (1 : ℝ)).carrier :=
        Tube.subset_dilate V (by norm_num : (1 : ℝ) ≤ (1 : ℝ)) hp
      have h0 := (Tube.abs_inner_and_perp_le_of_mem_dilate V (c := (1 : ℝ))
        (by norm_num : 0 < (1 : ℝ)) hp1).2
      simpa [u, one_mul] using h0
    have hqq : ‖(q - V.center) - inner ℝ u (q - V.center) • u‖ ≤ (r : ℝ) := by
      have hq1 : q ∈ (Kakeya.Tube.dilate V (1 : ℝ)).carrier :=
        Tube.subset_dilate V (by norm_num : (1 : ℝ) ≤ (1 : ℝ)) hq
      have h0 := (Tube.abs_inner_and_perp_le_of_mem_dilate V (c := (1 : ℝ))
        (by norm_num : 0 < (1 : ℝ)) hq1).2
      simpa [u, one_mul] using h0
    -- the transverse part of the midpoint is the midpoint of the transverse parts
    have hmid : midpoint ℝ p q - V.center = (2⁻¹ : ℝ) • ((p - V.center) + (q - V.center)) := by
      rw [midpoint_eq_smul_add]
      norm_num
      module
    have hid : z - inner ℝ u z • u =
        (2⁻¹ : ℝ) • (((p - V.center) - inner ℝ u (p - V.center) • u) +
          ((q - V.center) - inner ℝ u (q - V.center) • u)) := by
      dsimp [z]
      rw [hmid]
      simp only [inner_sub_right, inner_add_right, real_inner_smul_right]
      module
    have htr : ‖z - inner ℝ u z • u‖ ≤ (r : ℝ) := by
      rw [hid]
      have hsum : ‖((p - V.center) - inner ℝ u (p - V.center) • u) +
            ((q - V.center) - inner ℝ u (q - V.center) • u)‖ ≤ (r : ℝ) + (r : ℝ) := by
        exact (norm_add_le _ _).trans (add_le_add hpp hqq)
      calc
        ‖(2⁻¹ : ℝ) • (((p - V.center) - inner ℝ u (p - V.center) • u) +
            ((q - V.center) - inner ℝ u (q - V.center) • u))‖
          = (2⁻¹ : ℝ) * ‖((p - V.center) - inner ℝ u (p - V.center) • u) +
              ((q - V.center) - inner ℝ u (q - V.center) • u)‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by norm_num : 0 ≤ (2⁻¹ : ℝ))]
        _ ≤ (2⁻¹ : ℝ) * ((r : ℝ) + (r : ℝ)) :=
          mul_le_mul_of_nonneg_left hsum (by norm_num : 0 ≤ (2⁻¹ : ℝ))
        _ = (r : ℝ) := by ring
    -- assemble the axial and transverse parts
    have hpy := Kakeya.inner_sq_add_norm_transverse_sq_eq hu z
    have hl1 : (inner ℝ u z) ^ 2 ≤ (2 * (r : ℝ)) ^ 2 := by
      have hnon2 : 0 ≤ 2 * (r : ℝ) := by positivity
      exact (sq_le_sq.mpr (by simpa [abs_of_nonneg hnon2] using hax))
    have ht_sq : ‖z - inner ℝ u z • u‖ ^ 2 ≤ (r : ℝ) ^ 2 := by
      exact (sq_le_sq.mpr (by simpa [abs_of_nonneg (NNReal.coe_nonneg r), abs_of_nonneg (norm_nonneg _)] using htr))
    have hsq : ‖z‖ ^ 2 ≤ (4 * (r : ℝ)) ^ 2 := by
      nlinarith [hl1, ht_sq, hpy, sq_nonneg (r : ℝ)]
    exact (le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) (by positivity) hsq)
  · -- large regime: 1 < 2 * r
    have hm := norm_midpoint_sub_center_le_of_mem_carrier V hp hq
    calc
      ‖midpoint ℝ p q - V.center‖ ≤ (r : ℝ) + 1 / 2 := hm
      _ ≤ 4 * (r : ℝ) := by nlinarith [NNReal.coe_nonneg r, hr]

omit [Nontrivial E] in
/-- **Angular confinement: the direction of a unit segment in a rescaling** (blueprint
`lem:ml1bootCoverDirectionConfined`).

The minimum over the two orientations is the statement, and not a weakening of one: a segment has
no orientation, and the two labellings `[p, q]` and `[q, p]` of the core of a tube give opposite
chords.

This replaces the *angular* net of blueprint `def:ml1bootNeighbouringParentsConstant` by an ambient
one: the conclusion is a bound in `E` on the difference of two unit vectors, not a bound on an
angle, so the net used against it in `Kakeya.ml1Boot.isEnlargementCover_rescale` is a net of a ball
of `E` and **no net of a sphere or of a set of angles is constructed anywhere**.  That is what
makes the direction parameter and the centre parameter netted by the *same* finite set, and hence
what makes `Kakeya.ml1Boot.enlargementCoverConstant` a square rather than a product of two
unrelated counts.

**No regime split occurs**: the bound `1 - 4 r ^ 2 ≤ |⟪u, e⟫|` this cites — the second half of
blueprint `lem:ml1bootUnitChordTilt`, that is
`Kakeya.Tube.one_sub_abs_inner_chord_le_of_endpoints_mem_dilate` at ratio `1` — is vacuous exactly
when `2 r > 1`, and the chain stays valid there. -/
theorem min_norm_chord_sub_direction_le {r : NNReal} (V : Tube r E) {p q : E} (hp : p ∈ V.carrier)
    (hq : q ∈ V.carrier) (hpq : ‖q - p‖ = 1) :
    min ‖q - p - V.direction‖ ‖q - p + V.direction‖ ≤ 4 * (r : ℝ) := by
  set e : E := q - p
  set u : E := V.direction
  have he : ‖e‖ = 1 := by simpa [e] using hpq
  have hu : ‖u‖ = 1 := by simpa [u] using V.norm_direction
  have hi : 1 - |inner ℝ u e| ≤ 4 * (r : ℝ) ^ 2 := by
    have hdist : dist p q = 1 := by
      rwa [dist_eq_norm']
    have hmain : 1 - |inner ℝ V.direction (q - p)| ≤ 4 * 1 ^ 2 * (r : ℝ) ^ 2 :=
      one_sub_abs_inner_chord_le_of_endpoints_mem_dilate V (by norm_num : 0 < (1 : ℝ)) hdist
        (Tube.subset_dilate V (by norm_num : 1 ≤ (1 : ℝ)) hp)
        (Tube.subset_dilate V (by norm_num : 1 ≤ (1 : ℝ)) hq)
    simpa [u, e] using hmain
  have hsub_sq : ‖e - u‖ ^ 2 = 2 - 2 * inner ℝ u e := by
    calc
      ‖e - u‖ ^ 2 = ‖e‖ ^ 2 - 2 * inner ℝ e u + ‖u‖ ^ 2 := by
        simpa using (norm_sub_sq_real e u)
      _ = 2 - 2 * inner ℝ e u := by nlinarith [he, hu]
      _ = 2 - 2 * inner ℝ u e := by rw [real_inner_comm u e]
  have hadd_sq : ‖e + u‖ ^ 2 = 2 + 2 * inner ℝ u e := by
    calc
      ‖e + u‖ ^ 2 = ‖e‖ ^ 2 + 2 * inner ℝ e u + ‖u‖ ^ 2 := by
        simpa using (norm_add_sq_real e u)
      _ = 2 + 2 * inner ℝ e u := by nlinarith [he, hu]
      _ = 2 + 2 * inner ℝ u e := by rw [real_inner_comm u e]
  have hle_of_sq : ∀ {a : ℝ}, 0 ≤ a → a ^ 2 ≤ (4 * (r : ℝ)) ^ 2 → a ≤ 4 * (r : ℝ) := by
    intro a ha0 hsq
    exact le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0)
      (by positivity : 0 ≤ 4 * (r : ℝ)) hsq
  rcases le_or_gt 0 (inner ℝ u e) with hpos | hneg
  · have ha : |inner ℝ u e| = inner ℝ u e := abs_of_nonneg hpos
    have hine : 1 - 4 * (r : ℝ) ^ 2 ≤ inner ℝ u e := by nlinarith [hi, ha]
    have hsq : ‖e - u‖ ^ 2 ≤ (4 * (r : ℝ)) ^ 2 := by
      calc
        ‖e - u‖ ^ 2 = 2 - 2 * inner ℝ u e := hsub_sq
        _ ≤ 2 - 2 * (1 - 4 * (r : ℝ) ^ 2) := by nlinarith [hine]
        _ = 8 * (r : ℝ) ^ 2 := by ring
        _ ≤ (4 * (r : ℝ)) ^ 2 := by nlinarith [sq_nonneg (r : ℝ)]
    exact le_trans (min_le_left _ _) (hle_of_sq (norm_nonneg _) hsq)
  · have ha : |inner ℝ u e| = -inner ℝ u e := abs_of_neg hneg
    have hine : inner ℝ u e ≤ 4 * (r : ℝ) ^ 2 - 1 := by nlinarith [hi, ha]
    have hsq : ‖e + u‖ ^ 2 ≤ (4 * (r : ℝ)) ^ 2 := by
      calc
        ‖e + u‖ ^ 2 = 2 + 2 * inner ℝ u e := hadd_sq
        _ ≤ 2 + 2 * (4 * (r : ℝ) ^ 2 - 1) := by nlinarith [hine]
        _ = 8 * (r : ℝ) ^ 2 := by ring
        _ ≤ (4 * (r : ℝ)) ^ 2 := by nlinarith [sq_nonneg (r : ℝ)]
    exact le_trans (min_le_right _ _) (hle_of_sq (norm_nonneg _) hsq)

/-! ### The three moves the producer makes on a single leaf

From a containment of tubes to oriented endpoint data
(`Kakeya.Tube.exists_core_endpoints_of_subset`), from that data to a pair of net points
(`Kakeya.Tube.exists_net_parameters`), and from the net points back to a containment of tubes —
that third move is `Kakeya.Tube.subset_ofMidpointDirection_of_dist_params_le`, which is stated in
the core block above.  They are stated separately so that
`Kakeya.ml1Boot.isEnlargementCover_rescale` is the construction of the family and nothing else.
-/

omit [Nontrivial E] in
/-- **Endpoints of a leaf, oriented along the axis** (blueprint
`lem:ml1bootCoverLeafEndpoints`).

This is the passage from the hypothesis the producer is handed — a containment of tubes — to the
oriented, endpointwise data that `Kakeya.Tube.exists_net_parameters` consumes, and it is the only
place where an orientation of a core is chosen.

The core is asked for as an equality of **sets** because that is all that is used downstream and
all that survives the exchange of `p` and `q`: no second `Tube` is produced and `Tube.reverse` does
not occur.  Nothing here needs a relation between `δ` and `r`, and `δ` enters only as the radius
of `T`. -/
theorem exists_core_endpoints_of_subset {δ r : NNReal} (V : Tube r E) (T : Tube δ E)
    (hT : T.carrier ⊆ V.carrier) :
    ∃ p q : E, segment ℝ p q = segment ℝ T.x T.y ∧ p ∈ V.carrier ∧ q ∈ V.carrier ∧
      ‖q - p‖ = 1 ∧ ‖q - p - V.direction‖ ≤ 4 * (r : ℝ) := by
  have hx : T.x ∈ V.carrier := hT (Tube.x_mem_carrier T)
  have hy : T.y ∈ V.carrier := hT (Tube.y_mem_carrier T)
  have hxy : ‖T.y - T.x‖ = 1 := by
    simpa [dist_eq_norm'] using (T.dist_eq_one : dist T.x T.y = 1)
  have hmin : min ‖T.y - T.x - V.direction‖ ‖T.y - T.x + V.direction‖ ≤ 4 * (r : ℝ) :=
    min_norm_chord_sub_direction_le V hx hy hxy
  rcases (min_le_iff.mp hmin) with h1 | h2
  · refine ⟨T.x, T.y, rfl, hx, hy, hxy, h1⟩
  · refine ⟨T.y, T.x, segment_symm ℝ T.y T.x, hy, hx, ?_, ?_⟩
    · rwa [norm_sub_rev]
    · rw [show T.x - T.y - V.direction = -(T.y - T.x + V.direction) by abel, norm_neg]
      exact h2

omit [Nontrivial E] in
/-- **Net parameters for a leaf** (blueprint `lem:ml1bootCoverLeafParameters`).

**One net, used twice** — once at the centre and once at the direction — and that is what makes
`Kakeya.ml1Boot.enlargementCoverConstant` a square rather than a product of two unrelated counts.
It is also why `N` is carried as a hypothesis rather than constructed:
`Kakeya.exists_finset_nonempty_forall_exists_norm_sub_le` is an existence statement, and the choice
of witness is made once, at `Kakeya.ml1Boot.enlargementCoverNet`.  Finiteness of `N` is not used.

The two tolerances differ by a factor `2` because the direction parameter has to be normalized to
unit length before it can be a core (`Kakeya.norm_sub_normalizeWith_le`) and the centre parameter
does not.  The hypothesis `hdir` is the last conclusion of
`Kakeya.Tube.exists_core_endpoints_of_subset`, and it is what lets the direction be netted at the
**same** radius `4 Λ` as the centre. -/
theorem exists_net_parameters (Λ θ : NNReal) (V : Tube (Λ * θ) E) {N : Set E} (hN : N.Nonempty)
    (hnet : ∀ y : E, ‖y‖ ≤ 4 * (Λ : ℝ) → ∃ v ∈ N, ‖y - v‖ ≤ 1 / 16) {p q : E}
    (hp : p ∈ V.carrier) (hq : q ∈ V.carrier) (hpq : ‖q - p‖ = 1)
    (hdir : ‖q - p - V.direction‖ ≤ 4 * ((Λ : ℝ) * (θ : ℝ))) :
    ∃ v ∈ N, ∃ v' ∈ N,
      ‖midpoint ℝ p q - (V.center + (θ : ℝ) • v)‖ ≤ (θ : ℝ) / 16 ∧
      ‖q - p - normalizeWith V.direction (V.direction + (θ : ℝ) • v')‖ ≤ (θ : ℝ) / 8 := by
  have hθ : 0 ≤ (θ : ℝ) := NNReal.coe_nonneg θ
  -- CENTRE: net the midpoint of the chord against N at the centre.
  have hcentre : ‖midpoint ℝ p q - V.center‖ ≤ (θ : ℝ) * (4 * (Λ : ℝ)) := by
    have hc := norm_midpoint_sub_center_le_of_norm_chord_eq_one V hp hq hpq
    calc
      ‖midpoint ℝ p q - V.center‖ ≤ 4 * ((Λ * θ : NNReal) : ℝ) := hc
      _ = (θ : ℝ) * (4 * (Λ : ℝ)) := by rw [NNReal.coe_mul]; ring
  rcases exists_mem_norm_sub_add_smul_le (R := 4 * (Λ : ℝ)) (ε := 1 / 16) hθ hN hnet
      (a := V.center) (z := midpoint ℝ p q) hcentre with ⟨v, hv, hvle⟩
  -- DIRECTION: net the direction of the configuration from N at the direction.
  have hdir' : ‖(q - p) - V.direction‖ ≤ (θ : ℝ) * (4 * (Λ : ℝ)) := by
    nlinarith [hdir]
  rcases exists_mem_norm_sub_add_smul_le (R := 4 * (Λ : ℝ)) (ε := 1 / 16) hθ hN hnet
      (a := V.direction) (z := q - p) hdir' with ⟨v', hv', hv'le⟩
  refine ⟨v, hv, v', hv', ?_, ?_⟩
  · -- centre bound: θ * (1/16) = θ/16
    have hdiv : (θ : ℝ) * (1 / 16 : ℝ) = (θ : ℝ) / 16 := by ring
    rwa [← hdiv]
  · -- direction bound: normalize at cost of a factor two
    have hdu : ‖V.direction‖ = 1 := V.norm_direction
    have hvle16 : ‖(q - p) - (V.direction + (θ : ℝ) • v')‖ ≤ (θ : ℝ) / 16 := by
      calc
        ‖(q - p) - (V.direction + (θ : ℝ) • v')‖ ≤ (θ : ℝ) * (1 / 16 : ℝ) := hv'le
        _ = (θ : ℝ) / 16 := by ring
    have h1 := norm_sub_normalizeWith_le (e := q - p) (u := V.direction)
      (w := V.direction + (θ : ℝ) • v') (s := (θ : ℝ) / 16) hpq hdu hvle16
    calc
      ‖q - p - normalizeWith V.direction (V.direction + (θ : ℝ) • v')‖ ≤ 2 * ((θ : ℝ) / 16) := h1
      _ = (θ : ℝ) / 8 := by ring

end Tube

namespace ml1Boot

/-! ### The constant, and the producer -/

/-- **The net underlying the covering constant** (blueprint
`def:ml1bootEnlargementCoverConstant`): one *chosen* finite nonempty `1/16`-net of the closed ball
of radius `4 Λ` about the origin of `E`, fixed once and for all.

`Kakeya.exists_finset_nonempty_forall_exists_norm_sub_le` is existentially quantified, so a witness
has to be chosen; this is that choice.  The radius `4 Λ` is the numeral of
`Kakeya.Tube.norm_midpoint_sub_center_le_of_norm_chord_eq_one` and
`Kakeya.Tube.min_norm_chord_sub_direction_le` divided by `θ`, and the spacing `1/16` is `1/8`
halved to pay for the normalization of `Kakeya.norm_sub_normalizeWith_le`. -/
noncomputable def enlargementCoverNet (E : Type*) [NormedAddCommGroup E] [ProperSpace E]
    (Λ : NNReal) : Finset E :=
  (exists_finset_nonempty_forall_exists_norm_sub_le E (R := 4 * (Λ : ℝ)) (ε := 1 / 16)
    (by norm_num)).choose

/-- **The covering constant** `M(E, Λ)` (blueprint `def:ml1bootEnlargementCoverConstant`), the
square of the cardinality of `Kakeya.ml1Boot.enlargementCoverNet`.

The square is the two parameters of a unit segment, the centre and the direction, each netted by
the **same** set — the centre after translation to the centre of `W` and the direction after
translation to the direction of `W`, both after scaling by `θ`.  That is what makes one net serve
both and makes the count independent of `θ`.

This quantity depends on `E` and on `Λ` and **on nothing else**: not on `θ`, not on `δ`, not on the
tube `W`, not on the family and not on the index set.  It is indexed by the ambient space rather
than by a dimension because the finiteness above comes from compactness of a ball of `E` and no
isometry-invariance statement is made or needed.

**It is not the `M(n, Λ)` of blueprint `def:ml1bootNeighbouringParentsConstant`, only an upper
bound for it.**  That `M(n, Λ)` is the *least* integer admitting a covering family, whereas this is
*one* admissible value and depends on the choice of net made in
`Kakeya.ml1Boot.enlargementCoverNet`; what holds is `M(n, Λ) ≤ enlargementCoverConstant (ℝ^n) Λ`.
Its worth is that the right-hand side exists at all, which is what makes that "least integer"
well defined, and what witnesses this is the family-first
`Kakeya.ml1Boot.exists_cover_of_subset_rescale` and **not** its packaging
`Kakeya.ml1Boot.isEnlargementCover_rescale`, which covers the members of one finite indexed family
and so exhibits no admissible integer in the sense of that definition.

**It is not an explicit numeral.**  `Kakeya.exists_finset_nonempty_forall_exists_norm_sub_le`
asserts no cardinality bound, so no bound of the form `(C Λ) ^ (2 n)` is available here; a consumer
needing a numeral would have to add a covering-number estimate this development does not contain.
The prose of blueprint `def:ml1bootNeighbouringParentsConstant` likewise counts its nets only up to
`O_{n,Λ}(1)`. -/
noncomputable def enlargementCoverConstant (E : Type*) [NormedAddCommGroup E] [ProperSpace E]
    (Λ : NNReal) : ℕ :=
  (enlargementCoverNet E Λ).card ^ 2

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

omit [Nontrivial E] in
/-- **(GWZ Step 5a item (a)) A covering family for *all* leaves of a rescaling** (blueprint
`lem:ml1bootEnlargementCoverFamily`).

**This is the form blueprint `def:ml1bootNeighbouringParentsConstant` actually asserts.**  The
covering family `V` is quantified **before** the tubes it covers: `V` is produced from `W`, from
`θ` and from `Kakeya.ml1Boot.enlargementCoverNet` alone, and the covered `T` then ranges over
*every* `δ`-tube of the container `W.rescale (Λ * θ)` — no index set, no indexed family, and no
restriction to finitely many leaves, of which there are in fact a continuum.  It is this
quantifier order that makes the "least integer admitting a covering family" of that definition
well posed at all, and hence what makes
`C_{lem:ml1bootNeighbouringParents}(3, Λ, C_ds) = M(3, Λ) C_ds` well defined and finite.

`Kakeya.ml1Boot.isEnlargementCover_rescale` below is the **packaging** of this same family as the
hypothesis `Kakeya.ml1Boot.IsEnlargementCover`, which quantifies the covering tubes *after* a
finite indexed family of leaves and is therefore **strictly weaker as a statement**; deriving it
from this one is a weakening of the quantifier order and nothing else.

**The constant is the same** `Kakeya.ml1Boot.enlargementCoverConstant E Λ`, a term in `E` and `Λ`
alone: it depends on the ambient space and on the enlargement factor and **on nothing else** — not
on `θ`, not on `δ`, not on `W`, and here not on any index set because there is none.

Everything said at `Kakeya.ml1Boot.isEnlargementCover_rescale` about the shape of the container —
that it is the concentric rescaling of blueprint `note:ml1bootTwoDilates` and **not** a homothety,
which the sliding configuration of blueprint `note:ml1bootHomothetyOverlapInsufficient` defeats —
about what is asked of the scales, and about keeping the covering radius at exactly `θ`, applies
verbatim here and is not repeated. -/
theorem exists_cover_of_subset_rescale (Λ : NNReal) {θ δ : NNReal} (hδθ : 2 * (δ : ℝ) ≤ (θ : ℝ))
    (W : Tube θ E) :
    ∃ V : Fin (enlargementCoverConstant E Λ) → Tube θ E,
      ∀ T : Tube δ E, T.toConvexSpaceBody ≤ (W.rescale (Λ * θ)).toConvexSpaceBody →
        ∃ q : Fin (enlargementCoverConstant E Λ),
          T.toConvexSpaceBody ≤ (V q).toConvexSpaceBody := by
  classical
  let N : Finset E := enlargementCoverNet E Λ
  have hNspec : (enlargementCoverNet E Λ).Nonempty ∧
      ∀ z : E, ‖z‖ ≤ 4 * (Λ : ℝ) → ∃ v ∈ enlargementCoverNet E Λ, ‖z - v‖ ≤ 1 / 16 := by
    exact Exists.choose_spec (exists_finset_nonempty_forall_exists_norm_sub_le E
      (R := 4 * (Λ : ℝ)) (ε := 1 / 16) (by norm_num))
  have hN1 : N.Nonempty := by simpa [N] using hNspec.1
  have hN2 : ∀ z : E, ‖z‖ ≤ 4 * (Λ : ℝ) → ∃ v ∈ N, ‖z - v‖ ≤ 1 / 16 := by
    intro z hz
    rcases hNspec.2 z hz with ⟨v, hv, hvle⟩
    exact ⟨v, by simpa [N] using hv, hvle⟩
  have hN1' : ((N : Finset E) : Set E).Nonempty := by simpa using hN1
  have hN2' : ∀ y : E, ‖y‖ ≤ 4 * (Λ : ℝ) → ∃ v ∈ (N : Set E), ‖y - v‖ ≤ 1 / 16 := by
    intro y hy
    rcases hN2 y hy with ⟨v, hv, hvle⟩
    exact ⟨v, by simpa using hv, hvle⟩
  have hM : enlargementCoverConstant E Λ = N.card * N.card := by
    unfold enlargementCoverConstant
    rw [sq]
  let V₀ : Tube (Λ * θ) E := W.rescale (Λ * θ)
  let f : E × E → Tube θ E := fun z =>
    Tube.ofMidpointDirection θ
      (V₀.center + (θ : ℝ) • z.1)
      (normalizeWith V₀.direction (V₀.direction + (θ : ℝ) • z.2))
      (Kakeya.norm_normalizeWith V₀.norm_direction (V₀.direction + (θ : ℝ) • z.2))
  let idx : Fin (enlargementCoverConstant E Λ) → E × E := fun i =>
    let jk := finProdFinEquiv.symm (Fin.cast hM i)
    ((N.equivFin.symm jk.1 : E), (N.equivFin.symm jk.2 : E))
  let V : Fin (enlargementCoverConstant E Λ) → Tube θ E := fun j => f (idx j)
  refine ⟨V, ?_⟩
  intro T hT
  have hT' : T.carrier ⊆ V₀.carrier := by
    change T.toConvexSpaceBody ≤ V₀.toConvexSpaceBody
    simpa [V₀] using hT
  rcases Kakeya.Tube.exists_core_endpoints_of_subset V₀ T hT' with ⟨p, q, hcore, hp, hq, hpq, hdir⟩
  have hdir' : ‖q - p - V₀.direction‖ ≤ 4 * ((Λ : ℝ) * (θ : ℝ)) := by
    simpa [NNReal.coe_mul] using hdir
  rcases Kakeya.Tube.exists_net_parameters Λ θ V₀ hN1' hN2' hp hq hpq hdir' with
      ⟨v, hv, v', hv', hvle_m, hvle_d⟩
  have hvN : v ∈ N := by simpa using hv
  have hv'N : v' ∈ N := by simpa using hv'
  let j : Fin (enlargementCoverConstant E Λ) :=
    Fin.cast hM.symm (finProdFinEquiv (N.equivFin ⟨v, hvN⟩, N.equivFin ⟨v', hv'N⟩))
  have hroundtrip :
      Fin.cast hM (Fin.cast hM.symm (finProdFinEquiv (N.equivFin ⟨v, hvN⟩, N.equivFin ⟨v', hv'N⟩)))
        = finProdFinEquiv (N.equivFin ⟨v, hvN⟩, N.equivFin ⟨v', hv'N⟩) := by
    simp
  have hJK : finProdFinEquiv.symm
      (finProdFinEquiv (N.equivFin ⟨v, hvN⟩, N.equivFin ⟨v', hv'N⟩)) =
      (N.equivFin ⟨v, hvN⟩, N.equivFin ⟨v', hv'N⟩) :=
    Equiv.symm_apply_apply finProdFinEquiv _
  have hj : idx j = (v, v') := by
    apply Prod.ext
    · change ((N.equivFin.symm
          (finProdFinEquiv.symm (Fin.cast hM
            (Fin.cast hM.symm (finProdFinEquiv (N.equivFin ⟨v, hvN⟩, N.equivFin ⟨v', hv'N⟩))))).1)
          : E) = v
      rw [hroundtrip, hJK]
      simp
    · change ((N.equivFin.symm
          (finProdFinEquiv.symm (Fin.cast hM
            (Fin.cast hM.symm (finProdFinEquiv (N.equivFin ⟨v, hvN⟩, N.equivFin ⟨v', hv'N⟩))))).2)
          : E) = v'
      rw [hroundtrip, hJK]
      simp
  have he' : ‖normalizeWith V₀.direction (V₀.direction + (θ : ℝ) • v')‖ = 1 :=
    Kakeya.norm_normalizeWith V₀.norm_direction (V₀.direction + (θ : ℝ) • v')
  have hδθ' : 8 * (δ : ℝ) ≤ 7 * (θ : ℝ) := by
    linarith [NNReal.coe_nonneg θ]
  have hcover : T.carrier ⊆ (f (v, v')).carrier := by
    simpa [f] using
      (Kakeya.Tube.subset_ofMidpointDirection_of_dist_params_le hδθ' T hcore he' hvle_m hvle_d)
  have hcv : T.toConvexSpaceBody ≤ (f (v, v')).toConvexSpaceBody := by
    change T.carrier ⊆ (f (v, v')).carrier
    exact hcover
  refine ⟨j, ?_⟩
  simpa [V, hj] using hcv

omit [Nontrivial E] in
/-- **(GWZ Step 5a item (a)) The covering family exists at a concentric rescaling** (blueprint
`lem:ml1bootEnlargementCoverExists`).

**This is the first producer of `Kakeya.ml1Boot.IsEnlargementCover` in this development.**

**The count is uniform in everything but `E` and `Λ`.**  `Kakeya.ml1Boot.enlargementCoverConstant
E Λ` is a term in `E` and `Λ` alone, so it cannot depend on `θ`, on `δ`, on `W`, on the index set
or on the family whatever the binder order.  The binders below are ordered to display it, and `Λ`
is taken explicit for the same reason.

**What this does not say.**  The covering tubes are quantified *inside* `IsEnlargementCover`, hence
*after* the finite indexed family `T`, so this statement is weaker than the assertion of blueprint
`def:ml1bootNeighbouringParentsConstant`, which names the covering family before the tubes it
covers and covers *every* `δ`-tube of the container, of which there are infinitely many.  That
family-first form is blueprint `lem:ml1bootEnlargementCoverFamily`, proved above as
`Kakeya.ml1Boot.exists_cover_of_subset_rescale`, and **this statement is derived from it**: the
proof below is the quantifier-order weakening and nothing else, the covering family being the one
that declaration produces from `W`, `θ` and `Kakeya.ml1Boot.enlargementCoverNet` alone, read at
`T i` for each `i ∈ s'`.  So the stronger form is what the development carries, and this is its
packaging in the shape the consumers' hypothesis is written in.

Read with `θ = ρ_a` the coarse grid radius and `W` a `ρ_a`-tube, this discharges the
hypothesis of `Kakeya.ml1Boot.card_neighbouringParents_le_of_cover`, and with it the same
hypothesis in `Kakeya.ml1Boot.card_completedFibreParents_le`,
`Kakeya.ml1Boot.card_completedFibre_le` and `Kakeya.ml1Boot.densityIn_le_of_neighbouringParents`.
**No consumer is instantiated here.**

**Container shape.**  The container is the concentric rescaling `W.rescale (Λ * θ)`, which keeps
the unit core of `W` and has longitudinal extent `1 + 2 Λ θ`.  It is **not** a homothety and this
lemma may not be read at one: `Kakeya.Tube.abs_inner_midpoint_sub_center_le_of_norm_chord_eq_one`,
the step that pins the leaf longitudinally, is false at a homothety `c • V` with `c > 1` fixed, by
the sliding configuration of blueprint `note:ml1bootHomothetyOverlapInsufficient`.  So this does
not close the longitudinal gap of blueprint `note:ml1bootEnlargementTubeStatus`, and nothing here
bears on hypothesis (R1) of `Kakeya.ml1Boot.card_neighbouringParents_le_of_essDistinct`.

**What is asked of the scales, and what is not.**  `2 δ ≤ θ` is the hypothesis of blueprint
`def:ml1bootNeighbouringParentsConstant` and it is genuinely needed — a continuum of `θ`-tubes of
unit length lies in the container and no two of them are nested, so the covered family may not be
widened to all tubes of radius at most `θ`.  The proof uses only the weaker `8 δ ≤ 7 θ` of
`Kakeya.Tube.subset_ofMidpointDirection_of_dist_params_le`; the stronger form is kept so that the
statement agrees with the definition it discharges.  No lower or upper bound on `θ`, no relation
between `δ` and `1`, and no lower bound on `Λ` is used; in particular `θ = 0` is admitted, where
every bound reads `≤ 0` and the covering family degenerates to repetitions of `W` itself.  The
consumers all read this at `Λ ≥ 1`, which is not needed.

**Keeping the covering radius at exactly `θ` is part of the conclusion and not a normalization**:
the clause that converts a cover into a node count,
`Tube.UniformTubeSet.boundedOverlap`, is asserted only at tubes of the exact grid radius.
Nothing asks `W` itself to have radius `θ` either — only its core enters, through the rescaling —
and it is displayed as a `θ`-tube only because that is how the consumers present it.

The family is the one built inside `Kakeya.ml1Boot.exists_cover_of_subset_rescale`, indexed by
`enlargementCoverNet E Λ ×ˢ enlargementCoverNet E Λ`, its member at `(v, v')` being
`Tube.ofMidpointDirection θ (W.center + θ • v) (normalizeWith W.direction (W.direction + θ • v'))`;
only its cardinality is claimed not to depend on `W` and `θ`. -/
theorem isEnlargementCover_rescale {ι : Type*} (Λ : NNReal) {θ δ : NNReal}
    (hδθ : 2 * (δ : ℝ) ≤ (θ : ℝ)) (W : Tube θ E) (s' : Finset ι) (T : ι → Tube δ E) :
    IsEnlargementCover s' T θ (W.rescale (Λ * θ)).toConvexSpaceBody
      (enlargementCoverConstant E Λ) := by
  obtain ⟨V, hV⟩ := exists_cover_of_subset_rescale (δ := δ) Λ hδθ W
  exact ⟨V, fun i _ hTi => hV (T i) hTi⟩

/-! ### Drawing the edge: the producer read at a coarse node of the grid

Blueprint `lem:ml1bootNeighbouringParents`.  The producer above is stated at an arbitrary
`θ`-tube `W` and an arbitrary `θ` subject to `2 δ ≤ θ`.  Read at `θ = ρ_a` the coarse grid scale
and at `W = P_a(l)` a coarse node tube, it discharges the covering hypothesis of all four
consumers, and the count `M` becomes the term `Kakeya.ml1Boot.enlargementCoverConstant E Λ`.

**`a < N` is not decoration.**  `Tube.gridScale δ N N = δ`, so at `a = N` the producer's
hypothesis `2 δ ≤ ρ_a` reads `2 δ ≤ δ` and fails for every `δ > 0`.  Nor is `a < N` by itself
enough: `ρ_a ≥ ρ_{N-1} = δ / δ ^ (1/N)`, so `2 δ ≤ ρ_a` needs `δ ^ (1/N) ≤ 1/2` as well.  The two
lemmas below separate those two facts, and the smallness is asked in the form
`δ ≤ 16 ^ (-N)` that `Tube.exists_uniformTubeSet_subfamily` already uses. -/

section Edge

open MeasureTheory ConvexSpaceBody StickyKakeya _root_.Tube Convexity
open _root_.StickyKakeya

/-- **The `1/N`-th grid scale is small when `δ` is.**

`gridScale δ N 1 = δ ^ (1/N) ≤ (16 ^ (-N)) ^ (1/N) = 1/16`. -/
theorem two_mul_gridScale_one_le_one {δ : NNReal} {N : ℕ} (hN : 0 < N)
    (hδ : δ ≤ (16 : NNReal) ^ (-(N : ℝ))) :
    2 * gridScale δ N 1 ≤ 1 := by
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast hN
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  have hgrid : gridScale δ N 1 = δ ^ (((1 : ℕ) : ℝ) / (N : ℝ)) := rfl
  have he : 0 ≤ (((1 : ℕ) : ℝ) / (N : ℝ)) := by positivity
  have hδpow : δ ^ (((1 : ℕ) : ℝ) / (N : ℝ)) ≤
      (16 : NNReal) ^ (-(N : ℝ) * (((1 : ℕ) : ℝ) / (N : ℝ))) := by
    have h₁ : δ ^ (((1 : ℕ) : ℝ) / (N : ℝ)) ≤
        ((16 : NNReal) ^ (-(N : ℝ))) ^ (((1 : ℕ) : ℝ) / (N : ℝ)) :=
      NNReal.rpow_le_rpow hδ he
    rwa [← NNReal.rpow_mul] at h₁
  have hshift : (16 : NNReal) ^ (-(N : ℝ) * (((1 : ℕ) : ℝ) / (N : ℝ))) =
      (16 : NNReal) ^ (-1 : ℝ) := by
    congr 1
    rw [show (-(N : ℝ) * (((1 : ℕ) : ℝ) / (N : ℝ)) : ℝ) = -((N : ℝ) / (N : ℝ)) by ring]
    rw [div_self hNne]
  have hle : gridScale δ N 1 ≤ (16 : NNReal) ^ (-1 : ℝ) := by
    rw [hgrid]
    calc
      δ ^ (((1 : ℕ) : ℝ) / (N : ℝ)) ≤
          (16 : NNReal) ^ (-(N : ℝ) * (((1 : ℕ) : ℝ) / (N : ℝ))) := hδpow
      _ = (16 : NNReal) ^ (-1 : ℝ) := hshift
  calc
    2 * gridScale δ N 1 ≤ 2 * (16 : NNReal) ^ (-1 : ℝ) :=
      mul_le_mul_of_nonneg_left hle (by positivity : 0 ≤ (2 : NNReal))
    _ = 2 * (16 : NNReal)⁻¹ := by rw [NNReal.rpow_neg_one]
    _ ≤ 1 := by
      rw [← NNReal.coe_le_coe]
      norm_num [NNReal.coe_inv]

/-- **Every grid scale strictly above the finest one is at least `2 δ`.**

`gridScale δ N a = δ ^ (a/N) ≥ δ ^ ((N-1)/N) = δ / δ ^ (1/N) ≥ 2 δ` once `2 δ ^ (1/N) ≤ 1`.  The
hypothesis `a < N` is what makes the exponent strictly less than `1`; at `a = N` the scale is `δ`
and the conclusion is false. -/
theorem two_mul_le_gridScale {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {N a : ℕ} (haN : a < N)
    (hsmall : 2 * gridScale δ N 1 ≤ 1) :
    2 * (δ : ℝ) ≤ (gridScale δ N a : ℝ) := by
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hN_ne : (N : ℝ) ≠ 0 := ne_of_gt hN_pos
  have hδ_ne : δ ≠ 0 := ne_of_gt hδ0
  have hsmall' : 2 * δ ^ ((1 : ℝ) / (N : ℝ)) ≤ 1 := by
    simpa [Tube.gridScale] using hsmall
  have hale : (a : ℝ) ≤ (N : ℝ) - 1 := by
    have h : (a : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast (by omega : a + 1 ≤ N)
    linarith
  have hexp : (a : ℝ) / (N : ℝ) ≤ (1 : ℝ) - (1 : ℝ) / (N : ℝ) := by
    have hdiv : (a : ℝ) / (N : ℝ) ≤ ((N : ℝ) - 1) / (N : ℝ) := by
      exact div_le_div_of_nonneg_right hale (by exact_mod_cast (Nat.zero_le N) : 0 ≤ (N : ℝ))
    rw [show ((N : ℝ) - 1) / (N : ℝ) = 1 - (1 : ℝ) / (N : ℝ) by
      field_simp [hN_ne]] at hdiv
    exact hdiv
  have hsplit : δ =
      δ ^ ((1 : ℝ) / (N : ℝ)) * δ ^ ((1 : ℝ) - (1 : ℝ) / (N : ℝ)) := by
    calc
      δ = δ ^ (1 : ℝ) := by rw [NNReal.rpow_one]
      _ = δ ^ (((1 : ℝ) / (N : ℝ)) + ((1 : ℝ) - (1 : ℝ) / (N : ℝ))) := by ring
      _ = δ ^ ((1 : ℝ) / (N : ℝ)) * δ ^ ((1 : ℝ) - (1 : ℝ) / (N : ℝ)) := by
        rw [NNReal.rpow_add hδ_ne]
  have hstep : 2 * δ ≤ δ ^ ((1 : ℝ) - (1 : ℝ) / (N : ℝ)) := by
    have h2δeq : 2 * δ = (2 * δ ^ ((1 : ℝ) / (N : ℝ))) * δ ^ ((1 : ℝ) - (1 : ℝ) / (N : ℝ)) := by
      calc
        2 * δ = 2 * (δ ^ ((1 : ℝ) / (N : ℝ)) * δ ^ ((1 : ℝ) - (1 : ℝ) / (N : ℝ))) := by
          exact congrArg (fun x => 2 * x) hsplit
        _ = (2 * δ ^ ((1 : ℝ) / (N : ℝ))) * δ ^ ((1 : ℝ) - (1 : ℝ) / (N : ℝ)) := by ring
    rw [h2δeq]
    calc
      (2 * δ ^ ((1 : ℝ) / (N : ℝ))) * δ ^ ((1 : ℝ) - (1 : ℝ) / (N : ℝ))
          ≤ 1 * δ ^ ((1 : ℝ) - (1 : ℝ) / (N : ℝ)) := by
        exact mul_le_mul_of_nonneg_right hsmall' (NNReal.coe_nonneg _)
      _ = δ ^ ((1 : ℝ) - (1 : ℝ) / (N : ℝ)) := by simp
  have hmono : δ ^ ((1 : ℝ) - (1 : ℝ) / (N : ℝ)) ≤ δ ^ ((a : ℝ) / (N : ℝ)) := by
    exact NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 hexp
  have hmain : 2 * δ ≤ δ ^ ((a : ℝ) / (N : ℝ)) := le_trans hstep hmono
  have hcast : 2 * (δ : ℝ) ≤ ((δ ^ ((a : ℝ) / (N : ℝ)) : NNReal) : ℝ) := by
    exact_mod_cast hmain
  simpa [Tube.gridScale] using hcast

/-- **The hypothesis the producer needs, from `a < N` and the standing smallness of `δ`.**

This is `Kakeya.ml1Boot.two_mul_le_gridScale` with its smallness hypothesis supplied by
`Kakeya.ml1Boot.two_mul_gridScale_one_le_one`. -/
theorem two_mul_le_gridScale_of_le_pow {δ : NNReal} (hδ0 : 0 < δ) {N a : ℕ} (haN : a < N)
    (hδ : δ ≤ (16 : NNReal) ^ (-(N : ℝ))) :
    2 * (δ : ℝ) ≤ (gridScale δ N a : ℝ) := by
  have hN0 : 0 < N := by
    exact lt_of_le_of_lt (Nat.zero_le a) haN
  have hδ1 : δ ≤ 1 := by
    refine le_trans hδ ?_
    exact NNReal.rpow_le_one_of_one_le_of_nonpos (x := (16 : NNReal)) (z := -(N : ℝ))
      (by norm_num : (1 : NNReal) ≤ 16) (by simp)
  exact two_mul_le_gridScale hδ0 hδ1 haN (two_mul_gridScale_one_le_one hN0 hδ)

omit [Nontrivial E] in
/-- **The covering family exists at every coarse node tube of the grid** (blueprint
`lem:ml1bootNeighbouringParents`, geometric half).

`Kakeya.ml1Boot.isEnlargementCover_rescale` at `θ = ρ_a` and `W = P_a(l)`.  This is the first
statement in the development that produces a `Kakeya.ml1Boot.IsEnlargementCover` at a container
the Step 5a consumers are actually stated at. -/
theorem isEnlargementCover_node_rescale {ι : Type*} {δ : NNReal} {s' : Finset ι}
    {T : ι → Tube δ E} {N : ℕ} {Cu : NNReal} (𝒰' : UniformTubeSet s' T N Cu)
    (hδ0 : 0 < δ) (hδ : δ ≤ (16 : NNReal) ^ (-(N : ℝ))) {a : ℕ} (haN : a < N)
    (Λ : NNReal) (l : ι) :
    IsEnlargementCover s' T (gridScale δ N a)
      ((𝒰'.cover.tube a l).rescale (Λ * gridScale δ N a)).toConvexSpaceBody
      (enlargementCoverConstant E Λ) := by
  exact isEnlargementCover_rescale Λ (θ := gridScale δ N a) (δ := δ)
    (two_mul_le_gridScale_of_le_pow hδ0 haN hδ)
    (W := 𝒰'.cover.tube a l) (s' := s') (T := T)

omit [Nontrivial E] in
/-- **`O(1)` neighbouring parents, unconditionally** (blueprint `lem:ml1bootNeighbouringParents`).

The counting half `Kakeya.ml1Boot.card_neighbouringParents_le_of_cover` with its covering
hypothesis discharged: the `a`-nodes reached by the leaves lying in the concentric rescaling
`P_a(l)^{(Λ ρ_a)}` number at most `M(E,Λ) · C_ds`, with
`M(E,Λ) = Kakeya.ml1Boot.enlargementCoverConstant E Λ` depending on the ambient space and on `Λ`
alone.  This is the first Lean target of that blueprint lemma, and its constant is
`enlargementCoverConstant E Λ * Cu`. -/
theorem card_neighbouringParents_le_rescale {ι : Type*} {δ : NNReal} {s' : Finset ι}
    {T : ι → Tube δ E} {N : ℕ} {Cu : NNReal} (𝒰' : UniformTubeSet s' T N Cu)
    (hδ0 : 0 < δ) (hδ : δ ≤ (16 : NNReal) ^ (-(N : ℝ))) {a : ℕ} (haN : a < N)
    (Λ : NNReal) (l : ι) :
    ((neighbouringParents 𝒰' a
          ((𝒰'.cover.tube a l).rescale (Λ * gridScale δ N a)).toConvexSpaceBody).card : NNReal)
      ≤ (enlargementCoverConstant E Λ : ℕ) * Cu := by
  exact card_neighbouringParents_le_of_cover 𝒰' haN.le
    (isEnlargementCover_node_rescale 𝒰' hδ0 hδ haN Λ l)

omit [Nontrivial E] in
/-- **The neighbouring parents of the completion are `O(1)` in number, unconditionally**
(blueprint `lem:ml1bootFibreCompletion`(b)).

`Kakeya.ml1Boot.card_completedFibreParents_le` with its covering hypothesis discharged. -/
theorem card_completedFibreParents_le_rescale {ι : Type*} [DecidableEq ι] {δ : NNReal}
    {s' : Finset ι} {T : ι → Tube δ E} {N : ℕ} {Cu : NNReal} (𝒰' : UniformTubeSet s' T N Cu)
    (hδ0 : 0 < δ) (hδ : δ ≤ (16 : NNReal) ^ (-(N : ℝ))) {a b : ℕ} (haN : a < N) {pθ : ι → ι}
    (hcnp : IsCoarseNodeParents 𝒰' a b pθ) {tτ : Finset ι} (htτ : tτ ⊆ 𝒰'.cover.indexSet b)
    (Λ : NNReal) (l : ι) :
    (((completedFibre 𝒰' a b tτ Λ l).image pθ).card : NNReal)
      ≤ (enlargementCoverConstant E Λ : ℕ) * Cu := by
  exact card_completedFibreParents_le 𝒰' haN.le hcnp htτ l
    (isEnlargementCover_node_rescale 𝒰' hδ0 hδ haN Λ l)

omit [Nontrivial E] in
/-- **The completion is `O(Λ_load N_m)` in size, unconditionally** (blueprint
`lem:ml1bootFibreCompletion`(c)).

`Kakeya.ml1Boot.card_completedFibre_le` with its covering hypothesis discharged.  The load pair
`(N_m, Λ_load)` is still given data; nothing here supplies it. -/
theorem card_completedFibre_le_rescale {ι : Type*} [DecidableEq ι] {δ : NNReal}
    {s' : Finset ι} {T : ι → Tube δ E} {N : ℕ} {Cu : NNReal} (𝒰' : UniformTubeSet s' T N Cu)
    (hδ0 : 0 < δ) (hδ : δ ≤ (16 : NNReal) ^ (-(N : ℝ))) {a b : ℕ} (haN : a < N) {pθ : ι → ι}
    (hcnp : IsCoarseNodeParents 𝒰' a b pθ) {tτ tθ : Finset ι}
    (htτ : tτ ⊆ 𝒰'.cover.indexSet b) (hpθ : ∀ k ∈ tτ, pθ k ∈ tθ) (Λ : NNReal) (l : ι)
    {Nm Λload : NNReal}
    (hload : ∀ l' ∈ tθ, ((fibre tτ pθ l').card : NNReal) ≤ Λload * Nm) :
    ((completedFibre 𝒰' a b tτ Λ l).card : NNReal)
      ≤ Λload * ((enlargementCoverConstant E Λ : ℕ) * Cu) * Nm := by
  exact card_completedFibre_le 𝒰' haN.le hcnp htτ hpθ (Λ := Λ) l
    (isEnlargementCover_node_rescale 𝒰' hδ0 hδ haN Λ l) hload

omit [Nontrivial E] in
/-- **(GWZ (5.10a)) The local density bound at a coarse node, unconditionally** (blueprint
`lem:ml1bootLocalDensityUnrefined`).

`Kakeya.ml1Boot.densityIn_le_of_neighbouringParents` read at the container
`big = P_a(l)^{(Λ ρ_a)}`, its covering hypothesis discharged by
`Kakeya.ml1Boot.isEnlargementCover_node_rescale`, so that the count `M` is replaced by the term
`Kakeya.ml1Boot.enlargementCoverConstant E Λ`.

The general statement is **not** superseded.  It admits an *arbitrary* container and is what makes
the bound readable at a homothety-shaped region; the present one buys an absolute count and pays
for it with the shape.  `a < ssfGridLen δ` is read off `hblock` and is not a new hypothesis: the
block asserts `a < b` and `b ≤ ssfGridLen δ`. -/
theorem densityIn_le_of_rescale {ι : Type*} {δ : NNReal} {s' : Finset ι}
    {T : ι → Tube δ E} {Cu : NNReal} {Kds cds a b m : ℕ} {p : Params} {ε' : ℝ}
    (𝒰' : UniformTubeSet s' T (ssfGridLen δ) Cu)
    (hblock : IsFrostmanDividingBlock 𝒰' Cu Kds cds p.η p.ε a b m p.N)
    (hloss : (Cu : ENNReal) * totalLoss Cu Kds cds δ ≤ (δ : ENNReal) ^ (-ε'))
    (hleaf : ∀ k ∈ 𝒰'.cover.indexSet b, ∃ i ∈ s', 𝒰'.cover.assign b i = k)
    (hδ0 : 0 < δ) (hδ : δ ≤ (16 : NNReal) ^ (-(ssfGridLen δ : ℝ)))
    (Λ : NNReal) (l : ι) {Dm ΛΔ : ENNReal}
    (hdens : ∀ l'' ∈ neighbouringParents 𝒰' a
        ((𝒰'.cover.tube a l).rescale (Λ * gridScale δ (ssfGridLen δ) a)).toConvexSpaceBody,
      densityIn (𝒰'.nodesUnder b a l'') (fun k => (𝒰'.cover.tube b k).toConvexSpaceBody)
          (𝒰'.cover.tube a l'').toConvexSpaceBody ≤ ΛΔ * Dm)
    {K' : ConvexSpaceBody E}
    (hK' : K' ≤
      ((𝒰'.cover.tube a l).rescale (Λ * gridScale δ (ssfGridLen δ) a)).toConvexSpaceBody) :
    densityIn (𝒰'.cover.indexSet b) (fun k => (𝒰'.cover.tube b k).toConvexSpaceBody) K'
      ≤ ΛΔ * ((enlargementCoverConstant E Λ : ℕ) * Cu : NNReal) * (δ : ENNReal) ^ (-ε') *
          ENNReal.ofReal (((gridScale δ (ssfGridLen δ) a : ℝ)
            / (gridScale δ (ssfGridLen δ) b : ℝ)) ^ p.η m) * Dm := by
  refine densityIn_le_of_neighbouringParents 𝒰' hblock hloss hleaf
    ((𝒰'.cover.tube a l).rescale (Λ * gridScale δ (ssfGridLen δ) a)).toConvexSpaceBody
    ?_ hdens hK'
  · exact isEnlargementCover_node_rescale 𝒰' hδ0 hδ
      (lt_of_lt_of_le hblock.coarse_lt_fine hblock.fine_le) Λ l

end Edge

end ml1Boot

end Kakeya
