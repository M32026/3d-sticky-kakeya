/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Covers
public import Kakeya.Tube.Dilate
public import Kakeya.DimensionThree.MainLemma2.SetupProduce

/-!
# The axial coordinate is essential-distinctness blind, and the pre-F12 / pre-centred transcription of
# `exists_setup_caseSideData` is false

Clause (e) of `Kakeya.VeryNotSticky.BandUniformRefinement` — the tube count `1 ≤ δ |𝕋'|`, the
Lean form of the configuration field `Kakeya.VeryNotSticky.tube_count` — is reduced by
`Kakeya.VeryNotSticky.eventually_tubeCount_of_edCover` to a single geometric object: a
**containment-preserving essentially distinct coarsening**, i.e. a family of `ρ`-tubes covering
`𝕋` (each `δ`-tube inside one of them) and pairwise essentially distinct.

**A unit-length tube has five parameters, not four.** The position of the core *along its own
axis* is the fifth, and in that coordinate essential distinctness costs a constant while the
covering budget affords only `≍ ρ`. The deficit is therefore a factor `≍ 1/ρ`, not `39 %`, and it
is fatal: an essentially distinct cover of a suitable family does not exist at all.

## What is proved

* `Kakeya.VeryNotSticky.dist_endpoints_le_of_carrier_subset` — **containment pins the endpoints**:
  a `δ`-tube inside a `ρ`-tube has its core's endpoints within `3ρ` of the containing core's, in
  one of the two orientations. The converse of `Kakeya.Tube.tube_carrier_subset_of_close`, which
  the tree did not have; `Kakeya.VeryNotSticky.dist_center_le_of_carrier_subset` is the
  orientation-free corollary.

* `Kakeya.VeryNotSticky.not_isEssentiallyDistinct_of_axial_translate` — **exact axial translates
  are never essentially distinct**, at any slide `|α| ≤ 1/12`. The threshold is a pure number,
  with no factor of `ρ`. Contrast the transverse twin
  `Kakeya.VeryNotSticky.isEssentiallyDistinct_of_transverse_sep_sharp`, where a gap of `ρ` already
  buys essential distinctness.

* `Kakeya.VeryNotSticky.card_le_of_ed_of_endpoints_confined` — **the packing bound**: an
  essentially distinct family of `ρ`-tubes whose cores are pinned, after removing a common axial
  slide, to `3ρ`-balls about two fixed points has at most `385 ^ 6` members. The bound contains
  no `ρ`.

* `Kakeya.VeryNotSticky.not_edCover_of_axialFamily` — **no essentially distinct cover exists** for
  a family of more than `385 ^ 6` `δ`-tubes that are axial translates of one another at offsets
  inside `[-1/288, 1/288]` and pairwise more than `6ρ` apart.
  `Kakeya.VeryNotSticky.exists_axialFamily` and
  `Kakeya.VeryNotSticky.exists_family_without_edCover` build such a family inside the closed unit
  ball, so the statement is not vacuous.

**Scope note.** Since `Kakeya.VeryNotSticky.exists_setup_caseSideData`
and `Kakeya.multiplicity_le_of_card_isEssDistinct_ge` carry the binder `∀ i ∈ s, (T i).toTube.IsCentred`; and the hypotheses
transcribed below (`h91`, the binders of `not_setupConclusion`) are the **pre-F12** clauses — an *unbounded* `∃ C` uniformity binder
and a `∀`-quantified `ρ`-cover — not the existing `∃`-form, to which the axial witness does not transfer. The witness family
of this module is a family of axial translates of one tube — centred tubes on a common axis coincide, so it does **not** meet
that binder — and every "is false" below is a record about the statements *before* that binder (the hypothesis list of
`Kakeya.VeryNotSticky.SetupCaseSideDataStatementOld`), not about the live ones; the hand-transcribed hypotheses (`h91`)
below are the pre-centred texts.

* `Kakeya.VeryNotSticky.not_setupConclusion` — **the conclusion of
  `Kakeya.VeryNotSticky.exists_setup_caseSideData`, as it stood before the centredness binder, is false.** The family above
  meets every binder of that pre-centred statement — `hball` by construction, `huni` by
  `Kakeya.VeryNotSticky.nonempty_shadedUniformTubeSet_of_core_injOn` (the binder is an *unbounded*
  `∃ C`), `hmax` by `Kakeya.maxDensity_le_card`, `hfull` because the shading is the whole carrier,
  and `hcount` **vacuously** — while its cardinality is the constant `385^6 + 1`, so the field
  `Kakeya.VeryNotSticky.tube_count` of the configuration it is asked to produce fails outright.
  Only `0 < exscal` and `0 < η` are used: the refutation does not lean on the Katz–Tao or Frostman
  estimates.

* `Kakeya.VeryNotSticky.exists_witnessFamily` — the same family with **all five binders verified
  and its multiplicity bounded below** by half its cardinality (the whole family lies inside the
  union of two of its members), which is what refutes the section's target itself:

* `Kakeya.VeryNotSticky.not_lemma91Conclusion` — **the conclusion of
  `Kakeya.multiplicity_le_of_card_isEssDistinct_ge`, GWZ Lemma 9.1, is false as rendered before the
  centredness binder** (its `h91` is the pre-centred text, transcribed by hand; the live statement is not refuted — scope
  note above), given its own two antecedents `K_KT(β)` and `K_F(β)`. The witness family has multiplicity `≥ #𝕋/2`
  with `#𝕋` a constant, while the conclusion asserts `multiplicity ≤ δ^ν (#𝕋)^β → 0`. The defect
  is the same missing binder: nothing in the statement asks `𝕋` to be large, and the `ρ`-count
  hypothesis cannot supply it.

* `Kakeya.VeryNotSticky.axialNet_budget_infeasible`, together with
  `Kakeya.VeryNotSticky.exists_axialNet_of_range_le` and
  `Kakeya.VeryNotSticky.not_axialNet_of_rho_small` — the arithmetic of the axial coordinate,
  isolated in the style of `Kakeya.VeryNotSticky.productNet_budget_infeasible`, with the sharpness
  witness that keeps it from being vacuous.

## What this means for the target

`hcount` is the only binder of `Kakeya.VeryNotSticky.exists_setup_caseSideData` that bounds `|𝕋|`
from below, and it is met by a family of *bounded* size. The field `tube_count` is therefore not
reachable from the binders, and the repair is a statement-level one:
`Kakeya.VeryNotSticky.tubeCount_of_parent_of_retention` names the binder that would discharge it,
`|𝕋| ≥ δ^{-1-α}`, one power below the field's own value because the refinement loses `δ^α` of the
cardinality. This is an additional cardinality hypothesis.
-/

@[expose] public section

namespace Kakeya.VeryNotSticky

open MeasureTheory Metric Set Produce

universe u

/-! ### Containment pins the endpoints -/

section Endpoints

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- **Containment pins the endpoints of the core** — the converse of
`Kakeya.Tube.tube_carrier_subset_of_close`.

If the `δ`-tube `T` lies inside the `ρ`-tube `V` then the two unit cores have matching endpoints
up to `3ρ`, in one of the two orientations. The proof is the only place the *equal length* of
the two cores is used: both endpoints of `T`'s core lie within `ρ` of `V`'s core, so their
parameters along that core differ by at least `1 - 2ρ`; since the core has length one, one
parameter is within `2ρ` of `0` and the other within `2ρ` of `1`.

This is the fact every argument about *which* `ρ`-tubes may cover a given `δ`-tube needs, and it
was absent: the tree carried only `Kakeya.Tube.tube_carrier_subset_of_close`, which runs the
other way (closeness of parameters implies containment). -/
theorem dist_endpoints_le_of_carrier_subset {δ ρ : NNReal} (T : Tube δ E) (V : Tube ρ E)
    (hsub : T.carrier ⊆ V.carrier) :
    (dist T.x V.x ≤ 3 * (ρ : ℝ) ∧ dist T.y V.y ≤ 3 * (ρ : ℝ)) ∨
    (dist T.x V.y ≤ 3 * (ρ : ℝ) ∧ dist T.y V.x ≤ 3 * (ρ : ℝ)) := by
  classical
  set d : E := V.y - V.x with hd
  have hdn : ‖d‖ = 1 := by
    rw [hd, ← dist_eq_norm, dist_comm]
    exact V.dist_eq_one
  have hxmem : T.x ∈ V.carrier := hsub (Tube.x_mem_carrier T)
  have hymem : T.y ∈ V.carrier := hsub (Tube.y_mem_carrier T)
  rw [V.carrier_eq] at hxmem hymem
  obtain ⟨zs, hzs, hxzs⟩ := Set.mem_iUnion₂.1 hxmem
  obtain ⟨zt, hzt, hyzt⟩ := Set.mem_iUnion₂.1 hymem
  rw [segment_eq_image'] at hzs hzt
  obtain ⟨s, hs, rfl⟩ := hzs
  obtain ⟨t, ht, rfl⟩ := hzt
  rw [Metric.mem_closedBall] at hxzs hyzt
  simp only [] at hxzs hyzt
  have hpar : ∀ a b : ℝ, dist (V.x + a • d) (V.x + b • d) = |a - b| := by
    intro a b
    rw [dist_eq_norm]
    have h : (V.x + a • d) - (V.x + b • d) = (a - b) • d := by module
    rw [h, norm_smul, hdn, Real.norm_eq_abs, mul_one]
  have hst : |s - t| ≥ 1 - 2 * (ρ : ℝ) := by
    have h1 : dist T.x T.y = 1 := T.dist_eq_one
    have hchain : dist T.x T.y
        ≤ dist T.x (V.x + s • d) + dist (V.x + s • d) (V.x + t • d)
            + dist (V.x + t • d) T.y := dist_triangle4 _ _ _ _
    rw [hpar] at hchain
    have h2 : dist (V.x + t • d) T.y ≤ (ρ : ℝ) := by rw [dist_comm]; exact hyzt
    rw [h1] at hchain
    linarith
  have hs0 : (0 : ℝ) ≤ s := hs.1
  have hs1 : s ≤ 1 := hs.2
  have ht0 : (0 : ℝ) ≤ t := ht.1
  have ht1 : t ≤ 1 := ht.2
  have hxs : dist T.x (V.x + s • d) ≤ (ρ : ℝ) := hxzs
  have hyt : dist T.y (V.x + t • d) ≤ (ρ : ℝ) := hyzt
  have hparx : ∀ a : ℝ, dist (V.x + a • d) V.x = |a| := by
    intro a
    rw [dist_eq_norm, show V.x + a • d - V.x = a • d from by abel, norm_smul, hdn,
      Real.norm_eq_abs, mul_one]
  have hpary : ∀ a : ℝ, dist (V.x + a • d) V.y = |a - 1| := by
    intro a
    rw [dist_eq_norm, show V.x + a • d - V.y = (a - 1) • d from by rw [hd]; module,
      norm_smul, hdn, Real.norm_eq_abs, mul_one]
  rcases le_total s t with hle | hle
  · left
    have habs : |s - t| = t - s := by rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    rw [habs] at hst
    refine ⟨?_, ?_⟩
    · have h := dist_triangle T.x (V.x + s • d) V.x
      rw [hparx s, abs_of_nonneg hs0] at h
      linarith
    · have h := dist_triangle T.y (V.x + t • d) V.y
      rw [hpary t, abs_of_nonpos (by linarith)] at h
      linarith
  · right
    have habs : |s - t| = s - t := abs_of_nonneg (by linarith)
    rw [habs] at hst
    refine ⟨?_, ?_⟩
    · have h := dist_triangle T.x (V.x + s • d) V.y
      rw [hpary s, abs_of_nonpos (by linarith)] at h
      linarith
    · have h := dist_triangle T.y (V.x + t • d) V.x
      rw [hparx t, abs_of_nonneg ht0] at h
      linarith

/-- **Containment pins the centre**, orientation-free.  The midpoint of a tube's core does not
depend on which endpoint is called `x`, so the two-case disjunction of
`Kakeya.VeryNotSticky.dist_endpoints_le_of_carrier_subset` collapses. -/
theorem dist_center_le_of_carrier_subset {δ ρ : NNReal} (T : Tube δ E) (V : Tube ρ E)
    (hsub : T.carrier ⊆ V.carrier) :
    dist T.center V.center ≤ 3 * (ρ : ℝ) := by
  rcases dist_endpoints_le_of_carrier_subset T V hsub with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have h : dist (midpoint ℝ T.x T.y) (midpoint ℝ V.x V.y)
        ≤ (dist T.x V.x + dist T.y V.y) / 2 := dist_midpoint_midpoint_le _ _ _ _
    simp only [Tube.center]
    linarith
  · have h : dist (midpoint ℝ T.x T.y) (midpoint ℝ V.y V.x)
        ≤ (dist T.x V.y + dist T.y V.x) / 2 := dist_midpoint_midpoint_le _ _ _ _
    rw [show midpoint ℝ V.y V.x = midpoint ℝ V.x V.y from by rw [midpoint_comm]] at h
    simp only [Tube.center]
    linarith

end Endpoints

/-! ### The axial coordinate is essential-distinctness blind -/

/-- **Exact axial translates are never essentially distinct**, at *any* slide `|α| ≤ 1/12`.

`Kakeya.Tube.not_essDistinct_of_axial_slide` at zero endpoint error.  What matters is the shape
of the threshold: `1/12 = 1/(4 n)` in dimension `n = 3` is an **absolute constant**, with no
factor of `ρ`.  So sliding a `ρ`-tube along its own axis buys no essential distinctness until the
slide is a constant fraction of the tube's *length* — never at the scale `ρ` on which the
covering budget of `Kakeya.Tube.tube_carrier_subset_of_close` operates.

Compare the transverse twin `Kakeya.VeryNotSticky.isEssentiallyDistinct_of_transverse_sep_sharp`:
there a gap of `ρ` already *gives* essential distinctness.  The asymmetry between the two is the
subject of this file. -/
theorem not_isEssentiallyDistinct_of_axial_translate {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (U U' : Tube ρ E3) {α : ℝ} (hα : |α| ≤ 1 / 12)
    (hx : U'.x = U.x + α • U.direction) (hy : U'.y = U.y + α • U.direction) :
    ¬ IsEssentiallyDistinct U.carrier U'.carrier := by
  have hfr : (Module.finrank ℝ E3 : ℝ) = 3 := by simp
  refine Tube.not_essDistinct_of_axial_slide hρ0 hρ1 U U' (α := α) ?_ ?_ ?_
  · rw [hfr]; linarith [hα]
  · rw [hx, dist_self, hfr]; positivity
  · rw [hy, dist_self, hfr]; positivity

/-- **An essentially distinct collinear family has `1/12`-separated axial parameters.**

`V j` is here the axial translate of a fixed `ρ`-tube `V₀` by `τ j`.  Two members with
`|τ j - τ k| ≤ 1/12` are exact axial translates of one another, hence not essentially distinct
by `Kakeya.VeryNotSticky.not_isEssentiallyDistinct_of_axial_translate`.

**The separation does not involve `ρ`.**  That is the whole content: in the transverse and
angular coordinates an essentially distinct family may be packed at spacing `≍ ρ`, and the
covering budget affords displacements of the same order; in the axial coordinate the covering
budget still affords only `≍ ρ`, but essential distinctness demands a constant. -/
theorem abs_sub_axialParam_of_ed_collinear {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    {κ : Type*} {t : Finset κ} {V : κ → Tube ρ E3} {V₀ : Tube ρ E3} {τ : κ → ℝ}
    (hx : ∀ j ∈ t, (V j).x = V₀.x + τ j • V₀.direction)
    (hy : ∀ j ∈ t, (V j).y = V₀.y + τ j • V₀.direction)
    (hED : (t : Set κ).Pairwise fun j k => IsEssentiallyDistinct (V j).carrier (V k).carrier)
    {j k : κ} (hj : j ∈ t) (hk : k ∈ t) (hjk : j ≠ k) :
    1 / 12 < |τ k - τ j| := by
  by_contra hcon
  rw [not_lt] at hcon
  have hdirj : (V j).direction = V₀.direction := by
    have : (V j).y - (V j).x = V₀.y - V₀.x := by
      rw [hx j hj, hy j hj]; abel
    simpa [Tube.direction] using this
  have hxk : (V k).x = (V j).x + (τ k - τ j) • (V j).direction := by
    rw [hx k hk, hx j hj, hdirj, sub_smul]
    abel
  have hyk : (V k).y = (V j).y + (τ k - τ j) • (V j).direction := by
    rw [hy k hk, hy j hj, hdirj, sub_smul]
    abel
  exact not_isEssentiallyDistinct_of_axial_translate hρ0 hρ1 (V j) (V k) hcon hxk hyk
    (hED hj hk hjk)

/-- **An essentially distinct collinear family inside an axial range `A` has at most
`⌊12A⌋ + 1` members** — a bound with no `ρ` in it.

The map `j ↦ ⌊12 τ j⌋₊` is injective on the family by
`Kakeya.VeryNotSticky.abs_sub_axialParam_of_ed_collinear` and lands in `{0, …, ⌊12A⌋}`. -/
theorem card_le_of_ed_collinear {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) {A : ℝ}
    {κ : Type*} {t : Finset κ} {V : κ → Tube ρ E3} {V₀ : Tube ρ E3} {τ : κ → ℝ}
    (hτ : ∀ j ∈ t, τ j ∈ Set.Icc (0 : ℝ) A)
    (hx : ∀ j ∈ t, (V j).x = V₀.x + τ j • V₀.direction)
    (hy : ∀ j ∈ t, (V j).y = V₀.y + τ j • V₀.direction)
    (hED : (t : Set κ).Pairwise fun j k => IsEssentiallyDistinct (V j).carrier (V k).carrier) :
    t.card ≤ ⌊12 * A⌋₊ + 1 := by
  classical
  have hmaps : ∀ j ∈ t, ⌊12 * τ j⌋₊ ∈ Finset.range (⌊12 * A⌋₊ + 1) := by
    intro j hj
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact Nat.floor_le_floor (by
      have h := hτ j hj
      have : τ j ≤ A := h.2
      linarith)
  have hinj : ∀ j ∈ t, ∀ k ∈ t, ⌊12 * τ j⌋₊ = ⌊12 * τ k⌋₊ → j = k := by
    intro j hj k hk hfl
    by_contra hjk
    have hsep := abs_sub_axialParam_of_ed_collinear hρ0 hρ1 hx hy hED hj hk hjk
    have hj0 : (0 : ℝ) ≤ 12 * τ j := by
      have := (hτ j hj).1; linarith
    have hk0 : (0 : ℝ) ≤ 12 * τ k := by
      have := (hτ k hk).1; linarith
    have h1 : (⌊12 * τ j⌋₊ : ℝ) ≤ 12 * τ j := Nat.floor_le hj0
    have h2 : 12 * τ j < (⌊12 * τ j⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    have h3 : (⌊12 * τ k⌋₊ : ℝ) ≤ 12 * τ k := Nat.floor_le hk0
    have h4 : 12 * τ k < (⌊12 * τ k⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    rw [hfl] at h1 h2
    have habs : |τ k - τ j| ≤ 1 / 12 := by
      rw [abs_le]
      constructor <;> linarith
    linarith
  have := Finset.card_le_card_of_injOn (f := fun j => ⌊12 * τ j⌋₊) hmaps
    (fun j hj k hk h => hinj j hj k hk h)
  simpa using this

/-! ### The consequence for the covering question -/

/-- **A collinear essentially distinct cover of an axially spread family cannot exist.**

Let `𝕋 = {T i}` be `δ`-tubes that are exact axial translates of a fixed `T₀`, at offsets `θ i`
pairwise more than `6ρ` apart.  Let `{V j}` be a family of `ρ`-tubes that are exact axial
translates of a fixed `V₀` at parameters `τ j ∈ [0, A]`, pairwise essentially distinct, covering
`𝕋`.  Then `#𝕋 ≤ ⌊12A⌋ + 1`.

Two ingredients: `Kakeya.VeryNotSticky.dist_center_le_of_carrier_subset` forces the covering map
to be injective (a single `ρ`-tube cannot contain two members whose centres are more than `6ρ`
apart), and `Kakeya.VeryNotSticky.card_le_of_ed_collinear` caps the cover.

**Read at `A = 1/12` the bound is `2`, while the `6ρ`-separation permits `1/(72 ρ)` members.**
So the collinear route to the coarsening asked for by
`Kakeya.VeryNotSticky.eventually_tubeCount_of_edCover` fails by a factor `≍ 1/ρ` — not by the
constant factor that `Kakeya.VeryNotSticky.productNet_budget_infeasible` measures in the
transverse and angular coordinates. -/
theorem card_le_of_collinear_edCover {δ ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) {A : ℝ}
    {ι κ : Type*} {s : Finset ι} {T : ι → Tube δ E3} {θ : ι → ℝ} {T₀ : Tube δ E3}
    (hTx : ∀ i ∈ s, (T i).x = T₀.x + θ i • T₀.direction)
    (hTy : ∀ i ∈ s, (T i).y = T₀.y + θ i • T₀.direction)
    (hsep : ∀ i ∈ s, ∀ i' ∈ s, i ≠ i' → 6 * (ρ : ℝ) < |θ i - θ i'|)
    {t : Finset κ} {V : κ → Tube ρ E3} {V₀ : Tube ρ E3} {τ : κ → ℝ}
    (hτ : ∀ j ∈ t, τ j ∈ Set.Icc (0 : ℝ) A)
    (hVx : ∀ j ∈ t, (V j).x = V₀.x + τ j • V₀.direction)
    (hVy : ∀ j ∈ t, (V j).y = V₀.y + τ j • V₀.direction)
    (hED : (t : Set κ).Pairwise fun j k => IsEssentiallyDistinct (V j).carrier (V k).carrier)
    (hcov : ∀ i ∈ s, ∃ j ∈ t, (T i).carrier ⊆ (V j).carrier) :
    s.card ≤ ⌊12 * A⌋₊ + 1 := by
  classical
  rcases Finset.eq_empty_or_nonempty s with rfl | ⟨i₀, hi₀⟩
  · simp
  obtain ⟨j₀, hj₀, -⟩ := hcov i₀ hi₀
  haveI : Nonempty κ := ⟨j₀⟩
  choose! g hg hgsub using hcov
  have hcenter : ∀ i ∈ s, T₀.center + θ i • T₀.direction = (T i).center := by
    intro i hi
    simp only [Tube.center, hTx i hi, hTy i hi, midpoint_eq_smul_add, invOf_eq_inv]
    module
  have hinj : ∀ i ∈ s, ∀ i' ∈ s, g i = g i' → i = i' := by
    intro i hi i' hi' hgg
    by_contra hne
    have h1 := dist_center_le_of_carrier_subset (T i) (V (g i)) (hgsub i hi)
    have h2 := dist_center_le_of_carrier_subset (T i') (V (g i')) (hgsub i' hi')
    rw [hgg] at h1
    have h3 : dist (T i).center (T i').center ≤ 6 * (ρ : ℝ) := by
      have := dist_triangle (T i).center (V (g i')).center (T i').center
      rw [dist_comm (V (g i')).center (T i').center] at this
      linarith
    have h4 : dist (T i).center (T i').center = |θ i - θ i'| := by
      rw [← hcenter i hi, ← hcenter i' hi', dist_eq_norm,
        show T₀.center + θ i • T₀.direction - (T₀.center + θ i' • T₀.direction)
          = (θ i - θ i') • T₀.direction from by module,
        norm_smul, Tube.norm_direction, Real.norm_eq_abs, mul_one]
    rw [h4] at h3
    exact absurd h3 (not_le.mpr (hsep i hi i' hi' hne))
  calc s.card ≤ t.card := Finset.card_le_card_of_injOn g hg hinj
    _ ≤ ⌊12 * A⌋₊ + 1 := card_le_of_ed_collinear hρ0 hρ1 hτ hVx hVy hED

/-! ### The arithmetic, isolated -/

/-- **The axial-net budget is infeasible**, in the style of
`Kakeya.VeryNotSticky.productNet_budget_infeasible`.

A collinear cover of an axial range `A` at the containment resolution `6ρ` needs `N` members with
`A ≤ 6ρN`; essential distinctness caps `N` at `12A + 1`
(`Kakeya.VeryNotSticky.card_le_of_ed_collinear`).  The two are compatible only when
`A ≤ 72ρA + 6ρ`.

Unlike the transverse and angular coordinates, where the analogous comparison is between two
quantities of the same order in `ρ` and the shortfall is a constant, here the two sides differ by
a factor `≍ 1/ρ`: at any fixed `A > 0` the conclusion fails for all `ρ < A / (72A + 6)`. -/
theorem axialNet_budget_infeasible {A ρ N : ℝ} (hρ : 0 ≤ ρ)
    (hcover : A ≤ 6 * ρ * N) (hED : N ≤ 12 * A + 1) :
    A ≤ 72 * ρ * A + 6 * ρ := by
  nlinarith [hcover, hED, hρ]

/-- **The threshold `A ≤ 72ρA + 6ρ` is sharp**, so the previous lemma is not vacuous: below it a
collinear net of the required size does exist, at `N = 12A + 1`. -/
theorem exists_axialNet_of_range_le {A ρ : ℝ} (h : A ≤ 72 * ρ * A + 6 * ρ) :
    ∃ N : ℝ, A ≤ 6 * ρ * N ∧ N ≤ 12 * A + 1 :=
  ⟨12 * A + 1, by nlinarith, le_rfl⟩

/-- **The contrapositive, in the form a producer meets it in**: at any fixed axial range `A > 0`
and any `ρ` below `A / (72A + 6)`, no collinear essentially distinct cover of that range exists.
At `A = 1/12` the threshold is `ρ < 1/144`. -/
theorem not_axialNet_of_rho_small {A ρ : ℝ} (hρ : 0 ≤ ρ)
    (h : 72 * ρ * A + 6 * ρ < A) :
    ¬ ∃ N : ℝ, A ≤ 6 * ρ * N ∧ N ≤ 12 * A + 1 := by
  rintro ⟨N, hcov, hED⟩
  exact absurd (axialNet_budget_infeasible hρ hcov hED) (not_le.mpr h)

/-! ### The general case: the endpoint pigeonhole -/

/-- **A maximal `r`-separated subset**, in the form the two-step pigeonhole consumes: it is
`r`-separated, and every member of the ambient family is within `r` of one of its members. -/
private theorem exists_maximal_separated {κ : Type*} (t : Finset κ) (Φ : κ → E3) {r : ℝ}
    (hr : 0 < r) :
    ∃ A ⊆ t, (∀ j ∈ A, ∀ k ∈ A, j ≠ k → r ≤ dist (Φ j) (Φ k)) ∧
      ∀ j ∈ t, ∃ a ∈ A, dist (Φ j) (Φ a) < r := by
  classical
  set S : Finset (Finset κ) :=
    t.powerset.filter (fun A => ∀ j ∈ A, ∀ k ∈ A, j ≠ k → r ≤ dist (Φ j) (Φ k)) with hS
  have hemp : (∅ : Finset κ) ∈ S := by simp [hS]
  obtain ⟨A, hAS, hmax⟩ := Finset.exists_max_image S (fun A => A.card) ⟨∅, hemp⟩
  rw [hS, Finset.mem_filter, Finset.mem_powerset] at hAS
  refine ⟨A, hAS.1, hAS.2, ?_⟩
  intro j hj
  by_contra hcon
  have hcon' : ∀ a ∈ A, r ≤ dist (Φ j) (Φ a) := by
    intro a ha
    by_contra h
    exact hcon ⟨a, ha, not_le.mp h⟩
  have hjA : j ∉ A := by
    intro hjA
    have h := hcon' j hjA
    rw [dist_self] at h
    linarith
  have hins : insert j A ∈ S := by
    rw [hS, Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.insert_subset hj hAS.1, ?_⟩
    intro p hp q hq hpq
    rcases Finset.mem_insert.1 hp with rfl | hp' <;> rcases Finset.mem_insert.1 hq with rfl | hq'
    · exact absurd rfl hpq
    · exact hcon' q hq'
    · rw [dist_comm]; exact hcon' p hp'
    · exact hAS.2 p hp' q hq' hpq
  have hle := hmax _ hins
  rw [Finset.card_insert_of_notMem hjA] at hle
  omega

/-- The packing bound of `Kakeya.finite_and_card_le_of_separated`, in the `Finset` form used
below: an `r`-separated family of points of `E3` inside a ball of radius `R` has at most
`(1 + 2R/r) ^ 3` members. -/
private theorem card_le_of_separated_ball {κ : Type*} (A : Finset κ) (Φ : κ → E3)
    {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (x₀ : E3)
    (hsep : ∀ j ∈ A, ∀ k ∈ A, j ≠ k → r ≤ dist (Φ j) (Φ k))
    (hball : ∀ j ∈ A, dist (Φ j) x₀ < R) :
    (A.card : ℝ) ≤ (1 + 2 * R / r) ^ 3 := by
  classical
  have hinj : Set.InjOn Φ (A : Set κ) := by
    intro j hj k hk hjk
    by_contra hne
    have h := hsep j hj k hk hne
    rw [hjk, dist_self] at h
    linarith
  have hN : (Φ '' (A : Set κ)) ⊆ Metric.ball x₀ R := by
    rintro _ ⟨j, hj, rfl⟩
    exact Metric.mem_ball.2 (hball j hj)
  have hsep' : ∀ y ∈ Φ '' (A : Set κ), ∀ z ∈ Φ '' (A : Set κ), y ≠ z → r ≤ dist y z := by
    rintro _ ⟨j, hj, rfl⟩ _ ⟨k, hk, rfl⟩ hne
    exact hsep j hj k hk (fun h => hne (by rw [h]))
  have h := (Kakeya.finite_and_card_le_of_separated hr hR x₀ hsep' hN).2
  rw [Set.InjOn.ncard_image hinj, Set.ncard_coe_finset] at h
  have hfr : Module.finrank ℝ E3 = 3 := by simp
  rwa [hfr] at h

/-- **The endpoint pigeonhole: an essentially distinct family of `ρ`-tubes whose cores are pinned
to a common axial line is of bounded size, with a bound that does not involve `ρ`.**

The hypotheses are exactly what `Kakeya.VeryNotSticky.dist_endpoints_le_of_carrier_subset`
delivers for a cover: each `V j` contains a `δ`-tube whose core is the segment `[a, b]` slid
along its own direction by `θ j`, so after removing that slide the two endpoints of `V j`'s core
lie in the `3ρ`-balls about `a` and `b`.

The conclusion is a **constant**: `385 ^ 6`, with no `ρ` in it. Two members of the family whose
normalised endpoints are within `ρ/24` are, up to an error the axial-slide criterion tolerates,
exact axial translates of each other, hence not essentially distinct
(`Kakeya.Tube.not_essDistinct_of_axial_slide`); and a `ρ/48`-separated set inside a `4ρ`-ball has
at most `385 ^ 3` members, twice over for the two endpoints.

**This is the whole obstruction to clause (e).** A family of more than `385 ^ 6` `δ`-tubes on a
common axis, at axial offsets inside `[-1/288, 1/288]` and pairwise more than `6ρ` apart, has one
covering tube per member (`Kakeya.VeryNotSticky.dist_center_le_of_carrier_subset`) and therefore
admits **no** essentially distinct cover at all — while its cardinality is a constant, far below
the `δ^{-1}` that `Kakeya.VeryNotSticky.eventually_tubeCount_of_edCover` is asked to produce. -/
theorem card_le_of_ed_of_endpoints_confined {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    {κ : Type*} (t : Finset κ) (V : κ → Tube ρ E3) (a b : E3) (θ : κ → ℝ)
    (hθ : ∀ j ∈ t, |θ j| ≤ 1 / 288)
    (hx : ∀ j ∈ t, dist ((V j).x - θ j • (b - a)) a ≤ 3 * (ρ : ℝ))
    (hy : ∀ j ∈ t, dist ((V j).y - θ j • (b - a)) b ≤ 3 * (ρ : ℝ))
    (hED : (t : Set κ).Pairwise fun j k => IsEssentiallyDistinct (V j).carrier (V k).carrier) :
    t.card ≤ 385 ^ 6 := by
  classical
  by_contra hcard
  rw [not_le] at hcard
  have hρR : (0 : ℝ) < (ρ : ℝ) := by exact_mod_cast hρ0
  set u : E3 := b - a with hu
  set Φ : κ → E3 := fun j => (V j).x - θ j • u with hΦ
  set Ψ : κ → E3 := fun j => (V j).y - θ j • u with hΨ
  set r : ℝ := (ρ : ℝ) / 48 with hrdef
  have hr : 0 < r := by rw [hrdef]; positivity
  have hR : (0 : ℝ) ≤ 4 * (ρ : ℝ) := by positivity
  -- the packing bound, specialised
  have hK : ∀ (B : Finset κ) (F : κ → E3) (x₀ : E3),
      (∀ j ∈ B, ∀ k ∈ B, j ≠ k → r ≤ dist (F j) (F k)) →
      (∀ j ∈ B, dist (F j) x₀ < 4 * (ρ : ℝ)) → B.card ≤ 385 ^ 3 := by
    intro B F x₀ hsep hball
    have h := card_le_of_separated_ball B F hr hR x₀ hsep hball
    have hnum : 1 + 2 * (4 * (ρ : ℝ)) / r = 385 := by
      have hne : (ρ : ℝ) ≠ 0 := ne_of_gt hρR
      rw [hrdef]
      field_simp
      norm_num
    rw [hnum] at h
    exact_mod_cast h
  -- step 1: a maximal `r`-separated subset in the `x`-endpoint
  obtain ⟨A, hAsub, hAsep, hAcov⟩ := exists_maximal_separated t Φ hr
  have hAcard : A.card ≤ 385 ^ 3 := by
    refine hK A Φ a hAsep ?_
    intro j hj
    have := hx j (hAsub hj)
    have h3 : (3 : ℝ) * (ρ : ℝ) < 4 * (ρ : ℝ) := by linarith
    exact lt_of_le_of_lt this h3
  have htne : t.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨j₀, hj₀⟩ := htne
  haveI : Nonempty κ := ⟨j₀⟩
  choose! f hfA hfd using hAcov
  -- step 2: a fibre of the representative map that is too big to be `r`-separated in `y`
  have hlt : A.card * 385 ^ 3 < t.card := by
    calc A.card * 385 ^ 3 ≤ 385 ^ 3 * 385 ^ 3 := Nat.mul_le_mul_right _ hAcard
      _ = 385 ^ 6 := by norm_num
      _ < t.card := hcard
  obtain ⟨y, hyA, hfib⟩ :=
    Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to (f := f) (t := A) hfA hlt
  set fib : Finset κ := {x ∈ t | f x = y} with hfib_def
  have hfibsub : fib ⊆ t := Finset.filter_subset _ _
  have hnotsep : ¬ (∀ j ∈ fib, ∀ k ∈ fib, j ≠ k → r ≤ dist (Ψ j) (Ψ k)) := by
    intro hsep
    have hb : ∀ j ∈ fib, dist (Ψ j) b < 4 * (ρ : ℝ) := by
      intro j hj
      have := hy j (hfibsub hj)
      linarith
    have := hK fib Ψ b hsep hb
    omega
  have hpair : ∃ j ∈ fib, ∃ k ∈ fib, j ≠ k ∧ dist (Ψ j) (Ψ k) < r := by
    by_contra hc
    apply hnotsep
    intro j hj k hk hjk
    by_contra hlt2
    exact hc ⟨j, hj, k, hk, hjk, not_le.mp hlt2⟩
  obtain ⟨j, hjfib, k, hkfib, hjk, hΨlt⟩ := hpair
  have hjt : j ∈ t := hfibsub hjfib
  have hkt : k ∈ t := hfibsub hkfib
  have hfj : f j = y := (Finset.mem_filter.1 hjfib).2
  have hfk : f k = y := (Finset.mem_filter.1 hkfib).2
  have hΦlt : dist (Φ j) (Φ k) < 2 * r := by
    have h1 : dist (Φ j) (Φ y) < r := by have := hfd j hjt; rwa [hfj] at this
    have h2 : dist (Φ k) (Φ y) < r := by have := hfd k hkt; rwa [hfk] at this
    have := dist_triangle (Φ j) (Φ y) (Φ k)
    rw [dist_comm (Φ y) (Φ k)] at this
    linarith
  -- step 3: the two are axial translates up to the tolerated error
  set α : ℝ := θ k - θ j with hα_def
  have hαbd : |α| ≤ 1 / 144 := by
    have h1 := abs_le.mp (hθ j hjt)
    have h2 := abs_le.mp (hθ k hkt)
    rw [hα_def, abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have hdir : ‖u - (V j).direction‖ ≤ 6 * (ρ : ℝ) := by
    have heq : u - (V j).direction = (b - Ψ j) - (a - Φ j) := by
      simp only [hΦ, hΨ, hu, Tube.direction]
      module
    have h1 : ‖a - Φ j‖ ≤ 3 * (ρ : ℝ) := by
      rw [← dist_eq_norm, dist_comm]; exact hx j hjt
    have h2 : ‖b - Ψ j‖ ≤ 3 * (ρ : ℝ) := by
      rw [← dist_eq_norm, dist_comm]; exact hy j hjt
    calc ‖u - (V j).direction‖ = ‖(b - Ψ j) - (a - Φ j)‖ := by rw [heq]
      _ ≤ ‖b - Ψ j‖ + ‖a - Φ j‖ := norm_sub_le _ _
      _ ≤ 6 * (ρ : ℝ) := by linarith
  have hαdir : ‖α • (u - (V j).direction)‖ ≤ (ρ : ℝ) / 24 := by
    rw [norm_smul, Real.norm_eq_abs]
    calc |α| * ‖u - (V j).direction‖ ≤ (1 / 144) * (6 * (ρ : ℝ)) := by
          apply mul_le_mul hαbd hdir (norm_nonneg _) (by norm_num)
      _ = (ρ : ℝ) / 24 := by ring
  have hex : dist ((V k).x) ((V j).x + α • (V j).direction)
      ≤ 1 / (4 * (Module.finrank ℝ E3 : ℝ)) * (ρ : ℝ) := by
    have heq : (V k).x - ((V j).x + α • (V j).direction)
        = (Φ k - Φ j) + α • (u - (V j).direction) := by
      simp only [hΦ, hα_def, Tube.direction]
      module
    have h1 : ‖Φ k - Φ j‖ < 2 * r := by rw [← dist_eq_norm]; rwa [dist_comm] at hΦlt
    have hfr : (Module.finrank ℝ E3 : ℝ) = 3 := by simp
    rw [dist_eq_norm, heq, hfr]
    calc ‖(Φ k - Φ j) + α • (u - (V j).direction)‖
        ≤ ‖Φ k - Φ j‖ + ‖α • (u - (V j).direction)‖ := norm_add_le _ _
      _ ≤ 2 * r + (ρ : ℝ) / 24 := by linarith
      _ = 1 / (4 * (3 : ℝ)) * (ρ : ℝ) := by rw [hrdef]; ring
  have hey : dist ((V k).y) ((V j).y + α • (V j).direction)
      ≤ 1 / (4 * (Module.finrank ℝ E3 : ℝ)) * (ρ : ℝ) := by
    have heq : (V k).y - ((V j).y + α • (V j).direction)
        = (Ψ k - Ψ j) + α • (u - (V j).direction) := by
      simp only [hΨ, hα_def, Tube.direction]
      module
    have h1 : ‖Ψ k - Ψ j‖ < r := by rw [← dist_eq_norm]; rwa [dist_comm] at hΨlt
    have hfr : (Module.finrank ℝ E3 : ℝ) = 3 := by simp
    rw [dist_eq_norm, heq, hfr]
    calc ‖(Ψ k - Ψ j) + α • (u - (V j).direction)‖
        ≤ ‖Ψ k - Ψ j‖ + ‖α • (u - (V j).direction)‖ := norm_add_le _ _
      _ ≤ r + (ρ : ℝ) / 24 := by linarith
      _ ≤ 1 / (4 * (3 : ℝ)) * (ρ : ℝ) := by rw [hrdef]; linarith
  have hαsmall : |α| ≤ 1 / (4 * (Module.finrank ℝ E3 : ℝ)) := by
    have hfr : (Module.finrank ℝ E3 : ℝ) = 3 := by simp
    rw [hfr]
    linarith [hαbd]
  exact Tube.not_essDistinct_of_axial_slide hρ0 hρ1 (V j) (V k) hαsmall hex hey
    (hED hjt hkt hjk)

/-! ### The punchline: an axial family of bounded size admits no essentially distinct cover -/

/-- The centre of an axial translate, computed once. -/
private theorem center_of_axial {δ : NNReal} {T T₀ : Tube δ E3} {c : ℝ}
    (hTx : T.x = T₀.x + c • T₀.direction) (hTy : T.y = T₀.y + c • T₀.direction) :
    T.center = T₀.center + c • T₀.direction := by
  simp only [Tube.center, hTx, hTy, midpoint_eq_smul_add, invOf_eq_inv]
  module

/-- **A collinear family of more than `385 ^ 6` `δ`-tubes admits no essentially distinct
`ρ`-tube cover.**

`𝕋 = {T i}` is a family of `δ`-tubes that are exact axial translates of a fixed `T₀`, at offsets
`θ i` inside `[-1/288, 1/288]` and pairwise more than `6ρ` apart. Then no `ρ`-tube family can be
simultaneously a cover of `𝕋` and pairwise essentially distinct.

Two steps, both already proved above. The `6ρ`-separation of the offsets and
`Kakeya.VeryNotSticky.dist_center_le_of_carrier_subset` make the covering assignment injective, so
the cover has at least `#𝕋` distinct members; and
`Kakeya.VeryNotSticky.card_le_of_ed_of_endpoints_confined` caps an essentially distinct family of
`ρ`-tubes whose cores are pinned to the common axis at `385 ^ 6`, **independently of `ρ`**.

**This is the obstruction to clause (e) of
`Kakeya.VeryNotSticky.BandUniformRefinement`.** The coarsening asked for by
`Kakeya.VeryNotSticky.eventually_tubeCount_of_edCover` does not exist for such a family, and
`385 ^ 6` is a constant: the family is of *bounded* size, far below the `δ^{-1}` that the tube
count needs. So the `ρ`-count binder `hcount` of
`Kakeya.VeryNotSticky.exists_setup_caseSideData` is satisfied — vacuously, there being no legal
cover to test it on — by families with `#𝕋` bounded, and cannot force `#𝕋 ≥ δ^{-1}`;
see `Kakeya.VeryNotSticky.not_edCover_of_axialFamily_of_le`. -/
theorem not_edCover_of_axialFamily {δ ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    {ι κ : Type*} {s : Finset ι} {T : ι → Tube δ E3} {θ : ι → ℝ} {T₀ : Tube δ E3}
    (hTx : ∀ i ∈ s, (T i).x = T₀.x + θ i • T₀.direction)
    (hTy : ∀ i ∈ s, (T i).y = T₀.y + θ i • T₀.direction)
    (hθ : ∀ i ∈ s, |θ i| ≤ 1 / 288)
    (hsep : ∀ i ∈ s, ∀ i' ∈ s, i ≠ i' → 6 * (ρ : ℝ) < |θ i - θ i'|)
    (hbig : 385 ^ 6 < s.card)
    (tρ : Finset κ) (Tρ : κ → Tube ρ E3)
    (hcov : ∀ i ∈ s, ∃ j ∈ tρ, (T i).carrier ⊆ (Tρ j).carrier)
    (hED : (tρ : Set κ).Pairwise
      fun j k ↦ IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) :
    False := by
  classical
  have hρR : (0 : ℝ) < (ρ : ℝ) := by exact_mod_cast hρ0
  have hsne : s.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨i₁, hi₁⟩ := hsne
  obtain ⟨j₁, hj₁, -⟩ := hcov i₁ hi₁
  haveI : Nonempty κ := ⟨j₁⟩
  haveI : Nonempty (Tube ρ E3) := ⟨Tρ j₁⟩
  choose! g hg hgsub using hcov
  -- the covering assignment is injective
  have hginj : ∀ i ∈ s, ∀ i' ∈ s, g i = g i' → i = i' := by
    intro i hi i' hi' hgg
    by_contra hne
    have h1 := dist_center_le_of_carrier_subset (T i) (Tρ (g i)) (hgsub i hi)
    have h2 := dist_center_le_of_carrier_subset (T i') (Tρ (g i')) (hgsub i' hi')
    rw [hgg] at h1
    have h3 : dist (T i).center (T i').center ≤ 6 * (ρ : ℝ) := by
      have h := dist_triangle (T i).center (Tρ (g i')).center (T i').center
      rw [dist_comm (Tρ (g i')).center (T i').center] at h
      linarith
    have h4 : dist (T i).center (T i').center = |θ i - θ i'| := by
      rw [center_of_axial (hTx i hi) (hTy i hi), center_of_axial (hTx i' hi') (hTy i' hi'),
        dist_eq_norm,
        show T₀.center + θ i • T₀.direction - (T₀.center + θ i' • T₀.direction)
          = (θ i - θ i') • T₀.direction from by module,
        norm_smul, Tube.norm_direction, Real.norm_eq_abs, mul_one]
    rw [h4] at h3
    exact absurd h3 (not_le.mpr (hsep i hi i' hi' hne))
  -- orient the covering tubes so that endpoints match endpoints
  have hWex : ∀ i ∈ s, ∃ W : Tube ρ E3, W.carrier = (Tρ (g i)).carrier ∧
      dist (T i).x W.x ≤ 3 * (ρ : ℝ) ∧ dist (T i).y W.y ≤ 3 * (ρ : ℝ) := by
    intro i hi
    rcases dist_endpoints_le_of_carrier_subset (T i) (Tρ (g i)) (hgsub i hi) with
      ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨Tρ (g i), rfl, h1, h2⟩
    · exact ⟨(Tρ (g i)).reverse, rfl, by simpa using h1, by simpa using h2⟩
  choose! W hWcar hWx hWy using hWex
  -- the oriented family is essentially distinct
  have hED' : (s : Set ι).Pairwise
      fun i i' ↦ IsEssentiallyDistinct (W i).carrier (W i').carrier := by
    intro i hi i' hi' hne
    rw [hWcar i hi, hWcar i' hi']
    exact hED (hg i hi) (hg i' hi') (fun h => hne (hginj i hi i' hi' h))
  -- the endpoints, normalised by the axial slide
  have hx' : ∀ i ∈ s, dist ((W i).x - θ i • (T₀.y - T₀.x)) T₀.x ≤ 3 * (ρ : ℝ) := by
    intro i hi
    have h : (W i).x - θ i • (T₀.y - T₀.x) - T₀.x = (W i).x - (T i).x := by
      rw [hTx i hi]
      simp only [Tube.direction]
      module
    rw [dist_eq_norm, h, ← dist_eq_norm, dist_comm]
    exact hWx i hi
  have hy' : ∀ i ∈ s, dist ((W i).y - θ i • (T₀.y - T₀.x)) T₀.y ≤ 3 * (ρ : ℝ) := by
    intro i hi
    have h : (W i).y - θ i • (T₀.y - T₀.x) - T₀.y = (W i).y - (T i).y := by
      rw [hTy i hi]
      simp only [Tube.direction]
      module
    rw [dist_eq_norm, h, ← dist_eq_norm, dist_comm]
    exact hWy i hi
  have := card_le_of_ed_of_endpoints_confined hρ0 hρ1 s W T₀.x T₀.y θ hθ hx' hy' hED'
  omega

/-- **The `ρ`-count binder is met, vacuously, by a family of bounded cardinality — at every
scale of the window at once.**

The binder `hcount` of `Kakeya.VeryNotSticky.exists_setup_caseSideData` asks that *every*
essentially distinct `ρ`-tube cover of `𝕋` have at least `ρ^{-2-ζ}` members, for every `ρ` in the
window.  For the axial family of `Kakeya.VeryNotSticky.not_edCover_of_axialFamily` there is **no**
such cover at any scale `ρ ≤ ρmax`, so the binder holds with nothing to check — while `#𝕋` is a
fixed constant.  Only the coarse endpoint of the window has to be checked, the separation
hypothesis being monotone in `ρ`.

`Kakeya.VeryNotSticky.eventually_tubeCount_of_edCover` is the only route in the tree from `hcount`
to the field `Kakeya.VeryNotSticky.tube_count`, and
`Kakeya.VeryNotSticky.tubeCount_of_parent_of_retention` records that `tube_count` needs
`#𝕋 ≳ δ^{-1}`.  This lemma says the binder cannot supply it. -/
theorem not_edCover_of_axialFamily_of_le {δ : NNReal} {ρmax : NNReal}
    {ι : Type*} {s : Finset ι} {T : ι → Tube δ E3} {θ : ι → ℝ} {T₀ : Tube δ E3}
    (hTx : ∀ i ∈ s, (T i).x = T₀.x + θ i • T₀.direction)
    (hTy : ∀ i ∈ s, (T i).y = T₀.y + θ i • T₀.direction)
    (hθ : ∀ i ∈ s, |θ i| ≤ 1 / 288)
    (hsep : ∀ i ∈ s, ∀ i' ∈ s, i ≠ i' → 6 * (ρmax : ℝ) < |θ i - θ i'|)
    (hbig : 385 ^ 6 < s.card)
    {ρ : NNReal} (hρ0 : 0 < ρ) (hρmax : ρ ≤ ρmax) (hρ1 : ρ ≤ 1)
    {κ : Type*} (tρ : Finset κ) (Tρ : κ → Tube ρ E3)
    (hcov : ∀ i ∈ s, ∃ j ∈ tρ, (T i).carrier ⊆ (Tρ j).carrier)
    (hED : (tρ : Set κ).Pairwise
      fun j k ↦ IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) :
    False := by
  have hle : (ρ : ℝ) ≤ (ρmax : ℝ) := by exact_mod_cast hρmax
  have hsep' : ∀ i ∈ s, ∀ i' ∈ s, i ≠ i' → 6 * (ρ : ℝ) < |θ i - θ i'| := by
    intro i hi i' hi' hne
    have h := hsep i hi i' hi' hne
    linarith
  exact not_edCover_of_axialFamily hρ0 hρ1 hTx hTy hθ hsep' hbig tρ Tρ hcov hED

/-! ### Non-vacuity: the forbidden family exists, inside the unit ball -/

/-- **The obstruction is not vacuous.**  For every `N` and every `ρ` below
`1 / (6 · 288 · (N+1))` there is a family of `N + 1` `δ`-tubes inside the closed unit ball that
are exact axial translates of one another, at offsets inside `[0, 1/288]` and pairwise more than
`6ρ` apart — exactly the hypotheses of `Kakeya.VeryNotSticky.not_edCover_of_axialFamily`.

Without this the obstruction could be an empty statement; with it,
`Kakeya.VeryNotSticky.not_edCover_of_axialFamily` says something about families the target's own
binders allow.  Compare `Kakeya.VeryNotSticky.exists_productNet_of_threshold_le`, the sharpness
witness of the transverse-angular pricing. -/
theorem exists_axialFamily {δ ρ : NNReal} (N : ℕ) (hδ : (δ : ℝ) ≤ 1 / 4)
    (hρ : (ρ : ℝ) < 1 / (6 * 288 * ((N : ℝ) + 1))) :
    ∃ (T : Fin (N + 1) → Tube δ E3) (θ : Fin (N + 1) → ℝ) (T₀ : Tube δ E3),
      (∀ i, (T i).x = T₀.x + θ i • T₀.direction) ∧
      (∀ i, (T i).y = T₀.y + θ i • T₀.direction) ∧
      (∀ i, |θ i| ≤ 1 / 288) ∧
      (∀ i i', i ≠ i' → 6 * (ρ : ℝ) < |θ i - θ i'|) ∧
      (∀ i, (T i).carrier ⊆ Metric.closedBall (0 : E3) 1) ∧
      (∀ i, (T i).carrier ⊆ (T 0).carrier ∪ (T (Fin.last N)).carrier) := by
  classical
  set e : E3 := EuclideanSpace.single (0 : Fin 3) (1 : ℝ) with he
  have hen : ‖e‖ = 1 := by
    rw [he]
    simp
  set h : ℝ := 1 / (288 * ((N : ℝ) + 1)) with hh
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hhpos : 0 < h := by rw [hh]; positivity
  have hheq : h * (288 * ((N : ℝ) + 1)) = 1 := by
    rw [hh]; field_simp
  set θ : Fin (N + 1) → ℝ := fun i => (i : ℕ) * h with hθdef
  have hθnn : ∀ i, 0 ≤ θ i := by
    intro i; rw [hθdef]; positivity
  have hθle : ∀ i, θ i ≤ 1 / 288 := by
    intro i
    have hiN : ((i : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast Fin.is_le i
    have : θ i ≤ (N : ℝ) * h := by
      rw [hθdef]; exact mul_le_mul_of_nonneg_right hiN hhpos.le
    refine this.trans ?_
    nlinarith [hheq, hhpos, Nat.cast_nonneg (α := ℝ) N]
  have hdist : ∀ c : ℝ, dist ((-(1 / 2 : ℝ) + c) • e) (((1 / 2 : ℝ) + c) • e) = 1 := by
    intro c
    rw [dist_eq_norm, show (-(1 / 2 : ℝ) + c) • e - ((1 / 2 : ℝ) + c) • e = (-1 : ℝ) • e from
      by module, norm_smul, hen, Real.norm_eq_abs]
    norm_num
  refine ⟨fun i => Tube.mk' δ (hdist (θ i)), θ, Tube.mk' δ (hdist 0), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    have hdir : (Tube.mk' δ (hdist 0)).direction = e := by
      simp only [Tube.direction, Tube.mk'_x, Tube.mk'_y]
      module
    simp only [Tube.mk'_x, hdir]
    module
  · intro i
    have hdir : (Tube.mk' δ (hdist 0)).direction = e := by
      simp only [Tube.direction, Tube.mk'_x, Tube.mk'_y]
      module
    simp only [Tube.mk'_y, hdir]
    module
  · intro i
    rw [abs_of_nonneg (hθnn i)]
    exact hθle i
  · intro i i' hne
    have hnat : (i : ℕ) ≠ (i' : ℕ) := fun hh' => hne (Fin.ext hh')
    have hone : (1 : ℝ) ≤ |((i : ℕ) : ℝ) - ((i' : ℕ) : ℝ)| := by
      rcases Nat.lt_or_ge (i : ℕ) (i' : ℕ) with hlt | hge
      · have : ((i : ℕ) : ℝ) + 1 ≤ ((i' : ℕ) : ℝ) := by exact_mod_cast hlt
        rw [abs_of_nonpos (by linarith)]
        linarith
      · have hgt : (i' : ℕ) < (i : ℕ) := lt_of_le_of_ne hge (Ne.symm hnat)
        have : ((i' : ℕ) : ℝ) + 1 ≤ ((i : ℕ) : ℝ) := by exact_mod_cast hgt
        rw [abs_of_nonneg (by linarith)]
        linarith
    have hfac : |θ i - θ i'| = |((i : ℕ) : ℝ) - ((i' : ℕ) : ℝ)| * h := by
      rw [hθdef]
      simp only []
      rw [← sub_mul, abs_mul, abs_of_pos hhpos]
    have hh6 : 6 * (ρ : ℝ) < h := by
      rw [hh]
      have : 6 * (ρ : ℝ) < 6 * (1 / (6 * 288 * ((N : ℝ) + 1))) := by linarith
      calc 6 * (ρ : ℝ) < 6 * (1 / (6 * 288 * ((N : ℝ) + 1))) := this
        _ = 1 / (288 * ((N : ℝ) + 1)) := by field_simp
    rw [hfac]
    nlinarith [hhpos, hone, hh6]
  · intro i p hp
    have hδ0 : (0 : ℝ) ≤ (δ : ℝ) := δ.coe_nonneg
    simp only [Tube.mk'_carrier] at hp
    obtain ⟨z, hz, hpz⟩ := Set.mem_iUnion₂.1 hp
    have hzball : z ∈ Metric.closedBall (0 : E3) (1 / 2 + 1 / 288) := by
      refine (convex_closedBall (0 : E3) (1 / 2 + 1 / 288)).segment_subset ?_ ?_ hz
      · rw [Metric.mem_closedBall, dist_zero_right, norm_smul, hen, mul_one, Real.norm_eq_abs]
        have h1 := hθnn i
        have h2 := hθle i
        rw [abs_le]
        exact ⟨by linarith, by linarith⟩
      · rw [Metric.mem_closedBall, dist_zero_right, norm_smul, hen, mul_one, Real.norm_eq_abs]
        have h1 := hθnn i
        have h2 := hθle i
        rw [abs_le]
        exact ⟨by linarith, by linarith⟩
    rw [Metric.mem_closedBall, dist_zero_right] at hzball ⊢
    have hpz' : ‖p - z‖ ≤ (δ : ℝ) := by
      rw [← dist_eq_norm]; exact Metric.mem_closedBall.1 hpz
    calc ‖p‖ = ‖(p - z) + z‖ := by congr 1; abel
      _ ≤ ‖p - z‖ + ‖z‖ := norm_add_le _ _
      _ ≤ (δ : ℝ) + (1 / 2 + 1 / 288) := by linarith
      _ ≤ 1 := by linarith
  · intro i p hp
    simp only [Tube.mk'_carrier] at hp ⊢
    obtain ⟨z, hz, hpz⟩ := Set.mem_iUnion₂.1 hp
    have hθ0 : θ 0 = 0 := by rw [hθdef]; simp
    have hθL : θ (Fin.last N) = (N : ℝ) * h := by rw [hθdef]; simp
    have hθiL : θ i ≤ θ (Fin.last N) := by
      simp only [hθdef, Fin.val_last]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast Fin.is_le i) hhpos.le
    have hθLle : θ (Fin.last N) ≤ 1 / 288 := hθle _
    -- parametrise the segment
    rw [segment_eq_image'] at hz
    obtain ⟨t, ht, rfl⟩ := hz
    have hseg : ∀ (c u : ℝ), 0 ≤ u → u ≤ 1 →
        ((-(1 / 2 : ℝ) + c) • e + u • (((1 / 2 : ℝ) + c) • e - (-(1 / 2 : ℝ) + c) • e))
          = (-(1 / 2 : ℝ) + (c + u)) • e := by
      intro c u _ _
      module
    have hrw : ((-(1 / 2 : ℝ) + θ i) • e
        + t • (((1 / 2 : ℝ) + θ i) • e - (-(1 / 2 : ℝ) + θ i) • e))
        = (-(1 / 2 : ℝ) + (θ i + t)) • e := hseg (θ i) t ht.1 ht.2
    simp only [] at hpz
    rw [hrw] at hpz
    rcases le_total (θ i + t) 1 with hle | hge
    · left
      refine Set.mem_iUnion₂.2 ⟨(-(1 / 2 : ℝ) + (θ i + t)) • e, ?_, hpz⟩
      rw [segment_eq_image']
      refine ⟨θ i + t, ⟨by linarith [hθnn i, ht.1], hle⟩, ?_⟩
      rw [hθ0]
      have := hseg 0 (θ i + t) (by linarith [hθnn i, ht.1]) hle
      simpa using this
    · right
      refine Set.mem_iUnion₂.2 ⟨(-(1 / 2 : ℝ) + (θ i + t)) • e, ?_, hpz⟩
      rw [segment_eq_image']
      refine ⟨θ i + t - θ (Fin.last N), ⟨by linarith, by linarith [ht.2]⟩, ?_⟩
      have := hseg (θ (Fin.last N)) (θ i + t - θ (Fin.last N))
        (by linarith) (by linarith [ht.2])
      simp only []
      rw [this]
      ring_nf

/-- **The compiled witness.**  At any `ρ` below `1 / (6 · 288 · (385^6 + 1))` there is a family of
`385^6 + 1` `δ`-tubes in the closed unit ball for which **no** essentially distinct family of
`ρ`-tubes covers it.

This is the statement the run's record did not have: the coarsening asked for by
`Kakeya.VeryNotSticky.eventually_tubeCount_of_edCover` does not merely cost too much, it **does
not exist**, and the family that defeats it has *constant* cardinality. -/
theorem exists_family_without_edCover {δ ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hδ : (δ : ℝ) ≤ 1 / 4) (hρ : (ρ : ℝ) < 1 / (6 * 288 * ((385 ^ 6 : ℕ) + 1))) :
    ∃ T : Fin (385 ^ 6 + 1) → Tube δ E3,
      (∀ i, (T i).carrier ⊆ Metric.closedBall (0 : E3) 1) ∧
      ∀ {κ : Type} (tρ : Finset κ) (Tρ : κ → Tube ρ E3),
        (∀ i, ∃ j ∈ tρ, (T i).carrier ⊆ (Tρ j).carrier) →
        ¬ (tρ : Set κ).Pairwise
            (fun j k ↦ IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) := by
  obtain ⟨T, θ, T₀, hTx, hTy, hθ, hsep, hball, -⟩ :=
    exists_axialFamily (δ := δ) (ρ := ρ) (385 ^ 6) hδ (by exact_mod_cast hρ)
  refine ⟨T, hball, ?_⟩
  intro κ tρ Tρ hcov hED
  refine not_edCover_of_axialFamily (s := Finset.univ) hρ0 hρ1
    (fun i _ => hTx i) (fun i _ => hTy i) (fun i _ => hθ i)
    (fun i _ i' _ hne => hsep i i' hne) ?_ tρ Tρ (fun i _ => hcov i) hED
  simp

/-! ### The remaining binders of the target, for the witness family -/

/-- `δ ≤ ρ_k` for every grid index `k ≤ N`: the grid is antitone and bottoms out at `δ`. -/
private theorem le_gridScale_of_le {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) {N k : ℕ}
    (hk : k ≤ N) : δ ≤ Tube.gridScale δ N k := by
  have hexp : (k : ℝ) / (N : ℝ) ≤ 1 := by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp at hk
      simp [hk]
    · rw [div_le_one (by exact_mod_cast hN)]
      exact_mod_cast hk
  have h := NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 hexp
  rwa [NNReal.rpow_one] at h

/-- **The uniformity binder is met by any family with distinct cores**, at the constant `#𝕋`.

The hierarchy is the *singleton* one: every member is its own node at every grid scale, the node
being the member's own core rescaled to the grid radius.  All six clauses of GWZ Definition 2.1
and all four of Definition 2.2 then hold with branching number `1`, and the only constant that has
to be paid is the bounded-overlap one, for which `#𝕋` is always enough.

This is why the binder `huni` of `Kakeya.VeryNotSticky.exists_setup_caseSideData` — an *unbounded*
`∃ C` — carries no information: it is met by every family. -/
theorem nonempty_shadedUniformTubeSet_of_core_injOn {δ : NNReal} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    {ι : Type*} (s : Finset ι) (V : ι → ShadedTube δ E3) (N : ℕ) {C : NNReal}
    (hC : 1 ≤ C) (hCcard : (s.card : NNReal) ≤ C)
    (hinj : ∀ i ∈ s, ∀ j ∈ s, (V i).x = (V j).x → (V i).y = (V j).y → i = j) :
    Nonempty (ShadedTube.ShadedUniformTubeSet s V N C) := by
  classical
  have hnode : ∀ (k : ℕ), k ≤ N → ∀ i : ι,
      ((V i).toTube).toConvexSpaceBody
        ≤ (((V i).toTube).rescale (Tube.gridScale δ N k)).toConvexSpaceBody := by
    intro k hk i
    have h := Tube.rescale_le_rescale_of_endpoint_dist ((V i).toTube) ((V i).toTube)
      (τ := δ) (θ := Tube.gridScale δ N k)
      (by
        simp only [sub_self, norm_zero, add_zero, zero_add]
        exact_mod_cast le_gridScale_of_le hδ0 hδ1 hk)
    rwa [Tube.toConvexSpaceBody_rescale_self] at h
  have hnest : ∀ (k : ℕ), k + 1 ≤ N → ∀ i : ι,
      (((V i).toTube).rescale (Tube.gridScale δ N (k + 1))).toConvexSpaceBody
        ≤ (((V i).toTube).rescale (Tube.gridScale δ N k)).toConvexSpaceBody := by
    intro k hk i
    refine Tube.rescale_le_rescale_of_endpoint_dist ((V i).toTube) ((V i).toTube) ?_
    simp only [sub_self, norm_zero, add_zero, zero_add]
    exact_mod_cast Tube.gridScale_antitone hδ0 hδ1 N (by omega : k ≤ k + 1)
  have hclass : ∀ j : ι, j ∈ s → Tube.coverClass s (fun i => i) j = {j} := by
    intro j hj
    ext i
    simp only [Tube.coverClass, Finset.mem_filter, Finset.mem_singleton]
    exact ⟨fun h => h.2, fun h => ⟨h ▸ hj, h⟩⟩
  let 𝒢 : Tube.GridCoverSystem s (fun i => (V i).toTube) N :=
    { indexSet := fun _ => s
      assign := fun _ i => i
      tube := fun k i => ((V i).toTube).rescale (Tube.gridScale δ N k)
      assign_mem := fun _ _ i hi => hi
      le_tube_assign := fun k hk i _ => hnode k hk i
      nested := fun _ _ _ _ _ _ h => h
      tube_nested := fun k hk i _ => hnest k hk i }
  let 𝒰 : Tube.UniformTubeSet s (fun i => (V i).toTube) N C :=
    { cover := 𝒢
      branchingN := fun _ => 1
      tube_injOn := by
        intro k _ i hi j hj hij
        have hx := congrArg Tube.x hij
        have hy := congrArg Tube.y hij
        exact hinj i hi j hj hx hy
      boundedOverlap := by
        intro k _ W
        refine le_trans ?_ hCcard
        exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
      card_class_le := by
        intro k _ j hj
        rw [hclass j hj, Finset.card_singleton]
        simpa using hC
      le_card_class := by
        intro k _ j hj
        rw [hclass j hj, Finset.card_singleton]
        simpa using hC }
  have hshadeClass : ∀ (k : ℕ) (i : ι), i ∈ s → ∀ x : E3, x ∈ (V i).shade →
      ShadedTube.shadeClass s V (fun i => i) i x = {i} := by
    intro k i hi x hx
    ext j
    simp only [ShadedTube.shadeClass, Finset.mem_filter, Finset.mem_singleton, hclass i hi]
    constructor
    · intro h
      exact h.1
    · intro h
      subst h
      exact ⟨rfl, hx⟩
  exact ⟨{ tubeUniform := 𝒰
           branchingN := fun _ => 1
           localN := fun _ _ => 1
           card_shadeClass_le := by
             intro x _ k _ i hi hxi
             rw [hshadeClass k i hi x hxi, Finset.card_singleton]
             simpa using hC
           le_card_shadeClass := by
             intro x _ k _ i hi hxi
             rw [hshadeClass k i hi x hxi, Finset.card_singleton]
             simpa using hC
           branchingN_le := by
             intro x _ k _
             simpa using hC
           le_branchingN := by
             intro x _ k _
             simpa using hC }⟩

/-! ### The refutation -/

open Topology Filter in
/-- Eventually `δ^p ≤ c`, for `p > 0` and `c > 0`: the threshold form used below. -/
private theorem eventually_rpow_le {c : NNReal} (hc : 0 < c) {p : ℝ} (hp : 0 < p) :
    ∀ᶠ (δ : NNReal) in 𝓝[>] 0, δ ^ p ≤ c := by
  have hd : (0 : NNReal) < c ^ (1 / p) := NNReal.rpow_pos hc
  filter_upwards [Ioo_mem_nhdsGT hd] with δ hδ
  have h1 : δ ≤ c ^ (1 / p) := hδ.2.le
  calc δ ^ p ≤ (c ^ (1 / p)) ^ p := NNReal.rpow_le_rpow h1 hp.le
    _ = c := by
        rw [← NNReal.rpow_mul, one_div, inv_mul_cancel₀ hp.ne', NNReal.rpow_one]

open MeasureTheory Topology Filter ShadedBody in
/-- **The witness family, with all five binders of the pre-centred target verified and its multiplicity
bounded below.**

`385^6 + 1` `δ`-tubes on a common axis inside the closed unit ball, shaded by their own carriers.
Every pre-centred binder of `Kakeya.VeryNotSticky.exists_setup_caseSideData` — equivalently, of
`Kakeya.multiplicity_le_of_card_isEssDistinct_ge`, whose binder list is the same — holds, the
`ρ`-count one **vacuously**; and the multiplicity is at least half the cardinality, because the
whole family lies inside the union of just two of its members. -/
theorem exists_witnessFamily {δ : NNReal} {exscal η : ℝ} (hδ0 : 0 < δ) (hδ4 : (δ : ℝ) ≤ 1 / 4)
    (hexscal : 0 < exscal) (hη : 0 < η)
    (hgap : ((δ ^ exscal : NNReal) : ℝ) < 1 / (6 * 288 * (((385 ^ 6 : ℕ) : ℝ) + 1)))
    (hden : (((385 ^ 6 + 1 : ℕ) : ℕ) : ENNReal) ≤ (δ : ENNReal) ^ (-η)) :
    ∃ T : Fin (385 ^ 6 + 1) → ShadedTube δ E3,
      (∀ i ∈ (Finset.univ : Finset (Fin (385 ^ 6 + 1))),
        (T i).carrier ⊆ Metric.closedBall 0 1) ∧
      (∃ C : NNReal, Nonempty (ShadedTube.ShadedUniformTubeSet
        (Finset.univ : Finset (Fin (385 ^ 6 + 1))) T (Tube.ssfGridLen δ) C)) ∧
      maxDensity (Finset.univ : Finset (Fin (385 ^ 6 + 1)))
        (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η) ∧
      ShadedBody.fullness (Finset.univ : Finset (Fin (385 ^ 6 + 1)))
        (fun i ↦ (T i).toShadedBody) ≥ δ ^ η ∧
      (∀ (ζ : ℝ) (ρ : NNReal), ρ ∈ Set.Icc (δ ^ (1 - exscal)) (δ ^ exscal) →
        ∀ {κ : Type} (tρ : Finset κ) (Tρ : κ → Tube ρ E3),
          (∀ i ∈ (Finset.univ : Finset (Fin (385 ^ 6 + 1))), ∃ j ∈ tρ,
            (T i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) →
          (tρ : Set κ).Pairwise
            (fun j k ↦ IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) →
          (ρ : ℝ) ^ (-2 - ζ) ≤ (tρ.card : ℝ)) ∧
      ((385 ^ 6 + 1 : ℕ) : ENNReal) / 2 ≤ ShadedBody.multiplicity
        (Finset.univ : Finset (Fin (385 ^ 6 + 1))) (fun i ↦ (T i).toShadedBody) := by
  classical
  have hδ1 : δ ≤ 1 := by
    rw [← NNReal.coe_le_coe]; push_cast; linarith
  obtain ⟨Wt, θ, T₀, hTx, hTy, hθ, hsepθ, hball, hun⟩ :=
    exists_axialFamily (δ := δ) (ρ := δ ^ exscal) (385 ^ 6) hδ4 hgap
  set ST : Fin (385 ^ 6 + 1) → ShadedTube δ E3 := fun i =>
    { toTube := Wt i
      shade := (Wt i).carrier
      measurableSet_shade := (Wt i).toConvexSpaceBody.isCompact.measurableSet
      shade_subset := subset_rfl } with hSTdef
  -- (1) the ball binder
  have hballST : ∀ i ∈ (Finset.univ : Finset (Fin (385 ^ 6 + 1))),
      (ST i).carrier ⊆ Metric.closedBall 0 1 := fun i _ => hball i
  -- injectivity of the cores
  have hcoreinj : ∀ i ∈ (Finset.univ : Finset (Fin (385 ^ 6 + 1))),
      ∀ j ∈ (Finset.univ : Finset (Fin (385 ^ 6 + 1))),
      (ST i).x = (ST j).x → (ST i).y = (ST j).y → i = j := by
    intro i _ j _ hx _
    by_contra hne
    have hxx : T₀.x + θ i • T₀.direction = T₀.x + θ j • T₀.direction := by
      rw [← hTx i, ← hTx j]; exact hx
    have hsub : (θ i - θ j) • T₀.direction = 0 := by
      rw [sub_smul, sub_eq_zero]
      exact add_left_cancel hxx
    have hz : θ i - θ j = 0 := by
      have hn := congrArg norm hsub
      rw [norm_smul, Tube.norm_direction, mul_one, Real.norm_eq_abs, norm_zero] at hn
      exact abs_eq_zero.mp hn
    have hs := hsepθ i j hne
    rw [hz, abs_zero] at hs
    have hpos : (0 : ℝ) < ((δ ^ exscal : NNReal) : ℝ) := by
      exact_mod_cast NNReal.rpow_pos hδ0
    linarith
  -- (2) the uniformity binder
  have huniST : ∃ C : NNReal,
      Nonempty (ShadedTube.ShadedUniformTubeSet (Finset.univ : Finset (Fin (385 ^ 6 + 1))) ST
        (Tube.ssfGridLen δ) C) :=
    ⟨((Finset.univ : Finset (Fin (385 ^ 6 + 1))).card : NNReal) + 1,
      nonempty_shadedUniformTubeSet_of_core_injOn hδ0 hδ1 _ ST _
        le_add_self le_self_add hcoreinj⟩
  -- (3) the density binder
  have hmaxST : maxDensity (Finset.univ : Finset (Fin (385 ^ 6 + 1)))
      (fun i ↦ (ST i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η) := by
    refine le_trans (Kakeya.maxDensity_le_card _ _) ?_
    have hcard : (((Finset.univ : Finset (Fin (385 ^ 6 + 1))).card : ℕ) : ENNReal)
        = (((385 ^ 6 + 1 : ℕ) : ℕ) : ENNReal) := by
      simp
    rw [hcard]
    exact hden
  -- (4) the fullness binder
  have hfullST : ShadedBody.fullness (Finset.univ : Finset (Fin (385 ^ 6 + 1)))
      (fun i ↦ (ST i).toShadedBody) ≥ δ ^ η := by
    have hpos : ∀ i : Fin (385 ^ 6 + 1), 0 < volume (Wt i).carrier :=
      fun i => (Tube.volume_pos_and_lt_top hδ0 hδ1 (Wt i)).1
    have hfin : ∀ i : Fin (385 ^ 6 + 1), volume (Wt i).carrier < ⊤ :=
      fun i => (Tube.volume_pos_and_lt_top hδ0 hδ1 (Wt i)).2
    have hXne : (∑ i : Fin (385 ^ 6 + 1), volume (Wt i).carrier) ≠ 0 := by
      refine ne_of_gt (lt_of_lt_of_le (hpos 0) ?_)
      exact Finset.single_le_sum (f := fun i => volume (Wt i).carrier)
        (fun i _ => by positivity) (Finset.mem_univ 0)
    have hXtop : (∑ i : Fin (385 ^ 6 + 1), volume (Wt i).carrier) ≠ ⊤ :=
      (ENNReal.sum_lt_top.mpr (fun i _ => hfin i)).ne
    have hone : ShadedBody.fullness' (Finset.univ : Finset (Fin (385 ^ 6 + 1)))
        (fun i ↦ (ST i).toShadedBody) = 1 := ENNReal.div_self hXne hXtop
    have hfl : ShadedBody.fullness (Finset.univ : Finset (Fin (385 ^ 6 + 1)))
        (fun i ↦ (ST i).toShadedBody) = 1 := by
      simp only [ShadedBody.fullness, hone]
      rfl
    rw [ge_iff_le, hfl]
    exact NNReal.rpow_le_one hδ1 hη.le
  -- (5) the `ρ`-count binder, vacuously
  have hcountST : ∀ (ζ : ℝ) (ρ : NNReal), ρ ∈ Set.Icc (δ ^ (1 - exscal)) (δ ^ exscal) →
      ∀ {κ : Type} (tρ : Finset κ) (Tρ : κ → Tube ρ E3),
        (∀ i ∈ (Finset.univ : Finset (Fin (385 ^ 6 + 1))), ∃ j ∈ tρ,
          (ST i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) →
        (tρ : Set κ).Pairwise
          (fun j k ↦ IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) →
        (ρ : ℝ) ^ (-2 - ζ) ≤ (tρ.card : ℝ) := by
    intro ζ ρ hρmem κ tρ Tρ hcov hED
    have hρ0 : 0 < ρ := lt_of_lt_of_le (NNReal.rpow_pos hδ0) hρmem.1
    have hρmax : ρ ≤ δ ^ exscal := hρmem.2
    have hρ1 : ρ ≤ 1 := le_trans hρmax (NNReal.rpow_le_one hδ1 hexscal.le)
    exact absurd (not_edCover_of_axialFamily_of_le (s := Finset.univ) (T := Wt) (θ := θ)
      (T₀ := T₀)
      (fun i _ => hTx i) (fun i _ => hTy i) (fun i _ => hθ i)
      (fun i _ i' _ hne => hsepθ i i' hne) (by simp) hρ0 hρmax hρ1 tρ Tρ
      (fun i _ => by
        obtain ⟨j, hj, hle⟩ := hcov i (Finset.mem_univ i)
        exact ⟨j, hj, hle⟩) hED) not_false
  -- (6) the multiplicity, from the two-member union bound
  have hvol : ∀ i : Fin (385 ^ 6 + 1), volume (Wt i).carrier = volume (Wt 0).carrier := fun i =>
    _root_.Tube.volume_carrier_eq_volume_carrier (Wt i) (Wt 0)
  have hvpos : 0 < volume (Wt 0).carrier := (Tube.volume_pos_and_lt_top hδ0 hδ1 (Wt 0)).1
  have hvtop : volume (Wt 0).carrier < ⊤ := (Tube.volume_pos_and_lt_top hδ0 hδ1 (Wt 0)).2
  have hsum : ∑ i : Fin (385 ^ 6 + 1), volume ((ST i).toShadedBody).shade
      = ((385 ^ 6 + 1 : ℕ) : ENNReal) * volume (Wt 0).carrier := by
    have : ∀ i : Fin (385 ^ 6 + 1), volume ((ST i).toShadedBody).shade
        = volume (Wt 0).carrier := fun i => hvol i
    rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  have hUsub : (⋃ i ∈ (Finset.univ : Finset (Fin (385 ^ 6 + 1))), ((ST i).toShadedBody).shade)
      ⊆ (Wt 0).carrier ∪ (Wt (Fin.last (385 ^ 6))).carrier := by
    intro x hx
    obtain ⟨i, -, hxi⟩ := Set.mem_iUnion₂.1 hx
    exact hun i hxi
  have hUle : volume (⋃ i ∈ (Finset.univ : Finset (Fin (385 ^ 6 + 1))),
      ((ST i).toShadedBody).shade) ≤ 2 * volume (Wt 0).carrier := by
    refine le_trans (measure_mono hUsub) ?_
    refine le_trans (measure_union_le _ _) ?_
    rw [hvol (Fin.last (385 ^ 6)), two_mul]
  have hUne : volume (⋃ i ∈ (Finset.univ : Finset (Fin (385 ^ 6 + 1))),
      ((ST i).toShadedBody).shade) ≠ 0 := by
    refine ne_of_gt (lt_of_lt_of_le hvpos ?_)
    exact measure_mono (fun x hx => Set.mem_iUnion₂.2 ⟨0, Finset.mem_univ 0, hx⟩)
  refine ⟨ST, hballST, huniST, hmaxST, hfullST, hcountST, ?_⟩
  rw [ShadedBody.le_multiplicity_iff _ _ hUne]
  calc ((385 ^ 6 + 1 : ℕ) : ENNReal) / 2
        * volume (⋃ i ∈ (Finset.univ : Finset (Fin (385 ^ 6 + 1))), ((ST i).toShadedBody).shade)
      ≤ ((385 ^ 6 + 1 : ℕ) : ENNReal) / 2 * (2 * volume (Wt 0).carrier) := by gcongr
    _ = ((385 ^ 6 + 1 : ℕ) : ENNReal) * volume (Wt 0).carrier := by
        rw [← mul_assoc, ENNReal.div_mul_cancel (by norm_num) (by norm_num)]
    _ = ∑ i : Fin (385 ^ 6 + 1), volume ((ST i).toShadedBody).shade := hsum.symm

open MeasureTheory Topology Filter ShadedBody in
/-- **The conclusion of `Kakeya.VeryNotSticky.exists_setup_caseSideData` is false.**

The hypothesis `hsetup` is that conclusion, transcribed at universe `0`; nothing else is assumed
but `0 < exscal` and `0 < η`, two of the positivity binders the target already carries.  The
target's remaining binders — `hβ`, `hβ1`, `hζ`, `hϱ`, `params`, `hplankF`, `hKT`, `hF` — are
**not** used, so the refutation does not lean on the Katz–Tao or Frostman estimates and is not
vacuous for want of them.

**The witness** is the family of `Kakeya.VeryNotSticky.exists_family_without_edCover`: `385^6 + 1`
`δ`-tubes on a common axis inside the closed unit ball, shaded by their own carriers.  It meets
every binder:

* `hball` — by construction;
* `huni` — `Kakeya.VeryNotSticky.nonempty_shadedUniformTubeSet_of_core_injOn`, the binder being an
  *unbounded* `∃ C`;
* `hmax` — `Kakeya.maxDensity_le_card` bounds the density by the (constant) cardinality, and a
  constant is eventually below `δ^{-η}`;
* `hfull` — the shading is the whole carrier, so the fullness is `1`;
* `hcount` — **vacuously**, by `Kakeya.VeryNotSticky.not_edCover_of_axialFamily_of_le`: at every
  scale of the window there is no essentially distinct cover at all.

But the configuration the target produces carries `Kakeya.VeryNotSticky.tube_count`,
`1 ≤ δ·#cfg.s`, and `#cfg.s ≤ #𝕋 = 385^6 + 1` because the refinement reindexes a subfamily of the
given one.  At `δ < 1/(385^6+1)` that is false.

**What this settles.**  `tube_count` is not reachable from the binders: `hcount` is the only one
that bounds `#𝕋` from below, and it is met by a family of bounded size.  That is the whole content
here; which statement-level repair to prefer is not settled by this theorem and no longer belongs
in its docstring. -/
theorem not_setupConclusion {β ζ exscal ϱ η τ τ' : ℝ} (hexscal : 0 < exscal) (hη : 0 < η)
    (hsetup : ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type} (s : Finset ι) (T : ι → ShadedTube δ E3),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
        (∃ C : NNReal,
          Nonempty (ShadedTube.ShadedUniformTubeSet s T (Tube.ssfGridLen δ) C)) →
        maxDensity s (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η) →
        ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
        (∀ ρ : NNReal, ρ ∈ Set.Icc (δ ^ (1 - exscal)) (δ ^ exscal) →
          ∀ {κ : Type} (tρ : Finset κ) (Tρ : κ → Tube ρ E3),
            (∀ i ∈ s, ∃ j ∈ tρ, (T i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) →
            (tρ : Set κ).Pairwise
              (fun j k ↦ IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) →
            (ρ : ℝ) ^ (-2 - ζ) ≤ (tρ.card : ℝ)) →
        ∃ (cfg : VeryNotSticky.{0}) (bd : BallData cfg) (e : cfg.ι ≃ ι) (c : NNReal),
          (cfg.β = β ∧ cfg.ζ = ζ ∧ cfg.δ = δ ∧ cfg.exscal = exscal ∧ cfg.ϱ = ϱ ∧
              cfg.η = η) ∧
          ShadedBody.IsCRefinement (cfg.s.map e.toEmbedding)
              (fun i ↦ (cfg.T (e.symm i)).toShadedBody)
              s (fun i ↦ (T i).toShadedBody) c ∧
          (δ : ENNReal) ^ η ≤ (c : ENNReal) ∧
          Nonempty (CaseSideData cfg bd τ τ')) :
    False := by
  classical
  set MN : ℕ := 385 ^ 6 + 1 with hMN
  have hMR : (0 : ℝ) < (MN : ℝ) := by rw [hMN]; positivity
  obtain ⟨G, hGpos, hG⟩ : ∃ G : ℝ, 0 < G ∧ G = 1 / (6 * 288 * (((385 ^ 6 : ℕ) : ℝ) + 1)) :=
    ⟨_, by positivity, rfl⟩
  obtain ⟨cgap, hcgap⟩ : ∃ c : NNReal, (c : ℝ) = G / 2 := ⟨⟨G / 2, by positivity⟩, rfl⟩
  have hcgappos : 0 < cgap := by rw [← NNReal.coe_pos, hcgap]; positivity
  have h1 : ∀ᶠ (δ : NNReal) in 𝓝[>] 0, (δ : ℝ) ≤ 1 / 4 := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : NNReal) < 1 / 4 by norm_num)] with δ hδ
    exact_mod_cast hδ.2.le
  have h2 : ∀ᶠ (δ : NNReal) in 𝓝[>] 0, (δ : ℝ) * (MN : ℝ) < 1 := by
    obtain ⟨b, hb⟩ : ∃ b : NNReal, (b : ℝ) = 1 / (MN : ℝ) :=
      ⟨⟨1 / (MN : ℝ), by positivity⟩, rfl⟩
    have hbpos : (0 : NNReal) < b := by rw [← NNReal.coe_pos, hb]; positivity
    filter_upwards [Ioo_mem_nhdsGT hbpos] with δ hδ
    have hlt : (δ : ℝ) < (b : ℝ) := by exact_mod_cast hδ.2
    rw [hb, lt_div_iff₀ hMR] at hlt
    linarith
  have h3 : (0 : ENNReal) < (((MN : NNReal)) : ENNReal)⁻¹ := by
    rw [ENNReal.inv_pos]
    exact ENNReal.coe_ne_top
  have hthr : ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      δ ∈ Set.Ioi (0 : NNReal) ∧ (δ : ℝ) ≤ 1 / 4 ∧ δ ^ exscal ≤ cgap ∧
        (δ : ENNReal) ^ η ≤ (((MN : NNReal)) : ENNReal)⁻¹ ∧ (δ : ℝ) * (MN : ℝ) < 1 := by
    filter_upwards [self_mem_nhdsWithin, h1, eventually_rpow_le hcgappos hexscal,
      ENNReal.eventually_coe_rpow_le_of_pos hη h3, h2] with δ ha hb hc hd he
    exact ⟨ha, hb, hc, hd, he⟩
  obtain ⟨δ, hsetupδ, hδ0', hδ4, hδex, hδη, hδM⟩ := (hsetup.and hthr).exists
  have hδ0 : (0 : NNReal) < δ := hδ0'
  have hδ1 : δ ≤ 1 := by
    rw [← NNReal.coe_le_coe]; push_cast; linarith
  -- the witness family
  have hGlt : ((δ ^ exscal : NNReal) : ℝ) < G := by
    have h := hδex
    have : ((δ ^ exscal : NNReal) : ℝ) ≤ (cgap : ℝ) := by exact_mod_cast h
    rw [hcgap] at this
    linarith
  obtain ⟨Wt, θ, T₀, hTx, hTy, hθ, hsepθ, hball, -⟩ :=
    exists_axialFamily (δ := δ) (ρ := δ ^ exscal) (385 ^ 6) hδ4 (by rw [← hG]; exact hGlt)
  set ST : Fin (385 ^ 6 + 1) → ShadedTube δ E3 := fun i =>
    { toTube := Wt i
      shade := (Wt i).carrier
      measurableSet_shade := (Wt i).toConvexSpaceBody.isCompact.measurableSet
      shade_subset := subset_rfl } with hSTdef
  -- (1) the ball binder
  have hballST : ∀ i ∈ (Finset.univ : Finset (Fin (385 ^ 6 + 1))),
      (ST i).carrier ⊆ Metric.closedBall 0 1 := fun i _ => hball i
  -- injectivity of the cores
  have hcoreinj : ∀ i ∈ (Finset.univ : Finset (Fin (385 ^ 6 + 1))),
      ∀ j ∈ (Finset.univ : Finset (Fin (385 ^ 6 + 1))),
      (ST i).x = (ST j).x → (ST i).y = (ST j).y → i = j := by
    intro i _ j _ hx _
    by_contra hne
    have hxx : T₀.x + θ i • T₀.direction = T₀.x + θ j • T₀.direction := by
      rw [← hTx i, ← hTx j]; exact hx
    have hsub : (θ i - θ j) • T₀.direction = 0 := by
      rw [sub_smul, sub_eq_zero]
      exact add_left_cancel hxx
    have hz : θ i - θ j = 0 := by
      have hn := congrArg norm hsub
      rw [norm_smul, Tube.norm_direction, mul_one, Real.norm_eq_abs, norm_zero] at hn
      exact abs_eq_zero.mp hn
    have hs := hsepθ i j hne
    rw [hz, abs_zero] at hs
    have hpos : (0 : ℝ) < ((δ ^ exscal : NNReal) : ℝ) := by
      exact_mod_cast NNReal.rpow_pos hδ0
    linarith
  -- (2) the uniformity binder
  have huniST : ∃ C : NNReal,
      Nonempty (ShadedTube.ShadedUniformTubeSet (Finset.univ : Finset (Fin (385 ^ 6 + 1))) ST
        (Tube.ssfGridLen δ) C) :=
    ⟨((Finset.univ : Finset (Fin (385 ^ 6 + 1))).card : NNReal) + 1,
      nonempty_shadedUniformTubeSet_of_core_injOn hδ0 hδ1 _ ST _
        le_add_self le_self_add hcoreinj⟩
  -- (3) the density binder
  have hmaxST : maxDensity (Finset.univ : Finset (Fin (385 ^ 6 + 1)))
      (fun i ↦ (ST i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η) := by
    refine le_trans (Kakeya.maxDensity_le_card _ _) ?_
    have hcard : (((Finset.univ : Finset (Fin (385 ^ 6 + 1))).card : ℕ) : ENNReal)
        = (((MN : NNReal)) : ENNReal) := by
      simp [hMN]
    rw [hcard, ENNReal.rpow_neg]
    calc (((MN : NNReal)) : ENNReal) = ((((MN : NNReal)) : ENNReal)⁻¹)⁻¹ := by
          rw [inv_inv]
      _ ≤ ((δ : ENNReal) ^ η)⁻¹ := ENNReal.inv_le_inv' hδη
  -- (4) the fullness binder
  have hfullST : ShadedBody.fullness (Finset.univ : Finset (Fin (385 ^ 6 + 1)))
      (fun i ↦ (ST i).toShadedBody) ≥ δ ^ η := by
    have hpos : ∀ i : Fin (385 ^ 6 + 1), 0 < volume (Wt i).carrier :=
      fun i => (Tube.volume_pos_and_lt_top hδ0 hδ1 (Wt i)).1
    have hfin : ∀ i : Fin (385 ^ 6 + 1), volume (Wt i).carrier < ⊤ :=
      fun i => (Tube.volume_pos_and_lt_top hδ0 hδ1 (Wt i)).2
    have hXne : (∑ i : Fin (385 ^ 6 + 1), volume (Wt i).carrier) ≠ 0 := by
      refine ne_of_gt (lt_of_lt_of_le (hpos 0) ?_)
      exact Finset.single_le_sum (f := fun i => volume (Wt i).carrier)
        (fun i _ => by positivity) (Finset.mem_univ 0)
    have hXtop : (∑ i : Fin (385 ^ 6 + 1), volume (Wt i).carrier) ≠ ⊤ :=
      (ENNReal.sum_lt_top.mpr (fun i _ => hfin i)).ne
    have hone : ShadedBody.fullness' (Finset.univ : Finset (Fin (385 ^ 6 + 1)))
        (fun i ↦ (ST i).toShadedBody) = 1 := ENNReal.div_self hXne hXtop
    have hfl : ShadedBody.fullness (Finset.univ : Finset (Fin (385 ^ 6 + 1)))
        (fun i ↦ (ST i).toShadedBody) = 1 := by
      simp only [ShadedBody.fullness, hone]
      rfl
    rw [ge_iff_le, hfl]
    exact NNReal.rpow_le_one hδ1 hη.le
  -- (5) the `ρ`-count binder, vacuously
  have hcountST : ∀ ρ : NNReal, ρ ∈ Set.Icc (δ ^ (1 - exscal)) (δ ^ exscal) →
      ∀ {κ : Type} (tρ : Finset κ) (Tρ : κ → Tube ρ E3),
        (∀ i ∈ (Finset.univ : Finset (Fin (385 ^ 6 + 1))), ∃ j ∈ tρ,
          (ST i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) →
        (tρ : Set κ).Pairwise
          (fun j k ↦ IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) →
        (ρ : ℝ) ^ (-2 - ζ) ≤ (tρ.card : ℝ) := by
    intro ρ hρmem κ tρ Tρ hcov hED
    have hρ0 : 0 < ρ := lt_of_lt_of_le (NNReal.rpow_pos hδ0) hρmem.1
    have hρmax : ρ ≤ δ ^ exscal := hρmem.2
    have hρ1 : ρ ≤ 1 := le_trans hρmax (NNReal.rpow_le_one hδ1 hexscal.le)
    exact absurd (not_edCover_of_axialFamily_of_le (s := Finset.univ) (T := Wt) (θ := θ)
      (T₀ := T₀)
      (fun i _ => hTx i) (fun i _ => hTy i) (fun i _ => hθ i)
      (fun i _ i' _ hne => hsepθ i i' hne) (by simp) hρ0 hρmax hρ1 tρ Tρ
      (fun i _ => by
        obtain ⟨j, hj, hle⟩ := hcov i (Finset.mem_univ i)
        exact ⟨j, hj, hle⟩) hED) not_false
  -- the configuration, and the contradiction
  obtain ⟨cfg, bd, e, c, hexp, href, hc, -⟩ :=
    hsetupδ Finset.univ ST hballST huniST hmaxST hfullST hcountST
  have hcardcfg : cfg.s.card ≤ MN := by
    have hle : (cfg.s.map e.toEmbedding).card ≤ Fintype.card (Fin (385 ^ 6 + 1)) :=
      Finset.card_le_univ _
    rwa [Finset.card_map, Fintype.card_fin, ← hMN] at hle
  have htc := cfg.tube_count
  rw [hexp.2.2.1] at htc
  have hstep : (δ : ENNReal) * (cfg.s.card : ENNReal) ≤ (δ : ENNReal) * (MN : ENNReal) := by
    have hc : ((cfg.s.card : ℕ) : ENNReal) ≤ ((MN : ℕ) : ENNReal) := by exact_mod_cast hcardcfg
    exact mul_le_mul_of_nonneg_left hc (by positivity)
  have hlt1 : (δ : ENNReal) * (MN : ENNReal) < 1 := by
    have hn : (δ * (MN : NNReal) : NNReal) < 1 := by
      rw [← NNReal.coe_lt_coe]
      push_cast
      exact hδM
    calc (δ : ENNReal) * (MN : ENNReal) = ((δ * (MN : NNReal) : NNReal) : ENNReal) := by
          push_cast
          ring
      _ < 1 := by exact_mod_cast hn
  exact absurd (le_trans htc hstep) (not_le.mpr hlt1)

open MeasureTheory Topology Filter ShadedBody in
/-- **The conclusion of `Kakeya.multiplicity_le_of_card_isEssDistinct_ge` — GWZ Lemma 9.1, the
target of this section — is false as rendered before the centredness binder.** ( R4: `h91` below is the
pre-centred text, transcribed by hand; the live statement carries `∀ i ∈ s, (T i).toTube.IsCentred`, which the axial
witness family does not meet, and is not refuted here. See the module docstring's scope note.)

The hypothesis `h91` is that theorem's conclusion, transcribed at universe `0`; `hKT` and `hF` are
its own two antecedents, so the refutation is *conditional on the section's standing conjectures*
and says exactly this: **Lemma 9.1 as currently stated is inconsistent with the Katz–Tao and
Frostman estimates.**

The witness is `Kakeya.VeryNotSticky.exists_witnessFamily`: `385^6 + 1` `δ`-tubes on a common
axis, shaded by their own carriers.  Every binder holds — the `ρ`-count one vacuously, since the
family admits no essentially distinct cover at any scale of the window
(`Kakeya.VeryNotSticky.not_edCover_of_axialFamily`).  Its multiplicity is at least `#𝕋 / 2`,
because the whole family lies inside the union of two of its members.  The conclusion asserts
`multiplicity ≤ δ^ν · (#𝕋)^β`, which at fixed `#𝕋` tends to `0` with `δ`.

**The defect is the same one as in `Kakeya.VeryNotSticky.exists_setup_caseSideData`** and it is a
missing binder, not a missing proof: nothing in the statement asks `𝕋` to be large.  GWZ's
very-not-sticky case has `|𝕋| ⪆ δ^{-2}` from the ambient setup; the Lean rendering leaves that to
the `ρ`-count hypothesis, and `Kakeya.VeryNotSticky.not_edCover_of_axialFamily` shows the
`ρ`-count hypothesis cannot supply it.  Which statement-level repair to prefer is not settled by
this theorem. -/
theorem not_lemma91Conclusion {β : ℝ} (hβ1 : β ≤ 1)
    (hKT : KatzTaoEstimate.{0} (EuclideanSpace ℝ (Fin 3)) β)
    (hF : FrostmanEstimate.{0} (EuclideanSpace ℝ (Fin 3)) β)
    (h91 : ∃ ϖ > (0 : ℝ), ∀ ζ > (0 : ℝ), ∃ ν > (0 : ℝ), ∃ η > (0 : ℝ),
      KatzTaoEstimate.{0} (EuclideanSpace ℝ (Fin 3)) β →
      FrostmanEstimate.{0} (EuclideanSpace ℝ (Fin 3)) β →
      ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      ∀ {ι : Type} (s : Finset ι) (T : ι → ShadedTube δ E3),
        (∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall 0 1) →
        (∃ C : NNReal,
          Nonempty (ShadedTube.ShadedUniformTubeSet s T (Tube.ssfGridLen δ) C)) →
        maxDensity s (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η) →
        ShadedBody.fullness s (fun i ↦ (T i).toShadedBody) ≥ δ ^ η →
        (∀ ρ : NNReal, ρ ∈ Set.Icc (δ ^ (1 - ϖ)) (δ ^ ϖ) →
          ∀ {κ : Type} (tρ : Finset κ) (Tρ : κ → Tube ρ E3),
            (∀ i ∈ s, ∃ j ∈ tρ, (T i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) →
            (tρ : Set κ).Pairwise
              (fun j k ↦ IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) →
            (ρ : ℝ) ^ (-2 - ζ) ≤ (tρ.card : ℝ)) →
        ShadedBody.multiplicity s (fun i ↦ (T i).toShadedBody) ≤
          (δ : ENNReal) ^ ν * (s.card : ENNReal) ^ β) :
    False := by
  classical
  obtain ⟨ϖ, hϖ, h⟩ := h91
  obtain ⟨ν, hν, η, hη, hrest⟩ := h 1 (by norm_num)
  have hev := hrest hKT hF
  obtain ⟨G, hGpos, hG⟩ : ∃ G : ℝ, 0 < G ∧ G = 1 / (6 * 288 * (((385 ^ 6 : ℕ) : ℝ) + 1)) :=
    ⟨_, by positivity, rfl⟩
  obtain ⟨cgap, hcgap⟩ : ∃ c : NNReal, (c : ℝ) = G / 2 := ⟨⟨G / 2, by positivity⟩, rfl⟩
  have hcgappos : 0 < cgap := by rw [← NNReal.coe_pos, hcgap]; positivity
  have h1 : ∀ᶠ (δ : NNReal) in 𝓝[>] 0, (δ : ℝ) ≤ 1 / 4 := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : NNReal) < 1 / 4 by norm_num)] with δ hδ
    exact_mod_cast hδ.2.le
  have h3 : (0 : ENNReal) < (((385 ^ 6 + 1 : ℕ) : ℕ) : ENNReal)⁻¹ := by
    rw [ENNReal.inv_pos]
    exact ENNReal.natCast_ne_top _
  have hthr : ∀ᶠ (δ : NNReal) in 𝓝[>] 0,
      δ ∈ Set.Ioi (0 : NNReal) ∧ (δ : ℝ) ≤ 1 / 4 ∧ δ ^ ϖ ≤ cgap ∧
        (δ : ENNReal) ^ η ≤ (((385 ^ 6 + 1 : ℕ) : ℕ) : ENNReal)⁻¹ ∧
        (δ : ENNReal) ^ ν ≤ 1 / 4 := by
    filter_upwards [self_mem_nhdsWithin, h1, eventually_rpow_le hcgappos hϖ,
      ENNReal.eventually_coe_rpow_le_of_pos hη h3,
      ENNReal.eventually_coe_rpow_le_of_pos hν (show (0 : ENNReal) < 1 / 4 by norm_num)]
      with δ ha hb hc hd he
    exact ⟨ha, hb, hc, hd, he⟩
  obtain ⟨δ, hevδ, hδ0', hδ4, hδϖ, hδη, hδν⟩ := (hev.and hthr).exists
  have hδ0 : (0 : NNReal) < δ := hδ0'
  have hGlt : ((δ ^ ϖ : NNReal) : ℝ) < G := by
    have hle : ((δ ^ ϖ : NNReal) : ℝ) ≤ (cgap : ℝ) := by exact_mod_cast hδϖ
    rw [hcgap] at hle
    linarith
  have hden : (((385 ^ 6 + 1 : ℕ) : ℕ) : ENNReal) ≤ (δ : ENNReal) ^ (-η) := by
    rw [ENNReal.rpow_neg]
    calc (((385 ^ 6 + 1 : ℕ) : ℕ) : ENNReal)
        = ((((385 ^ 6 + 1 : ℕ) : ℕ) : ENNReal)⁻¹)⁻¹ := by rw [inv_inv]
      _ ≤ ((δ : ENNReal) ^ η)⁻¹ := ENNReal.inv_le_inv' hδη
  obtain ⟨T, hball, huni, hmax, hfull, hcount, hmult⟩ :=
    exists_witnessFamily hδ0 hδ4 hϖ hη (by rw [← hG]; exact hGlt) hden
  have hle := hevδ (Finset.univ : Finset (Fin (385 ^ 6 + 1))) T hball huni hmax hfull
    (fun ρ hρ => hcount 1 ρ hρ)
  set M : ENNReal := ((385 ^ 6 + 1 : ℕ) : ENNReal) with hM
  have hMne : M ≠ 0 := by rw [hM]; simp
  have hMtop : M ≠ ⊤ := by rw [hM]; exact ENNReal.natCast_ne_top _
  have hM1 : (1 : ENNReal) ≤ M := by rw [hM]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by simp)
  have hcardM : (((Finset.univ : Finset (Fin (385 ^ 6 + 1))).card : ℕ) : ENNReal) = M := by
    rw [hM]; simp
  have hpow : ((((Finset.univ : Finset (Fin (385 ^ 6 + 1))).card : ℕ) : ENNReal)) ^ β ≤ M := by
    rw [hcardM]
    calc M ^ β ≤ M ^ (1 : ℝ) := ENNReal.rpow_le_rpow_of_exponent_le hM1 hβ1
      _ = M := ENNReal.rpow_one M
  have hchain : M / 2 ≤ (1 / 4 : ENNReal) * M := by
    calc M / 2 ≤ (δ : ENNReal) ^ ν
          * ((((Finset.univ : Finset (Fin (385 ^ 6 + 1))).card : ℕ) : ENNReal)) ^ β :=
        le_trans hmult hle
      _ ≤ (1 / 4 : ENNReal) * M := by
        exact mul_le_mul' hδν hpow
  have hbad : (2 : ENNReal)⁻¹ * M ≤ (4 : ENNReal)⁻¹ * M := by
    calc (2 : ENNReal)⁻¹ * M = M / 2 := by rw [ENNReal.div_eq_inv_mul]
      _ ≤ (1 / 4 : ENNReal) * M := hchain
      _ = (4 : ENNReal)⁻¹ * M := by rw [one_div]
  rw [ENNReal.mul_le_mul_iff_left hMne hMtop] at hbad
  have h24 : ((4 : ENNReal))⁻¹ < ((2 : ENNReal))⁻¹ := by
    rw [ENNReal.inv_lt_inv]
    norm_num
  exact absurd hbad (not_le.mpr h24)


end Kakeya.VeryNotSticky
