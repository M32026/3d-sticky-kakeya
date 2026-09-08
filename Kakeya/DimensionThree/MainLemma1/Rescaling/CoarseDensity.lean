/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma1.Rescaling.Assembly
public import Kakeya.Thickness.Diam
import Mathlib.Analysis.Normed.Module.Normalize

/-!
# Main Lemma 1, Case (ii): The maximal density of the `b`-tubes

Split out of `Kakeya/DimensionThree/MainLemma1/Rescaling.lean`.
-/

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody Filter Topology

namespace Kakeya

namespace ml1Boot

/-! ### The maximal density of the `b`-tubes -/

/-- **The constant `C_{lem:ml1bootDilateTestBody}(3)`** (blueprint
`def:ml1bootDilateTestBodyConstant`):

`C(n) = 3 ^ n · C_{lem:outerPrismVolumeComparison}(n)`, so in particular
`C(3) = 3 ^ 3 · Metric.volume_outerPrism_le_volume_self.C 3 ≥ 1`,

the factor by which a convex test body has to be enlarged before it absorbs the `2`-dilates of
all the tubes it contains (`Kakeya.ml1Boot.exists_dilate_testBody`).

The two factors are the two steps of that lemma, whose witness is
`K* = 3 · outerPrism K` (`Kakeya.ml1Boot.dilateTestBody`).  The factor
`Metric.volume_outerPrism_le_volume_self.C 3` pays for replacing `K` by the outer prism
`P = outerPrism K` around it, and the factor `3 ^ 3` is the volume of a homothety of ratio `3`
in `ℝ³`, which pays for the enlargement of `P` to `3 · P` that absorbs the dilates.  Both
factors are `≥ 1`, hence so is the product.  It depends only on the ambient dimension; in
particular not on `δ̃`, `ap`, `bp`, `ρ`, `γ`, `j`, the family, or the test body.

It is emphatically *not* `Kakeya.Tube.tubeDilateVolume.C' 3 2 = 2³`: that constant compares
`|2 · T|` with `|T|` for a single tube, whereas the quantity bounded here is `|K*| / |K|` for
a test body `K`, and a tube is in general far from centrally placed inside a `K` containing
it.

The earlier value was `2 ^ 3 * (6 choose 3)`, whose second factor was the Rogers–Shephard
constant of the now retired blueprint `prop:ml1bootDifferenceBodyVolume` and whose first was
the volume of a ratio-`2` homothety.  Nothing downstream uses the numerical value: it enters
`Kakeya.ml1Boot.coarsePlank.C` symbolically and is carried symbolically from there. -/
noncomputable abbrev dilateTestBody.C : NNReal :=
  3 ^ 3 * Metric.volume_outerPrism_le_volume_self.C 3

/-- **The constant `C_{lem:ml1bootCoarsePlankDensity}`** (blueprint
`def:ml1bootCoarsePlankConstant`):
`C_{lem:ml1bootDilateTestBody} · 2 · C_{lem:ml1bootPlankInTubeRepaired} · C_{lem:ml1bootCardBound}`.

The middle factor compares a `b`-tube with the plank it contains, the first pays for the
passage to a test body absorbing the `2`-dilates, and the last counts the essentially
distinct `ρ`-tubes of `𝕋̃_ρ` in `B₁ ⊆ ℝ³`.  It depends only on the ambient dimension `3`,
and on nothing else.

The plank-to-tube factor is `Kakeya.ml1Boot.plankInTube.C`; see the docstring of
`Kakeya.ml1Boot.volume_plankTube_le` for why the earlier candidate
`Kakeya.ml1Boot.densityTransfer.C * Kakeya.ml1Boot.plankPigeonhole.C`, computed with the
retired value of `densityTransfer.C`, was too small by a factor
`1280 · Metric.volume_comparison.C 3`. -/
noncomputable abbrev coarsePlank.C : NNReal :=
  dilateTestBody.C * 2 * plankInTube.C * cardBound.C

/-- **The constant `C_{lem:ml1bootPlankTubeParents}(n)`** (blueprint
`def:ml1bootPlankTubeParentsConstant`):

`C(n) = 6 · C_{lem:tubeOverlapCoreClose}(n) ²`, with
`C_{lem:tubeOverlapCoreClose}(n) = 9 + 2 · 4 ^ n / c_{le_volume}(n)`
(`Kakeya.Tube.tubeOverlapCoreClose.C`), so that in `ℝ³`
`C(3) = 6 · (9 + 128 / c_{le_volume}(3)) ²`.

This is the dilation ratio of the parent family that
`Kakeya.ml1Boot.exists_plankTube_parentFamily_essDistinct` produces: it replaces the ratio `2`
that the plank-to-tube step alone would give, and the enlargement pays for making the `b`-tubes
pairwise essentially distinct *without* discarding any fine tube.  It depends only on the
ambient dimension `n`; in particular not on `δ̃`, `ap`, `bp`, `ρ`, the family, or the index
sets.

**The enlargement is not needed, because the distinctness it pays for is not needed, and this
constant now has no live consumer.**  The `b`-tubes' pairwise essential distinctness was asked
for only by `Kakeya.ml1Boot.multiplicity_coarse_le`, and that hypothesis was inert: it was used
only to build the corresponding hypothesis of `Kakeya.ml1Boot.bracket_mem_Icc`, which never
referenced it, and neither did `Kakeya.ml1Boot.multiplicity_coarse_raw`, while
`Kakeya.KatzTaoEstimate.multiplicity_bound` has no such hypothesis at all.  What excludes
degenerate repetition at the bottom of that chain is the fullness hypothesis.  All three
hypotheses have been deleted, and `Kakeya.ml1Boot.exists_plankTube_parentFamily` now delivers
the parent family at the plank's own ratio `2`, obtaining the `injOn` field of
`Kakeya.ml1Boot.IsParentFamilyDilate` from `Kakeya.ml1Boot.exists_dedupe_dilate` instead — which
identifies only blocks whose `b`-tubes have *equal bodies*, and so costs nothing in the ratio.

This constant is therefore reached only through
`Kakeya.ml1Boot.exists_plankTube_parentFamily_essDistinct`, which is itself retained but
uncalled, against a future consumer that does need distinctness.  It is kept rather than
deleted for the same reason.  See blueprint `note:ml1bootCoarseEDInert`.

Three constraints fix it, all read at `C_ov = Kakeya.Tube.tubeOverlapCoreClose.C n`:

* the plank clause `T_k ⊆ 2 · T_{b,l}` must survive at the new ratio, so `2 ≤ C(n)`;
* `Kakeya.Tube.subset_dilate_rescale_of_subset_dilate`, which transports a containment from a
  discarded `b`-tube to a retained one, asks `2 · C_ov ≤ C(n)`;
* and, at equal scales `δ = ρ = C_𝕎 bp`, its numeric hypothesis
  `6 · C_ov ² · δ ≤ C(n) · ρ` asks `6 · C_ov ² ≤ C(n)`.

The third is the binding one, `C_ov > 9` making it dominate the other two, so `C(n) = 6 C_ov ²`
is exactly the least value the route allows.  The figure `3` (hence `6 = 2 · 3`) that blueprint
`note:auditPlankTubeParents`(b) guessed for the discarded-to-retained containment is *not*
what the available geometry gives: `Kakeya.Tube.tubeOverlapCoreClose` produces `C_ov`, whose
value is dictated by the near-parallelism bound `2 · 4 ^ n / c_n` of
`Kakeya.Tube.overlapTransversal` together with the axial overhang. -/
noncomputable abbrev plankTubeParents.C (n : ℕ) : ℝ :=
  6 * Tube.tubeOverlapCoreClose.C n ^ 2

/-- **`Kakeya.ml1Boot.plankTubeParents.C` as an `NNReal`.**

The dilation ratio of the `b`-tube parent family is `ℝ`-valued because
`Kakeya.Tube.tubeOverlapCoreClose.C` is, but every consumer that carries it as a *scale* — the
`c` of `Kakeya.ml1Boot.IsParentFamilyDilate` and of
`Kakeya.ml1Boot.normalized_le_of_coarse_dilate` — needs an `NNReal`.  This is that `NNReal`,
together with the two facts a caller reads off it: its coercion is the `ℝ`-valued constant
(`Kakeya.ml1Boot.plankTubeParents.coe_CNN`) and it is at least `1`
(`Kakeya.ml1Boot.plankTubeParents.one_le_CNN`).

Recorded in the ledger of `Kakeya.ml1Boot.multTildeT_of_planksClose` as "naming an `NNReal` whose
coercion is the `ℝ`-valued `Kakeya.ml1Boot.plankTubeParents.C 3`"; this discharges it.  Positivity
comes from `Kakeya.Tube.tubeOverlapCoreClose.one_lt_C`, so no numeral is evaluated. -/
noncomputable def plankTubeParents.CNN (n : ℕ) : NNReal :=
  Real.toNNReal (plankTubeParents.C n)

/-- The `ℝ`-valued dilation ratio is at least `1`, from
`Kakeya.Tube.tubeOverlapCoreClose.one_lt_C`; no numeral is evaluated. -/
theorem plankTubeParents.one_le_C (n : ℕ) : (1 : ℝ) ≤ plankTubeParents.C n := by
  have h := Tube.tubeOverlapCoreClose.one_lt_C n
  have h0 : (0 : ℝ) ≤ Tube.tubeOverlapCoreClose.C n :=
    le_of_lt (lt_trans zero_lt_one h)
  simp only [plankTubeParents.C]
  nlinarith

@[simp]
theorem plankTubeParents.coe_CNN (n : ℕ) :
    ((plankTubeParents.CNN n : NNReal) : ℝ) = plankTubeParents.C n :=
  Real.coe_toNNReal _ (le_trans zero_le_one (plankTubeParents.one_le_C n))

theorem plankTubeParents.one_le_CNN (n : ℕ) : 1 ≤ plankTubeParents.CNN n := by
  rw [← NNReal.coe_le_coe, plankTubeParents.coe_CNN, NNReal.coe_one]
  exact plankTubeParents.one_le_C n

section CoarseDensity

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **The blocks of the plank factorizations are the fibres of a single map** (blueprint
`lem:ml1bootPlankBlockPartition`).

With the output of `Kakeya.ml1Boot.exists_plankDimensions` in force — a refined index set
`u''` and, for every parent index `m`, a `2`-factorization `F m` of `fibre u'' pρ m` into
nonempty parts — put

`𝓘 = {(m, t) : m ∈ t_ρ, t ∈ (F m).parts}`.

Then the map `q` sending `k ∈ u''` to `(pρ k, t)`, with `t` the unique part of `F (pρ k)`
containing `k`, is well defined, lands in `𝓘`, is surjective onto `𝓘`, and has exactly the
blocks as fibres: `{k ∈ u'' : q k = (m, t)} = t`.

This is the bookkeeping that lets the two-index family `(W_{m,t})` of planks be treated as a
single indexed family, which is what `Kakeya.ml1Boot.exists_plankTube_family` and the density
sums of `Kakeya.ml1Boot.maxDensity_coarse_le` need.  Surjectivity is where nonemptiness of
the parts is used.

The parent enters in exactly one place — the `mapsTo` clause, used to put `pρ k` in `tρ` — and
neither the parent tubes nor the containment clause is inspected at all.  The hypothesis is
therefore taken as the bare `hmapsTo` rather than as a parent-family structure, so that the
statement serves `Kakeya.ml1Boot.IsParentFamily` and
`Kakeya.ml1Boot.IsParentFamilyDilate c` alike: each caller passes its own `.mapsTo` field, and
no conversion between the two structures is needed.  This is what lets the block partition run
after the `ρ`-parents have been merged by `Kakeya.ml1Boot.exists_merged_rhoParentFamily`, where
only the dilate form is available.  The parent family `Tρ` is consequently absent from the
signature; callers holding one simply do not pass it. -/
theorem plankBlocks_partition {δt : NNReal}
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {u u'' : Finset ι} {tρ : Finset κ}
    (T : ι → Tube δt E) (pρ : ι → κ)
    (hu'' : u'' ⊆ u) (hmapsTo : ∀ i ∈ u, pρ i ∈ tρ)
    (F : (m : κ) → ConvexSpaceBody.Factorization (fibre u'' pρ m)
      (fun i => (T i).toConvexSpaceBody) 2)
    (hparts : ∀ m ∈ tρ, ∀ part ∈ (F m).parts, part.Nonempty) :
    ∃ q : ι → κ × Finset ι,
      (∀ k ∈ u'', (q k).1 = pρ k ∧ (q k).2 ∈ (F (pρ k)).parts ∧ k ∈ (q k).2) ∧
      (∀ k ∈ u'', q k ∈ tρ.biUnion fun m => (F m).parts.image fun part => (m, part)) ∧
      Set.SurjOn q ↑u'' ↑(tρ.biUnion fun m => (F m).parts.image fun part => (m, part)) ∧
      ∀ m ∈ tρ, ∀ part ∈ (F m).parts, u''.filter (fun k => q k = (m, part)) = part := by
  let q : ι → κ × Finset ι := fun k => (pρ k, (F (pρ k)).part k)
  refine ⟨q, ?_, ?_, ?_, ?_⟩
  · intro k hk
    have hkfib : k ∈ fibre u'' pρ (pρ k) := by
      unfold fibre
      exact Finset.mem_filter.mpr ⟨hk, rfl⟩
    refine ⟨rfl, ?_, ?_⟩
    · exact (F (pρ k)).part_mem.2 hkfib
    · exact (F (pρ k)).mem_part hkfib
  · intro k hk
    change (pρ k, (F (pρ k)).part k) ∈
      tρ.biUnion fun m => (F m).parts.image fun part => (m, part)
    exact Finset.mem_biUnion.mpr
      ⟨pρ k, hmapsTo k (hu'' hk),
        Finset.mem_image.mpr ⟨(F (pρ k)).part k, (F (pρ k)).part_mem.2
          (by unfold fibre; exact Finset.mem_filter.mpr ⟨hk, rfl⟩), rfl⟩⟩
  · intro y hy
    have hy' : y ∈ tρ.biUnion (fun m => (F m).parts.image fun part => (m, part)) :=
      Finset.mem_coe.mp hy
    obtain ⟨m, hm, hym⟩ := Finset.mem_biUnion.mp hy'
    obtain ⟨part, hpartmem, hyeq⟩ := Finset.mem_image.mp hym
    obtain ⟨k, hkp⟩ := hparts m hm part hpartmem
    have hkfib : k ∈ fibre u'' pρ m := (F m).subset hpartmem hkp
    have hku : k ∈ u'' := (Finset.mem_filter.mp hkfib).1
    have hpm : pρ k = m := (Finset.mem_filter.mp hkfib).2
    have hpart_eq : (F (pρ k)).part k = part := by
      calc (F (pρ k)).part k = (F m).part k := by rw [hpm]
        _ = part := (F m).part_eq_of_mem hpartmem hkp
    have hq : q k = (m, part) := by
      change (pρ k, (F (pρ k)).part k) = (m, part)
      apply Prod.ext
      · exact hpm
      · exact hpart_eq
    refine ⟨k, hku, ?_⟩
    rw [hq, hyeq]
  · intro m hm part hpart
    apply Finset.ext
    intro k
    constructor
    · intro hkfilter
      have hku : k ∈ u'' := (Finset.mem_filter.mp hkfilter).1
      have hqeq : q k = (m, part) := (Finset.mem_filter.mp hkfilter).2
      have hkfib : k ∈ fibre u'' pρ (pρ k) := by
        unfold fibre
        exact Finset.mem_filter.mpr ⟨hku, rfl⟩
      have hkmem : k ∈ (F (pρ k)).part k := (F (pρ k)).mem_part hkfib
      have hpp : (F (pρ k)).part k = part := congrArg Prod.snd hqeq
      rw [hpp] at hkmem
      exact hkmem
    · intro hkp
      have hkfib : k ∈ fibre u'' pρ m := (F m).subset hpart hkp
      have hku : k ∈ u'' := (Finset.mem_filter.mp hkfib).1
      have hpm : pρ k = m := (Finset.mem_filter.mp hkfib).2
      have hpart_eq : (F (pρ k)).part k = part := by
        calc (F (pρ k)).part k = (F m).part k := by rw [hpm]
          _ = part := (F m).part_eq_of_mem hpart hkp
      have hqeq : q k = (m, part) := by
        change (pρ k, (F (pρ k)).part k) = (m, part)
        apply Prod.ext
        · exact hpm
        · exact hpart_eq
      exact Finset.mem_filter.mpr ⟨hku, hqeq⟩

/-- **Deduplication that survives dilation** (the Lean bridge inside blueprint
`lem:ml1bootPlankTubeChoice`).

`Kakeya.ml1Boot.exists_dedupe` returns equality of the underlying convex *bodies*, which is all
it can return: a tube and `Kakeya.Tube.reverse` of it are distinct tubes with the same body, so a
family made injective on bodies must identify them.  Combined with `Kakeya.Tube.dilate_congr`
(blueprint `cor:ml1bootDilateFromCarrier`) that equality upgrades to equality of every dilate,
which is the form the containment clauses of `Kakeya.ml1Boot.IsParentFamilyDilate` are stated
in. -/
theorem exists_dedupe_dilate [Nontrivial E] {σ : NNReal} {ι' : Type*}
    (s : Finset ι') (V : ι' → Tube σ E) :
    ∃ t ⊆ s, ∃ r : ι' → ι',
      Set.InjOn (fun j => (V j).toConvexSpaceBody) ↑t ∧
      (∀ j ∈ s, r j ∈ t) ∧
      Set.SurjOn r ↑s ↑t ∧
      ∀ j ∈ s, ∀ c : ℝ, Tube.dilate (V (r j)) c = Tube.dilate (V j) c := by
  classical
  obtain ⟨t, hts, q, hqt, hbody, hinj, hsurj⟩ := exists_dedupe s V
  exact ⟨t, hts, q, hinj, hqt, hsurj,
    fun j hj c => Tube.dilate_congr (V (q j)) (V j) (hbody j hj) c⟩

/-- **A dilate of a tube lies in a ball about the tube's centre.**

`Kakeya.Tube.dilate_carrier_eq_cthickening` writes `c · T` as the closed `c σ`-neighbourhood of
the segment of length `c` through `T.center` in the direction of `T`.  Every point of that
segment is within `c / 2` of `T.center`, because `‖T.direction‖ = 1`, so every point of `c · T`
is within `c / 2 + c σ` of `T.center`. -/
theorem dilate_carrier_subset_closedBall_center [Nontrivial E] {σ : NNReal} (T : Tube σ E)
    {c : ℝ} (hc : 0 < c) :
    (Tube.dilate T c).carrier ⊆ Metric.closedBall T.center (c / 2 + c * (σ : ℝ)) := by
  have hs0 : (0 : ℝ) ≤ (σ : ℝ) := σ.coe_nonneg
  have hcs0 : (0 : ℝ) ≤ c * (σ : ℝ) := mul_nonneg hc.le hs0
  have hc20 : (0 : ℝ) ≤ c / 2 := by linarith
  have hc0 : (0 : ℝ) ≤ c := by linarith
  have hseg : segment ℝ (T.center - (c / 2) • T.direction)
      (T.center + (c / 2) • T.direction) ⊆ Metric.closedBall T.center (c / 2) := by
    refine (convex_closedBall (T.center) (c / 2)).segment_subset ?_ ?_ <;>
      · rw [Metric.mem_closedBall, dist_eq_norm]
        simp [norm_smul, T.norm_direction, abs_of_nonneg hc0]
  calc (Tube.dilate T c).carrier
      = Metric.cthickening (c * (σ : ℝ))
          (segment ℝ (T.center - (c / 2) • T.direction)
            (T.center + (c / 2) • T.direction)) :=
        _root_.Tube.dilate_carrier_eq_cthickening T hc
    _ ⊆ Metric.cthickening (c * (σ : ℝ)) (Metric.closedBall T.center (c / 2)) :=
        Metric.cthickening_subset_of_subset _ hseg
    _ = Metric.closedBall T.center (c * (σ : ℝ) + c / 2) :=
        cthickening_closedBall hcs0 hc20 _
    _ = Metric.closedBall T.center (c / 2 + c * (σ : ℝ)) := by rw [add_comm]

/-- **A tube whose `c`-dilate contains a body inside the unit ball is itself located.**

This is the *location clause for the `b`-scale tubes*, derived from data that
`Kakeya.ml1Boot.exists_plank_tube_of_thickness_le_one` actually exports.

That producer hands back an existential tube `T` about which only `W ≤ c · T` and two volume
comparisons are known; the witness it uses internally is `Kakeya.ml1Boot.plankTube`, but that
is not visible through the existential, so the sharper direct bound
`Kakeya.ml1Boot.plankTube_carrier_subset_closedBall_of_le` (radius `9 / 2`) cannot be applied
at the call site.  What is available is enough: `c · T` contains a point `x` of `W`, hence a
point of the unit ball, and `c · T` lies in the ball of radius `c / 2 + c σ` about `T.center`
(`Kakeya.ml1Boot.dilate_carrier_subset_closedBall_center`), so

`‖T.center‖ ≤ ‖x‖ + dist x T.center ≤ 1 + c / 2 + c σ`,

and `T` itself lies within `1 / 2 + σ` of its centre
(`Kakeya.Tube.carrier_subset_closedBall_midpoint`).  Adding the two gives the radius below.

At `c = 2` the radius is `5 / 2 + 3 σ`, and under the side condition `σ ≤ 1` that the Section 8
route carries as `hbq1 : plankPigeonhole.C * bp ≤ 1` it is at most `11 / 2`.  This is coarser
than the `9 / 2` obtainable from the explicit construction, by the factor the existential
costs; no consumer distinguishes the two, since the containments hypothesised downstream are at
radius `1`. -/
theorem carrier_subset_closedBall_of_le_dilate [Nontrivial E] {σ : NNReal} (T : Tube σ E)
    {c : ℝ} (hc : 0 < c) {W : ConvexSpaceBody E} (hWdil : W ≤ Tube.dilate T c)
    (hWball : W.carrier ⊆ Metric.closedBall (0 : E) 1) :
    T.carrier ⊆ Metric.closedBall (0 : E) (3 / 2 + (σ : ℝ) + c * (1 / 2 + (σ : ℝ))) := by
  obtain ⟨x, hx⟩ := W.nonempty'
  have hWc : W.carrier ⊆ (Tube.dilate T c).carrier := SetLike.coe_subset_coe.mpr hWdil
  have hxd : dist x T.center ≤ c / 2 + c * (σ : ℝ) :=
    Metric.mem_closedBall.mp (dilate_carrier_subset_closedBall_center T hc (hWc hx))
  have hx1 : dist x (0 : E) ≤ 1 := Metric.mem_closedBall.mp (hWball hx)
  have hcentre : dist T.center (0 : E) ≤ 1 + (c / 2 + c * (σ : ℝ)) := by
    have htri : dist T.center (0 : E) ≤ dist T.center x + dist x (0 : E) := dist_triangle _ _ _
    rw [dist_comm T.center x] at htri
    linarith
  refine (Tube.carrier_subset_closedBall_midpoint (E := E) T).trans ?_
  refine Metric.closedBall_subset_closedBall' ?_
  nlinarith [hcentre, σ.coe_nonneg, hc.le]

/-- **A tube for every block** (the blockwise step of blueprint `lem:ml1bootPlankTubeChoice`).

`Kakeya.ml1Boot.exists_plank_tube_of_thickness_le_one` applied to each plank `W_{m,t}` of the
block index set, with no injectivity claimed: the map from blocks to tubes need not be injective,
and making it so is the separate job of `Kakeya.ml1Boot.exists_dedupe_dilate`.

No parent family appears in the signature, for the reason recorded on
`Kakeya.ml1Boot.plankBlocks_partition`: the argument never inspects the `ρ`-parents.  Each plank
is handled on its own, through `hball` and its plank dimensions `hdims`, and the parent scale `ρ`
enters neither a hypothesis nor the conclusion.  An `IsParentFamily` hypothesis was carried here
until it was observed to be entirely unused, and dropping it is what lets the *same* declaration
serve `Kakeya.ml1Boot.IsParentFamily` and `Kakeya.ml1Boot.IsParentFamilyDilate c` alike -- in
particular after the `ρ`-parents have been merged by
`Kakeya.ml1Boot.exists_merged_rhoParentFamily`, where only the dilate form is available.  A
separate dilate twin of this lemma would have differed from it in an unused hypothesis only. -/
theorem exists_plankTube_blockwise [Nontrivial E] (hdim : Module.finrank ℝ E = 3)
    {δt ap bp : NNReal} (hδt : 0 < δt) (hδa : δt ≤ ap) (hab : ap ≤ bp) (hb1 : bp ≤ 1)
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {u u'' : Finset ι} {tρ : Finset κ}
    (T : ι → Tube δt E) (pρ : ι → κ)
    (hu'' : u'' ⊆ u)
    (hball : ∀ i ∈ u, (T i).carrier ⊆ Metric.closedBall 0 1)
    (F : (m : κ) → ConvexSpaceBody.Factorization (fibre u'' pρ m)
      (fun i => (T i).toConvexSpaceBody) 2)
    (hparts : ∀ m ∈ tρ, ∀ part ∈ (F m).parts, part.Nonempty)
    (hdims : ∀ m ∈ tρ, IsPlankFamilyOfDimensions plankPigeonhole.C ap bp (F m).parts
      (fun part => part.convexHull_biUnion (fun i => (T i).toConvexSpaceBody))) :
    ∃ V : κ × Finset ι → Tube (plankPigeonhole.C * bp) E,
      ∀ j ∈ tρ.biUnion fun m => (F m).parts.image fun part => (m, part),
        (j.2.convexHull_biUnion fun i => (T i).toConvexSpaceBody) ≤ Tube.dilate (V j) 2 ∧
        (∀ k ∈ j.2, (T k).toConvexSpaceBody ≤ Tube.dilate (V j) 2) ∧
        (densityTransfer.C : ENNReal)⁻¹ * ((bp : ENNReal) / (ap : ENNReal))
            * volume (j.2.convexHull_biUnion fun i => (T i).toConvexSpaceBody).carrier
          ≤ volume (Tube.dilate (V j) 2).carrier ∧
        volume (Tube.dilate (V j) 2).carrier
          ≤ (densityTransfer.C : ENNReal) * ((bp : ENNReal) / (ap : ENNReal))
            * volume (j.2.convexHull_biUnion fun i => (T i).toConvexSpaceBody).carrier ∧
        (V j).carrier ⊆ Metric.closedBall (0 : E)
          (5 / 2 + 3 * ((plankPigeonhole.C * bp : NNReal) : ℝ)) := by
  classical
  have htube : Nonempty (Tube (plankPigeonhole.C * bp) E) := by
    obtain ⟨z, hz⟩ := exists_ne (0 : E)
    exact ⟨Tube.ofMidpointDirection (plankPigeonhole.C * bp) (0 : E)
      (NormedSpace.normalize z) (NormedSpace.norm_normalize_eq_one_iff.mpr hz)⟩
  have ha0 : 0 < ap := lt_of_lt_of_le hδt hδa
  have hforall :
      ∀ j : κ × Finset ι, ∃ V : Tube (plankPigeonhole.C * bp) E,
        j ∈ tρ.biUnion (fun m => (F m).parts.image fun part => (m, part)) →
          (j.2.convexHull_biUnion fun i => (T i).toConvexSpaceBody) ≤ Tube.dilate V 2 ∧
          (∀ k ∈ j.2, (T k).toConvexSpaceBody ≤ Tube.dilate V 2) ∧
          (densityTransfer.C : ENNReal)⁻¹ * ((bp : ENNReal) / (ap : ENNReal))
              * volume (j.2.convexHull_biUnion fun i => (T i).toConvexSpaceBody).carrier
            ≤ volume (Tube.dilate V 2).carrier ∧
          volume (Tube.dilate V 2).carrier
            ≤ (densityTransfer.C : ENNReal) * ((bp : ENNReal) / (ap : ENNReal))
              * volume (j.2.convexHull_biUnion fun i => (T i).toConvexSpaceBody).carrier ∧
          V.carrier ⊆ Metric.closedBall (0 : E)
            (5 / 2 + 3 * ((plankPigeonhole.C * bp : NNReal) : ℝ)) := by
    intro j
    by_cases hj : j ∈ tρ.biUnion (fun m => (F m).parts.image fun part => (m, part))
    · rcases Finset.mem_biUnion.mp hj with ⟨m, hm, hmemImage⟩
      rcases Finset.mem_image.mp hmemImage with ⟨part, hpart, hpair⟩
      subst j
      let W : ConvexSpaceBody E :=
        part.convexHull_biUnion (fun i => (T i).toConvexSpaceBody)
      have hpart0 : part.Nonempty := hparts m hm part hpart
      have hfibre' : part ⊆ fibre u'' pρ m := (F m).subset hpart
      have hWball : W.carrier ⊆ Metric.closedBall (0 : E) 1 := by
        dsimp [W]
        exact (Finset.Nonempty.convexHull_biUnion_subset_iff hpart0
          (fun i => (T i).toConvexSpaceBody) (convex_closedBall 0 1).isConvexSet).mpr
            (by
              intro i hi
              exact hball i (hu'' (Finset.filter_subset (fun i => pρ i = m) u'' (hfibre' hi))))
      have hdims' : IsPlankOfDimensions plankPigeonhole.C ap bp W := by
        dsimp [W]
        exact hdims m hm part hpart
      have hlong : Metric.ethickness ℝ W.carrier 0 ≤ 1 := by
        exact Metric.ethickness_le_of_subset_closedBall (x := (0 : E)) 1 hWball 0
      obtain ⟨Tb, hWle, hvol1, hvol2⟩ :=
        exists_plank_tube_of_thickness_le_one hdim ha0 hab hb1 W hWball hdims' hlong
      refine ⟨Tb, fun _ => ?_⟩
      refine ⟨hWle, ?_, ?_, ?_, ?_⟩
      · intro k hk
        exact le_trans (Finset.le_convexHull_biUnion (fun i => (T i).toConvexSpaceBody) hk) hWle
      · simpa [densityTransfer.C] using hvol1
      · simpa [densityTransfer.C] using hvol2
      · refine (carrier_subset_closedBall_of_le_dilate (T := Tb) (c := 2) (by norm_num)
          hWle hWball).trans (Metric.closedBall_subset_closedBall ?_)
        have : (0 : ℝ) ≤ ((plankPigeonhole.C * bp : NNReal) : ℝ) := NNReal.coe_nonneg _
        linarith
    · exact ⟨Classical.choice htube, fun hmem => (hj hmem).elim⟩
  choose V hV using hforall
  exact ⟨V, fun j hj => hV j hj⟩

/-- **The tubes attached to the planks, indexed injectively** (blueprint
`lem:ml1bootPlankTubeChoice`).

Write `b♯ = C_𝕎 b` and let `𝓘` be the block index set of
`Kakeya.ml1Boot.plankBlocks_partition`.  Then there are a family `(T̃_{b,ι})_{ι ∈ t_b}` of
tubes of scale `b♯`, indexed *injectively* by a subset `t_b ⊆ 𝓘`, and a surjection
`r : 𝓘 → t_b`, such that for every `(m, t) ∈ 𝓘` the `2`-dilate of `T̃_{b,r(m,t)}` contains the
plank `W_{m,t}` and every `T̃_k` with `k ∈ t`, and its volume is comparable to
`(b/a) |W_{m,t}|` with constant `C_T = Kakeya.ml1Boot.densityTransfer.C`.

This is `Kakeya.ml1Boot.exists_plankTube_blockwise` followed by
`Kakeya.ml1Boot.exists_dedupe_dilate`, which makes the resulting family injectively indexed —
what the injectivity clause of `Kakeya.ml1Boot.IsParentFamily` requires — and transports the
three conclusions along the resulting equality of dilates.  The containment is stated for the
`2`-dilate and not for the tube itself: see blueprint `def:ml1bootParentFamilyDilate` and
`note:ml1bootPlankInTubeVacuous`.

Like `Kakeya.ml1Boot.exists_plankTube_blockwise`, which is its only geometric input, this carries
no parent family and no parent scale: neither appears in the conclusion, and the two steps behind
it -- the blockwise choice and `Kakeya.ml1Boot.exists_dedupe_dilate` -- inspect no `ρ`-tube.  So
the statement serves the merged, dilate-only parents as well as the undilated ones. -/
theorem exists_plankTube_family [Nontrivial E] (hdim : Module.finrank ℝ E = 3)
    {δt ap bp : NNReal} (hδt : 0 < δt) (hδa : δt ≤ ap) (hab : ap ≤ bp) (hb1 : bp ≤ 1)
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {u u'' : Finset ι} {tρ : Finset κ}
    (T : ι → Tube δt E) (pρ : ι → κ)
    (hu'' : u'' ⊆ u)
    (hball : ∀ i ∈ u, (T i).carrier ⊆ Metric.closedBall 0 1)
    (F : (m : κ) → ConvexSpaceBody.Factorization (fibre u'' pρ m)
      (fun i => (T i).toConvexSpaceBody) 2)
    (hparts : ∀ m ∈ tρ, ∀ part ∈ (F m).parts, part.Nonempty)
    (hdims : ∀ m ∈ tρ, IsPlankFamilyOfDimensions plankPigeonhole.C ap bp (F m).parts
      (fun part => part.convexHull_biUnion (fun i => (T i).toConvexSpaceBody))) :
    ∃ (tb : Finset (κ × Finset ι)) (Tb : κ × Finset ι → Tube (plankPigeonhole.C * bp) E)
      (r : κ × Finset ι → κ × Finset ι),
      tb ⊆ tρ.biUnion (fun m => (F m).parts.image fun part => (m, part)) ∧
      Set.InjOn (fun j => (Tb j).toConvexSpaceBody) ↑tb ∧
      (∀ j ∈ tρ.biUnion fun m => (F m).parts.image fun part => (m, part), r j ∈ tb) ∧
      Set.SurjOn r ↑(tρ.biUnion fun m => (F m).parts.image fun part => (m, part)) ↑tb ∧
      ∀ j ∈ tρ.biUnion fun m => (F m).parts.image fun part => (m, part),
        (j.2.convexHull_biUnion fun i => (T i).toConvexSpaceBody) ≤ Tube.dilate (Tb (r j)) 2 ∧
        (∀ k ∈ j.2, (T k).toConvexSpaceBody ≤ Tube.dilate (Tb (r j)) 2) ∧
        (densityTransfer.C : ENNReal)⁻¹ * ((bp : ENNReal) / (ap : ENNReal))
            * volume (j.2.convexHull_biUnion fun i => (T i).toConvexSpaceBody).carrier
          ≤ volume (Tube.dilate (Tb (r j)) 2).carrier ∧
        volume (Tube.dilate (Tb (r j)) 2).carrier
          ≤ (densityTransfer.C : ENNReal) * ((bp : ENNReal) / (ap : ENNReal))
            * volume (j.2.convexHull_biUnion fun i => (T i).toConvexSpaceBody).carrier ∧
        (Tb j).carrier ⊆ Metric.closedBall (0 : E)
          (5 / 2 + 3 * ((plankPigeonhole.C * bp : NNReal) : ℝ)) := by
  classical
  obtain ⟨V, hV⟩ :=
    exists_plankTube_blockwise hdim hδt hδa hab hb1 T pρ hu'' hball F hparts hdims
  obtain ⟨tb, hts, r, hinj, hrt, hsurj, hdil⟩ :=
    exists_dedupe_dilate
      (s := tρ.biUnion (fun m => (F m).parts.image fun part => (m, part))) V
  refine ⟨tb, V, r, hts, hinj, hrt, hsurj, ?_⟩
  intro j hj
  rw [hdil j hj 2]
  exact hV j hj

/-- **The tube attached to a plank lies in a dilate of the parent `ρ`-tube** (blueprint
`lem:ml1bootPlankTubeInParentDilate`).

Write `c' = Kakeya.ml1Boot.plankTubeInParent.C = 32 C_𝕎`.  If a plank `W` of dimensions
`ap × bp × 1` lies in a `ρ`-tube `T_ρ` and has `ethickness … 0 ≥ 1/2`, then the tube `T_b` of
scale `C_𝕎 bp` attached to it by `Kakeya.ml1Boot.exists_plankTube_family` lies in the
`c'`-dilate of `T_ρ`.

**This is an accepted hypothesis, not a derived one.**  It replaces the plain containment
`T_b ⊆ T_ρ`, which earlier drafts asserted and which is *false*: `T_b` has thickness up to
`C_𝕎 bp` and its unit core is built from the outer prism of `W` rather than from the core of
`T_ρ`, so it protrudes both transversally and longitudinally.  What is true is that the
protrusion is `O(ρ)`, hence absorbed by a dilation of constant ratio.

Two points fix the value of `c'`, both recorded in blueprint
`note:auditPlankTubeInParentDilate`.  First, `Tb` is an *arbitrary* tube of scale `C_𝕎 bp`
admitting `W`, and `hlong` gives only `diam W ≥ 2⁻¹`, so `Tb` is pinned to the axis of `T_ρ`
only up to a chord angle.  Second, `hTb` is the *dilated* containment `W ≤ 2 · Tb`, which is
what `Kakeya.ml1Boot.exists_plankTube_family` supplies; the undilated `W ≤ Tb` is
unsatisfiable for these planks (blueprint `note:ml1bootPlankInTubeStillFalse`), and using it
here would make the hypothesis unavailable at the one call site.  With the dilated hypothesis
the transverse protrusion is `ρ + 21 C_𝕎 ρ ≤ 22 C_𝕎 ρ` and the longitudinal reach is
`2 + ρ + 3 C_𝕎 ρ`, both dominated by `c' = 32 C_𝕎` and neither by `c' ≥ 1`. -/
theorem plankTube_subset_parent_dilate [Nontrivial E] (_hdim : Module.finrank ℝ E = 3)
    {δt ap bp ρ : NNReal} (_hδt : 0 < δt) (_hδa : δt ≤ ap) (_hab : ap ≤ bp) (hbρ : bp ≤ ρ)
    (hρ1 : ρ ≤ 1) (Tρ : Tube ρ E) (W : ConvexSpaceBody E)
    (_hdims : IsPlankOfDimensions plankPigeonhole.C ap bp W)
    (hWsub : W ≤ Tρ.toConvexSpaceBody)
    (hlong : 2⁻¹ ≤ Metric.ethickness ℝ W.carrier 0)
    (Tb : Tube (plankPigeonhole.C * bp) E) (hTb : W ≤ Tube.dilate Tb 2) :
    Tb.toConvexSpaceBody ≤ Tube.dilate Tρ (plankTubeInParent.C : ℝ) := by
  classical
  set Cw : ℝ := (plankPigeonhole.C : ℝ)
  set r : ℝ := (ρ : ℝ)
  set b : ℝ := (bp : ℝ)
  have hCw1 : 1 ≤ Cw := by
    dsimp [Cw, plankPigeonhole.C, Metric.volume_comparison.C, Metric.lt_volume_convexHull.c]
    norm_num
  have hCw0 : 0 ≤ Cw := by linarith
  have hr0 : 0 ≤ r := by simp [r]
  have hr1 : r ≤ 1 := by
    simpa [r] using (show ((ρ : ℝ) ≤ 1) from (by exact_mod_cast hρ1))
  have hb0 : 0 ≤ b := by simp [b]
  have hbr : b ≤ r := by
    simpa [b, r] using (show ((bp : ℝ) ≤ (ρ : ℝ)) from (by exact_mod_cast hbρ))
  have hδc : ((plankPigeonhole.C * bp : NNReal) : ℝ) = Cw * b := by
    rw [NNReal.coe_mul]
  have hδle : ((plankPigeonhole.C * bp : NNReal) : ℝ) ≤ Cw * r := by
    rw [hδc]
    exact mul_le_mul_of_nonneg_left hbr hCw0
  -- Two points of W at distance > 2/5, via the diameter route
  have hfar : ∃ p ∈ W.carrier, ∃ q ∈ W.carrier, (2 / 5 : ℝ) < dist p q := by
    by_contra h
    push Not at h
    have hle : Metric.ediam W.carrier ≤ ENNReal.ofReal (2 / 5 : ℝ) := by
      apply Metric.ediam_le
      intro x hx y hy
      rw [edist_dist]
      exact ENNReal.ofReal_le_ofReal (h x hx y hy)
    have hlt : ENNReal.ofReal (2 / 5 : ℝ) < (2 : ENNReal)⁻¹ := by
      have htwo : (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) := by norm_num
      rw [htwo, ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)).2 (by norm_num)
    have hchain : (2 : ENNReal)⁻¹ ≤ ENNReal.ofReal (2 / 5 : ℝ) :=
      le_trans (le_trans hlong (Metric.ethickness_zero_le_ediam (𝕜 := ℝ) W.carrier)) hle
    exact (not_le_of_gt hlt) hchain
  rcases hfar with ⟨p, hpW, q, hqW, hpq⟩
  have hpρ : p ∈ Tρ.carrier := by
    change p ∈ (Tρ.toConvexSpaceBody : Set E)
    exact (SetLike.le_def.mp hWsub) hpW
  have hqρ : q ∈ Tρ.carrier := by
    change q ∈ (Tρ.toConvexSpaceBody : Set E)
    exact (SetLike.le_def.mp hWsub) hqW
  have hpTb : p ∈ (Tube.dilate Tb 2).carrier := by
    change p ∈ (Tube.dilate Tb 2 : Set E)
    exact (SetLike.le_def.mp hTb) hpW
  have hqTb : q ∈ (Tube.dilate Tb 2).carrier := by
    change q ∈ (Tube.dilate Tb 2 : Set E)
    exact (SetLike.le_def.mp hTb) hqW
  -- transverse bound through the chord p q
  have hS : ‖Tb.direction - inner ℝ Tρ.direction Tb.direction • Tρ.direction‖ ≤ 15 * Cw * r := by
    have hchord := Tube.norm_perp_direction_le_of_chord Tρ Tb (d := (2 / 5 : ℝ))
      (by norm_num) (le_of_lt hpq) hpρ hqρ hpTb hqTb
    calc
      ‖Tb.direction - inner ℝ Tρ.direction Tb.direction • Tρ.direction‖
          ≤ (2 * (ρ : ℝ) + 4 * ((plankPigeonhole.C * bp : NNReal) : ℝ)) / (2 / 5) := hchord
      _ = 5 * r + 10 * (Cw * b) := by
        rw [hδc]
        field_simp
        ring
      _ ≤ 15 * Cw * r := by
        nlinarith [hCw1, hCw0, hb0, hr0, hbr]
  -- the dilution ratio `plankTubeInParent.C = 32 * Cw`
  have hcc : (plankTubeInParent.C : ℝ) = 32 * Cw := by
    rfl
  rw [hcc]
  -- the factored containment lemma `Tube.subset_dilate_of_norm_perp_direction_le`
  have hsub : Tb.carrier ⊆ (Tube.dilate Tρ (32 * Cw)).carrier :=
    Tube.subset_dilate_of_norm_perp_direction_le Tρ Tb (K := Cw) hCw1 hr1 hδle hpρ hpTb hS
  apply SetLike.le_def.mpr
  exact hsub

/-! ### The pinning chain against a *dilated* parent

The six declarations below are the `Kakeya/Tube/Dilate.lean` pinning chain
(`Tube.norm_perp_direction_le_of_chord` … `Tube.subset_dilate_of_norm_perp_direction_le`) with
the parent membership of the pinning point `p` weakened from `p ∈ T_ρ` to
`p ∈ c · T_ρ` for a ratio `c ≥ 1`.  They are what the merge-before-pigeonhole route needs:
once the `ρ`-parents are merged by `Kakeya.ml1Boot.exists_merged_rhoParentFamily`, every plank
containment is only a `c`-dilate containment, and the original chain — which reads `hpρ` at the
undilated carrier in three places — is unavailable.

They are *parked* here rather than placed beside the lemmas they generalize, exactly as
`Kakeya.ml1Boot.dilate_le_dilate_of_le` is: `Kakeya/Tube/Dilate.lean` is closed, and the
signed chord-angle step it uses is `private` there, so the copy
`Kakeya.ml1Boot.perp_direction_le_of_aux` is unavoidable.

Every `ρ`-term of the original picks up one factor of `c` and the axial `1/2` becomes `c/2`,
because `Tube.abs_inner_and_perp_le_of_mem_dilate` is already stated at a free ratio and reads
`c / 2 + c δ` and `c δ` there.  With `c ≤ K` and `c ρ ≤ 1` the two branch constants `59/2 K ρ`
and the longitudinal `16 K` are unchanged, so the final ratio is `32 K` exactly as before; at
`c = 1` each statement is the original one, `Tube.subset_dilate` turning `p ∈ T_ρ` into
`p ∈ 1 · T_ρ`. -/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The signed chord-angle step: unit vectors `e f g` with `⟪e, g⟫ ≥ 0` and `⟪g, f⟫ ≥ 0`, whose
perpendicular parts with respect to `e` and `f` are bounded by `A` and `B` with `A + B < 1`,
have the perpendicular part of `f` with respect to `e` bounded by `A + B`.

A copy of the `private` `Kakeya.Tube.norm_perp_direction_le_of_aux`
(`Kakeya/Tube/Dilate.lean:491`), which is unreachable from here.  The statement contains no
tube and no dilation ratio, so it is shared verbatim by the undilated chord bound and by
`Kakeya.ml1Boot.norm_perp_direction_le_of_chord_dilate` below; if
`Kakeya/Tube/Dilate.lean` is ever reopened, the two copies should be merged by making the
original non-private and deleting this one. -/
private lemma perp_direction_le_of_aux {e f g : E} (he : ‖e‖ = 1) (hf : ‖f‖ = 1)
    (hg : ‖g‖ = 1) (hge : 0 ≤ inner ℝ e g) (hgf : 0 ≤ inner ℝ g f) {A B : ℝ}
    (hA : ‖g - inner ℝ e g • e‖ ≤ A) (hB : ‖g - inner ℝ f g • f‖ ≤ B) (hAB : A + B < 1) :
    ‖f - inner ℝ e f • e‖ ≤ A + B := by
  let α : ℝ := InnerProductGeometry.angle e g
  let β : ℝ := InnerProductGeometry.angle g f
  have hα0 : 0 ≤ α := by
    dsimp [α]
    exact InnerProductGeometry.angle_nonneg e g
  have hβ0 : 0 ≤ β := by
    dsimp [β]
    exact InnerProductGeometry.angle_nonneg g f
  have hα_le_pi : α ≤ Real.pi := by
    dsimp [α]
    exact InnerProductGeometry.angle_le_pi e g
  have hα_le : α ≤ Real.pi / 2 := by
    dsimp [α]
    rw [InnerProductGeometry.angle, Real.arccos_le_pi_div_two]
    exact div_nonneg hge (mul_pos (by (rw [he]; norm_num)) (by rw [hg]; norm_num)).le
  have hβ_le : β ≤ Real.pi / 2 := by
    dsimp [β]
    rw [InnerProductGeometry.angle, Real.arccos_le_pi_div_two]
    exact div_nonneg hgf (mul_pos (by rw [hg]; norm_num) (by rw [hf]; norm_num)).le
  have hsinα : Real.sin α = ‖g - inner ℝ e g • e‖ := by
    dsimp [α]
    exact (InnerProductGeometry.norm_sub_inner_smul_eq_sin_angle he hg).symm
  have hsinβ : Real.sin β = ‖g - inner ℝ f g • f‖ := by
    dsimp [β]
    rw [InnerProductGeometry.angle_comm]
    exact (InnerProductGeometry.norm_sub_inner_smul_eq_sin_angle hf hg).symm
  have hsinα_le_A : Real.sin α ≤ A := by rw [hsinα]; exact hA
  have hsinβ_le_B : Real.sin β ≤ B := by rw [hsinβ]; exact hB
  have hαβ_le : α + β ≤ Real.pi / 2 := by
    by_contra hnot
    have hgt : Real.pi / 2 < α + β := lt_of_not_ge hnot
    have hsub0 : 0 ≤ Real.pi / 2 - α := by linarith
    have hβgt : Real.pi / 2 - α < β := by linarith
    have hsin_gt : Real.cos α < Real.sin β := by
      have hlt := Real.sin_lt_sin_of_lt_of_le_pi_div_two
        (x := Real.pi / 2 - α) (y := β) (by linarith) hβ_le hβgt
      rwa [Real.sin_pi_div_two_sub] at hlt
    have hcosα0 : 0 ≤ Real.cos α := Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) hα_le
    have hsinα0 : 0 ≤ Real.sin α := by
      dsimp [α]
      exact InnerProductGeometry.sin_angle_nonneg e g
    have hsum1 : 1 ≤ Real.sin α + Real.cos α := by
      have hshow : (1 : ℝ) ^ 2 ≤ (Real.sin α + Real.cos α) ^ 2 := by
        have hsc : Real.sin α ^ 2 + Real.cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
        nlinarith [sq_nonneg (Real.sin α), sq_nonneg (Real.cos α)]
      exact le_of_sq_le_sq hshow (add_nonneg hsinα0 hcosα0)
    nlinarith [hsinα_le_A, hsinβ_le_B, hsin_gt, hsum1, hAB]
  have hangle : InnerProductGeometry.angle e f ≤ α + β := by
    dsimp [α, β]
    exact InnerProductGeometry.angle_le_angle_add_angle e g f
  have hsin_ef_le : Real.sin (InnerProductGeometry.angle e f) ≤ Real.sin (α + β) := by
    have hx0 : 0 ≤ InnerProductGeometry.angle e f := InnerProductGeometry.angle_nonneg e f
    exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) hαβ_le hangle
  have hsin_add : Real.sin (α + β) ≤ Real.sin α + Real.sin β :=
    Real.sin_add_le_sin_add_sin hα0 hβ0 hαβ_le
  calc
    ‖f - inner ℝ e f • e‖ = Real.sin (InnerProductGeometry.angle e f) :=
      InnerProductGeometry.norm_sub_inner_smul_eq_sin_angle he hf
    _ ≤ Real.sin (α + β) := hsin_ef_le
    _ ≤ Real.sin α + Real.sin β := hsin_add
    _ ≤ A + B := add_le_add hsinα_le_A hsinβ_le_B

/-- **The chord-angle bound against a dilated parent** (blueprint `lem:chordAngleBound`, read at
a dilate).

Two points at distance at least `d` lying both in the `c`-dilate of the `ρ`-tube `Tρ` and in the
`2`-dilate of the `δ`-tube `Tb` pin the direction of `Tb` to that of `Tρ`, with the transverse
component at most `(2 c ρ + 4 δ) / d`.

This is `Kakeya.Tube.norm_perp_direction_le_of_chord` (`Kakeya/Tube/Dilate.lean:564`) with
`hpρ`, `hqρ` weakened from `Tρ.carrier` to `(c · Tρ).carrier`.  That lemma consumes them in
exactly one way — `Tube.subset_dilate Tρ 1` followed by
`Tube.abs_inner_and_perp_le_of_mem_dilate Tρ (c := 1)`, at lines 589-596 — to bound each
transverse offset by `ρ`; reading the same free-ratio lemma at `c` bounds them by `c ρ`, so the
chord's transverse part becomes `2 c ρ` and the numerator `2 c ρ + 4 δ`.  Nothing else in the
proof touches the parent, and at `c = 1` this is that lemma. -/
theorem norm_perp_direction_le_of_chord_dilate {ρ δ : NNReal} (Tρ : Tube ρ E) (Tb : Tube δ E)
    {c : ℝ} (hc : 0 < c) {d : ℝ} (hd : 0 < d) {p q : E} (hpq : d ≤ dist p q)
    (hpρ : p ∈ (Tube.dilate Tρ c).carrier) (hqρ : q ∈ (Tube.dilate Tρ c).carrier)
    (hpb : p ∈ (Tube.dilate Tb 2).carrier) (hqb : q ∈ (Tube.dilate Tb 2).carrier) :
    ‖Tb.direction - inner ℝ Tρ.direction Tb.direction • Tρ.direction‖
      ≤ (2 * c * (ρ : ℝ) + 4 * (δ : ℝ)) / d := by
  let e : E := Tρ.direction
  let f : E := Tb.direction
  let g : E := (‖p - q‖)⁻¹ • (p - q)
  let A : ℝ := 2 * c * (ρ : ℝ) / d
  let B : ℝ := 4 * (δ : ℝ) / d
  have he : ‖e‖ = 1 := by
    dsimp [e]
    exact Tρ.norm_direction
  have hf : ‖f‖ = 1 := by
    dsimp [f]
    exact Tb.norm_direction
  have hpq_le : d ≤ ‖p - q‖ := by simpa [dist_eq_norm] using hpq
  have hpqn_pos : 0 < ‖p - q‖ := lt_of_lt_of_le hd hpq_le
  have hg : ‖g‖ = 1 := by
    dsimp [g]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpqn_pos)]
    exact inv_mul_cancel₀ (ne_of_gt hpqn_pos)
  -- Step 1: the chord `p - q` is nearly parallel to `e = Tρ.direction`
  have hppρ : ‖p - Tρ.center - inner ℝ e (p - Tρ.center) • e‖ ≤ c * (ρ : ℝ) := by
    have hz := (Tube.abs_inner_and_perp_le_of_mem_dilate Tρ (c := c) hc hpρ).2
    simpa [e] using hz
  have hqpρ : ‖q - Tρ.center - inner ℝ e (q - Tρ.center) • e‖ ≤ c * (ρ : ℝ) := by
    have hz := (Tube.abs_inner_and_perp_le_of_mem_dilate Tρ (c := c) hc hqρ).2
    simpa [e] using hz
  have hperp_e : ‖(p - q) - inner ℝ e (p - q) • e‖ ≤ 2 * c * (ρ : ℝ) := by
    have hid : (p - q) - inner ℝ e (p - q) • e
        = (p - Tρ.center - inner ℝ e (p - Tρ.center) • e)
            - (q - Tρ.center - inner ℝ e (q - Tρ.center) • e) := by
      rw [inner_sub_right, inner_sub_right, inner_sub_right]
      module
    calc
      ‖(p - q) - inner ℝ e (p - q) • e‖
          = ‖(p - Tρ.center - inner ℝ e (p - Tρ.center) • e)
              - (q - Tρ.center - inner ℝ e (q - Tρ.center) • e)‖ := by
            rw [hid]
      _ ≤ ‖p - Tρ.center - inner ℝ e (p - Tρ.center) • e‖
            + ‖q - Tρ.center - inner ℝ e (q - Tρ.center) • e‖ := by
        exact norm_sub_le _ _
      _ ≤ c * (ρ : ℝ) + c * (ρ : ℝ) := by linarith
      _ = 2 * c * (ρ : ℝ) := by ring
  have hIdent_e : g - inner ℝ e g • e = (‖p - q‖)⁻¹ • ((p - q) - inner ℝ e (p - q) • e) := by
    dsimp [g]
    rw [real_inner_smul_right]
    rw [← smul_smul]
    rw [← smul_sub]
  have hgperp_e : ‖g - inner ℝ e g • e‖ ≤ A := by
    dsimp [A]
    rw [hIdent_e]
    rw [norm_smul]
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpqn_pos)]
    have hdiv : (‖p - q‖)⁻¹ * ‖(p - q) - inner ℝ e (p - q) • e‖
        = ‖(p - q) - inner ℝ e (p - q) • e‖ / ‖p - q‖ := by
      rw [div_eq_inv_mul]
    rw [hdiv]
    calc
      ‖(p - q) - inner ℝ e (p - q) • e‖ / ‖p - q‖
          ≤ ‖(p - q) - inner ℝ e (p - q) • e‖ / d := by
            exact div_le_div_of_nonneg_left (norm_nonneg _) hd hpq_le
      _ ≤ 2 * c * (ρ : ℝ) / d := div_le_div_of_nonneg_right hperp_e hd.le
  -- Step 2: the chord is nearly parallel to `f = Tb.direction`
  have hppδ : ‖p - Tb.center - inner ℝ f (p - Tb.center) • f‖ ≤ 2 * (δ : ℝ) := by
    have hz := (Tube.abs_inner_and_perp_le_of_mem_dilate Tb (c := 2) (by norm_num) hpb).2
    simpa [f] using hz
  have hqpδ : ‖q - Tb.center - inner ℝ f (q - Tb.center) • f‖ ≤ 2 * (δ : ℝ) := by
    have hz := (Tube.abs_inner_and_perp_le_of_mem_dilate Tb (c := 2) (by norm_num) hqb).2
    simpa [f] using hz
  have hperp_f : ‖(p - q) - inner ℝ f (p - q) • f‖ ≤ 4 * (δ : ℝ) := by
    have hid : (p - q) - inner ℝ f (p - q) • f
        = (p - Tb.center - inner ℝ f (p - Tb.center) • f)
            - (q - Tb.center - inner ℝ f (q - Tb.center) • f) := by
      rw [inner_sub_right, inner_sub_right, inner_sub_right]
      module
    rw [hid]
    exact (norm_sub_le _ _).trans (by linarith)
  have hIdent_f : g - inner ℝ f g • f = (‖p - q‖)⁻¹ • ((p - q) - inner ℝ f (p - q) • f) := by
    dsimp [g]
    rw [real_inner_smul_right]
    rw [← smul_smul]
    rw [← smul_sub]
  have hgperp_f : ‖g - inner ℝ f g • f‖ ≤ B := by
    dsimp [B]
    rw [hIdent_f]
    rw [norm_smul]
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpqn_pos)]
    have hdiv : (‖p - q‖)⁻¹ * ‖(p - q) - inner ℝ f (p - q) • f‖
        = ‖(p - q) - inner ℝ f (p - q) • f‖ / ‖p - q‖ := by
      rw [div_eq_inv_mul]
    rw [hdiv]
    calc
      ‖(p - q) - inner ℝ f (p - q) • f‖ / ‖p - q‖
          ≤ ‖(p - q) - inner ℝ f (p - q) • f‖ / d := by
              exact div_le_div_of_nonneg_left (norm_nonneg _) hd hpq_le
      _ ≤ 4 * (δ : ℝ) / d := div_le_div_of_nonneg_right hperp_f hd.le
  -- Step 3: combine the two near-parallelisms through the angle triangle inequality
  have hmain : ‖f - inner ℝ e f • e‖ ≤ A + B := by
    by_cases htriv : 1 ≤ A + B
    · have hle1 : ‖f - inner ℝ e f • e‖ ≤ 1 := by
        rw [InnerProductGeometry.norm_sub_inner_smul_eq_sin_angle he hf]
        exact Real.sin_le_one _
      exact le_trans hle1 htriv
    · have hAB : A + B < 1 := by linarith
      by_cases hge : 0 ≤ inner ℝ e g
      · by_cases hgf : 0 ≤ inner ℝ g f
        · exact perp_direction_le_of_aux he hf hg hge hgf hgperp_e hgperp_f hAB
        · have hgf' : 0 ≤ inner ℝ g (-f) := by
            rw [inner_neg_right]
            linarith [lt_of_not_ge hgf]
          have hB' : ‖g - inner ℝ (-f) g • (-f)‖ ≤ B := by
            have hid : g - inner ℝ (-f) g • (-f) = g - inner ℝ f g • f := by
              simp [inner_neg_left]
            rwa [hid]
          have hconc := perp_direction_le_of_aux he (by simpa using hf) hg hge hgf'
            hgperp_e hB' hAB
          have hnorm : ‖(-f) - inner ℝ e (-f) • e‖ = ‖f - inner ℝ e f • e‖ := by
            calc
              ‖(-f) - inner ℝ e (-f) • e‖ = ‖-(f - inner ℝ e f • e)‖ := by
                congr 1
                simp [inner_neg_right]
                abel
              _ = ‖f - inner ℝ e f • e‖ := norm_neg (f - inner ℝ e f • e)
          rwa [← hnorm]
      · by_cases hgf : 0 ≤ inner ℝ g f
        · have hge' : 0 ≤ inner ℝ (-e) g := by
            rw [inner_neg_left]
            linarith [lt_of_not_ge hge]
          have hA' : ‖g - inner ℝ (-e) g • (-e)‖ ≤ A := by
            have hid : g - inner ℝ (-e) g • (-e) = g - inner ℝ e g • e := by
              simp [inner_neg_left]
            rwa [hid]
          have hconc := perp_direction_le_of_aux (by simpa using he) hf hg hge' hgf
            hA' hgperp_f hAB
          simpa [inner_neg_left] using hconc
        · have hge' : 0 ≤ inner ℝ (-e) g := by
            rw [inner_neg_left]
            linarith [lt_of_not_ge hge]
          have hgf' : 0 ≤ inner ℝ g (-f) := by
            rw [inner_neg_right]
            linarith [lt_of_not_ge hgf]
          have hA' : ‖g - inner ℝ (-e) g • (-e)‖ ≤ A := by
            have hid : g - inner ℝ (-e) g • (-e) = g - inner ℝ e g • e := by
              simp [inner_neg_left]
            rwa [hid]
          have hB' : ‖g - inner ℝ (-f) g • (-f)‖ ≤ B := by
            have hid : g - inner ℝ (-f) g • (-f) = g - inner ℝ f g • f := by
              simp [inner_neg_left]
            rwa [hid]
          have hconc := perp_direction_le_of_aux (by simpa using he) (by simpa using hf) hg
            hge' hgf' hA' hB' hAB
          have hnorm : ‖(-f) - inner ℝ (-e) (-f) • (-e)‖ = ‖f - inner ℝ e f • e‖ := by
            calc
              ‖(-f) - inner ℝ (-e) (-f) • (-e)‖ = ‖-(f - inner ℝ e f • e)‖ := by
                congr 1
                simp [inner_neg_left, inner_neg_right]
                abel
              _ = ‖f - inner ℝ e f • e‖ := norm_neg (f - inner ℝ e f • e)
          rwa [← hnorm]
  have hmain' : ‖f - inner ℝ e f • e‖ ≤ (2 * c * (ρ : ℝ) + 4 * (δ : ℝ)) / d := by
    dsimp [A, B] at hmain
    rw [add_div]
    exact hmain
  simpa [e, f] using hmain'

/-- **A pinned thin tube is longitudinally confined, against a dilated parent** (blueprint
`lem:thinTubeInFatDilateLongitudinal`, read at a dilate).

`Kakeya.Tube.abs_inner_sub_center_le_of_pinned` (`Kakeya/Tube/Dilate.lean:830`) with `hpρ` read
at `c · Tρ`.  The axial offset of `p` grows from `1/2 + ρ` to `c / 2 + c ρ`; with `c ≤ K` and
`c ρ ≤ 1` the chain is `c / 2 + c ρ + 3 / 2 + 6 δ ≤ K / 2 + 1 + 3 / 2 + 6 K ≤ 16 K`, so the
figure `16 K` is unchanged.  The hypothesis `hρ1 : ρ ≤ 1` of the original is subsumed by
`hcρ : c ρ ≤ 1` together with `1 ≤ c`. -/
theorem abs_inner_sub_center_le_of_pinned_dilate {ρ δ : NNReal} (Tρ : Tube ρ E) (Tb : Tube δ E)
    {c K : ℝ} (hc : 1 ≤ c) (hcK : c ≤ K) (hcρ : c * (ρ : ℝ) ≤ 1) (hδ : (δ : ℝ) ≤ K * (ρ : ℝ))
    {p : E} (hpρ : p ∈ (Tube.dilate Tρ c).carrier) (hpb : p ∈ (Tube.dilate Tb 2).carrier)
    {x : E} (hx : x ∈ Tb.carrier) :
    |inner ℝ Tρ.direction (x - Tρ.center)| ≤ 16 * K := by
  -- x lies in the 1-dilate of Tb, so the chord estimate bounds `dist x p`
  have hx1 : x ∈ (Tube.dilate Tb 1).carrier := Tube.subset_dilate Tb (by norm_num) hx
  have hdist : dist x p ≤ 3 / 2 + 6 * (δ : ℝ) := by
    have hz := Tube.dist_le_of_mem_dilate_of_mem_dilate (T := Tb) (c := 1) (c' := 2)
      (by norm_num) (by norm_num) hx1 hpb
    nlinarith
  -- p lies in the c-dilate of Tρ, pinning its axial coordinate with respect to Tρ
  have hcpos : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hpax : |inner ℝ Tρ.direction (p - Tρ.center)| ≤ c / 2 + c * (ρ : ℝ) := by
    have hz := (Tube.abs_inner_and_perp_le_of_mem_dilate Tρ (c := c) hcpos hpρ).1
    simpa [real_inner_comm] using hz
  -- Cauchy-Schwarz with `‖Tρ.direction‖ = 1`
  have hxp : |inner ℝ Tρ.direction (x - p)| ≤ dist x p := by
    calc
      |inner ℝ Tρ.direction (x - p)| ≤ ‖Tρ.direction‖ * ‖x - p‖ :=
        abs_real_inner_le_norm Tρ.direction (x - p)
      _ = ‖x - p‖ := by simp [Tρ.norm_direction]
      _ = dist x p := by rw [← dist_eq_norm]
  -- the arithmetic: c / 2 + c·ρ + 3 / 2 + 6·δ ≤ 16·K
  have hρ0 : 0 ≤ (ρ : ℝ) := NNReal.coe_nonneg ρ
  have hρ1 : (ρ : ℝ) ≤ 1 := by
    calc
      (ρ : ℝ) ≤ c * (ρ : ℝ) := by
        simpa using mul_le_mul_of_nonneg_right hc hρ0
      _ ≤ 1 := hcρ
  have hK1 : 1 ≤ K := le_trans hc hcK
  have hK0 : 0 ≤ K := by linarith
  have hδK : (δ : ℝ) ≤ K := by
    calc
      (δ : ℝ) ≤ K * (ρ : ℝ) := hδ
      _ ≤ K := by
        simpa using mul_le_mul_of_nonneg_left hρ1 hK0
  -- triangle inequality, then the two estimates, then the arithmetic
  calc
    |inner ℝ Tρ.direction (x - Tρ.center)|
        ≤ |inner ℝ Tρ.direction (p - Tρ.center)| + |inner ℝ Tρ.direction (x - p)| := by
          rw [show x - Tρ.center = (p - Tρ.center) + (x - p) by abel]
          rw [inner_add_right]
          exact abs_add_le _ _
    _ ≤ (c / 2 + c * (ρ : ℝ)) + dist x p := add_le_add hpax hxp
    _ ≤ (c / 2 + c * (ρ : ℝ)) + (3 / 2 + 6 * (δ : ℝ)) := by
          exact add_le_add (le_refl (c / 2 + c * (ρ : ℝ))) hdist
    _ ≤ 16 * K := by
          nlinarith [hc, hcK, hcρ, hδ, hρ0, hρ1, hK1, hK0, hδK]

/-- **Transverse confinement against a dilated parent: the small-angle branch** (blueprint
`lem:thinTubeInFatDilateTransverseSmallAngle`, read at a dilate).

`Kakeya.Tube.norm_perp_sub_center_le_of_pinned_of_le_one` (`Kakeya/Tube/Dilate.lean:875`) with
`hpρ` read at `c · Tρ`: the transverse offset of `p` grows from `ρ` to `c ρ`, and `c ≤ K` puts
that back under `K ρ`.  The rest of the chain is untouched, so the sum
`c ρ + (3/2 + 3 δ) S + 3 δ` is again at most `29.5 K ρ`, the case hypothesis `15 K ρ ≤ 1`
absorbing the quadratic term `45 K² ρ²` into `3 K ρ` exactly as before. -/
theorem norm_perp_sub_center_le_of_pinned_dilate_of_le_one {ρ δ : NNReal} (Tρ : Tube ρ E)
    (Tb : Tube δ E) {c K : ℝ} (hc : 1 ≤ c) (hcK : c ≤ K) (hδ : (δ : ℝ) ≤ K * (ρ : ℝ))
    {p : E} (hpρ : p ∈ (Tube.dilate Tρ c).carrier) (hpb : p ∈ (Tube.dilate Tb 2).carrier)
    (hS : ‖Tb.direction - inner ℝ Tρ.direction Tb.direction • Tρ.direction‖
      ≤ 15 * K * (ρ : ℝ))
    (hsmall : 15 * K * (ρ : ℝ) ≤ 1) {x : E} (hx : x ∈ Tb.carrier) :
    ‖(x - Tρ.center) - inner ℝ Tρ.direction (x - Tρ.center) • Tρ.direction‖
      ≤ 59 / 2 * K * (ρ : ℝ) := by
  let e : E := Tρ.direction
  let S : ℝ := ‖Tb.direction - inner ℝ e Tb.direction • e‖
  have he : ‖e‖ = 1 := by
    simpa [e] using Tρ.norm_direction
  have hS' : S ≤ 15 * K * (ρ : ℝ) := by
    simpa [S, e] using hS
  have hS0 : 0 ≤ S := by
    dsimp [S]
    exact norm_nonneg _
  have hK : 1 ≤ K := le_trans hc hcK
  have hK0 : 0 ≤ K := by linarith
  have hρ0 : 0 ≤ (ρ : ℝ) := NNReal.coe_nonneg ρ
  have hδ0 : 0 ≤ (δ : ℝ) := NNReal.coe_nonneg δ
  have hx1 : x ∈ (Tube.dilate Tb 1).carrier := Tube.subset_dilate Tb (by norm_num) hx
  have hpa : ‖(p - Tρ.center) - inner ℝ e (p - Tρ.center) • e‖ ≤ c * (ρ : ℝ) := by
    have hz := (Tube.abs_inner_and_perp_le_of_mem_dilate Tρ (c := c)
      (lt_of_lt_of_le zero_lt_one hc) hpρ).2
    simpa [e] using hz
  have hpbp : ‖(p - Tb.center) - inner ℝ e (p - Tb.center) • e‖
      ≤ (1 + 2 * (δ : ℝ)) * S + 2 * (δ : ℝ) := by
    have hz := Tube.norm_perp_sub_center_le_of_mem_dilate (T := Tb) (c := 2) (hc := by norm_num)
      (e := e) (he := he) (y := p) (hy := hpb)
    simpa [S, e, one_mul] using hz
  have hxb : ‖(x - Tb.center) - inner ℝ e (x - Tb.center) • e‖
      ≤ (1 / 2 + (δ : ℝ)) * S + (δ : ℝ) := by
    have hz := Tube.norm_perp_sub_center_le_of_mem_dilate (T := Tb) (c := 1) (hc := by norm_num)
      (e := e) (he := he) (y := x) (hy := hx1)
    simpa [S, e, one_mul] using hz
  have hid : (x - Tρ.center) - inner ℝ e (x - Tρ.center) • e
      = ((p - Tρ.center) - inner ℝ e (p - Tρ.center) • e)
        - ((p - Tb.center) - inner ℝ e (p - Tb.center) • e)
        + ((x - Tb.center) - inner ℝ e (x - Tb.center) • e) := by
    rw [show x - Tρ.center = (p - Tρ.center) - (p - Tb.center) + (x - Tb.center) by abel]
    rw [inner_add_right, inner_sub_right, inner_sub_right, inner_sub_right]
    module
  have htri : ‖(x - Tρ.center) - inner ℝ e (x - Tρ.center) • e‖
      ≤ ‖(p - Tρ.center) - inner ℝ e (p - Tρ.center) • e‖
        + (‖(p - Tb.center) - inner ℝ e (p - Tb.center) • e‖
          + ‖(x - Tb.center) - inner ℝ e (x - Tb.center) • e‖) := by
    let A : E := (p - Tρ.center) - inner ℝ e (p - Tρ.center) • e
    let B : E := (p - Tb.center) - inner ℝ e (p - Tb.center) • e
    let C : E := (x - Tb.center) - inner ℝ e (x - Tb.center) • e
    rw [hid]
    calc
      ‖A - B + C‖ ≤ ‖A - B‖ + ‖C‖ := norm_add_le (A - B) C
      _ ≤ (‖A‖ + ‖B‖) + ‖C‖ := add_le_add (norm_sub_le A B) le_rfl
      _ = ‖A‖ + (‖B‖ + ‖C‖) := by ring
  have hbound : ‖(x - Tρ.center) - inner ℝ e (x - Tρ.center) • e‖
      ≤ c * (ρ : ℝ) + (3 / 2 + 3 * (δ : ℝ)) * S + 3 * (δ : ℝ) := by
    nlinarith [htri, hpa, hpbp, hxb]
  have hK3 : 0 ≤ 3 * K := by nlinarith
  have hpos : 0 ≤ 3 * K * (ρ : ℝ) := mul_nonneg hK3 hρ0
  have hprod : 45 * K ^ 2 * (ρ : ℝ) ^ 2 ≤ 3 * K * (ρ : ℝ) := by
    rw [show 45 * K ^ 2 * (ρ : ℝ) ^ 2 = 3 * K * (ρ : ℝ) * (15 * K * (ρ : ℝ)) by ring]
    simpa using mul_le_mul_of_nonneg_left hsmall hpos
  have hcρK : c * (ρ : ℝ) ≤ K * (ρ : ℝ) := by
    exact mul_le_mul_of_nonneg_right hcK hρ0
  calc
    ‖(x - Tρ.center) - inner ℝ e (x - Tρ.center) • e‖
        ≤ c * (ρ : ℝ) + (3 / 2 + 3 * (δ : ℝ)) * S + 3 * (δ : ℝ) := hbound
    _ ≤ 59 / 2 * K * (ρ : ℝ) := by
      nlinarith [hS', hS0, hδ, hδ0, hρ0, hK, hK0, hprod, hcρK]

/-- **Transverse confinement against a dilated parent: the large-angle branch** (blueprint
`lem:thinTubeInFatDilateTransverseLargeAngle`, read at a dilate).

`Kakeya.Tube.norm_perp_sub_center_le_of_pinned_of_one_lt` (`Kakeya/Tube/Dilate.lean:948`) with
`hpρ` read at `c · Tρ`.  This branch is angle-free: the bound is
`c ρ + 3/2 + 6 δ ≤ K ρ + (45/2) K ρ + 6 K ρ = 29.5 K ρ`, the middle step being
`3/2 ≤ (45/2) K ρ` from the case hypothesis `1 < 15 K ρ`, and `c ≤ K` is what keeps the first
term under `K ρ`. -/
theorem norm_perp_sub_center_le_of_pinned_dilate_of_one_lt {ρ δ : NNReal} (Tρ : Tube ρ E)
    (Tb : Tube δ E) {c K : ℝ} (hc : 1 ≤ c) (hcK : c ≤ K) (hδ : (δ : ℝ) ≤ K * (ρ : ℝ))
    {p : E} (hpρ : p ∈ (Tube.dilate Tρ c).carrier) (hpb : p ∈ (Tube.dilate Tb 2).carrier)
    (hlarge : 1 < 15 * K * (ρ : ℝ)) {x : E} (hx : x ∈ Tb.carrier) :
    ‖(x - Tρ.center) - inner ℝ Tρ.direction (x - Tρ.center) • Tρ.direction‖
      ≤ 59 / 2 * K * (ρ : ℝ) := by
  let e : E := Tρ.direction
  let m : E := Tρ.center
  have hρ0 : 0 ≤ (ρ : ℝ) := NNReal.coe_nonneg ρ
  -- `x` lies in the `1`-dilate of `Tb`, pinned with `p` in its `2`-dilate
  have hxp : ‖x - p‖ ≤ 3 / 2 + 6 * (K * (ρ : ℝ)) := by
    have hx1 : x ∈ (Tube.dilate Tb 1).carrier := Tube.subset_dilate Tb (by norm_num) hx
    have hd : dist x p ≤ 3 / 2 + 6 * (δ : ℝ) := by
      have hd0 := Tube.dist_le_of_mem_dilate_of_mem_dilate (T := Tb) (c := 1) (c' := 2)
        (by norm_num) (by norm_num) hx1 hpb
      norm_num at hd0
      exact hd0
    have hdx : ‖x - p‖ ≤ 3 / 2 + 6 * (δ : ℝ) := by
      simpa [dist_eq_norm] using hd
    linarith [hδ]
  -- `p` is within `c · ρ` of `m` in the transverse directions (the dilated bound at ratio `c`)
  have hperp_p : ‖(p - m) - inner ℝ e (p - m) • e‖ ≤ c * (ρ : ℝ) := by
    have hz := (Tube.abs_inner_and_perp_le_of_mem_dilate Tρ (c := c)
      (lt_of_lt_of_le zero_lt_one hc) hpρ).2
    simpa [e, m] using hz
  -- the perpendicular part is linear
  have hid : (x - m) - inner ℝ e (x - m) • e
      = ((p - m) - inner ℝ e (p - m) • e) + ((x - p) - inner ℝ e (x - p) • e) := by
    rw [show x - m = (p - m) + (x - p) by abel]
    rw [inner_add_right, add_smul]
    module
  have hperp_x : ‖(x - m) - inner ℝ e (x - m) • e‖
      ≤ c * (ρ : ℝ) + 3 / 2 + 6 * (K * (ρ : ℝ)) := by
    calc
      ‖(x - m) - inner ℝ e (x - m) • e‖
          ≤ ‖(p - m) - inner ℝ e (p - m) • e‖ + ‖(x - p) - inner ℝ e (x - p) • e‖ := by
            rw [hid]
            exact norm_add_le _ _
      _ ≤ c * (ρ : ℝ) + ‖x - p‖ := by
            exact add_le_add hperp_p (by simpa [e] using Tube.norm_perp_le Tρ (x - p))
      _ ≤ c * (ρ : ℝ) + 3 / 2 + 6 * (K * (ρ : ℝ)) := by
            linarith [hxp]
  -- numerical bookkeeping: `c·ρ ≤ K·ρ` and `3/2 ≤ 45/2 · K·ρ` (the latter from `hlarge`)
  have hcρK : c * (ρ : ℝ) ≤ K * (ρ : ℝ) := mul_le_mul_of_nonneg_right hcK hρ0
  have hle2 : (3 / 2 : ℝ) ≤ 45 / 2 * (K * (ρ : ℝ)) := by
    have hl1 := mul_le_mul_of_nonneg_left (le_of_lt hlarge) (by norm_num : (0 : ℝ) ≤ 3 / 2)
    nlinarith
  calc
    ‖(x - Tρ.center) - inner ℝ Tρ.direction (x - Tρ.center) • Tρ.direction‖
        = ‖(x - m) - inner ℝ e (x - m) • e‖ := by simp [e, m]
    _ ≤ c * (ρ : ℝ) + 3 / 2 + 6 * (K * (ρ : ℝ)) := hperp_x
    _ ≤ 59 / 2 * K * (ρ : ℝ) := by nlinarith [hcρK, hle2]

/-- **Transverse confinement against a dilated parent** (blueprint
`lem:thinTubeInFatDilateTransverse`, read at a dilate): the two branches of the split on
`15 K ρ ≤ 1`, both landing on `29.5 K ρ ≤ 32 K ρ`.

This is `Kakeya.Tube.norm_perp_sub_center_le_of_pinned` (`Kakeya/Tube/Dilate.lean:1011`) with
`hpρ` read at `c · Tρ`, and it is what fixes `32 K` as the ratio in
`Kakeya.ml1Boot.subset_dilate_of_norm_perp_direction_le_dilate`. -/
theorem norm_perp_sub_center_le_of_pinned_dilate {ρ δ : NNReal} (Tρ : Tube ρ E) (Tb : Tube δ E)
    {c K : ℝ} (hc : 1 ≤ c) (hcK : c ≤ K) (hδ : (δ : ℝ) ≤ K * (ρ : ℝ))
    {p : E} (hpρ : p ∈ (Tube.dilate Tρ c).carrier) (hpb : p ∈ (Tube.dilate Tb 2).carrier)
    (hS : ‖Tb.direction - inner ℝ Tρ.direction Tb.direction • Tρ.direction‖
      ≤ 15 * K * (ρ : ℝ))
    {x : E} (hx : x ∈ Tb.carrier) :
    ‖(x - Tρ.center) - inner ℝ Tρ.direction (x - Tρ.center) • Tρ.direction‖
      ≤ 32 * K * (ρ : ℝ) := by
  have hK : (1 : ℝ) ≤ K := le_trans hc hcK
  have hKρ : 0 ≤ K * (ρ : ℝ) := mul_nonneg (le_trans zero_le_one hK) (NNReal.coe_nonneg ρ)
  have hhalf : 59 / 2 * K * (ρ : ℝ) ≤ 32 * K * (ρ : ℝ) := by
    nlinarith [hKρ]
  rcases le_or_gt (15 * K * (ρ : ℝ)) 1 with hsmall | hlarge
  · exact le_trans
      (norm_perp_sub_center_le_of_pinned_dilate_of_le_one Tρ Tb hc hcK hδ hpρ hpb hS hsmall hx)
      hhalf
  · exact le_trans
      (norm_perp_sub_center_le_of_pinned_dilate_of_one_lt Tρ Tb hc hcK hδ hpρ hpb hlarge hx)
      hhalf

/-- **A thin tube pinned to a dilated fat one lies in a bounded dilate of it** (blueprint
`lem:thinTubeInFatDilate`, read at a dilate).

If `Tb` has thickness at most `K ρ`, meets the `c`-dilate of the `ρ`-tube `Tρ` in a point `p`
that also lies in `2 · Tb`, and its direction is transverse to that of `Tρ` by at most
`15 K ρ`, then `Tb ⊆ 32 K · Tρ` — the *same* ratio as
`Kakeya.Tube.subset_dilate_of_norm_perp_direction_le` (`Kakeya/Tube/Dilate.lean:1038`), the
cost of the dilated pinning being charged to `K` through `hcK : c ≤ K` rather than to the
conclusion.

That is the whole point of the shape: at the one call site
`Kakeya.ml1Boot.plankTube_subset_parent_dilate_dilate` the value is `K = c C_𝕎`, so
`32 K = c · 32 C_𝕎 = c · C_{plankTubeInParent}` and the dilation ratio of the parent family is
paid exactly once, linearly.  Both hypotheses that mention `ρ` and the conclusion's transverse
extent `32 K ρ` carry the same single power of `ρ`, which is what makes the linear charge the
correct placement rather than merely a large enough one.  At `c = 1` this is that lemma, with
`hcρ` its `hρ1` and `hcK` its `hK`. -/
theorem subset_dilate_of_norm_perp_direction_le_dilate {ρ δ : NNReal} (Tρ : Tube ρ E)
    (Tb : Tube δ E) {c K : ℝ} (hc : 1 ≤ c) (hcK : c ≤ K) (hcρ : c * (ρ : ℝ) ≤ 1)
    (hδ : (δ : ℝ) ≤ K * (ρ : ℝ))
    {p : E} (hpρ : p ∈ (Tube.dilate Tρ c).carrier) (hpb : p ∈ (Tube.dilate Tb 2).carrier)
    (hS : ‖Tb.direction - inner ℝ Tρ.direction Tb.direction • Tρ.direction‖
      ≤ 15 * K * (ρ : ℝ)) :
    Tb.carrier ⊆ (Tube.dilate Tρ (32 * K)).carrier := by
  intro x hx
  let s : ℝ := inner ℝ Tρ.direction (x - Tρ.center)
  have hK : (1 : ℝ) ≤ K := le_trans hc hcK
  have hC : 0 < 32 * K := by linarith
  have hs : |s| ≤ (32 * K) / 2 := by
    have h := abs_inner_sub_center_le_of_pinned_dilate Tρ Tb hc hcK hcρ hδ hpρ hpb hx
    dsimp [s] at h ⊢
    nlinarith
  have hz : dist x (Tρ.center + s • Tρ.direction) ≤ 32 * K * (ρ : ℝ) := by
    have h := norm_perp_sub_center_le_of_pinned_dilate Tρ Tb hc hcK hδ hpρ hpb hS hx
    rw [dist_eq_norm, sub_add_eq_sub_sub]
    dsimp [s] at h ⊢
    exact h
  exact Tube.mem_dilate_of_dist_axis_le Tρ hC hs hz

/-- **The tube attached to a plank lies in a dilate of a *dilated* parent `ρ`-tube** (blueprint
`lem:ml1bootPlankTubeInParentDilate`, read at a dilated parent).

This is `Kakeya.ml1Boot.plankTube_subset_parent_dilate` with the plank containment weakened from
`W ≤ T_ρ` to `W ≤ c · T_ρ`, which is what a parent family merged by
`Kakeya.ml1Boot.exists_merged_rhoParentFamily` supplies, and with `hbρ : bp ≤ ρ` — which the
dilated plank pigeonhole no longer produces — relaxed to `bp ≤ c ρ`.

**The ratio is `c · C_{plankTubeInParent}`, and it is derived, not guessed.**  Put
`K = c C_𝕎`, so that `32 K = c · 32 C_𝕎 = c · C_{plankTubeInParent}`.  The three hypotheses of
`Kakeya.ml1Boot.subset_dilate_of_norm_perp_direction_le_dilate` are then met at that `K`:

* `c ≤ K` because `C_𝕎 ≥ 1`;
* `C_𝕎 bp ≤ K ρ`, which is `bp ≤ c ρ` multiplied by `C_𝕎`;
* the transverse hypothesis, from `Kakeya.ml1Boot.norm_perp_direction_le_of_chord_dilate` at
  `d = 2/5`: two points of `W` at distance more than `2/5` — supplied by `hlong` through
  `Metric.ethickness_zero_le_ediam`, exactly as in the undilated lemma — give
  `S ≤ (2 c ρ + 4 C_𝕎 bp) / (2/5) = 5 c ρ + 10 C_𝕎 bp ≤ 15 C_𝕎 c ρ = 15 K ρ`,
  the last step using `bp ≤ c ρ` and `C_𝕎 ≥ 1`.

Both sides of every one of these carries a single power of `ρ`, and the conclusion's transverse
extent is `32 K ρ = c · 32 C_𝕎 ρ`; so the factor `c` sits on the ratio and not, say, on a
`ρ²` term that a larger constant would also have absorbed.  At `c = 1` the statement is
`Kakeya.ml1Boot.plankTube_subset_parent_dilate` verbatim.

As in that lemma, `_hdim`, `_hδt`, `_hδa`, `_hab` and `_hdims` are carried for signature parity with
its call sites and are not consumed: the plank enters only through `hlong`, `hWsub` and
`hTb`. -/
theorem plankTube_subset_parent_dilate_dilate [Nontrivial E] (_hdim : Module.finrank ℝ E = 3)
    {δt ap bp ρ : NNReal} {c : ℝ} (hc : 1 ≤ c)
    (_hδt : 0 < δt) (_hδa : δt ≤ ap) (_hab : ap ≤ bp)
    (hbρ : (bp : ℝ) ≤ c * (ρ : ℝ)) (hρ1 : c * (ρ : ℝ) ≤ 1)
    (Tρ : Tube ρ E) (W : ConvexSpaceBody E)
    (_hdims : IsPlankOfDimensions plankPigeonhole.C ap bp W)
    (hWsub : W ≤ Tube.dilate Tρ c)
    (hlong : 2⁻¹ ≤ Metric.ethickness ℝ W.carrier 0)
    (Tb : Tube (plankPigeonhole.C * bp) E) (hTb : W ≤ Tube.dilate Tb 2) :
    Tb.toConvexSpaceBody ≤ Tube.dilate Tρ (c * (plankTubeInParent.C : ℝ)) := by
  classical
  set Cw : ℝ := (plankPigeonhole.C : ℝ)
  set r : ℝ := (ρ : ℝ)
  set b : ℝ := (bp : ℝ)
  set K : ℝ := c * Cw
  have hCw1 : 1 ≤ Cw := by
    dsimp [Cw, plankPigeonhole.C, Metric.volume_comparison.C, Metric.lt_volume_convexHull.c]
    norm_num
  have hCw0 : 0 ≤ Cw := by linarith
  have hr0 : 0 ≤ r := by simp [r]
  have hb0 : 0 ≤ b := by simp [b]
  have hcρ : c * r ≤ 1 := by
    simpa [r] using hρ1
  have hbc : b ≤ c * r := by
    simpa [b, r] using hbρ
  have hδc : ((plankPigeonhole.C * bp : NNReal) : ℝ) = Cw * b := by
    rw [NNReal.coe_mul]
  have hcK : c ≤ K := by
    dsimp [K]
    calc
      c = 1 * c := by ring
      _ ≤ Cw * c := mul_le_mul_of_nonneg_right hCw1 (le_trans zero_le_one hc)
      _ = c * Cw := by ring
  have hδle : ((plankPigeonhole.C * bp : NNReal) : ℝ) ≤ K * r := by
    rw [hδc]
    dsimp [K]
    calc
      Cw * b ≤ Cw * (c * r) := mul_le_mul_of_nonneg_left hbc hCw0
      _ = (c * Cw) * r := by ring
  -- Two points of W at distance > 2/5, via the diameter route
  have hfar : ∃ p ∈ W.carrier, ∃ q ∈ W.carrier, (2 / 5 : ℝ) < dist p q := by
    by_contra h
    push Not at h
    have hle : Metric.ediam W.carrier ≤ ENNReal.ofReal (2 / 5 : ℝ) := by
      apply Metric.ediam_le
      intro x hx y hy
      rw [edist_dist]
      exact ENNReal.ofReal_le_ofReal (h x hx y hy)
    have hlt : ENNReal.ofReal (2 / 5 : ℝ) < (2 : ENNReal)⁻¹ := by
      have htwo : (2 : ENNReal) = ENNReal.ofReal (2 : ℝ) := by norm_num
      rw [htwo, ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)).2 (by norm_num)
    have hchain : (2 : ENNReal)⁻¹ ≤ ENNReal.ofReal (2 / 5 : ℝ) :=
      le_trans (le_trans hlong (Metric.ethickness_zero_le_ediam (𝕜 := ℝ) W.carrier)) hle
    exact (not_le_of_gt hlt) hchain
  rcases hfar with ⟨p, hpW, q, hqW, hpq⟩
  have hpρ : p ∈ (Tube.dilate Tρ c).carrier := by
    change p ∈ (Tube.dilate Tρ c : Set E)
    exact (SetLike.le_def.mp hWsub) hpW
  have hqρ : q ∈ (Tube.dilate Tρ c).carrier := by
    change q ∈ (Tube.dilate Tρ c : Set E)
    exact (SetLike.le_def.mp hWsub) hqW
  have hpTb : p ∈ (Tube.dilate Tb 2).carrier := by
    change p ∈ (Tube.dilate Tb 2 : Set E)
    exact (SetLike.le_def.mp hTb) hpW
  have hqTb : q ∈ (Tube.dilate Tb 2).carrier := by
    change q ∈ (Tube.dilate Tb 2 : Set E)
    exact (SetLike.le_def.mp hTb) hqW
  -- the transverse bound through the chord p q
  have hS : ‖Tb.direction - inner ℝ Tρ.direction Tb.direction • Tρ.direction‖ ≤ 15 * K * r := by
    have hchord := norm_perp_direction_le_of_chord_dilate Tρ Tb (c := c)
      (hc := lt_of_lt_of_le zero_lt_one hc) (d := (2 / 5 : ℝ))
      (by norm_num) (le_of_lt hpq) hpρ hqρ hpTb hqTb
    calc
      ‖Tb.direction - inner ℝ Tρ.direction Tb.direction • Tρ.direction‖
          ≤ (2 * c * (ρ : ℝ) + 4 * ((plankPigeonhole.C * bp : NNReal) : ℝ)) / (2 / 5) := hchord
      _ = 5 * c * r + 10 * (Cw * b) := by
        rw [hδc]
        field_simp
        ring
      _ ≤ 15 * Cw * c * r := by
        nlinarith [hCw1, hCw0, hb0, hr0, hc, hbc,
          mul_nonneg (le_trans zero_le_one hc) hr0]
      _ = 15 * K * r := by
        dsimp [K]
        ring
  -- the dilution ratio `plankTubeInParent.C = 32 * Cw`
  have hcc : (plankTubeInParent.C : ℝ) = 32 * Cw := by
    rfl
  have hratio : c * (plankTubeInParent.C : ℝ) = 32 * K := by
    dsimp [K]
    change c * (32 * Cw) = 32 * (c * Cw)
    ring
  have hsub : Tb.carrier ⊆ (Tube.dilate Tρ (32 * K)).carrier :=
    subset_dilate_of_norm_perp_direction_le_dilate Tρ Tb (c := c) (K := K)
      hc hcK hcρ hδle hpρ hpTb hS
  rw [hratio]
  apply SetLike.le_def.mpr
  exact hsub

/-- **A test body absorbing the `2`-dilates of all the tubes it contains** (blueprint
`lem:ml1bootDilateTestBody`).

For every convex body `K ⊆ ℝ³` there is a convex body `K*` with `K ⊆ K*` and
`|K*| ≤ C_*(3) |K|`, where `C_*(3) = Kakeya.ml1Boot.dilateTestBody.C`, such that
`2 · T ⊆ K*` for **every** tube `T`, of any scale, with `T ⊆ K`.  One may take

`K* = 3 · P` with `P = outerPrism K` (`Kakeya.ml1Boot.dilateTestBody`),

the homothety of ratio `3` of the outer prism of `K` about its own centre.  In particular `K*`
is itself a rectangular prism, hence a convex body, and no Minkowski arithmetic of convex
bodies is needed in order to name it.

The three moves are `Kakeya.ml1Boot.subset_dilateTestBody`,
`Kakeya.ml1Boot.dilate_tube_subset_dilateTestBody` and
`Kakeya.ml1Boot.volume_dilateTestBody_le`, all in
`Kakeya/DimensionThree/MainLemma1/TestBody.lean`.  The earlier witness was `K* = 2 K - K`,
which forced the Rogers–Shephard inequality in `ℝ³` (blueprint
`prop:ml1bootDifferenceBodyVolume`, now retired); the assertion is word for word the one made
then, so no consumer needs editing.

This is what converts a Frostman/density test against `K` into one against the dilated tubes
of `Kakeya.ml1Boot.exists_plankTube_family`, whose containments are only up to a `2`-dilate. -/
theorem exists_dilate_testBody [Nontrivial E] (hdim : Module.finrank ℝ E = 3)
    (K : ConvexSpaceBody E) :
    ∃ Ks : ConvexSpaceBody E, K ≤ Ks ∧
      volume Ks.carrier ≤ (dilateTestBody.C : ENNReal) * volume K.carrier ∧
      ∀ {s : NNReal} (T : Tube s E), T.toConvexSpaceBody ≤ K → Tube.dilate T 2 ≤ Ks := by
  refine ⟨(dilateTestBody hdim K).toConvexSpaceBody, ?_, ?_, ?_⟩
  · exact le_trans (subset_dilateTestBody hdim K).1 (subset_dilateTestBody hdim K).2
  · calc
      volume (dilateTestBody hdim K).toConvexSpaceBody.carrier
          = volume (dilateTestBody hdim K).carrier := rfl
      _ ≤ 3 ^ 3 * (Metric.volume_outerPrism_le_volume_self.C 3 : ENNReal) * volume K.carrier := by
        exact (volume_dilateTestBody_le hdim K).2
      _ = (dilateTestBody.C : ENNReal) * volume K.carrier := by
        rfl
  · intro s T hT
    exact dilate_tube_subset_dilateTestBody hdim K T hT

/-- **The volume of the `2`-dilate of the tube attached to a plank** (blueprint
`lem:ml1bootPlankTubeVolumeCompare`).

Write `C_P = Kakeya.ml1Boot.plankInTube.C` and `C_𝕎 = Kakeya.ml1Boot.plankPigeonhole.C`.
For a plank `W` of dimensions `ap × bp × 1` with `ethickness … 0 ≤ 1`, and the tube `T̃` of
scale `C_𝕎 bp` attached to it,

`|T̃| ≤ |2 · T̃| ≤ C_P (bp / ap) |W|`.

The first inequality is monotonicity of volume (a tube is contained in its own `2`-dilate,
its centre being a point of it); the second is
`Kakeya.ml1Boot.volume_bounds_of_tube_dilate` and
`Kakeya.ml1Boot.volume_bounds_of_isPlankOfDimensions` combined by
`Kakeya.ml1Boot.plank_dilate_volume_ratio`.

The constant is `C_P`, the honest ratio available from the API being
`320 C_𝕎 ^ 6 / c₃ = 5 C_𝕎 ^ 6 V` with `V = Metric.volume_comparison.C 3` and
`c₃ = Metric.lt_volume_convexHull.c 3` (`Kakeya.ml1Boot.plankInTube_constant_bounds`).  The
earlier candidate `C_T C_𝕎` with the retired value of `C_T` was smaller by a factor
`1280 V ≥ 8 · 10 ^ 4`; that failure mode is blueprint
`note:ml1bootDensityTransferConstantTooSmall`, and it is why
`Kakeya.ml1Boot.densityTransfer.C` is now `C_P` itself. -/
theorem volume_plankTube_le [Nontrivial E] (hdim : Module.finrank ℝ E = 3)
    {ap bp : NNReal} (hap0 : 0 < ap) (hab : ap ≤ bp) (hb1 : bp ≤ 1)
    (W : ConvexSpaceBody E) (hdims : IsPlankOfDimensions plankPigeonhole.C ap bp W)
    (_hlong : Metric.ethickness ℝ W.carrier 0 ≤ 1)
    (Tb : Tube (plankPigeonhole.C * bp) E) (_hTb : W ≤ Tb.toConvexSpaceBody) :
    volume Tb.carrier ≤ volume (Tube.dilate Tb 2).carrier ∧
      volume (Tube.dilate Tb 2).carrier
        ≤ (plankInTube.C : ENNReal)
          * ((bp : ENNReal) / (ap : ENNReal)) * volume W.carrier := by
  classical
  have hc_pos : 0 < Metric.lt_volume_convexHull.c 3 := Metric.lt_volume_convexHull.c_pos 3
  have hc_ne : Metric.lt_volume_convexHull.c 3 ≠ 0 := hc_pos.ne'
  have hCw : 1 ≤ plankPigeonhole.C := by
    dsimp [plankPigeonhole.C, Metric.volume_comparison.C, Metric.lt_volume_convexHull.c]
    norm_num
  have hCw0 : 0 < plankPigeonhole.C := lt_of_lt_of_le zero_lt_one hCw
  have hb0 : 0 < bp := lt_of_lt_of_le hap0 hab
  -- the two volume bounds of W
  have hvolW := volume_bounds_of_isPlankOfDimensions hdim hCw hdims
  -- the two volume bounds of the 2-dilate of the tube
  have hs0 : 0 < plankPigeonhole.C * bp := by positivity
  have hs : plankPigeonhole.C * bp ≤ 2 * plankPigeonhole.C := by
    calc
      plankPigeonhole.C * bp ≤ plankPigeonhole.C * 1 :=
        mul_le_mul_of_nonneg_left (by exact_mod_cast hb1) hCw0.le
      _ = plankPigeonhole.C := by rw [mul_one]
      _ ≤ 2 * plankPigeonhole.C := by
        calc
          plankPigeonhole.C = 1 * plankPigeonhole.C := by rw [one_mul]
          _ ≤ 2 * plankPigeonhole.C :=
            mul_le_mul_of_nonneg_right (by norm_num : (1 : NNReal) ≤ 2) hCw0.le
  have hvolT := volume_bounds_of_tube_dilate hdim hCw hs0 hs Tb
  have hsq : ((plankPigeonhole.C * bp : NNReal) : ENNReal) ^ 2
      = (plankPigeonhole.C : ENNReal) ^ 2 * (bp : ENNReal) ^ 2 := by
    rw [ENNReal.coe_mul]
    ring
  have hVlo : 4 * (Metric.lt_volume_convexHull.c 3 : ENNReal) * (plankPigeonhole.C : ENNReal) ^ 2
      * (bp : ENNReal) ^ 2 ≤ volume (Tube.dilate Tb 2).carrier := by
    calc
      4 * (Metric.lt_volume_convexHull.c 3 : ENNReal) * (plankPigeonhole.C : ENNReal) ^ 2
            * (bp : ENNReal) ^ 2
          = 4 * (Metric.lt_volume_convexHull.c 3 : ENNReal)
              * ((plankPigeonhole.C * bp : NNReal) : ENNReal) ^ 2 := by
            rw [hsq]
            ring
      _ ≤ volume (Tube.dilate Tb 2).carrier := hvolT.1
  have hVhi : volume (Tube.dilate Tb 2).carrier ≤ 320 * (plankPigeonhole.C : ENNReal) ^ 3
      * (bp : ENNReal) ^ 2 := by
    calc
      volume (Tube.dilate Tb 2).carrier
          ≤ 320 * (plankPigeonhole.C : ENNReal)
              * ((plankPigeonhole.C * bp : NNReal) : ENNReal) ^ 2 := hvolT.2
      _ = 320 * (plankPigeonhole.C : ENNReal) ^ 3 * (bp : ENNReal) ^ 2 := by
        rw [hsq]
        ring
  -- the constant requirements 2 Cw / c₃ ≤ C and 320 Cw⁶ / c₃ ≤ C (C = plankInTube.C)
  have hC : 1 ≤ plankInTube.C := by
    dsimp [plankInTube.C]
    have hp : (1 : NNReal) ≤ plankPigeonhole.C ^ 6 :=
      le_trans hCw (by simpa using pow_le_pow_right₀ hCw (by norm_num : 1 ≤ 6))
    have hv : (1 : NNReal) ≤ Metric.volume_comparison.C 3 := by
      dsimp [Metric.volume_comparison.C, Metric.lt_volume_convexHull.c]
      norm_num
    calc
      (1 : NNReal) ≤ 256 := by norm_num
      _ ≤ 256 * (plankPigeonhole.C ^ 6 * Metric.volume_comparison.C 3) := by
        exact le_mul_of_one_le_right (by norm_num) (one_le_mul hp hv)
      _ = 256 * plankPigeonhole.C ^ 6 * Metric.volume_comparison.C 3 := by ring
  obtain ⟨hC₂, hC₁⟩ := plankInTube_constant_bounds (C := plankPigeonhole.C) hCw
  -- feed the four volume bounds and the two constant requirements into the ratio lemma
  have hratio := plank_dilate_volume_ratio
    (Cw := plankPigeonhole.C) (C := plankInTube.C) (a := ap) (b := bp)
    (w := volume W.carrier) (V := volume (Tube.dilate Tb 2).carrier)
    hCw hC hap0 hab hvolW.1 hvolW.2 hVlo hVhi hC₁ hC₂
  -- first inequality: |Tb| ≤ |2 · Tb|
  have hle1 : volume Tb.carrier ≤ volume (Tube.dilate Tb 2).carrier := by
    have htd := Tube.tubeDilateVolume Tb (show (1 : ℝ) < 2 by norm_num)
    have hconv : ENNReal.ofReal (Tube.tubeDilateVolume.C' (Module.finrank ℝ E) 2)
        = (8 : ENNReal) := by
      rw [hdim]
      norm_num [Tube.tubeDilateVolume.C']
    calc
      volume Tb.carrier ≤ 8 * volume Tb.carrier := by
        simpa using mul_le_mul_of_nonneg_right (by norm_num : (1 : ENNReal) ≤ 8)
          (by positivity : (0 : ENNReal) ≤ volume Tb.carrier)
      _ = volume (Tube.dilate Tb 2).carrier := by
        rw [← hconv, ← htd]
  exact ⟨hle1, hratio.2⟩

/-- **The planks of a fibre are distinct members of `𝕎_m`** (blueprint
`lem:ml1bootPlankSumOverFibre`).

Let `L` be a finite set of block indices `(m, t)` all with the *same* first entry `m`, whose
second entries are parts of `𝒫_m`, and let `K*` be a convex body containing the plank
`W t` of every `(m, t) ∈ L`.  Then

`∑_{(m,t) ∈ L} |W t| ≤ Δ(𝕎_m, K*) |K*|`.

The map `(m, t) ↦ t` is injective on `L`, the first entries all agreeing, so the sum is a sum
over a subset of `𝕎_m[K*]` (blueprint `def:WW`), which by `Kakeya.densityIn` is at most
`Δ(𝕎_m, K*) |K*|`. -/
theorem sum_volume_plank_le_densityIn {ι κ : Type*}
    {m : κ} {L : Finset (κ × Finset ι)} (hL : ∀ j ∈ L, j.1 = m)
    {P : Finset (Finset ι)} (hP : ∀ j ∈ L, j.2 ∈ P)
    (W : Finset ι → ConvexSpaceBody E) (Ks : ConvexSpaceBody E)
    (hsub : ∀ j ∈ L, W j.2 ≤ Ks) :
    ∑ j ∈ L, volume (W j.2).carrier ≤ densityIn P W Ks * volume Ks.carrier := by
  classical
  have hinj : Set.InjOn (fun j : κ × Finset ι => j.2) (↑L : Set (κ × Finset ι)) := by
    intro j hj j' hj' hjj
    apply Prod.ext
    · calc j.1 = m := hL j hj
        _ = j'.1 := (hL j' hj').symm
    · simpa using hjj
  rw [← Finset.sum_image (s := L) (g := fun j : κ × Finset ι => j.2)
      (f := fun x : Finset ι => volume (W x).carrier) hinj]
  rw [← Kakeya.sum_volume_eq_densityIn_mul_volume P W Ks]
  apply Finset.sum_le_sum_of_subset
  intro i hi
  rcases Finset.mem_image.mp hi with ⟨j, hj, rfl⟩
  simp only [Finset.mem_filter]
  exact ⟨hP j hj, hsub j hj⟩

/-- **The density of the `b`-tubes over a single `ρ`-tube, inside a fixed test body**
(blueprint `lem:ml1bootFibreCoarseDensityIn`).

Write `C_P = Kakeya.ml1Boot.plankInTube.C` and `C_* = Kakeya.ml1Boot.dilateTestBody.C`.  In
the situation of `Kakeya.ml1Boot.maxDensity_fibre_le`, the density of the fibre `ϖ⁻¹(m)`
inside an *arbitrary* convex body `K` is bounded by `C_* · 2 C_P (bp / ap)`.

The bound is uniform in `K`, which is what makes `Kakeya.ml1Boot.maxDensity_fibre_le` a
one-line passage to the supremum through `Kakeya.le_maxDensity`.

*The `b`-tubes must be indexed by the block indices* `(m, t) ∈ 𝓘`, with `ϖ` the first
projection, and not by an abstract type with the block supplied existentially: the assignment
`j ↦ j.2` sending a `b`-tube to the block whose plank its `2`-dilate contains has to be
injective on the fibre, which is exactly what `Kakeya.ml1Boot.sum_volume_plank_le_densityIn`
consumes.  `Kakeya.densityIn` sums over the *index* set, so without injectivity `N` indices
carrying one and the same tube multiply the left-hand side by `N` while the right-hand side is
a fixed constant, and the statement is false.  See blueprint
`note:ml1bootFibreCoarseDensityInInjectivity` for the counterexample; note that requiring
`j ↦ Tb j` to be injective does *not* repair it.  This is the shape
`Kakeya.ml1Boot.exists_plankTube_family` produces. -/
theorem densityIn_fibre_le [Nontrivial E] (hdim : Module.finrank ℝ E = 3)
    {δt ap bp bq ρ : NNReal} (hδt : 0 < δt) (hδa : δt ≤ ap) (hab : ap ≤ bp) (hb1 : bp ≤ 1)
    (hbbq : bp ≤ bq) (hbq : bq ≤ plankPigeonhole.C * bp)
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    {u'' : Finset ι} {tρ : Finset κ} {tb : Finset (κ × Finset ι)}
    (T : ι → Tube δt E) (Tρ : κ → Tube ρ E) (pρ : ι → κ)
    (Tb : κ × Finset ι → Tube bq E)
    (F : (m : κ) → ConvexSpaceBody.Factorization (fibre u'' pρ m)
      (fun i => (T i).toConvexSpaceBody) 2)
    (hdims : ∀ m ∈ tρ, IsPlankFamilyOfDimensions plankPigeonhole.C ap bp (F m).parts
      (fun part => part.convexHull_biUnion (fun i => (T i).toConvexSpaceBody)))
    {m : κ} (hm : m ∈ tρ) {cpar : ℝ}
    (hcover : ∀ j ∈ fibre tb Prod.fst m, j.2 ∈ (F m).parts ∧
      (j.2.convexHull_biUnion fun i => (T i).toConvexSpaceBody) ≤ Tube.dilate (Tb j) 2 ∧
        (Tb j).toConvexSpaceBody ≤ Tube.dilate (Tρ m) cpar)
    (K : ConvexSpaceBody E) :
    densityIn (fibre tb Prod.fst m) (fun j => (Tb j).toConvexSpaceBody) K
      ≤ (dilateTestBody.C : ENNReal) * 2 * (plankInTube.C : ENNReal)
        * ((bp : ENNReal) / (ap : ENNReal)) := by
  classical
  -- 1. reduce to a sum inequality (division-free form)
  rw [densityIn_le_iff (fibre tb Prod.fst m) (fun j => (Tb j).toConvexSpaceBody) K
    ((dilateTestBody.C : ENNReal) * 2 * (plankInTube.C : ENNReal)
      * ((bp : ENNReal) / (ap : ENNReal)))]
  -- 2. the dilated test body Ks ⊇ K absorbing the 2-dilates
  obtain ⟨Ks, hKs_le, hKs_vol, hKs_dil⟩ := exists_dilate_testBody hdim K
  -- 3. bookkeeping for the surviving tubes and the planks they contain
  set s0 := fibre tb Prod.fst m
  set surv := s0.filter fun j => (Tb j).toConvexSpaceBody ≤ K
  let plankf : Finset ι → ConvexSpaceBody E := fun part =>
    part.convexHull_biUnion (fun i => (T i).toConvexSpaceBody)
  have hsurv_sub : surv ⊆ s0 := Finset.filter_subset _ _
  have hsurv_mem : ∀ j ∈ surv, j ∈ s0 := fun j hj => hsurv_sub hj
  have hsurv_K : ∀ j ∈ surv, (Tb j).toConvexSpaceBody ≤ K := fun j hj =>
    (Finset.mem_filter.mp hj).2
  have hpart_mem : ∀ j ∈ surv, j.2 ∈ (F m).parts := by
    intro j hj
    exact (hcover j (hsurv_mem j hj)).1
  have hpart_le : ∀ j ∈ surv, plankf j.2 ≤ Tube.dilate (Tb j) 2 := by
    intro j hj
    exact (hcover j (hsurv_mem j hj)).2.1
  -- every surviving tube's 2-dilate lies in Ks, so each plank's body lies in Ks
  have hplank_Ks : ∀ j ∈ surv, plankf j.2 ≤ Ks := by
    intro j hj
    exact le_trans (hpart_le j hj) (hKs_dil (Tb j) (hsurv_K j hj))
  have hap0 : 0 < ap := lt_of_lt_of_le hδt hδa
  -- 4. per surviving tube bound at the honest `bq` scale (so `volume_plankTube_le`, whose tube
  --    has scale `plankPigeonhole.C * bp`, does not apply):
  --    `|2·Tb j| ≤ C_P (bp/ap) |plank(j.2)|`
  have hbq_vol : ∀ {W : ConvexSpaceBody E},
      IsPlankOfDimensions plankPigeonhole.C ap bp W → ∀ Tb : Tube bq E,
        volume (Tube.dilate Tb 2).carrier
          ≤ (plankInTube.C : ENNReal) * ((bp : ENNReal) / (ap : ENNReal)) * volume W.carrier := by
    intro W hdimsW Tb
    have hc₃pos : 0 < Metric.lt_volume_convexHull.c 3 := Metric.lt_volume_convexHull.c_pos 3
    have hc₃_ne : Metric.lt_volume_convexHull.c 3 ≠ 0 := hc₃pos.ne'
    have hCw : 1 ≤ plankPigeonhole.C := by
      dsimp [plankPigeonhole.C, Metric.volume_comparison.C, Metric.lt_volume_convexHull.c]
      norm_num
    have hCw0 : 0 < plankPigeonhole.C := lt_of_lt_of_le zero_lt_one hCw
    have hb0 : 0 < bp := lt_of_lt_of_le hap0 hab
    have hbq0 : 0 < bq := lt_of_lt_of_le hb0 hbbq
    set CwE : ENNReal := (plankPigeonhole.C : ENNReal) with hCwEdef
    set CE : ENNReal := (plankInTube.C : ENNReal) with hCEdef
    set bE : ENNReal := (bp : ENNReal) with hbEdef
    set aE : ENNReal := (ap : ENNReal) with haEdef
    set c₃ : ENNReal := (Metric.lt_volume_convexHull.c 3 : ENNReal) with hc₃def
    have hCwE0 : CwE ≠ 0 := by
      change (plankPigeonhole.C : ENNReal) ≠ 0
      exact ENNReal.coe_ne_zero.mpr hCw0.ne'
    have hCwEtop : CwE ≠ ⊤ := ENNReal.coe_ne_top
    have hCwE3n0 : CwE ^ 3 ≠ 0 := pow_ne_zero 3 hCwE0
    have hCwE3top : CwE ^ 3 ≠ ⊤ := by
      rw [show CwE ^ 3 = CwE * CwE * CwE by ring]
      exact ENNReal.mul_ne_top (ENNReal.mul_ne_top hCwEtop hCwEtop) hCwEtop
    have hCE0 : CE ≠ 0 := by
      change (plankInTube.C : ENNReal) ≠ 0
      exact ENNReal.coe_ne_zero.mpr
        (lt_of_lt_of_le zero_lt_one (by
          dsimp [plankInTube.C, plankPigeonhole.C, Metric.volume_comparison.C,
            Metric.lt_volume_convexHull.c]
          norm_num)).ne'
    have hCEtop : CE ≠ ⊤ := ENNReal.coe_ne_top
    have hc₃0 : c₃ ≠ 0 := by
      change (Metric.lt_volume_convexHull.c 3 : ENNReal) ≠ 0
      exact_mod_cast hc₃pos.ne'
    have hc₃top : c₃ ≠ ⊤ := ENNReal.coe_ne_top
    have haE0 : aE ≠ 0 := by
      change (ap : ENNReal) ≠ 0
      exact ENNReal.coe_ne_zero.mpr hap0.ne'
    have haEtop : aE ≠ ⊤ := ENNReal.coe_ne_top
    -- the two volume bounds of W
    have hvolW := volume_bounds_of_isPlankOfDimensions hdim hCw hdimsW
    -- the two volume bounds of the 2-dilate of the `bq`-tube
    have hs : bq ≤ 2 * plankPigeonhole.C := by
      calc
        bq ≤ plankPigeonhole.C * bp := hbq
        _ ≤ plankPigeonhole.C * 1 :=
          mul_le_mul_of_nonneg_left (by exact_mod_cast hb1) hCw0.le
        _ = plankPigeonhole.C := by rw [mul_one]
        _ ≤ 2 * plankPigeonhole.C := by
          calc
            plankPigeonhole.C = 1 * plankPigeonhole.C := by rw [one_mul]
            _ ≤ 2 * plankPigeonhole.C :=
              mul_le_mul_of_nonneg_right (by norm_num : (1 : NNReal) ≤ 2) hCw0.le
    have hvolT := volume_bounds_of_tube_dilate hdim hCw hbq0 hs Tb
    -- the constant requirement `320 · Cw⁶ / c₃ ≤ C_P`
    have ⟨hC₂, _hC₁⟩ := plankInTube_constant_bounds (C := plankPigeonhole.C) hCw
    have hcast₂ :
        ((320 * plankPigeonhole.C ^ 6 / Metric.lt_volume_convexHull.c 3 : NNReal) : ENNReal)
        = (320 : ENNReal) * CwE ^ 6 / c₃ := by
      rw [ENNReal.coe_div hc₃_ne]
      rw [ENNReal.coe_mul, ENNReal.coe_pow]
      simp [hCwEdef, hc₃def]
    have hC₂EN : (320 : ENNReal) * CwE ^ 6 / c₃ ≤ CE := by
      change (320 : ENNReal) * (plankPigeonhole.C : ENNReal) ^ 6 /
          (Metric.lt_volume_convexHull.c 3 : ENNReal) ≤ (plankInTube.C : ENNReal)
      rw [← hcast₂]
      exact_mod_cast hC₂
    -- the ratio b/a · a·b = b²
    have hba : (bE / aE) * (aE * bE) = bE ^ 2 := by
      calc
        (bE / aE) * (aE * bE) = ((bE / aE) * aE) * bE := by rw [mul_assoc]
        _ = bE * bE := by rw [ENNReal.div_mul_cancel haE0 haEtop]
        _ = bE ^ 2 := by rw [pow_two]
    -- |2·Tb| ≤ 320 · Cw³ · bp²  (the `bq`-scale upper bound weakened via bq ≤ Cw·bp)
    have hVhi : volume (Tube.dilate Tb 2).carrier ≤ 320 * CwE ^ 3 * bE ^ 2 := by
      have hbq_le : (bq : ENNReal) ≤ CwE * bE := by
        change (bq : ENNReal) ≤ (plankPigeonhole.C : ENNReal) * (bp : ENNReal)
        exact_mod_cast hbq
      calc
        volume (Tube.dilate Tb 2).carrier
            ≤ 320 * (plankPigeonhole.C : ENNReal) * (bq : ENNReal) ^ 2 := hvolT.2
        _ = 320 * CwE * (bq : ENNReal) ^ 2 := by rw [hCwEdef]
        _ ≤ 320 * CwE * (CwE * bE) ^ 2 := by
          gcongr
        _ = 320 * CwE ^ 3 * bE ^ 2 := by ring
    -- the upper-bound half of the ratio lemma, reproduced at the `bq` scale
    have hCm : CwE ^ 6 * (CwE ^ 3)⁻¹ = CwE ^ 3 := by
      calc
        CwE ^ 6 * (CwE ^ 3)⁻¹ = (CwE ^ 3 * CwE ^ 3) * (CwE ^ 3)⁻¹ := by ring
        _ = CwE ^ 3 * (CwE ^ 3 * (CwE ^ 3)⁻¹) := by rw [mul_assoc]
        _ = CwE ^ 3 * 1 := by rw [ENNReal.mul_inv_cancel hCwE3n0 hCwE3top]
        _ = CwE ^ 3 := by rw [mul_one]
    have hD : ((320 * CwE ^ 6) / c₃) * (CwE ^ 3)⁻¹ * c₃ = 320 * CwE ^ 3 := by
      calc
        ((320 * CwE ^ 6) / c₃) * (CwE ^ 3)⁻¹ * c₃
            = 320 * CwE ^ 6 * (CwE ^ 3)⁻¹ * (c₃ * c₃⁻¹) := by
                rw [div_eq_mul_inv]
                ring
        _ = 320 * CwE ^ 6 * (CwE ^ 3)⁻¹ := by
                rw [ENNReal.mul_inv_cancel hc₃0 hc₃top]
                ring
        _ = 320 * CwE ^ 3 := by
                rw [show 320 * CwE ^ 6 * (CwE ^ 3)⁻¹ = 320 * (CwE ^ 6 * (CwE ^ 3)⁻¹) by ring]
                rw [hCm]
    have hUconst : 320 * CwE ^ 3 ≤ CE * (CwE ^ 3)⁻¹ * c₃ := by
      calc
        320 * CwE ^ 3 = ((320 * CwE ^ 6) / c₃) * (CwE ^ 3)⁻¹ * c₃ := by rw [← hD]
        _ ≤ CE * (CwE ^ 3)⁻¹ * c₃ :=
              mul_le_mul_left (mul_le_mul_left hC₂EN (CwE ^ 3)⁻¹) c₃
    calc
      volume (Tube.dilate Tb 2).carrier ≤ 320 * CwE ^ 3 * bE ^ 2 := hVhi
      _ = ((320 * CwE ^ 6) / c₃) * (CwE ^ 3)⁻¹ * c₃ * bE ^ 2 := by rw [← hD]
      _ ≤ (CE * (CwE ^ 3)⁻¹ * c₃) * bE ^ 2 := by
            rw [hD]
            exact mul_le_mul_left hUconst (bE ^ 2)
      _ = CE * (bE / aE) * ((CwE ^ 3)⁻¹ * c₃ * (aE * bE)) := by
            rw [← hba]
            ring
      _ ≤ CE * (bE / aE) * volume W.carrier := by
            exact mul_le_mul_right hvolW.1 (CE * (bE / aE))
  have hperm : ∀ j ∈ surv, volume (Tb j).carrier ≤
      (plankInTube.C : ENNReal) * ((bp : ENNReal) / (ap : ENNReal)) *
        volume (plankf j.2).carrier := by
    intro j hj
    have hle1 : volume (Tb j).carrier ≤ volume (Tube.dilate (Tb j) 2).carrier := by
      have htd := Tube.tubeDilateVolume (Tb j) (show (1 : ℝ) < 2 by norm_num)
      have hconv : ENNReal.ofReal (Tube.tubeDilateVolume.C' (Module.finrank ℝ E) 2)
          = (8 : ENNReal) := by
        rw [hdim]
        norm_num [Tube.tubeDilateVolume.C']
      calc
        volume (Tb j).carrier ≤ 8 * volume (Tb j).carrier := by
          simpa using mul_le_mul_of_nonneg_right (by norm_num : (1 : ENNReal) ≤ 8)
            (by positivity : (0 : ENNReal) ≤ volume (Tb j).carrier)
        _ = volume (Tube.dilate (Tb j) 2).carrier := by
          rw [← hconv, ← htd]
    exact le_trans hle1 (hbq_vol (hdims m hm j.2 (hpart_mem j hj)) (Tb j))
  -- 5. sum the per-tube bounds
  have hsum1 : ∑ j ∈ surv, volume (Tb j).carrier ≤
      (plankInTube.C : ENNReal) * ((bp : ENNReal) / (ap : ENNReal)) *
        ∑ j ∈ surv, volume (plankf j.2).carrier := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hperm
  -- 6. sum the plank volumes over the block indices: `j ↦ j.2` is injective on the fibre
  --    (the first entries all agree), so `sum_volume_plank_le_densityIn` applies with
  --    `L := surv`; then `densityIn (F m).parts plankf Ks ≤ maxDensity (F m).parts plankf ≤ 2`
  --    from the `2`-factorization.
  have hsum_plank : ∑ j ∈ surv, volume (plankf j.2).carrier ≤ 2 * volume Ks.carrier := by
    have hL : ∀ j ∈ surv, j.1 = m := by
      intro j hj
      exact (Finset.mem_filter.mp (hsurv_mem j hj)).2
    have hP : ∀ j ∈ surv, j.2 ∈ (F m).parts := hpart_mem
    have hsub : ∀ j ∈ surv, plankf j.2 ≤ Ks := hplank_Ks
    have hplank_sum := sum_volume_plank_le_densityIn (m := m) (L := surv) hL
      (P := (F m).parts) hP plankf Ks hsub
    have hleMax : densityIn (F m).parts plankf Ks ≤ (2 : ENNReal) := by
      exact le_trans (Kakeya.le_maxDensity (s := (F m).parts) (W := plankf) Ks) (F m).isKatzTao
    calc
      ∑ j ∈ surv, volume (plankf j.2).carrier
          ≤ densityIn (F m).parts plankf Ks * volume Ks.carrier := hplank_sum
      _ ≤ 2 * volume Ks.carrier := by
          gcongr
  -- 7. assemble
  calc
    ∑ j ∈ surv, volume (Tb j).carrier
        ≤ (plankInTube.C : ENNReal) * ((bp : ENNReal) / (ap : ENNReal)) *
            ∑ j ∈ surv, volume (plankf j.2).carrier := hsum1
    _ ≤ (plankInTube.C : ENNReal) * ((bp : ENNReal) / (ap : ENNReal))
          * (2 * volume Ks.carrier) := by
          gcongr
    _ = (plankInTube.C : ENNReal) * ((bp : ENNReal) / (ap : ENNReal)) * 2 * volume Ks.carrier := by
          ring
    _ ≤ (plankInTube.C : ENNReal) * ((bp : ENNReal) / (ap : ENNReal)) * 2 *
          ((dilateTestBody.C : ENNReal) * volume K.carrier) := by
          gcongr
    _ = (dilateTestBody.C : ENNReal) * 2 * (plankInTube.C : ENNReal) *
          ((bp : ENNReal) / (ap : ENNReal)) * volume K.carrier := by
          ring

/-- **The maximal density of the `b`-tubes over a single `ρ`-tube** (blueprint
`lem:ml1bootFibreCoarseDensity`).

Write `C_P = Kakeya.ml1Boot.plankInTube.C` and `C_* = Kakeya.ml1Boot.dilateTestBody.C`.  Fix a
parent index `m` and let the `b`-tubes over it be those `j` in the fibre `ϖ⁻¹(m)`, each
containing one of the planks of `𝕎_m` and contained in `T̃_{ρ,m}`.  Then

`Δ_max(𝕋̃_b[T̃_{ρ,m}]) ≤ C_* · 2 C_P (bp / ap)`.

The factor `Δ_max(𝕎_m) ≤ 2` comes from the factorization; `C_P (bp/ap)` compares each
`b`-tube with the plank inside it (`Kakeya.ml1Boot.volume_plankTube_le`); and `C_*` pays for
the passage from a test body `K` to the body `K*` of
`Kakeya.ml1Boot.exists_dilate_testBody` that absorbs the `2`-dilates.

The covering hypothesis is in the dilate form used by `Kakeya.ml1Boot.maxDensity_coarse_le`:
the plank sits inside `2 · T̃_{b,j}` and `T̃_{b,j}` inside `cpar · T̃_{ρ,m}`.  Neither
containment is available in its undilated form; see blueprint
`note:ml1bootPlankInTubeVacuous` and `Kakeya.ml1Boot.plankTube_subset_parent_dilate`.

The ratio `cpar` is a *free parameter* and is never consumed: the estimate reads the plank
clause and the factorization only, and the parent containment is carried purely to record the
geometry the caller is in.  Callers over undilated `ρ`-parents instantiate it at
`Kakeya.ml1Boot.plankTubeInParent.C`; callers over `c`-dilate parents, which is what
`Kakeya.ml1Boot.exists_plankTube_parentFamily_dilate` produces after the merge of
`Kakeya.ml1Boot.exists_merged_rhoParentFamily`, instantiate it at
`c · C_{plankTubeInParent}`.  Leaving it free is what lets both use this lemma unchanged.

The `b`-tubes are indexed by the block indices, with `ϖ = Prod.fst`, for the reason set out in
`Kakeya.ml1Boot.densityIn_fibre_le`. -/
theorem maxDensity_fibre_le [Nontrivial E] (hdim : Module.finrank ℝ E = 3)
    {δt ap bp bq ρ : NNReal} (hδt : 0 < δt) (hδa : δt ≤ ap) (hab : ap ≤ bp) (hb1 : bp ≤ 1)
    (hbbq : bp ≤ bq) (hbq : bq ≤ plankPigeonhole.C * bp)
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    {u'' : Finset ι} {tρ : Finset κ} {tb : Finset (κ × Finset ι)}
    (T : ι → Tube δt E) (Tρ : κ → Tube ρ E) (pρ : ι → κ)
    (Tb : κ × Finset ι → Tube bq E)
    (F : (m : κ) → ConvexSpaceBody.Factorization (fibre u'' pρ m)
      (fun i => (T i).toConvexSpaceBody) 2)
    (hdims : ∀ m ∈ tρ, IsPlankFamilyOfDimensions plankPigeonhole.C ap bp (F m).parts
      (fun part => part.convexHull_biUnion (fun i => (T i).toConvexSpaceBody)))
    {m : κ} (hm : m ∈ tρ) {cpar : ℝ}
    (hcover : ∀ j ∈ fibre tb Prod.fst m, j.2 ∈ (F m).parts ∧
      (j.2.convexHull_biUnion fun i => (T i).toConvexSpaceBody) ≤ Tube.dilate (Tb j) 2 ∧
        (Tb j).toConvexSpaceBody ≤ Tube.dilate (Tρ m) cpar) :
    maxDensity (fibre tb Prod.fst m) (fun j => (Tb j).toConvexSpaceBody)
      ≤ (dilateTestBody.C : ENNReal) * 2 * (plankInTube.C : ENNReal)
        * ((bp : ENNReal) / (ap : ENNReal)) := by
  classical
  rw [maxDensity_le_iff]
  intro K
  exact densityIn_fibre_le hdim hδt hδa hab hb1 hbbq hbq T Tρ pρ Tb F hdims hm hcover K

/-- **Summing the fibrewise densities over the parent index set**, from a power-law count.

The general form of `Kakeya.ml1Boot.density_le_card_mul_fibre_of_card`: the only thing the sum
over parents needs is a *cardinality* bound `|t_ρ| ≤ Ccard ρ ^ (-e)`, supplied here as `hcard`,
at an arbitrary absolute constant `Ccard` and an arbitrary exponent `e`.  Both are carried
unchanged into the conclusion.  The `ρ`-tubes themselves, their containment in `B₁` and their
pairwise essential distinctness play no role once the count is in hand, so none of them is a
binder.

The count enters through a single `gcongr`, which reads it as an inequality of extended
non-negative reals and nothing else; in particular no side condition on `Ccard` or `e` — no
`1 ≤ Ccard`, no `0 ≤ e` — is needed or assumed.

This is the form to use when the count comes from something other than essential
distinctness — bounded overlap, say, where
`Kakeya.ml1Boot.card_parents_le_of_hasBoundedOverlap` supplies `Co · C_{parentCount} ρ ^ (-5)`
in place of the `C_{cardBound} ρ ^ (-4)` of `Kakeya.ml1Boot.card_le` — which is why the
hypothesis is stated as the count and not as a property of a tube family. -/
theorem density_le_card_mul_fibre_of_cardPow
    {ρ bq Ccard : NNReal} {e : ℝ}
    {κ l : Type*} [DecidableEq κ] {tρ : Finset κ} {tb : Finset l}
    (Tb : l → Tube bq E) (ϖ : l → κ)
    (hcard : (tρ.card : ENNReal) ≤ (Ccard : ENNReal) * (ρ : ENNReal) ^ (-e))
    (hmaps : ∀ j ∈ tb, ϖ j ∈ tρ)
    {M : ENNReal}
    (hM : ∀ m ∈ tρ, maxDensity (fibre tb ϖ m) (fun j => (Tb j).toConvexSpaceBody) ≤ M) :
    maxDensity tb (fun j => (Tb j).toConvexSpaceBody)
      ≤ (Ccard : ENNReal) * (ρ : ENNReal) ^ (-e) * M := by
  classical
  refine maxDensity_le_of_forall_sum_le ?_
  intro K
  let s : Finset l := tb.filter fun j => (Tb j).toConvexSpaceBody ≤ K
  have hfibresum : ∀ m ∈ tρ,
      (∑ j ∈ s with ϖ j = m, volume ((Tb j).toConvexSpaceBody).carrier) ≤ M * volume K.carrier := by
    intro m hm
    have hset : (s.filter fun j => ϖ j = m) =
        (fibre tb ϖ m).filter fun j => (Tb j).toConvexSpaceBody ≤ K := by
      simp [s, fibre, Finset.filter_filter, and_comm]
    calc
      (∑ j ∈ s with ϖ j = m, volume ((Tb j).toConvexSpaceBody).carrier)
          = ∑ j ∈ fibre tb ϖ m with (Tb j).toConvexSpaceBody ≤ K,
              volume ((Tb j).toConvexSpaceBody).carrier := by
        rw [hset]
      _ = densityIn (fibre tb ϖ m) (fun j => (Tb j).toConvexSpaceBody) K * volume K.carrier := by
        exact Kakeya.sum_volume_eq_densityIn_mul_volume (fibre tb ϖ m)
          (fun j => (Tb j).toConvexSpaceBody) K
      _ ≤ M * volume K.carrier := by
        gcongr
        exact (Kakeya.le_maxDensity (s := fibre tb ϖ m)
          (W := fun j => (Tb j).toConvexSpaceBody) K).trans (hM m hm)
  calc
    (∑ j ∈ tb with (Tb j).toConvexSpaceBody ≤ K, volume ((Tb j).toConvexSpaceBody).carrier)
        = ∑ j ∈ s, volume ((Tb j).toConvexSpaceBody).carrier := by
      rfl
    _ = ∑ m ∈ tρ, ∑ j ∈ s with ϖ j = m, volume ((Tb j).toConvexSpaceBody).carrier := by
      symm
      exact Finset.sum_fiberwise_of_maps_to
        (fun j hj => hmaps j ((Finset.mem_filter.mp hj).1))
        (fun j => volume ((Tb j).toConvexSpaceBody).carrier)
    _ ≤ ∑ m ∈ tρ, M * volume K.carrier := by
      apply Finset.sum_le_sum
      intro m hm
      exact hfibresum m hm
    _ = (tρ.card : ENNReal) * (M * volume K.carrier) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Ccard : ENNReal) * (ρ : ENNReal) ^ (-e) * (M * volume K.carrier) := by
      gcongr
    _ = ((Ccard : ENNReal) * (ρ : ENNReal) ^ (-e) * M) * volume K.carrier := by
      ring

/-- **Summing the fibrewise densities over the parent index set**, from a count.

The specialization of `Kakeya.ml1Boot.density_le_card_mul_fibre_of_cardPow` at the constant
`C_{cardBound}` and the exponent `4`, that is, at the count
`|t_ρ| ≤ C_{cardBound} ρ ^ (-4)` that `Kakeya.ml1Boot.card_le` produces.  This is the shape the
essential-distinctness route uses; see the general form for the mathematics. -/
theorem density_le_card_mul_fibre_of_card
    {ρ bq : NNReal}
    {κ l : Type*} [DecidableEq κ] {tρ : Finset κ} {tb : Finset l}
    (Tb : l → Tube bq E) (ϖ : l → κ)
    (hcard : (tρ.card : ENNReal) ≤ (cardBound.C : ENNReal) * (ρ : ENNReal) ^ (-4 : ℝ))
    (hmaps : ∀ j ∈ tb, ϖ j ∈ tρ)
    {M : ENNReal}
    (hM : ∀ m ∈ tρ, maxDensity (fibre tb ϖ m) (fun j => (Tb j).toConvexSpaceBody) ≤ M) :
    maxDensity tb (fun j => (Tb j).toConvexSpaceBody)
      ≤ (cardBound.C : ENNReal) * (ρ : ENNReal) ^ (-4 : ℝ) * M :=
  density_le_card_mul_fibre_of_cardPow Tb ϖ hcard hmaps hM

/-- **Summing the fibrewise densities over the `ρ`-tubes** (blueprint
`lem:ml1bootDensitySumOverParents`).

If `ϖ : t_b → t_ρ` is *any* assignment of `b`-tubes to `ρ`-tubes and every fibre has maximal
density at most `M`, then `Δ_max(𝕋̃_b) ≤ C_{cardBound} ρ ^ (-4) M`, the factor counting the
essentially distinct `ρ`-tubes in `B₁ ⊆ ℝ³` (`Kakeya.ml1Boot.card_le`).

Only the assignment `ϖ` is used: no containment of `T̃_{b,j}` in `T̃_{ρ,ϖ(j)}`, exact or up to
a dilation, is needed anywhere.

The blueprint writes the right-hand side with `max_{m ∈ t_ρ} Δ_max(𝕋̃_b[T̃_{ρ,m}])`; here the
maximum is replaced by an arbitrary upper bound `M` for the fibrewise densities, which is the
same statement (`M` may be taken to be the maximum) and is the form the caller
`Kakeya.ml1Boot.maxDensity_coarse_le` uses, its fibrewise bound being the uniform constant of
`Kakeya.ml1Boot.maxDensity_fibre_le`.

Essential distinctness enters only through `Kakeya.ml1Boot.card_le`, so this is the thin
specialization of `Kakeya.ml1Boot.density_le_card_mul_fibre_of_card` at that count. -/
theorem density_le_card_mul_fibre (hdim : Module.finrank ℝ E = 3)
    {ρ bq : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    {κ l : Type*} [DecidableEq κ] {tρ : Finset κ} {tb : Finset l}
    (Tρ : κ → Tube ρ E) (Tb : l → Tube bq E) (ϖ : l → κ)
    (hball : ∀ m ∈ tρ, (Tρ m).carrier ⊆ Metric.closedBall 0 1)
    (hEDρ : (tρ : Set κ).Pairwise
      fun m m' => IsEssentiallyDistinct (Tρ m).carrier (Tρ m').carrier)
    (hmaps : ∀ j ∈ tb, ϖ j ∈ tρ)
    {M : ENNReal}
    (hM : ∀ m ∈ tρ, maxDensity (fibre tb ϖ m) (fun j => (Tb j).toConvexSpaceBody) ≤ M) :
    maxDensity tb (fun j => (Tb j).toConvexSpaceBody)
      ≤ (cardBound.C : ENNReal) * (ρ : ENNReal) ^ (-4 : ℝ) * M := by
  exact density_le_card_mul_fibre_of_card Tb ϖ (card_le hdim hρ0 hρ1 tρ Tρ hball hEDρ)
    hmaps (M := M) hM

/-- **Enlarging the ratio of a tube dilate.**  For `0 < c ≤ c'` the `c`-dilate of a tube is
contained in its `c'`-dilate.

By `Kakeya.Tube.dilate_carrier_eq_cthickening` the `c`-dilate is the closed `c σ`-neighbourhood
of the segment of length `c` through the centre in the direction of the tube; raising `c`
enlarges both the radius and the segment, and the two monotonicities compose.

An auxiliary of `Kakeya.ml1Boot.exists_plankTube_parentFamily_essDistinct`: the plank clause it
inherits from `Kakeya.ml1Boot.exists_plankTube_blockwise` is stated at the ratio `2`, while
that parent family carries the larger ratio `Kakeya.ml1Boot.plankTubeParents.C`.  It is a
general fact about `Kakeya.Tube.dilate` and belongs in `Kakeya/Tube/Dilate.lean`; it is stated
here only because that file is not open for this round. -/
theorem dilate_le_dilate_of_le [Nontrivial E] {σ : NNReal} (T : Tube σ E) {c c' : ℝ}
    (hc : 0 < c) (hcc' : c ≤ c') :
    Tube.dilate T c ≤ Tube.dilate T c' := by
  have hc' : 0 < c' := lt_of_lt_of_le hc hcc'
  have hc'ne : c' ≠ 0 := hc'.ne'
  have hσ : c * (σ : ℝ) ≤ c' * (σ : ℝ) :=
    mul_le_mul_of_nonneg_right hcc' (NNReal.coe_nonneg σ)
  change (Tube.dilate T c).carrier ⊆ (Tube.dilate T c').carrier
  rw [_root_.Tube.dilate_carrier_eq_cthickening T hc, _root_.Tube.dilate_carrier_eq_cthickening T hc']
  refine (Metric.cthickening_subset_of_subset (c * (σ : ℝ)) ?hseg).trans
    (Metric.cthickening_mono hσ _)
  refine Convex.segment_subset (convex_segment _ _) ?_ ?_
  · let s : ℝ := (c' - c) / (2 * c')
    have hs : s ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · dsimp [s]
        exact div_nonneg (sub_nonneg.mpr hcc') (mul_pos (by norm_num) hc').le
      · dsimp [s]
        rw [div_le_iff₀ (mul_pos (by norm_num) hc')]
        nlinarith [hc]
    have hx : AffineMap.lineMap (T.center - (c' / 2) • T.direction)
        (T.center + (c' / 2) • T.direction) s = T.center - (c / 2) • T.direction := by
      set ctr : E := T.center with hctr
      set dir : E := T.direction with hdir
      rw [AffineMap.lineMap_apply_module]
      have hcombo : ∀ u : ℝ,
          (1 - u) • (ctr - (c' / 2) • dir) + u • (ctr + (c' / 2) • dir)
            = ctr + ((2 * u - 1) * (c' / 2)) • dir := by
        intro u
        module
      rw [hcombo s]
      have hscalar : (2 * s - 1) * (c' / 2) = -(c / 2) := by
        dsimp [s]
        field_simp [hc'ne]
        ring
      rw [hscalar]
      module
    rw [← hx]
    exact lineMap_mem_segment ℝ _ _ hs
  · let s : ℝ := (c' + c) / (2 * c')
    have hs : s ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · dsimp [s]
        exact div_nonneg (by linarith) (mul_pos (by norm_num) hc').le
      · dsimp [s]
        rw [div_le_iff₀ (mul_pos (by norm_num) hc')]
        nlinarith [hcc']
    have hy : AffineMap.lineMap (T.center - (c' / 2) • T.direction)
        (T.center + (c' / 2) • T.direction) s = T.center + (c / 2) • T.direction := by
      set ctr : E := T.center with hctr
      set dir : E := T.direction with hdir
      rw [AffineMap.lineMap_apply_module]
      have hcombo : ∀ u : ℝ,
          (1 - u) • (ctr - (c' / 2) • dir) + u • (ctr + (c' / 2) • dir)
            = ctr + ((2 * u - 1) * (c' / 2)) • dir := by
        intro u
        module
      rw [hcombo s]
      have hscalar : (2 * s - 1) * (c' / 2) = c / 2 := by
        dsimp [s]
        field_simp [hc'ne]
        ring
      rw [hscalar]
    rw [← hy]
    exact lineMap_mem_segment ℝ _ _ hs

/-- **Merging two heavily overlapping tubes of the same scale.**  If `A` and `B` are `σ`-tubes
with `σ ≤ 1` that fail to be essentially distinct, then the `2`-dilate of `B` lies in the
`C_{lem:ml1bootPlankTubeParents}`-dilate of `A`.

This is what lets `Kakeya.ml1Boot.exists_plankTube_parentFamily_essDistinct` discard a `b`-tube
without discarding any fine tube: the fine tubes of `B` are re-assigned to `A`, and the clause
`T_k ⊆ 2 · B` they carry is transported to `T_k ⊆ C · A`.

Failure of `Kakeya.IsEssentiallyDistinct` means `|A ∩ B| > ½ max(|A|, |B|)`, hence more than
half of *each*, so `Kakeya.Tube.tubeOverlapCoreClose` applies in both directions and gives
`B ⊆ C_ov · A` together with `A ⊆ C_ov · B`, with
`C_ov = Kakeya.Tube.tubeOverlapCoreClose.C n`.  Feeding the second containment to
`Kakeya.Tube.subset_dilate_rescale_of_subset_dilate` at `K = C_ov · B`, `c = C_ov` and
`ρ = σ` moves the whole of `C_ov · B` into the `6 C_ov ²`-dilate of `A`, the rescale being the
identity at the ambient scale `σ`; the `2`-dilate of `B` sits inside `K` because `2 ≤ C_ov`. -/
theorem dilate_le_dilate_of_not_essDistinct [Nontrivial E] {σ : NNReal}
    (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) (A B : Tube σ E)
    (h : ¬ IsEssentiallyDistinct A.carrier B.carrier) :
    Tube.dilate B 2 ≤ Tube.dilate A (plankTubeParents.C (Module.finrank ℝ E)) := by
  let n := Module.finrank ℝ E
  let Cov : ℝ := Tube.tubeOverlapCoreClose.C n
  let Lam : ℝ := 6 * Cov ^ 2
  change Tube.dilate B 2 ≤ Tube.dilate A Lam
  -- 1. Failure of essential distinctness gives a majority overlap in both directions.
  have hgt : (1 / 2 : ENNReal) * max (volume A.carrier) (volume B.carrier) <
      volume (A.carrier ∩ B.carrier) := by
    exact not_le.mp (by simpa [IsEssentiallyDistinct] using h)
  have hAov : (1 / 2 : ENNReal) * volume A.carrier <
      volume (A.carrier ∩ B.carrier) := by
    calc
      (1 / 2 : ENNReal) * volume A.carrier
          ≤ (1 / 2 : ENNReal) * max (volume A.carrier) (volume B.carrier) := by
            gcongr
            exact le_max_left _ _
      _ < volume (A.carrier ∩ B.carrier) := hgt
  have hBov : (1 / 2 : ENNReal) * volume B.carrier <
      volume (B.carrier ∩ A.carrier) := by
    calc
      (1 / 2 : ENNReal) * volume B.carrier
          ≤ (1 / 2 : ENNReal) * max (volume A.carrier) (volume B.carrier) := by
            gcongr
            exact le_max_right _ _
      _ < volume (B.carrier ∩ A.carrier) := by
            simpa [Set.inter_comm] using hgt
  -- 2. Majority overlap forces containment in the `C_ov`-dilate of each other.
  have hBsub : B.carrier ⊆ (Tube.dilate A Cov).carrier := by
    exact Tube.tubeOverlapCoreClose hσ0 hσ1 A B hAov
  have hAsub : A.carrier ⊆ (Tube.dilate B Cov).carrier := by
    exact Tube.tubeOverlapCoreClose hσ0 hσ1 B A hBov
  -- 3. The `C_ov`-dilate of `B` sits inside the `6·C_ov²`-dilate of `A`.
  have h1Cov : (1 : ℝ) ≤ Cov := (Tube.tubeOverlapCoreClose.one_lt_C n).le
  have hCov0 : (0 : ℝ) ≤ Cov := by linarith
  have hLamCov : 2 * Cov ≤ Lam := by
    dsimp [Lam]
    calc
      2 * Cov ≤ 6 * Cov := by nlinarith
      _ ≤ 6 * Cov ^ 2 := by
        have hul : Cov ≤ Cov * Cov := by
          calc
            Cov = Cov * 1 := by ring
            _ ≤ Cov * Cov := mul_le_mul_of_nonneg_left h1Cov hCov0
        nlinarith
  have hρ : 6 * Cov ^ 2 * (σ : ℝ) ≤ Lam * (σ : ℝ) := by
    dsimp [Lam]
    rfl
  have hbig : (Tube.dilate B Cov).carrier ⊆ (Tube.dilate (A.rescale σ) Lam).carrier :=
    Tube.subset_dilate_rescale_of_subset_dilate (T := B) (T₀ := A) (c := Cov) (Λ := Lam)
      (K := (Tube.dilate B Cov).carrier) h1Cov hLamCov hρ hAsub (subset_rfl)
  -- 4. Rescaling `A` back to its ambient scale is the identity.
  have hrescale : A.rescale σ = A := by
    refine Tube.ext ?_ ?_ ?_
    · exact A.carrier_eq.symm
    · rfl
    · rfl
  -- 5. The `2`-dilate of `B` lies inside its `C_ov`-dilate.
  have h2leCov : (2 : ℝ) ≤ Cov := by
    have hcn : (0 : ℝ) < (Tube.le_volume.c n : ℝ) := by
      exact_mod_cast Tube.le_volume.c_pos n
    have hnonneg : (0 : ℝ) ≤ 2 * 4 ^ n / (Tube.le_volume.c n : ℝ) :=
      div_nonneg (by positivity) hcn.le
    dsimp [Cov]
    rw [Tube.tubeOverlapCoreClose.C]
    linarith
  have h2B : Tube.dilate B 2 ≤ Tube.dilate B Cov :=
    dilate_le_dilate_of_le B (by norm_num : (0 : ℝ) < 2) h2leCov
  calc
    Tube.dilate B 2 ≤ Tube.dilate B Cov := h2B
    _ ≤ Tube.dilate (A.rescale σ) Lam := by
      change (Tube.dilate B Cov).carrier ⊆ (Tube.dilate (A.rescale σ) Lam).carrier
      exact hbig
    _ = Tube.dilate A Lam := by
      rw [hrescale]

/-- **A convex hull of tubes is at least half as thick as a unit segment.**  The rank-zero
affine thickness of the convex hull of a nonempty block of tubes is at least `2⁻¹`.

The core of a `Kakeya.Tube` is a segment of length exactly `1` (`Kakeya.Tube.dist_eq_one`), so
the hull of a nonempty block contains two points at distance `1`, and
`Metric.half_dist_le_ethickness_zero` gives the bound.  This is the hypothesis `hlong` of
`Kakeya.ml1Boot.plankTube_subset_parent_dilate`, which is *not* available from the plank
dimensions: `Kakeya.IsPlankOfDimensions` bounds `τ₀` below only by `C_𝕎 ⁻¹`, and
`C_𝕎 ≥ 1024`. -/
theorem half_le_ethickness_convexHull_biUnion {δt : NNReal} {ι : Type*} (T : ι → Tube δt E)
    {part : Finset ι} (hne : part.Nonempty) :
    (2 : ENNReal)⁻¹ ≤ Metric.ethickness ℝ
      (part.convexHull_biUnion (fun i => (T i).toConvexSpaceBody)).carrier 0 := by
  classical
  let W : ConvexSpaceBody E := part.convexHull_biUnion (fun i => (T i).toConvexSpaceBody)
  obtain ⟨k, hk⟩ := hne
  have hsub : (T k).toConvexSpaceBody ≤ W := by
    dsimp [W]
    exact Finset.le_convexHull_biUnion (fun i => (T i).toConvexSpaceBody) hk
  have hx : (T k).x ∈ W.carrier := (SetLike.le_def.mp hsub) (Tube.x_mem_carrier (T k))
  have hy : (T k).y ∈ W.carrier := (SetLike.le_def.mp hsub) (Tube.y_mem_carrier (T k))
  have h := Metric.half_dist_le_ethickness_zero (𝕜 := ℝ) hx hy
  have hconv : ENNReal.ofReal (1 / 2 : ℝ) = (2 : ENNReal)⁻¹ := by
    rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2),
      ENNReal.ofReal_ofNat]
  rwa [show dist (T k).x (T k).y = 1 from (T k).dist_eq_one, hconv] at h

/-- **A pairwise essentially distinct family of tubes is injectively indexed by its bodies.**

Two tubes with the same underlying convex body have the same carrier, and a set of positive
finite volume is not essentially distinct from itself
(`not_isEssentiallyDistinct_self`, with `Kakeya.Tube.volume_pos_and_lt_top`).  This is how
`Kakeya.ml1Boot.exists_plankTube_parentFamily_essDistinct` discharges the injectivity clause of
`Kakeya.ml1Boot.IsParentFamilyDilate` for the retained `b`-tubes: no separate deduplication
step is needed once the retained set is pairwise essentially distinct. -/
theorem injOn_toConvexSpaceBody_of_pairwise_essDistinct [Nontrivial E] {σ : NNReal}
    (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) {ι' : Type*} {s : Finset ι'} (V : ι' → Tube σ E)
    (h : (s : Set ι').Pairwise
      fun l l' => IsEssentiallyDistinct (V l).carrier (V l').carrier) :
    Set.InjOn (fun j => (V j).toConvexSpaceBody) ↑s := by
  intro l hl l' hl' heq
  by_contra hne
  have hdis : IsEssentiallyDistinct (V l).carrier (V l').carrier := h hl hl' hne
  have hcar : (V l).carrier = (V l').carrier := by
    simpa using congrArg (fun W : ConvexSpaceBody E => W.carrier) heq
  have hself : IsEssentiallyDistinct (V l).carrier (V l).carrier := by
    simpa [hcar] using hdis
  have hvol : 0 < volume (V l).carrier ∧ volume (V l).carrier < ⊤ :=
    Tube.volume_pos_and_lt_top hσ0 hσ1 (V l)
  exact False.elim ((not_isEssentiallyDistinct_self (U := (V l).carrier)
    hvol.1.ne' hvol.2.ne) hself)

omit [MeasurableSpace E] [BorelSpace E] in
/-- **A block of a fibre lies in the parent `ρ`-tube.**  The convex hull of a nonempty block of
the fibre of `pρ` over `m` is contained in `T_{ρ,m}`.

Every member of the block lies in `u''`, has `pρ`-image `m`, and is therefore contained in
`T_{ρ,m}` by the parent relation; the containment passes to the convex hull because a tube is
convex (`Finset.Nonempty.convexHull_biUnion_subset_iff`).

This is the hypothesis `hWsub` of `Kakeya.ml1Boot.plankTube_subset_parent_dilate` at the call
site inside `Kakeya.ml1Boot.exists_plankTube_parentFamily`; the containment of the same hull in
`B₁`, which `Kakeya.ml1Boot.exists_plankTube_blockwise` needs, is the same argument run against
the closed unit ball. -/
theorem convexHull_biUnion_le_parent {δt ρ : NNReal} {ι κ : Type*}
    [DecidableEq κ] {u u'' : Finset ι} {tρ : Finset κ}
    (T : ι → Tube δt E) (Tρ : κ → Tube ρ E) (pρ : ι → κ)
    (hu'' : u'' ⊆ u) (hparent : IsParentFamily u T tρ Tρ pρ) {m : κ} {part : Finset ι}
    (hne : part.Nonempty) (hsub : part ⊆ fibre u'' pρ m) :
    (part.convexHull_biUnion fun i => (T i).toConvexSpaceBody) ≤ (Tρ m).toConvexSpaceBody := by
  classical
  exact (Finset.Nonempty.convexHull_biUnion_le_iff hne
    (fun i => (T i).toConvexSpaceBody) (Tρ m).toConvexSpaceBody).mpr (by
      intro i hi
      rcases Finset.mem_filter.mp (hsub hi) with ⟨hiu'', hpm⟩
      rw [← hpm]
      exact hparent.le_parent i (hu'' hiu''))

omit [MeasurableSpace E] [BorelSpace E] in
/-- **A block of a fibre lies in the `c`-dilate of the parent `ρ`-tube.**  The `c`-dilate form
of `Kakeya.ml1Boot.convexHull_biUnion_le_parent`, reading its parent hypothesis at
`Kakeya.ml1Boot.IsParentFamilyDilate c` rather than `Kakeya.ml1Boot.IsParentFamily`.

The argument is the same single step: every member of the block lies in `u''` and has `pρ`-image
`m`, so lies in `c · T_{ρ,m}` by the `le_parent_dilate` clause, and the containment passes to the
convex hull through `Finset.Nonempty.convexHull_biUnion_le_iff`, a dilate of a tube being a
convex body just as the tube is.  Neither the plank nor the ratio is inspected, so `c` is free
and `c = 1` gives the undilated statement back.

This supplies the hypothesis `hWsub` of
`Kakeya.ml1Boot.plankTube_subset_parent_dilate_dilate`, which is the shape the coarse endgame
needs once the `ρ`-parents have been merged by
`Kakeya.ml1Boot.exists_merged_rhoParentFamily` and the leaf-to-parent containment survives only
up to a dilation. -/
theorem convexHull_biUnion_le_parent_dilate [Nontrivial E] {δt ρ : NNReal} {ι κ : Type*}
    [DecidableEq κ] {u u'' : Finset ι} {tρ : Finset κ} {c : ℝ}
    (T : ι → Tube δt E) (Tρ : κ → Tube ρ E) (pρ : ι → κ)
    (hu'' : u'' ⊆ u) (hparent : IsParentFamilyDilate c u T tρ Tρ pρ) {m : κ} {part : Finset ι}
    (hne : part.Nonempty) (hsub : part ⊆ fibre u'' pρ m) :
    (part.convexHull_biUnion fun i => (T i).toConvexSpaceBody) ≤ Tube.dilate (Tρ m) c := by
  classical
  exact (Finset.Nonempty.convexHull_biUnion_le_iff hne
    (fun i => (T i).toConvexSpaceBody) (Tube.dilate (Tρ m) c)).mpr (by
      intro i hi
      rcases Finset.mem_filter.mp (hsub hi) with ⟨hiu'', hpm⟩
      rw [← hpm]
      exact hparent.le_parent_dilate i (hu'' hiu''))

/-- **Merging a `2`-dilate parent family into an essentially distinct one.**  Given tubes
`(V l)_{l ∈ s}` of a common scale `σ ≤ 1` and an assignment `q` of the fine tubes of `u''` to
`s` with `T_k ⊆ 2 · V_{q k}`, there is a *retained* subset `tb ⊆ s` whose tubes are pairwise
essentially distinct and a re-assignment `pb` making `(tb, V, pb)` a
`C_{lem:ml1bootPlankTubeParents}`-dilate parent family for the whole of `u''`.

This is the combinatorial heart of
`Kakeya.ml1Boot.exists_plankTube_parentFamily_essDistinct`, stated
without any reference to planks.  `tb` is a maximal essentially distinct subset
(`Kakeya.Tube.exists_maximal_essDistinct`), so a discarded tube always fails to be essentially
distinct from a retained one, and `Kakeya.ml1Boot.dilate_le_dilate_of_not_essDistinct`
transports the clause `T_k ⊆ 2 · V_{q k}` to the retained tube at the larger ratio.  **No
element of `u''` is dropped**: the price of the essential distinctness is paid entirely in the
dilation ratio.  Surjectivity survives because a retained index is hit by whatever hit it
before the merge, and the injectivity clause is
`Kakeya.ml1Boot.injOn_toConvexSpaceBody_of_pairwise_essDistinct`.

Two further clauses pin the re-assignment `pb` down on the retained indices.  First, a
retained index keeps the fine tubes that were already assigned to it: `q k ∈ tb → pb k = q k`.
Second, `pb` is constant on the fibres of `q`: fine tubes that `q` sends to the same index are
sent by `pb` to the same index, so a block is never split between two `b`-tubes.  As a
consequence the fibre of a retained index under `pb` is in general strictly larger than its own
block — it is the union of all the blocks that were merged into it — so `fibre u'' pb j = j.2`
is *false* for this producer; what holds is the inclusion `j.2 ⊆ fibre u'' pb j` together with
the fact that a block is never split between two `b`-tubes. -/
theorem exists_merged_parentFamily [Nontrivial E] {δt σ : NNReal} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1)
    {ι κ' : Type*} {u'' : Finset ι} {s : Finset κ'}
    (T : ι → Tube δt E) (V : κ' → Tube σ E) (q : ι → κ')
    (hq : ∀ k ∈ u'', q k ∈ s)
    (hsurj : Set.SurjOn q ↑u'' ↑s)
    (hcov : ∀ k ∈ u'', (T k).toConvexSpaceBody ≤ Tube.dilate (V (q k)) 2) :
    ∃ tb ⊆ s, ∃ pb : ι → κ',
      IsParentFamilyDilate (plankTubeParents.C (Module.finrank ℝ E)) u'' T tb V pb ∧
      Set.SurjOn pb ↑u'' ↑tb ∧
      (tb : Set κ').Pairwise
        (fun l l' => IsEssentiallyDistinct (V l).carrier (V l').carrier) ∧
      (∀ k ∈ u'', q k ∈ tb → pb k = q k) ∧
      (∀ k ∈ u'', ∀ k' ∈ u'', q k = q k' → pb k = pb k') := by
  classical
  obtain ⟨tb, htbs, hpair, hmax⟩ := Tube.exists_maximal_essDistinct s V
  have hC2 : (2 : ℝ) ≤ plankTubeParents.C (Module.finrank ℝ E) := by
    have h1 : (1 : ℝ) ≤ Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E) :=
      (Tube.tubeOverlapCoreClose.one_lt_C (Module.finrank ℝ E)).le
    have hpos : (0 : ℝ) ≤ Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E) := by linarith
    have hsqC : (1 : ℝ) ≤ Tube.tubeOverlapCoreClose.C (Module.finrank ℝ E) ^ 2 := by
      nlinarith [mul_le_mul h1 h1 (by norm_num : (0 : ℝ) ≤ 1) hpos]
    dsimp [plankTubeParents.C]
    nlinarith [hsqC]
  let g : κ' → κ' := fun j =>
    if hj : j ∈ tb then j
    else
      if hj' : ∃ i ∈ tb, ¬ IsEssentiallyDistinct (V i).carrier (V j).carrier then
        hj'.choose
      else j
  let pb : ι → κ' := fun k => g (q k)
  have hg_id : ∀ j ∈ tb, g j = j := by
    intro j hj
    simp [g, hj]
  have hg_mem : ∀ j ∈ s, g j ∈ tb := by
    intro j hjs
    by_cases hj : j ∈ tb
    · simp [g, hj]
    · by_cases hj' : ∃ i ∈ tb, ¬ IsEssentiallyDistinct (V i).carrier (V j).carrier
      · simp [g, hj, hj', hj'.choose_spec.1]
      · exfalso
        exact hj' (hmax j hjs hj)
  have hg_dilate : ∀ j ∈ s,
      Tube.dilate (V j) 2 ≤ Tube.dilate (V (g j)) (plankTubeParents.C (Module.finrank ℝ E)) := by
    intro j hjs
    by_cases hj : j ∈ tb
    · have hgj : g j = j := by simp [g, hj]
      rw [hgj]
      exact dilate_le_dilate_of_le (V j) (by norm_num : (0 : ℝ) < 2) hC2
    · by_cases hj' : ∃ i ∈ tb, ¬ IsEssentiallyDistinct (V i).carrier (V j).carrier
      · have hgj : g j = hj'.choose := by simp [g, hj, hj']
        rw [hgj]
        exact dilate_le_dilate_of_not_essDistinct hσ0 hσ1 (V hj'.choose) (V j) hj'.choose_spec.2
      · exfalso
        exact hj' (hmax j hjs hj)
  refine ⟨tb, htbs, pb, ?_, ?_, hpair, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · nlinarith [hC2]
    · exact fun i hi => hg_mem (q i) (hq i hi)
    · exact injOn_toConvexSpaceBody_of_pairwise_essDistinct hσ0 hσ1 V hpair
    · exact fun i hi => (hcov i hi).trans (hg_dilate (q i) (hq i hi))
  · intro l hl
    have hls : l ∈ s := htbs hl
    have hsurj' : ↑s ⊆ q '' ↑u'' := hsurj
    obtain ⟨k, hk, hqk⟩ := hsurj' hls
    refine ⟨k, hk, ?_⟩
    rw [show pb k = g (q k) from rfl]
    rw [hqk]
    exact hg_id l hl
  · intro k hk hqktb
    change g (q k) = q k
    exact hg_id (q k) hqktb
  · intro k hk k' hk' hqeq
    change g (q k) = g (q k')
    rw [hqeq]

/-- **Merging a `ρ`-parent family into an essentially distinct one, at the price of a dilation
ratio.**

`Kakeya.ml1Boot.exists_merged_parentFamily` read at the *parent* scale rather than at the
plank-tube scale.  That lemma is generic in the family it merges — it never inspects a plank —
so the same statement applies verbatim to the `ρ`-tubes of
`Kakeya.ml1Boot.exists_parentFamily_atSixEps`, whose only geometric input is an honest
`Kakeya.ml1Boot.IsParentFamily` together with `Set.SurjOn`.

The output retains a subset `t_ρ' ⊆ t_ρ` whose tubes are pairwise essentially distinct and
re-assigns every leaf of `u` to a retained parent.  **No leaf is dropped**: the whole cost is
paid in the containment clause, which weakens from `T_i ⊆ T_{ρ, p i}` to
`T_i ⊆ C · T_{ρ, p' i}` at `C = Kakeya.ml1Boot.plankTubeParents.C n`.  That weakening is
unavoidable rather than an artefact of this proof: two nearly coincident `ρ`-tubes are not
essentially distinct, and a leaf of one need not lie in the other, so no selection can deliver
pairwise essential distinctness *and* undilated containment without discarding leaves.
Discarding them is the other exit, `Kakeya.ml1Boot.exists_essDistinct_parentFamily`, which
needs `Kakeya.ml1Boot.HasBoundedOverlap` to bound the loss and is false without it.

The last two clauses are inherited from
`Kakeya.ml1Boot.exists_merged_parentFamily`: a retained parent keeps the leaves already
assigned to it, and `p'` is constant on the fibres of `p`, so a fibre is never split between
two parents.  Consequently the fibre of a retained parent under `p'` is the *union* of the
fibres merged into it, which is why a plank factorization taken at `p` is not one at `p'`;
see the ledger of `Kakeya.ml1Boot.multTildeT_of_planksClose`.

What the merge buys is exactly the hypothesis `hEDρ` of
`Kakeya.ml1Boot.maxDensity_coarse_le`, and it buys it *for free in the count*:
`Kakeya.ml1Boot.card_le` reads only pairwise essential distinctness and containment in `B₁` of
the `ρ`-tubes themselves, never the parent relation, so the dilation ratio does not appear in
`|t_ρ'| ≤ C_card ρ ^ (-4)`.  That is
`Kakeya.ml1Boot.card_merged_rhoParents_le`. -/
theorem exists_merged_rhoParentFamily [Nontrivial E] {δt ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    {ι κ : Type*} {u : Finset ι} {tρ : Finset κ}
    (T : ι → Tube δt E) (Tρ : κ → Tube ρ E) (pρ : ι → κ)
    (hparent : IsParentFamily u T tρ Tρ pρ)
    (hsurj : Set.SurjOn pρ ↑u ↑tρ) :
    ∃ tρ' ⊆ tρ, ∃ pρ' : ι → κ,
      IsParentFamilyDilate (plankTubeParents.C (Module.finrank ℝ E)) u T tρ' Tρ pρ' ∧
      Set.SurjOn pρ' ↑u ↑tρ' ∧
      (tρ' : Set κ).Pairwise
        (fun m m' => IsEssentiallyDistinct (Tρ m).carrier (Tρ m').carrier) ∧
      (∀ k ∈ u, pρ k ∈ tρ' → pρ' k = pρ k) ∧
      (∀ k ∈ u, ∀ k' ∈ u, pρ k = pρ k' → pρ' k = pρ' k') := by
  classical
  have hcov : ∀ k ∈ u, (T k).toConvexSpaceBody ≤ Tube.dilate (Tρ (pρ k)) 2 := by
    intro k hk
    calc
      (T k).toConvexSpaceBody ≤ (Tρ (pρ k)).toConvexSpaceBody := hparent.le_parent k hk
      _ ≤ Tube.dilate (Tρ (pρ k)) 2 := by
        change (Tρ (pρ k)).carrier ⊆ (Tube.dilate (Tρ (pρ k)) 2).carrier
        exact Tube.subset_dilate (Tρ (pρ k)) (by norm_num : (1 : ℝ) ≤ 2)
  exact exists_merged_parentFamily hρ0 hρ1 T Tρ pρ hparent.mapsTo hsurj hcov

/-- **The merged `ρ`-parents are counted by `Kakeya.ml1Boot.card_le`, with no charge for the
dilation ratio.**

The retained parent set of `Kakeya.ml1Boot.exists_merged_rhoParentFamily` satisfies
`|t_ρ'| ≤ C_card ρ ^ (-4)`.  The point is negative: `Kakeya.ml1Boot.card_le` inspects only the
`ρ`-tubes — pairwise essential distinctness and containment in `B₁` — and never the parent
relation, so weakening `Kakeya.ml1Boot.IsParentFamily` to
`Kakeya.ml1Boot.IsParentFamilyDilate c` costs nothing here for any `c`.  Containment in `B₁`
transports because the retained set is a subset of the original one.

This is the exponent account behind the `ρ ^ (-5) ↦ δ̃ ^ (-30 ε)` step of
`Kakeya.ml1Boot.maxDensity_coarse_le_rpow` at `ρ = δ̃ ^ (6 ε)`, which budgets the count at
`ρ ^ (-5)` and so is supplied a fortiori by the `ρ ^ (-4)` here. -/
theorem card_merged_rhoParents_le (hdim : Module.finrank ℝ E = 3)
    {ρ : NNReal} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    {κ : Type*} {tρ tρ' : Finset κ} (Tρ : κ → Tube ρ E) (hsub : tρ' ⊆ tρ)
    (hball : ∀ m ∈ tρ, (Tρ m).carrier ⊆ Metric.closedBall 0 1)
    (hED : (tρ' : Set κ).Pairwise
      fun m m' => IsEssentiallyDistinct (Tρ m).carrier (Tρ m').carrier) :
    (tρ'.card : ENNReal) ≤ (cardBound.C : ENNReal) * (ρ : ENNReal) ^ (-4 : ℝ) := by
  exact card_le hdim hρ0 hρ1 tρ' Tρ (fun m hm => hball m (hsub hm)) hED

/-- **The `b`-tubes attached to the planks form a parent family, with pairwise essentially
distinct members** (blueprint `lem:ml1bootPlankTubeParents`, the distinctness-carrying form).

**Retained, and currently unused.**  Every consumer is served by
`Kakeya.ml1Boot.exists_plankTube_parentFamily`, which drops the distinctness and thereby
delivers the same parent family at the plank's own ratio `2` instead of at
`Kakeya.ml1Boot.plankTubeParents.C 3 ≥ 486`.  Distinctness of the `b`-tubes turned out to be
inert in the only place that asked for it; see the docstring of
`Kakeya.ml1Boot.multiplicity_coarse_le` and blueprint `note:ml1bootCoarseEDInert`.  This
statement, and the `Kakeya.ml1Boot.exists_merged_parentFamily` and
`Kakeya.ml1Boot.dilate_le_dilate_of_not_essDistinct` behind it, are kept against a future
consumer that does need distinctness — they are proved and harmless, merely uncalled.

Given the output of `Kakeya.ml1Boot.exists_plankDimensions` — a refined index set `u''`, the
widths `ap ≤ bp` and, for every `ρ`-tube index `m`, a `2`-factorization `F m` of the fibre
`fibre u'' pρ m` whose planks have dimensions `ap × bp × 1` — the tubes supplied for those
planks by `Kakeya.ml1Boot.exists_plank_tube_of_thickness_le_one` are a
`C_{lem:ml1bootPlankTubeParents}`-dilate parent family for `𝕋̃|_{u''}` at the plank-tube scale
`C_𝕎 bp`, with pairwise essentially distinct members, such that every `b`-tube lies in a
dilate of its `ρ`-tube and its `2`-dilate contains the plank of its own block.

The parts of `F m` are the parts of a `Finpartition` of
`fibre u'' pρ m` (`ConvexSpaceBody.Factorization` extends `Finpartition`), and the fibres of
`pρ` cover `u''`, so every `i ∈ u''` lies in exactly one plank and the parent map is total.

## The dilation ratio, and why `u''` is not shrunk

The `b`-tube is `bp / ap` times fatter than the plank it is attached to, so several
`ap`-separated planks in one `bp`-slab over the same `ρ`-tube give heavily overlapping,
hence not essentially distinct, `b`-tubes; some of them have to go.  Discarding a `b`-tube
does *not* force discarding its fine tubes: their parent is re-assigned to a retained
`b`-tube, and the whole cost is paid in the dilation ratio.  That is why the conclusion is
`IsParentFamilyDilate (plankTubeParents.C 3) u'' …` with `u''` still the *fixed* input and
no fine tube dropped — no cardinality share and no positive power of `δ̃` is lost anywhere.

Blueprint `note:auditPlankTubeParents`(a) claimed the distinctness "cannot be arranged at
all while `u''` stays a fixed input".  What is actually obstructed is arranging it *at the
ratio `2`*, which is what (b) of that note already anticipated; the note has been corrected
accordingly.  The escape needs no refinement of `u''`, and in particular no appeal to
`Kakeya.ml1Boot.exists_essDistinct_parentFamily`, whose subsets `s' ⊆ s`, `t' ⊆ t` were the
reason the old citation was invalid: passing to a proper subset of `u''` is exactly what the
conclusion forbids, and it is also not needed.

The retained set is a *maximal* pairwise essentially distinct set of `b`-tubes
(`Kakeya.Tube.exists_maximal_essDistinct`), so every discarded `b`-tube fails to be
essentially distinct from some retained one; at equal scales that is heavy overlap, and
`Kakeya.Tube.tubeOverlapCoreClose` turns it into containment in the retained tube's
`C_ov`-dilate, in both directions.  `Kakeya.Tube.subset_dilate_rescale_of_subset_dilate` then
carries the plank clause `T_k ⊆ 2 · T_{b,l}` of the discarded tube over to the retained one,
at the ratio `Kakeya.ml1Boot.plankTubeParents.C 3 = 6 C_ov ²` whose three constraints are set
out on that constant.  Maximality is also all that the injectivity clause of
`Kakeya.ml1Boot.IsParentFamilyDilate` needs: a pairwise essentially distinct family is
injective on its underlying bodies, a body of positive finite volume not being essentially
distinct from itself.

## Two further points on the shape

The `b`-tubes are indexed by the block indices `(m, t) ∈ 𝓘`, with the parent named as `j.1`
and the block as `j.2` rather than existentially.  This is the shape
`Kakeya.ml1Boot.exists_plankTube_family` produces and the shape
`Kakeya.ml1Boot.maxDensity_coarse_le` consumes — its `hcover` is literally the last clause
below — and an abstract index type with the block supplied existentially makes the density
estimate false, for the reason set out in `Kakeya.ml1Boot.densityIn_fibre_le`.

The scale is the honest `plankPigeonhole.C * bp = C_𝕎 bp` of
`Kakeya.ml1Boot.exists_plank_tube_of_thickness_le_one` and not a free `bq ∈ [bp, C_𝕎 bp]`:
a tube of a *smaller* scale cannot be produced from one of scale `C_𝕎 bp` without losing the
containments.  Consumers stated for a free `bq` with `bp ≤ bq ≤ C_𝕎 bp`, such as
`Kakeya.ml1Boot.maxDensity_coarse_le`, are read at `bq = C_𝕎 bp`.

The containment `T_b ⊆ T_{ρ,m}` holds only up to the bounded dilation
`Kakeya.ml1Boot.plankTubeInParent.C` of `T_{ρ,m}`, since `T_b` has thickness up to `C_𝕎 bp`
and a core built from the plank's outer prism; it is
`Kakeya.ml1Boot.plankTube_subset_parent_dilate`.  The dilation is absorbed by enlarging `ρ`,
which is free because `Kakeya.ml1Boot.flatPrism_dichotomy_decoupled` is stated for an
arbitrary parent scale (`∀ ap bp ρ, … bp ≤ ρ → ρ ≤ 1`).

`hbq1` is new and is not free: `Kakeya.Tube.tubeOverlapCoreClose` is stated for tubes of scale
at most `1`, so the plank-tube scale `C_𝕎 bp` has to be `≤ 1`.  On the route this is met once
`δ̃` is small in terms of `C_𝕎`, `bp` being at most the parent scale `ρ = δ̃ ^ (6 ε)`.

## The fibres of the re-assignment `pb`

The last two conjuncts describe how the merged `b`-tubes relate to the fine tubes they absorb.
A retained index `j` keeps the fine tubes of its own block: `j.2 ⊆ fibre u'' pb j`, where
`fibre u'' pb j = {k ∈ u'' : pb k = j}`.  And a block is never split between two `b`-tubes: if
`j'` is any block index and one of its fine tubes is sent by `pb` to `j`, then the whole block
`j'.2` lies in `fibre u'' pb j`.

The fibre of a retained index is in general *strictly larger* than its own block: it is the
union of all the blocks that were merged into it, so `fibre u'' pb j = j.2` is **false** for
this producer.  What holds is exactly the inclusion `j.2 ⊆ fibre u'' pb j` together with the
no-split clause above. -/
theorem exists_plankTube_parentFamily_essDistinct [Nontrivial E]
    (hdim : Module.finrank ℝ E = 3)
    {δt ap bp ρ : NNReal} (hδt : 0 < δt) (hδa : δt ≤ ap) (hab : ap ≤ bp) (hbρ : bp ≤ ρ)
    (hρ1 : ρ ≤ 1) (hbq1 : plankPigeonhole.C * bp ≤ 1)
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {u u'' : Finset ι} {tρ : Finset κ}
    (T : ι → Tube δt E) (Tρ : κ → Tube ρ E) (pρ : ι → κ)
    (hu'' : u'' ⊆ u)
    (hball : ∀ i ∈ u, (T i).carrier ⊆ Metric.closedBall 0 1)
    (hparent : IsParentFamily u T tρ Tρ pρ)
    (F : (m : κ) → ConvexSpaceBody.Factorization (fibre u'' pρ m)
      (fun i => (T i).toConvexSpaceBody) 2)
    (hparts : ∀ m ∈ tρ, ∀ part ∈ (F m).parts, part.Nonempty)
    (hdims : ∀ m ∈ tρ, IsPlankFamilyOfDimensions plankPigeonhole.C ap bp (F m).parts
      (fun part => part.convexHull_biUnion (fun i => (T i).toConvexSpaceBody))) :
    ∃ (tb : Finset (κ × Finset ι)) (Tb : κ × Finset ι → Tube (plankPigeonhole.C * bp) E)
      (pb : ι → κ × Finset ι),
      tb ⊆ tρ.biUnion (fun m => (F m).parts.image fun part => (m, part)) ∧
      IsParentFamilyDilate (plankTubeParents.C 3) u'' T tb Tb pb ∧
      Set.SurjOn pb ↑u'' ↑tb ∧
      (tb : Set (κ × Finset ι)).Pairwise
        (fun l l' => IsEssentiallyDistinct (Tb l).carrier (Tb l').carrier) ∧
      ∀ j ∈ tb, j.1 ∈ tρ ∧ j.2 ∈ (F j.1).parts ∧
        (Tb j).toConvexSpaceBody ≤ Tube.dilate (Tρ j.1) (plankTubeInParent.C : ℝ) ∧
        (j.2.convexHull_biUnion fun i => (T i).toConvexSpaceBody) ≤ Tube.dilate (Tb j) 2 ∧
        (Tb j).carrier ⊆ Metric.closedBall (0 : E)
          (5 / 2 + 3 * ((plankPigeonhole.C * bp : NNReal) : ℝ)) ∧
        j.2 ⊆ fibre u'' pb j ∧
        (∀ j' ∈ tρ.biUnion (fun m => (F m).parts.image fun part => (m, part)),
          ∀ k ∈ j'.2, pb k = j → j'.2 ⊆ fibre u'' pb j) := by
  classical
  have hb1 : bp ≤ 1 := hbρ.trans hρ1
  have hCw : 1 ≤ plankPigeonhole.C := by
    dsimp [plankPigeonhole.C, Metric.volume_comparison.C, Metric.lt_volume_convexHull.c]
    norm_num
  have hCw0 : 0 < plankPigeonhole.C := lt_of_lt_of_le zero_lt_one hCw
  have hap0 : 0 < ap := lt_of_lt_of_le hδt hδa
  have hbp0 : 0 < bp := lt_of_lt_of_le hap0 hab
  let bq : NNReal := plankPigeonhole.C * bp
  have hbq0 : 0 < bq := by
    dsimp [bq]
    exact mul_pos hCw0 hbp0
  obtain ⟨V, hV⟩ :=
    exists_plankTube_blockwise hdim hδt hδa hab hb1 T pρ hu'' hball F hparts hdims
  obtain ⟨q, hq1, hq2, hq3, hq4⟩ := plankBlocks_partition T pρ hu'' hparent.mapsTo F hparts
  have hcov : ∀ k ∈ u'', (T k).toConvexSpaceBody ≤ Tube.dilate (V (q k)) 2 := by
    intro k hk
    exact (hV (q k) (hq2 k hk)).2.1 k (hq1 k hk).2.2
  obtain ⟨tb, htbs, pb, hpf, hpsurj, hpair, hpb_fix, hpb_factor⟩ :=
    exists_merged_parentFamily (σ := bq) hbq0 hbq1 T V q hq2 hq3 hcov
  rw [hdim] at hpf
  refine ⟨tb, V, pb, htbs, hpf, hpsurj, hpair, ?_⟩
  intro j hj
  have hjt : j ∈ tρ.biUnion (fun m => (F m).parts.image fun part => (m, part)) := htbs hj
  rcases Finset.mem_biUnion.mp hjt with ⟨m, hm, hmemImage⟩
  rcases Finset.mem_image.mp hmemImage with ⟨part, hpmem, hpeq⟩
  have hjt1 : j.1 ∈ tρ := by rw [← hpeq]; exact hm
  have hjt2 : j.2 ∈ (F j.1).parts := by rw [← hpeq]; exact hpmem
  have hne : j.2.Nonempty := hparts j.1 hjt1 j.2 hjt2
  have hdims' : IsPlankOfDimensions plankPigeonhole.C ap bp
      (j.2.convexHull_biUnion fun i => (T i).toConvexSpaceBody) :=
    hdims j.1 hjt1 j.2 hjt2
  have hsub : j.2 ⊆ fibre u'' pρ j.1 := (F j.1).subset hjt2
  have hWsub : (j.2.convexHull_biUnion fun i => (T i).toConvexSpaceBody)
      ≤ (Tρ j.1).toConvexSpaceBody :=
    convexHull_biUnion_le_parent T Tρ pρ hu'' hparent hne hsub
  have hlong : (2 : ENNReal)⁻¹ ≤ Metric.ethickness ℝ
      (j.2.convexHull_biUnion fun i => (T i).toConvexSpaceBody).carrier 0 :=
    half_le_ethickness_convexHull_biUnion T hne
  have hTb : (j.2.convexHull_biUnion fun i => (T i).toConvexSpaceBody) ≤ Tube.dilate (V j) 2 :=
    (hV j hjt).1
  have hparentClause : (V j).toConvexSpaceBody ≤
      Tube.dilate (Tρ j.1) (plankTubeInParent.C : ℝ) :=
    plankTube_subset_parent_dilate hdim hδt hδa hab hbρ hρ1 (Tρ j.1)
      (j.2.convexHull_biUnion fun i => (T i).toConvexSpaceBody) hdims' hWsub hlong (V j) hTb
  have hloc : (V j).carrier ⊆ Metric.closedBall (0 : E)
      (5 / 2 + 3 * ((plankPigeonhole.C * bp : NNReal) : ℝ)) :=
    (hV j hjt).2.2.2.2
  have hfibre_j : j.2 ⊆ fibre u'' pb j := by
    intro k hk
    have hkf : k ∈ u''.filter (fun i => q i = (j.1, j.2)) := by
      rw [hq4 j.1 hjt1 j.2 hjt2]
      exact hk
    have hku : k ∈ u'' := (Finset.mem_filter.mp hkf).1
    have hqkj : q k = (j.1, j.2) := (Finset.mem_filter.mp hkf).2
    have hjj : j = (j.1, j.2) := by rfl
    have hqk : q k = j := by rw [hqkj, hjj]
    have hqtb : q k ∈ tb := by rw [hqk]; exact hj
    have hpbk : pb k = q k := hpb_fix k hku hqtb
    change k ∈ u''.filter (fun i => pb i = j)
    exact Finset.mem_filter.mpr ⟨hku, by rw [hpbk]; exact hqk⟩
  have hnosplit :
      ∀ j' ∈ tρ.biUnion (fun m => (F m).parts.image fun part => (m, part)),
      ∀ k ∈ j'.2, pb k = j → j'.2 ⊆ fibre u'' pb j := by
    intro j' hj' k hk hpbk
    rcases Finset.mem_biUnion.mp hj' with ⟨m', hm', himage'⟩
    rcases Finset.mem_image.mp himage' with ⟨part', hpmem', hpeq'⟩
    have hjt1' : j'.1 ∈ tρ := by rw [← hpeq']; exact hm'
    have hjt2' : j'.2 ∈ (F j'.1).parts := by rw [← hpeq']; exact hpmem'
    have hqfil : u''.filter (fun i => q i = (j'.1, j'.2)) = j'.2 :=
      hq4 j'.1 hjt1' j'.2 hjt2'
    have hkf : k ∈ u''.filter (fun i => q i = (j'.1, j'.2)) := by rw [hqfil]; exact hk
    have hku : k ∈ u'' := (Finset.mem_filter.mp hkf).1
    have hqk : q k = (j'.1, j'.2) := (Finset.mem_filter.mp hkf).2
    intro k'' hk''
    have hkf'' : k'' ∈ u''.filter (fun i => q i = (j'.1, j'.2)) := by rw [hqfil]; exact hk''
    have hku'' : k'' ∈ u'' := (Finset.mem_filter.mp hkf'').1
    have hqk'' : q k'' = (j'.1, j'.2) := (Finset.mem_filter.mp hkf'').2
    have hqq : q k'' = q k := by rw [hqk'', hqk]
    have hpb'' : pb k'' = pb k := hpb_factor k'' hku'' k hku hqq
    change k'' ∈ u''.filter (fun i => pb i = j)
    exact Finset.mem_filter.mpr ⟨hku'', by rw [hpb'']; exact hpbk⟩
  exact ⟨hjt1, hjt2, hparentClause, hTb, hloc, hfibre_j, hnosplit⟩

/-- **The `b`-tubes attached to the planks form a `2`-dilate parent family** (blueprint
`lem:ml1bootPlankTubeParents`).

Given the output of `Kakeya.ml1Boot.exists_plankDimensions` — a refined index set `u''`, the
widths `ap ≤ bp` and, for every `ρ`-tube index `m`, a `2`-factorization `F m` of the fibre
`fibre u'' pρ m` whose planks have dimensions `ap × bp × 1` — the tubes supplied for those
planks by `Kakeya.ml1Boot.exists_plank_tube_of_thickness_le_one` are a `2`-dilate parent family
for `𝕋̃|_{u''}` at the plank-tube scale `C_𝕎 bp`, such that every `b`-tube lies in a bounded
dilate of its `ρ`-tube and its `2`-dilate contains the plank of its own block.  No fine tube is
dropped: `u''` is the fixed input.

This closes the second half of the parent-family gap recorded in blueprint
`note:ml1bootMiddleFactorGaps`.  The parts of `F m` are the parts of a `Finpartition` of
`fibre u'' pρ m` (`ConvexSpaceBody.Factorization` extends `Finpartition`), and the fibres of
`pρ` cover `u''`, so every `i ∈ u''` lies in exactly one plank and the parent map is total.

This is the form every consumer uses.  `Kakeya.ml1Boot.exists_plankTube_parentFamily_essDistinct`
is the same statement with the members additionally pairwise essentially distinct, at the cost of
the ratio `Kakeya.ml1Boot.plankTubeParents.C 3 = 6 C_ov ² ≥ 486`; it is retained but uncalled.

## Why the ratio retreats all the way to `2`

The enlargement to `6 C_ov ²` bought exactly one thing: the `injOn` field of
`Kakeya.ml1Boot.IsParentFamilyDilate`, obtained from a *maximal* essentially distinct subset
via `Kakeya.ml1Boot.injOn_toConvexSpaceBody_of_pairwise_essDistinct`.  Merging heavily
overlapping `b`-tubes is what forces the ratio up, because a discarded tube's plank clause has
to be transported to a retained tube through `Kakeya.Tube.tubeOverlapCoreClose`.

But `injOn` is available without merging anything: `Kakeya.ml1Boot.exists_dedupe_dilate`
identifies only blocks whose `b`-tubes have *equal bodies*, and its last conclusion is equality
of dilates at **every** ratio, so the containment `T_k ⊆ 2 · V_{q k}` transports to the retained
index at the same ratio `2`.  Nothing is paid.

The essential distinctness the enlargement bought is not needed downstream: it was asked for
only by `Kakeya.ml1Boot.multiplicity_coarse_le`, where it was inert — used only to build the
corresponding hypothesis of `Kakeya.ml1Boot.bracket_mem_Icc`, which never referenced it, and
neither did `Kakeya.ml1Boot.multiplicity_coarse_raw` or
`Kakeya.KatzTaoEstimate.multiplicity_bound`.  What excludes degenerate repetition at the bottom
of that chain is the fullness hypothesis, not distinctness.  Those hypotheses have since been
deleted, so nothing asks for it at all.

`Kakeya.ml1Boot.exists_merged_parentFamily` and
`Kakeya.ml1Boot.dilate_le_dilate_of_not_essDistinct` are retained, unused, against a future
consumer that does need distinctness, as is
`Kakeya.ml1Boot.exists_plankTube_parentFamily_essDistinct` itself.

The one candidate consumer that has been checked is *not* one of them.  The open `hcatch` of
`Kakeya.ml1Boot.frostmanConstIn_fibre_le_rpow_atTube` — every fine tube of `u''` lying in
`2 · T_{b,l}` is assigned to `l` — is not supplied by the merge, and not by any strengthening of
it.  Read at every `l ∈ t_b`, which is how hypothesis (a) of
`Kakeya.ml1Boot.normalized_le_of_coarse` reads it, it is equivalent to a separation property of
the `b`-tubes: no fine tube of `u''` lies in two of the `2`-dilates
(`Kakeya.ml1Boot.disjoint_familyIn_of_familyIn_subset_fibre`).  Pairwise essential distinctness,
the merge's only geometric export, is strictly weaker — two `σ`-tubes with parallel cores at
distance `3 σ` are disjoint, hence essentially distinct, while both `2`-dilates contain the
`δ̃`-tube whose core runs midway between them — and the merge's dilation ratio buys nothing here,
being spent on transporting the plank clause of a discarded tube rather than on emptying a
retained tube's dilate.  The re-assignment `pb` is also blind to the relevant geometry: it is
`g ∘ q` with `q` the plank-block map and `g` chosen by maximality among retained `b`-tubes, and
neither factor ever tests `T_k ⊆ 2 · V_l`.  What can replace `hcatch` is the mass share of
`Kakeya.ml1Boot.frostmanConstIn_fibre_le_of_mass`.

The ratio matters, and the `κ ≤ 4` this paragraph names is real --- though the declaration it
named is not, and an earlier correction of mine wrongly concluded from that that the bound was
unsupported.  There is no Lean `Kakeya.ml1Boot.fine_normalize_core`; the lemma is blueprint
`lem:ml1bootFineNormalizeCore`, stated at an abstract normalized ambient radius `R`, and it carries
`κ ≤ 4` as a *genuine hypothesis*.  Its own justification localises the failure, and is worth
repeating here because it says where a large ratio breaks and where it does not.

*Where it does not break.*  The output tubes are placed in `B₁` by the homothety of ratio `4R`, not
by any ambient containment, so the unit-ball clause of the conclusion survives as `κ` grows.  Nor
does the geometry: `Kakeya.Tube.perp_norm_core_sub_le_of_subset_dilate` is proved for free `c` with
the bound `2 c θ`, and `Kakeya/Tube/Rescale.lean` imposes only `0 ≤ κ`.

*Where it does break.*  At the stated constant, and only there.  The selection constant of the
downstairs route is `Kakeya.Tube.essDistinctTubesInSelfDilate.C 3 (4 * (κ + 2) * R * Cₙ)`, which
grows like `κ ^ 12`, while the core's own constant does not see `κ` at all.  The blueprint records
that the margin at `κ = 4` is of order `(4 R) ^ 36 / 6 ^ 12`, so the check survives `κ` into the
hundreds --- and says plainly that this is a numeral, not a proof.  The plank route needs
`c = plankTubeParents.C 3 ≥ 486`, hence `κ = 2 c ≥ 972`, just past that margin.

So the repair is a constant, not a restatement of the output scale: let the core's constant see
`κ`.  Blueprint `note:ml1bootDilateRatioFreeLeafUnargued` carries the same account.

One hypothesis is also gone: the distinctness-carrying form needs `C_𝕎 bp ≤ 1`, because
`Kakeya.Tube.tubeOverlapCoreClose` is stated only for tubes of scale at most `1`.
Deduplication inspects no tube, so no bound on the plank-tube scale is required here. -/
theorem exists_plankTube_parentFamily [Nontrivial E] (hdim : Module.finrank ℝ E = 3)
    {δt ap bp ρ : NNReal} (hδt : 0 < δt) (hδa : δt ≤ ap) (hab : ap ≤ bp) (hbρ : bp ≤ ρ)
    (hρ1 : ρ ≤ 1)
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {u u'' : Finset ι} {tρ : Finset κ}
    (T : ι → Tube δt E) (Tρ : κ → Tube ρ E) (pρ : ι → κ)
    (hu'' : u'' ⊆ u)
    (hball : ∀ i ∈ u, (T i).carrier ⊆ Metric.closedBall 0 1)
    (hparent : IsParentFamily u T tρ Tρ pρ)
    (F : (m : κ) → ConvexSpaceBody.Factorization (fibre u'' pρ m)
      (fun i => (T i).toConvexSpaceBody) 2)
    (hparts : ∀ m ∈ tρ, ∀ part ∈ (F m).parts, part.Nonempty)
    (hdims : ∀ m ∈ tρ, IsPlankFamilyOfDimensions plankPigeonhole.C ap bp (F m).parts
      (fun part => part.convexHull_biUnion (fun i => (T i).toConvexSpaceBody))) :
    ∃ (tb : Finset (κ × Finset ι)) (Tb : κ × Finset ι → Tube (plankPigeonhole.C * bp) E)
      (pb : ι → κ × Finset ι),
      tb ⊆ tρ.biUnion (fun m => (F m).parts.image fun part => (m, part)) ∧
      IsParentFamilyDilate 2 u'' T tb Tb pb ∧
      Set.SurjOn pb ↑u'' ↑tb ∧
      ∀ j ∈ tb, j.1 ∈ tρ ∧ j.2 ∈ (F j.1).parts ∧
        (Tb j).toConvexSpaceBody ≤ Tube.dilate (Tρ j.1) (plankTubeInParent.C : ℝ) ∧
        (j.2.convexHull_biUnion fun i => (T i).toConvexSpaceBody) ≤ Tube.dilate (Tb j) 2 ∧
        (Tb j).carrier ⊆ Metric.closedBall (0 : E)
          (5 / 2 + 3 * ((plankPigeonhole.C * bp : NNReal) : ℝ)) := by
  classical
  have hb1 : bp ≤ 1 := hbρ.trans hρ1
  have hCw : 1 ≤ plankPigeonhole.C := by
    dsimp [plankPigeonhole.C, Metric.volume_comparison.C, Metric.lt_volume_convexHull.c]
    norm_num
  have hCw0 : 0 < plankPigeonhole.C := lt_of_lt_of_le zero_lt_one hCw
  have hap0 : 0 < ap := lt_of_lt_of_le hδt hδa
  have hbp0 : 0 < bp := lt_of_lt_of_le hap0 hab
  obtain ⟨V, hV⟩ :=
    exists_plankTube_blockwise hdim hδt hδa hab hb1 T pρ hu'' hball F hparts hdims
  obtain ⟨q, hq1, hq2, hq3, hq4⟩ := plankBlocks_partition T pρ hu'' hparent.mapsTo F hparts
  have hcov : ∀ k ∈ u'', (T k).toConvexSpaceBody ≤ Tube.dilate (V (q k)) 2 := by
    intro k hk
    exact (hV (q k) (hq2 k hk)).2.1 k (hq1 k hk).2.2
  obtain ⟨tb, htbs, r, hinj, hrmem, hrsurj, hrdil⟩ :=
    exists_dedupe_dilate (tρ.biUnion fun m => (F m).parts.image fun part => (m, part)) V
  refine ⟨tb, V, fun k => r (q k), htbs, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · norm_num
  · exact fun i hi => hrmem (q i) (hq2 i hi)
  · exact hinj
  · intro i hi
    rw [hrdil (q i) (hq2 i hi) 2]
    exact hcov i hi
  · intro l hl
    obtain ⟨j, hj, hrj⟩ := hrsurj hl
    obtain ⟨k, hk, hqk⟩ := hq3 hj
    exact ⟨k, hk, by change r (q k) = l; rw [hqk]; exact hrj⟩
  · intro j hj
    have hjt : j ∈ tρ.biUnion (fun m => (F m).parts.image fun part => (m, part)) := htbs hj
    rcases Finset.mem_biUnion.mp hjt with ⟨m, hm, hmemImage⟩
    rcases Finset.mem_image.mp hmemImage with ⟨part, hpmem, hpeq⟩
    have hjt1 : j.1 ∈ tρ := by rw [← hpeq]; exact hm
    have hjt2 : j.2 ∈ (F j.1).parts := by rw [← hpeq]; exact hpmem
    have hne : j.2.Nonempty := hparts j.1 hjt1 j.2 hjt2
    have hdims' : IsPlankOfDimensions plankPigeonhole.C ap bp
        (j.2.convexHull_biUnion fun i => (T i).toConvexSpaceBody) :=
      hdims j.1 hjt1 j.2 hjt2
    have hsub : j.2 ⊆ fibre u'' pρ j.1 := (F j.1).subset hjt2
    have hWsub : (j.2.convexHull_biUnion fun i => (T i).toConvexSpaceBody)
        ≤ (Tρ j.1).toConvexSpaceBody :=
      convexHull_biUnion_le_parent T Tρ pρ hu'' hparent hne hsub
    have hlong : (2 : ENNReal)⁻¹ ≤ Metric.ethickness ℝ
        (j.2.convexHull_biUnion fun i => (T i).toConvexSpaceBody).carrier 0 :=
      half_le_ethickness_convexHull_biUnion T hne
    have hTb : (j.2.convexHull_biUnion fun i => (T i).toConvexSpaceBody) ≤ Tube.dilate (V j) 2 :=
      (hV j hjt).1
    have hparentClause : (V j).toConvexSpaceBody ≤
        Tube.dilate (Tρ j.1) (plankTubeInParent.C : ℝ) :=
      plankTube_subset_parent_dilate hdim hδt hδa hab hbρ hρ1 (Tρ j.1)
        (j.2.convexHull_biUnion fun i => (T i).toConvexSpaceBody) hdims' hWsub hlong (V j) hTb
    have hloc : (V j).carrier ⊆ Metric.closedBall (0 : E)
        (5 / 2 + 3 * ((plankPigeonhole.C * bp : NNReal) : ℝ)) :=
      (hV j hjt).2.2.2.2
    exact ⟨hjt1, hjt2, hparentClause, hTb, hloc⟩

/-- **The `b`-tubes attached to the planks form a parent family, over `c`-dilate `ρ`-parents**
(blueprint `lem:ml1bootPlankTubeParents`, the dilate-parent form).

This is `Kakeya.ml1Boot.exists_plankTube_parentFamily` with its input parent family weakened
from `Kakeya.ml1Boot.IsParentFamily` to `Kakeya.ml1Boot.IsParentFamilyDilate c`, which is the
only form available once the `ρ`-parents have been made pairwise essentially distinct by
`Kakeya.ml1Boot.exists_merged_rhoParentFamily`: that merge keeps every leaf and pays for the
distinctness purely in a dilation ratio.  It is what lets the merge run *before* the plank
pigeonhole, which is forced -- the merged map's fibres are unions of the old ones, and a union
of factorizations is not a factorization, `ConvexSpaceBody.Factorization.maxDensity_le_mul`
constraining the maximal density of the whole indexed set.

Three of the four steps are literally the undilated ones.  The blockwise tube choice
`Kakeya.ml1Boot.exists_plankTube_blockwise` and the block partition
`Kakeya.ml1Boot.plankBlocks_partition` carry no parent family at all, the latter reading only a
bare `hmapsTo` supplied here by `hparent.mapsTo`; the hull containment is
`Kakeya.ml1Boot.convexHull_biUnion_le_parent_dilate` in place of
`Kakeya.ml1Boot.convexHull_biUnion_le_parent`, landing in `c · T̃_{ρ,m}`, which is exactly the
`hWsub` that `Kakeya.ml1Boot.plankTube_subset_parent_dilate_dilate` consumes.

The two scale hypotheses are read at the dilated parent scale: `bp ≤ c ρ` and `c ρ ≤ 1`, the
form `Kakeya.ml1Boot.exists_plankDimensions_dilate` concludes in.  `1 ≤ c` is not a hypothesis;
it is the `one_le` field of `Kakeya.ml1Boot.IsParentFamilyDilate`.  Consequently the parent
clause is delivered at the ratio `c · C_{plankTubeInParent}` rather than
`C_{plankTubeInParent}`, which is why the density consumers
`Kakeya.ml1Boot.maxDensity_coarse_le` and `Kakeya.ml1Boot.maxDensity_coarse_le_rpow` take that
ratio as a free parameter `cpar`.  The parent family produced is still at the plank's own
ratio `2`: the dilation of the `ρ`-parents is spent in the `ρ`-clause and nowhere else.

At `c = 1` this has the *shape* of `Kakeya.ml1Boot.exists_plankTube_parentFamily`; it does not
reduce to it as a Lean derivation, since that would need `Tube.dilate T 1 = T.toConvexSpaceBody`
to convert the hypothesis, a lemma this development records as true but does not carry.  The
same convention is used at `Kakeya.ml1Boot.plankTube_subset_parent_dilate_dilate` and
`Kakeya.ml1Boot.perParent_ethickness_ranges_dilate`. -/
theorem exists_plankTube_parentFamily_dilate [Nontrivial E] (hdim : Module.finrank ℝ E = 3)
    {δt ap bp ρ : NNReal} {c : ℝ} (hδt : 0 < δt) (hδa : δt ≤ ap) (hab : ap ≤ bp)
    (hbρ : (bp : ℝ) ≤ c * (ρ : ℝ)) (hρ1 : c * (ρ : ℝ) ≤ 1)
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {u u'' : Finset ι} {tρ : Finset κ}
    (T : ι → Tube δt E) (Tρ : κ → Tube ρ E) (pρ : ι → κ)
    (hu'' : u'' ⊆ u)
    (hball : ∀ i ∈ u, (T i).carrier ⊆ Metric.closedBall 0 1)
    (hparent : IsParentFamilyDilate c u T tρ Tρ pρ)
    (F : (m : κ) → ConvexSpaceBody.Factorization (fibre u'' pρ m)
      (fun i => (T i).toConvexSpaceBody) 2)
    (hparts : ∀ m ∈ tρ, ∀ part ∈ (F m).parts, part.Nonempty)
    (hdims : ∀ m ∈ tρ, IsPlankFamilyOfDimensions plankPigeonhole.C ap bp (F m).parts
      (fun part => part.convexHull_biUnion (fun i => (T i).toConvexSpaceBody))) :
    ∃ (tb : Finset (κ × Finset ι)) (Tb : κ × Finset ι → Tube (plankPigeonhole.C * bp) E)
      (pb : ι → κ × Finset ι),
      tb ⊆ tρ.biUnion (fun m => (F m).parts.image fun part => (m, part)) ∧
      IsParentFamilyDilate 2 u'' T tb Tb pb ∧
      Set.SurjOn pb ↑u'' ↑tb ∧
      ∀ j ∈ tb, j.1 ∈ tρ ∧ j.2 ∈ (F j.1).parts ∧
        (Tb j).toConvexSpaceBody ≤ Tube.dilate (Tρ j.1) (c * (plankTubeInParent.C : ℝ)) ∧
        (j.2.convexHull_biUnion fun i => (T i).toConvexSpaceBody) ≤ Tube.dilate (Tb j) 2 ∧
        (Tb j).carrier ⊆ Metric.closedBall (0 : E)
          (5 / 2 + 3 * ((plankPigeonhole.C * bp : NNReal) : ℝ)) := by
  classical
  have hb1 : bp ≤ 1 := NNReal.coe_le_coe.mp (le_trans hbρ hρ1)
  obtain ⟨V, hV⟩ :=
    exists_plankTube_blockwise hdim hδt hδa hab hb1 T pρ hu'' hball F hparts hdims
  obtain ⟨q, hq1, hq2, hq3, hq4⟩ := plankBlocks_partition T pρ hu'' hparent.mapsTo F hparts
  have hcov : ∀ k ∈ u'', (T k).toConvexSpaceBody ≤ Tube.dilate (V (q k)) 2 := by
    intro k hk
    exact (hV (q k) (hq2 k hk)).2.1 k (hq1 k hk).2.2
  obtain ⟨tb, htbs, r, hinj, hrmem, hrsurj, hrdil⟩ :=
    exists_dedupe_dilate (tρ.biUnion fun m => (F m).parts.image fun part => (m, part)) V
  refine ⟨tb, V, fun k => r (q k), htbs, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · norm_num
  · exact fun i hi => hrmem (q i) (hq2 i hi)
  · exact hinj
  · intro i hi
    rw [hrdil (q i) (hq2 i hi) 2]
    exact hcov i hi
  · intro l hl
    obtain ⟨j, hj, hrj⟩ := hrsurj hl
    obtain ⟨k, hk, hqk⟩ := hq3 hj
    exact ⟨k, hk, by change r (q k) = l; rw [hqk]; exact hrj⟩
  · intro j hj
    have hjt : j ∈ tρ.biUnion (fun m => (F m).parts.image fun part => (m, part)) := htbs hj
    rcases Finset.mem_biUnion.mp hjt with ⟨m, hm, hmemImage⟩
    rcases Finset.mem_image.mp hmemImage with ⟨part, hpmem, hpeq⟩
    have hjt1 : j.1 ∈ tρ := by rw [← hpeq]; exact hm
    have hjt2 : j.2 ∈ (F j.1).parts := by rw [← hpeq]; exact hpmem
    have hne : j.2.Nonempty := hparts j.1 hjt1 j.2 hjt2
    have hdims' : IsPlankOfDimensions plankPigeonhole.C ap bp
        (j.2.convexHull_biUnion fun i => (T i).toConvexSpaceBody) :=
      hdims j.1 hjt1 j.2 hjt2
    have hsub : j.2 ⊆ fibre u'' pρ j.1 := (F j.1).subset hjt2
    have hWsub : (j.2.convexHull_biUnion fun i => (T i).toConvexSpaceBody)
        ≤ Tube.dilate (Tρ j.1) c :=
      convexHull_biUnion_le_parent_dilate T Tρ pρ hu'' hparent hne hsub
    have hlong : (2 : ENNReal)⁻¹ ≤ Metric.ethickness ℝ
        (j.2.convexHull_biUnion fun i => (T i).toConvexSpaceBody).carrier 0 :=
      half_le_ethickness_convexHull_biUnion T hne
    have hTb : (j.2.convexHull_biUnion fun i => (T i).toConvexSpaceBody) ≤ Tube.dilate (V j) 2 :=
      (hV j hjt).1
    have hparentClause : (V j).toConvexSpaceBody ≤
        Tube.dilate (Tρ j.1) (c * (plankTubeInParent.C : ℝ)) :=
      plankTube_subset_parent_dilate_dilate hdim hparent.one_le hδt hδa hab hbρ hρ1 (Tρ j.1)
        (j.2.convexHull_biUnion fun i => (T i).toConvexSpaceBody) hdims' hWsub hlong (V j) hTb
    have hloc : (V j).carrier ⊆ Metric.closedBall (0 : E)
        (5 / 2 + 3 * ((plankPigeonhole.C * bp : NNReal) : ℝ)) :=
      (hV j hjt).2.2.2.2
    exact ⟨hjt1, hjt2, hparentClause, hTb, hloc⟩

/-- **The `b`-tubes of the planks form an essentially distinct parent family, over a dilated
`ρ`-parent** (blueprint `lem:ml1bootPlankTubeParents`).

The dilated-input analogue of `Kakeya.ml1Boot.exists_plankTube_parentFamily_essDistinct`: the
same conclusion over an `IsParentFamilyDilate c` `ρ`-parent and the relaxed binders `bp ≤ c ρ`,
`c ρ ≤ 1` that `Kakeya.ml1Boot.exists_plankDimensions_dilate` concludes in.  It is strictly more
general than that lemma — at `c = 1` the binders are its own and `IsParentFamily` implies
`IsParentFamilyDilate 1` — and exports the same full clause list: pairwise essential distinctness
of the `b`-tubes, the own-block inclusion `j.2 ⊆ fibre u'' pb j` and the no-split clause, all of
which `Kakeya.ml1Boot.exists_plankTube_parentFamily_dilate` drops.  **It has no Lean consumer.**
An earlier version of this docstring called it what the restated fine-normalize leaf supplies at
`c = 2`; no such call site exists, so that claim is withdrawn rather than repeated.

As at `Kakeya.ml1Boot.plankTube_subset_parent_dilate_dilate`, the dilation is spent entirely in
the `ρ`-clause, delivered at ratio `c · C_{plankTubeInParent}`; the `b`-tube family is still at
`C_{lem:ml1bootPlankTubeParents}`, `1 ≤ c` is the `one_le` field of `hparent`, and `hbq1` is not
free — `Kakeya.ml1Boot.exists_merged_parentFamily` is stated for tubes of scale at most `1`. -/
theorem exists_plankTube_parentFamily_essDistinct_dilate [Nontrivial E]
    (hdim : Module.finrank ℝ E = 3)
    {δt ap bp ρ : NNReal} {c : ℝ} (hδt : 0 < δt) (hδa : δt ≤ ap) (hab : ap ≤ bp)
    (hbρ : (bp : ℝ) ≤ c * (ρ : ℝ)) (hρ1 : c * (ρ : ℝ) ≤ 1)
    (hbq1 : plankPigeonhole.C * bp ≤ 1)
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {u u'' : Finset ι} {tρ : Finset κ}
    (T : ι → Tube δt E) (Tρ : κ → Tube ρ E) (pρ : ι → κ)
    (hu'' : u'' ⊆ u)
    (hball : ∀ i ∈ u, (T i).carrier ⊆ Metric.closedBall 0 1)
    (hparent : IsParentFamilyDilate c u T tρ Tρ pρ)
    (F : (m : κ) → ConvexSpaceBody.Factorization (fibre u'' pρ m)
      (fun i => (T i).toConvexSpaceBody) 2)
    (hparts : ∀ m ∈ tρ, ∀ part ∈ (F m).parts, part.Nonempty)
    (hdims : ∀ m ∈ tρ, IsPlankFamilyOfDimensions plankPigeonhole.C ap bp (F m).parts
      (fun part => part.convexHull_biUnion (fun i => (T i).toConvexSpaceBody))) :
    ∃ (tb : Finset (κ × Finset ι)) (Tb : κ × Finset ι → Tube (plankPigeonhole.C * bp) E)
      (pb : ι → κ × Finset ι),
      tb ⊆ tρ.biUnion (fun m => (F m).parts.image fun part => (m, part)) ∧
      IsParentFamilyDilate (plankTubeParents.C 3) u'' T tb Tb pb ∧
      Set.SurjOn pb ↑u'' ↑tb ∧
      (tb : Set (κ × Finset ι)).Pairwise
        (fun l l' => IsEssentiallyDistinct (Tb l).carrier (Tb l').carrier) ∧
      ∀ j ∈ tb, j.1 ∈ tρ ∧ j.2 ∈ (F j.1).parts ∧
        (Tb j).toConvexSpaceBody ≤ Tube.dilate (Tρ j.1) (c * (plankTubeInParent.C : ℝ)) ∧
        (j.2.convexHull_biUnion fun i => (T i).toConvexSpaceBody) ≤ Tube.dilate (Tb j) 2 ∧
        (Tb j).carrier ⊆ Metric.closedBall (0 : E)
          (5 / 2 + 3 * ((plankPigeonhole.C * bp : NNReal) : ℝ)) ∧
        j.2 ⊆ fibre u'' pb j ∧
        (∀ j' ∈ tρ.biUnion (fun m => (F m).parts.image fun part => (m, part)),
          ∀ k ∈ j'.2, pb k = j → j'.2 ⊆ fibre u'' pb j) := by
  classical
  have hb1 : bp ≤ 1 := NNReal.coe_le_coe.mp (le_trans hbρ hρ1)
  have hCw : 1 ≤ plankPigeonhole.C := by
    dsimp [plankPigeonhole.C, Metric.volume_comparison.C, Metric.lt_volume_convexHull.c]
    norm_num
  have hCw0 : 0 < plankPigeonhole.C := lt_of_lt_of_le zero_lt_one hCw
  have hap0 : 0 < ap := lt_of_lt_of_le hδt hδa
  have hbp0 : 0 < bp := lt_of_lt_of_le hap0 hab
  let bq : NNReal := plankPigeonhole.C * bp
  have hbq0 : 0 < bq := by
    dsimp [bq]
    exact mul_pos hCw0 hbp0
  obtain ⟨V, hV⟩ :=
    exists_plankTube_blockwise hdim hδt hδa hab hb1 T pρ hu'' hball F hparts hdims
  obtain ⟨q, hq1, hq2, hq3, hq4⟩ := plankBlocks_partition T pρ hu'' hparent.mapsTo F hparts
  have hcov : ∀ k ∈ u'', (T k).toConvexSpaceBody ≤ Tube.dilate (V (q k)) 2 := by
    intro k hk
    exact (hV (q k) (hq2 k hk)).2.1 k (hq1 k hk).2.2
  obtain ⟨tb, htbs, pb, hpf, hpsurj, hpair, hpb_fix, hpb_factor⟩ :=
    exists_merged_parentFamily (σ := bq) hbq0 hbq1 T V q hq2 hq3 hcov
  rw [hdim] at hpf
  refine ⟨tb, V, pb, htbs, hpf, hpsurj, hpair, ?_⟩
  intro j hj
  have hjt : j ∈ tρ.biUnion (fun m => (F m).parts.image fun part => (m, part)) := htbs hj
  rcases Finset.mem_biUnion.mp hjt with ⟨m, hm, hmemImage⟩
  rcases Finset.mem_image.mp hmemImage with ⟨part, hpmem, hpeq⟩
  have hjt1 : j.1 ∈ tρ := by rw [← hpeq]; exact hm
  have hjt2 : j.2 ∈ (F j.1).parts := by rw [← hpeq]; exact hpmem
  have hne : j.2.Nonempty := hparts j.1 hjt1 j.2 hjt2
  have hdims' : IsPlankOfDimensions plankPigeonhole.C ap bp
      (j.2.convexHull_biUnion fun i => (T i).toConvexSpaceBody) :=
    hdims j.1 hjt1 j.2 hjt2
  have hsub : j.2 ⊆ fibre u'' pρ j.1 := (F j.1).subset hjt2
  have hWsub : (j.2.convexHull_biUnion fun i => (T i).toConvexSpaceBody)
      ≤ Tube.dilate (Tρ j.1) c :=
    convexHull_biUnion_le_parent_dilate T Tρ pρ hu'' hparent hne hsub
  have hlong : (2 : ENNReal)⁻¹ ≤ Metric.ethickness ℝ
      (j.2.convexHull_biUnion fun i => (T i).toConvexSpaceBody).carrier 0 :=
    half_le_ethickness_convexHull_biUnion T hne
  have hTb : (j.2.convexHull_biUnion fun i => (T i).toConvexSpaceBody) ≤ Tube.dilate (V j) 2 :=
    (hV j hjt).1
  have hparentClause : (V j).toConvexSpaceBody ≤
      Tube.dilate (Tρ j.1) (c * (plankTubeInParent.C : ℝ)) :=
    plankTube_subset_parent_dilate_dilate hdim hparent.one_le hδt hδa hab hbρ hρ1 (Tρ j.1)
      (j.2.convexHull_biUnion fun i => (T i).toConvexSpaceBody) hdims' hWsub hlong (V j) hTb
  have hloc : (V j).carrier ⊆ Metric.closedBall (0 : E)
      (5 / 2 + 3 * ((plankPigeonhole.C * bp : NNReal) : ℝ)) :=
    (hV j hjt).2.2.2.2
  have hfibre_j : j.2 ⊆ fibre u'' pb j := by
    intro k hk
    have hkf : k ∈ u''.filter (fun i => q i = (j.1, j.2)) := by
      rw [hq4 j.1 hjt1 j.2 hjt2]
      exact hk
    have hku : k ∈ u'' := (Finset.mem_filter.mp hkf).1
    have hqkj : q k = (j.1, j.2) := (Finset.mem_filter.mp hkf).2
    have hjj : j = (j.1, j.2) := by rfl
    have hqk : q k = j := by rw [hqkj, hjj]
    have hqtb : q k ∈ tb := by rw [hqk]; exact hj
    have hpbk : pb k = q k := hpb_fix k hku hqtb
    change k ∈ u''.filter (fun i => pb i = j)
    exact Finset.mem_filter.mpr ⟨hku, by rw [hpbk]; exact hqk⟩
  have hnosplit :
      ∀ j' ∈ tρ.biUnion (fun m => (F m).parts.image fun part => (m, part)),
      ∀ k ∈ j'.2, pb k = j → j'.2 ⊆ fibre u'' pb j := by
    intro j' hj' k hk hpbk
    rcases Finset.mem_biUnion.mp hj' with ⟨m', hm', himage'⟩
    rcases Finset.mem_image.mp himage' with ⟨part', hpmem', hpeq'⟩
    have hjt1' : j'.1 ∈ tρ := by rw [← hpeq']; exact hm'
    have hjt2' : j'.2 ∈ (F j'.1).parts := by rw [← hpeq']; exact hpmem'
    have hqfil : u''.filter (fun i => q i = (j'.1, j'.2)) = j'.2 :=
      hq4 j'.1 hjt1' j'.2 hjt2'
    have hkf : k ∈ u''.filter (fun i => q i = (j'.1, j'.2)) := by rw [hqfil]; exact hk
    have hku : k ∈ u'' := (Finset.mem_filter.mp hkf).1
    have hqk : q k = (j'.1, j'.2) := (Finset.mem_filter.mp hkf).2
    intro k'' hk''
    have hkf'' : k'' ∈ u''.filter (fun i => q i = (j'.1, j'.2)) := by rw [hqfil]; exact hk''
    have hku'' : k'' ∈ u'' := (Finset.mem_filter.mp hkf'').1
    have hqk'' : q k'' = (j'.1, j'.2) := (Finset.mem_filter.mp hkf'').2
    have hqq : q k'' = q k := by rw [hqk'', hqk]
    have hpb'' : pb k'' = pb k := hpb_factor k'' hku'' k hku hqq
    change k'' ∈ u''.filter (fun i => pb i = j)
    exact Finset.mem_filter.mpr ⟨hku'', by rw [hpb'']; exact hpbk⟩
  exact ⟨hjt1, hjt2, hparentClause, hTb, hloc, hfibre_j, hnosplit⟩

/-- **(GWZ Lemma 8.1) The maximal density of the `b`-tubes**, from a power-law count of the
parents.

The general form of `Kakeya.ml1Boot.maxDensity_coarse_le_of_card`, taking the parent count
`|t_ρ| ≤ Ccard ρ ^ (-e)` as the hypothesis `hcard`, at an arbitrary absolute constant `Ccard`
and an arbitrary exponent `e`, rather than deriving it from pairwise essential distinctness.
This is the form to use when the count comes from bounded overlap instead, where
`Kakeya.ml1Boot.card_parents_le_of_hasBoundedOverlap` gives `Co · C_{parentCount} ρ ^ (-5)`.

The count is consumed only by `Kakeya.ml1Boot.density_le_card_mul_fibre_of_cardPow`, which
reads it as a bare inequality of extended non-negative reals, so neither `1 ≤ Ccard` nor
`0 ≤ e` is needed or assumed.

If every `b`-tube of the coarse family lies in some `ρ`-tube of `𝕋̃_ρ` and contains one of
the planks of `Kakeya.ml1Boot.exists_plankDimensions`, then
`Δ_max(𝕋̃_b) ≤ C_* · 2 C_P · Ccard · ρ ^ (-e) (b / a)`.  At `Ccard = C_{cardBound}` and
`e = 4` the constant is `Kakeya.ml1Boot.coarsePlank.C` and this is
`Kakeya.ml1Boot.maxDensity_coarse_le_of_card`.

The proof estimates `Δ_max` over a single `ρ`-tube by `C_* · 2 C_P (b/a)`, using
`Δ_max(𝕎_m) ≤ 2`, and then sums over the at most `Ccard ρ ^ (-e)` parent
`ρ`-tubes counted by `hcard`.  The blueprint's "in particular", the
substitution `ρ = δ̃ ^ (6 ε)` and `b / a ≤ δ̃ ^ (-η'_{j-1})` giving
`Δ_max(𝕋̃_b) ≤ C_Δ δ̃ ^ (-30 ε - η'_{j-1})` at `e = 5`, is immediate and is
`Kakeya.ml1Boot.maxDensity_coarse_le_rpow_of_cardPow`.

As in `Kakeya.ml1Boot.frostmanConstIn_fibre_le`, the `b`-tubes have the honest scale `bq`
with `bp ≤ bq ≤ C_𝕎 bp`, the extra `C_𝕎²` in the volume comparison being absorbed by
`Kakeya.ml1Boot.coarsePlank.C`; and the parent family at scale `bq` is for the *refined*
family `𝕋̃|_{u''}`, which is the family the planks factor.

Nothing here constrains *how* `hcard` is obtained.  The route through
`Kakeya.ml1Boot.card_le` — pairwise essential distinctness of `ρ`-tubes lying in `B₁` — is
the wrapper `Kakeya.ml1Boot.maxDensity_coarse_le`.  Note that `B₁`-containment does *not*
follow from the parent relation `T i ⊆ Tρ (pρ i)`, a containment running the wrong way, so a
parent tube may protrude from `B₁`; consumers of the wrapper get it from
`Kakeya.ml1Boot.exists_normalizedMiddleData`, whose `ρ`-tube is in `B₁`, the general
construction `Kakeya.ml1Boot.exists_essDistinct_parentFamily` only reaching `B₂`.

The statement is generic in the parent scale `ρ`; the substitution `ρ = δ̃ ^ (6 ε)`, which
turns `ρ ^ (-e)` into `δ̃ ^ (-6 ε e)` and hence gives
`Δ_max(𝕋̃_b) ≤ C_Δ δ̃ ^ (-6 ε e - η'_{j-1})`, is
`Kakeya.ml1Boot.maxDensity_coarse_le_rpow_of_cardPow`.

The ambient family `𝕋̃` itself, the parent relations it stands in and the containment of its
members in `B₁` are *not* binders here: nothing in the estimate refers to them.  All the
proof uses is the factorization `F` of each coarse fibre `fibre u'' pρ m`, its plank
dimensions `hdims`, and the covering `hcover`.

The `b`-tubes are indexed by the block indices `(m, t) ∈ 𝓘`, and `hcover` names the block of
`j` as `j` itself rather than existentially: the parent is `j.1` and the plank is that of
`j.2`.  An abstract index type with the block supplied existentially makes the statement
false, for the reason set out in `Kakeya.ml1Boot.densityIn_fibre_le`; here the fibrewise input
`Kakeya.ml1Boot.maxDensity_fibre_le` is the declaration that needs it.  This is the shape
`Kakeya.ml1Boot.exists_plankTube_family` produces.

## The parent-containment ratio, and the two scale hypotheses

The ratio `cpar` at which `hcover` places `T̃_{b,j}` inside `T̃_{ρ,j.1}` is a free parameter,
because it is never consumed: the estimate reads only the plank clause and the factorization,
so no relation between `cpar`, `bp` and `ρ` is required.  Undilated callers read it at
`Kakeya.ml1Boot.plankTubeInParent.C`; callers whose `ρ`-parents have been merged by
`Kakeya.ml1Boot.exists_merged_rhoParentFamily` -- and so hold only a
`Kakeya.ml1Boot.IsParentFamilyDilate c` -- read it at `c · C_{plankTubeInParent}`, which is the
ratio `Kakeya.ml1Boot.exists_plankTube_parentFamily_dilate` delivers.

For the same reason the scale hypothesis is `hb1 : bp ≤ 1` together with `hρ0 : 0 < ρ`, rather
than the single `bp ≤ ρ` carried before.  That hypothesis was used for exactly these two
consequences and for nothing else, and `bp ≤ ρ` is *not* available on the dilate route, where
the pigeonhole delivers only `(bp : ℝ) ≤ c ρ`.  Positivity of `ρ` has to be assumed rather
than derived: `bp ≤ c ρ` with `c ≥ 1` does give `0 < ρ` from `0 < δt ≤ ap ≤ bp`, but `c` is not
in scope here, so the caller supplies it. -/
theorem maxDensity_coarse_le_of_cardPow [Nontrivial E] (hdim : Module.finrank ℝ E = 3)
    {δt ap bp bq ρ Ccard : NNReal} {e : ℝ}
    (hδt : 0 < δt) (hδa : δt ≤ ap) (hab : ap ≤ bp) (hb1 : bp ≤ 1)
    (hbbq : bp ≤ bq) (hbq : bq ≤ plankPigeonhole.C * bp)
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {u'' : Finset ι} {tρ : Finset κ}
    {tb : Finset (κ × Finset ι)}
    (T : ι → Tube δt E) (Tρ : κ → Tube ρ E) (pρ : ι → κ)
    (Tb : κ × Finset ι → Tube bq E)
    (hcard : (tρ.card : ENNReal) ≤ (Ccard : ENNReal) * (ρ : ENNReal) ^ (-e))
    (F : (m : κ) → ConvexSpaceBody.Factorization (fibre u'' pρ m)
      (fun i => (T i).toConvexSpaceBody) 2)
    (hdims : ∀ m ∈ tρ, IsPlankFamilyOfDimensions plankPigeonhole.C ap bp (F m).parts
      (fun part => part.convexHull_biUnion (fun i => (T i).toConvexSpaceBody)))
    {cpar : ℝ}
    (hcover : ∀ j ∈ tb, j.1 ∈ tρ ∧ j.2 ∈ (F j.1).parts ∧
      (Tb j).toConvexSpaceBody ≤ Tube.dilate (Tρ j.1) cpar ∧
      (j.2.convexHull_biUnion fun i => (T i).toConvexSpaceBody) ≤ Tube.dilate (Tb j) 2) :
    maxDensity tb (fun j => (Tb j).toConvexSpaceBody)
      ≤ ((dilateTestBody.C * 2 * plankInTube.C * Ccard : NNReal) : ENNReal)
        * (ρ : ENNReal) ^ (-e) * ((bp : ENNReal) / (ap : ENNReal)) := by
  classical
  have hmaps : ∀ j ∈ tb, Prod.fst j ∈ tρ := by
    intro j hj
    exact (hcover j hj).1
  let M : ENNReal :=
    (dilateTestBody.C : ENNReal) * 2 * (plankInTube.C : ENNReal)
      * ((bp : ENNReal) / (ap : ENNReal))
  have hM : ∀ m ∈ tρ,
      maxDensity (fibre tb Prod.fst m) (fun j => (Tb j).toConvexSpaceBody) ≤ M := by
    intro m hm
    have hcov_m : ∀ j ∈ fibre tb Prod.fst m, j.2 ∈ (F m).parts ∧
        (j.2.convexHull_biUnion fun i => (T i).toConvexSpaceBody) ≤ Tube.dilate (Tb j) 2 ∧
          (Tb j).toConvexSpaceBody ≤ Tube.dilate (Tρ m) cpar := by
      intro j hj
      have hjm : j ∈ tb := (Finset.mem_filter.mp hj).1
      have hϖ : Prod.fst j = m := (Finset.mem_filter.mp hj).2
      have hh := hcover j hjm
      have hpart : j.2 ∈ (F m).parts := by
        rw [← hϖ]
        exact hh.2.1
      have hB : (j.2.convexHull_biUnion fun i => (T i).toConvexSpaceBody)
          ≤ Tube.dilate (Tb j) 2 := hh.2.2.2
      have hT : (Tb j).toConvexSpaceBody ≤ Tube.dilate (Tρ m) cpar := by
        rw [← hϖ]
        exact hh.2.2.1
      exact ⟨hpart, hB, hT⟩
    simpa [M] using (maxDensity_fibre_le hdim hδt hδa hab hb1 hbbq hbq T Tρ pρ Tb F hdims
      (hm := hm) (hcover := hcov_m))
  have hmain := density_le_card_mul_fibre_of_cardPow Tb Prod.fst hcard hmaps
    (M := M) hM
  have hquiv : (Ccard : ENNReal) * (ρ : ENNReal) ^ (-e) * M
      = ((dilateTestBody.C * 2 * plankInTube.C * Ccard : NNReal) : ENNReal)
        * (ρ : ENNReal) ^ (-e) * ((bp : ENNReal) / (ap : ENNReal)) := by
    let r : ENNReal := (bp : ENNReal) / (ap : ENNReal)
    let Q : ENNReal := (ρ : ENNReal) ^ (-e)
    change (Ccard : ENNReal) * Q * (dilateTestBody.C * 2 * plankInTube.C * r)
        = (dilateTestBody.C * 2 * plankInTube.C * Ccard) * Q * r
    ring
  exact le_trans hmain (le_of_eq hquiv)

/-- **(GWZ Lemma 8.1) The maximal density of the `b`-tubes**, from a count of the parents.

The specialization of `Kakeya.ml1Boot.maxDensity_coarse_le_of_cardPow` at the constant
`C_{cardBound}` and the exponent `4`, that is, at the count
`|t_ρ| ≤ C_{cardBound} ρ ^ (-4)` that `Kakeya.ml1Boot.card_le` produces, whose constant
`C_* · 2 C_P · C_{cardBound}` is `Kakeya.ml1Boot.coarsePlank.C`.  See the general form for the
mathematics. -/
theorem maxDensity_coarse_le_of_card [Nontrivial E] (hdim : Module.finrank ℝ E = 3)
    {δt ap bp bq ρ : NNReal} (hδt : 0 < δt) (hδa : δt ≤ ap) (hab : ap ≤ bp) (hb1 : bp ≤ 1)
    (hbbq : bp ≤ bq) (hbq : bq ≤ plankPigeonhole.C * bp)
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {u'' : Finset ι} {tρ : Finset κ}
    {tb : Finset (κ × Finset ι)}
    (T : ι → Tube δt E) (Tρ : κ → Tube ρ E) (pρ : ι → κ)
    (Tb : κ × Finset ι → Tube bq E)
    (hcard : (tρ.card : ENNReal) ≤ (cardBound.C : ENNReal) * (ρ : ENNReal) ^ (-4 : ℝ))
    (F : (m : κ) → ConvexSpaceBody.Factorization (fibre u'' pρ m)
      (fun i => (T i).toConvexSpaceBody) 2)
    (hdims : ∀ m ∈ tρ, IsPlankFamilyOfDimensions plankPigeonhole.C ap bp (F m).parts
      (fun part => part.convexHull_biUnion (fun i => (T i).toConvexSpaceBody)))
    {cpar : ℝ}
    (hcover : ∀ j ∈ tb, j.1 ∈ tρ ∧ j.2 ∈ (F j.1).parts ∧
      (Tb j).toConvexSpaceBody ≤ Tube.dilate (Tρ j.1) cpar ∧
      (j.2.convexHull_biUnion fun i => (T i).toConvexSpaceBody) ≤ Tube.dilate (Tb j) 2) :
    maxDensity tb (fun j => (Tb j).toConvexSpaceBody)
      ≤ (coarsePlank.C : ENNReal) * (ρ : ENNReal) ^ (-4 : ℝ)
        * ((bp : ENNReal) / (ap : ENNReal)) :=
  maxDensity_coarse_le_of_cardPow hdim hδt hδa hab hb1 hbbq hbq T Tρ pρ Tb hcard F hdims hcover

/-- **(GWZ Lemma 8.1) The maximal density of the `b`-tubes** (blueprint
`lem:ml1bootCoarsePlankDensity`).

`Kakeya.ml1Boot.maxDensity_coarse_le_of_card` with the parent count supplied by
`Kakeya.ml1Boot.card_le`, that is, from the `ρ`-tubes being pairwise essentially distinct
(`hEDρ`) and contained in `B₁` (`hballρ`).  See that declaration for the mathematics; the
essential-distinctness hypothesis is used for the count and for nothing else. -/
theorem maxDensity_coarse_le [Nontrivial E] (hdim : Module.finrank ℝ E = 3)
    {δt ap bp bq ρ : NNReal} (hδt : 0 < δt) (hδa : δt ≤ ap) (hab : ap ≤ bp) (hb1 : bp ≤ 1)
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hbbq : bp ≤ bq) (hbq : bq ≤ plankPigeonhole.C * bp)
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {u'' : Finset ι} {tρ : Finset κ}
    {tb : Finset (κ × Finset ι)}
    (T : ι → Tube δt E) (Tρ : κ → Tube ρ E) (pρ : ι → κ)
    (Tb : κ × Finset ι → Tube bq E)
    (hballρ : ∀ m ∈ tρ, (Tρ m).carrier ⊆ Metric.closedBall 0 1)
    (hEDρ : (tρ : Set κ).Pairwise
      fun m m' => IsEssentiallyDistinct (Tρ m).carrier (Tρ m').carrier)
    (F : (m : κ) → ConvexSpaceBody.Factorization (fibre u'' pρ m)
      (fun i => (T i).toConvexSpaceBody) 2)
    (hdims : ∀ m ∈ tρ, IsPlankFamilyOfDimensions plankPigeonhole.C ap bp (F m).parts
      (fun part => part.convexHull_biUnion (fun i => (T i).toConvexSpaceBody)))
    {cpar : ℝ}
    (hcover : ∀ j ∈ tb, j.1 ∈ tρ ∧ j.2 ∈ (F j.1).parts ∧
      (Tb j).toConvexSpaceBody ≤ Tube.dilate (Tρ j.1) cpar ∧
      (j.2.convexHull_biUnion fun i => (T i).toConvexSpaceBody) ≤ Tube.dilate (Tb j) 2) :
    maxDensity tb (fun j => (Tb j).toConvexSpaceBody)
      ≤ (coarsePlank.C : ENNReal) * (ρ : ENNReal) ^ (-4 : ℝ)
        * ((bp : ENNReal) / (ap : ENNReal)) := by
  exact maxDensity_coarse_le_of_card hdim hδt hδa hab hb1 hbbq hbq T Tρ pρ Tb
    (card_le hdim hρ0 hρ1 tρ Tρ hballρ hEDρ) F hdims hcover

/-- **The maximal density of the `b`-tubes at the parent scale `ρ = δ̃ ^ (6 ε)`**, from a
power-law count of the parents.

The general form of `Kakeya.ml1Boot.maxDensity_coarse_le_rpow_of_card`, taking the parent count
`hcard` at an arbitrary absolute constant `Ccard` and an arbitrary exponent `e` rather than
deriving it from pairwise essential distinctness.

In the situation of `Kakeya.ml1Boot.maxDensity_coarse_le_of_cardPow`, if moreover
`ρ = δ̃ ^ (6 ε)` and
`bp / ap ≤ δ̃ ^ (-η'_{j-1})`, then

`Δ_max(𝕋̃_b) ≤ C_* · 2 C_P · Ccard · δ̃ ^ (-6 ε e - η'_{j-1})`.

Substituting `ρ = δ̃ ^ (6 ε)` turns `ρ ^ (-e)` into `δ̃ ^ (-6 ε e)` — an unconditional
`ENNReal.rpow_mul`, so no sign condition on `e` is involved — and the two powers of `δ̃`
combine.  At `Ccard = C_{cardBound}` and `e = 5` the constant is
`Kakeya.ml1Boot.coarsePlank.C`, the exponent is `-30 ε - η'_{j-1}`, and this is
`Kakeya.ml1Boot.maxDensity_coarse_le_rpow_of_card`, the form in which the second hypothesis of
`Kakeya.ml1Boot.bracket_mem_Icc` is used in `Kakeya.ml1Boot.multiplicity_coarse_le`.

The parent scale is `δ̃ ^ (6 ε)` and not `δ̃ ^ (2 ε)` because the lower Frostman bounds of
`Kakeya.ml1Boot.exists_normalizedMiddleData`(iv) are available only on the `5 ε`-window
`[δ̃ ^ (1 - 5 ε), δ̃ ^ (5 ε)]`, which excludes `δ̃ ^ (2 ε)`; see blueprint
`note:ml1bootWindowConsumers`(3). -/
theorem maxDensity_coarse_le_rpow_of_cardPow [Nontrivial E] (hdim : Module.finrank ℝ E = 3)
    {δt ap bp bq ρ Ccard : NNReal} {e : ℝ}
    (hδt : 0 < δt) (hδa : δt ≤ ap) (hab : ap ≤ bp) (hb1 : bp ≤ 1)
    (hbbq : bp ≤ bq) (hbq : bq ≤ plankPigeonhole.C * bp)
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {u'' : Finset ι} {tρ : Finset κ}
    {tb : Finset (κ × Finset ι)}
    (T : ι → Tube δt E) (Tρ : κ → Tube ρ E) (pρ : ι → κ)
    (Tb : κ × Finset ι → Tube bq E)
    (hcard : (tρ.card : ENNReal) ≤ (Ccard : ENNReal) * (ρ : ENNReal) ^ (-e))
    (F : (m : κ) → ConvexSpaceBody.Factorization (fibre u'' pρ m)
      (fun i => (T i).toConvexSpaceBody) 2)
    (hdims : ∀ m ∈ tρ, IsPlankFamilyOfDimensions plankPigeonhole.C ap bp (F m).parts
      (fun part => part.convexHull_biUnion (fun i => (T i).toConvexSpaceBody)))
    {cpar : ℝ}
    (hcover : ∀ j ∈ tb, j.1 ∈ tρ ∧ j.2 ∈ (F j.1).parts ∧
      (Tb j).toConvexSpaceBody ≤ Tube.dilate (Tρ j.1) cpar ∧
      (j.2.convexHull_biUnion fun i => (T i).toConvexSpaceBody) ≤ Tube.dilate (Tb j) 2)
    {ε ηp : ℝ} (_hε : 0 ≤ ε) (_hηp : 0 ≤ ηp)
    (hρeq : (ρ : ENNReal) = (δt : ENNReal) ^ (6 * ε))
    (hba : (bp : ENNReal) / (ap : ENNReal) ≤ (δt : ENNReal) ^ (-ηp)) :
    maxDensity tb (fun j => (Tb j).toConvexSpaceBody)
      ≤ ((dilateTestBody.C * 2 * plankInTube.C * Ccard : NNReal) : ENNReal)
        * (δt : ENNReal) ^ (-(6 * ε * e) - ηp) := by
  set C : ENNReal := ((dilateTestBody.C * 2 * plankInTube.C * Ccard : NNReal) : ENNReal) with hC
  have h1 : maxDensity tb (fun j => (Tb j).toConvexSpaceBody)
      ≤ C * (ρ : ENNReal) ^ (-e) * ((bp : ENNReal) / (ap : ENNReal)) :=
    maxDensity_coarse_le_of_cardPow hdim hδt hδa hab hb1 hbbq hbq T Tρ pρ Tb
      hcard F hdims hcover
  have hDt0 : (δt : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr (ne_of_gt hδt)
  have hDtTop : (δt : ENNReal) ≠ ⊤ := ENNReal.coe_ne_top
  have hpow1 : (ρ : ENNReal) ^ (-e) = (δt : ENNReal) ^ (-(6 * ε * e)) := by
    calc
      (ρ : ENNReal) ^ (-e) = ((δt : ENNReal) ^ (6 * ε)) ^ (-e) := by rw [hρeq]
      _ = (δt : ENNReal) ^ ((6 * ε) * (-e)) := by rw [← ENNReal.rpow_mul]
      _ = (δt : ENNReal) ^ (-(6 * ε * e)) := by congr 1; ring
  have hmid :
      C * (ρ : ENNReal) ^ (-e) * ((bp : ENNReal) / (ap : ENNReal))
        ≤ C * (δt : ENNReal) ^ (-(6 * ε * e)) * (δt : ENNReal) ^ (-ηp) := by
    calc
      C * (ρ : ENNReal) ^ (-e) * ((bp : ENNReal) / (ap : ENNReal))
          = C * (δt : ENNReal) ^ (-(6 * ε * e))
              * ((bp : ENNReal) / (ap : ENNReal)) := by
            rw [hpow1]
      _ ≤ C * (δt : ENNReal) ^ (-(6 * ε * e)) * (δt : ENNReal) ^ (-ηp) := by
            exact mul_le_mul_right hba (C * (δt : ENNReal) ^ (-(6 * ε * e)))
  have hcomb :
      C * (δt : ENNReal) ^ (-(6 * ε * e)) * (δt : ENNReal) ^ (-ηp)
        = C * (δt : ENNReal) ^ (-(6 * ε * e) - ηp) := by
    calc
      C * (δt : ENNReal) ^ (-(6 * ε * e)) * (δt : ENNReal) ^ (-ηp)
          = C * ((δt : ENNReal) ^ (-(6 * ε * e)) * (δt : ENNReal) ^ (-ηp)) := by
            rw [mul_assoc]
      _ = C * (δt : ENNReal) ^ (-(6 * ε * e) - ηp) := by
            congr 1
            rw [← ENNReal.rpow_add (-(6 * ε * e)) (-ηp) hDt0 hDtTop]
            congr 1
  exact le_trans (le_trans h1 hmid) (le_of_eq hcomb)

/-- **The maximal density of the `b`-tubes at the parent scale `ρ = δ̃ ^ (6 ε)`**, from a count
of the parents.

The specialization of `Kakeya.ml1Boot.maxDensity_coarse_le_rpow_of_cardPow` at the constant
`C_{cardBound}` and the exponent `5`, where the constant is `Kakeya.ml1Boot.coarsePlank.C` and
`ρ ^ (-5) = δ̃ ^ (-30 ε)`, giving

`Δ_max(𝕋̃_b) ≤ C_Δ δ̃ ^ (-30 ε - η'_{j-1})`.

The parent count is read at `ρ ^ (-5)` and not at the `ρ ^ (-4)` that
`Kakeya.ml1Boot.card_le` proves: for `ρ ≤ 1` the former is the weaker bound, and budgeting the
count there is what leaves the exponent account of the coarse route stated at a single place.

This is the form in which the second hypothesis of `Kakeya.ml1Boot.bracket_mem_Icc` is used in
`Kakeya.ml1Boot.multiplicity_coarse_le`.  See the general form for the mathematics. -/
theorem maxDensity_coarse_le_rpow_of_card [Nontrivial E] (hdim : Module.finrank ℝ E = 3)
    {δt ap bp bq ρ : NNReal} (hδt : 0 < δt) (hδa : δt ≤ ap) (hab : ap ≤ bp) (hb1 : bp ≤ 1)
    (hbbq : bp ≤ bq) (hbq : bq ≤ plankPigeonhole.C * bp)
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {u'' : Finset ι} {tρ : Finset κ}
    {tb : Finset (κ × Finset ι)}
    (T : ι → Tube δt E) (Tρ : κ → Tube ρ E) (pρ : ι → κ)
    (Tb : κ × Finset ι → Tube bq E)
    (hcard : (tρ.card : ENNReal) ≤ (cardBound.C : ENNReal) * (ρ : ENNReal) ^ (-5 : ℝ))
    (F : (m : κ) → ConvexSpaceBody.Factorization (fibre u'' pρ m)
      (fun i => (T i).toConvexSpaceBody) 2)
    (hdims : ∀ m ∈ tρ, IsPlankFamilyOfDimensions plankPigeonhole.C ap bp (F m).parts
      (fun part => part.convexHull_biUnion (fun i => (T i).toConvexSpaceBody)))
    {cpar : ℝ}
    (hcover : ∀ j ∈ tb, j.1 ∈ tρ ∧ j.2 ∈ (F j.1).parts ∧
      (Tb j).toConvexSpaceBody ≤ Tube.dilate (Tρ j.1) cpar ∧
      (j.2.convexHull_biUnion fun i => (T i).toConvexSpaceBody) ≤ Tube.dilate (Tb j) 2)
    {ε ηp : ℝ} (_hε : 0 ≤ ε) (_hηp : 0 ≤ ηp)
    (hρeq : (ρ : ENNReal) = (δt : ENNReal) ^ (6 * ε))
    (hba : (bp : ENNReal) / (ap : ENNReal) ≤ (δt : ENNReal) ^ (-ηp)) :
    maxDensity tb (fun j => (Tb j).toConvexSpaceBody)
      ≤ (coarsePlank.C : ENNReal) * (δt : ENNReal) ^ (-30 * ε - ηp) := by
  have h := maxDensity_coarse_le_rpow_of_cardPow hdim hδt hδa hab hb1 hbbq hbq T Tρ pρ Tb
    hcard F hdims hcover _hε _hηp hρeq hba
  have hexp : -(6 * ε * (5 : ℝ)) - ηp = -30 * ε - ηp := by ring
  rwa [hexp] at h

/-- **The maximal density of the `b`-tubes at the parent scale `ρ = δ̃ ^ (6 ε)`** (blueprint
`cor:ml1bootCoarsePlankDensityAtRho`).

`Kakeya.ml1Boot.maxDensity_coarse_le_rpow_of_card` with the parent count supplied by
`Kakeya.ml1Boot.card_le`, that is, from the `ρ`-tubes being pairwise essentially distinct
(`hEDρ`) and contained in `B₁` (`hballρ`).

`Kakeya.ml1Boot.card_le` proves the sharper `|t_ρ| ≤ C_{cardBound} ρ ^ (-4)`, and it is
weakened here to the `ρ ^ (-5)` at which the exponent account is budgeted; `ρ ≤ 1` makes that a
weakening. -/
theorem maxDensity_coarse_le_rpow [Nontrivial E] (hdim : Module.finrank ℝ E = 3)
    {δt ap bp bq ρ : NNReal} (hδt : 0 < δt) (hδa : δt ≤ ap) (hab : ap ≤ bp) (hb1 : bp ≤ 1)
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hbbq : bp ≤ bq) (hbq : bq ≤ plankPigeonhole.C * bp)
    {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] {u'' : Finset ι} {tρ : Finset κ}
    {tb : Finset (κ × Finset ι)}
    (T : ι → Tube δt E) (Tρ : κ → Tube ρ E) (pρ : ι → κ)
    (Tb : κ × Finset ι → Tube bq E)
    (hballρ : ∀ m ∈ tρ, (Tρ m).carrier ⊆ Metric.closedBall 0 1)
    (hEDρ : (tρ : Set κ).Pairwise
      fun m m' => IsEssentiallyDistinct (Tρ m).carrier (Tρ m').carrier)
    (F : (m : κ) → ConvexSpaceBody.Factorization (fibre u'' pρ m)
      (fun i => (T i).toConvexSpaceBody) 2)
    (hdims : ∀ m ∈ tρ, IsPlankFamilyOfDimensions plankPigeonhole.C ap bp (F m).parts
      (fun part => part.convexHull_biUnion (fun i => (T i).toConvexSpaceBody)))
    {cpar : ℝ}
    (hcover : ∀ j ∈ tb, j.1 ∈ tρ ∧ j.2 ∈ (F j.1).parts ∧
      (Tb j).toConvexSpaceBody ≤ Tube.dilate (Tρ j.1) cpar ∧
      (j.2.convexHull_biUnion fun i => (T i).toConvexSpaceBody) ≤ Tube.dilate (Tb j) 2)
    {ε ηp : ℝ} (_hε : 0 ≤ ε) (_hηp : 0 ≤ ηp)
    (hρeq : (ρ : ENNReal) = (δt : ENNReal) ^ (6 * ε))
    (hba : (bp : ENNReal) / (ap : ENNReal) ≤ (δt : ENNReal) ^ (-ηp)) :
    maxDensity tb (fun j => (Tb j).toConvexSpaceBody)
      ≤ (coarsePlank.C : ENNReal) * (δt : ENNReal) ^ (-30 * ε - ηp) := by
  have hcard : (tρ.card : ENNReal) ≤ (cardBound.C : ENNReal) * (ρ : ENNReal) ^ (-5 : ℝ) := by
    have hcard4 : (tρ.card : ENNReal) ≤ (cardBound.C : ENNReal) * (ρ : ENNReal) ^ (-4 : ℝ) :=
      card_le hdim hρ0 hρ1 tρ Tρ hballρ hEDρ
    have hweak : (ρ : ENNReal) ^ (-4 : ℝ) ≤ (ρ : ENNReal) ^ (-5 : ℝ) := by
      exact ENNReal.rpow_le_rpow_of_exponent_ge (x := (ρ : ENNReal))
        (y := (-4 : ℝ)) (z := (-5 : ℝ)) (by exact_mod_cast hρ1) (by norm_num)
    exact le_trans hcard4 (mul_le_mul_right hweak (cardBound.C : ENNReal))
  have h := maxDensity_coarse_le_rpow_of_card hdim hδt hδa hab hb1 hbbq hbq T Tρ pρ Tb
    hcard F hdims hcover _hε _hηp hρeq hba
  exact h

end CoarseDensity

end ml1Boot

end Kakeya
