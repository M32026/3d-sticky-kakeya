/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Cap.BroadNarrow

/-!
# The narrow mass accounting of the Cap Lemma (band item A4)

This file is the *narrow* half of the bilinear broad–narrow decomposition behind the Cap Lemma
`L(γ) ⇒ K_KT(γ)` (, verified ,
constants corrected /§2.6). The broad half is band item A3
(`Cap/BroadBound.lean`); the pointwise decomposition it shares with this file is band item A2
(`Cap/BroadNarrow.lean`).

## What is proved

Write `Y_i = (T i).shade`, `U = ⋃_{i ∈ s} Y_i`, `M = ∑_{i ∈ s} |Y_i|`, `λ` for the fullness of
`(s, T)` and `μ` for its multiplicity.

1. **The `U_p` partition.** `narrowPart P s T r k` is the set of narrow points whose *least*
   capturing net direction is the `k`-th, the enumeration of the net `P` being `netEnum P`.
   These sets are measurable (`measurableSet_narrowPart`), pairwise disjoint
   (`pairwiseDisjoint_narrowPart`) and their union is exactly `narrowSet P s T r`
   (`iUnion_narrowPart`). "Least" is what makes the pieces measurable: a bare choice of a
   capturing direction is not a measurable function.
2. **Restricted shadings as `ShadedTube`s.** `capShade Ti S hS` keeps the tube and replaces the
   shade by `Ti.shade ∩ S`; `capShadeFam T S hS` is the family version. Nothing but the shade
   moves, so carriers — hence the *denominator* of the fullness — are untouched.
3. **The localisation engine** `exists_good_piece`: an abstract fullness pigeonhole over a finite
   family of pairwise disjoint measurable "pieces" `A c` with subfamilies `sub c`. Given
   *mass domination* `M ≤ b · ∑_c ∑_{i ∈ sub c} |Y_i ∩ A c|`, a *packing* bound
   `∑_c ∑_{i ∈ sub c} |carrier i| ≤ K · ∑_{i ∈ s} |carrier i|` and a threshold `t` with
   `2 b K t ≤ λ`, some piece `c` is *good* — its restricted subfamily has fullness `≥ t` and
   positive shade mass — and satisfies `μ ≤ 2 b · μ(sub c, Y ∩ A c)`.
4. **`mult_le_max_caps`** (the narrow case): narrow domination `M ≤ 2 ∑_i |Y_i ∩ narrowSet|` gives
   a good cap `p` with `μ ≤ 8 · μ(𝕋_p, Y_p)`. Here `b = 4` (a factor `2` from narrow domination,
   a factor `2` from the pointwise cap capture `m ≤ 2 m_p` on each piece) and `K = C_P`
   (`capPackingConst`), so `2 b = 8` — the constant .
5. **`mult_cap_le_max_columns`** (the column localisation): for a finite family of pairwise
   disjoint measurable columns covering the shades, with each tube meeting at most `K` of the
   column subfamilies, `μ ≤ 2 · μ(𝕋_Q, Y_Q)` for a good column, whose fullness is `≥ λ/(2K)`.

## The cap radius is `4θ`, not `3θ`

 uses cap radius `3θ` and `C_P ≤ 7³`. Both are wrong, as A2 measured:
`Tube.sphere_sep_net` covers the unit sphere only within `2θ` (and separates in the plain norm,
not in `dirDist`), so with transversality threshold `t = 2θ` the cap radius is `r = 4θ` and the
packing constant is

`C_P = capPackingConst E = 2 · C_cov(d)⁻¹ · 10^d · |B(0,1)|`,  `d = finrank ℝ E`,

which is `θ`-free and finite (`capPackingConst_ne_top`). Every statement here takes `r` as a
parameter with the hypothesis `r ≤ 4 * θ`, so no constant is baked in silently.

## Where the constants are *not* hidden

The two headline theorems take the fullness threshold `t` as a parameter, with the single
hypothesis `8 * capPackingConst E * t ≤ λ` (resp. `2 * K * t ≤ λ`). The `λ / (8 C_P)` reading  is the corollary `mult_le_max_caps_div` (resp.
`mult_cap_le_max_columns_div`), which needs no side condition on `C_P` because
`ENNReal.mul_div_le` holds unconditionally. Keeping `t` a parameter means the induction of band
item A6 can carry its own level constants without re-deriving a division.

## What makes the pigeonhole non-vacuous

A bound of the form `μ ≤ 8 · max_p μ_p` over *all* `p` is not the content here — it is the
factor-`4` mass accounting, and it is available with no pigeonhole at all. The content is that
the maximum may be restricted to *good* `p`, i.e. that the surviving cap **inherits the
fullness**: `λ_p ≥ t` with `8 C_P t ≤ λ`, and `C_P` **`θ`-free**. The hypothesis doing that work
is the packing bound `card_filter_dirDist_le` at cap radius `r ≤ 4θ`
(`card_filter_mem_capFamily_le` below): without it, the bad caps could only be charged
`|P|` times over, the threshold would degrade to `λ/(8|P|)` with `|P| ≈ θ^{-(d-1)}`, and the
per-step fullness loss of the induction would stop being absolute — the step would be true and
buy nothing. Positivity of the mass (`hM`) is what forces a good piece to exist at all, and
`S c ≠ 0` is part of "good" precisely so that an *empty* subfamily cannot be counted as good
with fullness `0/0 = 0`.
-/

@[expose] public section

open MeasureTheory Metric Set ENNReal

namespace Kakeya.CapBroadNarrow

/-! ## Enumerating the net -/

section NetEnum

variable {E : Type*}

/-- **An enumeration of a finite set of net directions.** The broad/narrow split of band item A2
takes the net as a `Finset E`; the narrow mass accounting needs to select, for each narrow point,
*one* capturing direction, and it must do so measurably. Choosing the direction of least index
under a fixed enumeration is measurable; a bare `Classical.choice` selection is not. -/
noncomputable def netEnum (P : Finset E) (k : Fin P.card) : E := (P.equivFin.symm k : E)

theorem netEnum_mem (P : Finset E) (k : Fin P.card) : netEnum P k ∈ P :=
  (P.equivFin.symm k).2

theorem netEnum_injective (P : Finset E) : Function.Injective (netEnum P) := by
  intro k l h
  have : P.equivFin.symm k = P.equivFin.symm l := Subtype.ext h
  exact P.equivFin.symm.injective this

theorem exists_netEnum_eq {P : Finset E} {p : E} (hp : p ∈ P) : ∃ k, netEnum P k = p := by
  refine ⟨P.equivFin ⟨p, hp⟩, ?_⟩
  simp [netEnum]

end NetEnum

/-! ## The `U_p` partition of the narrow set -/

section Partition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] {ι : Type*} {δ : NNReal}

/-- **`U_p`, the narrow set localised at one cap.** `x ∈ narrowPart P s T r k` says that `x` is
captured by the `k`-th net direction — at least half the shades through `x` belong to that cap —
and by none of the earlier ones. -/
noncomputable def narrowPart (P : Finset E) (s : Finset ι) (T : ι → ShadedTube δ E) (r : ℝ)
    (k : Fin P.card) : Set E :=
  {x | mult s T x ≤ 2 * multCap s T (netEnum P k) r x ∧
    ∀ j : Fin P.card, j < k → ¬ mult s T x ≤ 2 * multCap s T (netEnum P j) r x}

theorem mem_narrowPart {P : Finset E} {s : Finset ι} {T : ι → ShadedTube δ E} {r : ℝ}
    {k : Fin P.card} {x : E} :
    x ∈ narrowPart P s T r k ↔
      mult s T x ≤ 2 * multCap s T (netEnum P k) r x ∧
        ∀ j : Fin P.card, j < k → ¬ mult s T x ≤ 2 * multCap s T (netEnum P j) r x := Iff.rfl

theorem measurable_two_mul_multCap (s : Finset ι) (T : ι → ShadedTube δ E) (p : E) (r : ℝ) :
    Measurable fun x => 2 * multCap s T p r x :=
  Measurable.of_discrete.comp (measurable_multCap s T p r)

theorem measurableSet_narrowPart (P : Finset E) (s : Finset ι) (T : ι → ShadedTube δ E) (r : ℝ)
    (k : Fin P.card) : MeasurableSet (narrowPart P s T r k) := by
  have hbase : ∀ j : Fin P.card,
      MeasurableSet {x | mult s T x ≤ 2 * multCap s T (netEnum P j) r x} := fun j =>
    measurableSet_le_nat (measurable_mult s T) (measurable_two_mul_multCap s T (netEnum P j) r)
  have hrw : narrowPart P s T r k =
      {x | mult s T x ≤ 2 * multCap s T (netEnum P k) r x} ∩
        ⋂ j : {j : Fin P.card // j < k},
          {x | mult s T x ≤ 2 * multCap s T (netEnum P (j : Fin P.card)) r x}ᶜ := by
    ext x
    simp only [narrowPart, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter, Set.mem_compl_iff]
    constructor
    · exact fun h => ⟨h.1, fun j => h.2 j j.2⟩
    · exact fun h => ⟨h.1, fun j hj => h.2 ⟨j, hj⟩⟩
  rw [hrw]
  exact (hbase k).inter (MeasurableSet.iInter fun j => (hbase (j : Fin P.card)).compl)

theorem narrowPart_subset_narrowSet (P : Finset E) (s : Finset ι) (T : ι → ShadedTube δ E)
    (r : ℝ) (k : Fin P.card) : narrowPart P s T r k ⊆ narrowSet P s T r := by
  intro x hx
  exact ⟨netEnum P k, netEnum_mem P k, hx.1⟩

theorem pairwiseDisjoint_narrowPart (P : Finset E) (s : Finset ι) (T : ι → ShadedTube δ E)
    (r : ℝ) : Pairwise (Function.onFun Disjoint (narrowPart P s T r)) := by
  intro k l hkl
  refine Set.disjoint_left.2 fun x hxk hxl => ?_
  rcases lt_or_gt_of_ne hkl with h | h
  · exact hxl.2 k h hxk.1
  · exact hxk.2 l h hxl.1

theorem iUnion_narrowPart (P : Finset E) (s : Finset ι) (T : ι → ShadedTube δ E) (r : ℝ) :
    (⋃ k : Fin P.card, narrowPart P s T r k) = narrowSet P s T r := by
  refine Set.Subset.antisymm (Set.iUnion_subset fun k => narrowPart_subset_narrowSet P s T r k) ?_
  intro x hx
  obtain ⟨p, hp, hpx⟩ := hx
  obtain ⟨k, hk⟩ := exists_netEnum_eq hp
  have hkQ : mult s T x ≤ 2 * multCap s T (netEnum P k) r x := by rw [hk]; exact hpx
  have hne : ((Finset.univ : Finset (Fin P.card)).filter
      fun j => mult s T x ≤ 2 * multCap s T (netEnum P j) r x).Nonempty :=
    ⟨k, Finset.mem_filter.2 ⟨Finset.mem_univ k, hkQ⟩⟩
  have hk₀mem := Finset.min'_mem _ hne
  rw [Finset.mem_filter] at hk₀mem
  refine Set.mem_iUnion.2 ⟨_, hk₀mem.2, ?_⟩
  intro j hj hjQ
  exact absurd hj (not_lt.2 (Finset.min'_le _ j (Finset.mem_filter.2 ⟨Finset.mem_univ j, hjQ⟩)))

end Partition

/-! ## Restricted shadings -/

section CapShade

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [MeasurableSpace E] {ι : Type*} {δ : NNReal}

/-- **A shaded tube with its shade cut down to a measurable set.** The tube — hence the carrier,
hence the denominator of the fullness — is untouched. This is `Y_p(i) = Y_i ∩ U_p`  as a `ShadedTube`, so the restricted family is again a legitimate input
for `ShadedBody.multiplicity` and `ShadedBody.fullness`. -/
def capShade (Ti : ShadedTube δ E) (S : Set E) (hS : MeasurableSet S) : ShadedTube δ E :=
  { Ti with
    shade := Ti.shade ∩ S
    measurableSet_shade := Ti.measurableSet_shade.inter hS
    shade_subset := Set.Subset.trans Set.inter_subset_left Ti.shade_subset }

@[simp]
theorem capShade_shade (Ti : ShadedTube δ E) (S : Set E) (hS : MeasurableSet S) :
    (capShade Ti S hS).shade = Ti.shade ∩ S := rfl

@[simp]
theorem capShade_toTube (Ti : ShadedTube δ E) (S : Set E) (hS : MeasurableSet S) :
    (capShade Ti S hS).toTube = Ti.toTube := rfl

@[simp]
theorem capShade_carrier (Ti : ShadedTube δ E) (S : Set E) (hS : MeasurableSet S) :
    (capShade Ti S hS).carrier = Ti.carrier := rfl

/-- **The convex body is untouched by `capShade`.** This is what lets band items A5/A6 transport
`ConvexSpaceBody.IsKatzTao` and `Kakeya.maxDensity` to the restricted family for free: the
convex-set density is a statement about the *carriers*, and the carriers are literally the same. -/
@[simp]
theorem capShade_toConvexSpaceBody (Ti : ShadedTube δ E) (S : Set E) (hS : MeasurableSet S) :
    (capShade Ti S hS).toConvexSpaceBody = Ti.toConvexSpaceBody := rfl

/-- The family version of `capShade`. -/
def capShadeFam (T : ι → ShadedTube δ E) (S : Set E) (hS : MeasurableSet S) :
    ι → ShadedTube δ E := fun i => capShade (T i) S hS

@[simp]
theorem capShadeFam_apply (T : ι → ShadedTube δ E) (S : Set E) (hS : MeasurableSet S) (i : ι) :
    capShadeFam T S hS i = capShade (T i) S hS := rfl

end CapShade

/-! ## The mass of a counting function over a measurable set -/

section Mass

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*} {δ : NNReal}

omit [BorelSpace E] in
/-- `m(x)` in `ℝ≥0∞` as a finite sum of `ℝ≥0∞`-valued indicators of the shades. The companion of
A2's `coe_transverseCount`. -/
theorem coe_mult (s : Finset ι) (T : ι → ShadedTube δ E) (x : E) :
    ((mult s T x : ℕ) : ENNReal)
      = ∑ i ∈ s, ((T i).shade).indicator (fun _ => (1 : ENNReal)) x := by
  rw [mult, Nat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : x ∈ (T i).shade <;> simp [h]

/-- **The mass identity.** The integral of the multiplicity function over a set `A` is the total
shade mass inside `A`. This is the bridge between the pointwise decomposition of band item A2 and
the mass accounting below.

**No measurability hypothesis on `A` is needed, and this was measured rather than assumed.** The
first version of this lemma carried `(hA : MeasurableSet A)`; the proof never used it (only the
*shades* have to be measurable, for `setLIntegral_indicator`), and the linter said so. The binder
was removed rather than renamed: an unused hypothesis on a mass identity is exactly the
`Kakeya.ML2Cap.Arith.broad_level` failure shape (`Cap/Arith.lean`, outside this file's import
closure; , re-confirmed by compiler experiment ), where a true statement bought nothing until one checked what the
hypothesis was for. -/
theorem setLIntegral_coe_mult (s : Finset ι) (T : ι → ShadedTube δ E) (A : Set E) :
    ∫⁻ x in A, ((mult s T x : ℕ) : ENNReal) = ∑ i ∈ s, volume ((T i).shade ∩ A) := by
  simp only [coe_mult]
  rw [lintegral_finsetSum s
    (f := fun i (x : E) => ((T i).shade).indicator (fun _ => (1 : ENNReal)) x)
    (fun i _ => Measurable.indicator (f := fun _ : E => (1 : ENNReal)) measurable_const
      (T i).measurableSet_shade)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [setLIntegral_indicator (T i).measurableSet_shade, setLIntegral_one]

/-- **The pointwise cap capture, integrated.** On the piece `U_k` at least half the shades through
each point belong to the `k`-th cap, so at least half the shade mass carried by `U_k` is carried
by the cap subfamily. This is the factor `2` of the `b = 4` in `mult_le_max_caps`. -/
theorem sum_volume_inter_narrowPart_le (P : Finset E) (s : Finset ι) (T : ι → ShadedTube δ E)
    (r : ℝ) (k : Fin P.card) :
    ∑ i ∈ s, volume ((T i).shade ∩ narrowPart P s T r k)
      ≤ 2 * ∑ i ∈ capFamily s T (netEnum P k) r,
          volume ((T i).shade ∩ narrowPart P s T r k) := by
  have hmeas := measurableSet_narrowPart P s T r k
  rw [← setLIntegral_coe_mult s T _, ← setLIntegral_coe_mult _ T _]
  have hmono : ∫⁻ x in narrowPart P s T r k, ((mult s T x : ℕ) : ENNReal)
      ≤ ∫⁻ x in narrowPart P s T r k,
          2 * ((mult (capFamily s T (netEnum P k) r) T x : ℕ) : ENNReal) := by
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem hmeas] with x hx
    have hx1 : mult s T x ≤ 2 * multCap s T (netEnum P k) r x := hx.1
    calc ((mult s T x : ℕ) : ENNReal)
        ≤ ((2 * multCap s T (netEnum P k) r x : ℕ) : ENNReal) := Nat.cast_le.mpr hx1
      _ = 2 * ((mult (capFamily s T (netEnum P k) r) T x : ℕ) : ENNReal) := by
          rw [multCap]; push_cast; ring
  refine hmono.trans_eq ?_
  exact lintegral_const_mul' 2 _ (by simp)

/-- **The narrow mass is captured by the caps, up to a factor `2`.** -/
theorem sum_volume_inter_narrowSet_le (P : Finset E) (s : Finset ι) (T : ι → ShadedTube δ E)
    (r : ℝ) :
    ∑ i ∈ s, volume ((T i).shade ∩ narrowSet P s T r)
      ≤ 2 * ∑ k : Fin P.card, ∑ i ∈ capFamily s T (netEnum P k) r,
          volume ((T i).shade ∩ narrowPart P s T r k) := by
  have hsplit : ∀ i : ι, volume ((T i).shade ∩ narrowSet P s T r)
      = ∑ k : Fin P.card, volume ((T i).shade ∩ narrowPart P s T r k) := by
    intro i
    have hset : (T i).shade ∩ narrowSet P s T r
        = ⋃ k : Fin P.card, ((T i).shade ∩ narrowPart P s T r k) := by
      rw [← Set.inter_iUnion, iUnion_narrowPart]
    rw [hset, measure_iUnion, tsum_fintype]
    · intro k l hkl
      exact ((pairwiseDisjoint_narrowPart P s T r) hkl).mono Set.inter_subset_right
        Set.inter_subset_right
    · exact fun k => (T i).measurableSet_shade.inter (measurableSet_narrowPart P s T r k)
  calc ∑ i ∈ s, volume ((T i).shade ∩ narrowSet P s T r)
      = ∑ i ∈ s, ∑ k : Fin P.card, volume ((T i).shade ∩ narrowPart P s T r k) :=
        Finset.sum_congr rfl fun i _ => hsplit i
    _ = ∑ k : Fin P.card, ∑ i ∈ s, volume ((T i).shade ∩ narrowPart P s T r k) :=
        Finset.sum_comm
    _ ≤ ∑ k : Fin P.card, 2 * ∑ i ∈ capFamily s T (netEnum P k) r,
          volume ((T i).shade ∩ narrowPart P s T r k) :=
        Finset.sum_le_sum fun k _ => sum_volume_inter_narrowPart_le P s T r k
    _ = 2 * ∑ k : Fin P.card, ∑ i ∈ capFamily s T (netEnum P k) r,
          volume ((T i).shade ∩ narrowPart P s T r k) := by rw [Finset.mul_sum]

/-- **The broad/narrow mass split.** `broadSet` is the exact complement of `narrowSet`
(A2's `broadSet_eq_compl_narrowSet`), so the shade mass splits with no loss. -/
theorem sum_volume_inter_narrowSet_add_broadSet (P : Finset E) (s : Finset ι)
    (T : ι → ShadedTube δ E) (r : ℝ) :
    ∑ i ∈ s, volume ((T i).shade ∩ narrowSet P s T r)
        + ∑ i ∈ s, volume ((T i).shade ∩ broadSet P s T r)
      = ∑ i ∈ s, volume (T i).shade := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [broadSet_eq_compl_narrowSet, ← Set.sdiff_eq]
  exact measure_inter_add_sdiff _ (measurableSet_narrowSet P s T r)

/-- **The broad/narrow dichotomy in mass form** — the entry point band item A6 uses to feed either
`mult_le_max_caps` (this file) or the broad bound of band item A3 (`Cap/BroadBound.lean`). One of
the two halves carries at least half the shade mass. -/
theorem narrow_dominated_or_broad_dominated (P : Finset E) (s : Finset ι)
    (T : ι → ShadedTube δ E) (r : ℝ) :
    (∑ i ∈ s, volume (T i).shade
        ≤ 2 * ∑ i ∈ s, volume ((T i).shade ∩ narrowSet P s T r))
      ∨ (∑ i ∈ s, volume (T i).shade
        ≤ 2 * ∑ i ∈ s, volume ((T i).shade ∩ broadSet P s T r)) := by
  have hsum := sum_volume_inter_narrowSet_add_broadSet P s T r
  rcases le_total (∑ i ∈ s, volume ((T i).shade ∩ narrowSet P s T r))
      (∑ i ∈ s, volume ((T i).shade ∩ broadSet P s T r)) with h | h
  · refine Or.inr ?_
    rw [← hsum, two_mul]
    exact add_le_add h le_rfl
  · refine Or.inl ?_
    rw [← hsum, two_mul]
    exact add_le_add le_rfl h

/-- **The broad/narrow dichotomy in the integral form band item A3 asked for.**

 flagged this statement as belonging to no  row: A2
supplies only the *set*-level identity `broadSet = narrowSetᶜ`, and A3's own `hdom` is the broad
branch alone. It is owned here because the narrow branch is this file's, so both sides are proved
in one place and neither is weakened to fit.

It is the same fact as `narrow_dominated_or_broad_dominated`, rewritten through
`setLIntegral_coe_mult`; A3 and band item A6 may use whichever of the two forms their goal is
already in, with no conversion lemma. Stated for an arbitrary `P : Finset E`, which specialises to
`N.points` for a `DirNet E θ`. -/
theorem broad_or_narrow_dominated (P : Finset E) (s : Finset ι) (T : ι → ShadedTube δ E) (r : ℝ) :
    (∑ i ∈ s, volume (T i).shade
        ≤ 2 * ∫⁻ x in broadSet P s T r, ((mult s T x : ℕ) : ENNReal))
      ∨ (∑ i ∈ s, volume (T i).shade
        ≤ 2 * ∫⁻ x in narrowSet P s T r, ((mult s T x : ℕ) : ENNReal)) := by
  rw [setLIntegral_coe_mult, setLIntegral_coe_mult]
  exact (narrow_dominated_or_broad_dominated P s T r).symm

omit [BorelSpace E] in
/-- The shaded union of a restricted family sits inside the restricting set. The transport
statement band item A5 needs in order to place the rescaled family inside one piece. -/
theorem iUnionShade_capShadeFam_subset (u : Finset ι) (T : ι → ShadedTube δ E) (S : Set E)
    (hS : MeasurableSet S) : (⋃ i ∈ u, (capShadeFam T S hS i).shade) ⊆ S :=
  Set.iUnion₂_subset fun _ _ => Set.inter_subset_right

end Mass

/-! ## The packing bound in the form the pigeonhole consumes -/

section Packing

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*} {δ : NNReal}

/-- **Carrier mass counted over the pieces.** If every index lies in at most `K` of the
subfamilies, the total carrier mass of the subfamilies is at most `K` times the family's. -/
theorem sum_carrier_pieces_le {κ : Type*} (C : Finset κ) (sub : κ → Finset ι) (s : Finset ι)
    (T : ι → ShadedTube δ E) {K : ENNReal} (hsub : ∀ c ∈ C, sub c ⊆ s)
    (hcount : ∀ i ∈ s, ((C.filter fun c => i ∈ sub c).card : ENNReal) ≤ K) :
    ∑ c ∈ C, ∑ i ∈ sub c, volume (T i).carrier
      ≤ K * ∑ i ∈ s, volume (T i).carrier := by
  have hstep : ∀ c ∈ C, ∑ i ∈ sub c, volume (T i).carrier
      = ∑ i ∈ s, if i ∈ sub c then volume (T i).carrier else 0 := by
    intro c hc
    rw [← Finset.sum_filter]
    refine Finset.sum_congr (Finset.ext fun i => ?_) fun _ _ => rfl
    simp only [Finset.mem_filter]
    exact ⟨fun h => ⟨hsub c hc h, h⟩, fun h => h.2⟩
  calc ∑ c ∈ C, ∑ i ∈ sub c, volume (T i).carrier
      = ∑ c ∈ C, ∑ i ∈ s, if i ∈ sub c then volume (T i).carrier else 0 :=
        Finset.sum_congr rfl hstep
    _ = ∑ i ∈ s, ∑ c ∈ C, if i ∈ sub c then volume (T i).carrier else 0 := Finset.sum_comm
    _ = ∑ i ∈ s, ((C.filter fun c => i ∈ sub c).card : ENNReal) * volume (T i).carrier := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ i ∈ s, K * volume (T i).carrier :=
        Finset.sum_le_sum fun i hi => mul_le_mul' (hcount i hi) le_rfl
    _ = K * ∑ i ∈ s, volume (T i).carrier := by rw [Finset.mul_sum]

/-- **The cap packing count in the enumerated form.** A single tube direction lies in at most
`capPackingConst E` of the caps of a `θ`-separated net, at cap radius `r ≤ 4θ`. This is A2's
`card_filter_dirDist_le` transported along `netEnum`, and it is the hypothesis that makes the
fullness pigeonhole of `mult_le_max_caps` non-vacuous: the constant is `θ`-free. -/
theorem card_filter_mem_capFamily_le [Nontrivial E] {θ : ℝ} (hθ : 0 < θ) (N : DirNet E θ)
    {r : ℝ} (hr : r ≤ 4 * θ) (s : Finset ι) (T : ι → ShadedTube δ E) (i : ι) :
    (((Finset.univ.filter fun k : Fin N.points.card =>
        i ∈ capFamily s T (netEnum N.points k) r).card : ℕ) : ENNReal)
      ≤ capPackingConst E := by
  refine le_trans (Nat.cast_le.mpr ?_) (card_filter_dirDist_le hθ N (u := (T i).direction) hr)
  refine Finset.card_le_card_of_injOn (netEnum N.points) ?_ ?_
  · intro k hk
    rw [Finset.mem_coe, Finset.mem_filter] at hk
    rw [Finset.mem_coe, Finset.mem_filter]
    exact ⟨netEnum_mem N.points k, (mem_capFamily.1 hk.2).2⟩
  · exact fun k _ l _ h => netEnum_injective N.points h

end Packing

/-! ## The localisation engine -/

section Engine

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*} {δ : NNReal}

/-- **The fullness pigeonhole, abstractly.**

`A c` are finitely many pairwise disjoint measurable pieces, `sub c ⊆ s` the subfamily attached to
the piece `c`, and `capShadeFam T (A c) _` the family `(T i)` with shades cut to `A c`. Given

* *mass domination* `hdom`: the family's total shade mass is at most `b` times the total mass the
  subfamilies carry inside their pieces;
* *packing* `hpack`: the subfamilies' total carrier mass is at most `K` times the family's;
* a *threshold* `t` with `2 b K t ≤ λ`;
* *positive mass* `hM`,

some piece is **good** — its subfamily has fullness `≥ t` and nonzero shade mass — and its
multiplicity controls the family's up to `2 b`.

The `S c ≠ 0` conjunct of "good" is not cosmetic: without it an *empty* subfamily would qualify
(`t * 0 ≤ 0`) with fullness `0 / 0 = 0`, and the fullness conclusion would be vacuous. -/
theorem exists_good_piece {κ : Type*} (C : Finset κ) (A : κ → Set E)
    (hAmeas : ∀ c, MeasurableSet (A c)) (hAdisj : (C : Set κ).PairwiseDisjoint A)
    (s : Finset ι) (T : ι → ShadedTube δ E) (sub : κ → Finset ι)
    (hsub : ∀ c ∈ C, sub c ⊆ s) {b K t : ENNReal}
    (hdom : ∑ i ∈ s, volume (T i).shade
      ≤ b * ∑ c ∈ C, ∑ i ∈ sub c, volume ((T i).shade ∩ A c))
    (hpack : ∑ c ∈ C, ∑ i ∈ sub c, volume (T i).carrier
      ≤ K * ∑ i ∈ s, volume (T i).carrier)
    (hthr : 2 * b * K * t
      ≤ (ShadedBody.fullness s (fun i => (T i).toShadedBody) : ENNReal))
    (hM : ∑ i ∈ s, volume (T i).shade ≠ 0) :
    ∃ c ∈ C,
      (t ≤ (ShadedBody.fullness (sub c)
          (fun i => (capShadeFam T (A c) (hAmeas c) i).toShadedBody) : ENNReal)) ∧
        ShadedBody.multiplicity s (fun i => (T i).toShadedBody)
          ≤ 2 * b * ShadedBody.multiplicity (sub c)
              (fun i => (capShadeFam T (A c) (hAmeas c) i).toShadedBody) := by
  classical
  set Mtot := ∑ i ∈ s, volume (T i).shade with hMtot
  set Ctot := ∑ i ∈ s, volume (T i).carrier with hCtot
  set S : κ → ENNReal := fun c => ∑ i ∈ sub c, volume ((T i).shade ∩ A c) with hS
  set Ccar : κ → ENNReal := fun c => ∑ i ∈ sub c, volume (T i).carrier with hCcar
  set lam := (ShadedBody.fullness s (fun i => (T i).toShadedBody) : ENNReal) with hlam
  -- the family of restricted subfamilies
  set V : κ → ι → ShadedBody E :=
    fun c i => (capShadeFam T (A c) (hAmeas c) i).toShadedBody with hV
  have hVshade : ∀ c i, (V c i).shade = (T i).shade ∩ A c := fun c i => rfl
  have hVcarrier : ∀ c i, (V c i).carrier = (T i).carrier := fun c i => rfl
  have hSeq : ∀ c, S c = ∑ i ∈ sub c, volume (V c i).shade := fun c => rfl
  have hCcareq : ∀ c, Ccar c = ∑ i ∈ sub c, volume (V c i).carrier := fun c => rfl
  -- basic finiteness
  have hCtop : Ctot ≠ ⊤ := ShadedBody.sum_volume_carrier_ne_top s (fun i => (T i).toShadedBody)
  have hMle : Mtot ≤ Ctot :=
    Finset.sum_le_sum fun i _ => measure_mono (T i).shade_subset
  have hMtop : Mtot ≠ ⊤ := ne_top_of_le_ne_top hCtop hMle
  have hmass : Mtot = lam * Ctot :=
    ShadedBody.sum_volumeReal_shade_eq_fullness_mul s (fun i => (T i).toShadedBody)
  -- good and bad pieces
  set G := C.filter (fun c => t * Ccar c ≤ S c ∧ S c ≠ 0) with hG
  set Bd := C.filter (fun c => ¬ (t * Ccar c ≤ S c ∧ S c ≠ 0)) with hBd
  have hsplitsum : ∑ c ∈ C, S c = ∑ c ∈ G, S c + ∑ c ∈ Bd, S c := by
    rw [hG, hBd]
    exact (Finset.sum_filter_add_sum_filter_not C _ S).symm
  -- the bad pieces carry little mass
  have hbadterm : ∀ c ∈ Bd, S c ≤ t * Ccar c := by
    intro c hc
    rw [hBd, Finset.mem_filter] at hc
    by_cases h0 : S c = 0
    · simp [h0]
    · exact le_of_lt (not_le.1 fun h => hc.2 ⟨h, h0⟩)
  have hbad : ∑ c ∈ Bd, S c ≤ t * ∑ c ∈ C, Ccar c := by
    calc ∑ c ∈ Bd, S c ≤ ∑ c ∈ Bd, t * Ccar c := Finset.sum_le_sum hbadterm
      _ = t * ∑ c ∈ Bd, Ccar c := by rw [Finset.mul_sum]
      _ ≤ t * ∑ c ∈ C, Ccar c := by
          refine mul_le_mul' le_rfl (Finset.sum_le_sum_of_subset ?_)
          rw [hBd]; exact Finset.filter_subset _ _
  have hbad2 : 2 * b * ∑ c ∈ Bd, S c ≤ Mtot := by
    calc 2 * b * ∑ c ∈ Bd, S c ≤ 2 * b * (t * ∑ c ∈ C, Ccar c) := mul_le_mul' le_rfl hbad
      _ ≤ 2 * b * (t * (K * Ctot)) := mul_le_mul' le_rfl (mul_le_mul' le_rfl hpack)
      _ = (2 * b * K * t) * Ctot := by ring
      _ ≤ lam * Ctot := mul_le_mul' hthr le_rfl
      _ = Mtot := hmass.symm
  -- the good pieces carry the rest
  have key : Mtot ≤ 2 * b * ∑ c ∈ G, S c := by
    have h1 : Mtot + Mtot ≤ 2 * b * ∑ c ∈ G, S c + Mtot := by
      calc Mtot + Mtot = 2 * Mtot := by ring
        _ ≤ 2 * (b * ∑ c ∈ C, S c) := mul_le_mul' le_rfl hdom
        _ = 2 * b * (∑ c ∈ G, S c + ∑ c ∈ Bd, S c) := by rw [hsplitsum]; ring
        _ = 2 * b * ∑ c ∈ G, S c + 2 * b * ∑ c ∈ Bd, S c := by ring
        _ ≤ 2 * b * ∑ c ∈ G, S c + Mtot := add_le_add le_rfl hbad2
    exact (ENNReal.add_le_add_iff_right hMtop).1 h1
  -- there is a good piece
  have hGne : G.Nonempty := by
    rcases Finset.eq_empty_or_nonempty G with h | h
    · rw [h, Finset.sum_empty, mul_zero, le_zero_iff] at key
      exact absurd key hM
    · exact h
  obtain ⟨c₀, hc₀, hmax⟩ :=
    Finset.exists_max_image G (fun c => ShadedBody.multiplicity (sub c) (V c)) hGne
  have hc₀C : c₀ ∈ C := Finset.mem_of_mem_filter _ (hG ▸ hc₀)
  have hc₀good : t * Ccar c₀ ≤ S c₀ ∧ S c₀ ≠ 0 := by
    rw [hG, Finset.mem_filter] at hc₀; exact hc₀.2
  refine ⟨c₀, hc₀C, ?_, ?_⟩
  · -- fullness of the good piece
    have hCne : Ccar c₀ ≠ 0 := by
      intro h
      have hle : S c₀ ≤ Ccar c₀ :=
        Finset.sum_le_sum fun i _ => measure_mono (V c₀ i).shade_subset
      rw [h] at hle
      exact hc₀good.2 (by simpa using hle)
    have hCctop : Ccar c₀ ≠ ⊤ :=
      ShadedBody.sum_volume_carrier_ne_top (sub c₀) (V c₀)
    have hfull : (ShadedBody.fullness (sub c₀) (V c₀) : ENNReal) = S c₀ / Ccar c₀ :=
      ShadedBody.fullness_def (sub c₀) (V c₀)
    rw [show (fun i => (capShadeFam T (A c₀) (hAmeas c₀) i).toShadedBody) = V c₀ from rfl, hfull]
    exact (ENNReal.le_div_iff_mul_le (Or.inl hCne) (Or.inl hCctop)).2 hc₀good.1
  · -- multiplicity of the good piece
    set W : κ → Set E := fun c => ⋃ i ∈ sub c, (V c i).shade with hW
    have hWsub : ∀ c ∈ C, W c ⊆ ⋃ i ∈ s, (T i).shade := by
      intro c hc
      refine Set.iUnion₂_subset fun i hi => ?_
      intro x hx
      rw [hVshade] at hx
      exact Set.mem_iUnion₂.2 ⟨i, hsub c hc hi, hx.1⟩
    have hWA : ∀ c, W c ⊆ A c := by
      intro c
      refine Set.iUnion₂_subset fun i _ => ?_
      rw [hVshade]; exact Set.inter_subset_right
    have hWmeas : ∀ c, MeasurableSet (W c) := by
      intro c
      exact MeasurableSet.biUnion (Finset.countable_toSet _) fun i _ => (V c i).measurableSet_shade
    have hGC : G ⊆ C := by rw [hG]; exact Finset.filter_subset _ _
    have hWdisj : (G : Set κ).PairwiseDisjoint W := by
      intro c hc c' hc' hne
      exact (hAdisj (hGC hc) (hGC hc') hne).mono (hWA c) (hWA c')
    have hsumW : ∑ c ∈ G, volume (W c) ≤ volume (⋃ i ∈ s, (T i).shade) := by
      rw [← measure_biUnion_finset hWdisj fun c _ => hWmeas c]
      exact measure_mono (Set.iUnion₂_subset fun c hc => hWsub c (hGC hc))
    have hSmul : ∀ c, S c = ShadedBody.multiplicity (sub c) (V c) * volume (W c) := by
      intro c
      rw [hSeq]
      exact ShadedBody.sum_shade_eq_multiplicity_mul_union (sub c) (V c)
    have hchain : Mtot ≤ (2 * b * ShadedBody.multiplicity (sub c₀) (V c₀))
        * volume (⋃ i ∈ s, (T i).shade) := by
      calc Mtot ≤ 2 * b * ∑ c ∈ G, S c := key
        _ = 2 * b * ∑ c ∈ G, ShadedBody.multiplicity (sub c) (V c) * volume (W c) := by
            simp only [hSmul]
        _ ≤ 2 * b * ∑ c ∈ G, ShadedBody.multiplicity (sub c₀) (V c₀) * volume (W c) := by
            refine mul_le_mul' le_rfl (Finset.sum_le_sum fun c hc => ?_)
            exact mul_le_mul' (hmax c hc) le_rfl
        _ = 2 * b * (ShadedBody.multiplicity (sub c₀) (V c₀) * ∑ c ∈ G, volume (W c)) := by
            rw [← Finset.mul_sum]
        _ ≤ 2 * b * (ShadedBody.multiplicity (sub c₀) (V c₀)
              * volume (⋃ i ∈ s, (T i).shade)) := mul_le_mul' le_rfl (mul_le_mul' le_rfl hsumW)
        _ = (2 * b * ShadedBody.multiplicity (sub c₀) (V c₀))
              * volume (⋃ i ∈ s, (T i).shade) := by ring
    rw [show (fun i => (capShadeFam T (A c₀) (hAmeas c₀) i).toShadedBody) = V c₀ from rfl]
    exact (ShadedBody.multiplicity_le_iff s (fun i => (T i).toShadedBody)).2 hchain

end Engine

/-! ## The narrow case -/

section NarrowCase

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*} {δ : NNReal}

/-- **`mult_le_max_caps` — the narrow half of the broad/narrow dichotomy.**

If the narrow set carries at least half the shade mass, then some cap of the net is *good* — its
restricted subfamily `(𝕋_p, Y_p)` has fullness at least `t` and nonzero mass — and

`μ(s, T) ≤ 8 · μ(𝕋_p, Y_p)`.

The constant `8` is `2 b` with `b = 4`: a factor `2` from narrow domination and a factor `2` from
the pointwise cap capture `m ≤ 2 m_p` on each piece `U_p`
(`sum_volume_inter_narrowPart_le`). The threshold hypothesis is
`8 * capPackingConst E * t ≤ λ`, i.e. `t = λ / (8 C_P)` 's notation —
see `mult_le_max_caps_div`.

**Cap radius.** `r ≤ 4 * θ`, not `3 * θ`: `Tube.sphere_sep_net`'s cover radius is `2θ`
.

**What makes this non-vacuous.** The hypothesis that does the work is `hr : r ≤ 4 * θ`, through
`card_filter_mem_capFamily_le`: it is what bounds the number of caps a single tube belongs to by
the `θ`-free constant `capPackingConst E`, and hence what makes the surviving cap's fullness
threshold `t ≈ λ / (8 C_P)` an absolute loss rather than a `θ`-dependent one. -/
theorem mult_le_max_caps [Nontrivial E] {θ : ℝ} (hθ : 0 < θ) (N : DirNet E θ) {r : ℝ}
    (hr : r ≤ 4 * θ) (s : Finset ι) (T : ι → ShadedTube δ E) {t : ENNReal}
    (hthr : 8 * capPackingConst E * t
      ≤ (ShadedBody.fullness s (fun i => (T i).toShadedBody) : ENNReal))
    (hM : ∑ i ∈ s, volume (T i).shade ≠ 0)
    (hnar : ∑ i ∈ s, volume (T i).shade
      ≤ 2 * ∑ i ∈ s, volume ((T i).shade ∩ narrowSet N.points s T r)) :
    ∃ k : Fin N.points.card,
      (t ≤ (ShadedBody.fullness (capFamily s T (netEnum N.points k) r)
          (fun i => (capShadeFam T (narrowPart N.points s T r k)
            (measurableSet_narrowPart N.points s T r k) i).toShadedBody) : ENNReal)) ∧
        ShadedBody.multiplicity s (fun i => (T i).toShadedBody)
          ≤ 8 * ShadedBody.multiplicity (capFamily s T (netEnum N.points k) r)
              (fun i => (capShadeFam T (narrowPart N.points s T r k)
                (measurableSet_narrowPart N.points s T r k) i).toShadedBody) := by
  set P := N.points with hP
  have h24 : (2 : ENNReal) * 4 = 8 := by norm_num
  obtain ⟨k, -, hk⟩ :=
    exists_good_piece (Finset.univ : Finset (Fin P.card)) (narrowPart P s T r)
      (measurableSet_narrowPart P s T r)
      (fun c _ c' _ hne => (pairwiseDisjoint_narrowPart P s T r) hne)
      s T (fun k => capFamily s T (netEnum P k) r)
      (fun k _ => capFamily_subset s T (netEnum P k) r)
      (b := 4) (K := capPackingConst E) (t := t)
      (by
        calc ∑ i ∈ s, volume (T i).shade
            ≤ 2 * ∑ i ∈ s, volume ((T i).shade ∩ narrowSet P s T r) := hnar
          _ ≤ 2 * (2 * ∑ k : Fin P.card, ∑ i ∈ capFamily s T (netEnum P k) r,
                volume ((T i).shade ∩ narrowPart P s T r k)) :=
              mul_le_mul' le_rfl (sum_volume_inter_narrowSet_le P s T r)
          _ = 4 * ∑ k ∈ (Finset.univ : Finset (Fin P.card)),
                ∑ i ∈ capFamily s T (netEnum P k) r,
                  volume ((T i).shade ∩ narrowPart P s T r k) := by ring)
      (sum_carrier_pieces_le _ _ s T (fun k _ => capFamily_subset s T (netEnum P k) r)
        (fun i _ => card_filter_mem_capFamily_le hθ N hr s T i))
      (by rw [h24]; exact hthr) hM
  exact ⟨k, hk.1, by rw [h24] at hk; exact hk.2⟩

/-- `mult_le_max_caps` at the explicit threshold `λ / (8 C_P)` . No
side condition on `capPackingConst E` is needed: `ENNReal.mul_div_le` is unconditional. -/
theorem mult_le_max_caps_div [Nontrivial E] {θ : ℝ} (hθ : 0 < θ) (N : DirNet E θ) {r : ℝ}
    (hr : r ≤ 4 * θ) (s : Finset ι) (T : ι → ShadedTube δ E)
    (hM : ∑ i ∈ s, volume (T i).shade ≠ 0)
    (hnar : ∑ i ∈ s, volume (T i).shade
      ≤ 2 * ∑ i ∈ s, volume ((T i).shade ∩ narrowSet N.points s T r)) :
    ∃ k : Fin N.points.card,
      ((ShadedBody.fullness s (fun i => (T i).toShadedBody) : ENNReal)
            / (8 * capPackingConst E)
          ≤ (ShadedBody.fullness (capFamily s T (netEnum N.points k) r)
          (fun i => (capShadeFam T (narrowPart N.points s T r k)
            (measurableSet_narrowPart N.points s T r k) i).toShadedBody) : ENNReal)) ∧
        ShadedBody.multiplicity s (fun i => (T i).toShadedBody)
          ≤ 8 * ShadedBody.multiplicity (capFamily s T (netEnum N.points k) r)
              (fun i => (capShadeFam T (narrowPart N.points s T r k)
                (measurableSet_narrowPart N.points s T r k) i).toShadedBody) :=
  mult_le_max_caps hθ N hr s T ENNReal.mul_div_le hM hnar

/-- `mult_le_max_caps` with the narrow-domination hypothesis in the *integral* form, i.e. the exact
shape produced by `broad_or_narrow_dominated`'s right disjunct and by band item A3's own integral
form of `mult` (in `Cap/BroadBound.lean`, which is *not* in this file's import closure — a forward
reference, cited as such). No mathematical content beyond `setLIntegral_coe_mult`; it exists so
that band item A6's assembly does not have to convert. -/
theorem mult_le_max_caps_of_lintegral [Nontrivial E] {θ : ℝ} (hθ : 0 < θ) (N : DirNet E θ)
    {r : ℝ} (hr : r ≤ 4 * θ) (s : Finset ι) (T : ι → ShadedTube δ E) {t : ENNReal}
    (hthr : 8 * capPackingConst E * t
      ≤ (ShadedBody.fullness s (fun i => (T i).toShadedBody) : ENNReal))
    (hM : ∑ i ∈ s, volume (T i).shade ≠ 0)
    (hnar : ∑ i ∈ s, volume (T i).shade
      ≤ 2 * ∫⁻ x in narrowSet N.points s T r, ((mult s T x : ℕ) : ENNReal)) :
    ∃ k : Fin N.points.card,
      (t ≤ (ShadedBody.fullness (capFamily s T (netEnum N.points k) r)
          (fun i => (capShadeFam T (narrowPart N.points s T r k)
            (measurableSet_narrowPart N.points s T r k) i).toShadedBody) : ENNReal)) ∧
        ShadedBody.multiplicity s (fun i => (T i).toShadedBody)
          ≤ 8 * ShadedBody.multiplicity (capFamily s T (netEnum N.points k) r)
              (fun i => (capShadeFam T (narrowPart N.points s T r k)
                (measurableSet_narrowPart N.points s T r k) i).toShadedBody) :=
  mult_le_max_caps hθ N hr s T hthr hM (by rwa [setLIntegral_coe_mult] at hnar)

end NarrowCase

/-! ## The column localisation -/

section Columns

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type*} {δ : NNReal}

/-- **`mult_cap_le_max_columns` — the column localisation inside one cap.**

`Q` are finitely many pairwise disjoint measurable columns whose union covers every shade of the
family, and `sub Q` is a subfamily containing every tube whose shade meets `Q`. If no tube meets
more than `K` of the subfamilies, then some column is good — its subfamily has fullness `≥ t` and
nonzero mass — and `μ ≤ 2 · μ(𝕋_Q, Y_Q)`.

**Constants.**  prices this step at `8 · 9 = 72` on the multiplicity and
`λ / (8 C_P · 72)` on the fullness. The achieved constants are better and the reason is
structural: the columns *partition* the shades exactly, so there is no capture loss at all
(`b = 1`), and the only loss is the `K`-fold over-counting of carriers in the pigeonhole. Hence
`2 b = 2` on the multiplicity and `λ / (2 K)` on the fullness — `λ / 18` at the intended `K = 9`.

**The geometric input, named.** `hcount` — each tube of the cap meets at most `K` columns — is
the caller's geometry, and it is band item A5's obligation: for columns of side `4θ` transverse
to `p` and a cap of radius `4θ` at scale `δ ≤ θ / 2`, `K = 9` in `ℝ³`. It is a genuine
hypothesis with a named owner, not a hypothesis added to make the statement typecheck; the mass
accounting below is complete without it except for that one count. -/
theorem mult_cap_le_max_columns {κ : Type*} (C : Finset κ) (A : κ → Set E)
    (hAmeas : ∀ c, MeasurableSet (A c)) (hAdisj : (C : Set κ).PairwiseDisjoint A)
    (s : Finset ι) (T : ι → ShadedTube δ E) (sub : κ → Finset ι)
    (hsub : ∀ c ∈ C, sub c ⊆ s)
    (hcover : ∀ i ∈ s, (T i).shade ⊆ ⋃ c ∈ C, A c)
    (hsupp : ∀ c ∈ C, ∀ i ∈ s, ((T i).shade ∩ A c).Nonempty → i ∈ sub c)
    {K t : ENNReal}
    (hcount : ∀ i ∈ s, ((C.filter fun c => i ∈ sub c).card : ENNReal) ≤ K)
    (hthr : 2 * K * t ≤ (ShadedBody.fullness s (fun i => (T i).toShadedBody) : ENNReal))
    (hM : ∑ i ∈ s, volume (T i).shade ≠ 0) :
    ∃ c ∈ C,
      (t ≤ (ShadedBody.fullness (sub c)
          (fun i => (capShadeFam T (A c) (hAmeas c) i).toShadedBody) : ENNReal)) ∧
        ShadedBody.multiplicity s (fun i => (T i).toShadedBody)
          ≤ 2 * ShadedBody.multiplicity (sub c)
              (fun i => (capShadeFam T (A c) (hAmeas c) i).toShadedBody) := by
  have hsplit : ∀ i ∈ s, volume (T i).shade
      = ∑ c ∈ C, volume ((T i).shade ∩ A c) := by
    intro i hi
    have hset : (T i).shade = ⋃ c ∈ C, ((T i).shade ∩ A c) := by
      rw [← Set.inter_iUnion₂]
      exact (Set.inter_eq_left.2 (hcover i hi)).symm
    have hmb : volume (⋃ c ∈ C, ((T i).shade ∩ A c))
        = ∑ c ∈ C, volume ((T i).shade ∩ A c) := by
      refine measure_biUnion_finset ?_ ?_
      · intro c hc c' hc' hne
        exact (hAdisj hc hc' hne).mono Set.inter_subset_right Set.inter_subset_right
      · exact fun c _ => (T i).measurableSet_shade.inter (hAmeas c)
    conv_lhs => rw [hset]
    exact hmb
  have hinner : ∀ c ∈ C, ∑ i ∈ s, volume ((T i).shade ∩ A c)
      = ∑ i ∈ sub c, volume ((T i).shade ∩ A c) := by
    intro c hc
    refine (Finset.sum_subset (hsub c hc) ?_).symm
    intro i hi hni
    rw [Set.not_nonempty_iff_eq_empty.1 (fun h => hni (hsupp c hc i hi h))]
    simp
  have heq : ∑ i ∈ s, volume (T i).shade
      = ∑ c ∈ C, ∑ i ∈ sub c, volume ((T i).shade ∩ A c) :=
    calc ∑ i ∈ s, volume (T i).shade
        = ∑ i ∈ s, ∑ c ∈ C, volume ((T i).shade ∩ A c) := Finset.sum_congr rfl hsplit
      _ = ∑ c ∈ C, ∑ i ∈ s, volume ((T i).shade ∩ A c) := Finset.sum_comm
      _ = ∑ c ∈ C, ∑ i ∈ sub c, volume ((T i).shade ∩ A c) := Finset.sum_congr rfl hinner
  have hdom : ∑ i ∈ s, volume (T i).shade
      ≤ 1 * ∑ c ∈ C, ∑ i ∈ sub c, volume ((T i).shade ∩ A c) := by
    rw [one_mul]; exact le_of_eq heq
  obtain ⟨c₀, hc₀, hgood⟩ :=
    exists_good_piece C A hAmeas hAdisj s T sub hsub (b := 1) (K := K) (t := t) hdom
      (sum_carrier_pieces_le C sub s T hsub hcount) (by simpa using hthr) hM
  exact ⟨c₀, hc₀, hgood.1, by simpa using hgood.2⟩

/-- `mult_cap_le_max_columns` at the explicit threshold `λ / (2 K)`. -/
theorem mult_cap_le_max_columns_div {κ : Type*} (C : Finset κ) (A : κ → Set E)
    (hAmeas : ∀ c, MeasurableSet (A c)) (hAdisj : (C : Set κ).PairwiseDisjoint A)
    (s : Finset ι) (T : ι → ShadedTube δ E) (sub : κ → Finset ι)
    (hsub : ∀ c ∈ C, sub c ⊆ s)
    (hcover : ∀ i ∈ s, (T i).shade ⊆ ⋃ c ∈ C, A c)
    (hsupp : ∀ c ∈ C, ∀ i ∈ s, ((T i).shade ∩ A c).Nonempty → i ∈ sub c)
    {K : ENNReal}
    (hcount : ∀ i ∈ s, ((C.filter fun c => i ∈ sub c).card : ENNReal) ≤ K)
    (hM : ∑ i ∈ s, volume (T i).shade ≠ 0) :
    ∃ c ∈ C,
      ((ShadedBody.fullness s (fun i => (T i).toShadedBody) : ENNReal) / (2 * K)
          ≤ (ShadedBody.fullness (sub c)
          (fun i => (capShadeFam T (A c) (hAmeas c) i).toShadedBody) : ENNReal)) ∧
        ShadedBody.multiplicity s (fun i => (T i).toShadedBody)
          ≤ 2 * ShadedBody.multiplicity (sub c)
              (fun i => (capShadeFam T (A c) (hAmeas c) i).toShadedBody) :=
  mult_cap_le_max_columns C A hAmeas hAdisj s T sub hsub hcover hsupp hcount
    ENNReal.mul_div_le hM

end Columns

end Kakeya.CapBroadNarrow
