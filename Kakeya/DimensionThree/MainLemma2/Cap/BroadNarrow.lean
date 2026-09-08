/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Tube.Nets
public import Kakeya.Tube.Dilate
public import Kakeya.Multiplicity

/-!
# The pointwise broad/narrow decomposition of the Cap Lemma (band item A2)

This file sets up the *pointwise* half of the bilinear broad–narrow decomposition used in the
Cap Lemma `L(γ) ⇒ K_KT(γ)` (, verified ).
Nothing here is analytic: every statement is a pointwise or finite-combinatorial fact about a
finite family of shaded tubes, plus the measurability of the two counting functions that the
integration step (band item A3) consumes.

## The angular quantity

Tube directions are only defined up to sign (`Tube.reverse` has direction `-d` and the same
carrier), so the angular distance used throughout is

`dirDist u v = min ‖u - v‖ ‖u + v‖`,

which is *exactly* the quantity appearing in `Tube.volume_inter_le_of_angle`
(`Kakeya/Tube/IntersectionVolume.lean`); `dirDist_tube` records that identification. `dirDist` is
symmetric, sign-blind and satisfies the triangle inequality (`dirDist_triangle`), which is all the
decomposition needs.

## The net

`DirNet E θ` bundles what `Tube.sphere_sep_net` produces: a finite set of unit vectors which is
`θ`-separated **in `‖·‖`** and covers the unit sphere within `2 * θ`, again in `‖·‖`.

**Sign convention, measured rather than assumed.** `Tube.sphere_sep_net`
(`Kakeya/Tube/Nets.lean:465`) is stated with the *plain* norm `‖a - b‖` on both the separation and
the covering clause — it is **not** sign-blind, and its covering radius is `2 * θ`, not `θ`. Both
readings matter:

* the covering clause `‖u - p‖ ≤ 2 * θ` implies `dirDist u p ≤ 2 * θ` (`DirNet.cover_dirDist`),
  so covering transfers to `dirDist` for free;
* the separation clause does **not** transfer: `p` and `-p` may both be net points, and they are
  `2`-separated in `‖·‖` while `dirDist p (-p) = 0`. Hence the packing count of the caps
  (`card_filter_dirDist_le`) is run on the two *sign branches* separately and pays a factor `2`.

Because the cover radius is `2 * θ` rather than `θ`, the cap radius in the broad/narrow split must
be `t + 2 * θ` where `t` is the transversality threshold — this is the constant correction flagged
 ("`sphere_sep_net` is a `θ`-separated `2θ`-net"). All statements below take
the cap radius `r` as a parameter together with the hypothesis `t + 2 * θ ≤ r`, so the caller
fixes the constants.

## The counting functions

`mult s T x` is `m(x) = #{i ∈ s : x ∈ Y_i}` and `multCap s T p r x` is
`m_p(x) = #{i ∈ s : x ∈ Y_i, dirDist (T i).direction p ≤ r}`, both **`ℕ`-valued**. They are
*defined* as finite sums of `Set.indicator`s of the shades rather than as `Finset.filter` cards:
that is what makes `Measurable` immediate (`measurable_mult`, `measurable_multCap`) from
`MeasurableSet (T i).shade`, with no decidability side conditions. `mult_eq_card_filter` is the
bridge to the `Finset.filter` form used by the combinatorics.

## The decomposition

`x` is **narrow** if some net direction captures at least half the shades through `x`, and
**broad** otherwise; `broadSet_eq_compl_narrowSet` records that the two sets partition the space,
and both are measurable.

The main output is `broad_sq_le_two_mul_transverse_pairs`: pointwise on the broad set,
`m(x) ^ 2 ≤ 2 * ∑_{(i,j) transverse} 1_{Y_i ∩ Y_j}(x)`. `enn_broad_sq_le_two_mul_transverse_pairs`
is the same statement pushed into `ℝ≥0∞`, which is the form band item A3 integrates.

## What is *not* here

The integration (`∫⁻_B m ^ 2 ≤ 2 ∑ |T_i ∩ T_j|`), the Cauchy–Schwarz step, the narrow mass
accounting and the cap rescaling are items A3–A5 and are not touched.
-/

@[expose] public section

open MeasureTheory Metric Set Module

namespace Kakeya.CapBroadNarrow

/-! ## The sign-blind angular distance -/

section DirDist

variable {E : Type*} [SeminormedAddCommGroup E]

/-- **Angular distance modulo sign**, `∠(u, v) = min ‖u - v‖ ‖u + v‖`.

For unit vectors this is comparable to the angle between the lines `ℝ ∙ u` and `ℝ ∙ v`, and it is
literally the quantity bounding a two-tube intersection in
`Tube.volume_inter_le_of_angle`. Tube directions are only well defined up to sign, so this — and
not `‖u - v‖` — is the quantity the broad/narrow decomposition must be phrased in. -/
noncomputable def dirDist (u v : E) : ℝ := min ‖u - v‖ ‖u + v‖

theorem dirDist_comm (u v : E) : dirDist u v = dirDist v u := by
  unfold dirDist
  rw [norm_sub_rev, add_comm]

theorem dirDist_nonneg (u v : E) : 0 ≤ dirDist u v :=
  le_min (norm_nonneg _) (norm_nonneg _)

theorem dirDist_le_norm_sub (u v : E) : dirDist u v ≤ ‖u - v‖ := min_le_left _ _

theorem dirDist_le_norm_add (u v : E) : dirDist u v ≤ ‖u + v‖ := min_le_right _ _

@[simp]
theorem dirDist_self (u : E) : dirDist u u = 0 := by
  have h : dirDist u u ≤ ‖u - u‖ := dirDist_le_norm_sub u u
  simp only [sub_self, norm_zero] at h
  exact le_antisymm h (dirDist_nonneg u u)

@[simp]
theorem dirDist_neg_right (u v : E) : dirDist u (-v) = dirDist u v := by
  unfold dirDist
  rw [sub_neg_eq_add, ← sub_eq_add_neg]
  exact min_comm _ _

@[simp]
theorem dirDist_neg_left (u v : E) : dirDist (-u) v = dirDist u v := by
  rw [dirDist_comm, dirDist_neg_right, dirDist_comm]

/-- **The triangle inequality for `dirDist`.** The four sign combinations all reduce to
`norm_add_le` after writing the relevant difference as a sum of two differences. -/
theorem dirDist_triangle (u v w : E) : dirDist u w ≤ dirDist u v + dirDist v w := by
  have hsub : ∀ a b c : E, ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖ := fun a b c => by
    have : a - c = (a - b) + (b - c) := by abel
    rw [this]; exact norm_add_le _ _
  have haddadd : ∀ a b c : E, ‖a + c‖ ≤ ‖a - b‖ + ‖b + c‖ := fun a b c => by
    have : a + c = (a - b) + (b + c) := by abel
    rw [this]; exact norm_add_le _ _
  have haddsub : ∀ a b c : E, ‖a + c‖ ≤ ‖a + b‖ + ‖b - c‖ := fun a b c => by
    have : a + c = (a + b) + (c - b) := by abel
    rw [this]
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_sub_rev]
  have hsubadd : ∀ a b c : E, ‖a - c‖ ≤ ‖a + b‖ + ‖b + c‖ := fun a b c => by
    have : a - c = (a + b) - (b + c) := by abel
    rw [this]
    exact norm_sub_le _ _
  rcases le_total ‖u - v‖ ‖u + v‖ with h1 | h1 <;>
    rcases le_total ‖v - w‖ ‖v + w‖ with h2 | h2
  · calc dirDist u w ≤ ‖u - w‖ := dirDist_le_norm_sub u w
      _ ≤ ‖u - v‖ + ‖v - w‖ := hsub u v w
      _ = dirDist u v + dirDist v w := by
          rw [dirDist, dirDist, min_eq_left h1, min_eq_left h2]
  · calc dirDist u w ≤ ‖u + w‖ := dirDist_le_norm_add u w
      _ ≤ ‖u - v‖ + ‖v + w‖ := haddadd u v w
      _ = dirDist u v + dirDist v w := by
          rw [dirDist, dirDist, min_eq_left h1, min_eq_right h2]
  · calc dirDist u w ≤ ‖u + w‖ := dirDist_le_norm_add u w
      _ ≤ ‖u + v‖ + ‖v - w‖ := haddsub u v w
      _ = dirDist u v + dirDist v w := by
          rw [dirDist, dirDist, min_eq_right h1, min_eq_left h2]
  · calc dirDist u w ≤ ‖u - w‖ := dirDist_le_norm_sub u w
      _ ≤ ‖u + v‖ + ‖v + w‖ := hsubadd u v w
      _ = dirDist u v + dirDist v w := by
          rw [dirDist, dirDist, min_eq_right h1, min_eq_right h2]

end DirDist

/-- **`dirDist` is the angular quantity of the two-tube intersection bound.** Definitional, but
recorded so that band item A3 can rewrite `Tube.volume_inter_le_of_angle` into `dirDist` form
without unfolding anything. -/
theorem dirDist_tube {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {δ : NNReal} (T₁ T₂ : Tube δ E) :
    dirDist T₁.direction T₂.direction
      = min ‖T₁.direction - T₂.direction‖ ‖T₁.direction + T₂.direction‖ := rfl

/-! ## The separated direction net -/

/-- **A `θ`-separated `2θ`-net of unit directions**, i.e. exactly the datum
`Tube.sphere_sep_net` produces. Both clauses are in the plain norm `‖·‖`, as the source lemma
states them; `DirNet.cover_dirDist` weakens the covering clause to `dirDist`. -/
structure DirNet (E : Type*) [SeminormedAddCommGroup E] (θ : ℝ) where
  /-- The net points. -/
  points : Finset E
  /-- Every net point is a unit vector. -/
  norm_eq_one : ∀ p ∈ points, ‖p‖ = 1
  /-- Distinct net points are `θ`-separated in the plain norm. -/
  sep : ∀ p ∈ points, ∀ q ∈ points, p ≠ q → θ ≤ ‖p - q‖
  /-- The net covers the unit sphere within `2 * θ` in the plain norm. -/
  cover : ∀ u : E, ‖u‖ = 1 → ∃ p ∈ points, ‖u - p‖ ≤ 2 * θ

namespace DirNet

variable {E : Type*} [SeminormedAddCommGroup E] {θ : ℝ}

/-- The covering clause, read in `dirDist`. -/
theorem cover_dirDist (N : DirNet E θ) (u : E) (hu : ‖u‖ = 1) :
    ∃ p ∈ N.points, dirDist u p ≤ 2 * θ := by
  obtain ⟨p, hp, hup⟩ := N.cover u hu
  exact ⟨p, hp, le_trans (dirDist_le_norm_sub u p) hup⟩

end DirNet

/-- **A `θ`-separated `2θ`-net of unit directions exists**, from `Tube.sphere_sep_net`. -/
theorem exists_dirNet {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) : Nonempty (DirNet E θ) := by
  obtain ⟨D, hunit, hsep, hcover⟩ := Tube.sphere_sep_net (E := E) hθ hθ1
  exact ⟨⟨D, hunit, hsep, hcover⟩⟩


/-! ## Indicator sums as cardinalities -/

/-- A finite sum of `ℕ`-valued indicators, evaluated at `x`, counts the indices whose set
contains `x`. This is the only bridge needed between the measurability-friendly definition of the
counting functions (indicator sums) and their combinatorial form (`Finset.filter` cards). -/
theorem sum_indicator_eq_card_filter {E : Type*} {κ : Type*} (u : Finset κ) (A : κ → Set E)
    (x : E) [DecidablePred fun k => x ∈ A k] :
    ∑ k ∈ u, (A k).indicator (fun _ => (1 : ℕ)) x = (u.filter fun k => x ∈ A k).card := by
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases h : x ∈ A k <;> simp [h]

/-! ## The counting functions `m` and `m_p` -/

section Counting

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] {ι : Type*} {δ : NNReal}

/-- **`m(x)`**: the number of shades of the family `(s, T)` that contain `x`.

Defined as a finite sum of `ℕ`-valued indicators of the shades. That is deliberate: it makes
`Measurable (mult s T)` (`measurable_mult`) a one-liner from `MeasurableSet (T i).shade` with no
decidability hypothesis anywhere, which is what band item A3 needs in order to integrate `m ^ 2`.
`mult_eq_card_filter` recovers the `Finset.filter` reading. -/
noncomputable def mult (s : Finset ι) (T : ι → ShadedTube δ E) (x : E) : ℕ :=
  ∑ i ∈ s, ((T i).shade).indicator (fun _ => (1 : ℕ)) x

/-- `m(x) = #{i ∈ s : x ∈ Y_i}`. -/
theorem mult_eq_card_filter (s : Finset ι) (T : ι → ShadedTube δ E) (x : E)
    [DecidablePred fun i => x ∈ (T i).shade] :
    mult s T x = (s.filter fun i => x ∈ (T i).shade).card :=
  sum_indicator_eq_card_filter s (fun i => (T i).shade) x

/-- **`m` is measurable** as an `ℕ`-valued function. -/
theorem measurable_mult (s : Finset ι) (T : ι → ShadedTube δ E) : Measurable (mult s T) :=
  Finset.measurable_sum s fun i _ => measurable_const.indicator (T i).measurableSet_shade

/-- **`m` is measurable** after the coercion into `ℝ≥0∞` — the form band item A3 integrates. -/
theorem measurable_coe_mult (s : Finset ι) (T : ι → ShadedTube δ E) :
    Measurable fun x => ((mult s T x : ℕ) : ENNReal) :=
  Measurable.of_discrete.comp (measurable_mult s T)

theorem mult_mono {s s' : Finset ι} (h : s ⊆ s') (T : ι → ShadedTube δ E) (x : E) :
    mult s T x ≤ mult s' T x :=
  Finset.sum_le_sum_of_subset h

theorem mult_le_card (s : Finset ι) (T : ι → ShadedTube δ E) (x : E) : mult s T x ≤ s.card := by
  classical
  rw [mult_eq_card_filter]
  exact Finset.card_filter_le _ _

/-- **`𝕋_p`**: the members of the family whose direction lies within `r` of `p`, modulo sign. -/
noncomputable def capFamily (s : Finset ι) (T : ι → ShadedTube δ E) (p : E) (r : ℝ) : Finset ι :=
  s.filter fun i => dirDist (T i).direction p ≤ r

theorem capFamily_subset (s : Finset ι) (T : ι → ShadedTube δ E) (p : E) (r : ℝ) :
    capFamily s T p r ⊆ s := Finset.filter_subset _ _

theorem mem_capFamily {s : Finset ι} {T : ι → ShadedTube δ E} {p : E} {r : ℝ} {i : ι} :
    i ∈ capFamily s T p r ↔ i ∈ s ∧ dirDist (T i).direction p ≤ r := Finset.mem_filter

/-- **`m_p(x)`**: the number of shades containing `x` whose tube direction lies within `r` of the
net direction `p`, modulo sign. -/
noncomputable def multCap (s : Finset ι) (T : ι → ShadedTube δ E) (p : E) (r : ℝ) (x : E) : ℕ :=
  mult (capFamily s T p r) T x

/-- **`m_p` is measurable** as an `ℕ`-valued function. -/
theorem measurable_multCap (s : Finset ι) (T : ι → ShadedTube δ E) (p : E) (r : ℝ) :
    Measurable (multCap s T p r) := measurable_mult _ _

theorem measurable_coe_multCap (s : Finset ι) (T : ι → ShadedTube δ E) (p : E) (r : ℝ) :
    Measurable fun x => ((multCap s T p r x : ℕ) : ENNReal) :=
  Measurable.of_discrete.comp (measurable_multCap s T p r)

theorem multCap_eq_card_filter (s : Finset ι) (T : ι → ShadedTube δ E) (p : E) (r : ℝ) (x : E)
    [DecidablePred fun i => x ∈ (T i).shade] :
    multCap s T p r x = ((capFamily s T p r).filter fun i => x ∈ (T i).shade).card :=
  mult_eq_card_filter _ _ _

theorem multCap_le_mult (s : Finset ι) (T : ι → ShadedTube δ E) (p : E) (r : ℝ) (x : E) :
    multCap s T p r x ≤ mult s T x := mult_mono (capFamily_subset s T p r) T x

/-! ## Narrow and broad points -/

/-- **The narrow set.** `x` is narrow (at net `P` and cap radius `r`) when some net direction
captures at least half the shades through `x`. -/
def narrowSet (P : Finset E) (s : Finset ι) (T : ι → ShadedTube δ E) (r : ℝ) : Set E :=
  {x | ∃ p ∈ P, mult s T x ≤ 2 * multCap s T p r x}

/-- **The broad set** `B`. `x` is broad when *no* net direction captures half the shades through
`x`: for every `p ∈ P`, strictly fewer than `m(x) / 2` of the tubes through `x` have direction
within `r` of `p`. -/
def broadSet (P : Finset E) (s : Finset ι) (T : ι → ShadedTube δ E) (r : ℝ) : Set E :=
  {x | ∀ p ∈ P, 2 * multCap s T p r x < mult s T x}

theorem mem_broadSet {P : Finset E} {s : Finset ι} {T : ι → ShadedTube δ E} {r : ℝ} {x : E} :
    x ∈ broadSet P s T r ↔ ∀ p ∈ P, 2 * multCap s T p r x < mult s T x := Iff.rfl

theorem mem_narrowSet {P : Finset E} {s : Finset ι} {T : ι → ShadedTube δ E} {r : ℝ} {x : E} :
    x ∈ narrowSet P s T r ↔ ∃ p ∈ P, mult s T x ≤ 2 * multCap s T p r x := Iff.rfl

/-- **Broad and narrow are complementary**: every point is exactly one of the two. -/
theorem broadSet_eq_compl_narrowSet (P : Finset E) (s : Finset ι) (T : ι → ShadedTube δ E)
    (r : ℝ) : broadSet P s T r = (narrowSet P s T r)ᶜ := by
  ext x
  simp only [mem_broadSet, Set.mem_compl_iff, mem_narrowSet, not_exists, not_and, not_le]

theorem narrowSet_union_broadSet (P : Finset E) (s : Finset ι) (T : ι → ShadedTube δ E) (r : ℝ) :
    narrowSet P s T r ∪ broadSet P s T r = Set.univ := by
  rw [broadSet_eq_compl_narrowSet, Set.union_compl_self]

/-- Every set of naturals is measurable, so `{x | f x ≤ g x}` is measurable for measurable
`ℕ`-valued `f`, `g`: decompose along the (countably many) values of `g`. -/
theorem measurableSet_le_nat {E : Type*} [MeasurableSpace E] {f g : E → ℕ} (hf : Measurable f)
    (hg : Measurable g) : MeasurableSet {x | f x ≤ g x} := by
  have hrw : {x | f x ≤ g x} = ⋃ n : ℕ, (g ⁻¹' {n} ∩ f ⁻¹' {k | k ≤ n}) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_singleton_iff]
    exact ⟨fun h => ⟨g x, rfl, h⟩, fun ⟨n, hn, hk⟩ => hn ▸ hk⟩
  rw [hrw]
  exact MeasurableSet.iUnion fun n =>
    (hg MeasurableSet.of_discrete).inter (hf MeasurableSet.of_discrete)

theorem measurableSet_narrowSet (P : Finset E) (s : Finset ι) (T : ι → ShadedTube δ E) (r : ℝ) :
    MeasurableSet (narrowSet P s T r) := by
  have hrw : narrowSet P s T r
      = ⋃ p ∈ (P : Set E), {x | mult s T x ≤ 2 * multCap s T p r x} := by
    ext x
    simp only [mem_narrowSet, Set.mem_iUnion, Set.mem_setOf_eq, Finset.mem_coe, exists_prop]
  rw [hrw]
  refine MeasurableSet.biUnion P.countable_toSet fun p _ => ?_
  exact measurableSet_le_nat (measurable_mult s T)
    (Measurable.of_discrete.comp (measurable_multCap s T p r))

theorem measurableSet_broadSet (P : Finset E) (s : Finset ι) (T : ι → ShadedTube δ E) (r : ℝ) :
    MeasurableSet (broadSet P s T r) := by
  rw [broadSet_eq_compl_narrowSet]
  exact (measurableSet_narrowSet P s T r).compl

/-! ## Transverse pairs -/

/-- **The transverse index pairs** at threshold `t`: ordered pairs `(i, j)` of members of the
family whose directions are at angular distance at least `t`, modulo sign. -/
noncomputable def transverseSet (s : Finset ι) (T : ι → ShadedTube δ E) (t : ℝ) :
    Finset (ι × ι) :=
  (s ×ˢ s).filter fun q => t ≤ dirDist (T q.1).direction (T q.2).direction

theorem mem_transverseSet {s : Finset ι} {T : ι → ShadedTube δ E} {t : ℝ} {q : ι × ι} :
    q ∈ transverseSet s T t ↔
      (q.1 ∈ s ∧ q.2 ∈ s) ∧ t ≤ dirDist (T q.1).direction (T q.2).direction := by
  rw [transverseSet, Finset.mem_filter, Finset.mem_product]

/-- **The transverse pair count** `∑_{(i,j) transverse} 1_{Y_i ∩ Y_j}(x)`, `ℕ`-valued. -/
noncomputable def transverseCount (s : Finset ι) (T : ι → ShadedTube δ E) (t : ℝ) (x : E) : ℕ :=
  ∑ q ∈ transverseSet s T t, ((T q.1).shade ∩ (T q.2).shade).indicator (fun _ => (1 : ℕ)) x

theorem measurable_transverseCount (s : Finset ι) (T : ι → ShadedTube δ E) (t : ℝ) :
    Measurable (transverseCount s T t) :=
  Finset.measurable_sum _ fun q _ => measurable_const.indicator
    ((T q.1).measurableSet_shade.inter (T q.2).measurableSet_shade)

theorem measurable_coe_transverseCount (s : Finset ι) (T : ι → ShadedTube δ E) (t : ℝ) :
    Measurable fun x => ((transverseCount s T t x : ℕ) : ENNReal) :=
  Measurable.of_discrete.comp (measurable_transverseCount s T t)

theorem transverseCount_eq_card_filter (s : Finset ι) (T : ι → ShadedTube δ E) (t : ℝ) (x : E)
    [DecidablePred fun q : ι × ι => x ∈ (T q.1).shade ∩ (T q.2).shade] :
    transverseCount s T t x
      = ((transverseSet s T t).filter fun q => x ∈ (T q.1).shade ∩ (T q.2).shade).card :=
  sum_indicator_eq_card_filter _ _ _

/-- The `ℝ≥0∞` reading of the transverse pair count as a finite sum of indicators — the form band
item A3 exchanges with `MeasureTheory.lintegral_finsetSum`. -/
theorem coe_transverseCount (s : Finset ι) (T : ι → ShadedTube δ E) (t : ℝ) (x : E) :
    ((transverseCount s T t x : ℕ) : ENNReal)
      = ∑ q ∈ transverseSet s T t,
          ((T q.1).shade ∩ (T q.2).shade).indicator (fun _ => (1 : ENNReal)) x := by
  rw [transverseCount, Nat.cast_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  by_cases h : x ∈ (T q.1).shade ∩ (T q.2).shade <;> simp [h]

end Counting

/-! ## The pointwise broad inequality -/

/-- **Pointwise broad counting, pure combinatorics.** If for every `i ∈ u` strictly fewer than
half of `u` is `near i`, then `|u| ^ 2 ≤ 2 · #{(i, j) ∈ u × u : ¬ near i j}`.

(This is the `broad_pairs` auxiliary probe  — a probe file, not
a tree declaration — re-verified here.) -/
theorem card_sq_le_two_mul_card_notNear {κ : Type*} (u : Finset κ) (near : κ → κ → Prop)
    [DecidableRel near] (h : ∀ i ∈ u, 2 * (u.filter fun j => near i j).card < u.card) :
    u.card * u.card ≤ 2 * ((u ×ˢ u).filter fun q => ¬ near q.1 q.2).card := by
  classical
  have hnear : ((u ×ˢ u).filter fun q => near q.1 q.2).card
      = ∑ i ∈ u, (u.filter fun j => near i j).card := by
    rw [Finset.card_filter, Finset.sum_product]
    simp only [Finset.card_filter]
  have hsplit : ((u ×ˢ u).filter fun q => near q.1 q.2).card
      + ((u ×ˢ u).filter fun q => ¬ near q.1 q.2).card = u.card * u.card := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_product]
  have hbound : 2 * (∑ i ∈ u, (u.filter fun j => near i j).card) + u.card
      ≤ u.card * u.card := by
    calc 2 * (∑ i ∈ u, (u.filter fun j => near i j).card) + u.card
        = ∑ i ∈ u, (2 * (u.filter fun j => near i j).card + 1) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, smul_eq_mul, mul_one]
      _ ≤ ∑ i ∈ u, u.card := Finset.sum_le_sum fun i hi => by have := h i hi; omega
      _ = u.card * u.card := by rw [Finset.sum_const, smul_eq_mul]
  generalize hP : u.card * u.card = P at *
  generalize hA : ((u ×ˢ u).filter fun q => near q.1 q.2).card = A at *
  generalize hB : ((u ×ˢ u).filter fun q => ¬ near q.1 q.2).card = B at *
  generalize hS : (∑ i ∈ u, (u.filter fun j => near i j).card) = S at *
  omega

section Broad

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] {ι : Type*} {δ : NNReal}

/-- **The bilinear pointwise inequality** (band item A2's contract, ).

On the broad set, the multiplicity is controlled *bilinearly*: `m(x) ^ 2` is at most twice the
number of transverse ordered pairs of shades through `x`. The cap radius `r` must exceed the
transversality threshold `t` by the net's covering radius `2 * θ` — that is the whole content of
the hypothesis `t + 2 * θ ≤ r`, and it is where `Tube.sphere_sep_net`'s `2θ` cover radius (rather
than `θ`) is paid for.

The mechanism: for `i` with `x ∈ Y_i`, pick the net direction `p` covering `dir T_i`; every `j`
with `x ∈ Y_j` and `dirDist (dir T_i) (dir T_j) < t` then has `dirDist (dir T_j) p ≤ t + 2θ ≤ r`,
so lies in the cap `𝕋_p`. Broadness at `p` bounds those `j` by `m(x)/2`, and
`card_sq_le_two_mul_card_notNear` converts that into the bilinear bound. -/
theorem broad_sq_le_two_mul_transverse_pairs {θ : ℝ} (N : DirNet E θ) {s : Finset ι}
    {T : ι → ShadedTube δ E} {t r : ℝ} (hr : t + 2 * θ ≤ r) {x : E}
    (hx : x ∈ broadSet N.points s T r) :
    mult s T x ^ 2 ≤ 2 * transverseCount s T t x := by
  classical
  rw [mem_broadSet] at hx
  set sx : Finset ι := s.filter (fun i => x ∈ (T i).shade) with hsx
  have hm : mult s T x = sx.card := mult_eq_card_filter s T x
  set near : ι → ι → Prop :=
    fun i j => dirDist (T i).direction (T j).direction < t with hnear
  have hkey : ∀ i ∈ sx, 2 * (sx.filter fun j => near i j).card < sx.card := by
    intro i _
    obtain ⟨p, hp, hdp⟩ := N.cover_dirDist (T i).direction (T i).norm_direction
    have hsub : (sx.filter fun j => near i j)
        ⊆ (capFamily s T p r).filter (fun j => x ∈ (T j).shade) := by
      intro j hj
      simp only [Finset.mem_filter, hsx, hnear, mem_capFamily] at hj ⊢
      obtain ⟨⟨hjs, hjshade⟩, hjnear⟩ := hj
      refine ⟨⟨hjs, ?_⟩, hjshade⟩
      have hcomm : dirDist (T j).direction (T i).direction ≤ t := by
        rw [dirDist_comm]; exact le_of_lt hjnear
      calc dirDist (T j).direction p
          ≤ dirDist (T j).direction (T i).direction + dirDist (T i).direction p :=
            dirDist_triangle _ _ _
        _ ≤ t + 2 * θ := by linarith
        _ ≤ r := hr
    have hcard : (sx.filter fun j => near i j).card ≤ multCap s T p r x := by
      rw [multCap_eq_card_filter]
      exact Finset.card_le_card hsub
    have hb : 2 * multCap s T p r x < sx.card := by rw [← hm]; exact hx p hp
    omega
  have hpairs := card_sq_le_two_mul_card_notNear sx near hkey
  have heq : ((sx ×ˢ sx).filter fun q => ¬ near q.1 q.2)
      = (transverseSet s T t).filter (fun q => x ∈ (T q.1).shade ∩ (T q.2).shade) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_product, hsx, hnear, mem_transverseSet, not_lt,
      Set.mem_inter_iff]
    tauto
  rw [transverseCount_eq_card_filter, ← heq, hm, pow_two]
  exact hpairs

/-- The `ℝ≥0∞` form of `broad_sq_le_two_mul_transverse_pairs`, ready for `lintegral_mono`. -/
theorem enn_broad_sq_le_two_mul_transverse_pairs {θ : ℝ} (N : DirNet E θ) {s : Finset ι}
    {T : ι → ShadedTube δ E} {t r : ℝ} (hr : t + 2 * θ ≤ r) {x : E}
    (hx : x ∈ broadSet N.points s T r) :
    ((mult s T x : ℕ) : ENNReal) ^ 2 ≤ 2 * ((transverseCount s T t x : ℕ) : ENNReal) := by
  have h := broad_sq_le_two_mul_transverse_pairs N hr hx
  have hcast : ((mult s T x ^ 2 : ℕ) : ENNReal) ≤ ((2 * transverseCount s T t x : ℕ) : ENNReal) :=
    Nat.cast_le.mpr h
  simpa using hcast

end Broad


/-! ## The packing constant `C_P` -/

/-- **The one-sign-branch packing constant.** A `θ`-separated set of points inside a ball of
radius `4 * θ` has at most this many members (`card_le_capBranchConst`): the packing bound
`Tube.card_le_of_separated_parameterSpace` at separation radius `θ / 2` gives the factor
`(θ/2)^{-d}`, the `θ/2`-thickening of the `4θ`-ball sits inside the `5θ`-ball, and
`(2/θ)^d · (5θ)^d = 10^d`. Nothing here depends on `θ`, which is the point. -/
noncomputable def capBranchConst (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] : ENNReal :=
  ((Metric.coveringNumber_mul_pow_le_volume_cthickening.C (finrank ℝ E) : NNReal) : ENNReal)⁻¹
    * ENNReal.ofReal ((10 : ℝ) ^ (finrank ℝ E)) * volume (ball (0 : E) 1)

/-- **The cap packing constant `C_P`** of the narrow case's fullness pigeonhole: a single
direction lies in at most `C_P` of the `4θ`-caps (modulo sign) of a `θ`-separated net of unit
directions (`card_filter_dirDist_le`).

`C_P = 2 · C_cov(d)⁻¹ · 10^d · |B(0,1)|` (open unit ball), where `d = finrank ℝ E` and `C_cov` is
`Metric.coveringNumber_mul_pow_le_volume_cthickening.C`. In `d = 3` that reads
`2 · C_cov(3)⁻¹ · 1000 · |B(0,1)|`.

**The factor `2` is the sign convention, not slack.** `Tube.sphere_sep_net` separates in the plain
norm `‖a - b‖`, so a net may contain both `p` and `-p`, whose `dirDist` is `0`; the caps are
therefore counted on the two sign branches `‖u - p‖ ≤ 4θ` and `‖u + p‖ ≤ 4θ` separately and the
counts added. -/
noncomputable def capPackingConst (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] : ENNReal :=
  2 * capBranchConst E

section Packing

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Nontrivial E]

omit [Nontrivial E] in
theorem capBranchConst_ne_top : capBranchConst E ≠ ⊤ := by
  refine ENNReal.mul_ne_top (ENNReal.mul_ne_top ?_ ENNReal.ofReal_ne_top)
    (measure_ball_lt_top).ne
  refine ENNReal.inv_ne_top.mpr ?_
  exact_mod_cast ne_of_gt
    (Metric.coveringNumber_mul_pow_le_volume_cthickening.C_pos (finrank ℝ E))

omit [Nontrivial E] in
theorem capPackingConst_ne_top : capPackingConst E ≠ ⊤ :=
  ENNReal.mul_ne_top (by simp) capBranchConst_ne_top

/-- **Packing on one sign branch.** A `θ`-separated finite set contained in the closed ball of
radius `4 * θ` about any centre has at most `capBranchConst E` members. -/
theorem card_le_capBranchConst {θ : ℝ} (hθ : 0 < θ) {P : Finset E}
    (hsep : ∀ p ∈ P, ∀ q ∈ P, p ≠ q → θ ≤ ‖p - q‖) {c : E}
    (hmem : ∀ p ∈ P, ‖p - c‖ ≤ 4 * θ) :
    (P.card : ENNReal) ≤ capBranchConst E := by
  have hθne : θ ≠ 0 := ne_of_gt hθ
  set ρ : NNReal := Real.toNNReal (θ / 2) with hρdef
  have hρc : (ρ : ℝ) = θ / 2 := Real.coe_toNNReal _ (by positivity)
  have hρpos : 0 < ρ := by
    rw [← NNReal.coe_pos, hρc]; positivity
  have hpair : (P : Set E).Pairwise fun a b => (ρ : ℝ) < dist a b := by
    intro a ha b hb hab
    have h := hsep a ha b hb hab
    rw [dist_eq_norm, hρc]
    linarith
  have hGA : ∀ p ∈ P, p ∈ closedBall c (4 * θ) := by
    intro p hp
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact hmem p hp
  have hcard := Tube.card_le_of_separated_parameterSpace (F := E) (G := P) (Ψ := id)
    (A := closedBall c (4 * θ)) hρpos hGA (by simpa using hpair)
  have hsub : cthickening (ρ : ℝ) (closedBall c (4 * θ)) ⊆ closedBall c (5 * θ) := by
    have hcpt : IsCompact (closedBall c (4 * θ)) := isCompact_closedBall c (4 * θ)
    rw [hcpt.cthickening_eq_biUnion_closedBall (show (0:ℝ) ≤ (ρ:ℝ) by rw [hρc]; positivity)]
    refine Set.iUnion₂_subset fun y hy => Metric.closedBall_subset_closedBall' ?_
    have hy' : dist y c ≤ 4 * θ := by rwa [Metric.mem_closedBall] at hy
    rw [hρc]; linarith
  have hvol : volume (closedBall c (5 * θ))
      = ENNReal.ofReal ((5 * θ) ^ (finrank ℝ E)) * volume (ball (0 : E) 1) :=
    Measure.addHaar_closedBall (μ := (volume : Measure E)) c (r := 5 * θ) (by positivity)
  have hprod : ((ρ : NNReal) : ENNReal)⁻¹ ^ (finrank ℝ E)
      * ENNReal.ofReal ((5 * θ) ^ (finrank ℝ E))
      = ENNReal.ofReal ((10 : ℝ) ^ (finrank ℝ E)) := by
    have h1 : ((ρ : NNReal) : ENNReal) = ENNReal.ofReal (θ / 2) := by
      rw [← hρc]; exact ENNReal.ofReal_coe_nnreal.symm
    rw [h1, ← ENNReal.ofReal_inv_of_pos (by positivity),
      ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity), ← mul_pow]
    congr 2
    field_simp
    norm_num
  calc (P.card : ENNReal)
      ≤ ((Metric.coveringNumber_mul_pow_le_volume_cthickening.C (finrank ℝ E) : NNReal) :
            ENNReal)⁻¹ * ((ρ : NNReal) : ENNReal)⁻¹ ^ (finrank ℝ E)
          * volume (cthickening (ρ : ℝ) (closedBall c (4 * θ))) := hcard
    _ ≤ ((Metric.coveringNumber_mul_pow_le_volume_cthickening.C (finrank ℝ E) : NNReal) :
            ENNReal)⁻¹ * ((ρ : NNReal) : ENNReal)⁻¹ ^ (finrank ℝ E)
          * (ENNReal.ofReal ((5 * θ) ^ (finrank ℝ E)) * volume (ball (0 : E) 1)) := by
        gcongr
        exact hvol ▸ measure_mono hsub
    _ = ((Metric.coveringNumber_mul_pow_le_volume_cthickening.C (finrank ℝ E) : NNReal) :
            ENNReal)⁻¹
          * (((ρ : NNReal) : ENNReal)⁻¹ ^ (finrank ℝ E)
              * ENNReal.ofReal ((5 * θ) ^ (finrank ℝ E)))
          * volume (ball (0 : E) 1) := by ring
    _ = capBranchConst E := by rw [hprod, capBranchConst]

/-- **The fullness pigeonhole's packing count.** A single direction `u` lies in at most
`capPackingConst E` of the caps `{p : dirDist u p ≤ R}`, `R ≤ 4 * θ`, of a `θ`-separated net of
unit directions. This is the `C_P`  narrow case.

No hypothesis on `u` (not even `‖u‖ = 1`) and none on the cover clause of the net are needed: the
count is pure volume packing on the two sign branches. -/
theorem card_filter_dirDist_le {θ : ℝ} (hθ : 0 < θ) (N : DirNet E θ) {u : E} {R : ℝ}
    (hR : R ≤ 4 * θ) :
    (((N.points.filter fun p => dirDist u p ≤ R).card : ℕ) : ENNReal) ≤ capPackingConst E := by
  classical
  set Pp : Finset E := N.points.filter (fun p => ‖u - p‖ ≤ 4 * θ) with hPp
  set Pm : Finset E := N.points.filter (fun p => ‖u + p‖ ≤ 4 * θ) with hPm
  have hsubset : (N.points.filter fun p => dirDist u p ≤ R) ⊆ Pp ∪ Pm := by
    intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨hpN, hpd⟩ := hp
    have h4 : dirDist u p ≤ 4 * θ := le_trans hpd hR
    rw [Finset.mem_union, hPp, hPm, Finset.mem_filter, Finset.mem_filter]
    rcases le_total ‖u - p‖ ‖u + p‖ with h | h
    · refine Or.inl ⟨hpN, ?_⟩
      rwa [dirDist, min_eq_left h] at h4
    · refine Or.inr ⟨hpN, ?_⟩
      rwa [dirDist, min_eq_right h] at h4
  have hbp : (Pp.card : ENNReal) ≤ capBranchConst E := by
    refine card_le_capBranchConst hθ (c := u)
      (fun p hp q hq hpq => N.sep p (Finset.mem_of_mem_filter p hp) q
        (Finset.mem_of_mem_filter q hq) hpq) ?_
    intro p hp
    rw [hPp, Finset.mem_filter] at hp
    rw [norm_sub_rev]
    exact hp.2
  have hbm : (Pm.card : ENNReal) ≤ capBranchConst E := by
    refine card_le_capBranchConst hθ (c := -u)
      (fun p hp q hq hpq => N.sep p (Finset.mem_of_mem_filter p hp) q
        (Finset.mem_of_mem_filter q hq) hpq) ?_
    intro p hp
    rw [hPm, Finset.mem_filter] at hp
    have hrw : ‖p - -u‖ = ‖u + p‖ := by rw [sub_neg_eq_add, add_comm]
    rw [hrw]
    exact hp.2
  have hcards : (N.points.filter fun p => dirDist u p ≤ R).card ≤ Pp.card + Pm.card :=
    le_trans (Finset.card_le_card hsubset) (Finset.card_union_le Pp Pm)
  calc (((N.points.filter fun p => dirDist u p ≤ R).card : ℕ) : ENNReal)
      ≤ ((Pp.card + Pm.card : ℕ) : ENNReal) := Nat.cast_le.mpr hcards
    _ = (Pp.card : ENNReal) + (Pm.card : ENNReal) := by push_cast; ring
    _ ≤ capBranchConst E + capBranchConst E := add_le_add hbp hbm
    _ = capPackingConst E := by rw [capPackingConst, two_mul]

end Packing

end Kakeya.CapBroadNarrow
