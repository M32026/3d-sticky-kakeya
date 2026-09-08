/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Factoring.Step1
public import Kakeya.Mathlib.MeasureTheory.Lintegral
public import Kakeya.Multiplicity
public import Kakeya.Pigeonhole

/-! # Step 2 of the factoring construction

This file formalizes the blueprint subsection `subsec:step2Abstract`: the choice, at each point, of
the three dyadic scales `μ_inner`, `μ_outer`, `μ̃` of Item 2 of the outer factoring family of GWZ
Proposition 5.1, and the pigeonholing that makes a single triple carry almost all of the
multiplicity mass.

Everything is stated at the level of generality the argument actually uses:

* a measure space `(X, μ)`; in the application `X = ℝ³` with Lebesgue measure;
* a finite index set `t`; in the application `t` indexes `𝒲'`;
* a family of functions `m j : X → ℕ` for `j ∈ t`; in the application
  `m j = ShadedBody.pointwiseMultiplicity` of the fiber over `j`, and
  `ShadedBody.pointwiseMultiplicity_eq_sum_fiberwise` identifies `∑ j ∈ t, m j x` with
  `μ(𝒱', Y)(x)`;
* a family of neighbourhood assignments `nhd : κ → X → Set X` with `x ∈ nhd j x` for `j ∈ t`; in
  the application `nhd j x = Metric.closedBall x w₁`, constant in `j`. Indexing the neighbourhood by
  the block costs the argument nothing and leaves room for a per-block radius, which is what one
  gets by taking `w₁ j` to be the shortest dimension of the outer body `W j`.

Nothing about convex bodies, shadings, Frostman conditions or the ambient dimension is used, so
none of the results below is special to `ℝ³`.

All the material specific to this step lives in the namespace `Kakeya.MultiplicityFamily`, whose
declarations are named after the mathematics rather than after the step: the informal `≈` of
Item 2(i) becomes the explicit two-sided inequality of `IsScaleTriple`, with the constant
`scaleTripleConstant`, and the informal count `≲ (log |𝒱|)(log |𝒲|)²` of level sets becomes
`scalePigeonholeConstant`. Both constants are natural numbers and neither depends on the ambient
dimension.

## Main statements

* `ShadedBody.pointwiseMultiplicity_eq_sum_fiberwise` (blueprint
  `lem:pointwiseMultiplicityFiberwise`);
* `Kakeya.MultiplicityFamily.exists_isScaleTriple` (blueprint `lem:step2Pointwise`): at every
  point of positive multiplicity there is an admissible scale triple;
* `Kakeya.MultiplicityFamily.exists_isScaleTriple_lintegral_le` (blueprint
  `lem:step2LevelSetPigeonhole`): a single triple whose level set carries at least a
  `scalePigeonholeConstant`-th of the total mass.
-/

@[expose] public section

open MeasureTheory Convexity
open scoped ENNReal

namespace ShadedBody

variable
  {E : Type*} [TopologicalSpace E] [ConvexSpace ℝ E] [MeasurableSpace E]
  {ι κ : Type*} [DecidableEq κ]

/-- **The multiplicity family of the data of Step 2** (blueprint `def:factoringStep2Data`):
`m_j(x) = μ(𝒱_j, Y)(x)` is the pointwise multiplicity of the fiber
`u_j = {i ∈ u | F.parent i = j}` over the block `j`, taken inside `u`.

In the application `u` is the surviving index set
`u' = {i ∈ u | F.parent i ∈ t'}` of Step 1, and
`fiberMultiplicity F u' : κ → E → ℕ` is the family `m` of the abstract layer of
`Kakeya/Factoring/Step2.lean`. Blocks are indexed by `j` rather than by the bodies `W j`, since
`W j = W j'` is permitted for `j ≠ j'` and a fiber "`𝒱_W`" would be ill defined. -/
noncomputable def fiberMultiplicity (F : FactorFamily E ι κ) (u : Finset ι) (j : κ) (x : E) : ℕ :=
  pointwiseMultiplicity {i ∈ u | F.parent i = j} F.innerBody x

end ShadedBody

namespace Kakeya.MultiplicityFamily

variable {X : Type*} {κ : Type*}

/-- The `k`-th dyadic level set of the multiplicity family `m` at the point `x`:
`S_k(x) = {j ∈ t | 2 ^ k ≤ m j x < 2 ^ (k + 1)}` (blueprint `def:dyadicLevel`).

Its cardinality counts the *indices* `j ∈ t` at which `m j x` is comparable to `2 ^ k` in the strict
dyadic sense, which is Item 2(ii) of the outer factoring family. Indices are counted rather than
bodies because the family `𝒲` is indexed and `W j = W j'` is permitted for `j ≠ j'`. -/
def dyadicLevel (t : Finset κ) (m : κ → X → ℕ) (k : ℕ) (x : X) : Finset κ :=
  {j ∈ t | 2 ^ k ≤ m j x ∧ m j x < 2 ^ (k + 1)}

/-- The predicate defining `dyadicLevelNhd` is an unbounded existential over `nhd j x`, hence
undecidable; the instance is declared here rather than inside the definition so that the definition
and every proof about it use the same one. -/
noncomputable instance instDecidablePredExistsNhd (m : κ → X → ℕ) (nhd : κ → X → Set X) (k : ℕ)
    (x : X) :
    DecidablePred fun j : κ => ∃ y ∈ nhd j x, 2 ^ k ≤ m j y ∧ m j y < 2 ^ (k + 1) :=
  Classical.decPred _

/-- The neighbourhood variant of `dyadicLevel`:
`S̃_k(x) = {j ∈ t | ∃ y ∈ nhd j x, 2 ^ k ≤ m j y < 2 ^ (k + 1)}` (blueprint `def:dyadicLevel`).

Its cardinality is Item 2(iii) of the outer factoring family. The neighbourhood is indexed by the
block, so that each `m j` is tested on its own neighbourhood `nhd j x` of `x`. The defining
predicate is undecidable, so it is filtered with the classical instance
`instDecidablePredExistsNhd` and the definition is `noncomputable`; this is bookkeeping only, since
no statement below evaluates `S̃_k(x)`. -/
noncomputable def dyadicLevelNhd (t : Finset κ) (m : κ → X → ℕ) (nhd : κ → X → Set X) (k : ℕ)
    (x : X) : Finset κ :=
  {j ∈ t | ∃ y ∈ nhd j x, 2 ^ k ≤ m j y ∧ m j y < 2 ^ (k + 1)}

variable (t : Finset κ) (m : κ → X → ℕ) (nhd : κ → X → Set X) (k : ℕ) (x : X)

/-- **The neighbourhood level set is larger** (blueprint `lem:dyadicLevelSubset`, first assertion):
if `x ∈ nhd j x` for every `j ∈ t` then `y = x` witnesses membership in `S̃_k(x)`. -/
theorem dyadicLevel_subset_dyadicLevelNhd (hx : ∀ j ∈ t, x ∈ nhd j x) :
    dyadicLevel t m k x ⊆ dyadicLevelNhd t m nhd k x := by
  intro j hj
  have hjt : j ∈ t := (Finset.mem_filter.mp hj).1
  exact Finset.mem_filter.mpr ⟨hjt, ⟨x, hx j hjt, (Finset.mem_filter.mp hj).2⟩⟩

/-- **The neighbourhood level set is a subset of the index set** (blueprint
`lem:dyadicLevelSubset`, second assertion). This holds unconditionally. -/
theorem dyadicLevelNhd_subset : dyadicLevelNhd t m nhd k x ⊆ t :=
  Finset.filter_subset _ t

/-- **The neighbourhood level set is larger** (blueprint `lem:dyadicLevelSubset`, third
assertion). -/
theorem card_dyadicLevel_le_card_dyadicLevelNhd (hx : ∀ j ∈ t, x ∈ nhd j x) :
    (dyadicLevel t m k x).card ≤ (dyadicLevelNhd t m nhd k x).card :=
  Finset.card_le_card (dyadicLevel_subset_dyadicLevelNhd t m nhd k x hx)

/-- **The neighbourhood level set is a subset of the index set** (blueprint
`lem:dyadicLevelSubset`, fourth assertion). This holds unconditionally. -/
theorem card_dyadicLevelNhd_le_card : (dyadicLevelNhd t m nhd k x).card ≤ t.card :=
  Finset.card_le_card (dyadicLevelNhd_subset t m nhd k x)

/-- **The neighbourhood level set is larger** (blueprint `lem:dyadicLevelSubset`, fifth
assertion), in the `Nat.log 2` form used for the outer scales. -/
theorem log_card_dyadicLevel_le_log_card_dyadicLevelNhd (hx : ∀ j ∈ t, x ∈ nhd j x) :
    Nat.log 2 (dyadicLevel t m k x).card ≤ Nat.log 2 (dyadicLevelNhd t m nhd k x).card :=
  Nat.log_mono_right (card_dyadicLevel_le_card_dyadicLevelNhd t m nhd k x hx)

/-- **The neighbourhood level set is a subset of the index set** (blueprint
`lem:dyadicLevelSubset`, sixth assertion), in the `Nat.log 2` form. This holds
unconditionally. -/
theorem log_card_dyadicLevelNhd_le_log_card :
    Nat.log 2 (dyadicLevelNhd t m nhd k x).card ≤ Nat.log 2 t.card :=
  Nat.log_mono_right (card_dyadicLevelNhd_le_card t m nhd k x)

/-- **Constant in `Kakeya.MultiplicityFamily.exists_isScaleTriple`** (blueprint
`def:scaleTripleConstant`): `C(M) = 4 (Nat.log 2 M + 1) = 4 * dyadicPigeonholeNatConstant M`.

The three factors have distinct origins: `dyadicPigeonholeNatConstant M` is the number of dyadic
classes lost when the values `m j x` are pigeonholed to produce `μ_inner`; one factor `2` comes from
replacing the class bound `m j x < 2 ^ (k + 1)` by the scale `μ_inner = 2 ^ k`; the other factor `2`
comes from replacing `|S_k(x)| < 2 ^ (l + 1)` by the scale `μ_outer = 2 ^ l`.

Here `M` bounds the fiberwise multiplicities. The constant depends only on `M`; in particular it
does *not* depend on `t.card`, on the neighbourhood assignment, or on the ambient dimension. -/
def scaleTripleConstant (M : ℕ) : ℕ := 4 * dyadicPigeonholeNatConstant M

/-- **Admissible scale triple at a point** (blueprint `def:isStep2Scales`).

Writing `μ_inner = 2 ^ k`, `μ_outer = 2 ^ l` and `μ̃ = 2 ^ l'`, the triple `(k, l, l')` is
admissible at `x` with bound `M` when the four items (a)–(d) of the blueprint hold. The level set
`Ω_M(k, l, l')` of the blueprint is `{x | IsScaleTriple t m nhd M k l l' x}`.

The bound `M` is not decoration: it enters (a) through `Nat.log 2 M` and (b) through
`scaleTripleConstant M`, so the level set genuinely depends on `M`. Items (c) and (d) are the strict
dyadic comparisons `|S_k(x)| ∼ μ_outer` and `|S̃_k(x)| ∼ μ̃`, and `μ_outer ≤ μ̃` is part of (a). -/
structure IsScaleTriple (t : Finset κ) (m : κ → X → ℕ) (nhd : κ → X → Set X)
    (M k l l' : ℕ) (x : X) : Prop where
  /-- (a) *(Range.)* The inner scale is confined by the bound `M`. -/
  inner_le_log : k ≤ Nat.log 2 M
  /-- (a) *(Range.)* `μ_outer ≤ μ̃`. -/
  outer_le_outerNhd : l ≤ l'
  /-- (a) *(Range.)* Both outer scales are confined by the size of the index set. -/
  outerNhd_le_log_card : l' ≤ Nat.log 2 t.card
  /-- (b) *(Explicit form of Item (i), lower half.)* `μ_inner μ_outer ≤ m x`. -/
  mul_le_sum : 2 ^ k * 2 ^ l ≤ ∑ j ∈ t, m j x
  /-- (b) *(Explicit form of Item (i), upper half.)* `m x ≤ C(M) μ_inner μ_outer`. -/
  sum_le_mul : ∑ j ∈ t, m j x ≤ scaleTripleConstant M * (2 ^ k * 2 ^ l)
  /-- (c) *(Item (ii), lower half.)* `μ_outer ≤ |S_k(x)|`. -/
  le_card_dyadicLevel : 2 ^ l ≤ (dyadicLevel t m k x).card
  /-- (c) *(Item (ii), upper half.)* `|S_k(x)| < 2 μ_outer`. -/
  card_dyadicLevel_lt : (dyadicLevel t m k x).card < 2 * 2 ^ l
  /-- (d) *(Item (iii), lower half.)* `μ̃ ≤ |S̃_k(x)|`. -/
  le_card_dyadicLevelNhd : 2 ^ l' ≤ (dyadicLevelNhd t m nhd k x).card
  /-- (d) *(Item (iii), upper half.)* `|S̃_k(x)| < 2 μ̃`. -/
  card_dyadicLevelNhd_lt : (dyadicLevelNhd t m nhd k x).card < 2 * 2 ^ l'

/-- **Admissible points carry positive multiplicity** (blueprint
`lem:dyadicLevelSubsetSupport`): `Ω_M(k, l, l') ⊆ {m ≥ 1}`, because the lower half of Item (b)
bounds `m x` below by `2 ^ k 2 ^ l ≥ 1`.

In the application the right-hand side is the shaded union `U(𝒱', Y)`, so this is what makes the
requirement `Ω ⊆ U(𝒱', Y)` of the construction automatic. -/
theorem setOf_isScaleTriple_subset_setOf_one_le (M k l l' : ℕ) :
    {x | IsScaleTriple t m nhd M k l l' x} ⊆ {x | 1 ≤ ∑ j ∈ t, m j x} := fun _ hx =>
  le_trans (Nat.mul_le_mul Nat.one_le_two_pow Nat.one_le_two_pow) hx.mul_le_sum

/-- **A heavy dyadic level set is nonempty** (blueprint `lem:dyadicLevelNonempty`): a positive
quantity bounded by a multiple of the class sum forces the class sum, hence the class, to be
nonzero. -/
theorem dyadicLevel_nonempty (M : ℕ) (hpos : 1 ≤ ∑ j ∈ t, m j x)
    (hle : ∑ j ∈ t, m j x
      ≤ dyadicPigeonholeNatConstant M * ∑ j ∈ dyadicLevel t m k x, m j x) :
    (dyadicLevel t m k x).Nonempty := by
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  simp only [hne, Finset.sum_empty, Nat.mul_zero, Nat.le_zero] at hle
  omega

/-- **Choice of the inner scale** (blueprint `lem:step2InnerScale`).

Pigeonholing the values `m j x`, `j ∈ t`, with themselves as weights produces a dyadic scale
`2 ^ k`, `k ≤ Nat.log 2 M`, whose level set is nonempty and whose product with the level-set
cardinality is comparable to `m x`.

Only the values at the single point `x` are used, so no hypothesis on the neighbourhood assignment
is needed. -/
theorem exists_innerScale (M : ℕ) (hM : ∀ j ∈ t, m j x ≤ M) (hpos : 1 ≤ ∑ j ∈ t, m j x) :
    ∃ k ≤ Nat.log 2 M, (dyadicLevel t m k x).Nonempty ∧
      2 ^ k * (dyadicLevel t m k x).card ≤ ∑ j ∈ t, m j x ∧
      ∑ j ∈ t, m j x
        ≤ dyadicPigeonholeNatConstant M * 2 ^ (k + 1) * (dyadicLevel t m k x).card := by
  -- The dyadic pigeonhole lemma (self-weight, no lower bound required) supplies the inner scale;
  -- `dyadicLevel` is by definition the filtered set it produces.
  obtain ⟨k, hk_le_log, h_ineq⟩ := Nat.dyadic_pigeonhole_self t (fun j => m j x) hM
  have h_ineq' : ∑ j ∈ t, m j x
      ≤ dyadicPigeonholeNatConstant M * ∑ j ∈ dyadicLevel t m k x, m j x := h_ineq
  obtain ⟨h_low, h_high⟩ := Nat.dyadic_class_card_sandwich (dyadicLevel t m k x) (fun j => m j x) k
    fun j hj => (Finset.mem_filter.mp hj).2
  refine ⟨k, hk_le_log, dyadicLevel_nonempty t m k x M hpos h_ineq',
    h_low.trans (Finset.sum_le_sum_of_subset (Finset.filter_subset _ t)), ?_⟩
  rw [mul_assoc]
  exact h_ineq'.trans (Nat.mul_le_mul_left _ h_high)

/-- **Choice of the two outer scales** (blueprint `lem:step2OuterScales`).

Both level-set cardinalities are positive, so each lies in the dyadic block of its own
`Nat.log 2`; the two scales obtained are ordered, and the larger is confined by `Nat.log 2 t.card`.
These are Items (c) and (d) of `IsScaleTriple` together with the half of Item (a) not involving
`M`. -/
theorem exists_outerScales (hx : ∀ j ∈ t, x ∈ nhd j x) (hne : (dyadicLevel t m k x).Nonempty) :
    ∃ l l' : ℕ,
      2 ^ l ≤ (dyadicLevel t m k x).card ∧ (dyadicLevel t m k x).card < 2 ^ (l + 1) ∧
      2 ^ l' ≤ (dyadicLevelNhd t m nhd k x).card ∧
        (dyadicLevelNhd t m nhd k x).card < 2 ^ (l' + 1) ∧
      l ≤ l' ∧ l' ≤ Nat.log 2 t.card := by
  have hne' : (dyadicLevelNhd t m nhd k x).Nonempty :=
    hne.mono (dyadicLevel_subset_dyadicLevelNhd t m nhd k x hx)
  exact ⟨_, _, Nat.pow_log_le_self 2 hne.card_pos.ne',
    Nat.lt_pow_succ_log_self one_lt_two _,
    Nat.pow_log_le_self 2 hne'.card_pos.ne',
    Nat.lt_pow_succ_log_self one_lt_two _,
    log_card_dyadicLevel_le_log_card_dyadicLevelNhd t m nhd k x hx,
    log_card_dyadicLevelNhd_le_log_card t m nhd k x⟩

/-- **Pointwise choice of the three scales** (blueprint `lem:step2Pointwise`).

At every point of positive multiplicity there is an admissible scale triple with bound `M`. Only the
values `m j x` at the point `x` have to be bounded by `M`, and no lower bound on `M` is needed:
`1 ≤ ∑ j ∈ t, m j x` already forces `1 ≤ M`.

In particular the informal `≈` of Item 2(i) of the construction holds with the explicit constant
`Kakeya.MultiplicityFamily.scaleTripleConstant M = 4 (Nat.log 2 M + 1)`. -/
theorem exists_isScaleTriple (M : ℕ) (hM : ∀ j ∈ t, m j x ≤ M) (hx : ∀ j ∈ t, x ∈ nhd j x)
    (hpos : 1 ≤ ∑ j ∈ t, m j x) :
    ∃ k l l' : ℕ, IsScaleTriple t m nhd M k l l' x := by
  obtain ⟨k, hk_le_log, hne, hlow, hhigh⟩ := exists_innerScale t m x M hM hpos
  obtain ⟨l, l', hlow_card, hhigh_card, hlow_nhd, hhigh_nhd, l_le_l', l'_le_log⟩ :=
    exists_outerScales t m nhd k x hx hne
  obtain ⟨hmul_le_sum, hsum_le_mul⟩ :=
    Nat.scale_product_sandwich (k := k) (l := l) (N := (dyadicLevel t m k x).card)
      hlow hhigh hlow_card hhigh_card
  exact ⟨k, l, l', hk_le_log, l_le_l', l'_le_log, hmul_le_sum,
    by simpa [scaleTripleConstant, mul_assoc] using hsum_le_mul,
    hlow_card, by simpa [pow_succ, mul_comm] using hhigh_card,
    hlow_nhd, by simpa [pow_succ, mul_comm] using hhigh_nhd⟩

/-- **The box of admissible scale triples** (blueprint `def:scaleTripleBox`): the triple product of
ranges containing every triple allowed by Item (a) of `IsScaleTriple` with `T = t.card`, *except*
for the requirement `l ≤ l'`, which is dropped.

Dropping `l ≤ l'` loses nothing: the box is only ever used as a finite set that *contains* every
admissible triple, and enlarging it only enlarges `scalePigeonholeConstant`. It is nonempty,
`(0, 0, 0)` always belonging to it. -/
def scaleTripleBox (M T : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  Finset.range (Nat.log 2 M + 1) ×ˢ Finset.range (Nat.log 2 T + 1) ×ˢ
    Finset.range (Nat.log 2 T + 1)

/-- **The number of scale triples** (blueprint `lem:cardScaleTripleBox`):
`|Box(M, T)| = (Nat.log 2 M + 1)(Nat.log 2 T + 1)²`. In particular the box is nonempty. -/
theorem card_scaleTripleBox (M T : ℕ) :
    (scaleTripleBox M T).card
      = dyadicPigeonholeNatConstant M * dyadicPigeonholeNatConstant T ^ 2 := by
  simp [scaleTripleBox, dyadicPigeonholeNatConstant, pow_two]

/-- **Constant in `Kakeya.MultiplicityFamily.exists_isScaleTriple_lintegral_le`** (blueprint
`def:scalePigeonholeConstant`): the number `|Box(M, T)|` of scale triples, which by
`card_scaleTripleBox` equals `(Nat.log 2 M + 1)(Nat.log 2 T + 1)²`.

Here `M` bounds the fiberwise multiplicities and `T = t.card`. The constant is *defined* as the
cardinality of `scaleTripleBox`, keeping the pigeonholing argument independent of the arithmetic.
It is the explicit form of the informal count `≲ (log |𝒱|)(log |𝒲|)²`: the single
logarithmic factor comes from the inner scale and the squared factor from the pair of outer scales.
It depends only on `M` and `T`; in particular it does *not* depend on the neighbourhood assignment
or on the ambient dimension. -/
def scalePigeonholeConstant (M T : ℕ) : ℕ := (scaleTripleBox M T).card

/-- **The level sets cover the support** (blueprint `lem:step2LevelSetCover`).

Together with `setOf_isScaleTriple_subset_setOf_one_le`, which gives the reverse inclusion for the
union, this says that the level sets `Ω_M(c)`, `c ∈ Box(M, t.card)`, cover `{m ≥ 1}` exactly. -/
theorem setOf_one_le_subset_biUnion_scaleTripleBox (M : ℕ) (hM : ∀ j ∈ t, ∀ y, m j y ≤ M)
    (hnhd : ∀ y : X, ∀ j ∈ t, y ∈ nhd j y) :
    {x | 1 ≤ ∑ j ∈ t, m j x}
      ⊆ ⋃ c ∈ scaleTripleBox M t.card, {x | IsScaleTriple t m nhd M c.1 c.2.1 c.2.2 x} := by
  intro x hx
  obtain ⟨k, l, l', h⟩ :=
    exists_isScaleTriple t m nhd x M (fun j hj => hM j hj x) (hnhd x) hx
  have hmem : (k, l, l') ∈ scaleTripleBox M t.card := by
    simp only [scaleTripleBox, Finset.mem_product, Finset.mem_range_succ_iff]
    exact ⟨h.inner_le_log, h.outer_le_outerNhd.trans h.outerNhd_le_log_card,
      h.outerNhd_le_log_card⟩
  exact Set.mem_biUnion hmem h

/-- **Pigeonholing the three scales** (blueprint `lem:step2LevelSetPigeonhole`).

A single triple `c ∈ Box(M, t.card)` whose level set carries at least a
`scalePigeonholeConstant M t.card`-th of the total multiplicity mass. No measurability of the level
sets is needed: the only properties of the lower integral used are monotonicity in the set and
finite subadditivity. No nonemptiness of `t` is required either: the only nonemptiness the
pigeonholing uses is that of `scaleTripleBox M t.card`, which holds unconditionally since
`(0, 0, 0)` always belongs to it.

The remaining constraint `l ≤ l'` of Item (a) of `IsScaleTriple` then holds automatically as soon as
the level set is nonempty, which is the case whenever the right-hand side is nonzero.

This is the explicit form of the mass-preservation property `∫_Ω μ(𝒱', Y) ≈ ∫ μ(𝒱', Y)` required in
Item 2 of the construction. -/
theorem exists_isScaleTriple_lintegral_le [MeasurableSpace X] (μ : Measure X) (M : ℕ)
    (hM : ∀ j ∈ t, ∀ y, m j y ≤ M) (hnhd : ∀ y : X, ∀ j ∈ t, y ∈ nhd j y) :
    ∃ c ∈ scaleTripleBox M t.card,
      (scalePigeonholeConstant M t.card : ℝ≥0∞)⁻¹ * ∫⁻ x, ((∑ j ∈ t, m j x : ℕ) : ℝ≥0∞) ∂μ
        ≤ ∫⁻ x in {x | IsScaleTriple t m nhd M c.1 c.2.1 c.2.2 x},
            ((∑ j ∈ t, m j x : ℕ) : ℝ≥0∞) ∂μ := by
  -- The integrand vanishes off `{x | 1 ≤ ∑ j ∈ t, m j x}`, so integrals over `X` and over that set
  -- agree; the box is nonempty since `(0, 0, 0)` belongs to it.
  have h_lintegral_eq : ∫⁻ x, ((∑ j ∈ t, m j x : ℕ) : ℝ≥0∞) ∂μ
      = ∫⁻ x in {x | 1 ≤ ∑ j ∈ t, m j x}, ((∑ j ∈ t, m j x : ℕ) : ℝ≥0∞) ∂μ :=
    (MeasureTheory.setLIntegral_eq_of_support_subset
      fun x hx => Nat.one_le_iff_ne_zero.mpr (Nat.cast_ne_zero.mp hx)).symm
  have h_box_nonempty : (scaleTripleBox M t.card).Nonempty :=
    ⟨(0, 0, 0), by simp [scaleTripleBox]⟩
  obtain ⟨c, hc_mem, hc⟩ :=
    MeasureTheory.exists_card_inv_mul_setLIntegral_le μ h_box_nonempty
      (fun c => {x | IsScaleTriple t m nhd M c.1 c.2.1 c.2.2 x})
      (fun x => ((∑ j ∈ t, m j x : ℕ) : ℝ≥0∞))
      (setOf_one_le_subset_biUnion_scaleTripleBox t m nhd M hM hnhd)
  exact ⟨c, hc_mem, by rwa [scalePigeonholeConstant, h_lintegral_eq]⟩

end Kakeya.MultiplicityFamily

/-! ## Step 2 for a family of shaded convex bodies

The remainder of this file specializes the abstract multiplicity-family pigeonholing above to a
`ShadedBody.FactorFamily`. It fixes the selected triple through
`ShadedBody.FactorFamily.step2'`, proves its range, containment, pointwise, and mass-retention
properties directly, and then defines `ShadedBody.FactorFamily.step2` for the fixed at-scale Step 1
family.
-/
open MeasureTheory Convexity Kakeya
open scoped NNReal ENNReal

namespace Kakeya

/-! ### The two constants of Step 2 -/

/-- **Constant in `ShadedBody.FactorFamily.step2'`, pointwise form** (blueprint
`def:factoringStep2PointwiseConstant`): `C(N) = 4 (Nat.log 2 N + 1)`, the constant
`Kakeya.MultiplicityFamily.scaleTripleConstant` of the abstract layer evaluated at the bound
`M = N`.

Taking `M = N` is legitimate because the fiberwise multiplicities are bounded by `N`
(`ShadedBody.fiberMultiplicity_le_card`), and enlarging `M` only enlarges the constant
(`Kakeya.scaleTripleConstant_le_factoringStep2PointwiseConstant`). -/
def factoringStep2PointwiseConstant (N : ℕ) : ℕ := MultiplicityFamily.scaleTripleConstant N

/-- **Constant in `ShadedBody.FactorFamily.step2'`, loss form** (blueprint
`def:factoringStep2PigeonholeConstant`): `C(N) = |Box(N, N)|`, the constant
`Kakeya.MultiplicityFamily.scalePigeonholeConstant` of the abstract layer evaluated at the bounds
`M = N` and `T = N`.

Its closed form `(Nat.log 2 N + 1) ^ 3` is `Kakeya.factoringStep2PigeonholeConstant_eq`. Taking
`M = T = N` is legitimate because the fiberwise multiplicities are bounded by `N`
(`ShadedBody.fiberMultiplicity_le_card`) and the surviving blocks number at most `N`
(`Finset.card_le_card_of_subset_image`), and enlarging `M` and `T` only enlarges the constant
(`Kakeya.scalePigeonholeConstant_le_factoringStep2PigeonholeConstant`). -/
def factoringStep2PigeonholeConstant (N : ℕ) : ℕ := MultiplicityFamily.scalePigeonholeConstant N N

/-- **Closed form of the Step 2 loss constant** (blueprint
`lem:factoringStep2PigeonholeConstantEq`): `C(N) = (Nat.log 2 N + 1) ^ 3`. No hypothesis on `N` is
needed; at `N = 0` both sides are `1`. -/
theorem factoringStep2PigeonholeConstant_eq (N : ℕ) :
    factoringStep2PigeonholeConstant N = (Nat.log 2 N + 1) ^ 3 := by
  rw [factoringStep2PigeonholeConstant, MultiplicityFamily.scalePigeonholeConstant,
    MultiplicityFamily.card_scaleTripleBox, dyadicPigeonholeNatConstant]
  ring

/-- **Both Step 2 constants are positive** (blueprint `lem:factoringStep2ConstantPos`):
`1 ≤ C_pigeonhole(N)` and `4 ≤ C_pointwise(N)`, as inequalities of natural numbers. No hypothesis
on `N` is needed: at `N = 0` the constants are `1` and `4`.

Nonvanishing of `Kakeya.factoringStep2PigeonholeConstant N` *in `ℕ`* is the side condition of
`ENNReal.coe_inv_mul_le_of_coe_inv_mul_le_of_inv_natCast_mul_le`. -/
theorem factoringStep2Constant_pos (N : ℕ) :
    1 ≤ factoringStep2PigeonholeConstant N ∧ 4 ≤ factoringStep2PointwiseConstant N := by
  rw [factoringStep2PigeonholeConstant_eq, factoringStep2PointwiseConstant,
    MultiplicityFamily.scaleTripleConstant, dyadicPigeonholeNatConstant]
  exact ⟨Nat.one_le_pow _ _ (by omega), by omega⟩

/-- **Monotonicity of the Step 2 loss constant** (blueprint `lem:factoringStep2ConstantMono`): for
`M ≤ N` and `T ≤ N`, the abstract constant at `(M, T)` is at most the Step 2 constant at `N`.

This is what makes the substitution `M = T = N` of `Kakeya.factoringStep2PigeonholeConstant`
legitimate. -/
theorem scalePigeonholeConstant_le_factoringStep2PigeonholeConstant {M T N : ℕ} (hM : M ≤ N)
    (hT : T ≤ N) :
    MultiplicityFamily.scalePigeonholeConstant M T ≤ factoringStep2PigeonholeConstant N := by
  simp only [factoringStep2PigeonholeConstant, MultiplicityFamily.scalePigeonholeConstant,
    MultiplicityFamily.card_scaleTripleBox, dyadicPigeonholeNatConstant]
  exact Nat.mul_le_mul (Nat.add_le_add_right (Nat.log_mono_right hM) 1)
    (Nat.pow_le_pow_left (Nat.add_le_add_right (Nat.log_mono_right hT) 1) 2)

/-- **Monotonicity of the Step 2 pointwise constant** (blueprint
`lem:factoringStep2PointwiseConstantMono`): for `M ≤ N`, the abstract pointwise constant at `M` is
at most the Step 2 pointwise constant at `N`. -/
theorem scaleTripleConstant_le_factoringStep2PointwiseConstant {M N : ℕ} (hM : M ≤ N) :
    MultiplicityFamily.scaleTripleConstant M ≤ factoringStep2PointwiseConstant N :=
  Nat.mul_le_mul_left 4 (Nat.add_le_add_right (Nat.log_mono_right hM) 1)

end Kakeya

namespace ShadedBody

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {ι κ : Type*} [DecidableEq κ]

/-! ### The data of Step 2 -/

/-- **The neighbourhood assignment of the data of Step 2** (blueprint `def:factoringStep2Data`):
`𝒩_j(x) = closedBall x w₁`, the same ball for every block `j`. Nothing relates `w₁` to the bodies
`W j`; the only property used is `x ∈ 𝒩_j(x)`, which holds as soon as `0 ≤ w₁`.

The abstract layer takes a family indexed by the block, so a per-block radius is permitted there;
the family is constant here because Step 1 delivers no common radius, and the value of `w₁` is
supplied to the statements below as a parameter. -/
def step2Nhd (w₁ : ℝ) : κ → E → Set E := fun _ x => Metric.closedBall x w₁

/-- **The level set `Ω_N(k, l, l')` of the data of Step 2** (blueprint `def:factoringStep2Data`):
the set of points at which `(k, l, l')` is an admissible scale triple with bound `M = N`, in the
sense of `Kakeya.MultiplicityFamily.IsScaleTriple`, for the multiplicity family
`fiberMultiplicity F u'` over the selected blocks `t'` and the neighbourhood assignment
`step2Nhd w₁`, where `u' = {i ∈ u | F.parent i ∈ t'}`. -/
noncomputable def step2LevelSet (F : FactorFamily E ι κ) (u : Finset ι) (t' : Finset κ)
    (w₁ : ℝ) (N k l l' : ℕ) : Set E :=
  {x | MultiplicityFamily.IsScaleTriple t'
    (fiberMultiplicity F {i ∈ u | F.parent i ∈ t'}) (step2Nhd w₁) N k l l' x}

/-! ### Elementary properties of the data of Step 2 -/

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- **The abstract total function is the multiplicity of the surviving family** (blueprint
`lem:factoringStep2Total`): `m(x) = ∑_{j ∈ t'} μ(𝒱'_j, Y)(x) = μ(𝒱', Y)(x)`, an equality of
natural numbers valid at every `x`.

This is the single bridge between the abstract layer of `Kakeya/Factoring/Step2.lean`, phrased in
terms of `m`, and the concrete layer of this file, phrased in terms of
`pointwiseMultiplicity`. -/
theorem sum_fiberMultiplicity_eq_pointwiseMultiplicity (F : FactorFamily E ι κ)
    (u : Finset ι) (t' : Finset κ) (x : E) :
    ∑ j ∈ t', fiberMultiplicity F {i ∈ u | F.parent i ∈ t'} j x
      = pointwiseMultiplicity {i ∈ u | F.parent i ∈ t'} F.innerBody x :=
  (pointwiseMultiplicity_eq_sum_fiberwise {i ∈ u | F.parent i ∈ t'} t' F.parent F.innerBody x
    fun _ hi => (Finset.mem_filter.mp hi).2).symm

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- **The fiberwise multiplicities are bounded by the size of the original family** (blueprint
`lem:factoringStep2MultBound`): `m_j(x) ≤ |u'_j| ≤ |u'| ≤ N`, with `N = |s|`.

Consequently `M = N` is admissible in the abstract lemmas
`Kakeya.MultiplicityFamily.exists_isScaleTriple` and
`Kakeya.MultiplicityFamily.exists_isScaleTriple_lintegral_le`. -/
theorem fiberMultiplicity_le_card (F : FactorFamily E ι κ) {u : Finset ι}
    (hu : u ⊆ F.innerSet) (t' : Finset κ) (j : κ) (x : E) :
    fiberMultiplicity F {i ∈ u | F.parent i ∈ t'} j x ≤ F.innerSet.card :=
  (pointwiseMultiplicity_le_card _ _ _).trans <| Finset.card_le_card <|
    ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _)).trans hu

/-- **The total mass of the surviving multiplicity is its shading mass** (blueprint
`lem:factoringStep2MassIdentity`): `∫ μ(𝒱', Y) = ∑_{i ∈ u'} |Y (V i)|`, both sides read in
`[0, ∞]`.

Read through `ShadedBody.sum_fiberMultiplicity_eq_pointwiseMultiplicity`, the left-hand side is the
total mass `∫ m` appearing in `Kakeya.MultiplicityFamily.exists_isScaleTriple_lintegral_le`. -/
theorem lintegral_pointwiseMultiplicity_eq_sum_volume_shade (F : FactorFamily E ι κ)
    (u : Finset ι) (t' : Finset κ) :
    ∫⁻ x, (pointwiseMultiplicity {i ∈ u | F.parent i ∈ t'} F.innerBody x : ℝ≥0∞)
      = ∑ i ∈ {i ∈ u | F.parent i ∈ t'}, volume (F.innerBody i).shade :=
  (sum_volume_shade_eq_lintegral_pointwiseMultiplicity ..).symm

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- **The support of the surviving multiplicity is the shaded union** (blueprint
`lem:factoringStep2Support`): `{x | 1 ≤ μ(𝒱', Y)(x)} = U(𝒱', Y)`.

Read through `ShadedBody.sum_fiberMultiplicity_eq_pointwiseMultiplicity`, the left-hand side is the
set `{x | 1 ≤ m x}` of `Kakeya.MultiplicityFamily.setOf_isScaleTriple_subset_setOf_one_le`, which
turns that inclusion into Item (b) of the fixed Step 2 construction. -/
theorem setOf_one_le_pointwiseMultiplicity_eq_iUnion_shade (F : FactorFamily E ι κ)
    (u : Finset ι) (t' : Finset κ) :
    {x : E | 1 ≤ pointwiseMultiplicity {i ∈ u | F.parent i ∈ t'} F.innerBody x}
      = ⋃ i ∈ {i ∈ u | F.parent i ∈ t'}, (F.innerBody i).shade := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop, ← pointwiseMultiplicity_pos_iff]
  omega

/-! ### Properties of Step 2 level sets -/

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- **Item (c) of the fixed Step 2 construction holds for every triple** (blueprint
`lem:factoringStep2Pointwise`): the five estimates are the unfolding of membership in
`Ω_N(k, l, l')`, so no hypothesis on `w₁`, on `N` or on `x` beyond that membership is needed. -/
theorem bounds_of_mem_step2LevelSet (F : FactorFamily E ι κ) (u : Finset ι)
    (t' : Finset κ) (w₁ : ℝ) (N k l l' : ℕ) {x : E}
    (hx : x ∈ step2LevelSet F u t' w₁ N k l l') :
    2 ^ k * 2 ^ l
        ≤ pointwiseMultiplicity {i ∈ u | F.parent i ∈ t'} F.innerBody x ∧
      pointwiseMultiplicity {i ∈ u | F.parent i ∈ t'} F.innerBody x
        ≤ Kakeya.factoringStep2PointwiseConstant N * (2 ^ k * 2 ^ l) ∧
      2 ^ l ≤ (MultiplicityFamily.dyadicLevel t'
        (fiberMultiplicity F {i ∈ u | F.parent i ∈ t'}) k x).card ∧
      (MultiplicityFamily.dyadicLevel t'
        (fiberMultiplicity F {i ∈ u | F.parent i ∈ t'}) k x).card < 2 * 2 ^ l ∧
      2 ^ l' ≤ (MultiplicityFamily.dyadicLevelNhd t'
        (fiberMultiplicity F {i ∈ u | F.parent i ∈ t'}) (step2Nhd w₁) k x).card ∧
      (MultiplicityFamily.dyadicLevelNhd t'
        (fiberMultiplicity F {i ∈ u | F.parent i ∈ t'}) (step2Nhd w₁) k x).card
        < 2 * 2 ^ l' := by
  have hst : MultiplicityFamily.IsScaleTriple t'
    (fiberMultiplicity F {i ∈ u | F.parent i ∈ t'}) (step2Nhd w₁) N k l l' x := hx
  rw [← sum_fiberMultiplicity_eq_pointwiseMultiplicity F u t' x]
  exact ⟨hst.mul_le_sum, hst.sum_le_mul, hst.le_card_dyadicLevel, hst.card_dyadicLevel_lt,
    hst.le_card_dyadicLevelNhd, hst.card_dyadicLevelNhd_lt⟩

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- **Item (a) of the fixed Step 2 construction holds for every triple in the box** (blueprint
`lem:factoringStep2BoxRange`).

Only `|t'| ≤ N` is used, through `Finset.card_le_card_of_subset_image`; the point of taking the
second argument of the box equal to `|t'|` and then relaxing to `N` is that the three bounds
involve `N = |F.innerSet|` alone. -/
theorem le_log_card_of_mem_scaleTripleBox (F : FactorFamily E ι κ)
    {u : Finset ι} (hu : u ⊆ F.innerSet)
    {t' : Finset κ} (ht' : t' ⊆ u.image F.parent) {c : ℕ × ℕ × ℕ}
    (hc : c ∈ MultiplicityFamily.scaleTripleBox F.innerSet.card t'.card) :
    c.1 ≤ Nat.log 2 F.innerSet.card ∧ c.2.1 ≤ Nat.log 2 F.innerSet.card ∧
      c.2.2 ≤ Nat.log 2 F.innerSet.card := by
  simp only [MultiplicityFamily.scaleTripleBox, Finset.mem_product,
    Finset.mem_range_succ_iff] at hc
  have h_log : Nat.log 2 t'.card ≤ Nat.log 2 F.innerSet.card :=
    Nat.log_mono_right (Finset.card_le_card_of_subset_image hu ht')
  exact ⟨hc.1, hc.2.1.trans h_log, hc.2.2.trans h_log⟩

omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- **Item (b) of the fixed Step 2 construction holds for every triple** (blueprint
`lem:factoringStep2Containment`): `Ω ⊆ U(𝒱', Y)`, for every triple, including those for which
`Ω = ∅`. -/
theorem step2LevelSet_subset_iUnion_shade (F : FactorFamily E ι κ) (u : Finset ι)
    (t' : Finset κ) (w₁ : ℝ) (N k l l' : ℕ) :
    step2LevelSet F u t' w₁ N k l l'
      ⊆ ⋃ i ∈ {i ∈ u | F.parent i ∈ t'}, (F.innerBody i).shade := by
  rw [← setOf_one_le_pointwiseMultiplicity_eq_iUnion_shade F u t']
  intro x hx
  rw [Set.mem_setOf_eq, ← sum_fiberMultiplicity_eq_pointwiseMultiplicity F u t' x]
  exact MultiplicityFamily.setOf_isScaleTriple_subset_setOf_one_le t'
    (fiberMultiplicity F {i ∈ u | F.parent i ∈ t'}) (step2Nhd w₁) N k l l' hx

/-- **Item (d) of the fixed Step 2 construction is the abstract mass bound retranslated**
(blueprint `lem:factoringStep2LevelSetMass`).

The hypothesis is the conclusion of `Kakeya.MultiplicityFamily.exists_isScaleTriple_lintegral_le`
at `M = |s|` and `T = |t'|`; the conclusion is the same inequality read with the larger constant
`Kakeya.factoringStep2PigeonholeConstant |s|`, with the integrand rewritten by
`ShadedBody.sum_fiberMultiplicity_eq_pointwiseMultiplicity` and the total mass evaluated by
`ShadedBody.lintegral_pointwiseMultiplicity_eq_sum_volume_shade`. -/
theorem inv_mul_sum_volume_shade_le_lintegral_step2LevelSet (F : FactorFamily E ι κ)
    {u : Finset ι} (hu : u ⊆ F.innerSet)
    {t' : Finset κ} (ht' : t' ⊆ u.image F.parent) (w₁ : ℝ) (k l l' : ℕ)
    (h : ((MultiplicityFamily.scalePigeonholeConstant F.innerSet.card t'.card : ℝ≥0∞))⁻¹
          * ∫⁻ x, ((∑ j ∈ t',
            fiberMultiplicity F {i ∈ u | F.parent i ∈ t'} j x : ℕ) : ℝ≥0∞)
        ≤ ∫⁻ x in step2LevelSet F u t' w₁ F.innerSet.card k l l',
            ((∑ j ∈ t',
              fiberMultiplicity F {i ∈ u | F.parent i ∈ t'} j x : ℕ) : ℝ≥0∞)) :
    ((Kakeya.factoringStep2PigeonholeConstant F.innerSet.card : ℝ≥0∞))⁻¹
        * ∑ i ∈ {i ∈ u | F.parent i ∈ t'}, volume (F.innerBody i).shade
      ≤ ∫⁻ x in step2LevelSet F u t' w₁ F.innerSet.card k l l',
          (pointwiseMultiplicity
            {i ∈ u | F.parent i ∈ t'} F.innerBody x : ℝ≥0∞) := by
  -- Rewrite both integrands in terms of `pointwiseMultiplicity`, evaluate the total mass, and
  -- weaken the abstract constant to `Kakeya.factoringStep2PigeonholeConstant F.innerSet.card`.
  simp_rw [sum_fiberMultiplicity_eq_pointwiseMultiplicity F u t'] at h
  rw [← lintegral_pointwiseMultiplicity_eq_sum_volume_shade F u t']
  exact ENNReal.inv_natCast_mul_le_of_le
    (scalePigeonholeConstant_le_factoringStep2PigeonholeConstant le_rfl
      (Finset.card_le_card_of_subset_image hu ht')) h

namespace FactorFamily

/-- **Step 2 of the factoring construction** (blueprint `def:factoringStep2`): the fixed triple
of dyadic exponents selected from the Step 2 data.

The choice is noncomputable because the pigeonhole lemma is existential. Once made, it is fixed:
later declarations state properties of this triple rather than quantify over arbitrary valid
Step 2 selections. -/
noncomputable def step2' (F : FactorFamily E ι κ) {u : Finset ι}
    (hu : u ⊆ F.innerSet) (t' : Finset κ)
    {w₁ : ℝ} (hw₁ : 0 ≤ w₁) : ℕ × ℕ × ℕ :=
  (MultiplicityFamily.exists_isScaleTriple_lintegral_le (t := t')
    (m := fiberMultiplicity F {i ∈ u | F.parent i ∈ t'})
    (nhd := step2Nhd w₁) (μ := volume) (M := F.innerSet.card)
    (fun j _ y ↦ fiberMultiplicity_le_card F hu t' j y)
    (fun _ _ _ ↦ Metric.mem_closedBall_self hw₁)).choose

private theorem step2'_spec (F : FactorFamily E ι κ) {u : Finset ι}
    (hu : u ⊆ F.innerSet) (t' : Finset κ) {w₁ : ℝ} (hw₁ : 0 ≤ w₁) :
    F.step2' hu t' hw₁ ∈
        MultiplicityFamily.scaleTripleBox F.innerSet.card t'.card ∧
      ((MultiplicityFamily.scalePigeonholeConstant F.innerSet.card t'.card : ℝ≥0∞))⁻¹
          * ∫⁻ x, ((∑ j ∈ t',
            fiberMultiplicity F {i ∈ u | F.parent i ∈ t'} j x : ℕ) : ℝ≥0∞)
        ≤ ∫⁻ x in step2LevelSet F u t' w₁ F.innerSet.card
            (F.step2' hu t' hw₁).1 (F.step2' hu t' hw₁).2.1
            (F.step2' hu t' hw₁).2.2,
            ((∑ j ∈ t',
              fiberMultiplicity F {i ∈ u | F.parent i ∈ t'} j x : ℕ) : ℝ≥0∞) :=
  (MultiplicityFamily.exists_isScaleTriple_lintegral_le (t := t')
      (m := fiberMultiplicity F {i ∈ u | F.parent i ∈ t'})
      (nhd := step2Nhd w₁) (μ := volume) (M := F.innerSet.card)
      (fun j _ y ↦ fiberMultiplicity_le_card F hu t' j y)
      (fun _ _ _ ↦ Metric.mem_closedBall_self hw₁)).choose_spec

/-- The fixed Step 2 level set determined by `F.step2' hu t' hw₁`. -/
noncomputable def step2Set' (F : FactorFamily E ι κ) {u : Finset ι}
    (hu : u ⊆ F.innerSet) (t' : Finset κ)
    {w₁ : ℝ} (hw₁ : 0 ≤ w₁) : Set E :=
  step2LevelSet F u t' w₁ F.innerSet.card
    (F.step2' hu t' hw₁).1 (F.step2' hu t' hw₁).2.1 (F.step2' hu t' hw₁).2.2

/-- **Range of the fixed Step 2 triple** (blueprint `lem:factoringStep2Pigeonhole`, item (a)). -/
theorem step2'_range (F : FactorFamily E ι κ) {u : Finset ι}
    (hu : u ⊆ F.innerSet) {t' : Finset κ} (ht' : t' ⊆ u.image F.parent)
    {w₁ : ℝ} (hw₁ : 0 ≤ w₁) :
    (F.step2' hu t' hw₁).1 ≤ Nat.log 2 F.innerSet.card ∧
      (F.step2' hu t' hw₁).2.1 ≤ Nat.log 2 F.innerSet.card ∧
      (F.step2' hu t' hw₁).2.2 ≤ Nat.log 2 F.innerSet.card :=
  le_log_card_of_mem_scaleTripleBox F hu ht' (step2'_spec F hu t' hw₁).1

/-- **Containment of the fixed Step 2 level set** (blueprint
`lem:factoringStep2Pigeonhole`, item (b)). -/
theorem step2Set'_subset_iUnion_shade (F : FactorFamily E ι κ) {u : Finset ι}
    (hu : u ⊆ F.innerSet) (t' : Finset κ)
    {w₁ : ℝ} (hw₁ : 0 ≤ w₁) :
    F.step2Set' hu t' hw₁ ⊆
      ⋃ i ∈ {i ∈ u | F.parent i ∈ t'}, (F.innerBody i).shade :=
  step2LevelSet_subset_iUnion_shade F u t' w₁ F.innerSet.card
    (F.step2' hu t' hw₁).1 (F.step2' hu t' hw₁).2.1 (F.step2' hu t' hw₁).2.2

/-- **Pointwise estimates for the fixed Step 2 triple** (blueprint
`lem:factoringStep2Pigeonhole`, item (c)). -/
theorem bounds_of_mem_step2Set' (F : FactorFamily E ι κ) {u : Finset ι}
    (hu : u ⊆ F.innerSet) (t' : Finset κ)
    {w₁ : ℝ} (hw₁ : 0 ≤ w₁) {x : E} (hx : x ∈ F.step2Set' hu t' hw₁) :
    2 ^ (F.step2' hu t' hw₁).1 * 2 ^ (F.step2' hu t' hw₁).2.1
        ≤ pointwiseMultiplicity {i ∈ u | F.parent i ∈ t'} F.innerBody x ∧
      pointwiseMultiplicity {i ∈ u | F.parent i ∈ t'} F.innerBody x
        ≤ Kakeya.factoringStep2PointwiseConstant F.innerSet.card
          * (2 ^ (F.step2' hu t' hw₁).1 * 2 ^ (F.step2' hu t' hw₁).2.1) ∧
      2 ^ (F.step2' hu t' hw₁).2.1 ≤ (MultiplicityFamily.dyadicLevel t'
        (fiberMultiplicity F {i ∈ u | F.parent i ∈ t'})
          (F.step2' hu t' hw₁).1 x).card ∧
      (MultiplicityFamily.dyadicLevel t'
        (fiberMultiplicity F {i ∈ u | F.parent i ∈ t'})
          (F.step2' hu t' hw₁).1 x).card < 2 * 2 ^ (F.step2' hu t' hw₁).2.1 ∧
      2 ^ (F.step2' hu t' hw₁).2.2 ≤ (MultiplicityFamily.dyadicLevelNhd t'
        (fiberMultiplicity F {i ∈ u | F.parent i ∈ t'}) (step2Nhd w₁)
          (F.step2' hu t' hw₁).1 x).card ∧
      (MultiplicityFamily.dyadicLevelNhd t'
        (fiberMultiplicity F {i ∈ u | F.parent i ∈ t'}) (step2Nhd w₁)
          (F.step2' hu t' hw₁).1 x).card < 2 * 2 ^ (F.step2' hu t' hw₁).2.2 :=
  bounds_of_mem_step2LevelSet F u t' w₁ F.innerSet.card
    (F.step2' hu t' hw₁).1 (F.step2' hu t' hw₁).2.1
    (F.step2' hu t' hw₁).2.2 hx

/-- **Mass retention for the fixed Step 2 triple** (blueprint
`lem:factoringStep2Pigeonhole`, item (d)). -/
theorem inv_mul_sum_volume_shade_le_lintegral_step2Set'
    (F : FactorFamily E ι κ) {u : Finset ι} (hu : u ⊆ F.innerSet)
    {t' : Finset κ} (ht' : t' ⊆ u.image F.parent) {w₁ : ℝ} (hw₁ : 0 ≤ w₁) :
    ((Kakeya.factoringStep2PigeonholeConstant F.innerSet.card : ℝ≥0∞))⁻¹
        * ∑ i ∈ {i ∈ u | F.parent i ∈ t'}, volume (F.innerBody i).shade
      ≤ ∫⁻ x in F.step2Set' hu t' hw₁,
          (pointwiseMultiplicity
            {i ∈ u | F.parent i ∈ t'} F.innerBody x : ℝ≥0∞) :=
  inv_mul_sum_volume_shade_le_lintegral_step2LevelSet F hu ht' w₁
    (F.step2' hu t' hw₁).1 (F.step2' hu t' hw₁).2.1
      (F.step2' hu t' hw₁).2.2 (step2'_spec F hu t' hw₁).2

end FactorFamily


end ShadedBody

/-! ### Steps 1 and 2 chained at a scale `δ`

The two steps are stated for *different* families. Step 1 compares the surviving family with the
original one, bounding the shading mass `∑_{i ∈ s} |Y (V i)|` of all of `𝒱` by a multiple of the
shading mass `∑_{i ∈ u'} |Y (V i)|` of `𝒱'`. Step 2 does not mention `𝒱` at all, bounding that same
`∑_{i ∈ u'} |Y (V i)|` by a multiple of the multiplicity mass of `𝒱'` over the level set `Ω`. The
shared quantity occurs on the large side of the first inequality and on the small side of the
second, which is what makes them chain and why the composite constant is the plain product.

The two conclusions invert their constants in different places and in different types:
`ShadedBody.FactorFamily.isCRefinement_step1` inverts an element of `ℝ≥0` before coercing,
whereas Item (d) of
the fixed Step 2 construction inverts a natural number after coercing into `ℝ≥0∞`. Reconciling the
two is done once and for all in
`ENNReal.coe_inv_mul_le_of_coe_inv_mul_le_of_inv_natCast_mul_le`, so that the corollary below can
quote both items verbatim.
-/

namespace Kakeya

/-- **Constant in `ShadedBody.FactorFamily.step2`** (blueprint
`def:factoringStep1Step2AtScaleConstant`): the product `C₁(n, N, δ) C₂(N)` of the Step 1 loss
constant `Kakeya.factoringStep1AtScaleConstant` with the Step 2 loss constant
`Kakeya.factoringStep2PigeonholeConstant`, the latter read in `ℝ≥0`.

The product is formed in `ℝ≥0` so that its inverse is again in `ℝ≥0`, matching
`ShadedBody.FactorFamily.isCRefinement_step1`. -/
noncomputable def factoringStep1Step2AtScaleConstant (n N : ℕ) (δ : ℝ≥0) : ℝ≥0 :=
  factoringStep1AtScaleConstant n N δ * (factoringStep2PigeonholeConstant N : ℝ≥0)

/-- **The inverse of the composite constant factors** (blueprint
`lem:factoringStep1Step2ConstantInv`): inversion in `ℝ≥0` is multiplicative, so no hypotheses on
the factors, on `δ` or on `N` are needed. -/
theorem factoringStep1Step2AtScaleConstant_inv (n N : ℕ) (δ : ℝ≥0) :
    (factoringStep1Step2AtScaleConstant n N δ)⁻¹
      = (factoringStep1AtScaleConstant n N δ)⁻¹
        * ((factoringStep2PigeonholeConstant N : ℝ≥0))⁻¹ := by
  rw [factoringStep1Step2AtScaleConstant, mul_inv, mul_comm]

/-- **The composite constant as a real number** (blueprint `lem:factoringStep1Step2ConstantCoe`):
`↑C(n, N, δ) = 2 (1 + n + log₂ (n !) + log₂ N + n log₂ (1 / δ)) (Nat.log 2 N + 1) ^ 3`.

As in `Kakeya.coe_factoringStep1AtScaleConstant`, it is the coercion `ℝ≥0 → ℝ` which licenses
writing the first bracket without a positive part; that is the only role of `0 < δ ≤ 1` and
`1 ≤ N`. -/
theorem coe_factoringStep1Step2AtScaleConstant (n : ℕ) {N : ℕ} (hN : 1 ≤ N) {δ : ℝ≥0}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (factoringStep1Step2AtScaleConstant n N δ : ℝ)
      = 2 * (1 + n + Real.logb 2 (n.factorial : ℝ) + Real.logb 2 N
          + n * Real.logb 2 (1 / (δ : ℝ))) * ((Nat.log 2 N + 1 : ℕ) : ℝ) ^ 3 := by
  rw [factoringStep1Step2AtScaleConstant, NNReal.coe_mul, NNReal.coe_natCast,
    coe_factoringStep1AtScaleConstant n hN hδ hδ1, factoringStep2PigeonholeConstant_eq]
  push_cast
  ring

end Kakeya

namespace ShadedBody

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {ι κ : Type*} [DecidableEq κ]

namespace FactorFamily

/-- **Step 2 for the fixed Step 1 family at scale `δ`** (blueprint
`cor:factoringStep1Step2AtScale`): the fixed triple of dyadic exponents obtained by applying
`F.step2'` to the Step 0 inner set and the fixed Step 1 outer set. -/
noncomputable def step2 [Nontrivial E] (F : FactorFamily E ι κ) {δ : ℝ≥0}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) {w₁ : ℝ} (hw₁ : 0 ≤ w₁) :
    ℕ × ℕ × ℕ :=
  F.step2' F.innerSet_step0_subset (F.step1 hδ hdisc).outerSet hw₁

/-- The fixed Step 2 level set for the fixed Step 1 family at scale `δ`. -/
noncomputable def step2Set [Nontrivial E] (F : FactorFamily E ι κ) {δ : ℝ≥0}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) {w₁ : ℝ} (hw₁ : 0 ≤ w₁) : Set E :=
  F.step2Set' F.innerSet_step0_subset (F.step1 hδ hdisc).outerSet hw₁

/-- The three exponents of the fixed at-scale Step 2 triple are bounded by the logarithm of the
original family cardinality. -/
theorem step2_range [Nontrivial E] (F : FactorFamily E ι κ) {δ : ℝ≥0}
    (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ) {w₁ : ℝ} (hw₁ : 0 ≤ w₁) :
    (F.step2 hδ hdisc hw₁).1 ≤ Nat.log 2 F.innerSet.card ∧
      (F.step2 hδ hdisc hw₁).2.1 ≤ Nat.log 2 F.innerSet.card ∧
      (F.step2 hδ hdisc hw₁).2.2 ≤ Nat.log 2 F.innerSet.card := by
  simpa only [step2] using F.step2'_range F.innerSet_step0_subset
    (F.outerSet_step1_subset_image hδ hdisc) hw₁

/-- The fixed at-scale Step 2 level set lies in the shaded union of the fixed Step 1 family. -/
theorem step2Set_subset_iUnion_shade [Nontrivial E] (F : FactorFamily E ι κ)
    {δ : ℝ≥0} (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ)
    {w₁ : ℝ} (hw₁ : 0 ≤ w₁) :
    F.step2Set hδ hdisc hw₁ ⊆
      ⋃ i ∈ (F.step1 hδ hdisc).innerSet, (F.innerBody i).shade := by
  simpa only [step2Set, innerSet_step1] using F.step2Set'_subset_iUnion_shade
    F.innerSet_step0_subset (F.step1 hδ hdisc).outerSet hw₁

/-- The pointwise Step 2 estimates for the fixed at-scale triple and level set. -/
theorem bounds_of_mem_step2Set [Nontrivial E] (F : FactorFamily E ι κ)
    {δ : ℝ≥0} (hδ : 0 < δ) (hdisc : F.InnerIsDiscretizedAtScale δ)
    {w₁ : ℝ} (hw₁ : 0 ≤ w₁) {x : E} (hx : x ∈ F.step2Set hδ hdisc hw₁) :
    2 ^ (F.step2 hδ hdisc hw₁).1 * 2 ^ (F.step2 hδ hdisc hw₁).2.1
        ≤ pointwiseMultiplicity (F.step1 hδ hdisc).innerSet F.innerBody x ∧
      pointwiseMultiplicity (F.step1 hδ hdisc).innerSet F.innerBody x
        ≤ Kakeya.factoringStep2PointwiseConstant F.innerSet.card
          * (2 ^ (F.step2 hδ hdisc hw₁).1 * 2 ^ (F.step2 hδ hdisc hw₁).2.1) ∧
      2 ^ (F.step2 hδ hdisc hw₁).2.1 ≤ (MultiplicityFamily.dyadicLevel
        (F.step1 hδ hdisc).outerSet
        (fiberMultiplicity F (F.step1 hδ hdisc).innerSet)
          (F.step2 hδ hdisc hw₁).1 x).card ∧
      (MultiplicityFamily.dyadicLevel (F.step1 hδ hdisc).outerSet
        (fiberMultiplicity F (F.step1 hδ hdisc).innerSet)
          (F.step2 hδ hdisc hw₁).1 x).card < 2 * 2 ^ (F.step2 hδ hdisc hw₁).2.1 ∧
      2 ^ (F.step2 hδ hdisc hw₁).2.2 ≤ (MultiplicityFamily.dyadicLevelNhd
        (F.step1 hδ hdisc).outerSet
        (fiberMultiplicity F (F.step1 hδ hdisc).innerSet) (step2Nhd w₁)
          (F.step2 hδ hdisc hw₁).1 x).card ∧
      (MultiplicityFamily.dyadicLevelNhd (F.step1 hδ hdisc).outerSet
        (fiberMultiplicity F (F.step1 hδ hdisc).innerSet) (step2Nhd w₁)
          (F.step2 hδ hdisc hw₁).1 x).card < 2 * 2 ^ (F.step2 hδ hdisc hw₁).2.2 := by
  simpa only [step2, step2Set, innerSet_step1] using F.bounds_of_mem_step2Set'
    F.innerSet_step0_subset (F.step1 hδ hdisc).outerSet hw₁ hx

/-- Step 2 retains the inverse Step 2 loss times the shading mass of the fixed Step 1 family. -/
theorem inv_mul_sum_volume_shade_le_lintegral_step2Set [Nontrivial E]
    (F : FactorFamily E ι κ) {δ : ℝ≥0} (hδ : 0 < δ)
    (hdisc : F.InnerIsDiscretizedAtScale δ) {w₁ : ℝ} (hw₁ : 0 ≤ w₁) :
    ((Kakeya.factoringStep2PigeonholeConstant F.innerSet.card : ℝ≥0∞))⁻¹
        * ∑ i ∈ (F.step1 hδ hdisc).innerSet, volume (F.innerBody i).shade
      ≤ ∫⁻ x in F.step2Set hδ hdisc hw₁,
          (pointwiseMultiplicity
            (F.step1 hδ hdisc).innerSet F.innerBody x : ℝ≥0∞) := by
  simpa only [step2Set, innerSet_step1] using F.inv_mul_sum_volume_shade_le_lintegral_step2Set'
    F.innerSet_step0_subset (F.outerSet_step1_subset_image hδ hdisc) hw₁

/-- **Mass retention through the fixed Steps 1 and 2 at scale `δ`** (blueprint
`cor:factoringStep1Step2AtScale`). -/
theorem inv_mul_sum_volume_shade_le_lintegral_step1_step2Set [Nontrivial E]
    (F : FactorFamily E ι κ) {δ : ℝ≥0} (hδ : 0 < δ)
    (hdisc : F.InnerIsDiscretizedAtScale δ) {w₁ : ℝ} (hw₁ : 0 ≤ w₁) :
    ((Kakeya.factoringStep1Step2AtScaleConstant
      (Module.finrank ℝ E) F.innerSet.card δ)⁻¹ : ℝ≥0)
        * ∑ i ∈ F.innerSet, volume (F.innerBody i).shade
      ≤ ∫⁻ x in F.step2Set hδ hdisc hw₁,
          (pointwiseMultiplicity
            (F.step1 hδ hdisc).innerSet F.innerBody x : ℝ≥0∞) := by
  -- The two mass bounds chain; the composite constant is the plain product by definition.
  have h₁ : ((Kakeya.factoringStep1AtScaleConstant
        (Module.finrank ℝ E) F.innerSet.card δ)⁻¹ : ℝ≥0)
        * ∑ i ∈ F.innerSet, volume (F.innerBody i).shade
      ≤ ∑ i ∈ (F.step1 hδ hdisc).innerSet, volume (F.innerBody i).shade := by
    simpa using (F.isCRefinement_step1 hδ hdisc).2
  exact ENNReal.coe_inv_mul_le_of_coe_inv_mul_le_of_inv_natCast_mul_le
    (Nat.one_le_iff_ne_zero.mp (Kakeya.factoringStep2Constant_pos _).1) h₁
    (F.inv_mul_sum_volume_shade_le_lintegral_step2Set hδ hdisc hw₁)

end FactorFamily

end ShadedBody
