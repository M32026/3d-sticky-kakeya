/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.AccuracyCardExchange

/-!
# Why Section 8's branch (i) closes and Section 9's does not: the sign of the cardinality gap

GWZ prove Main Lemma 1 (§8, Lemma 8.1) and Main Lemma 2 (§9) by the *same* two-branch scheme —
apply Lemma 7.7, and in Conclusion (i) feed the every-scale hypothesis to Theorem 7.3 — but they
write the two openings differently, and only one of the two is internally consistent.  This file
localises the difference, and it is not a matter of care in writing: **the two branches need
cardinality bounds pointing in opposite directions, and only §8's direction is universally
available.**

## The two texts

*§8, proof of Lemma 8.1 (p. 30).*

> Let `ϵ₀` and `δ₀` be the output of Theorem 7.3 **with `γ/2` in place of `ϵ`**. Let `N ≥ 25/ϵ₀²`
> be an integer to be chosen later, and define `ϵ = 1/√N`. … Apply Lemma 7.7(A) to `T`, with `N`
> as above. If Conclusion (i) holds, then `T` is `δ^{-ϵ₀}` Frostman at every scale, and hence by
> Theorem 7.3(A) we have `|U(T,Y)| ≥ δ^{γ/2} ≥ δ^{2(γ/2)}(|T||T|)^{(γ/2)/2}`, **where we used the
> fact that `|T| ≤ δ^{-4}`**. … In this case, Lemma 8.1 holds with `ν = γ/2`.

*§9, proof of Main Lemma 2 from Lemma 9.1 (pp. 32–33).*

> Let `ϵ₁` and `δ₁` be the output of Theorem 7.3 **with `ϵ` as above**. … Let
> `ϵ₂ = ϵ₂(ϵ₁, ϵ_scale, β)` be a number to be chosen later (**since `ϵ₁` and `ϵ_scale` depend only
> on `β`, `ϵ₂` depends only on `β`**). … Apply Lemma 7.7(B) to `T`. If Conclusion (i) holds, then
> (provided we select `ϵ₂ ≤ ϵ₁/5`) we have that `T` is `δ^{-ϵ₁}` Katz–Tao at every scale, and hence
> by Theorem 7.3(B) we have `μ(T,Y) ≤ δ^{-ϵ}`, and thus (67) is satisfied.

`(67)` is `μ(T,Y) ≤ δ^{-ϵ}|T|^{β-ν}`.  Reading Theorem 7.3 at the outer `ϵ` makes `ϵ₁ = ϵ₁(ϵ)`,
hence `ϵ₂`, `N`, the ladder `η₁ ≤ … ≤ η_N ≤ ϵ₂` and finally `ν ≺ η₁` all depend on `ϵ` — which
contradicts both the displayed parenthetical and Main Lemma 2's own `ν = ν(β)`.  §8 has no such
defect, because it reads Theorem 7.3 at `γ/2`, an accuracy fixed by the exponent alone.

## What §8's branch actually spends its cardinality bound on

Writing `N = |T|` and `a = γ/2`, and using `|T| |T| = |T| · δ²` (the count times the volume of one
`δ`-tube), the displayed chain of §8 is `δ^{a} ≥ δ^{2a}(δ²N)^{a/2}`, and it is an **equivalence**
with GWZ's own printed side condition: `Kakeya.ML2S8Transfer.sectionEight_printed_iff` says

```
δ^{2a}(δ² N)^{a/2} ≤ δ^{a}   ↔   N ≤ δ^{-4}.
```

The exponent `-4` is *not* put in by hand here: it is `(q - p)/(u - v)` of the general comparison
below, computed from GWZ's own exponents.  That the general lemma reproduces the paper's printed
`|T| ≤ δ^{-4}` exactly is the positive control on this file's reading of the source.

## The general comparison, and the one bit that decides everything

Both branches reduce to one inequality between a `δ`-power times a cardinality power:

```
δ^p N^u ≤ δ^q N^v        (Kakeya.ML2S8Transfer.key_iff:  ↔  N^{u-v} ≤ δ^{q-p})
```

and solving for `N` inverts the inequality exactly when `u - v` changes sign
(`Kakeya.ML2S8Transfer.card_le_iff`, `Kakeya.ML2S8Transfer.le_card_iff`):

* **§8 (i).**  LHS is the `K_F(γ/2)` target, `(p, u) = (3a, a/2)`; RHS is Theorem 7.3(A)'s
  output, `(q, v) = (a, 0)`.  So `u - v = +a/2 > 0` and the side condition is the **upper**
  bound `N ≤ δ^{-4}`.
* **§9 (i).**  LHS is Theorem 7.3(B)'s output, `(p, u) = (-ε₀, 0)`; RHS is the `K_KT(β-ν)`
  goal, `(q, v) = (-ε, γ)`.  So `u - v = -γ < 0` and the side condition is the **lower**
  bound `δ^{-(ε₀-ε)/γ} ≤ N`.

The mechanism behind the sign flip is the direction of the two conclusions.  `K_F`'s conclusion is a
**lower** bound on a volume, so its cardinality factor is a *burden* placed on the branch and the
branch is helped by an upper bound on `N`; `K_KT`'s conclusion is an **upper** bound on a
multiplicity, so its cardinality factor is an *allowance* and the branch is helped only by a lower
bound on `N`.  `Kakeya.ML2S8Transfer.branchOne_side_conditions` states the two solved forms in one
theorem.

## Why that settles the transfer

* The bound §8 spends, `|T| ≤ δ^{-4}`, is a theorem of the ambient geometry for essentially
  distinct `δ`-tubes in `B₁ ⊆ ℝ³` — `Kakeya.ml1Boot.card_le`, and it is what
  `Kakeya.ml1Boot.multiplicity_le_of_frostmanAtEveryScale` (this repository's §8 branch (i)) in
  fact consumes, alongside sticky Kakeya read at the absolute accuracy `γ₀/2`.  So it is available
  in §9 too.
* **And it is inert there.**  `Kakeya.ML2S8Transfer.sectionNine_cardBound_inert`: for every
  constant `C ≥ 1` and every `ε < ε₀`, the hypothesis `N ≤ C δ^{-4}` does not give §9's branch,
  because `N = 1` satisfies it.  More generally no upper bound whatsoever does
  (`Kakeya.ML2S8Transfer.sectionNine_no_upper_bound_helps`).
* The mirror holds, so the direction claim is two-sided and the gate can fail both ways:
  `Kakeya.ML2S8Transfer.sectionEight_no_lower_bound_helps` — in §8 no *lower* bound on `N` gives
  the branch.
* The lower bound §9 would need is `δ^{-(ε₀-ε)/γ} ≤ |T|`, and the solved exponent agrees with the
  budget the development derived independently: `Kakeya.ML2S8Transfer.budget_iff_threshold` shows
  `ε₀ ≤ ε + θγ`, the hypothesis of
  `Kakeya.ML2Exchange.katzTaoGoal_of_absoluteLoss_of_card_ge_rpow`, is exactly
  `δ^{-(ε₀-ε)/γ} ≤ δ^{-θ}`.

## The asymmetry is inside §9, not between §8 and §9

§9's *other* branch is on §8's side of the dichotomy.  Branch (ii) assembles
`μ(T,Y) ⪅ μ(T[T_τ]) μ(T_τ[T_θ]) μ(T_θ)` into `μ ≤ δ^{g}|T|^{β}` with an `ε`-free gain `g`
(GWZ (68), (70) and the two displayed factor bounds), and converting that into
`μ ≤ δ^{-ε}|T|^{β-ν}` costs an **upper** bound `|T| ≤ δ^{-c}`, at the budget `cν ≤ g`
(`Kakeya.ML2S8Transfer.sectionNine_branchTwo_closes`) — and it closes at `ε = 0`.  An upper bound is
exactly what §9's setting has: `Kakeya.ml1Boot.card_le` gives `c = 4` for essentially distinct
`δ`-tubes in `B₁ ⊆ ℝ³` unconditionally, and reading GWZ Definition 3.2 at `K = B₁` turns
`Δ_max(T) ≤ δ^{-η}` into `c = 2 + η` (that last is a reading of the source's definition; it is not
a statement of this repository).  The budget reproduces the one recorded independently
in `Reduction/SpineCardBand.lean` — *"the budget `c ≤ g`, not the `4c ≤ g` the large-cardinality
branch has to pay"* — as the two instances `c = 1` and `c = 4` of
`Kakeya.ML2S8Transfer.sectionNine_branchTwo_closes`.

So within §9: branch (ii) is absorbed by the upper bound the hypotheses give, and branch (i) would
need a lower bound they do not give.  The outer `ε` is consumed at exactly one place in the whole
proof, and it is branch (i).

## Where the lower bound is, in GWZ

It is not absent from §9 — it is in the *other* branch.  Conclusion (ii) of Lemma 7.7(B) supplies
`Δ_max(T̃_ρ) ≥ ρ^{-η_j}`, GWZ's (73), and that is what (79),
`|T̃_σ[T_b]| ≳ δ̃^{2η'_{j-1}} σ^{-2-η_j}`, is extracted from — the count hypothesis Lemma 9.1
requires.  Branch (i) is the negation of Conclusion (ii); the bound is structurally unavailable
there.  Symmetrically, the lower bound §8's *statement* carries — `C_F(T, B₁) ≤ δ^{-η}` gives
`|T| ≥ δ^{-2+η}`, GWZ p. 6 and p. 29 — is the one §9 would need and does not have, because `K_KT`'s
hypothesis `Δ_max(T) ≤ δ^{-η}` is the reverse pin on the same quantity: it bounds `δ²|T|` from
*above*.  The two statements differ precisely by which side of `δ^{-2}` the count is pinned, and
each supplies the bound the other's branch (i) would need.

## What is *not* claimed

Nothing here refutes GWZ Main Lemma 2, GWZ Lemma 9.1, Theorem 7.3(B) or Lemma 8.1, and nothing here
is a counterexample to Main Lemma 2's conclusion at small cardinality — at `|T| = 1` the goal
`μ ≤ δ^{-ε}|T|^{β-ν}` reads `μ ≤ δ^{-ε}`, which is `K_KT(β)` itself and is a hypothesis.  What is
refuted is one *route*: closing §9's branch (i) at an `ε`-free accuracy by importing §8's
cardinality step.  The obstruction is at the level of the implication
`μ ≤ δ^{-ε₀} ⟹ μ ≤ δ^{-ε}|T|^{γ}`, whose second step is strictly false below the threshold —
`Kakeya.ML2Exchange.zeroThreshold_insufficient`, re-derived here as
`Kakeya.ML2S8Transfer.sectionNine_fails_at_one`.
-/

@[expose] public section

namespace Kakeya.ML2S8Transfer

/-! ## Part I — the comparison both branches reduce to -/

/-- **The comparison, cleared of both bases.**  `δ^p N^u ≤ δ^q N^v` is a statement about `N^{u-v}`
alone; everything below is this rearrangement plus the sign of `u - v`. -/
theorem key_iff {δ N : ℝ} (hδ : 0 < δ) (hN : 0 < N) (p q u v : ℝ) :
    δ ^ p * N ^ u ≤ δ ^ q * N ^ v ↔ N ^ (u - v) ≤ δ ^ (q - p) := by
  have hA : (0:ℝ) < δ ^ p := Real.rpow_pos_of_pos hδ p
  have hD : (0:ℝ) < N ^ v := Real.rpow_pos_of_pos hN v
  rw [Real.rpow_sub hN, Real.rpow_sub hδ, div_le_div_iff₀ hD hA]
  constructor <;> intro h <;> nlinarith

/-- `(δ^{a/w})^w = δ^a`, the step that solves the comparison for `N`. -/
theorem rpow_div_mul {δ : ℝ} (hδ : 0 < δ) (a w : ℝ) (hw : w ≠ 0) :
    (δ ^ (a / w)) ^ w = δ ^ a := by
  rw [← Real.rpow_mul hδ.le, div_mul_cancel₀ _ hw]

/-- **`u > v`: the comparison is an UPPER bound on the cardinality.**  This is §8's sign. -/
theorem card_le_iff {δ N : ℝ} (hδ : 0 < δ) (hN : 0 < N) {p q u v : ℝ} (huv : v < u) :
    δ ^ p * N ^ u ≤ δ ^ q * N ^ v ↔ N ≤ δ ^ ((q - p) / (u - v)) := by
  rw [key_iff hδ hN p q u v]
  have hw : (0:ℝ) < u - v := by linarith
  rw [← rpow_div_mul hδ (q - p) (u - v) hw.ne']
  exact Real.rpow_le_rpow_iff hN.le (Real.rpow_pos_of_pos hδ _).le hw

/-- **`u < v`: the comparison is a LOWER bound on the cardinality.**  This is §9's sign. -/
theorem le_card_iff {δ N : ℝ} (hδ : 0 < δ) (hN : 0 < N) {p q u v : ℝ} (huv : u < v) :
    δ ^ p * N ^ u ≤ δ ^ q * N ^ v ↔ δ ^ ((q - p) / (u - v)) ≤ N := by
  rw [key_iff hδ hN p q u v]
  have hw : u - v < 0 := by linarith
  have hMpos : (0:ℝ) < δ ^ ((q - p) / (u - v)) := Real.rpow_pos_of_pos hδ _
  rw [(rpow_div_mul hδ (q - p) (u - v) hw.ne).symm]
  constructor
  · intro h
    by_contra hcon
    rw [not_le] at hcon
    have hlt' : (δ ^ ((q - p) / (u - v))) ^ (u - v) < N ^ (u - v) :=
      Real.rpow_lt_rpow_of_neg hN hcon hw
    linarith
  · intro h
    rcases eq_or_lt_of_le h with heq | hlt
    · exact le_of_eq (by rw [heq])
    · exact le_of_lt (Real.rpow_lt_rpow_of_neg hMpos hlt hw)

/-! ## Part II — GWZ §8, Lemma 8.1, branch (i) -/

/-- **GWZ's branch (i) of Lemma 8.1, and its printed side condition, as an equivalence.**

With `a = γ/2` the accuracy Theorem 7.3(A) was read at and `N = |T|`, the displayed chain
`|U(T,Y)| ≥ δ^{a} ≥ δ^{2a}(|T||T|)^{a/2}` holds **iff** `N ≤ δ^{-4}`.  GWZ annotate the step with
*"where we used the fact that `|T| ≤ δ^{-4}`"*; the `-4` here is produced by
`Kakeya.ML2S8Transfer.card_le_iff` from GWZ's exponents, not assumed. -/
theorem sectionEight_printed_iff {δ N a : ℝ} (hδ : 0 < δ) (hN : 0 < N) (ha : 0 < a) :
    δ ^ (2 * a) * (δ ^ (2:ℝ) * N) ^ (a / 2) ≤ δ ^ a ↔ N ≤ δ ^ (-4 : ℝ) := by
  have hδ2 : (0:ℝ) < δ ^ (2:ℝ) := Real.rpow_pos_of_pos hδ 2
  have hsplit : (δ ^ (2:ℝ) * N) ^ (a / 2) = δ ^ a * N ^ (a / 2) := by
    rw [Real.mul_rpow hδ2.le hN.le, ← Real.rpow_mul hδ.le]
    ring_nf
  have hL : δ ^ (2 * a) * (δ ^ (2:ℝ) * N) ^ (a / 2) = δ ^ (3 * a) * N ^ (a / 2) := by
    rw [hsplit, ← mul_assoc, ← Real.rpow_add hδ]
    ring_nf
  have hR : δ ^ a = δ ^ a * N ^ (0:ℝ) := by rw [Real.rpow_zero, mul_one]
  rw [hL, hR, card_le_iff hδ hN (p := 3 * a) (q := a) (u := a / 2) (v := 0) (by linarith)]
  have hhalf : (a / 2 : ℝ) ≠ 0 := by positivity
  have hexp : (a - 3 * a) / (a / 2 - 0) = (-4 : ℝ) := by
    rw [sub_zero, div_eq_iff hhalf]
    ring
  rw [hexp]

/-- **§8's branch (i) costs no outer accuracy at all.**  The conclusion carries no `δ^{-ε}`: this is
why reading Theorem 7.3 at the `ε`-free accuracy `γ/2` is legitimate in §8, and hence why §8's `ν`
is a function of the exponents alone. -/
theorem sectionEight_closes {δ N a : ℝ} (hδ : 0 < δ) (hN : 0 < N) (ha : 0 < a)
    (hcard : N ≤ δ ^ (-4 : ℝ)) :
    δ ^ (2 * a) * (δ ^ (2:ℝ) * N) ^ (a / 2) ≤ δ ^ a :=
  (sectionEight_printed_iff hδ hN ha).mpr hcard

/-- **In §8 a cardinality LOWER bound is inert.**  For every `B`, the hypothesis `B ≤ N` fails to
give branch (i): the comparison is violated by any `N` beyond `δ^{-4}`.  Together with
`Kakeya.ML2S8Transfer.sectionNine_no_upper_bound_helps` this shows the direction claim is two-sided
— each section's branch is refuted by the *other* section's kind of hypothesis. -/
theorem sectionEight_no_lower_bound_helps {δ a : ℝ} (hδ : 0 < δ) (ha : 0 < a) (B : ℝ) :
    ¬ ∀ N : ℝ, 0 < N → B ≤ N →
        δ ^ (2 * a) * (δ ^ (2:ℝ) * N) ^ (a / 2) ≤ δ ^ a := by
  intro h
  set N : ℝ := max B (δ ^ (-4 : ℝ)) + 1 with hN
  have hpow : (0:ℝ) < δ ^ (-4 : ℝ) := Real.rpow_pos_of_pos hδ _
  have hNpos : (0:ℝ) < N := by
    have : δ ^ (-4 : ℝ) ≤ max B (δ ^ (-4 : ℝ)) := le_max_right _ _
    simp only [hN]; linarith
  have hNB : B ≤ N := by
    have : B ≤ max B (δ ^ (-4 : ℝ)) := le_max_left _ _
    simp only [hN]; linarith
  have hgt : δ ^ (-4 : ℝ) < N := by
    have : δ ^ (-4 : ℝ) ≤ max B (δ ^ (-4 : ℝ)) := le_max_right _ _
    simp only [hN]; linarith
  exact absurd ((sectionEight_printed_iff hδ hNpos ha).mp (h N hNpos hNB)) (not_le.mpr hgt)

/-! ## Part III — GWZ §9, Main Lemma 2 from Lemma 9.1, branch (i) -/

/-- **GWZ's branch (i) of §9, and the side condition it would need, as an equivalence.**

Theorem 7.3(B) read at an accuracy `ε₀` gives `μ ≤ δ^{-ε₀}`; the goal (67) is `μ ≤ δ^{-ε}|T|^{γ}`
with `γ = β - ν`.  The branch closes **iff** `δ^{-(ε₀-ε)/γ} ≤ N`, a cardinality **lower** bound.
Compare `Kakeya.ML2S8Transfer.sectionEight_printed_iff`: same lemma, opposite direction, because
`u - v` is `-γ < 0` here and `+a/2 > 0` there. -/
theorem sectionNine_printed_iff {δ N ε ε₀ γ : ℝ} (hδ : 0 < δ) (hN : 0 < N) (hγ : 0 < γ) :
    δ ^ (-ε₀) ≤ δ ^ (-ε) * N ^ γ ↔ δ ^ (-((ε₀ - ε) / γ)) ≤ N := by
  have hL : δ ^ (-ε₀) = δ ^ (-ε₀) * N ^ (0:ℝ) := by rw [Real.rpow_zero, mul_one]
  rw [hL, le_card_iff hδ hN (p := -ε₀) (q := -ε) (u := 0) (v := γ) hγ]
  have hzero : (0 : ℝ) - γ = -γ := by ring
  have hexp : (-ε - -ε₀) / (0 - γ) = -((ε₀ - ε) / γ) := by
    rw [hzero, div_neg]
    congr 1
    ring
  rw [hexp]

/-- **The `ε`-free version closes exactly at the threshold.** -/
theorem sectionNine_closes {δ N ε ε₀ γ : ℝ} (hδ : 0 < δ) (hN : 0 < N) (hγ : 0 < γ)
    (hcard : δ ^ (-((ε₀ - ε) / γ)) ≤ N) :
    δ ^ (-ε₀) ≤ δ ^ (-ε) * N ^ γ :=
  (sectionNine_printed_iff hδ hN hγ).mpr hcard

/-- **In §9 no cardinality UPPER bound is of any use.**  Whatever bound `B ≥ 1` one has — and
`|T| ≤ δ^{-4}` is one — the hypothesis `N ≤ B` does not give branch (i) whenever `ε < ε₀`,
because `N = 1` satisfies it and the comparison fails there. -/
theorem sectionNine_no_upper_bound_helps {δ ε ε₀ γ B : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hB : 1 ≤ B) (hlt : ε < ε₀) :
    ¬ ∀ N : ℝ, 0 < N → N ≤ B → δ ^ (-ε₀) ≤ δ ^ (-ε) * N ^ γ := by
  intro h
  have h1 := h 1 one_pos hB
  rw [Real.one_rpow, mul_one] at h1
  exact absurd h1 (not_le.mpr (Real.rpow_lt_rpow_of_exponent_gt hδ0 hδ1 (by linarith)))

/-- **§8's own side condition, transported to §9, is inert.**

`Kakeya.ml1Boot.card_le` gives `|T| ≤ C δ^{-4}` for essentially distinct `δ`-tubes in `B₁ ⊆ ℝ³`,
with `1 ≤ C` (`Kakeya.ml1Boot.cardBound.one_le_C`); the same geometric fact holds of §9's families.
It buys nothing: this is `Kakeya.ML2S8Transfer.sectionNine_no_upper_bound_helps` at
`B = C δ^{-4}`. -/
theorem sectionNine_cardBound_inert {δ ε ε₀ γ C : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hC : 1 ≤ C) (hlt : ε < ε₀) :
    ¬ ∀ N : ℝ, 0 < N → N ≤ C * δ ^ (-4 : ℝ) → δ ^ (-ε₀) ≤ δ ^ (-ε) * N ^ γ := by
  refine sectionNine_no_upper_bound_helps (γ := γ) hδ0 hδ1 ?_ hlt
  have h1 : (1:ℝ) ≤ δ ^ (-4 : ℝ) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ0 hδ1.le (by norm_num)
  nlinarith

/-- **The deficit at the worst case.**  `N = 1` is a family that is Katz–Tao at every scale, so the
branch must cover it, and there the comparison fails by the genuine power `δ^{-(ε₀-ε)}`.  This is
`Kakeya.ML2Exchange.zeroThreshold_insufficient` in the present notation. -/
theorem sectionNine_fails_at_one {δ ε ε₀ γ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hγ : 0 ≤ γ)
    (hlt : ε < ε₀) :
    ¬ (δ ^ (-ε₀) ≤ δ ^ (-ε) * (1:ℝ) ^ γ) := by
  have := Kakeya.ML2Exchange.zeroThreshold_insufficient (δ := δ) (ε := ε) (ε₀ := ε₀) (γ := γ)
    hδ0 hδ1 hγ hlt
  exact not_le.mpr this

/-! ## Part IV — GWZ §9, branch (ii): the same file's other sign -/

/-- **§9's branch (ii), and its side condition, as an equivalence.**

Branch (ii) ends at `μ ≤ δ^{g}|T|^{β}` with an accuracy-free gain `g` (GWZ's `9η_{j-1} - η₁` after
(68), (70) and the two factor bounds); the goal is `μ ≤ δ^{-ε}|T|^{β-ν}`.  At `ε = 0` this closes
**iff** `N ≤ δ^{-g/ν}` — an **upper** bound, `u - v = ν > 0`.  Branch (ii) is therefore on §8's
side of the dichotomy, and only branch (i) is on the other. -/
theorem sectionNine_branchTwo_iff {δ N β ν g : ℝ} (hδ : 0 < δ) (hN : 0 < N) (hν : 0 < ν) :
    δ ^ g * N ^ β ≤ δ ^ (0:ℝ) * N ^ (β - ν) ↔ N ≤ δ ^ (-(g / ν)) := by
  rw [card_le_iff hδ hN (p := g) (q := 0) (u := β) (v := β - ν) (by linarith)]
  have hνne : ν ≠ 0 := ne_of_gt hν
  have hexp : ((0:ℝ) - g) / (β - (β - ν)) = -(g / ν) := by
    have hsub : β - (β - ν) = ν := by ring
    rw [hsub, zero_sub, neg_div]
  rw [hexp]

/-- **§9's branch (ii) closes at `ε = 0` from *any* upper cardinality bound.**

With `|T| ≤ δ^{-c}` and `ν` chosen small compared to the branch's gain — `cν ≤ g`, GWZ's
*"the quantity `ν` … will be selected small compared to `η₁`"* — the conversion goes through with no
outer accuracy spent at all.  At `c = 4` this is the budget `4ν ≤ g` that
`Reduction/SpineCardBand.lean` records for the large-cardinality branch, and at `c = 1` the `ν ≤ g`
it records for the band. -/
theorem sectionNine_branchTwo_closes {δ N β ν g c : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hN : 0 < N)
    (hν : 0 < ν) (hcard : N ≤ δ ^ (-c)) (hbudget : c * ν ≤ g) :
    δ ^ g * N ^ β ≤ δ ^ (0:ℝ) * N ^ (β - ν) := by
  refine (sectionNine_branchTwo_iff hδ0 hN hν).mpr (hcard.trans ?_)
  refine Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1 ?_
  rw [neg_le_neg_iff, le_div_iff₀ hν]
  linarith

/-! ## Part V — the two branches in one statement, and the cross-check -/

/-- **THE SIDE-BY-SIDE.**  One comparison lemma; the sign of the cardinality exponent gap decides
the direction of the side condition.  In §8 the gap is `a/2 - 0 > 0` and the condition is an upper
bound, the universally true `|T| ≤ δ^{-4}`; in §9 the gap is `0 - γ < 0` and the condition is a
lower bound, which §9's hypotheses do not supply. -/
theorem branchOne_side_conditions {δ N a ε ε₀ γ : ℝ} (hδ : 0 < δ) (hN : 0 < N) (ha : 0 < a)
    (hγ : 0 < γ) :
    (δ ^ (2 * a) * (δ ^ (2:ℝ) * N) ^ (a / 2) ≤ δ ^ a ↔ N ≤ δ ^ (-4 : ℝ)) ∧
      (δ ^ (-ε₀) ≤ δ ^ (-ε) * N ^ γ ↔ δ ^ (-((ε₀ - ε) / γ)) ≤ N) :=
  ⟨sectionEight_printed_iff hδ hN ha, sectionNine_printed_iff hδ hN hγ⟩

/-- **Cross-check against the development's independently derived budget.**

`Kakeya.ML2Exchange.katzTaoGoal_of_absoluteLoss_of_card_ge_rpow` closes the large-cardinality side
on `δ^{-θ} ≤ |T|` under the budget `ε₀ ≤ ε + θγ`.  That budget is exactly the statement that the
threshold `θ` reaches the solved side condition of
`Kakeya.ML2S8Transfer.sectionNine_printed_iff`.  Two derivations, one exponent. -/
theorem budget_iff_threshold {δ ε ε₀ γ θ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hγ : 0 < γ) :
    ε₀ ≤ ε + θ * γ ↔ δ ^ (-((ε₀ - ε) / γ)) ≤ δ ^ (-θ) := by
  rw [Real.rpow_le_rpow_left_iff_of_base_lt_one hδ0 hδ1]
  constructor
  · intro h
    rw [neg_le_neg_iff, div_le_iff₀ hγ]
    linarith
  · intro h
    rw [neg_le_neg_iff, div_le_iff₀ hγ] at h
    linarith

end Kakeya.ML2S8Transfer
