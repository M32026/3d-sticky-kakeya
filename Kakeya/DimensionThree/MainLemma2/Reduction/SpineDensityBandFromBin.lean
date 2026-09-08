/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineJointStatisticBin
public import Kakeya.Density

/-!
# From a dyadic bin to a two-sided `ENNReal` band — `level_density_band`'s engine

`Kakeya.ML2Reduction.IsKatzTaoDividingWindowLevels.level_density_band` (refined source
l.4032-4035, *"pairwise within a factor two at every fixed level or pair of levels"*) is a
**two-sided `ENNReal`** statement through a profile `Φ`:

  `Φ p c ≤ Δ_max(𝕋_c⟨j⟩) ≤ Cstar · Φ p c`   for every level-`p` cell `j`.

`Kakeya.ML2Core.exists_jointStatisticBand` (`SpineJointStatisticBin.lean:150`) is the source's
*"simultaneous vector-bin regularization"* (l.2708-2713) but it is **ℕ-shaped**: it regularizes
integer statistics of leaves and its factor-two clause is `stat p (f p j) < 2 * stat p (f p i)`
for leaves in a common dyadic bin.  The gap between the two is this file.

## What the bridge actually needs, and what it does not

It does **not** need a real-number logarithm or an `ENNReal → ℕ` discretization.  The only content
of "one dyadic bin" that the band uses is the *pairwise* clause

  `bucket k = bucket k' → D k' ≤ 2 * D k`,

and `dyadicBandIndex` already supplies exactly that for `ℕ` values
(`Kakeya.ML2Core.within_factor_two_of_dyadicBandIndex_eq`).  So `exists_bucket_band` takes the
bucket map and its pairwise clause abstractly, does the pigeonhole, and produces the profile.

**The profile is the bin's infimum, and `Cstar = 2` exactly.**  Taking `Φ := inf_{k ∈ K'} D k`
gives `Φ ≤ D k` on the nose, and `D k ≤ 2 * D k₁ = 2 * Φ` at the minimiser `k₁`.  No division, no
finiteness hypothesis on `D`, and the constant is the source's own factor two rather than a fitted
one.  (Taking `Φ := D k₀` for an arbitrary `k₀` would give the weaker two-sided
`Φ ≤ 2 * D k ∧ D k ≤ 2 * Φ`; the infimum is what makes the left half exact, which is the half
`level_density_band` states without a constant.)

## The factor two is not slack — `not_bucket_band_at_factor_one` is a counterexample to the stronger bound: the same hypotheses with
`Cstar` tightened from `2` to `1` are **false**, witnessed by `K = {0,1}`, `bucket ≡ 0`, `D 0 = 1`,
`D 1 = 2`.  Those satisfy the pairwise clause (`2 ≤ 2·1` and `1 ≤ 2·2`) and no `Φ` can satisfy
`Φ ≤ D k ∧ D k ≤ 1 * Φ` at both, since that forces `D` constant.  So the `2` is doing work and the
theorem is not vacuously improvable.

## MEASURED: the existing A1 is a **balanced-bin** statement, not a **single-bin** one

The plan for this row was to instantiate `Kakeya.ML2Core.exists_jointStatisticBand` at the four
statistics of l.4032-4035 and read `level_density_band` off it.  **That does not work as stated**,
and the reason is a shape difference worth recording rather than working around silently.

`exists_jointStatisticBand`'s pigeonhole content is its *second* conjunct
(`SpineJointStatisticBin.lean:154-158`):

> `∀ p, ∀ v ∈ s'.image (fun i => dyadicBandIndex (stat p (f p i))),`
> `  N p ≤ {i ∈ s' | … = v}.card ∧ {i ∈ s' | … = v}.card ≤ relativePlankBandRatio … * N p`

— every bin **that survives** has cardinality within a fixed ratio of `N p`.  That is
*equidistribution across bins*.  Its third conjunct is not pigeonhole content at all: it is
`within_factor_two_of_dyadicBandIndex_eq` applied pointwise, i.e. it is conditional on two leaves
*already* sharing a bin.

What `level_density_band` needs is the opposite: **all** surviving members in **one** bin per
statistic, so that a single profile `Φ p c` bounds them two-sidedly.  Equidistribution does not
imply concentration — a family evenly spread over many bins satisfies the existing conclusion and has
no single profile at all.

The two pigeonholes have the **same loss shape** (`relativePlankJointLoss n M =
2 * relativePlankBucket n ^ relativePlankRounds M` is exactly "one dyadic bucketing per partition"),
which is presumably why the plan conflated them.  `exists_joint_bucket_band` below is the
concentration form, proved directly by iterating `exists_bucket_band` over the statistics; its loss
is `L ^ n`, the same product of per-statistic bucket counts.

** and nothing is claimed against `exists_jointStatisticBand`**: it is a
correct statement of a different pigeonhole, and it remains the right tool wherever
equidistribution is what is wanted.

## The three riders (3), and the one thing that must not ride

§9.6 amends §9.4: the source's vector bin is **concentration** (l.4919-4920 *"retaining one joint
vector bin"*, l.4925 *"every label is then constant"*), the existing
`Kakeya.exists_jointPartitionRegularization` states equidistribution, and **A1 is the concentration
sibling** — the object this file builds.  For the record, and at the visibility §9.6 asks: this is
*standard pigeonholing, cheap, and it has to be written*; it is **the one genuinely new lemma text
of the payload side**, everything else on this route being a restatement or a composition of existing
material.

Three things ride with the abstract band or the transcription is not faithful:

1. **The label** (l.4918-4919, l.4925) — a discrete label taking at most `K₀` values, *constant*
   across survivors.  `exists_constant_label` is that pigeonhole and
   `exists_joint_bucket_band_with_label` carries it, at the extra factor `K₀` in the loss.  `K₀` is
   the source's own bound on the number of label values and is a parameter here, not a fitted
   constant.
2. **The root-ward descent over `M + 1` levels** (l.4919-4922).  `exists_joint_bucket_band`'s
   `L ^ n` is **one** application at **one** level; the source's `[K₀(2 + 2log₂Λ)^{K₀}]^{-(M+1)}` is
   the composition across levels.  The two are stated separately here: the per-level loss is
   `K₀ * L ^ n` (`exists_joint_bucket_band_with_label`) and the composition is
   `card_le_pow_of_chain`, giving the total `(K₀ * L ^ n) ^ (M + 1)`.  With `L` the bucket count
   `2 + 2log₂Λ` and `n = K₀` statistics this is the source's expression verbatim; **that** is where
   `Λ_f`'s polylog shape comes from, not from a single application.
3. **Leaf-locality, and the stability it buys** (l.4917-4918 *"depends only on the leaves of the
   relevant thread cell"*; l.4926-4927 *"Later restrictions to an ancestor retain or discard an
   entire descendant fibre, so an already regularized leaf-local statistic is not changed"*).  This
   is the load-bearing one and a bare bucket band does **not** imply it.  It is therefore a
   **hypothesis** — `LeafLocalStat`, a statistic whose value at a leaf depends only on that leaf's
   cell fibre *within the family it is computed in* — and the stability is a **conclusion**,
   `band_stable_of_leafLocal`: the band survives any whole-fibre ancestor restriction.
   `not_stable_of_not_leafLocal` is the control: the family-size statistic `#u` is not leaf-local
   and its value **does** move under a whole-fibre restriction, so the hypothesis is doing work.

**And one clause that must NOT ride.**  `Kakeya.exists_jointPartitionRegularization`'s third
conjunct protects partition `0` against the *original* family (`SpineJointStatisticBin.lean:95-97`).
That is a virtue of the existing device — it solves ML1's plank-block problem — but the source's bin
has **no such clause**; its analogue is leaf-locality, a different mechanism.  Nothing in this file
has it: the conclusions of `exists_bucket_band`, `exists_joint_bucket_band` and
`exists_joint_bucket_band_with_label` mention only `K`, `K'`, the statistics and the label, and no
distinguished index.  Importing it would be a clause the source does not have — the  objection
in the one place where it does hold.

## The bucket map for `ENNReal` statistics, and the brackets it needs — measured

`exists_bucket_band` and `exists_joint_bucket_band` take `bucket` abstractly.  For a genuinely
`ENNReal`-valued statistic the bucket is `dyadicScaleBucket lo D`, the **least `j` with
`D ≤ 2 ^ j * lo`** — a dyadic bucketing relative to a supplied floor `lo`, entirely inside
`ENNReal`, with no `Real.logb`, no `toReal` and no finiteness side condition.  Its pairwise clause
`le_two_mul_of_dyadicScaleBucket_eq` is the exact analogue of
`Kakeya.ML2Core.within_factor_two_of_dyadicBandIndex_eq`, and its proof is the same one: the
minimality of `Nat.find` at `j` gives `2 ^ (j-1) * lo < x`, and `y ≤ 2 ^ j * lo`.
The `j = 0` case is where the **lower** bracket `lo ≤ x` is used, and it is the only place.

The ceiling is `L = J + 1` for any `J` with `D ≤ 2 ^ J * lo` on the whole family
(`dyadicScaleBucket_lt_succ`); `exists_pow_two_bracket` shows such a `J` exists as soon as the
bracket is nondegenerate (`lo ≠ 0`, `hi ≠ ⊤`).

**The brackets, per statistic of l.4032-4035, with the fact that supplies each.**

| statistic | lower bracket | supplied by | upper bracket | supplied by |
|---|---|---|---|---|
| two-level maximal densities | `1` | `one_le_maxDensity` | `#𝕋_c⟨S⟩` | `maxDensity_le_card` |
| descendant / two-level counts | `1` | `Finset.card_pos` | `(32/ρ_k)^6`, l.4028 | source hyp. |
| fibre shaded masses | `δ^{3η_f}` | l.4030-4031, *"fullness at least"* | total mass | trivial |

**`C₁ = 0` for the first two rows — the lower bracket is `1`, not a power of `δ`.**  That is worth
recording because it was not the expected shape: `Kakeya.one_le_maxDensity` says a cell containing
one positive-volume tube already has `Δ_max ≥ 1`, so nothing has to be assumed and no `δ`-power is
spent below.  `Λ_f`'s logarithm therefore comes **entirely from the upper bracket**: with
`D ≤ hi` and `lo = 1` the ceiling is `J = ⌈log₂ hi⌉`, and at the source's `hi = (32/ρ_k)^6` this is
`O(log₂(1/δ))`, i.e. `L = O(2 + log₂(1/δ))` and `L ^ n = Λ_f` with `K_f = n` the number of
statistics — the source's l.4057 shape, with `C₁ = 0` and `C₂` read off l.4028 rather than fitted.
Only the shaded-mass row spends a `δ`-power below, and it spends the source's own `3η_f`.

## Where `Λ_f` is paid

The loss is the bucket count `L`: the pigeonhole keeps a `1/L` share, `K.card ≤ L * K'.card`.  With
`L` instantiated at the existing `relativePlankJointLoss n M` — one dyadic bucketing per partition,
times the deletion factor `2` — `bucketBandLoss_le_polylog` composes with the existing
`relativePlankJointLoss_le_of_card_le_pow` to give `L ≤ 2 * (k + 1) ^ (M + 2)` under `n ≤ 2 ^ k`.
That is `Λ_f = (2 + log₂(1/δ))^{K_f}`'s shape with `K_f = M + 2`, exactly as
`SpineJointStatisticBin.lean`'s own header records; applied at the source's `#s ≤ δ^{-4}` one takes
`k = 4 log₂(1/δ)` and the numeric factors are absorbed into the named constant.  **Nothing here
rewrites `Λ_f`**: `k` and `M` are left free and the caller supplies its own ceiling.

## Family / shading / level pair

| declaration | family / shading | level pair |
|---|---|---|
| `exists_bucket_band` | abstract: a `Finset κ` with an `ENNReal` statistic; no shading | none |
| `exists_joint_bucket_band` | abstract: `n` statistics at once; no shading | none |
| `dyadicScaleBucket`, its two lemmas | abstract; no shading | none |
| `exists_joint_bucket_band_of_bracket` | abstract; no shading | none |
| `exists_constant_label`, `..._with_label` | abstract; no shading | none |
| `LeafLocalStat`, `band_stable_of_leafLocal` | the leaf's thread cell | its statistic's level |
| `card_le_pow_of_chain` | none | the `M + 1` levels of the descent |
| `not_bucket_band_at_factor_one` | none — a two-point counterexample | none |
| `bucketBandLoss_le_polylog` | none | none |

## A1-a

Nothing here mentions `GridUniformCore`, and nothing here is an (F)-branch interface statement:
`exists_bucket_band` is a pigeonhole about an abstract `Finset`.
-/

@[expose] public section

open scoped NNReal ENNReal

namespace Kakeya.ML2Core

section DensityBandFromBin

/-- **The bin-to-band pigeonhole.**  Given a bucketing of a finite family whose members' statistics
are pairwise within a factor two inside each bucket, one bucket carries a `1/L` share of the family
and its statistics are pinned to a single profile within a factor two.

`Φ` is the bucket's **infimum**, which is why the left half `Φ ≤ D k` carries no constant — the
shape `Kakeya.ML2Reduction.IsKatzTaoDividingWindowLevels.level_density_band` states.

**Family/shading:** abstract.  **Level pair:** none. -/
theorem exists_bucket_band {κ : Type*} (K : Finset κ) (hK : K.Nonempty)
    (D : κ → ENNReal) (bucket : κ → ℕ) (L : ℕ)
    (hb : ∀ k ∈ K, ∀ k' ∈ K, bucket k = bucket k' → D k' ≤ 2 * D k)
    (hL : ∀ k ∈ K, bucket k < L) :
    ∃ K' : Finset κ, K' ⊆ K ∧ K'.Nonempty ∧ K.card ≤ L * K'.card ∧
      ∃ Φ : ENNReal, ∀ k ∈ K', Φ ≤ D k ∧ D k ≤ 2 * Φ := by
  classical
  obtain ⟨k₀, hk₀⟩ := hK
  have hLpos : 0 < L := lt_of_le_of_lt (Nat.zero_le _) (hL k₀ hk₀)
  have hmaps : ∀ k ∈ K, bucket k ∈ Finset.range L := fun k hk => Finset.mem_range.mpr (hL k hk)
  have hsum : ∑ v ∈ Finset.range L, (K.filter (fun k => bucket k = v)).card = K.card :=
    (Finset.card_eq_sum_card_fiberwise hmaps).symm
  have hne : (Finset.range L).Nonempty := Finset.nonempty_range_iff.mpr hLpos.ne'
  have hle : ∑ _v ∈ Finset.range L, K.card
      ≤ ∑ v ∈ Finset.range L, L * (K.filter (fun k => bucket k = v)).card := by
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul, ← Finset.mul_sum, hsum]
  obtain ⟨v, -, hv⟩ := Finset.exists_le_of_sum_le hne hle
  refine ⟨K.filter (fun k => bucket k = v), Finset.filter_subset _ _, ?_, hv, ?_⟩
  · rw [← Finset.card_pos]
    by_contra hzero
    rw [Nat.pos_iff_ne_zero, not_not] at hzero
    rw [hzero, Nat.mul_zero, Nat.le_zero, Finset.card_eq_zero] at hv
    exact absurd hk₀ (by rw [hv]; exact Finset.notMem_empty k₀)
  · have hK'ne : (K.filter (fun k => bucket k = v)).Nonempty := by
      rw [← Finset.card_pos]
      by_contra hzero
      rw [Nat.pos_iff_ne_zero, not_not] at hzero
      rw [hzero, Nat.mul_zero, Nat.le_zero, Finset.card_eq_zero] at hv
      exact absurd hk₀ (by rw [hv]; exact Finset.notMem_empty k₀)
    refine ⟨(K.filter (fun k => bucket k = v)).inf' hK'ne D, fun k hk => ⟨?_, ?_⟩⟩
    · exact Finset.inf'_le D hk
    · obtain ⟨k₁, hk₁mem, hk₁eq⟩ := Finset.exists_mem_eq_inf' hK'ne D
      rw [hk₁eq]
      obtain ⟨hk₁K, hk₁v⟩ := Finset.mem_filter.mp hk₁mem
      obtain ⟨hkK, hkv⟩ := Finset.mem_filter.mp hk
      exact hb k₁ hk₁K k hkK (by rw [hk₁v, hkv])

/-- **Firing control: the factor two is not slack.**  With the band tightened to `Cstar = 1` the
same hypotheses become false — `bucket ≡ 0` on `{0,1}` with `D 0 = 1`, `D 1 = 2` satisfies the
pairwise clause but admits no profile `Φ` with `Φ ≤ D k` and `D k ≤ 1 * Φ` at both points, because
that would force `D 0 = D 1`. -/
theorem not_bucket_band_at_factor_one :
    ∃ (K : Finset ℕ) (D : ℕ → ENNReal) (bucket : ℕ → ℕ),
      (∀ k ∈ K, ∀ k' ∈ K, bucket k = bucket k' → D k' ≤ 2 * D k) ∧
      ¬ ∃ Φ : ENNReal, ∀ k ∈ K, Φ ≤ D k ∧ D k ≤ 1 * Φ := by
  classical
  refine ⟨{0, 1}, fun k => if k = 0 then 1 else 2, fun _ => 0, ?_, ?_⟩
  · intro k hk k' hk' _
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk hk'
    rcases hk with rfl | rfl <;> rcases hk' with rfl | rfl <;> norm_num
  · rintro ⟨Φ, hΦ⟩
    have h0 := hΦ 0 (by simp)
    have h1 := hΦ 1 (by simp)
    simp only [one_mul, if_neg (by norm_num : (1 : ℕ) ≠ 0)] at h0 h1
    have : (2 : ENNReal) ≤ 1 := le_trans h1.2 h0.1
    exact absurd this (by norm_num)

/-- **The joint single-bin band**: `n` statistics regularized at once, at the loss `L ^ n`.

This is the concentration form that
`Kakeya.ML2Reduction.IsKatzTaoDividingWindowLevels.level_density_band` needs — **all** of
`K'` in one bucket per statistic, hence one profile `Φ q` per statistic — as opposed to the
equidistribution form the existing `Kakeya.ML2Core.exists_jointStatisticBand` proves.
See the module docstring for the measured difference.

The proof is the obvious induction: peel off the last statistic with `exists_bucket_band`, apply the
inductive hypothesis to the survivors (the hypotheses are `∀`-over-members, so they restrict), and
multiply the losses.  The earlier statistics' bands survive because the sets only shrink.

**Family/shading:** abstract.  **Level pair:** none — the caller flattens its pair index `(p,c)`
into `Fin n`. -/
theorem exists_joint_bucket_band {κ : Type*} :
    ∀ (n : ℕ) (K : Finset κ), K.Nonempty →
      ∀ (D : Fin n → κ → ENNReal) (bucket : Fin n → κ → ℕ) (L : ℕ), 0 < L →
      (∀ q : Fin n, ∀ k ∈ K, ∀ k' ∈ K, bucket q k = bucket q k' → D q k' ≤ 2 * D q k) →
      (∀ q : Fin n, ∀ k ∈ K, bucket q k < L) →
      ∃ K' : Finset κ, K' ⊆ K ∧ K'.Nonempty ∧ K.card ≤ L ^ n * K'.card ∧
        ∃ Φ : Fin n → ENNReal, ∀ q : Fin n, ∀ k ∈ K', Φ q ≤ D q k ∧ D q k ≤ 2 * Φ q := by
  intro n
  induction n with
  | zero =>
      intro K hK D bucket L hL _ _
      exact ⟨K, Finset.Subset.refl K, hK, by simp,
        Fin.elim0, fun q => q.elim0⟩
  | succ n ih =>
      intro K hK D bucket L hL hb hLlt
      obtain ⟨K₁, hK₁sub, hK₁ne, hK₁card, Φlast, hΦlast⟩ :=
        exists_bucket_band K hK (D (Fin.last n)) (bucket (Fin.last n)) L
          (hb (Fin.last n)) (hLlt (Fin.last n))
      obtain ⟨K₂, hK₂sub, hK₂ne, hK₂card, Φ, hΦ⟩ :=
        ih K₁ hK₁ne (fun q => D q.castSucc) (fun q => bucket q.castSucc) L hL
          (fun q k hk k' hk' h => hb q.castSucc k (hK₁sub hk) k' (hK₁sub hk') h)
          (fun q k hk => hLlt q.castSucc k (hK₁sub hk))
      refine ⟨K₂, hK₂sub.trans hK₁sub, hK₂ne, ?_, Fin.snoc Φ Φlast, ?_⟩
      · calc K.card ≤ L * K₁.card := hK₁card
          _ ≤ L * (L ^ n * K₂.card) := Nat.mul_le_mul_left L hK₂card
          _ = L ^ (n + 1) * K₂.card := by ring
      · intro q k hk
        refine Fin.lastCases ?_ ?_ q
        · simpa using hΦlast k (hK₂sub hk)
        · intro q'
          simpa using hΦ q' k hk

/-! ### The bucket map for `ENNReal` statistics -/

open scoped Classical in
/-- **The dyadic bucket of `D` relative to a floor `lo`**: the least `j` with `D ≤ 2 ^ j * lo`.

Entirely inside `ENNReal` — no `Real.logb`, no `toReal`, no finiteness side condition.  The
`ENNReal` analogue of `Kakeya.ML2Core.dyadicBandIndex`. -/
noncomputable def dyadicScaleBucket (lo D : ENNReal) : ℕ :=
  if h : ∃ j : ℕ, D ≤ 2 ^ j * lo then Nat.find h else 0

/-- **The ceiling**: a single `J` working for the whole family caps every bucket by `J`, so the
bucket count is `L = J + 1`. -/
theorem dyadicScaleBucket_lt_succ {lo D : ENNReal} {J : ℕ} (h : D ≤ 2 ^ J * lo) :
    dyadicScaleBucket lo D < J + 1 := by
  have hex : ∃ j : ℕ, D ≤ 2 ^ j * lo := ⟨J, h⟩
  rw [dyadicScaleBucket, dif_pos hex]
  exact Nat.lt_succ_of_le (Nat.find_le h)

/-- **The pairwise clause** — the `ENNReal` analogue of
`Kakeya.ML2Core.within_factor_two_of_dyadicBandIndex_eq`, by the same argument.  The lower bracket
`lo ≤ x` is used **only** in the `j = 0` case. -/
theorem le_two_mul_of_dyadicScaleBucket_eq {lo x y : ENNReal}
    (hx : ∃ j : ℕ, x ≤ 2 ^ j * lo) (hy : ∃ j : ℕ, y ≤ 2 ^ j * lo) (hlox : lo ≤ x)
    (h : dyadicScaleBucket lo x = dyadicScaleBucket lo y) : y ≤ 2 * x := by
  classical
  rw [dyadicScaleBucket, dif_pos hx, dyadicScaleBucket, dif_pos hy] at h
  have hyspec : y ≤ 2 ^ (Nat.find hy) * lo := Nat.find_spec hy
  rw [← h] at hyspec
  have hxx : x ≤ 2 * x := by
    nth_rewrite 1 [← one_mul x]
    gcongr
    norm_num
  cases hj : Nat.find hx with
  | zero =>
      rw [hj] at hyspec
      simp only [pow_zero, one_mul] at hyspec
      exact hyspec.trans (hlox.trans hxx)
  | succ m =>
      have hmin : ¬ (x ≤ 2 ^ m * lo) := Nat.find_min hx (by rw [hj]; omega)
      have hlt : 2 ^ m * lo < x := lt_of_not_ge hmin
      rw [hj] at hyspec
      calc y ≤ 2 ^ (m + 1) * lo := hyspec
        _ = 2 * (2 ^ m * lo) := by ring
        _ ≤ 2 * x := by gcongr

/-- **The ceiling exists whenever the bracket is nondegenerate.**  Any statistic bounded above by a
finite `hi` and below by a nonzero `lo` has a finite dyadic range. -/
theorem exists_pow_two_bracket {lo hi : ENNReal} (hlo : lo ≠ 0) (hhi : hi ≠ ⊤) :
    ∃ J : ℕ, hi ≤ 2 ^ J * lo := by
  rcases eq_or_ne lo ⊤ with rfl | hlotop
  · refine ⟨0, ?_⟩
    simp
  · have hdiv : hi / lo ≠ ⊤ := by
      simp [ENNReal.div_eq_top, hlo, hhi, hlotop]
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hdiv
    refine ⟨n, ?_⟩
    have hcast : (n : ENNReal) ≤ 2 ^ n := by
      have : (n : ℕ) ≤ 2 ^ n := Nat.le_of_lt (Nat.lt_two_pow_self)
      calc (n : ENNReal) ≤ ((2 ^ n : ℕ) : ENNReal) := by exact_mod_cast this
        _ = 2 ^ n := by push_cast; ring
    calc hi = hi / lo * lo := (ENNReal.div_mul_cancel hlo hlotop).symm
      _ ≤ 2 ^ n * lo := by gcongr; exact hn.le.trans hcast

open scoped Classical in
/-- **The joint band, driven by brackets rather than by an abstract bucket map.**

Each statistic is bracketed `lo q ≤ D q k ≤ 2 ^ J * lo q` on the family; `dyadicScaleBucket` turns
that into a bucket map with ceiling `J + 1`, and `exists_joint_bucket_band` does the rest.  The
retained share is `(J + 1) ^ n` — `Λ_f`'s shape with `K_f = n`, the number of statistics.

**Family/shading:** abstract.  **Level pair:** none — the caller flattens `(p,c)` into `Fin n`. -/
theorem exists_joint_bucket_band_of_bracket {κ : Type*} (n : ℕ) (K : Finset κ) (hK : K.Nonempty)
    (D : Fin n → κ → ENNReal) (lo : Fin n → ENNReal) (J : ℕ)
    (hlo : ∀ q : Fin n, ∀ k ∈ K, lo q ≤ D q k)
    (hhi : ∀ q : Fin n, ∀ k ∈ K, D q k ≤ 2 ^ J * lo q) :
    ∃ K' : Finset κ, K' ⊆ K ∧ K'.Nonempty ∧ K.card ≤ (J + 1) ^ n * K'.card ∧
      ∃ Φ : Fin n → ENNReal, ∀ q : Fin n, ∀ k ∈ K', Φ q ≤ D q k ∧ D q k ≤ 2 * Φ q := by
  classical
  refine exists_joint_bucket_band n K hK D (fun q k => dyadicScaleBucket (lo q) (D q k)) (J + 1)
    (Nat.succ_pos J) (fun q k hk k' hk' hbeq => ?_) (fun q k hk => ?_)
  · exact le_two_mul_of_dyadicScaleBucket_eq ⟨J, hhi q k hk⟩ ⟨J, hhi q k' hk'⟩
      (hlo q k hk) hbeq
  · exact dyadicScaleBucket_lt_succ (hhi q k hk)

/-! ### Rider 1: the label (l.4918-4919, l.4925) -/

open scoped Classical in
/-- **The label pigeonhole**: a discrete label taking at most `K₀` values is made *constant* on a
`1/K₀` share.  l.4925's *"every label is then constant"*.

**Family/shading:** abstract.  **Level pair:** none. -/
theorem exists_constant_label {κ : Type*} (K : Finset κ) (hK : K.Nonempty)
    (lab : κ → ℕ) (K₀ : ℕ) (hlab : ∀ k ∈ K, lab k < K₀) :
    ∃ (v : ℕ) (K' : Finset κ), K' ⊆ K ∧ K'.Nonempty ∧ K.card ≤ K₀ * K'.card ∧
      ∀ k ∈ K', lab k = v := by
  classical
  obtain ⟨k₀, hk₀⟩ := hK
  have hK₀pos : 0 < K₀ := lt_of_le_of_lt (Nat.zero_le _) (hlab k₀ hk₀)
  have hmaps : ∀ k ∈ K, lab k ∈ Finset.range K₀ := fun k hk => Finset.mem_range.mpr (hlab k hk)
  have hsum : ∑ v ∈ Finset.range K₀, (K.filter (fun k => lab k = v)).card = K.card :=
    (Finset.card_eq_sum_card_fiberwise hmaps).symm
  have hne : (Finset.range K₀).Nonempty := Finset.nonempty_range_iff.mpr hK₀pos.ne'
  have hle : ∑ _v ∈ Finset.range K₀, K.card
      ≤ ∑ v ∈ Finset.range K₀, K₀ * (K.filter (fun k => lab k = v)).card := by
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul, ← Finset.mul_sum, hsum]
  obtain ⟨v, -, hv⟩ := Finset.exists_le_of_sum_le hne hle
  have hpos : (K.filter (fun k => lab k = v)).Nonempty := by
    rw [← Finset.card_pos]
    by_contra hzero
    rw [Nat.pos_iff_ne_zero, not_not] at hzero
    rw [hzero, Nat.mul_zero, Nat.le_zero, Finset.card_eq_zero] at hv
    exact absurd hk₀ (by rw [hv]; exact Finset.notMem_empty k₀)
  exact ⟨v, K.filter (fun k => lab k = v), Finset.filter_subset _ _, hpos, hv,
    fun k hk => (Finset.mem_filter.mp hk).2⟩

/-- **The per-level regularisation of the source's bin**: one constant label *and* `n` statistics
each pinned to a profile within a factor two, at the loss `K₀ * L ^ n`.

This is **one** application at **one** level; the descent over `M + 1` levels is
`card_le_pow_of_chain`, and the total loss is `(K₀ * L ^ n) ^ (M + 1)`.

**Family/shading:** abstract.  **Level pair:** none — the caller flattens its indices. -/
theorem exists_joint_bucket_band_with_label {κ : Type*} (n : ℕ) (K : Finset κ) (hK : K.Nonempty)
    (D : Fin n → κ → ENNReal) (bucket : Fin n → κ → ℕ) (L : ℕ) (hL : 0 < L)
    (lab : κ → ℕ) (K₀ : ℕ) (hlab : ∀ k ∈ K, lab k < K₀)
    (hb : ∀ q : Fin n, ∀ k ∈ K, ∀ k' ∈ K, bucket q k = bucket q k' → D q k' ≤ 2 * D q k)
    (hLlt : ∀ q : Fin n, ∀ k ∈ K, bucket q k < L) :
    ∃ (v : ℕ) (K' : Finset κ), K' ⊆ K ∧ K'.Nonempty ∧ K.card ≤ K₀ * L ^ n * K'.card ∧
      (∀ k ∈ K', lab k = v) ∧
      ∃ Φ : Fin n → ENNReal, ∀ q : Fin n, ∀ k ∈ K', Φ q ≤ D q k ∧ D q k ≤ 2 * Φ q := by
  obtain ⟨v, K₁, hK₁sub, hK₁ne, hK₁card, hK₁lab⟩ := exists_constant_label K hK lab K₀ hlab
  obtain ⟨K₂, hK₂sub, hK₂ne, hK₂card, Φ, hΦ⟩ :=
    exists_joint_bucket_band n K₁ hK₁ne D bucket L hL
      (fun q k hk k' hk' h => hb q k (hK₁sub hk) k' (hK₁sub hk') h)
      (fun q k hk => hLlt q k (hK₁sub hk))
  refine ⟨v, K₂, hK₂sub.trans hK₁sub, hK₂ne, ?_, fun k hk => hK₁lab k (hK₂sub hk), Φ, hΦ⟩
  calc K.card ≤ K₀ * K₁.card := hK₁card
    _ ≤ K₀ * (L ^ n * K₂.card) := Nat.mul_le_mul_left K₀ hK₂card
    _ = K₀ * L ^ n * K₂.card := by ring

/-! ### Rider 2: the root-ward descent over `M + 1` levels (l.4919-4922) -/

/-- **The composition across levels.**  A chain of restrictions each losing a factor `Loss`
composes to `Loss ^ m` over `m` levels.  At `m = M + 1` and `Loss = K₀ * L ^ n` this is the
source's `[K₀(2 + 2log₂Λ)^{K₀}]^{-(M+1)}`, and it is where `Λ_f`'s polylog shape comes from — a
single application gives only `L ^ n`.

**Family/shading:** none.  **Level pair:** the `m` levels of the descent. -/
theorem card_le_pow_of_chain {κ : Type*} (Loss : ℕ) (K : ℕ → Finset κ) :
    ∀ m : ℕ, (∀ i, i < m → (K i).card ≤ Loss * (K (i + 1)).card) →
      (K 0).card ≤ Loss ^ m * (K m).card := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
      intro h
      calc (K 0).card ≤ Loss ^ m * (K m).card := ih (fun i hi => h i (by omega))
        _ ≤ Loss ^ m * (Loss * (K (m + 1)).card) :=
            Nat.mul_le_mul_left _ (h m (by omega))
        _ = Loss ^ (m + 1) * (K (m + 1)).card := by ring

/-! ### Rider 3: leaf-locality, and the stability it buys (l.4917-4918, l.4926-4927) -/

/-- **A leaf-local statistic** (l.4917-4918: *"depends only on the leaves of the relevant thread
cell"*): its value at a leaf `i` is determined by the fibre of `i`'s cell **inside the family the
statistic is computed in**.  The family is an explicit argument precisely so that "not changed by a
later restriction" is expressible. -/
def LeafLocalStat {ι γ : Type*} [DecidableEq γ] (cell : ι → γ)
    (D : Finset ι → ι → ENNReal) : Prop :=
  ∀ (u v : Finset ι) (i : ι),
    {j ∈ u | cell j = cell i} = {j ∈ v | cell j = cell i} → D u i = D v i

/-- **A whole-fibre restriction** (l.4926-4927: *"retain or discard an entire descendant fibre"*):
`t` is obtained from `u` by keeping whole `cell`-fibres. -/
def WholeFibreSubset {ι γ : Type*} (cell : ι → γ) (t u : Finset ι) : Prop :=
  t ⊆ u ∧ ∀ i ∈ t, ∀ j ∈ u, cell j = cell i → j ∈ t

/-- **A leaf-local statistic is unchanged by a whole-fibre restriction** — l.4926-4927. -/
theorem leafLocalStat_stable {ι γ : Type*} [DecidableEq γ] {cell : ι → γ}
    {D : Finset ι → ι → ENNReal} (hD : LeafLocalStat cell D)
    {t u : Finset ι} (h : WholeFibreSubset cell t u) {i : ι} (hi : i ∈ t) :
    D t i = D u i := by
  refine hD t u i (Finset.ext fun j => ?_)
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hj, hcj⟩
    exact ⟨h.1 hj, hcj⟩
  · rintro ⟨hj, hcj⟩
    exact ⟨h.2 i hi j hj hcj, hcj⟩

/-- **The band survives the later refinement** — the retention property  step B
and §SPEC row 20 need, and the reason leaf-locality is a hypothesis rather than a remark.

**Family/shading:** the leaves; the statistic's own cell map.  **Level pair:** the statistic's
level. -/
theorem band_stable_of_leafLocal {ι γ : Type*} [DecidableEq γ] {n : ℕ}
    {cell : Fin n → ι → γ} {D : Fin n → Finset ι → ι → ENNReal}
    (hD : ∀ q : Fin n, LeafLocalStat (cell q) (D q))
    {u t : Finset ι} (hwf : ∀ q : Fin n, WholeFibreSubset (cell q) t u)
    {K' : Finset ι} (hK' : K' ⊆ t) {Φ : Fin n → ENNReal}
    (hband : ∀ q : Fin n, ∀ k ∈ K', Φ q ≤ D q u k ∧ D q u k ≤ 2 * Φ q) :
    ∀ q : Fin n, ∀ k ∈ K', Φ q ≤ D q t k ∧ D q t k ≤ 2 * Φ q := by
  intro q k hk
  rw [leafLocalStat_stable (hD q) (hwf q) (hK' hk)]
  exact hband q k hk

/-- **Firing control: leaf-locality is doing work.**  The family-size statistic `D u i = #u` is not
leaf-local, and its value *does* move under a whole-fibre restriction, so
`band_stable_of_leafLocal` is false without the hypothesis and a bare bucket band does not imply
the retention property. -/
theorem not_stable_of_not_leafLocal :
    ∃ (cell : ℕ → ℕ) (D : Finset ℕ → ℕ → ENNReal) (t u : Finset ℕ),
      WholeFibreSubset cell t u ∧ ¬ LeafLocalStat cell D ∧ ∃ i ∈ t, D t i ≠ D u i := by
  classical
  refine ⟨id, fun v _ => (v.card : ENNReal), {0}, {0, 1}, ⟨?_, ?_⟩, ?_, 0, by simp, ?_⟩
  · intro j hj
    simp only [Finset.mem_singleton] at hj
    simp [hj]
  · intro i hi j hj hij
    simp only [Finset.mem_singleton] at hi
    simp only [id_eq] at hij
    simp [hij, hi]
  · intro hLL
    have h := leafLocalStat_stable (cell := id) (D := fun v _ => (v.card : ENNReal)) hLL
      (t := ({0} : Finset ℕ)) (u := ({0, 1} : Finset ℕ))
      ⟨by intro j hj; simp only [Finset.mem_singleton] at hj; simp [hj],
       by intro i hi j hj hij; simp only [Finset.mem_singleton] at hi
          simp only [id_eq] at hij; simp [hij, hi]⟩ (i := 0) (by simp)
    simp only [Finset.card_singleton] at h
    rw [show ({0, 1} : Finset ℕ).card = 2 by decide] at h
    exact absurd h (by norm_num)
  · simp only [Finset.card_singleton]
    rw [show ({0, 1} : Finset ℕ).card = 2 by decide]
    norm_num

/-- **The loss is polylogarithmic**, composed with the existing accounting: at the bucket count
`relativePlankJointLoss n M` and a cardinality ceiling `n ≤ 2 ^ k`, the `1/L` share of
`exists_bucket_band` is a `Λ_f`-shaped loss with `K_f = M + 2`. -/
theorem bucketBandLoss_le_polylog {n k : ℕ} (M : ℕ) (h : n ≤ 2 ^ k) :
    relativePlankJointLoss n M ≤ 2 * (k + 1) ^ (M + 2) :=
  relativePlankJointLoss_le_of_card_le_pow M h

end DensityBandFromBin

end Kakeya.ML2Core

end
