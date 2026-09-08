/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Mathlib.Data.ENNReal.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Order.Partition.Finpartition

/-!
# The greedy partition for an arbitrary score

The greedy construction behind the factoring lemmas of [GWZ, Section 4] and [GWZ, Section 9] does
not depend on the quantity being maximized.  We isolate it here for an arbitrary score
`σ : Finset ι → ℝ≥0∞`, so that both the unbiased factoring (`Kakeya.Factorization`) and the biased
one (`Kakeya.BiasedDensity`) can reuse it verbatim.

See blueprint `def:greedyPartitionScore`, `lem:greedyPartitionIsPartition`,
`lem:maxScoreAttainedOnBlock` and `lem:scoreBlockEqMaxScore`.
-/

@[expose] public section

namespace Kakeya

noncomputable section GreedyPartitionScore

variable {ι : Type*}

/-- A subset of `s` at which an arbitrary score `σ` on the subsets of `s` is maximal. -/
def scoreMaximizer (σ : Finset ι → ENNReal) (s : Finset ι) : Finset ι :=
  (Finset.exists_max_image s.powerset σ s.powerset_nonempty).choose

/-- The score maximizer of `s` is a subset of `s`. -/
theorem scoreMaximizer_subset (σ : Finset ι → ENNReal) (s : Finset ι) :
    scoreMaximizer σ s ⊆ s :=
  Finset.mem_powerset.mp (Finset.exists_max_image s.powerset σ s.powerset_nonempty).choose_spec.1

/-- `σ_max(u) = max_{t ⊆ u} σ t`, the maximal score over the subsets of `u`. -/
def maxScore (σ : Finset ι → ENNReal) (u : Finset ι) : ENNReal := σ (scoreMaximizer σ u)

/-- The score of a subset of `u` is at most the maximal score over the subsets of `u`. -/
theorem le_maxScore (σ : Finset ι → ENNReal) {u t : Finset ι} (h : t ⊆ u) :
    σ t ≤ maxScore σ u :=
  (Finset.exists_max_image u.powerset σ u.powerset_nonempty).choose_spec.2 t (by simpa using h)

/-- `maxScore σ` is monotone in the index set. -/
theorem maxScore_mono (σ : Finset ι → ENNReal) : Monotone (maxScore σ) :=
  fun u _ huv => le_maxScore σ ((scoreMaximizer_subset σ u).trans huv)

variable [DecidableEq ι]

/-- Blueprint `def:greedyPartitionScore`: the greedy partition `𝒫_σ(s)` of `s` for an arbitrary
score `σ` on subsets, defined by peeling off a maximizing block and recursing on the rest.

This generalises `ConvexSpaceBody.greedy_partition`, which is the case where `σ` is the (unbiased)
density score; the biased factoring of [GWZ, Lemma 9.2] uses it with the biased score
`Kakeya.biasedScore`. -/
def greedyPartitionScore (σ : Finset ι → ENNReal) (s : Finset ι) : Finpartition s := by
  induction s using Finset.strongInductionOn
  case a s H =>
    have hts : scoreMaximizer σ s ⊆ s := scoreMaximizer_subset σ s
    by_cases ht : (scoreMaximizer σ s).Nonempty
    · apply (H (s \ scoreMaximizer σ s) (Finset.sdiff_ssubset hts ht)).extend
      · exact ht.ne_empty
      · exact Finset.sdiff_disjoint
      · exact sdiff_sup_cancel hts
    · exact ⊤

/-- Blueprint `lem:greedyPartitionIsPartition`: the greedy construction terminates and produces a
partition of `s` into nonempty blocks. -/
theorem greedyPartitionScore_isPartition (σ : Finset ι → ENNReal) (s : Finset ι) :
    (∀ t ∈ (greedyPartitionScore σ s).parts, t.Nonempty) ∧
      (greedyPartitionScore σ s).parts.sup id = s :=
  ⟨fun _ ht => (greedyPartitionScore σ s).nonempty_of_mem_parts ht,
    (greedyPartitionScore σ s).sup_parts⟩

/-- Unfolding the greedy construction at a step where the score maximizer is nonempty. -/
private lemma parts_greedyPartitionScore_of_nonempty (σ : Finset ι → ENNReal) (s : Finset ι)
    (h : (scoreMaximizer σ s).Nonempty) : (greedyPartitionScore σ s).parts =
      {scoreMaximizer σ s} ∪ (greedyPartitionScore σ (s \ scoreMaximizer σ s)).parts := by
  unfold greedyPartitionScore
  rw [Finset.strongInductionOn_eq, dif_pos h]
  simp

/-- Unfolding the greedy construction at a step where the score maximizer is empty. -/
private lemma parts_greedyPartitionScore_of_empty (σ : Finset ι → ENNReal) (s : Finset ι)
    (h : scoreMaximizer σ s = ∅) : (greedyPartitionScore σ s).parts ⊆ {s} := by
  unfold greedyPartitionScore
  rw [Finset.strongInductionOn_eq, dif_neg]
  · exact Finpartition.parts_top_subset s
  · simpa

/-- Blueprint `lem:maxScoreAttainedOnBlock`: for every nonempty subfamily `A` of the blocks of the
greedy partition, the maximum of `σ` over the subsets of `⨆ A` is attained at a block of `A`.

The normalisation `σ ∅ = 0` is part of blueprint `def:greedyPartitionScore` and is necessary: if
the maximum of `σ` over the subsets of `s` were attained at `∅` with `σ ∅ > 0`, the greedy
construction would stop immediately and no block could realise that maximum. Both scores used in
this development are normalised, the unbiased density score and `Kakeya.biasedScore`. -/
theorem maxScore_eq_of_subset_greedyPartition {σ : Finset ι → ENNReal} (hσ : σ ∅ = 0) {s : Finset ι}
    {A : Finset (Finset ι)} (hAne : A.Nonempty) (hA : A ⊆ (greedyPartitionScore σ s).parts) :
    ∃ r ∈ A, maxScore σ (A.sup id) = σ r := by
  induction s using Finset.strongInductionOn
  case a s H =>
    have hAs : A.sup id ⊆ s := by
      rw [← (greedyPartitionScore σ s).sup_parts]; exact Finset.sup_mono (f := id) hA
    by_cases ht : (scoreMaximizer σ s).Nonempty
    · by_cases h : scoreMaximizer σ s ∈ A
      · exact ⟨_, h, le_antisymm (maxScore_mono σ hAs)
          (le_maxScore σ (Finset.le_sup (f := id) h))⟩
      · refine H _ (Finset.sdiff_ssubset (scoreMaximizer_subset σ s) ht) fun t' ht' => ?_
        have h1 := parts_greedyPartitionScore_of_nonempty σ s ht ▸ hA ht'
        exact (Finset.mem_union.mp h1).resolve_left
          fun h2 => h (Finset.eq_of_mem_singleton h2 ▸ ht')
    · rw [Finset.not_nonempty_iff_eq_empty] at ht
      obtain ⟨r, hr⟩ := hAne
      have hr_eq_s : r = s :=
        Finset.mem_singleton.mp (parts_greedyPartitionScore_of_empty σ s ht (hA hr))
      have hmax : maxScore σ s = 0 := by rw [maxScore, ht, hσ]
      have hsup : A.sup id = s := le_antisymm hAs (hr_eq_s ▸ Finset.le_sup (f := id) hr)
      refine ⟨r, hr, ?_⟩
      -- Every subset of `s` has score `≤ maxScore σ s = 0`, so in particular `σ s = 0`.
      rw [hsup, hr_eq_s]
      exact le_antisymm (hmax.trans_le zero_le) (le_maxScore σ (Finset.Subset.refl s))

/-- Blueprint `lem:scoreBlockEqMaxScore`: the score of a block of the greedy partition equals the
maximal score over its own subsets. As in `Kakeya.maxScore_eq_of_subset_greedyPartition`, the score
is normalised by `σ ∅ = 0`. -/
theorem score_eq_maxScore_of_mem_greedyPartition {σ : Finset ι → ENNReal} (hσ : σ ∅ = 0)
    {s t : Finset ι}
    (ht : t ∈ (greedyPartitionScore σ s).parts) : σ t = maxScore σ t := by
  -- Apply `maxScore_eq_of_subset_greedyPartition` to the singleton subfamily `A = {t}`
  obtain ⟨r, hr, h⟩ := maxScore_eq_of_subset_greedyPartition hσ (Finset.singleton_nonempty t)
    (Finset.singleton_subset_iff.mpr ht)
  simpa [Finset.mem_singleton.mp hr] using h.symm

end GreedyPartitionScore

end Kakeya
