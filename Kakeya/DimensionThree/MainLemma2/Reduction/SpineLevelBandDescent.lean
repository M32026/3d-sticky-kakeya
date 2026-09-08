/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFourStatisticsLeafLocal
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineCanonicalCover
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineTowerArrayFibre
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorShapeRetube
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineWindowRestrictionTransport

/-!
# A1's root-ward descent, assembled: the multi-level band on one retained family

`SpineDensityBandFromBin.lean` supplies A1 at **one** level (`exists_joint_bucket_band_with_label`)
and prices the descent abstractly (`card_le_pow_of_chain`).  This file performs the descent: it
runs the per-level regularisation at every level of a nested cell system and returns **one**
retained family carrying **all** the levels' bands at once, read in the retained family itself.

## The order of the descent, and why it is forced

l.4919-4922: *"Descending from the leaves to the root and retaining one joint vector bin gives a
restricted threaded tower."*  The order is not decoration.  The band established at level `p` is a
statement about the statistic **read in the family it is established in**; a later restriction
changes the family and therefore may change the statistic.  Leaf-locality
(`Kakeya.ML2Core.LeafLocalStat`) says it does *not* change when the later restriction retains whole
`cell p`-fibres (l.4926-4927), and `Kakeya.ML2Core.leafLocalStat_stable` is that step.  A
restriction performed at level `p'` retains whole `cell p'`-fibres, and a whole-fibre restriction at
a **coarser** map is whole-fibre at every **finer** one (`wholeFibreSubset_of_refines`).  So the
level-`p` band survives exactly the restrictions performed at levels `p' ≥ p`:

> **the levels must be processed from the finest to the coarsest** — the source's leaves-to-root.

That is why `exists_multiLevel_band` takes `g` **increasingly coarse** (`hmono` : a finer cell map
determines a coarser one) and inducts on the coarsest index.  Instantiated at a tower it is
`g p := 𝒰.cover.assign (L - p)`, so `g 0` is the leaf level and `g L` the root.

## What had to be added to A1 to make the descent close

A1's per-level device returns an opaque retained set.  The descent needs that set to be a **union
of whole cells**, since that is the hypothesis of `leafLocalStat_stable`.  It is: every retained set
in A1's proof is a `Finset.filter` by a bucket value, and a filter by a **cell-determined**
predicate is whole-fibre by inspection.  The A1 declarations do not expose this, so the three
pigeonholes are restated here with the extra conclusion and the extra hypothesis that makes it true
(`hbc`, `hlabc`: the bucket and the label are constant on cells).  Nothing in
`SpineDensityBandFromBin.lean` is edited; these are siblings, and
`not_wholeFibre_of_not_cellDetermined` is the firing control that the new hypothesis is doing work.

## Family / shading / level pair

| declaration | family / shading | level pair |
|---|---|---|
| `WholeFibreSubset.trans`, `wholeFibreSubset_of_refines` | abstract | none |
| `exists_bucket_band_fibre`, `exists_joint_bucket_band_fibre` | abstract | one level |
| `exists_constant_label_fibre`, `exists_level_band_step` | abstract | one level |
| `exists_multiLevel_band` | abstract; the retained family is the conclusion | `0 … M` |
| `levelDensityStat_congr_cell`, `levelDensityStat_le_card` | the tower's `u` | `(p,c)` |
| `one_le_levelDensityStat_of_mem` | as above | `(p,c)` |
| `exists_levelDensityStat_band` | the **retained** family `t ⊆ u`; no shading | every `(p,c)` |
| `levelDensityBand_indexSet` | the tower's own family `t`; no shading | every `(p,c)` |
| `le_level_maxDensity_of_fibre_witness` | the tower's `u`; no shading | `(a,c)`, `c` inset |
| `pairwise_of_levelDensityBand` | the tower's own family; no shading | every `(p,c)` |

## The second half: A1 instantiated, and the two rows it closes

`exists_levelDensityStat_band` is the list's step 1 — A1 run at the two-level density statistics of
every level pair, brackets `1 ≤ · ≤ #u` (so `C₁ = 0`, no `δ`-power spent below), loss
`((J+1)^{L+1})^{L+1}` — and `levelDensityBand_indexSet` reads it onto the nodes in the shape
`Kakeya.ML2Reduction.IsKatzTaoDividingWindowLevels.level_density_band` states, verbatim (the
`example` after it is the match control: the field's projection inhabits the stated type).

`le_level_maxDensity_of_fibre_witness` is step 2, and it is the record that **no field
moves** : the lower-bound field stays stated on `nodesUnder` and its witness
is *produced* on the fibre array.

`pairwise_of_levelDensityBand` is the measurement of what remains: the field is a regularity
demand on the family it is asked on, so it cannot be supplied on an arbitrary subfamily.

## The third half: where the refinement is allowed to happen, and the route that allows it

The measurement above has a routing consequence and it is the file's main finding.
`Kakeya.ML2Core.InheritedWindowSupplyAt` (`= FixedTowerStoppingObligation`) asks for the window on
the tower over the **given** `S`, for **every** `S`.  By `pairwise_of_levelDensityBand` that is a
regularity demand on `S` and is therefore not supplied by `Kakeya.ML2Core.IsClassHomogeneousOn`,
which bands class *cardinalities* -- two cells of equal size can carry very different maximal
densities.  **`Kakeya.ML2Core.FloorDataAtTrichotomy` does not require it**: its `(F)` disjunct
`Kakeya.ML2Core.RefinedFloorHypothesis` binds `S' ⊆ S` and asks for the window on
`Kakeya.ML2Core.refinedHierarchy`, i.e. on the **refined** tower -- exactly where the source
performs its refinement (l.4056-4058).

So `levelDensityBand_refinedHierarchy` and `exists_refinement_levelDensityBand_refinedHierarchy`
deliver step 1 on the `(F)` branch's own tower, and `RefinedFloorSupplyAt` /
`floorDataAtTrichotomy_of_refinedFloorSupply` name the payload's remaining goal on that route.
`refinedFloorSupplyAt_of_windowed` is the control that the new route is weaker: the existing
windowed route produces it (on the `(F)` side).  

| declaration | family / shading | level pair |
|---|---|---|
| `levelDensityBand_refinedHierarchy` | `S'` with shading `W` | every `(p,c)` |
| `exists_refinement_levelDensityBand_refinedHierarchy` | `u` refined to `S'` | every `(p,c)` |
| `RefinedFloorSupplyAt`, `floorDataAtTrichotomy_of_refinedFloorSupply` | `S,Z → S',W` | `(a,b,m)` |
| `classCountStat` + its four lemmas | the family `w`; no shading | one level `k` |
| `fibreShadedMassStat` + its five lemmas | the family `w` **with shading `Z`** | one level `k` |
| `fourStatRow` + its extraction lemmas | `w`; shading only in the `q = 2L+3` row | one level `k` |
| `isClassHomogeneousOn_of_classCountBand` | the retained family | every `k` |
| `exists_levelBand_classHomogeneous` | `u` refined to `t`; no shading | every `(p,c)`, every `k` |
| `exists_refinement_classHomogeneous_levelDensityBand` | `u → S'`, shading `W` | all `(p,c)` |
| `exists_refinement_classHomogeneous_levelDensityBand` | `u → S'`; shading at `W` | every `(p,c)` |

## The fourth half:, applied

** — one joint pass, not two.**  A separate homogenising pass is a further restriction that
moves the already-regularised statistics **unless it is whole-fibre**, and the source avoids it by
construction: l.4032-4035 lists **descendant counts** among the four statistics regularised
together, and descendant counts *are* Def 2.1(iii)'s class band (l.227-228), which is what
`Kakeya.ML2Core.IsClassHomogeneousOn` renders.  l.4916-4917: *"all of them are regularized at
once."*  So the class count rides in A1's bin as one more leaf-local, cell-determined statistic
(`classCountStat`), and `isClassHomogeneousOn_of_classCountBand` reads the homogeneity off the
band.  `exists_levelBand_classHomogeneous` is that pass; **no second restriction is run, in either
order.**  The factor two is paid into the tower's own constant as `2 ≤ Cu`, `δ`-free.

** — the four statistics, and where the tree keeps them.**  The tree carries **two** of
l.4032-4035's four, in two different places and two different roles: two-level maximal densities as
the *field* `IsKatzTaoDividingWindowLevels.level_density_band`, and descendant counts as the
*hypothesis* `IsClassHomogeneousOn`.  That dispersal is itself the pattern.  The missing two —
**two-level counts** and **fibre shaded masses**, `SRC-A′`'s residue — are supplied here
(`levelCountStat`'s two new lemmas, `fibreShadedMassStat` and its five), and
`exists_levelBand_fourStatistics` produces **all four at once** on one retained family, together
with the class homogeneity.  That is the source's l.4030-4035 hypothesis on `𝕊'`, produced rather
than assumed — which is exactly why the obligation belongs on `S'` and not on an
arbitrary `S`.

The mass row is the only one that spends a `δ`-power below, and it spends the caller's per-tube
shade floor `m` (the source's `δ^{3η_f}`, which a `HasDenseShading` hypothesis already supplies);
`le_fourStatRow` is where that is discharged.  All four rows share one upper bracket
(`#u` + total shaded mass, both finite) so the vector runs at a single dyadic ceiling.

## The fifth half: the mass-weighted run, and `IsShadedRefinementOf` produced

l.4056-4058 retains a share of the **mass**, not of the node count, and that is
`Kakeya.ML2Core.IsShadedRefinementOf`'s fifth clause.  The `_wt` siblings
(`exists_bucket_band_fibre_wt`, `exists_constant_label_fibre_wt`,
`exists_joint_bucket_band_fibre_wt`, `exists_level_band_step_wt`, `exists_multiLevel_band_wt`) run
the same descent choosing at each bucketing the bucket of largest **weight**; nothing above is
edited, because a node pigeonhole and a mass pigeonhole are different pigeonholes and each is
correct for its own retention.

`exists_shadedRefinement_of_joint_bin` is the payoff: **all six** conjuncts of
`IsShadedRefinementOf` from one whole-fibre pass — subset, nonemptiness, same tubes and sub-shading
(at `W := Z`, both `rfl`), the mass retention (the weighted descent) and class homogeneity (the
descendant-count row) — with the four bands alongside.

So the `(F)` branch's first conjunct is no longer an obligation.
`refinedFloorHypothesis_of_parts` records exactly what is left and on which tower: the window and
`Kakeya.ML2Core.FloorHypothesisAt`, **both on `refinedHierarchy 𝒱 hS' hhom rfl`**, with `hS'` and
`hhom` the same terms in all three parts.  `isKatzTaoDividingWindowLevels_of_width_and_band`
assembles the first of those from the width `ε_d·L + a ≤ b`, the four density fields and this
file's band; the existing `Kakeya.ML2Core.floorHypothesisAt_of_windowLevels` assembles the second
from the window plus `ParentAdmissible` and `FillAt`.
| `refinedFloorSupplyAt_of_windowed` | as above | `(a,b,m)` |

No shading anywhere in this file: the descent is a statement about statistics of a cell system.
The shading `Z → W` enters at the caller that applies the refinement, not here.

## A1-a

No `GridUniformCore`; no (F)-branch interface statement is defined or altered.
-/

@[expose] public section

open scoped NNReal ENNReal

namespace Kakeya.ML2Core

section LevelBandDescent

variable {ι γ : Type*}

/-- **Whole-fibre restrictions compose.** -/
theorem WholeFibreSubset.trans {cell : ι → γ} {t s u : Finset ι}
    (hts : WholeFibreSubset cell t s) (hsu : WholeFibreSubset cell s u) :
    WholeFibreSubset cell t u := by
  refine ⟨hts.1.trans hsu.1, fun i hi j hj hcell => ?_⟩
  exact hts.2 i hi j (hsu.2 i (hts.1 hi) j hj hcell) hcell

/-- **A whole-fibre restriction at a coarser cell map is whole-fibre at every finer one.**

This is the step that forces the leaves-to-root order: `hrefines` says `c` **refines** `d` on `u`
(members sharing a `c`-cell share a `d`-cell), and the conclusion moves the property from the
coarse map `d` to the fine map `c`. -/
theorem wholeFibreSubset_of_refines {c : ι → γ} {d : ι → γ} {t u : Finset ι}
    (h : WholeFibreSubset d t u)
    (hrefines : ∀ i ∈ u, ∀ j ∈ u, c j = c i → d j = d i) :
    WholeFibreSubset c t u := by
  refine ⟨h.1, fun i hi j hj hcell => ?_⟩
  exact h.2 i hi j hj (hrefines i (h.1 hi) j hj hcell)

/-- **`Kakeya.ML2Core.exists_bucket_band` with the retained set exhibited as a union of whole
cells.**  Same pigeonhole, same `Cstar = 2`, same `1/L` share; the one new hypothesis is that the
bucket is **constant on cells**, which is what makes the retained filter whole-fibre. -/
theorem exists_bucket_band_fibre {κ : Type*} (cell : κ → γ) (K : Finset κ) (hK : K.Nonempty)
    (D : κ → ENNReal) (bucket : κ → ℕ) (L : ℕ)
    (hbc : ∀ k k', cell k = cell k' → bucket k = bucket k')
    (hb : ∀ k ∈ K, ∀ k' ∈ K, bucket k = bucket k' → D k' ≤ 2 * D k)
    (hL : ∀ k ∈ K, bucket k < L) :
    ∃ K' : Finset κ, K' ⊆ K ∧ K'.Nonempty ∧ K.card ≤ L * K'.card ∧
      WholeFibreSubset cell K' K ∧
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
  have hK'ne : (K.filter (fun k => bucket k = v)).Nonempty := by
    rw [← Finset.card_pos]
    by_contra hzero
    rw [Nat.pos_iff_ne_zero, not_not] at hzero
    rw [hzero, Nat.mul_zero, Nat.le_zero, Finset.card_eq_zero] at hv
    exact absurd hk₀ (by rw [hv]; exact Finset.notMem_empty k₀)
  refine ⟨K.filter (fun k => bucket k = v), Finset.filter_subset _ _, hK'ne, hv, ?_, ?_⟩
  · refine ⟨Finset.filter_subset _ _, fun i hi j hj hcell => ?_⟩
    refine Finset.mem_filter.mpr ⟨hj, ?_⟩
    rw [hbc j i hcell]
    exact (Finset.mem_filter.mp hi).2
  · refine ⟨(K.filter (fun k => bucket k = v)).inf' hK'ne D, fun k hk => ⟨?_, ?_⟩⟩
    · exact Finset.inf'_le D hk
    · obtain ⟨k₁, hk₁mem, hk₁eq⟩ := Finset.exists_mem_eq_inf' hK'ne D
      rw [hk₁eq]
      obtain ⟨hk₁K, hk₁v⟩ := Finset.mem_filter.mp hk₁mem
      obtain ⟨hkK, hkv⟩ := Finset.mem_filter.mp hk
      exact hb k₁ hk₁K k hkK (by rw [hk₁v, hkv])

/-- **`Kakeya.ML2Core.exists_constant_label` with the retained set whole-fibre**, on the same
hypothesis: the label is constant on cells (which the source's label is — it is a label *of a
cell*). -/
theorem exists_constant_label_fibre {κ : Type*} (cell : κ → γ) (K : Finset κ) (hK : K.Nonempty)
    (lab : κ → ℕ) (K₀ : ℕ) (hlab : ∀ k ∈ K, lab k < K₀)
    (hlabc : ∀ k k', cell k = cell k' → lab k = lab k') :
    ∃ (w : ℕ) (K' : Finset κ), K' ⊆ K ∧ K'.Nonempty ∧ K.card ≤ K₀ * K'.card ∧
      WholeFibreSubset cell K' K ∧ ∀ k ∈ K', lab k = w := by
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
  refine ⟨v, K.filter (fun k => lab k = v), Finset.filter_subset _ _, hpos, hv, ?_,
    fun k hk => (Finset.mem_filter.mp hk).2⟩
  refine ⟨Finset.filter_subset _ _, fun i hi j hj hcell => ?_⟩
  refine Finset.mem_filter.mpr ⟨hj, ?_⟩
  rw [hlabc j i hcell]
  exact (Finset.mem_filter.mp hi).2

/-- **The joint single-bin band with the retained set whole-fibre**: `n` statistics at once, loss
`L ^ n`, and a union of whole cells.  The `n` statistics of one level share the level's cell map,
which is why one `cell` serves the whole vector. -/
theorem exists_joint_bucket_band_fibre {κ : Type*} (cell : κ → γ) :
    ∀ (n : ℕ) (K : Finset κ), K.Nonempty →
      ∀ (D : Fin n → κ → ENNReal) (bucket : Fin n → κ → ℕ) (L : ℕ), 0 < L →
      (∀ q : Fin n, ∀ k k', cell k = cell k' → bucket q k = bucket q k') →
      (∀ q : Fin n, ∀ k ∈ K, ∀ k' ∈ K, bucket q k = bucket q k' → D q k' ≤ 2 * D q k) →
      (∀ q : Fin n, ∀ k ∈ K, bucket q k < L) →
      ∃ K' : Finset κ, K' ⊆ K ∧ K'.Nonempty ∧ K.card ≤ L ^ n * K'.card ∧
        WholeFibreSubset cell K' K ∧
        ∃ Φ : Fin n → ENNReal, ∀ q : Fin n, ∀ k ∈ K', Φ q ≤ D q k ∧ D q k ≤ 2 * Φ q := by
  intro n
  induction n with
  | zero =>
      intro K hK D bucket L hL _ _ _
      exact ⟨K, Finset.Subset.refl K, hK, by simp,
        ⟨Finset.Subset.refl K, fun _ _ j hj _ => hj⟩, Fin.elim0, fun q => q.elim0⟩
  | succ n ih =>
      intro K hK D bucket L hL hbc hb hLlt
      obtain ⟨K₁, hK₁sub, hK₁ne, hK₁card, hK₁wf, Φlast, hΦlast⟩ :=
        exists_bucket_band_fibre cell K hK (D (Fin.last n)) (bucket (Fin.last n)) L
          (hbc (Fin.last n)) (hb (Fin.last n)) (hLlt (Fin.last n))
      obtain ⟨K₂, hK₂sub, hK₂ne, hK₂card, hK₂wf, Φ, hΦ⟩ :=
        ih K₁ hK₁ne (fun q => D q.castSucc) (fun q => bucket q.castSucc) L hL
          (fun q => hbc q.castSucc)
          (fun q k hk k' hk' h => hb q.castSucc k (hK₁sub hk) k' (hK₁sub hk') h)
          (fun q k hk => hLlt q.castSucc k (hK₁sub hk))
      refine ⟨K₂, hK₂sub.trans hK₁sub, hK₂ne, ?_, hK₂wf.trans hK₁wf, Fin.snoc Φ Φlast, ?_⟩
      · calc K.card ≤ L * K₁.card := hK₁card
          _ ≤ L * (L ^ n * K₂.card) := Nat.mul_le_mul_left L hK₂card
          _ = L ^ (n + 1) * K₂.card := by ring
      · intro q k hk
        refine Fin.lastCases ?_ ?_ q
        · simpa using hΦlast k (hK₂sub hk)
        · intro q'
          simpa using hΦ q' k hk

/-- **One level of the descent**: the label made constant and the `n` statistics of the level each
pinned to a profile within a factor two, on a retained family that is a **union of whole cells**.
Loss `K₀ * L ^ n`, exactly `exists_joint_bucket_band_with_label`'s, with the whole-fibre conclusion
the descent needs added. -/
theorem exists_level_band_step {n : ℕ} (cell : ι → γ) (v : Finset ι) (hv : v.Nonempty)
    (D : Fin n → ι → ENNReal) (bucket : Fin n → ι → ℕ) (L : ℕ) (hL : 0 < L)
    (hbc : ∀ q : Fin n, ∀ i j, cell i = cell j → bucket q i = bucket q j)
    (hpair : ∀ q : Fin n, ∀ i ∈ v, ∀ j ∈ v, bucket q i = bucket q j → D q j ≤ 2 * D q i)
    (hlt : ∀ q : Fin n, ∀ i ∈ v, bucket q i < L)
    (lab : ι → ℕ) (K₀ : ℕ) (hK₀ : ∀ i ∈ v, lab i < K₀)
    (hlabc : ∀ i j, cell i = cell j → lab i = lab j) :
    ∃ t : Finset ι, t ⊆ v ∧ t.Nonempty ∧ v.card ≤ K₀ * L ^ n * t.card ∧
      WholeFibreSubset cell t v ∧ (∃ w : ℕ, ∀ k ∈ t, lab k = w) ∧
      ∃ Φ : Fin n → ENNReal, ∀ q : Fin n, ∀ k ∈ t, Φ q ≤ D q k ∧ D q k ≤ 2 * Φ q := by
  obtain ⟨w, v₁, hv₁sub, hv₁ne, hv₁card, hv₁wf, hv₁lab⟩ :=
    exists_constant_label_fibre cell v hv lab K₀ hK₀ hlabc
  obtain ⟨v₂, hv₂sub, hv₂ne, hv₂card, hv₂wf, Φ, hΦ⟩ :=
    exists_joint_bucket_band_fibre cell n v₁ hv₁ne D bucket L hL hbc
      (fun q k hk k' hk' h => hpair q k (hv₁sub hk) k' (hv₁sub hk') h)
      (fun q k hk => hlt q k (hv₁sub hk))
  refine ⟨v₂, hv₂sub.trans hv₁sub, hv₂ne, ?_, hv₂wf.trans hv₁wf,
    ⟨w, fun k hk => hv₁lab k (hv₂sub hk)⟩, Φ, hΦ⟩
  calc v.card ≤ K₀ * v₁.card := hv₁card
    _ ≤ K₀ * (L ^ n * v₂.card) := Nat.mul_le_mul_left K₀ hv₂card
    _ = K₀ * L ^ n * v₂.card := by ring

/-- **The descent, assembled** (l.4919-4922).  One retained family carries the band at **every**
level `p ≤ M`, read in the retained family itself, at the total loss
`(K₀ · L^n)^(M+1)` — the source's `[K₀(2+2log₂Λ)^{K₀}]^{-(M+1)}` shape, `card_le_pow_of_chain`'s
price paid level by level rather than assumed.

`g` is the level's cell map, **increasingly coarse**: `hmono` says a finer cell determines a
coarser one, so `g 0` is the leaf level and `g M` the root.  The bucket map is allowed to depend on
the family it is computed in — it must, since the statistic does — and its hypotheses are asked
only on subfamilies of `u`.

**Family/shading:** the retained family is the conclusion; no shading.  **Level pair:** `0 … M`. -/
theorem exists_multiLevel_band [DecidableEq γ] {n : ℕ}
    (u : Finset ι) (hu : u.Nonempty) (g : ℕ → ι → γ)
    (hmono : ∀ p q : ℕ, p ≤ q → ∀ i ∈ u, ∀ j ∈ u, g p i = g p j → g q i = g q j)
    (D : ℕ → Fin n → Finset ι → ι → ENNReal)
    (hloc : ∀ (p : ℕ) (q : Fin n), LeafLocalStat (g p) (D p q))
    (bucket : ℕ → Fin n → Finset ι → ι → ℕ)
    (hbc : ∀ (p : ℕ) (q : Fin n) (w : Finset ι) (i j : ι),
      g p i = g p j → bucket p q w i = bucket p q w j)
    (L : ℕ) (hL : 0 < L)
    (hlt : ∀ (p : ℕ) (q : Fin n), ∀ w ⊆ u, ∀ i ∈ w, bucket p q w i < L)
    (hpair : ∀ (p : ℕ) (q : Fin n), ∀ w ⊆ u, ∀ i ∈ w, ∀ j ∈ w,
      bucket p q w i = bucket p q w j → D p q w j ≤ 2 * D p q w i)
    (lab : ℕ → ι → ℕ) (K₀ : ℕ) (hK₀ : ∀ p : ℕ, ∀ i ∈ u, lab p i < K₀)
    (hlabc : ∀ (p : ℕ) (i j : ι), g p i = g p j → lab p i = lab p j) :
    ∀ M : ℕ, ∃ t : Finset ι, t ⊆ u ∧ t.Nonempty ∧
      u.card ≤ (K₀ * L ^ n) ^ (M + 1) * t.card ∧
      (∃ vl : ℕ → ℕ, ∀ p ≤ M, ∀ k ∈ t, lab p k = vl p) ∧
      ∃ Φ : ℕ → Fin n → ENNReal, ∀ p ≤ M, ∀ q : Fin n, ∀ k ∈ t,
        Φ p q ≤ D p q t k ∧ D p q t k ≤ 2 * Φ p q := by
  intro M
  induction M with
  | zero =>
      obtain ⟨t, hts, htne, htcard, htwf, ⟨w, hw⟩, Φ, hΦ⟩ :=
        exists_level_band_step (n := n) (g 0) u hu (fun q => D 0 q u) (fun q => bucket 0 q u)
          L hL (fun q => hbc 0 q u) (hpair 0 · u (Finset.Subset.refl u))
          (hlt 0 · u (Finset.Subset.refl u)) (lab 0) K₀ (hK₀ 0) (hlabc 0)
      refine ⟨t, hts, htne, by simpa using htcard, ⟨fun _ => w, fun p hp k hk => ?_⟩,
        fun _ q => Φ q, fun p hp q k hk => ?_⟩
      · rw [Nat.le_zero.mp hp]; exact hw k hk
      · rw [Nat.le_zero.mp hp, leafLocalStat_stable (hloc 0 q) htwf hk]
        exact hΦ q k hk
  | succ M ih =>
      obtain ⟨t₁, ht₁s, ht₁ne, ht₁card, ⟨vl, hvl⟩, Φ₁, hΦ₁⟩ := ih
      obtain ⟨t₂, ht₂s, ht₂ne, ht₂card, ht₂wf, ⟨w, hw⟩, Φ₂, hΦ₂⟩ :=
        exists_level_band_step (n := n) (g (M + 1)) t₁ ht₁ne (fun q => D (M + 1) q t₁)
          (fun q => bucket (M + 1) q t₁) L hL (fun q => hbc (M + 1) q t₁)
          (hpair (M + 1) · t₁ ht₁s) (hlt (M + 1) · t₁ ht₁s) (lab (M + 1)) K₀
          (fun i hi => hK₀ (M + 1) i (ht₁s hi)) (hlabc (M + 1))
      have hwfp : ∀ p ≤ M + 1, WholeFibreSubset (g p) t₂ t₁ := by
        intro p hp
        refine wholeFibreSubset_of_refines ht₂wf (fun i hi j hj hcell => ?_)
        exact hmono p (M + 1) hp j (ht₁s hj) i (ht₁s hi) hcell
      refine ⟨t₂, ht₂s.trans ht₁s, ht₂ne, ?_,
        ⟨fun p => if p = M + 1 then w else vl p, fun p hp k hk => ?_⟩,
        fun p => if p = M + 1 then Φ₂ else Φ₁ p, fun p hp q k hk => ?_⟩
      · calc u.card ≤ (K₀ * L ^ n) ^ (M + 1) * t₁.card := ht₁card
          _ ≤ (K₀ * L ^ n) ^ (M + 1) * (K₀ * L ^ n * t₂.card) :=
              Nat.mul_le_mul_left _ ht₂card
          _ = (K₀ * L ^ n) ^ (M + 1 + 1) * t₂.card := by ring
      · dsimp only
        rcases Nat.lt_or_ge p (M + 1) with hlt' | hge
        · rw [if_neg (by omega)]
          exact hvl p (by omega) k (ht₂s hk)
        · have hpe : p = M + 1 := by omega
          subst hpe
          rw [if_pos rfl]
          exact hw k hk
      · dsimp only
        rcases Nat.lt_or_ge p (M + 1) with hlt' | hge
        · rw [if_neg (by omega : ¬ p = M + 1),
            leafLocalStat_stable (hloc p q) (hwfp p (by omega)) hk]
          exact hΦ₁ p (by omega) q k (ht₂s hk)
        · have hpe : p = M + 1 := by omega
          subst hpe
          rw [if_pos rfl, leafLocalStat_stable (hloc (M + 1) q) (hwfp (M + 1) le_rfl) hk]
          exact hΦ₂ q k hk

/-- **Firing control: cell-determination of the bucket is doing work.**  Without `hbc` the retained
set of a bucket pigeonhole need not be a union of whole cells — `cell ≡ 0` on `{0,1}` with
`bucket 0 = 0`, `bucket 1 = 1` splits one cell — so `leafLocalStat_stable` would not apply and the
descent would not compose. -/
theorem not_wholeFibre_of_not_cellDetermined :
    ∃ (K K' : Finset ℕ) (cell : ℕ → ℕ) (bucket : ℕ → ℕ),
      K' = K.filter (fun k => bucket k = 0) ∧ ¬ WholeFibreSubset cell K' K ∧
      ¬ (∀ k k', cell k = cell k' → bucket k = bucket k') := by
  classical
  refine ⟨{0, 1}, ({0, 1} : Finset ℕ).filter (fun k => k = 0), fun _ => 0, id, rfl, ?_, ?_⟩
  · rintro ⟨-, h2⟩
    have h := h2 0 (by decide) 1 (by decide) rfl
    revert h
    decide
  · intro h
    have := h 0 1 rfl
    revert this
    decide


/-- **Firing control: the leaves-to-root order is forced.**  `wholeFibreSubset_of_refines` runs from
the coarse map to the fine one and **not** back: a restriction that retains whole *fine* cells can
split a *coarse* one.  So a descent that processed the root first would lose the coarse level's band
at the next step, and the order of `exists_multiLevel_band` is content, not presentation. -/
theorem not_wholeFibreSubset_of_finer :
    ∃ (c d : ℕ → ℕ) (t u : Finset ℕ), WholeFibreSubset c t u ∧
      (∀ i ∈ u, ∀ j ∈ u, c j = c i → d j = d i) ∧ ¬ WholeFibreSubset d t u := by
  classical
  refine ⟨id, fun _ => 0, {0}, {0, 1}, ⟨?_, ?_⟩, fun _ _ _ _ _ => rfl, ?_⟩
  · intro j hj
    simp only [Finset.mem_singleton] at hj
    simp [hj]
  · intro i hi j hj hcell
    simp only [Finset.mem_singleton] at hi
    simp only [id_eq] at hcell
    simp [hcell, hi]
  · rintro ⟨-, h2⟩
    have h := h2 0 (by decide) 1 (by decide) rfl
    revert h
    decide

end LevelBandDescent

section LevelDensityBandInstance

open MeasureTheory Tube

universe v

variable {ι : Type v} {δ Cu : NNReal} {u : Finset ι}
  {T : ι → Tube δ (EuclideanSpace ℝ (Fin 3))}

open scoped Classical in
/-- **The density statistic is a function of the leaf's cell** — it mentions the leaf only through
`𝒰.cover.assign p`, so two leaves of one level-`p` cell carry the same value.  This is what makes
the level-`p` bucket map cell-determined, which is what `exists_multiLevel_band` needs. -/
theorem levelDensityStat_congr_cell (𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu)
    (p c : ℕ) (w : Finset ι) {i j : ι} (h : 𝒰.cover.assign p i = 𝒰.cover.assign p j) :
    levelDensityStat 𝒰 p c w i = levelDensityStat 𝒰 p c w j := by
  simp only [levelDensityStat, h]

open scoped Classical in
/-- **The upper bracket, unconditionally**: the two-level density read in any subfamily `w` is at
most `#w`.  `Kakeya.maxDensity_le_card` then the two cardinality steps
(`Finset.card_image_le`, `Finset.card_filter_le`); no source hypothesis and no `δ`-power is
needed, so the bucket ceiling `J` is fixed by the family size alone. -/
theorem levelDensityStat_le_card (𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu)
    (p c : ℕ) (w : Finset ι) (i : ι) :
    levelDensityStat 𝒰 p c w i ≤ (w.card : ENNReal) := by
  classical
  refine le_trans (Kakeya.maxDensity_le_card _ _) ?_
  have h1 : ((Tube.coverClass w (𝒰.cover.assign p) (𝒰.cover.assign p i)).image
      (𝒰.cover.assign c)).card ≤ w.card := by
    refine le_trans (Finset.card_image_le) ?_
    exact Finset.card_le_card (Finset.filter_subset _ _)
  exact_mod_cast h1

open scoped Classical in
/-- **The lower bracket, at `1`** (`C₁ = 0`): the cell of `i` holds `i`'s own level-`c` node and a
grid-radius tube has positive volume, so `Kakeya.ML2Reduction.one_le_maxDensity_tube` applies.
`0 < δ` is the only hypothesis. -/
theorem one_le_levelDensityStat_of_mem (hδ : 0 < δ)
    (𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu)
    (p c : ℕ) {w : Finset ι} {i : ι} (hi : i ∈ w) :
    1 ≤ levelDensityStat 𝒰 p c w i := by
  classical
  refine Kakeya.ML2Reduction.one_le_maxDensity_tube
    (Tube.gridScale_pos hδ (Tube.ssfGridLen δ) c) (𝒰.cover.tube c) (k := 𝒰.cover.assign c i) ?_
  refine Finset.mem_image_of_mem _ ?_
  simp only [Tube.coverClass, Finset.mem_filter]
  exact ⟨hi, trivial⟩

open scoped Classical in
/-- **Step 1 of the payload list, assembled**: A1 instantiated at the two-level density statistics
of every level pair, descended root-ward over the `L + 1` levels of the grid, on one retained
family — and the band is read **in the retained family**, which is the family the restricted tower
is built on.

* the pair `(p,c)` is flattened by putting the **coarse** index `p` on the descent (it is the
  index whose cell map moves) and the **fine** index `c` into `Fin (L+1)`, so the level's `n` is
  `L + 1` and the total loss is `((J+1)^{L+1})^{L+1}`, the source's
  `[K₀(2+2log₂Λ)^{K₀}]^{-(M+1)}` shape at `K₀ = 1`;
* the brackets are `1 ≤ · ≤ #u` (`one_le_levelDensityStat_of_mem`, `levelDensityStat_le_card`),
  so `J` is `exists_pow_two_bracket`'s ceiling for `#u` and no `δ`-power is spent below —
  `C₁ = 0`, as the bracket table records;
* the label is trivial here (`K₀ = 1`): the source's label rides on the *four* statistics, and the
  density row alone carries none.  `exists_multiLevel_band` keeps the slot open for the row that
  does.

**Family/shading:** the retained family `t ⊆ u`; no shading — the density statistic is a function
of tubes and cells only, and `Z → W` happens at the caller.  **Level pair:** every `(p,c)` with
both `≤ ssfGridLen δ`. -/
theorem exists_levelDensityStat_band (hδ : 0 < δ)
    (𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu) (hu : u.Nonempty) :
    ∃ (t : Finset ι) (J : ℕ), t ⊆ u ∧ t.Nonempty ∧
      u.card ≤ ((J + 1) ^ (Tube.ssfGridLen δ + 1)) ^ (Tube.ssfGridLen δ + 1) * t.card ∧
      ∃ Φ : ℕ → ℕ → ENNReal, ∀ p ≤ Tube.ssfGridLen δ, ∀ c ≤ Tube.ssfGridLen δ, ∀ k ∈ t,
        Φ p c ≤ levelDensityStat 𝒰 p c t k ∧ levelDensityStat 𝒰 p c t k ≤ 2 * Φ p c := by
  classical
  obtain ⟨J, hJ⟩ := exists_pow_two_bracket (lo := (1 : ENNReal)) (hi := (u.card : ENNReal))
    one_ne_zero (by simp)
  have hcard : ∀ (w : Finset ι), w ⊆ u → ∀ (p c : ℕ) (i : ι),
      levelDensityStat 𝒰 p c w i ≤ 2 ^ J * (1 : ENNReal) := by
    intro w hw p c i
    refine le_trans (levelDensityStat_le_card 𝒰 p c w i) (le_trans ?_ hJ)
    exact_mod_cast Finset.card_le_card hw
  obtain ⟨t, hts, htne, htcard, -, Φ, hΦ⟩ :=
    exists_multiLevel_band (n := (Tube.ssfGridLen δ) + 1) (γ := ι) u hu
      (fun p => 𝒰.cover.assign ((Tube.ssfGridLen δ) - p))
      (fun p q hpq i hi j hj h =>
        𝒰.cover.assign_eq_of_le (by omega) (Nat.sub_le _ _) hi hj h)
      (fun p q w i => levelDensityStat 𝒰 ((Tube.ssfGridLen δ) - p) (q : ℕ) w i)
      (fun p q => leafLocal_levelDensityStat 𝒰 ((Tube.ssfGridLen δ) - p) (q : ℕ))
      (fun p q w i =>
        dyadicScaleBucket 1 (levelDensityStat 𝒰 ((Tube.ssfGridLen δ) - p) (q : ℕ) w i))
      (fun p q w i j h => by
        rw [levelDensityStat_congr_cell 𝒰 ((Tube.ssfGridLen δ) - p) (q : ℕ) w h])
      (J + 1) (Nat.succ_pos J)
      (fun p q w hw i _ =>
        dyadicScaleBucket_lt_succ (hcard w hw ((Tube.ssfGridLen δ) - p) (q : ℕ) i))
      (fun p q w hw i hi j hj hbeq =>
        le_two_mul_of_dyadicScaleBucket_eq ⟨J, hcard w hw ((Tube.ssfGridLen δ) - p) (q : ℕ) i⟩
          ⟨J, hcard w hw ((Tube.ssfGridLen δ) - p) (q : ℕ) j⟩
          (one_le_levelDensityStat_of_mem hδ 𝒰 ((Tube.ssfGridLen δ) - p) (q : ℕ) hi) hbeq)
      (fun _ _ => 0) 1 (fun _ _ _ => Nat.zero_lt_one) (fun _ _ _ _ => rfl) (Tube.ssfGridLen δ)
  refine ⟨t, J, hts, htne, ?_,
    fun p c => Φ ((Tube.ssfGridLen δ) - p) ⟨min c (Tube.ssfGridLen δ), by omega⟩, ?_⟩
  · simpa using htcard
  · intro p hp c hc k hk
    have hpp : (Tube.ssfGridLen δ) - ((Tube.ssfGridLen δ) - p) = p := Nat.sub_sub_self hp
    have hmin : min c (Tube.ssfGridLen δ) = c := min_eq_left hc
    have := hΦ ((Tube.ssfGridLen δ) - p) (Nat.sub_le _ _) ⟨min c (Tube.ssfGridLen δ), by omega⟩ k hk
    simpa [hmin, hpp] using this



open scoped Classical in
/-- **The class-count statistic** — `#(𝕋_k⟨T_k(i)⟩)`, the size of the level-`k` class of the leaf
`i`, read in the family `v`.  It is `Tube.coverClass` itself, so it is **leaf-local by definition**,
exactly like the two-level density; that is what lets it ride in A1's joint bin rather than needing
a second pigeonhole pass of its own. -/
noncomputable def classCountStat (𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu)
    (k : ℕ) (v : Finset ι) (i : ι) : ENNReal :=
  ((Tube.coverClass v (𝒰.cover.assign k) (𝒰.cover.assign k i)).card : ENNReal)

open scoped Classical in
/-- **Leaf-locality of the class count**, three lines by definition of `Tube.coverClass`. -/
theorem leafLocal_classCountStat [DecidableEq ι]
    (𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu) (k : ℕ) :
    LeafLocalStat (𝒰.cover.assign k) (classCountStat 𝒰 k) := by
  intro v w i h
  simp only [classCountStat]
  rw [coverClass_eq_filter, coverClass_eq_filter, h]

open scoped Classical in
/-- **The class count is a function of the leaf's cell**, so its dyadic bucket is
cell-determined. -/
theorem classCountStat_congr_cell (𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu)
    (k : ℕ) (v : Finset ι) {i j : ι} (h : 𝒰.cover.assign k i = 𝒰.cover.assign k j) :
    classCountStat 𝒰 k v i = classCountStat 𝒰 k v j := by
  simp only [classCountStat, h]

open scoped Classical in
/-- **The class count's brackets are the density row's**: `1` below (the class holds its own leaf)
and `#v` above.  No `δ`-power either way, so the fifth statistic costs one more factor `(J+1)` per
level and nothing in any exponent account. -/
theorem one_le_classCountStat (𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu)
    (k : ℕ) {v : Finset ι} {i : ι} (hi : i ∈ v) : 1 ≤ classCountStat 𝒰 k v i := by
  classical
  have hne : i ∈ Tube.coverClass v (𝒰.cover.assign k) (𝒰.cover.assign k i) := by
    simp only [Tube.coverClass, Finset.mem_filter]
    exact ⟨hi, trivial⟩
  have := Finset.card_pos.mpr ⟨_, hne⟩
  simp only [classCountStat]
  exact_mod_cast this

open scoped Classical in
/-- The class count in a subfamily is at most the subfamily's size. -/
theorem classCountStat_le_card (𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu)
    (k : ℕ) (v : Finset ι) (i : ι) : classCountStat 𝒰 k v i ≤ (v.card : ENNReal) := by
  classical
  have : (Tube.coverClass v (𝒰.cover.assign k) (𝒰.cover.assign k i)).card ≤ v.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  simp only [classCountStat]
  exact_mod_cast this


/-! ### The remaining two of l.4032-4035's four statistics

: the tree carries **two** of the source's four statistics, in two different
places and two different roles — the two-level maximal densities as the *field*
`IsKatzTaoDividingWindowLevels.level_density_band`, and the descendant counts as the *hypothesis*
`Kakeya.ML2Core.IsClassHomogeneousOn`.  The two missing are the **two-level counts** and the
**fibre shaded masses**, and `SRC-A′`'s residue is exactly those two.  Both are leaf-local,
cell-determined statistics with `δ`-free-shaped brackets, so both fall out of the same joint bin.

The fibre shaded mass is the **one statistic that carries the shading**, and it is the weight that
makes the source's retention true (l.4056-4058: the refinement retains `Λ_f^{-1}` of the *mass*).
-/

open scoped Classical in
/-- The two-level count is a function of the leaf's cell, like the density. -/
theorem levelCountStat_congr_cell (𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu)
    (p c : ℕ) (w : Finset ι) {i j : ι} (h : 𝒰.cover.assign p i = 𝒰.cover.assign p j) :
    levelCountStat 𝒰 p c w i = levelCountStat 𝒰 p c w j := by
  simp only [levelCountStat, h]

open scoped Classical in
/-- The two-level count in a subfamily is at most the subfamily's size. -/
theorem levelCountStat_le_card (𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu)
    (p c : ℕ) (w : Finset ι) (i : ι) : levelCountStat 𝒰 p c w i ≤ (w.card : ENNReal) := by
  classical
  have h1 : ((Tube.coverClass w (𝒰.cover.assign p) (𝒰.cover.assign p i)).image
      (𝒰.cover.assign c)).card ≤ w.card :=
    le_trans Finset.card_image_le (Finset.card_le_card (Finset.filter_subset _ _))
  simp only [levelCountStat]
  exact_mod_cast h1

open scoped Classical in
/-- **The fibre shaded mass** (l.4030-4031, l.4034): the total shaded volume of the thread cell of
the leaf `i` at level `k`, read in the family `w`.  **This is the one statistic that carries the
shading `Z`**, and it is the weight the source's refinement retains. -/
noncomputable def fibreShadedMassStat (𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu)
    (Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (k : ℕ) (w : Finset ι) (i : ι) : ENNReal :=
  ∑ j ∈ Tube.coverClass w (𝒰.cover.assign k) (𝒰.cover.assign k i),
    MeasureTheory.volume (Z j).shade

open scoped Classical in
/-- **Leaf-locality of the fibre shaded mass** — the same three lines as the density's, because the
sum is over `Tube.coverClass` and nothing else. -/
theorem leafLocal_fibreShadedMassStat [DecidableEq ι]
    (𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu)
    (Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (k : ℕ) :
    LeafLocalStat (𝒰.cover.assign k) (fibreShadedMassStat 𝒰 Z k) := by
  intro v w i h
  simp only [fibreShadedMassStat]
  rw [coverClass_eq_filter, coverClass_eq_filter, h]

open scoped Classical in
/-- The fibre shaded mass is a function of the leaf's cell. -/
theorem fibreShadedMassStat_congr_cell (𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu)
    (Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (k : ℕ) (w : Finset ι) {i j : ι}
    (h : 𝒰.cover.assign k i = 𝒰.cover.assign k j) :
    fibreShadedMassStat 𝒰 Z k w i = fibreShadedMassStat 𝒰 Z k w j := by
  simp only [fibreShadedMassStat, h]

open scoped Classical in
/-- **The upper bracket for the mass row is the total mass**, trivially. -/
theorem fibreShadedMassStat_le_total (𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu)
    (Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (k : ℕ) {w : Finset ι} (hw : w ⊆ u)
    (i : ι) :
    fibreShadedMassStat 𝒰 Z k w i ≤ ∑ j ∈ u, MeasureTheory.volume (Z j).shade := by
  classical
  refine Finset.sum_le_sum_of_subset ?_
  exact (Finset.filter_subset _ _).trans hw

open scoped Classical in
/-- **The total shaded mass is finite** — every shade sits inside a compact carrier, so no
finiteness hypothesis is needed for the mass row's bracket. -/
theorem sum_volume_shade_ne_top (Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
    (w : Finset ι) : (∑ j ∈ w, MeasureTheory.volume (Z j).shade) ≠ ⊤ := by
  classical
  refine (ENNReal.sum_lt_top.mpr fun j _ => ?_).ne
  refine lt_of_le_of_lt (MeasureTheory.measure_mono (Z j).shade_subset) ?_
  exact ((Z j).toConvexSpaceBody.isCompact.measure_ne_top).lt_top

open scoped Classical in
/-- **The lower bracket for the mass row** comes from the leaf's own shade: the cell contains `i`,
so a per-tube shade floor is a cell-mass floor.  A `HasDenseShading` hypothesis supplies exactly
such a floor, which is why no new source hypothesis is spent here. -/
theorem le_fibreShadedMassStat (𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu)
    (Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (k : ℕ) {w : Finset ι} {i : ι} (hi : i ∈ w) :
    MeasureTheory.volume (Z i).shade ≤ fibreShadedMassStat 𝒰 Z k w i := by
  classical
  refine Finset.single_le_sum (f := fun j => MeasureTheory.volume (Z j).shade)
    (fun _ _ => bot_le) ?_
  simp only [Tube.coverClass, Finset.mem_filter]
  exact ⟨hi, trivial⟩


open scoped Classical in
/-- **The class-count band *is* class homogeneity** : Def 2.1(iii)'s
descendant-count band `D_k ≤ #𝕋⟨S⟩ < 2 D_k` (l.227-228) is what
`Kakeya.ML2Core.IsClassHomogeneousOn` renders, so once the class count rides in A1's joint bin the
homogeneity is *read off* rather than re-derived by a second pass -- which  rules out as
unsound unless whole-fibre.

`bN k` is taken to be an actual class cardinality (the class of a fixed retained leaf), so no
`ENNReal`-to-`NNReal` choice is made.  `2 ≤ Cu` is where A1's factor two is paid into the tower's
own constant: `δ`-free, and it enters no exponent account. -/
theorem isClassHomogeneousOn_of_classCountBand (hCu : 2 ≤ Cu)
    (𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu) {t : Finset ι} {i₀ : ι} (hi₀ : i₀ ∈ t)
    {Ψ : ℕ → ENNReal}
    (hband : ∀ k ≤ Tube.ssfGridLen δ, ∀ i ∈ t,
      Ψ k ≤ classCountStat 𝒰 k t i ∧ classCountStat 𝒰 k t i ≤ 2 * Ψ k) :
    IsClassHomogeneousOn 𝒰 t := by
  classical
  refine ⟨fun k => ((Tube.coverClass t (𝒰.cover.assign k) (𝒰.cover.assign k i₀)).card : NNReal),
    fun k hk j hj => ?_⟩
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
  have hbi := hband k hk i hi
  have hbi₀ := hband k hk i₀ hi₀
  have h1 : classCountStat 𝒰 k t i ≤ 2 * classCountStat 𝒰 k t i₀ :=
    hbi.2.trans (mul_le_mul' le_rfl hbi₀.1)
  have h2 : classCountStat 𝒰 k t i₀ ≤ 2 * classCountStat 𝒰 k t i :=
    hbi₀.2.trans (mul_le_mul' le_rfl hbi.1)
  simp only [classCountStat] at h1 h2
  have h1' : (Tube.coverClass t (𝒰.cover.assign k) (𝒰.cover.assign k i)).card
      ≤ 2 * (Tube.coverClass t (𝒰.cover.assign k) (𝒰.cover.assign k i₀)).card := by
    exact_mod_cast h1
  have h2' : (Tube.coverClass t (𝒰.cover.assign k) (𝒰.cover.assign k i₀)).card
      ≤ 2 * (Tube.coverClass t (𝒰.cover.assign k) (𝒰.cover.assign k i)).card := by
    exact_mod_cast h2
  constructor
  · calc ((Tube.coverClass t (𝒰.cover.assign k) (𝒰.cover.assign k i)).card : NNReal)
        ≤ ((2 * (Tube.coverClass t (𝒰.cover.assign k) (𝒰.cover.assign k i₀)).card : ℕ) : NNReal) :=
          by exact_mod_cast h1'
      _ = 2 * ((Tube.coverClass t (𝒰.cover.assign k) (𝒰.cover.assign k i₀)).card : NNReal) := by
          push_cast; ring
      _ ≤ Cu * ((Tube.coverClass t (𝒰.cover.assign k) (𝒰.cover.assign k i₀)).card : NNReal) := by
          gcongr
  · calc ((Tube.coverClass t (𝒰.cover.assign k) (𝒰.cover.assign k i₀)).card : NNReal)
        ≤ ((2 * (Tube.coverClass t (𝒰.cover.assign k) (𝒰.cover.assign k i)).card : ℕ) : NNReal) :=
          by exact_mod_cast h2'
      _ = 2 * ((Tube.coverClass t (𝒰.cover.assign k) (𝒰.cover.assign k i)).card : NNReal) := by
          push_cast; ring
      _ ≤ Cu * ((Tube.coverClass t (𝒰.cover.assign k) (𝒰.cover.assign k i)).card : NNReal) := by
          gcongr

open scoped Classical in
/-- **Route (b), : one joint pass delivers the band *and* class homogeneity.**

's question, answered by measurement.  `Kakeya.ML2Core.IsClassHomogeneousOn` is
a two-sided band on class **cardinalities** at every level, and the class cardinality is a
leaf-local, cell-determined statistic of exactly the kind A1's bin already regularizes.  So it rides
in the **same** joint vector bin as a fifth row (the source lists its four statistics together,
l.4032-4035) instead of being a second restriction — which matters, because a second restriction
that is not whole-fibre would move the density statistics and destroy the band this same theorem
produces.

Cost: one extra factor `(J+1)` per level, `((J+1)^{L+2})^{L+1}` against `((J+1)^{L+1})^{L+1}`.  Both
`δ`-free in the sense that `J` is fixed by `#u` and no `δ`-power is spent in either bracket.

`hCu : 2 ≤ Cu` is where A1's factor two is paid into the tower's own constant: the band gives the
two class sizes within a factor `2` of each other, and `IsClassHomogeneousOn` asks for `Cu`.  It is
a `δ`-free constant condition, not an exponent condition.

**Family/shading:** the retained family `t ⊆ u`; no shading.  **Level pair:** every `(p,c)` for the
band, every `k` for the homogeneity. -/
theorem exists_levelBand_classHomogeneous (hδ : 0 < δ) (hCu : 2 ≤ Cu)
    (𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu) (hu : u.Nonempty) :
    ∃ (t : Finset ι) (J : ℕ), t ⊆ u ∧ t.Nonempty ∧
      u.card ≤ ((J + 1) ^ (Tube.ssfGridLen δ + 2)) ^ (Tube.ssfGridLen δ + 1) * t.card ∧
      IsClassHomogeneousOn 𝒰 t ∧
      ∃ Φ : ℕ → ℕ → ENNReal, ∀ p ≤ Tube.ssfGridLen δ, ∀ c ≤ Tube.ssfGridLen δ, ∀ k ∈ t,
        Φ p c ≤ levelDensityStat 𝒰 p c t k ∧ levelDensityStat 𝒰 p c t k ≤ 2 * Φ p c := by
  classical
  obtain ⟨J, hJ⟩ := exists_pow_two_bracket (lo := (1 : ENNReal)) (hi := (u.card : ENNReal))
    one_ne_zero (by simp)
  set D : ℕ → Fin (Tube.ssfGridLen δ + 2) → Finset ι → ι → ENNReal :=
    fun p q w i =>
      if (q : ℕ) < Tube.ssfGridLen δ + 1 then
        levelDensityStat 𝒰 (Tube.ssfGridLen δ - p) (q : ℕ) w i
      else classCountStat 𝒰 (Tube.ssfGridLen δ - p) w i with hD
  have hDlo : ∀ (p : ℕ) (q : Fin (Tube.ssfGridLen δ + 2)) (w : Finset ι), ∀ i ∈ w,
      1 ≤ D p q w i := by
    intro p q w i hi
    rw [hD]
    by_cases hq : (q : ℕ) < Tube.ssfGridLen δ + 1
    · simpa [hq] using one_le_levelDensityStat_of_mem hδ 𝒰 (Tube.ssfGridLen δ - p) (q : ℕ) hi
    · simpa [hq] using one_le_classCountStat 𝒰 (Tube.ssfGridLen δ - p) hi
  have hDhi : ∀ (p : ℕ) (q : Fin (Tube.ssfGridLen δ + 2)), ∀ w ⊆ u, ∀ i : ι,
      D p q w i ≤ 2 ^ J * (1 : ENNReal) := by
    intro p q w hw i
    have hcast : (w.card : ENNReal) ≤ 2 ^ J * (1 : ENNReal) := by
      refine le_trans ?_ hJ
      exact_mod_cast Finset.card_le_card hw
    rw [hD]
    by_cases hq : (q : ℕ) < Tube.ssfGridLen δ + 1
    · simp only [hq, if_true]
      exact (levelDensityStat_le_card 𝒰 _ _ w i).trans hcast
    · simp only [hq, if_false]
      exact (classCountStat_le_card 𝒰 _ w i).trans hcast
  obtain ⟨t, hts, htne, htcard, -, Φ, hΦ⟩ :=
    exists_multiLevel_band (n := Tube.ssfGridLen δ + 2) (γ := ι) u hu
      (fun p => 𝒰.cover.assign (Tube.ssfGridLen δ - p))
      (fun p q hpq i hi j hj h =>
        𝒰.cover.assign_eq_of_le (by omega) (Nat.sub_le _ _) hi hj h)
      D
      (fun p q => by
        rw [hD]
        by_cases hq : (q : ℕ) < Tube.ssfGridLen δ + 1
        · simpa [hq] using leafLocal_levelDensityStat 𝒰 (Tube.ssfGridLen δ - p) (q : ℕ)
        · simpa [hq] using leafLocal_classCountStat 𝒰 (Tube.ssfGridLen δ - p))
      (fun p q w i => dyadicScaleBucket 1 (D p q w i))
      (fun p q w i j h => by
        have : D p q w i = D p q w j := by
          rw [hD]
          by_cases hq : (q : ℕ) < Tube.ssfGridLen δ + 1
          · simp only [hq, if_true]
            exact levelDensityStat_congr_cell 𝒰 _ (q : ℕ) w h
          · simp only [hq, if_false]
            exact classCountStat_congr_cell 𝒰 _ w h
        rw [this])
      (J + 1) (Nat.succ_pos J)
      (fun p q w hw i _ => dyadicScaleBucket_lt_succ (hDhi p q w hw i))
      (fun p q w hw i hi j hj hbeq =>
        le_two_mul_of_dyadicScaleBucket_eq ⟨J, hDhi p q w hw i⟩ ⟨J, hDhi p q w hw j⟩
          (hDlo p q w i hi) hbeq)
      (fun _ _ => 0) 1 (fun _ _ _ => Nat.zero_lt_one) (fun _ _ _ _ => rfl) (Tube.ssfGridLen δ)
  obtain ⟨i₀, hi₀⟩ := htne
  refine ⟨t, J, hts, ⟨i₀, hi₀⟩, by simpa using htcard, ?_, ?_⟩
  · -- class homogeneity, read off the class-count row 
    refine isClassHomogeneousOn_of_classCountBand hCu 𝒰 hi₀
      (Ψ := fun k => Φ (Tube.ssfGridLen δ - k) (Fin.last (Tube.ssfGridLen δ + 1)))
      (fun k hk i hi => ?_)
    have hlast : ¬ ((Fin.last (Tube.ssfGridLen δ + 1) : Fin (Tube.ssfGridLen δ + 2)) : ℕ)
        < Tube.ssfGridLen δ + 1 := by simp
    have hkk : Tube.ssfGridLen δ - (Tube.ssfGridLen δ - k) = k := Nat.sub_sub_self hk
    have hb := hΦ (Tube.ssfGridLen δ - k) (Nat.sub_le _ _)
      (Fin.last (Tube.ssfGridLen δ + 1)) i hi
    rw [hD] at hb
    simpa only [hlast, if_false, hkk] using hb
  · -- the density band, at the rows `q ≤ L`
    refine ⟨fun p c => Φ (Tube.ssfGridLen δ - p) ⟨min c (Tube.ssfGridLen δ), by omega⟩, ?_⟩
    intro p hp c hc k hk
    have hpp : Tube.ssfGridLen δ - (Tube.ssfGridLen δ - p) = p := Nat.sub_sub_self hp
    have hmin : min c (Tube.ssfGridLen δ) = c := min_eq_left hc
    have hq : (min c (Tube.ssfGridLen δ)) < Tube.ssfGridLen δ + 1 := by omega
    have := hΦ (Tube.ssfGridLen δ - p) (Nat.sub_le _ _)
      ⟨min c (Tube.ssfGridLen δ), by omega⟩ k hk
    rw [hD] at this
    simpa [hq, hmin, hpp, hc] using this



/-! ### The mass-weighted descent (l.4056-4058: the refinement retains a share of the **mass**)

The source's refinement retains `Λ_f^{-1}` of the *shaded mass*, not of the node count
(l.4056-4058), and `Kakeya.ML2Core.IsShadedRefinementOf`'s fifth clause is exactly that inequality.
The card-based pigeonholes above give a node fraction; these siblings give the mass fraction
directly, by choosing at each bucketing the bucket of **largest weight** rather than of largest
cardinality.  Nothing above is edited: the two runs are different pigeonholes and each is correct
for its own retention.

The weight is arbitrary and additive, so the same devices serve any of the source's weights; the
mass instance takes `wt i = |Z(i)|`.
-/

open scoped Classical in
/-- **The bin-to-band pigeonhole, weighted.**  Same statement as `exists_bucket_band_fibre` with the
cardinality replaced by an additive weight: one bucket carries a `1/L` share of the **weight**, its
statistics are pinned to a profile within a factor two, and it is a union of whole cells. -/
theorem exists_bucket_band_fibre_wt {κ : Type*} (cell : κ → γ) (K : Finset κ)
    (wt : κ → ENNReal) (hwt : (∑ k ∈ K, wt k) ≠ 0)
    (D : κ → ENNReal) (bucket : κ → ℕ) (L : ℕ) (hL : 0 < L)
    (hbc : ∀ k k', cell k = cell k' → bucket k = bucket k')
    (hb : ∀ k ∈ K, ∀ k' ∈ K, bucket k = bucket k' → D k' ≤ 2 * D k)
    (hLlt : ∀ k ∈ K, bucket k < L) :
    ∃ K' : Finset κ, K' ⊆ K ∧ K'.Nonempty ∧ (∑ k ∈ K, wt k) ≤ L * ∑ k ∈ K', wt k ∧
      WholeFibreSubset cell K' K ∧
      ∃ Φ : ENNReal, ∀ k ∈ K', Φ ≤ D k ∧ D k ≤ 2 * Φ := by
  classical
  have hne : (Finset.range L).Nonempty := Finset.nonempty_range_iff.mpr hL.ne'
  set fib : ℕ → ENNReal := fun v => ∑ k ∈ K.filter (fun k => bucket k = v), wt k with hfib
  obtain ⟨v, -, hv⟩ := Finset.exists_max_image (Finset.range L) fib hne
  have hmaps : ∀ k ∈ K, bucket k ∈ Finset.range L := fun k hk => Finset.mem_range.mpr (hLlt k hk)
  have hsum : ∑ v ∈ Finset.range L, fib v = ∑ k ∈ K, wt k :=
    Finset.sum_fiberwise_of_maps_to hmaps wt
  have hle : (∑ k ∈ K, wt k) ≤ L * fib v := by
    rw [← hsum]
    calc ∑ v' ∈ Finset.range L, fib v' ≤ ∑ _v' ∈ Finset.range L, fib v :=
          Finset.sum_le_sum (fun v' hv' => hv v' hv')
      _ = (L : ENNReal) * fib v := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hfv : fib v ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hle
    exact hwt (le_antisymm hle bot_le)
  have hK'ne : (K.filter (fun k => bucket k = v)).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    exact hfv (by rw [hfib]; simp [hemp])
  refine ⟨K.filter (fun k => bucket k = v), Finset.filter_subset _ _, hK'ne, hle, ?_, ?_⟩
  · refine ⟨Finset.filter_subset _ _, fun i hi j hj hcell => ?_⟩
    refine Finset.mem_filter.mpr ⟨hj, ?_⟩
    rw [hbc j i hcell]
    exact (Finset.mem_filter.mp hi).2
  · refine ⟨(K.filter (fun k => bucket k = v)).inf' hK'ne D, fun k hk => ⟨?_, ?_⟩⟩
    · exact Finset.inf'_le D hk
    · obtain ⟨k₁, hk₁mem, hk₁eq⟩ := Finset.exists_mem_eq_inf' hK'ne D
      rw [hk₁eq]
      obtain ⟨hk₁K, hk₁v⟩ := Finset.mem_filter.mp hk₁mem
      obtain ⟨hkK, hkv⟩ := Finset.mem_filter.mp hk
      exact hb k₁ hk₁K k hkK (by rw [hk₁v, hkv])



open scoped Classical in
/-- **The label pigeonhole, weighted** — rider 1 on the mass side, same max-weight bucket. -/
theorem exists_constant_label_fibre_wt {κ : Type*} (cell : κ → γ) (K : Finset κ)
    (wt : κ → ENNReal) (hwt : (∑ k ∈ K, wt k) ≠ 0)
    (lab : κ → ℕ) (K₀ : ℕ) (hK₀ : 0 < K₀) (hlab : ∀ k ∈ K, lab k < K₀)
    (hlabc : ∀ k k', cell k = cell k' → lab k = lab k') :
    ∃ (w : ℕ) (K' : Finset κ), K' ⊆ K ∧ K'.Nonempty ∧
      (∑ k ∈ K, wt k) ≤ K₀ * ∑ k ∈ K', wt k ∧
      WholeFibreSubset cell K' K ∧ ∀ k ∈ K', lab k = w := by
  classical
  have hne : (Finset.range K₀).Nonempty := Finset.nonempty_range_iff.mpr hK₀.ne'
  set fib : ℕ → ENNReal := fun v => ∑ k ∈ K.filter (fun k => lab k = v), wt k with hfib
  obtain ⟨v, -, hv⟩ := Finset.exists_max_image (Finset.range K₀) fib hne
  have hmaps : ∀ k ∈ K, lab k ∈ Finset.range K₀ := fun k hk => Finset.mem_range.mpr (hlab k hk)
  have hsum : ∑ v ∈ Finset.range K₀, fib v = ∑ k ∈ K, wt k :=
    Finset.sum_fiberwise_of_maps_to hmaps wt
  have hle : (∑ k ∈ K, wt k) ≤ K₀ * fib v := by
    rw [← hsum]
    calc ∑ v' ∈ Finset.range K₀, fib v' ≤ ∑ _v' ∈ Finset.range K₀, fib v :=
          Finset.sum_le_sum (fun v' hv' => hv v' hv')
      _ = (K₀ : ENNReal) * fib v := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hfv : fib v ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hle
    exact hwt (le_antisymm hle bot_le)
  have hK'ne : (K.filter (fun k => lab k = v)).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    exact hfv (by rw [hfib]; simp [hemp])
  refine ⟨v, K.filter (fun k => lab k = v), Finset.filter_subset _ _, hK'ne, hle, ?_,
    fun k hk => (Finset.mem_filter.mp hk).2⟩
  refine ⟨Finset.filter_subset _ _, fun i hi j hj hcell => ?_⟩
  refine Finset.mem_filter.mpr ⟨hj, ?_⟩
  rw [hlabc j i hcell]
  exact (Finset.mem_filter.mp hi).2

open scoped Classical in
/-- **The joint single-bin band, weighted**: `n` statistics at once, weight loss `L ^ n`, retained
set a union of whole cells. -/
theorem exists_joint_bucket_band_fibre_wt {κ : Type*} (cell : κ → γ) (wt : κ → ENNReal) :
    ∀ (n : ℕ) (K : Finset κ), (∑ k ∈ K, wt k) ≠ 0 →
      ∀ (D : Fin n → κ → ENNReal) (bucket : Fin n → κ → ℕ) (L : ℕ), 0 < L →
      (∀ q : Fin n, ∀ k k', cell k = cell k' → bucket q k = bucket q k') →
      (∀ q : Fin n, ∀ k ∈ K, ∀ k' ∈ K, bucket q k = bucket q k' → D q k' ≤ 2 * D q k) →
      (∀ q : Fin n, ∀ k ∈ K, bucket q k < L) →
      ∃ K' : Finset κ, K' ⊆ K ∧ K'.Nonempty ∧
        (∑ k ∈ K, wt k) ≤ (L : ENNReal) ^ n * ∑ k ∈ K', wt k ∧
        WholeFibreSubset cell K' K ∧
        ∃ Φ : Fin n → ENNReal, ∀ q : Fin n, ∀ k ∈ K', Φ q ≤ D q k ∧ D q k ≤ 2 * Φ q := by
  intro n
  induction n with
  | zero =>
      intro K hK D bucket L hL _ _ _
      refine ⟨K, Finset.Subset.refl K, ?_, by simp,
        ⟨Finset.Subset.refl K, fun _ _ j hj _ => hj⟩, Fin.elim0, fun q => q.elim0⟩
      by_contra hemp
      rw [Finset.not_nonempty_iff_eq_empty] at hemp
      exact hK (by simp [hemp])
  | succ n ih =>
      intro K hK D bucket L hL hbc hb hLlt
      obtain ⟨K₁, hK₁sub, hK₁ne, hK₁wt, hK₁wf, Φlast, hΦlast⟩ :=
        exists_bucket_band_fibre_wt cell K wt hK (D (Fin.last n)) (bucket (Fin.last n)) L hL
          (hbc (Fin.last n)) (hb (Fin.last n)) (hLlt (Fin.last n))
      have hK₁ : (∑ k ∈ K₁, wt k) ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hK₁wt
        exact hK (le_antisymm hK₁wt bot_le)
      obtain ⟨K₂, hK₂sub, hK₂ne, hK₂wt, hK₂wf, Φ, hΦ⟩ :=
        ih K₁ hK₁ (fun q => D q.castSucc) (fun q => bucket q.castSucc) L hL
          (fun q => hbc q.castSucc)
          (fun q k hk k' hk' h => hb q.castSucc k (hK₁sub hk) k' (hK₁sub hk') h)
          (fun q k hk => hLlt q.castSucc k (hK₁sub hk))
      refine ⟨K₂, hK₂sub.trans hK₁sub, hK₂ne, ?_, hK₂wf.trans hK₁wf, Fin.snoc Φ Φlast, ?_⟩
      · calc (∑ k ∈ K, wt k) ≤ (L : ENNReal) * ∑ k ∈ K₁, wt k := hK₁wt
          _ ≤ (L : ENNReal) * ((L : ENNReal) ^ n * ∑ k ∈ K₂, wt k) :=
              mul_le_mul' le_rfl hK₂wt
          _ = (L : ENNReal) ^ (n + 1) * ∑ k ∈ K₂, wt k := by ring
      · intro q k hk
        refine Fin.lastCases ?_ ?_ q
        · simpa using hΦlast k (hK₂sub hk)
        · intro q'
          simpa using hΦ q' k hk

open scoped Classical in
/-- **One level of the weighted descent** — the mass analogue of `exists_level_band_step`. -/
theorem exists_level_band_step_wt {n : ℕ} (cell : ι → γ) (v : Finset ι) (wt : ι → ENNReal)
    (hwt : (∑ k ∈ v, wt k) ≠ 0)
    (D : Fin n → ι → ENNReal) (bucket : Fin n → ι → ℕ) (L : ℕ) (hL : 0 < L)
    (hbc : ∀ q : Fin n, ∀ i j, cell i = cell j → bucket q i = bucket q j)
    (hpair : ∀ q : Fin n, ∀ i ∈ v, ∀ j ∈ v, bucket q i = bucket q j → D q j ≤ 2 * D q i)
    (hlt : ∀ q : Fin n, ∀ i ∈ v, bucket q i < L)
    (lab : ι → ℕ) (K₀ : ℕ) (hK₀0 : 0 < K₀) (hK₀ : ∀ i ∈ v, lab i < K₀)
    (hlabc : ∀ i j, cell i = cell j → lab i = lab j) :
    ∃ t : Finset ι, t ⊆ v ∧ t.Nonempty ∧
      (∑ k ∈ v, wt k) ≤ (K₀ : ENNReal) * (L : ENNReal) ^ n * ∑ k ∈ t, wt k ∧
      WholeFibreSubset cell t v ∧ (∃ w : ℕ, ∀ k ∈ t, lab k = w) ∧
      ∃ Φ : Fin n → ENNReal, ∀ q : Fin n, ∀ k ∈ t, Φ q ≤ D q k ∧ D q k ≤ 2 * Φ q := by
  obtain ⟨w, v₁, hv₁sub, hv₁ne, hv₁wt, hv₁wf, hv₁lab⟩ :=
    exists_constant_label_fibre_wt cell v wt hwt lab K₀ hK₀0 hK₀ hlabc
  have hv₁ : (∑ k ∈ v₁, wt k) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hv₁wt
    exact hwt (le_antisymm hv₁wt bot_le)
  obtain ⟨v₂, hv₂sub, hv₂ne, hv₂wt, hv₂wf, Φ, hΦ⟩ :=
    exists_joint_bucket_band_fibre_wt cell wt n v₁ hv₁ D bucket L hL hbc
      (fun q k hk k' hk' h => hpair q k (hv₁sub hk) k' (hv₁sub hk') h)
      (fun q k hk => hlt q k (hv₁sub hk))
  refine ⟨v₂, hv₂sub.trans hv₁sub, hv₂ne, ?_, hv₂wf.trans hv₁wf,
    ⟨w, fun k hk => hv₁lab k (hv₂sub hk)⟩, Φ, hΦ⟩
  calc (∑ k ∈ v, wt k) ≤ (K₀ : ENNReal) * ∑ k ∈ v₁, wt k := hv₁wt
    _ ≤ (K₀ : ENNReal) * ((L : ENNReal) ^ n * ∑ k ∈ v₂, wt k) := mul_le_mul' le_rfl hv₂wt
    _ = (K₀ : ENNReal) * (L : ENNReal) ^ n * ∑ k ∈ v₂, wt k := by ring

open scoped Classical in
/-- **The weighted descent** — `exists_multiLevel_band` with the node fraction replaced by the
**mass** fraction of l.4056-4058.  One retained family, all levels' bands, and
`∑_u wt ≤ (K₀ L^n)^{M+1} · ∑_t wt`: the shape `Kakeya.ML2Core.IsShadedRefinementOf`'s fifth clause
asks for, with `Λ` the loss. -/
theorem exists_multiLevel_band_wt [DecidableEq γ] {n : ℕ}
    (u : Finset ι) (wt : ι → ENNReal) (hwt : (∑ k ∈ u, wt k) ≠ 0) (g : ℕ → ι → γ)
    (hmono : ∀ p q : ℕ, p ≤ q → ∀ i ∈ u, ∀ j ∈ u, g p i = g p j → g q i = g q j)
    (D : ℕ → Fin n → Finset ι → ι → ENNReal)
    (hloc : ∀ (p : ℕ) (q : Fin n), LeafLocalStat (g p) (D p q))
    (bucket : ℕ → Fin n → Finset ι → ι → ℕ)
    (hbc : ∀ (p : ℕ) (q : Fin n) (w : Finset ι) (i j : ι),
      g p i = g p j → bucket p q w i = bucket p q w j)
    (L : ℕ) (hL : 0 < L)
    (hlt : ∀ (p : ℕ) (q : Fin n), ∀ w ⊆ u, ∀ i ∈ w, bucket p q w i < L)
    (hpair : ∀ (p : ℕ) (q : Fin n), ∀ w ⊆ u, ∀ i ∈ w, ∀ j ∈ w,
      bucket p q w i = bucket p q w j → D p q w j ≤ 2 * D p q w i)
    (lab : ℕ → ι → ℕ) (K₀ : ℕ) (hK₀0 : 0 < K₀) (hK₀ : ∀ p : ℕ, ∀ i ∈ u, lab p i < K₀)
    (hlabc : ∀ (p : ℕ) (i j : ι), g p i = g p j → lab p i = lab p j) :
    ∀ M : ℕ, ∃ t : Finset ι, t ⊆ u ∧ t.Nonempty ∧
      (∑ k ∈ u, wt k) ≤ ((K₀ : ENNReal) * (L : ENNReal) ^ n) ^ (M + 1) * ∑ k ∈ t, wt k ∧
      (∃ vl : ℕ → ℕ, ∀ p ≤ M, ∀ k ∈ t, lab p k = vl p) ∧
      ∃ Φ : ℕ → Fin n → ENNReal, ∀ p ≤ M, ∀ q : Fin n, ∀ k ∈ t,
        Φ p q ≤ D p q t k ∧ D p q t k ≤ 2 * Φ p q := by
  intro M
  induction M with
  | zero =>
      obtain ⟨t, hts, htne, htwt, htwf, ⟨w, hw⟩, Φ, hΦ⟩ :=
        exists_level_band_step_wt (n := n) (g 0) u wt hwt (fun q => D 0 q u)
          (fun q => bucket 0 q u) L hL (fun q => hbc 0 q u)
          (hpair 0 · u (Finset.Subset.refl u)) (hlt 0 · u (Finset.Subset.refl u))
          (lab 0) K₀ hK₀0 (hK₀ 0) (hlabc 0)
      refine ⟨t, hts, htne, by simpa using htwt, ⟨fun _ => w, fun p hp k hk => ?_⟩,
        fun _ q => Φ q, fun p hp q k hk => ?_⟩
      · rw [Nat.le_zero.mp hp]; exact hw k hk
      · rw [Nat.le_zero.mp hp, leafLocalStat_stable (hloc 0 q) htwf hk]
        exact hΦ q k hk
  | succ M ih =>
      obtain ⟨t₁, ht₁s, ht₁ne, ht₁wt, ⟨vl, hvl⟩, Φ₁, hΦ₁⟩ := ih
      have ht₁ : (∑ k ∈ t₁, wt k) ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at ht₁wt
        exact hwt (le_antisymm ht₁wt bot_le)
      obtain ⟨t₂, ht₂s, ht₂ne, ht₂wt, ht₂wf, ⟨w, hw⟩, Φ₂, hΦ₂⟩ :=
        exists_level_band_step_wt (n := n) (g (M + 1)) t₁ wt ht₁ (fun q => D (M + 1) q t₁)
          (fun q => bucket (M + 1) q t₁) L hL (fun q => hbc (M + 1) q t₁)
          (hpair (M + 1) · t₁ ht₁s) (hlt (M + 1) · t₁ ht₁s) (lab (M + 1)) K₀ hK₀0
          (fun i hi => hK₀ (M + 1) i (ht₁s hi)) (hlabc (M + 1))
      have hwfp : ∀ p ≤ M + 1, WholeFibreSubset (g p) t₂ t₁ := by
        intro p hp
        refine wholeFibreSubset_of_refines ht₂wf (fun i hi j hj hcell => ?_)
        exact hmono p (M + 1) hp j (ht₁s hj) i (ht₁s hi) hcell
      refine ⟨t₂, ht₂s.trans ht₁s, ht₂ne, ?_,
        ⟨fun p => if p = M + 1 then w else vl p, fun p hp k hk => ?_⟩,
        fun p => if p = M + 1 then Φ₂ else Φ₁ p, fun p hp q k hk => ?_⟩
      · calc (∑ k ∈ u, wt k)
            ≤ ((K₀ : ENNReal) * (L : ENNReal) ^ n) ^ (M + 1) * ∑ k ∈ t₁, wt k := ht₁wt
          _ ≤ ((K₀ : ENNReal) * (L : ENNReal) ^ n) ^ (M + 1)
                * ((K₀ : ENNReal) * (L : ENNReal) ^ n * ∑ k ∈ t₂, wt k) :=
              mul_le_mul' le_rfl ht₂wt
          _ = ((K₀ : ENNReal) * (L : ENNReal) ^ n) ^ (M + 1 + 1) * ∑ k ∈ t₂, wt k := by ring
      · dsimp only
        rcases Nat.lt_or_ge p (M + 1) with hlt' | hge
        · rw [if_neg (by omega)]
          exact hvl p (by omega) k (ht₂s hk)
        · have hpe : p = M + 1 := by omega
          subst hpe
          rw [if_pos rfl]
          exact hw k hk
      · dsimp only
        rcases Nat.lt_or_ge p (M + 1) with hlt' | hge
        · rw [if_neg (by omega : ¬ p = M + 1),
            leafLocalStat_stable (hloc p q) (hwfp p (by omega)) hk]
          exact hΦ₁ p (by omega) q k (ht₂s hk)
        · have hpe : p = M + 1 := by omega
          subst hpe
          rw [if_pos rfl, leafLocalStat_stable (hloc (M + 1) q) (hwfp (M + 1) le_rfl) hk]
          exact hΦ₂ q k hk

/-! ### The four statistics of l.4030-4035, in one joint bin -/

open scoped Classical in
/-- **The four statistics as one row vector**, flattened into `q < 2L+4`: the two-level densities
at `q ≤ L`, the two-level counts at `L+1 ≤ q ≤ 2L+1`, the descendant (class) count at `q = 2L+2`
and the fibre shaded mass at `q = 2L+3`.  All four share the level's cell map `𝒰.cover.assign k`,
which is why one joint bin regularises them together (l.4916-4917). -/
noncomputable def fourStatRow (𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu)
    (Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (k q : ℕ) (w : Finset ι) (i : ι) : ENNReal :=
  if q < Tube.ssfGridLen δ + 1 then levelDensityStat 𝒰 k q w i
  else if q < 2 * Tube.ssfGridLen δ + 2 then
    levelCountStat 𝒰 k (q - (Tube.ssfGridLen δ + 1)) w i
  else if q < 2 * Tube.ssfGridLen δ + 3 then classCountStat 𝒰 k w i
  else fibreShadedMassStat 𝒰 Z k w i

open scoped Classical in
/-- Each row of `fourStatRow` is leaf-local at the level's cell map — the four proofs are the same
three lines, by definition of `Tube.coverClass` (l.4917-4918). -/
theorem leafLocal_fourStatRow [DecidableEq ι]
    (𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu)
    (Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (k q : ℕ) :
    LeafLocalStat (𝒰.cover.assign k) (fourStatRow 𝒰 Z k q) := by
  intro v w i h
  simp only [fourStatRow]
  by_cases h1 : q < Tube.ssfGridLen δ + 1
  · simp only [if_pos h1]
    exact leafLocal_levelDensityStat 𝒰 k q v w i h
  · by_cases h2 : q < 2 * Tube.ssfGridLen δ + 2
    · simp only [if_neg h1, if_pos h2]
      exact leafLocal_levelCountStat 𝒰 k _ v w i h
    · by_cases h3 : q < 2 * Tube.ssfGridLen δ + 3
      · simp only [if_neg h1, if_neg h2, if_pos h3]
        exact leafLocal_classCountStat 𝒰 k v w i h
      · simp only [if_neg h1, if_neg h2, if_neg h3]
        exact leafLocal_fibreShadedMassStat 𝒰 Z k v w i h

open scoped Classical in
/-- Row extraction, `q ≤ L`: the two-level maximal density. -/
theorem fourStatRow_density (𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu)
    (Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (k : ℕ) {q : ℕ}
    (hq : q < Tube.ssfGridLen δ + 1) (w : Finset ι) (i : ι) :
    fourStatRow 𝒰 Z k q w i = levelDensityStat 𝒰 k q w i := by
  simp only [fourStatRow, if_pos hq]

open scoped Classical in
/-- Row extraction, `L+1 ≤ q ≤ 2L+1`: the two-level count. -/
theorem fourStatRow_count (𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu)
    (Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (k : ℕ) {q : ℕ}
    (h1 : ¬ q < Tube.ssfGridLen δ + 1) (h2 : q < 2 * Tube.ssfGridLen δ + 2)
    (w : Finset ι) (i : ι) :
    fourStatRow 𝒰 Z k q w i = levelCountStat 𝒰 k (q - (Tube.ssfGridLen δ + 1)) w i := by
  simp only [fourStatRow, if_neg h1, if_pos h2]

open scoped Classical in
/-- Row extraction, `q = 2L+2`: the descendant (class) count. -/
theorem fourStatRow_classCount (𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu)
    (Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (k : ℕ) (w : Finset ι) (i : ι) :
    fourStatRow 𝒰 Z k (2 * Tube.ssfGridLen δ + 2) w i = classCountStat 𝒰 k w i := by
  simp only [fourStatRow, if_neg (by omega : ¬ 2 * Tube.ssfGridLen δ + 2
      < Tube.ssfGridLen δ + 1),
    if_neg (by omega : ¬ 2 * Tube.ssfGridLen δ + 2 < 2 * Tube.ssfGridLen δ + 2),
    if_pos (by omega : 2 * Tube.ssfGridLen δ + 2 < 2 * Tube.ssfGridLen δ + 3)]

open scoped Classical in
/-- Row extraction, `q = 2L+3`: the fibre shaded mass — the row that carries `Z`. -/
theorem fourStatRow_mass (𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu)
    (Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (k : ℕ) (w : Finset ι) (i : ι) :
    fourStatRow 𝒰 Z k (2 * Tube.ssfGridLen δ + 3) w i = fibreShadedMassStat 𝒰 Z k w i := by
  simp only [fourStatRow, if_neg (by omega : ¬ 2 * Tube.ssfGridLen δ + 3
      < Tube.ssfGridLen δ + 1),
    if_neg (by omega : ¬ 2 * Tube.ssfGridLen δ + 3 < 2 * Tube.ssfGridLen δ + 2),
    if_neg (by omega : ¬ 2 * Tube.ssfGridLen δ + 3 < 2 * Tube.ssfGridLen δ + 3)]

open scoped Classical in
/-- Each row of `fourStatRow` is a function of the leaf's cell, so its dyadic bucket is
cell-determined and the retained set is a union of whole cells. -/
theorem fourStatRow_congr_cell (𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu)
    (Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (k q : ℕ) (w : Finset ι) {i j : ι}
    (h : 𝒰.cover.assign k i = 𝒰.cover.assign k j) :
    fourStatRow 𝒰 Z k q w i = fourStatRow 𝒰 Z k q w j := by
  simp only [fourStatRow]
  split
  · exact levelDensityStat_congr_cell 𝒰 k q w h
  · split
    · exact levelCountStat_congr_cell 𝒰 k _ w h
    · split
      · exact classCountStat_congr_cell 𝒰 k w h
      · exact fibreShadedMassStat_congr_cell 𝒰 Z k w h

open scoped Classical in
/-- **One upper bracket for all four rows**: family size plus total shaded mass, both finite.  The
rows have different natural ceilings, and taking their sum lets the whole vector run at a single
dyadic ceiling `J`, which is what `exists_multiLevel_band` asks for. -/
theorem fourStatRow_le (𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu)
    (Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (k q : ℕ) {w : Finset ι} (hw : w ⊆ u)
    (i : ι) :
    fourStatRow 𝒰 Z k q w i
      ≤ (u.card : ENNReal) + ∑ j ∈ u, MeasureTheory.volume (Z j).shade := by
  classical
  have hcard : (w.card : ENNReal) ≤ (u.card : ENNReal) := by
    exact_mod_cast Finset.card_le_card hw
  simp only [fourStatRow]
  split
  · exact ((levelDensityStat_le_card 𝒰 k q w i).trans hcard).trans le_self_add
  · split
    · exact ((levelCountStat_le_card 𝒰 k _ w i).trans hcard).trans le_self_add
    · split
      · exact ((classCountStat_le_card 𝒰 k w i).trans hcard).trans le_self_add
      · exact (fibreShadedMassStat_le_total 𝒰 Z k hw i).trans le_add_self

open scoped Classical in
/-- **One lower bracket for all four rows**: `min 1 m`, where `m` is a per-tube shade floor.  Three
rows are bounded below by `1` (`C₁ = 0`, no `δ`-power); only the mass row spends anything, and it
spends the caller's `m` — the source's `δ^{3η_f}`, which a `HasDenseShading` hypothesis already
supplies. -/
theorem le_fourStatRow (hδ : 0 < δ) (𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu)
    (Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) {m : ENNReal}
    (hm : ∀ i ∈ u, m ≤ MeasureTheory.volume (Z i).shade) (k q : ℕ) {w : Finset ι} (hw : w ⊆ u)
    {i : ι} (hi : i ∈ w) :
    min 1 m ≤ fourStatRow 𝒰 Z k q w i := by
  classical
  simp only [fourStatRow]
  split
  · exact (min_le_left _ _).trans (one_le_levelDensityStat_of_mem hδ 𝒰 k q hi)
  · split
    · exact (min_le_left _ _).trans (one_le_levelCountStat 𝒰 k _ hi)
    · split
      · exact (min_le_left _ _).trans (one_le_classCountStat 𝒰 k hi)
      · exact (min_le_right _ _).trans
          ((hm i (hw hi)).trans (le_fibreShadedMassStat 𝒰 Z k hi))

open scoped Classical in
/-- **The source's l.4030-4035 hypothesis, produced.**

One whole-fibre joint pass over the `L+1` levels returns a retained family on which **all four** of
the source's statistics -- two-level maximal densities, two-level counts, descendant counts and
fibre shaded masses -- are pairwise within a factor two at every level or pair of levels, *and*
which is class-homogeneous (descendant counts **are** Def 2.1(iii)'s class
band, so homogeneity is one of the four and not a second pass).

's correction, carried: the tree already holds two of the four, in two roles --
two-level maximal densities as the *field* `IsKatzTaoDividingWindowLevels.level_density_band`, and
descendant counts as the *hypothesis* `IsClassHomogeneousOn`.  `SRC-A′`'s residue is the other two,
and this theorem supplies them.

Loss `((J+1)^{2L+4})^{L+1}`, `J` fixed by `#u`, the total shaded mass and the shade floor `m` --
the only `δ`-power spent anywhere in the brackets is the caller's `m` on the mass row.

**Family/shading:** `u` refined to `t`; the shading `Z` enters through the mass row and **only**
there.  **Level pair:** every `(p,c)` for the two banded pairs, every `k` for the class count and
the mass. -/
theorem exists_levelBand_fourStatistics (hδ : 0 < δ) (hCu : 2 ≤ Cu)
    (𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu) (hu : u.Nonempty)
    (Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) {m : ENNReal} (hm0 : m ≠ 0)
    (hm : ∀ i ∈ u, m ≤ MeasureTheory.volume (Z i).shade) :
    ∃ (t : Finset ι) (J : ℕ), t ⊆ u ∧ t.Nonempty ∧
      u.card ≤ ((J + 1) ^ (2 * Tube.ssfGridLen δ + 4)) ^ (Tube.ssfGridLen δ + 1) * t.card ∧
      IsClassHomogeneousOn 𝒰 t ∧
      (∃ Φ : ℕ → ℕ → ENNReal, ∀ p ≤ Tube.ssfGridLen δ, ∀ c ≤ Tube.ssfGridLen δ, ∀ k ∈ t,
        Φ p c ≤ levelDensityStat 𝒰 p c t k ∧ levelDensityStat 𝒰 p c t k ≤ 2 * Φ p c) ∧
      (∃ Ψ : ℕ → ℕ → ENNReal, ∀ p ≤ Tube.ssfGridLen δ, ∀ c ≤ Tube.ssfGridLen δ, ∀ k ∈ t,
        Ψ p c ≤ levelCountStat 𝒰 p c t k ∧ levelCountStat 𝒰 p c t k ≤ 2 * Ψ p c) ∧
      (∃ Mm : ℕ → ENNReal, ∀ p ≤ Tube.ssfGridLen δ, ∀ k ∈ t,
        Mm p ≤ fibreShadedMassStat 𝒰 Z p t k ∧
          fibreShadedMassStat 𝒰 Z p t k ≤ 2 * Mm p) := by
  classical
  obtain ⟨J, hJ⟩ := exists_pow_two_bracket (lo := min 1 m)
    (hi := (u.card : ENNReal) + ∑ j ∈ u, MeasureTheory.volume (Z j).shade)
    (by simp [hm0]) (by simp [sum_volume_shade_ne_top Z u])
  have hhi : ∀ (p : ℕ) (q : Fin (2 * Tube.ssfGridLen δ + 4)), ∀ w ⊆ u, ∀ i : ι,
      fourStatRow 𝒰 Z (Tube.ssfGridLen δ - p) (q : ℕ) w i ≤ 2 ^ J * min 1 m :=
    fun p q w hw i => (fourStatRow_le 𝒰 Z _ _ hw i).trans hJ
  obtain ⟨t, hts, htne, htcard, -, Φ, hΦ⟩ :=
    exists_multiLevel_band (n := 2 * Tube.ssfGridLen δ + 4) (γ := ι) u hu
      (fun p => 𝒰.cover.assign (Tube.ssfGridLen δ - p))
      (fun p q hpq i hi j hj h =>
        𝒰.cover.assign_eq_of_le (by omega) (Nat.sub_le _ _) hi hj h)
      (fun p q w i => fourStatRow 𝒰 Z (Tube.ssfGridLen δ - p) (q : ℕ) w i)
      (fun p q => leafLocal_fourStatRow 𝒰 Z (Tube.ssfGridLen δ - p) (q : ℕ))
      (fun p q w i => dyadicScaleBucket (min 1 m)
        (fourStatRow 𝒰 Z (Tube.ssfGridLen δ - p) (q : ℕ) w i))
      (fun p q w i j h => by
        rw [fourStatRow_congr_cell 𝒰 Z (Tube.ssfGridLen δ - p) (q : ℕ) w h])
      (J + 1) (Nat.succ_pos J)
      (fun p q w hw i _ => dyadicScaleBucket_lt_succ (hhi p q w hw i))
      (fun p q w hw i hi j hj hbeq =>
        le_two_mul_of_dyadicScaleBucket_eq ⟨J, hhi p q w hw i⟩ ⟨J, hhi p q w hw j⟩
          (le_fourStatRow hδ 𝒰 Z hm _ _ hw hi) hbeq)
      (fun _ _ => 0) 1 (fun _ _ _ => Nat.zero_lt_one) (fun _ _ _ _ => rfl) (Tube.ssfGridLen δ)
  obtain ⟨i₀, hi₀⟩ := htne
  have hrow : ∀ (k : ℕ), k ≤ Tube.ssfGridLen δ →
      ∀ (q : Fin (2 * Tube.ssfGridLen δ + 4)), ∀ i ∈ t,
        Φ (Tube.ssfGridLen δ - k) q ≤ fourStatRow 𝒰 Z k (q : ℕ) t i ∧
          fourStatRow 𝒰 Z k (q : ℕ) t i ≤ 2 * Φ (Tube.ssfGridLen δ - k) q := by
    intro k hk q i hi
    have hkk : Tube.ssfGridLen δ - (Tube.ssfGridLen δ - k) = k := Nat.sub_sub_self hk
    have hb := hΦ (Tube.ssfGridLen δ - k) (Nat.sub_le _ _) q i hi
    rwa [hkk] at hb
  refine ⟨t, J, hts, ⟨i₀, hi₀⟩, by simpa using htcard, ?_, ?_, ?_, ?_⟩
  · refine isClassHomogeneousOn_of_classCountBand hCu 𝒰 hi₀
      (Ψ := fun k => Φ (Tube.ssfGridLen δ - k)
        ⟨2 * Tube.ssfGridLen δ + 2, by omega⟩) (fun k hk i hi => ?_)
    have hb := hrow k hk ⟨2 * Tube.ssfGridLen δ + 2, by omega⟩ i hi
    rwa [fourStatRow_classCount 𝒰 Z k t i] at hb
  · refine ⟨fun p c => Φ (Tube.ssfGridLen δ - p) ⟨min c (Tube.ssfGridLen δ), by omega⟩, ?_⟩
    intro p hp c hc k hk
    have hb := hrow p hp ⟨min c (Tube.ssfGridLen δ), by omega⟩ k hk
    rw [fourStatRow_density 𝒰 Z p (by omega : min c (Tube.ssfGridLen δ)
      < Tube.ssfGridLen δ + 1) t k] at hb
    have heq : levelDensityStat 𝒰 p (min c (Tube.ssfGridLen δ)) t k
        = levelDensityStat 𝒰 p c t k := by rw [min_eq_left hc]
    rwa [heq] at hb
  · refine ⟨fun p c => Φ (Tube.ssfGridLen δ - p)
      ⟨Tube.ssfGridLen δ + 1 + min c (Tube.ssfGridLen δ), by omega⟩, ?_⟩
    intro p hp c hc k hk
    have hb := hrow p hp ⟨Tube.ssfGridLen δ + 1 + min c (Tube.ssfGridLen δ), by omega⟩ k hk
    rw [fourStatRow_count 𝒰 Z p
      (by omega : ¬ Tube.ssfGridLen δ + 1 + min c (Tube.ssfGridLen δ) < Tube.ssfGridLen δ + 1)
      (by omega : Tube.ssfGridLen δ + 1 + min c (Tube.ssfGridLen δ)
        < 2 * Tube.ssfGridLen δ + 2) t k] at hb
    rwa [show Tube.ssfGridLen δ + 1 + min c (Tube.ssfGridLen δ) - (Tube.ssfGridLen δ + 1) = c from
      by have := min_eq_left hc; omega] at hb
  · refine ⟨fun p => Φ (Tube.ssfGridLen δ - p)
      ⟨2 * Tube.ssfGridLen δ + 3, by omega⟩, ?_⟩
    intro p hp k hk
    have hb := hrow p hp ⟨2 * Tube.ssfGridLen δ + 3, by omega⟩ k hk
    rwa [fourStatRow_mass 𝒰 Z p t k] at hb



open scoped Classical in
/-- **`Kakeya.ML2Core.IsShadedRefinementOf`, produced by one mass-weighted joint bin.**

All six conjuncts, from a single whole-fibre pass:

* `S' ⊆ S`, `S'.Nonempty` — the pass;
* same tubes and sub-shading — `W := Z`, so both are `rfl`/`subset_rfl`; the source's refinement of
  the *shading* is not needed for the retention, only the refinement of the *family*;
* the **mass retention** `∑_S |Z| ≤ Λ · ∑_{S'} |Z|` — the mass-weighted descent, which is why the
  pigeonhole is run on the weight rather than on the node count (l.4056-4058);
* `IsClassHomogeneousOn 𝒱 S'` — the descendant-count row of the same bin

and the four bands of l.4030-4035 come out alongside.  So the `(F)` branch's first two conjuncts
are no longer obligations: what remains of `Kakeya.ML2Core.RefinedFloorHypothesis` is the window on
`Kakeya.ML2Core.refinedHierarchy` and `Kakeya.ML2Core.FloorHypothesisAt` there.

`Λ = ((J+1)^{2L+4})^{L+1}` with `J` fixed by `#S`, the total shaded mass and the shade floor `m`.

**Family/shading:** `S` with shading `Z`, refined to `S'` with the **same** shading.
**Level pair:** every `(p,c)` for the two banded pairs, every `k` for the class count and mass. -/
theorem exists_shadedRefinement_of_joint_bin (hδ : 0 < δ) (hCu : 2 ≤ Cu)
    {S : Finset ι} (Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
    (𝒱 : Tube.UniformTubeSet S (fun i => (Z i).toTube) (Tube.ssfGridLen δ) Cu)
    (hS : S.Nonempty) {mfl : ENNReal} (hm0 : mfl ≠ 0)
    (hm : ∀ i ∈ S, mfl ≤ MeasureTheory.volume (Z i).shade) :
    ∃ (S' : Finset ι) (J : ℕ), S' ⊆ S ∧ S'.Nonempty ∧
      IsShadedRefinementOf 𝒱
        ((((J + 1 : ENNReal)) ^ (2 * Tube.ssfGridLen δ + 4)) ^ (Tube.ssfGridLen δ + 1))
        S Z S' Z ∧
      (∃ Φ : ℕ → ℕ → ENNReal, ∀ p ≤ Tube.ssfGridLen δ, ∀ c ≤ Tube.ssfGridLen δ, ∀ k ∈ S',
        Φ p c ≤ levelDensityStat 𝒱 p c S' k ∧ levelDensityStat 𝒱 p c S' k ≤ 2 * Φ p c) ∧
      (∃ Ψ : ℕ → ℕ → ENNReal, ∀ p ≤ Tube.ssfGridLen δ, ∀ c ≤ Tube.ssfGridLen δ, ∀ k ∈ S',
        Ψ p c ≤ levelCountStat 𝒱 p c S' k ∧ levelCountStat 𝒱 p c S' k ≤ 2 * Ψ p c) ∧
      (∃ Mm : ℕ → ENNReal, ∀ p ≤ Tube.ssfGridLen δ, ∀ k ∈ S',
        Mm p ≤ fibreShadedMassStat 𝒱 Z p S' k ∧
          fibreShadedMassStat 𝒱 Z p S' k ≤ 2 * Mm p) := by
  classical
  obtain ⟨i₀, hi₀⟩ := hS
  have hwt : (∑ k ∈ S, MeasureTheory.volume (Z k).shade) ≠ 0 := by
    intro h0
    refine hm0 (le_antisymm ?_ bot_le)
    calc mfl ≤ MeasureTheory.volume (Z i₀).shade := hm i₀ hi₀
      _ ≤ ∑ k ∈ S, MeasureTheory.volume (Z k).shade :=
          Finset.single_le_sum (f := fun j => MeasureTheory.volume (Z j).shade)
            (fun _ _ => bot_le) hi₀
      _ = 0 := h0
  obtain ⟨J, hJ⟩ := exists_pow_two_bracket (lo := min 1 mfl)
    (hi := (S.card : ENNReal) + ∑ j ∈ S, MeasureTheory.volume (Z j).shade)
    (by simp [hm0]) (by simp [sum_volume_shade_ne_top Z S])
  have hhi : ∀ (p : ℕ) (q : Fin (2 * Tube.ssfGridLen δ + 4)), ∀ w ⊆ S, ∀ i : ι,
      fourStatRow 𝒱 Z (Tube.ssfGridLen δ - p) (q : ℕ) w i ≤ 2 ^ J * min 1 mfl :=
    fun p q w hw i => (fourStatRow_le 𝒱 Z _ _ hw i).trans hJ
  obtain ⟨t, hts, htne, htwt, -, Φ, hΦ⟩ :=
    exists_multiLevel_band_wt (n := 2 * Tube.ssfGridLen δ + 4) (γ := ι) S
      (fun k => MeasureTheory.volume (Z k).shade) hwt
      (fun p => 𝒱.cover.assign (Tube.ssfGridLen δ - p))
      (fun p q hpq i hi j hj h =>
        𝒱.cover.assign_eq_of_le (by omega) (Nat.sub_le _ _) hi hj h)
      (fun p q w i => fourStatRow 𝒱 Z (Tube.ssfGridLen δ - p) (q : ℕ) w i)
      (fun p q => leafLocal_fourStatRow 𝒱 Z (Tube.ssfGridLen δ - p) (q : ℕ))
      (fun p q w i => dyadicScaleBucket (min 1 mfl)
        (fourStatRow 𝒱 Z (Tube.ssfGridLen δ - p) (q : ℕ) w i))
      (fun p q w i j h => by
        rw [fourStatRow_congr_cell 𝒱 Z (Tube.ssfGridLen δ - p) (q : ℕ) w h])
      (J + 1) (Nat.succ_pos J)
      (fun p q w hw i _ => dyadicScaleBucket_lt_succ (hhi p q w hw i))
      (fun p q w hw i hi j hj hbeq =>
        le_two_mul_of_dyadicScaleBucket_eq ⟨J, hhi p q w hw i⟩ ⟨J, hhi p q w hw j⟩
          (le_fourStatRow hδ 𝒱 Z hm _ _ hw hi) hbeq)
      (fun _ _ => 0) 1 Nat.one_pos (fun _ _ _ => Nat.zero_lt_one) (fun _ _ _ _ => rfl)
      (Tube.ssfGridLen δ)
  obtain ⟨j₀, hj₀⟩ := htne
  have hrow : ∀ (k : ℕ), k ≤ Tube.ssfGridLen δ →
      ∀ (q : Fin (2 * Tube.ssfGridLen δ + 4)), ∀ i ∈ t,
        Φ (Tube.ssfGridLen δ - k) q ≤ fourStatRow 𝒱 Z k (q : ℕ) t i ∧
          fourStatRow 𝒱 Z k (q : ℕ) t i ≤ 2 * Φ (Tube.ssfGridLen δ - k) q := by
    intro k hk q i hi
    have hkk : Tube.ssfGridLen δ - (Tube.ssfGridLen δ - k) = k := Nat.sub_sub_self hk
    have hb := hΦ (Tube.ssfGridLen δ - k) (Nat.sub_le _ _) q i hi
    rwa [hkk] at hb
  have hhom : IsClassHomogeneousOn 𝒱 t := by
    refine isClassHomogeneousOn_of_classCountBand hCu 𝒱 hj₀
      (Ψ := fun k => Φ (Tube.ssfGridLen δ - k)
        ⟨2 * Tube.ssfGridLen δ + 2, by omega⟩) (fun k hk i hi => ?_)
    have hb := hrow k hk ⟨2 * Tube.ssfGridLen δ + 2, by omega⟩ i hi
    rwa [fourStatRow_classCount 𝒱 Z k t i] at hb
  refine ⟨t, J, hts, ⟨j₀, hj₀⟩,
    ⟨hts, ⟨j₀, hj₀⟩, fun _ => rfl, fun _ => subset_rfl, by simpa using htwt, hhom⟩, ?_, ?_, ?_⟩
  · refine ⟨fun p c => Φ (Tube.ssfGridLen δ - p) ⟨min c (Tube.ssfGridLen δ), by omega⟩, ?_⟩
    intro p hp c hc k hk
    have hb := hrow p hp ⟨min c (Tube.ssfGridLen δ), by omega⟩ k hk
    rw [fourStatRow_density 𝒱 Z p (by omega : min c (Tube.ssfGridLen δ)
      < Tube.ssfGridLen δ + 1) t k] at hb
    have heq : levelDensityStat 𝒱 p (min c (Tube.ssfGridLen δ)) t k
        = levelDensityStat 𝒱 p c t k := by rw [min_eq_left hc]
    rwa [heq] at hb
  · refine ⟨fun p c => Φ (Tube.ssfGridLen δ - p)
      ⟨Tube.ssfGridLen δ + 1 + min c (Tube.ssfGridLen δ), by omega⟩, ?_⟩
    intro p hp c hc k hk
    have hb := hrow p hp ⟨Tube.ssfGridLen δ + 1 + min c (Tube.ssfGridLen δ), by omega⟩ k hk
    rw [fourStatRow_count 𝒱 Z p
      (by omega : ¬ Tube.ssfGridLen δ + 1 + min c (Tube.ssfGridLen δ) < Tube.ssfGridLen δ + 1)
      (by omega : Tube.ssfGridLen δ + 1 + min c (Tube.ssfGridLen δ)
        < 2 * Tube.ssfGridLen δ + 2) t k] at hb
    rwa [show Tube.ssfGridLen δ + 1 + min c (Tube.ssfGridLen δ) - (Tube.ssfGridLen δ + 1) = c from
      by have := min_eq_left hc; omega] at hb
  · refine ⟨fun p => Φ (Tube.ssfGridLen δ - p) ⟨2 * Tube.ssfGridLen δ + 3, by omega⟩, ?_⟩
    intro p hp k hk
    have hb := hrow p hp ⟨2 * Tube.ssfGridLen δ + 3, by omega⟩ k hk
    rwa [fourStatRow_mass 𝒱 Z p t k] at hb

open scoped Classical in
/-- **The statistic *is* the fibre density**: `levelDensityStat 𝒰 p c u i` and
`Tube.UniformTubeSet.assignFibre c p (𝒰.cover.assign p i)` are the same `Finset` by definition, so
the band A1 produces over leaves is already in the shape
`le_mul_maxDensity_nodesUnder_of_lt_towerDensityArrayFibre` consumes. -/
theorem levelDensityStat_eq_maxDensity_assignFibre
    (𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu) (p c : ℕ) (i : ι) :
    levelDensityStat 𝒰 p c u i
      = Kakeya.maxDensity (𝒰.assignFibre c p (𝒰.cover.assign p i))
          (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) := rfl

open scoped Classical in
/-- **Step 1's node-side reading, in the field's own shape.**  A band over the *leaves* of the
tower's own family is the field
`Kakeya.ML2Reduction.IsKatzTaoDividingWindowLevels.level_density_band` verbatim, at any
`Cstar ≥ 2` — the factor `2` of A1 is `Cstar`'s *left* end, so a larger window constant is free.

`hidx` is exactly what `Kakeya.ML2Core.restrictOccupied_mem_indexSet_iff` supplies for
`Tube.UniformTubeSet.restrictOccupied`: the restricted hierarchy's level-`p` nodes are the level-`p`
nodes of the retained leaves.

**Family/shading:** the tower's own family `t`; no shading.  **Level pair:** every `(p,c)`. -/
theorem levelDensityBand_indexSet {t : Finset ι}
    (𝒱 : Tube.UniformTubeSet t T (Tube.ssfGridLen δ) Cu) {Cstar : ENNReal} (hCstar : 2 ≤ Cstar)
    {Φ : ℕ → ℕ → ENNReal}
    (hband : ∀ p ≤ Tube.ssfGridLen δ, ∀ c ≤ Tube.ssfGridLen δ, ∀ k ∈ t,
      Φ p c ≤ levelDensityStat 𝒱 p c t k ∧ levelDensityStat 𝒱 p c t k ≤ 2 * Φ p c)
    (hidx : ∀ p : ℕ, ∀ j ∈ 𝒱.cover.indexSet p, ∃ k ∈ t, 𝒱.cover.assign p k = j) :
    ∃ Φ' : ℕ → ℕ → ENNReal, ∀ p ≤ Tube.ssfGridLen δ, ∀ c ≤ Tube.ssfGridLen δ,
      ∀ j ∈ 𝒱.cover.indexSet p,
      Φ' p c ≤ Kakeya.maxDensity
          ((Tube.coverClass t (𝒱.cover.assign p) j).image (𝒱.cover.assign c))
          (fun j' => (𝒱.cover.tube c j').toConvexSpaceBody) ∧
        Kakeya.maxDensity
          ((Tube.coverClass t (𝒱.cover.assign p) j).image (𝒱.cover.assign c))
          (fun j' => (𝒱.cover.tube c j').toConvexSpaceBody) ≤ Cstar * Φ' p c := by
  classical
  refine ⟨Φ, fun p hp c hc j hj => ?_⟩
  obtain ⟨k, hk, rfl⟩ := hidx p j hj
  obtain ⟨hlo, hhi⟩ := hband p hp c hc k hk
  exact ⟨hlo, hhi.trans (mul_le_mul' hCstar le_rfl)⟩

open scoped Classical in
/-- **Step 2, and it moves no field**.

`le_level_maxDensity` is stated on `nodesUnder` and is a **lower** bound, so its witness must be
*produced* on the fibre array and then weakened along `assignFibre ⊆ nodesUnder`.  That is exactly
`Kakeya.ML2Core.le_mul_maxDensity_nodesUnder_of_lt_towerDensityArrayFibre`, and this is its
instantiation at the field's own quantifier: the `¬Test` of the fibre run supplies `hwit` at each
inset level, step 1's band supplies `hband`, and the existing field comes out unchanged.

**Family/shading:** the tower's family `u`; no shading.  **Level pair:** `(a,c)` for every inset
level `c` of the window `(a,b)`. -/
theorem le_level_maxDensity_of_fibre_witness
    (𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu) {Cstar : ENNReal} {η : ℕ → ℝ} {εd : ℝ}
    {a b m : ℕ} (hb : b ≤ Tube.ssfGridLen δ) {Φ : ℕ → ℕ → ENNReal}
    (hband : ∀ c ≤ Tube.ssfGridLen δ, ∀ j ∈ 𝒰.cover.indexSet a,
      Φ a c ≤ Kakeya.maxDensity (𝒰.assignFibre c a j)
          (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) ∧
        Kakeya.maxDensity (𝒰.assignFibre c a j)
          (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) ≤ Cstar * Φ a c)
    (hwit : ∀ c : ℕ, a + ⌈εd * ((b : ℝ) - (a : ℝ))⌉₊ ≤ c → c + ⌈εd * ((b : ℝ) - (a : ℝ))⌉₊ ≤ b →
      ENNReal.ofReal (((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
          / (Tube.gridScale δ (Tube.ssfGridLen δ) c : ℝ)) ^ η (m + 1))
        < towerDensityArrayFibre 𝒰 a c) :
    ∀ c : ℕ, a + ⌈εd * ((b : ℝ) - (a : ℝ))⌉₊ ≤ c → c + ⌈εd * ((b : ℝ) - (a : ℝ))⌉₊ ≤ b →
      ∀ j ∈ 𝒰.cover.indexSet a,
        ENNReal.ofReal (((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
            / (Tube.gridScale δ (Tube.ssfGridLen δ) c : ℝ)) ^ η (m + 1))
          ≤ Cstar * Kakeya.maxDensity (𝒰.nodesUnder c a j)
              (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) := by
  classical
  intro c h1 h2
  have hac : a ≤ c := by omega
  have hc : c ≤ Tube.ssfGridLen δ := by omega
  exact le_mul_maxDensity_nodesUnder_of_lt_towerDensityArrayFibre 𝒰 hac hc
    (hband c hc) (hwit c h1 h2)


open scoped Classical in
/-- **Match control**: `levelDensityBand_indexSet`'s conclusion is the field
`Kakeya.ML2Reduction.IsKatzTaoDividingWindowLevels.level_density_band` **verbatim** — the projection
inhabits it, so nothing has been reshaped in transcription. -/
example {t : Finset ι} {𝒱 : Tube.UniformTubeSet t T (Tube.ssfGridLen δ) Cu}
    {Cstar : ENNReal} {η : ℕ → ℝ} {εd : ℝ} {N a b m : ℕ}
    (hw : ML2Reduction.IsKatzTaoDividingWindowLevels 𝒱 Cstar η εd N a b m) :
    ∃ Φ' : ℕ → ℕ → ENNReal, ∀ p ≤ Tube.ssfGridLen δ, ∀ c ≤ Tube.ssfGridLen δ,
      ∀ j ∈ 𝒱.cover.indexSet p,
      Φ' p c ≤ Kakeya.maxDensity
          ((Tube.coverClass t (𝒱.cover.assign p) j).image (𝒱.cover.assign c))
          (fun j' => (𝒱.cover.tube c j').toConvexSpaceBody) ∧
        Kakeya.maxDensity
          ((Tube.coverClass t (𝒱.cover.assign p) j).image (𝒱.cover.assign c))
          (fun j' => (𝒱.cover.tube c j').toConvexSpaceBody) ≤ Cstar * Φ' p c :=
  hw.level_density_band


open scoped Classical in
/-- **What `level_density_band` demands of the family it is asked on** — the measurement that
locates the remaining gap on the (F) route.

The field is a *single* profile `Φ p c` bounding **every** level-`p` node's two-level density
two-sidedly, so it forces the densities of any two level-`p` nodes to agree within `Cstar`.  That
is a **regularity hypothesis on the family**, not a consequence of the tower: it is exactly what
A1's refinement (`exists_levelDensityStat_band`) buys and what
`Kakeya.ML2Core.IsClassHomogeneousOn` — a band on class *cardinalities* — does not, since two cells
of equal size can carry very different maximal densities.

Recorded so that the next hand reads the obstruction off a statement rather than off
prose: any producer asked for this field on an **arbitrary** subfamily must first refine. -/
theorem pairwise_of_levelDensityBand {t : Finset ι}
    (𝒱 : Tube.UniformTubeSet t T (Tube.ssfGridLen δ) Cu) {Cstar : ENNReal}
    {Φ : ℕ → ℕ → ENNReal}
    (hband : ∀ p ≤ Tube.ssfGridLen δ, ∀ c ≤ Tube.ssfGridLen δ,
      ∀ j ∈ 𝒱.cover.indexSet p,
      Φ p c ≤ Kakeya.maxDensity (𝒱.assignFibre c p j)
          (fun j' => (𝒱.cover.tube c j').toConvexSpaceBody) ∧
        Kakeya.maxDensity (𝒱.assignFibre c p j)
          (fun j' => (𝒱.cover.tube c j').toConvexSpaceBody) ≤ Cstar * Φ p c) :
    ∀ p ≤ Tube.ssfGridLen δ, ∀ c ≤ Tube.ssfGridLen δ,
      ∀ j ∈ 𝒱.cover.indexSet p, ∀ j' ∈ 𝒱.cover.indexSet p,
        Kakeya.maxDensity (𝒱.assignFibre c p j)
            (fun k => (𝒱.cover.tube c k).toConvexSpaceBody)
          ≤ Cstar * Kakeya.maxDensity (𝒱.assignFibre c p j')
              (fun k => (𝒱.cover.tube c k).toConvexSpaceBody) := by
  intro p hp c hc j hj j' hj'
  exact (hband p hp c hc j hj).2.trans (mul_le_mul' le_rfl (hband p hp c hc j' hj').1)

end LevelDensityBandInstance



section RefinedHierarchyBand

open MeasureTheory Tube

universe w

variable {ι : Type w} {δ Cu : NNReal} {u : Finset ι}
  {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}

open scoped Classical in
/-- **Step 1 delivered on the tower the `(F)` branch actually names.**

`Kakeya.ML2Core.RefinedFloorHypothesis` does not ask for the window on the *given* family: it binds
`S' ⊆ S` and asks for it on `Kakeya.ML2Core.refinedHierarchy`, whose `assign`, `tube` and
`indexSet` are the restricted tower's by `rfl`.  So A1's refinement is available exactly where the
source performs it (l.4056-4058), and this is the bridge: from the band produced by
`exists_levelDensityStat_band` on the retained family, the field
`Kakeya.ML2Reduction.IsKatzTaoDividingWindowLevels.level_density_band` on `refinedHierarchy`.

`IsClassHomogeneousOn 𝒰 S'` stays a hypothesis: it is a separate clause of the `(F)` branch (and of
`Kakeya.ML2Core.IsShadedRefinementOf`), not something the density band supplies.

**Family/shading:** the refinement `S'` with its shading `W` — this is the one place the shading
moves, and the band itself does not see it (`refinedHierarchy_tube` is `rfl`).
**Level pair:** every `(p,c)` with both `≤ ssfGridLen δ`. -/
theorem levelDensityBand_refinedHierarchy
    (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
    {S' : Finset ι} (hS' : S' ⊆ u) (hhom : IsClassHomogeneousOn 𝒰 S')
    {W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    (hW : (fun i => (W i).toTube) = (fun i => (T i).toTube))
    {Cstar : ENNReal} (hCstar : 2 ≤ Cstar) {Φ : ℕ → ℕ → ENNReal}
    (hband : ∀ p ≤ Tube.ssfGridLen δ, ∀ c ≤ Tube.ssfGridLen δ, ∀ k ∈ S',
      Φ p c ≤ levelDensityStat 𝒰 p c S' k ∧ levelDensityStat 𝒰 p c S' k ≤ 2 * Φ p c) :
    ∃ Φ' : ℕ → ℕ → ENNReal, ∀ p ≤ Tube.ssfGridLen δ, ∀ c ≤ Tube.ssfGridLen δ,
      ∀ j ∈ (refinedHierarchy 𝒰 hS' hhom hW).cover.indexSet p,
      Φ' p c ≤ Kakeya.maxDensity
          ((Tube.coverClass S' ((refinedHierarchy 𝒰 hS' hhom hW).cover.assign p) j).image
            ((refinedHierarchy 𝒰 hS' hhom hW).cover.assign c))
          (fun j' => ((refinedHierarchy 𝒰 hS' hhom hW).cover.tube c j').toConvexSpaceBody) ∧
        Kakeya.maxDensity
          ((Tube.coverClass S' ((refinedHierarchy 𝒰 hS' hhom hW).cover.assign p) j).image
            ((refinedHierarchy 𝒰 hS' hhom hW).cover.assign c))
          (fun j' => ((refinedHierarchy 𝒰 hS' hhom hW).cover.tube c j').toConvexSpaceBody)
          ≤ Cstar * Φ' p c := by
  classical
  refine levelDensityBand_indexSet (refinedHierarchy 𝒰 hS' hhom hW) hCstar (Φ := Φ)
    (fun p hp c hc k hk => hband p hp c hc k hk) (fun p j hj => ?_)
  simpa [refinedHierarchy, Tube.UniformTubeSet.retube, Tube.UniformTubeSet.restrictOccupied,
    eq_comm] using hj

open scoped Classical in
/-- **Step 1, end to end, in the `(F)` branch's own shape**: the A1 refinement of the family
*together with* the window field it supplies on `refinedHierarchy`.

This is the object the `(F)` producer consumes.  What it does **not** supply, and what therefore
remains, is named in the statement: `IsClassHomogeneousOn 𝒰 S'` is a hypothesis of the conclusion,
because homogenising the refinement is a second pigeonhole and is not part of the density band.

**Family/shading:** ambient `u` refined to `S'`; the shading enters only at `W`.
**Level pair:** every `(p,c)`. -/
theorem exists_refinement_levelDensityBand_refinedHierarchy (hδ : 0 < δ)
    (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
    (hu : u.Nonempty) {Cstar : ENNReal} (hCstar : 2 ≤ Cstar) :
    ∃ (S' : Finset ι) (J : ℕ) (hS' : S' ⊆ u), S'.Nonempty ∧
      u.card ≤ ((J + 1) ^ (Tube.ssfGridLen δ + 1)) ^ (Tube.ssfGridLen δ + 1) * S'.card ∧
      ∀ (hhom : IsClassHomogeneousOn 𝒰 S')
        (W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
        (hW : (fun i => (W i).toTube) = (fun i => (T i).toTube)),
      ∃ Φ' : ℕ → ℕ → ENNReal, ∀ p ≤ Tube.ssfGridLen δ, ∀ c ≤ Tube.ssfGridLen δ,
        ∀ j ∈ (refinedHierarchy 𝒰 hS' hhom hW).cover.indexSet p,
        Φ' p c ≤ Kakeya.maxDensity
            ((Tube.coverClass S' ((refinedHierarchy 𝒰 hS' hhom hW).cover.assign p) j).image
              ((refinedHierarchy 𝒰 hS' hhom hW).cover.assign c))
            (fun j' => ((refinedHierarchy 𝒰 hS' hhom hW).cover.tube c j').toConvexSpaceBody) ∧
          Kakeya.maxDensity
            ((Tube.coverClass S' ((refinedHierarchy 𝒰 hS' hhom hW).cover.assign p) j).image
              ((refinedHierarchy 𝒰 hS' hhom hW).cover.assign c))
            (fun j' => ((refinedHierarchy 𝒰 hS' hhom hW).cover.tube c j').toConvexSpaceBody)
            ≤ Cstar * Φ' p c := by
  classical
  obtain ⟨t, J, hts, htne, htcard, Φ, hΦ⟩ := exists_levelDensityStat_band hδ 𝒰 hu
  exact ⟨t, J, hts, htne, htcard, fun hhom W hW =>
    levelDensityBand_refinedHierarchy 𝒰 hts hhom hW hCstar hΦ⟩


open scoped Classical in
/-- **Step 1 on the `(F)` branch's tower, with class homogeneity no longer a hypothesis.**

, : descendant counts *are* Def 2.1(iii)'s class band (l.227-228),
which is what `Kakeya.ML2Core.IsClassHomogeneousOn` renders, and l.4916-4917 regularises all the
statistics **at once**.  So `exists_levelBand_classHomogeneous` produces `S'`, its class
homogeneity and its density band in **one** whole-fibre pass, and `refinedHierarchy` is then
available with no second restriction — the unsound thing  forbids.

Against `exists_refinement_levelDensityBand_refinedHierarchy` (which leaves `hhom` open) this is
strictly stronger; that one is kept because it is the statement that does not spend the `2 ≤ Cu`
condition.

**Family/shading:** ambient `u` refined to `S'`; the shading enters only at `W`.
**Level pair:** every `(p,c)` for the band, every `k` for the homogeneity. -/
theorem exists_refinement_classHomogeneous_levelDensityBand (hδ : 0 < δ) (hCu : 2 ≤ Cu)
    (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu)
    (hu : u.Nonempty) {Cstar : ENNReal} (hCstar : 2 ≤ Cstar) :
    ∃ (S' : Finset ι) (J : ℕ) (hS' : S' ⊆ u) (hhom : IsClassHomogeneousOn 𝒰 S'), S'.Nonempty ∧
      u.card ≤ ((J + 1) ^ (Tube.ssfGridLen δ + 2)) ^ (Tube.ssfGridLen δ + 1) * S'.card ∧
      ∀ (W : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
        (hW : (fun i => (W i).toTube) = (fun i => (T i).toTube)),
      ∃ Φ' : ℕ → ℕ → ENNReal, ∀ p ≤ Tube.ssfGridLen δ, ∀ c ≤ Tube.ssfGridLen δ,
        ∀ j ∈ (refinedHierarchy 𝒰 hS' hhom hW).cover.indexSet p,
        Φ' p c ≤ Kakeya.maxDensity
            ((Tube.coverClass S' ((refinedHierarchy 𝒰 hS' hhom hW).cover.assign p) j).image
              ((refinedHierarchy 𝒰 hS' hhom hW).cover.assign c))
            (fun j' => ((refinedHierarchy 𝒰 hS' hhom hW).cover.tube c j').toConvexSpaceBody) ∧
          Kakeya.maxDensity
            ((Tube.coverClass S' ((refinedHierarchy 𝒰 hS' hhom hW).cover.assign p) j).image
              ((refinedHierarchy 𝒰 hS' hhom hW).cover.assign c))
            (fun j' => ((refinedHierarchy 𝒰 hS' hhom hW).cover.tube c j').toConvexSpaceBody)
            ≤ Cstar * Φ' p c := by
  classical
  obtain ⟨t, J, hts, htne, htcard, hhom, Φ, hΦ⟩ :=
    exists_levelBand_classHomogeneous hδ hCu 𝒰 hu
  exact ⟨t, J, hts, hhom, htne, htcard, fun W hW =>
    levelDensityBand_refinedHierarchy 𝒰 hts hhom hW hCstar hΦ⟩

end RefinedHierarchyBand



section WindowAssembly

open MeasureTheory Tube

universe v2

variable {ι : Type v2} {δ Cu : NNReal} {u : Finset ι}
  {T : ι → Tube δ (EuclideanSpace ℝ (Fin 3))}

/-- **`scale_sep` from the window's width** — the converse of
`Kakeya.ML2Core.IsKatzTaoDividingWindow.mul_ssfGridLen_le_sub`, by the same `StrictAnti` chain read
in the other direction.

`Tube.gridScale δ L k = δ^{k/L}` and `δ < 1`, so `ρ_b ≤ δ^{ε_d} ρ_a` **is** `ε_d·L + a ≤ b`.  This
is the field-producing half; the existing lemma is the field-consuming half, and having both makes the
width the single arithmetic fact the four scale fields rest on.

**Family/shading:** none — this is grid arithmetic.  **Level pair:** `(a,b)`. -/
theorem scale_sep_of_width (hδ0 : 0 < δ) (hδ1 : δ < 1) {εd : ℝ} {a b : ℕ}
    (hab : a < b) (hbL : b ≤ Tube.ssfGridLen δ)
    (hwidth : εd * (Tube.ssfGridLen δ : ℝ) + (a : ℝ) ≤ (b : ℝ)) :
    (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
      ≤ (δ : ℝ) ^ εd * (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ) := by
  have hLn : 0 < Tube.ssfGridLen δ := by omega
  have hL : 0 < (Tube.ssfGridLen δ : ℝ) := by exact_mod_cast hLn
  have hδr0 : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
  have hδr1 : (δ : ℝ) < 1 := by exact_mod_cast hδ1
  have hanti : StrictAnti (fun x : ℝ => (δ : ℝ) ^ x) :=
    Real.strictAnti_rpow_of_base_lt_one hδr0 hδr1
  have hmono : εd + (a : ℝ) / (Tube.ssfGridLen δ : ℝ) ≤ (b : ℝ) / (Tube.ssfGridLen δ : ℝ) := by
    have key : (εd * (Tube.ssfGridLen δ : ℝ) + (a : ℝ)) / (Tube.ssfGridLen δ : ℝ)
        ≤ (b : ℝ) / (Tube.ssfGridLen δ : ℝ) := by gcongr
    calc εd + (a : ℝ) / (Tube.ssfGridLen δ : ℝ)
        = (εd * (Tube.ssfGridLen δ : ℝ) + (a : ℝ)) / (Tube.ssfGridLen δ : ℝ) := by
          field_simp
      _ ≤ (b : ℝ) / (Tube.ssfGridLen δ : ℝ) := key
  rw [Tube.gridScale, Tube.gridScale, NNReal.coe_rpow, NNReal.coe_rpow, ← Real.rpow_add hδr0]
  exact (StrictAnti.le_iff_ge hanti).mpr hmono

/-- **The dividing window, assembled from its fields** — the four scale fields reduced to the single
width inequality, and the three density fields taken as supplied.

This is the constructor the `(F)` route needs on `refinedHierarchy`: `coarse_maxDensity_le` comes
from the **fibre** array (`maxDensity_indexSet_le_mul_towerDensityArrayFibre`),
`middle_maxDensity_le` from the **containment** array (`maxDensity_nodesUnder_le_of_towerGood`),
and `le_window_maxDensity` is the lower-bound field whose witness must be *fibre*-produced

**A1-b column** for the fields this builds:

| field | direction | stated on | witness produced on |
|---|---|---|---|
| `coarse_maxDensity_le` | upper | the level family | fibre array |
| `middle_maxDensity_le` | upper | `nodesUnder` | containment array |
| `le_window_maxDensity` | lower | `nodesUnder` | **fibre** array |
| `le_level_maxDensity` | lower | `nodesUnder` | **fibre** array |
| `level_density_band` | two-sided | `assignFibre` | A1's joint bin |

**Family/shading:** the tower's own family; no shading.  **Level pair:** `(a,b,m)`. -/
theorem isKatzTaoDividingWindow_of_fields (hδ0 : 0 < δ) (hδ1 : δ < 1)
    {𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu}
    {Cstar : ENNReal} {η : ℕ → ℝ} {εd : ℝ} {N a b m : ℕ}
    (hmN : m < N) (hab : a < b) (hbL : b ≤ Tube.ssfGridLen δ)
    (hwidth : εd * (Tube.ssfGridLen δ : ℝ) + (a : ℝ) ≤ (b : ℝ))
    (hcoarse : Kakeya.maxDensity (𝒰.cover.indexSet a)
        (fun j => (𝒰.cover.tube a j).toConvexSpaceBody)
      ≤ Cstar * ENNReal.ofReal ((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ) ^ (-η m)))
    (hmiddle : ∀ j ∈ 𝒰.cover.indexSet a,
      Kakeya.maxDensity (𝒰.nodesUnder b a j) (fun j' => (𝒰.cover.tube b j').toConvexSpaceBody)
        ≤ Cstar * ENNReal.ofReal
            (((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
              / (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)) ^ η m))
    (hwindow : ∀ ρ : NNReal,
      (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
          * ((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
            / (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)) ^ εd ≤ (ρ : ℝ) →
      (ρ : ℝ) ≤ (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
          * ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
            / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ εd →
      ∀ j ∈ 𝒰.cover.indexSet a,
        ENNReal.ofReal (((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ) / (ρ : ℝ)) ^ η (m + 1))
          ≤ Cstar * Kakeya.maxDensity (𝒰.nodesUnder b a j)
              (fun j' => ((𝒰.cover.tube b j').rescale ρ).toConvexSpaceBody)) :
    ML2Reduction.IsKatzTaoDividingWindow 𝒰 Cstar η εd N a b m where
  step_lt := hmN
  coarse_lt_fine := hab
  fine_le_gridLen := hbL
  scale_sep := scale_sep_of_width hδ0 hδ1 hab hbL hwidth
  coarse_maxDensity_le := hcoarse
  middle_maxDensity_le := hmiddle
  le_window_maxDensity := hwindow

open scoped Classical in
/-- **The twin, assembled**: the parent plus the two clauses
`Kakeya.ML2Reduction.IsKatzTaoDividingWindowLevels` adds — the multiplicity-free level clause
(fibre-produced, `nodesUnder`-stated) and the two-level band (A1's joint bin, on `assignFibre`). -/
theorem isKatzTaoDividingWindowLevels_of_fields
    {𝒰 : Tube.UniformTubeSet u T (Tube.ssfGridLen δ) Cu}
    {Cstar : ENNReal} {η : ℕ → ℝ} {εd : ℝ} {N a b m : ℕ}
    (hpar : ML2Reduction.IsKatzTaoDividingWindow 𝒰 Cstar η εd N a b m)
    (hlevel : ∀ c : ℕ, a + ⌈εd * ((b : ℝ) - (a : ℝ))⌉₊ ≤ c →
      c + ⌈εd * ((b : ℝ) - (a : ℝ))⌉₊ ≤ b → ∀ j ∈ 𝒰.cover.indexSet a,
      ENNReal.ofReal (((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
          / (Tube.gridScale δ (Tube.ssfGridLen δ) c : ℝ)) ^ η (m + 1))
        ≤ Cstar * Kakeya.maxDensity (𝒰.nodesUnder c a j)
            (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody))
    (hband : ∃ Φ : ℕ → ℕ → ENNReal, ∀ p ≤ Tube.ssfGridLen δ, ∀ c ≤ Tube.ssfGridLen δ,
      ∀ j ∈ 𝒰.cover.indexSet p,
      Φ p c ≤ Kakeya.maxDensity
          ((Tube.coverClass u (𝒰.cover.assign p) j).image (𝒰.cover.assign c))
          (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) ∧
        Kakeya.maxDensity
          ((Tube.coverClass u (𝒰.cover.assign p) j).image (𝒰.cover.assign c))
          (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody) ≤ Cstar * Φ p c) :
    ML2Reduction.IsKatzTaoDividingWindowLevels 𝒰 Cstar η εd N a b m where
  toIsKatzTaoDividingWindow := hpar
  le_level_maxDensity := hlevel
  level_density_band := hband


open scoped Classical in
/-- **The twin, assembled from the width and A1's band** — the form the `(F)` route uses.

Generic in the tower, so it applies verbatim at `Kakeya.ML2Core.refinedHierarchy`.  The four scale
fields collapse to the single width inequality `ε_d·L + a ≤ b` (`scale_sep_of_width`); the two
upper-bound density fields and the two lower-bound ones are taken as supplied, with the A1-b
reading recorded in `isKatzTaoDividingWindow_of_fields`'s docstring; and `level_density_band` is
read off A1's band over the tower's own leaves by `levelDensityBand_indexSet`.

**Family/shading:** the tower's own family `t`; no shading.  **Level pair:** `(a,b,m)` for the
window, every `(p,c)` for the band. -/
theorem isKatzTaoDividingWindowLevels_of_width_and_band (hδ0 : 0 < δ) (hδ1 : δ < 1)
    {t : Finset ι} (𝒱 : Tube.UniformTubeSet t T (Tube.ssfGridLen δ) Cu)
    {Cstar : ENNReal} (hCstar : 2 ≤ Cstar) {η : ℕ → ℝ} {εd : ℝ} {N a b m : ℕ}
    (hmN : m < N) (hab : a < b) (hbL : b ≤ Tube.ssfGridLen δ)
    (hwidth : εd * (Tube.ssfGridLen δ : ℝ) + (a : ℝ) ≤ (b : ℝ))
    (hcoarse : Kakeya.maxDensity (𝒱.cover.indexSet a)
        (fun j => (𝒱.cover.tube a j).toConvexSpaceBody)
      ≤ Cstar * ENNReal.ofReal ((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ) ^ (-η m)))
    (hmiddle : ∀ j ∈ 𝒱.cover.indexSet a,
      Kakeya.maxDensity (𝒱.nodesUnder b a j) (fun j' => (𝒱.cover.tube b j').toConvexSpaceBody)
        ≤ Cstar * ENNReal.ofReal
            (((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
              / (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)) ^ η m))
    (hwindow : ∀ ρ : NNReal,
      (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
          * ((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
            / (Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)) ^ εd ≤ (ρ : ℝ) →
      (ρ : ℝ) ≤ (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
          * ((Tube.gridScale δ (Tube.ssfGridLen δ) b : ℝ)
            / (Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)) ^ εd →
      ∀ j ∈ 𝒱.cover.indexSet a,
        ENNReal.ofReal (((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ) / (ρ : ℝ)) ^ η (m + 1))
          ≤ Cstar * Kakeya.maxDensity (𝒱.nodesUnder b a j)
              (fun j' => ((𝒱.cover.tube b j').rescale ρ).toConvexSpaceBody))
    (hlevel : ∀ c : ℕ, a + ⌈εd * ((b : ℝ) - (a : ℝ))⌉₊ ≤ c →
      c + ⌈εd * ((b : ℝ) - (a : ℝ))⌉₊ ≤ b → ∀ j ∈ 𝒱.cover.indexSet a,
      ENNReal.ofReal (((Tube.gridScale δ (Tube.ssfGridLen δ) a : ℝ)
          / (Tube.gridScale δ (Tube.ssfGridLen δ) c : ℝ)) ^ η (m + 1))
        ≤ Cstar * Kakeya.maxDensity (𝒱.nodesUnder c a j)
            (fun j' => (𝒱.cover.tube c j').toConvexSpaceBody))
    (hidx : ∀ p : ℕ, ∀ j ∈ 𝒱.cover.indexSet p, ∃ k ∈ t, 𝒱.cover.assign p k = j)
    {Φ : ℕ → ℕ → ENNReal}
    (hband : ∀ p ≤ Tube.ssfGridLen δ, ∀ c ≤ Tube.ssfGridLen δ, ∀ k ∈ t,
      Φ p c ≤ levelDensityStat 𝒱 p c t k ∧ levelDensityStat 𝒱 p c t k ≤ 2 * Φ p c) :
    ML2Reduction.IsKatzTaoDividingWindowLevels 𝒱 Cstar η εd N a b m :=
  isKatzTaoDividingWindowLevels_of_fields
    (isKatzTaoDividingWindow_of_fields hδ0 hδ1 hmN hab hbL hwidth hcoarse hmiddle hwindow)
    hlevel (levelDensityBand_indexSet 𝒱 hCstar hband hidx)

end WindowAssembly

section RefinedFloorRoute

open MeasureTheory Tube

variable {ι : Type*} {δ Cu : NNReal} {u : Finset ι}
  {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}

/-- **The payload's remaining goal, named without the over-strong intermediate.**

`Kakeya.ML2Core.InheritedWindowSupplyAt` asks for a dividing window on the **given** restricted
tower, for **every** `S`.  `Kakeya.ML2Core.pairwise_of_levelDensityBand` measures why that is more
than the target needs: `level_density_band` forces all level-`p` two-level densities to agree
within `Cstar`, which is a regularity property of the family and is exactly what A1's refinement
buys — so it cannot be asserted of an arbitrary `S`.

`Kakeya.ML2Core.FloorDataAtTrichotomy` does not need it.  Its `(F)` disjunct is
`Kakeya.ML2Core.RefinedFloorHypothesis`, which itself **binds** `S' ⊆ S` and asks for the window on
`Kakeya.ML2Core.refinedHierarchy` — the refined tower.  So the refinement the source performs at
l.4056-4058 is available inside the branch, and this `def` is the payload's goal with the
refinement left where the source puts it. -/
def RefinedFloorSupplyAt (β ϖ ε₁ η' : ℝ) (gain dens : ℝ → ℝ) {C : NNReal} {Kl cl : ℕ} (Λf : ℝ≥0∞)
    (𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu) : Prop :=
  ∀ (S : Finset ι) (hS : S ⊆ u), S.Nonempty →
    ∀ (Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
      (ht : ∀ i, (Z i).toTube = (T i).toTube) (hh : IsClassHomogeneousOn 𝒰 S),
      ∃ a b m : ℕ, RefinedFloorHypothesis (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ gain dens
        η' Λf ((𝒰.restrictOccupied hS hh).retube (funext ht)) a b m

/-- **The alternative route to the payload**, additive to
`Kakeya.ML2Core.floorDataAtTrichotomy_of_windowed_of_supply` and strictly weaker in what it
demands: it never asks for a window on an unrefined family.; the
`(D)` disjunct is simply not used. -/
theorem floorDataAtTrichotomy_of_refinedFloorSupply
    {β ϖ ε₁ η' h : ℝ} {gain dens : ℝ → ℝ} {C : NNReal} {Kl cl : ℕ} {Λf : ℝ≥0∞}
    {𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu}
    (hsupply : RefinedFloorSupplyAt (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ η' gain dens Λf 𝒰) :
    FloorDataAtTrichotomy (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ η' h gain dens Λf 𝒰 := by
  intro S hS hne Z ht hh _
  obtain ⟨a, b, m, hf⟩ := hsupply S hS hne Z ht hh
  exact ⟨a, b, m, Or.inl hf⟩

/-- **Control: the new route is genuinely weaker than the existing one.**  The windowed route's two
inputs produce the refined supply, so `floorDataAtTrichotomy_of_refinedFloorSupply` subsumes
`Kakeya.ML2Core.floorDataAtTrichotomy_of_windowed_of_supply` on the `(F)` side and nothing that
holds today is lost by taking it. -/
theorem refinedFloorSupplyAt_of_windowed
    {β ϖ ε₁ η' h : ℝ} {gain dens : ℝ → ℝ} {C : NNReal} {Kl cl : ℕ} {Λf : ℝ≥0∞}
    {𝒰 : Tube.UniformTubeSet u (fun i => (T i).toTube) (Tube.ssfGridLen δ) Cu}
    (hW : WindowedFloorTrichotomyAt (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ η' h gain dens Λf 𝒰)
    (hsupply : InheritedWindowSupplyAt (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ gain dens 𝒰)
    (hno : ∀ (S : Finset ι) (Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) (lam : NNReal),
      ¬ DefectBranchAt h Λf lam 𝒰 S Z) :
    RefinedFloorSupplyAt (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ η' gain dens Λf 𝒰 := by
  intro S hS hne Z ht hh
  obtain ⟨a, b, m, hwin⟩ := hsupply S hS hne Z ht hh
  rcases hW S hS hne Z ht hh 0 a b m hwin with hF | hD
  · exact ⟨a, b, m, hF⟩
  · exact absurd hD (hno S Z 0)


/-! The loss-monotonicity `Kakeya.ML2Core.IsShadedRefinementOf.mono_loss` needed to absorb the
joint bin's per-family `J` into one uniform `Λf` is **already existing**
(`SpineFloorShapePayload.lean:81`); no sibling is cut for it. -/

/-- **`RefinedFloorHypothesis` from its three parts**, with the shading not refined (`W := Z`).

Part 1 (`href`) is now *produced* by `exists_shadedRefinement_of_joint_bin`; parts 2 and 3 are the
window and the floor **on the refined tower**, and they are what the run still owes.  Writing the
constructor down fixes which tower they must be produced on: `refinedHierarchy 𝒱 hS' hhom rfl`, and
`hS'`/`hhom` must be the *same* terms in all three parts, which is why they are explicit here. -/
theorem refinedFloorHypothesis_of_parts {β ϖ ε₁ η' : ℝ} {gain dens : ℝ → ℝ}
    {C : NNReal} {Kl cl : ℕ} {Λf : ℝ≥0∞}
    {S : Finset ι} {Z : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))}
    {𝒱 : Tube.UniformTubeSet S (fun i => (Z i).toTube) (Tube.ssfGridLen δ) Cu}
    {S' : Finset ι} (hS' : S' ⊆ S) (hhom : IsClassHomogeneousOn 𝒱 S')
    (href : IsShadedRefinementOf 𝒱 Λf S Z S' Z) {a b m : ℕ}
    (hwin : ML2Reduction.IsKatzTaoDividingWindowLevels (refinedHierarchy 𝒱 hS' hhom rfl)
      ((C : ENNReal) * StickyKakeya.totalLoss C Kl cl δ) (ML2Spine.spineRung β ϖ ε₁ gain dens)
      (ML2Spine.spineDiv ϖ ε₁) (ML2Spine.spineCount ϖ ε₁) a b m)
    (hflo : FloorHypothesisAt β ϖ ε₁ gain dens η' (refinedHierarchy 𝒱 hS' hhom rfl) a b m) :
    RefinedFloorHypothesis (C := C) (Kl := Kl) (cl := cl) β ϖ ε₁ gain dens η' Λf 𝒱 a b m :=
  ⟨S', Z, hS', hhom, rfl, href, hwin, hflo⟩

end RefinedFloorRoute

end Kakeya.ML2Core

end
