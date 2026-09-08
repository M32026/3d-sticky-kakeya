/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.NonSlabFibre

/-!
# `Tube.PartitionBrackets`: what the Section-9 fibre lemmas actually read from a hierarchy

**Relocated, not rewritten**.
Every declaration in this file was cut in `MainLemma2/LooseUniform.lean` and is moved here
**byte for byte**, statements and proofs alike; nothing is added, removed or weakened. The move
is forced by the import DAG and the DAG alone:

* E-L3 retypes the split/fibre chain over `Tube.PartitionBrackets`, and the chain's consumers are
  `Kakeya.VeryNotSticky.SplitInputs` (`MainLemma2/NonSlabSplit.lean`) and
  `Kakeya.VeryNotSticky.TangentialInputs` (`MainLemma2/TangentialCase.lean`);
* `LooseUniform.lean` imports `SplitInputsProduce` → `SetupAbsorption` → `VeryNotStickyCase` →
  `ThinCase` → `NonSlabCase` → `TangentialCase` → `NonSlabSplit`, so `PartitionBrackets` sat
  **downstream** of both consumers and neither could mention it (`lake build` reported the cycle
  explicitly: `build cycle detected: … SetupAbsorption:leanArts … TangentialCase:exportInfo …`).

`NonSlabFibre.lean` is the right home on the merits as well: the seven lemmas below are the
`Tube.PartitionBrackets` twins of the seven lemmas *of that file*, and this module is exactly one
import above it.

Seven declarations of `MainLemma2/NonSlabFibre.lean` take a `Tube.UniformTubeSet` and use
**none** of its geometry: they read the index sets, the assignment, the branching number and the
two class brackets, and nothing else. Abstracting exactly those six data decouples them from the
containment reading, so that the exact and the loose hierarchy both feed them through one binder
type.
-/

@[expose] public section

/-! **The prefix here is not `Kakeya.`**: the exact hierarchy lives in the **root**
`Tube` namespace, as `Tube.UniformTubeSet` (`Kakeya/Uniform.lean` opens `namespace Tube` at top
level), while `Kakeya.Tube.dilate` and friends live under `Kakeya`. `PartitionBrackets` is
placed beside `Tube.UniformTubeSet`, in the root namespace, so that `toPartitionBrackets` is
dot-notation on it. -/
namespace Tube

/-- **The six data of a partitioning hierarchy with class brackets**: an index set and an
assignment per grid level, a branching number, and GWZ Definition 2.1(iii) in both directions on
the assignment classes. No tube, no space, no containment — this is precisely the part of
`Tube.UniformTubeSet` that the Section-9 fibre lemmas consume, and it is common to the
exact hierarchy and to `Kakeya.LooseUniform.LooseUniformTubeSet`. -/
structure PartitionBrackets {ι : Type*} (s : Finset ι) (N : ℕ) (C : NNReal) where
  /-- The index set of the nodes at each grid level. -/
  indexSet : ℕ → Finset ι
  /-- The node a member is assigned to at each grid level. -/
  assign : ℕ → ι → ι
  /-- The branching number at each grid level. -/
  branchingN : ℕ → NNReal
  /-- Every member of `s` is assigned to an actual node; this is what makes the classes a
  partition of `s`. -/
  assign_mem : ∀ k, k ≤ N → ∀ i ∈ s, assign k i ∈ indexSet k
  /-- Definition 2.1(iii), upper half, on the class. -/
  card_class_le : ∀ k ≤ N, ∀ j ∈ indexSet k,
    ((Tube.coverClass s (assign k) j).card : NNReal) ≤ C * branchingN k
  /-- Definition 2.1(iii), lower half, on the class. -/
  le_card_class : ∀ k ≤ N, ∀ j ∈ indexSet k,
    branchingN k ≤ C * ((Tube.coverClass s (assign k) j).card : NNReal)

section
variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  {ι : Type*} {δ : NNReal}

/-- The exact hierarchy of GWZ Def 2.1, forgetting its geometry. -/
def UniformTubeSet.toPartitionBrackets {s : Finset ι} {T : ι → Tube δ E} {N : ℕ} {C : NNReal}
    (𝒰 : Tube.UniformTubeSet s T N C) : Tube.PartitionBrackets s N C where
  indexSet := 𝒰.cover.indexSet
  assign := 𝒰.cover.assign
  branchingN := 𝒰.branchingN
  assign_mem := 𝒰.cover.assign_mem
  card_class_le := 𝒰.card_class_le
  le_card_class := 𝒰.le_card_class

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
@[simp] lemma UniformTubeSet.toPartitionBrackets_indexSet {s : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} {C : NNReal} (𝒰 : Tube.UniformTubeSet s T N C) :
    𝒰.toPartitionBrackets.indexSet = 𝒰.cover.indexSet := rfl

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
@[simp] lemma UniformTubeSet.toPartitionBrackets_assign {s : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} {C : NNReal} (𝒰 : Tube.UniformTubeSet s T N C) :
    𝒰.toPartitionBrackets.assign = 𝒰.cover.assign := rfl

omit [Nontrivial E] [MeasurableSpace E] [BorelSpace E] in
@[simp] lemma UniformTubeSet.toPartitionBrackets_branchingN {s : Finset ι} {T : ι → Tube δ E}
    {N : ℕ} {C : NNReal} (𝒰 : Tube.UniformTubeSet s T N C) :
    𝒰.toPartitionBrackets.branchingN = 𝒰.branchingN := rfl

end

end Tube

namespace Kakeya

/-! ### The seven fibre lemmas over `PartitionBrackets` -/

namespace VeryNotSticky

open MeasureTheory Metric Set ShadedBody Filter Topology

universe u

open scoped Classical in
/-- The fibre `𝕋[T_ρ]` of a node, read off `Tube.PartitionBrackets`: the tubes
assigned to the node indexed by `j` at grid level `k`. Definitionally equal to
`Kakeya.VeryNotSticky.tubeFibre` at the brackets of an exact hierarchy
(`Kakeya.VeryNotSticky.tubeFibre_eq_pbTubeFibre`). -/
noncomputable def pbTubeFibre (cfg : VeryNotSticky) {N : ℕ} {C : NNReal}
    (𝒰 : Tube.PartitionBrackets cfg.s N C)
    (k : ℕ) (j : cfg.ι) : Finset cfg.ι :=
  Tube.coverClass cfg.s (𝒰.assign k) j

/-- A fibre is a subfamily. -/
lemma pbTubeFibre_subset (cfg : VeryNotSticky) {N : ℕ} {C : NNReal}
    (𝒰 : Tube.PartitionBrackets cfg.s N C)
    (k : ℕ) (j : cfg.ι) : cfg.pbTubeFibre 𝒰 k j ⊆ cfg.s := by
  simp [pbTubeFibre, Tube.coverClass]

open scoped Classical in
/-- The nodes at level `k` that have a nonempty assignment class. -/
noncomputable def pbActiveTubeNodes (cfg : VeryNotSticky) {N : ℕ} {C : NNReal}
    (𝒰 : Tube.PartitionBrackets cfg.s N C)
    (k : ℕ) : Finset cfg.ι :=
  (𝒰.indexSet k).filter fun j ↦ (cfg.pbTubeFibre 𝒰 k j).Nonempty

open scoped Classical in
/-- **Comparing the parent families at two angular scales** (blueprint
`lem:ml2tubeScaleCompare`), over `Tube.PartitionBrackets`. The statement and proof of
`Kakeya.VeryNotSticky.tubeScaleCompare` verbatim: it reads only the index sets. -/
theorem pbTubeScaleCompare (cfg : VeryNotSticky) {N : ℕ} {C : NNReal}
    (𝒰 : Tube.PartitionBrackets cfg.s N C)
    {k k' : ℕ} (par : cfg.ι → cfg.ι)
    (hpar : ∀ j ∈ 𝒰.indexSet k, par j ∈ 𝒰.indexSet k')
    (hbranch : ∀ j' ∈ 𝒰.indexSet k',
      (((𝒰.indexSet k).filter fun j ↦ par j = j').card : ℝ) ≤
        ((Tube.gridScale cfg.δ N k' : ℝ) /
          (Tube.gridScale cfg.δ N k : ℝ)) ^ 2) :
    ((𝒰.indexSet k).card : ℝ) ≤
      ((Tube.gridScale cfg.δ N k' : ℝ) /
        (Tube.gridScale cfg.δ N k : ℝ)) ^ 2 *
          ((𝒰.indexSet k').card : ℝ) := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (s := 𝒰.indexSet k)
    (t := 𝒰.indexSet k') (f := par) hpar]
  rw [Nat.cast_sum]
  calc
    (∑ j' ∈ 𝒰.indexSet k',
        (((𝒰.indexSet k).filter fun j ↦ par j = j').card : ℝ))
        ≤ ∑ _ ∈ 𝒰.indexSet k',
            ((Tube.gridScale cfg.δ N k' : ℝ) /
              (Tube.gridScale cfg.δ N k : ℝ)) ^ 2 := by
          exact Finset.sum_le_sum (fun j' hj' => hbranch j' hj')
    _ = ((Tube.gridScale cfg.δ N k' : ℝ) /
              (Tube.gridScale cfg.δ N k : ℝ)) ^ 2 *
          ((𝒰.indexSet k').card : ℝ) := by
          simp [Finset.sum_const, nsmul_eq_mul, mul_comm]

open scoped Classical in
/-- **The `ρ₂*`-fibres partition `𝕋`** (blueprint `lem:ml2nonslabFibrePartition`), over
`Tube.PartitionBrackets`. The statement and proof of
`Kakeya.VeryNotSticky.nonslabFibrePartition` verbatim: it reads only `assign_mem` and the fact
that the classes are the fibres of a function, both of which the brackets carry. This is the
lemma that makes the loose hierarchy usable at all — the classes still partition. -/
theorem pbNonslabFibrePartition (cfg : VeryNotSticky) {N : ℕ} {C₀ C : NNReal}
    (𝒰 : Tube.PartitionBrackets cfg.s N C)
    (k : ℕ) (hk : k ≤ N)
    (_hscale_ge : cfg.rho2Star C₀ ≤ Tube.gridScale cfg.δ N k)
    (_hscale_le : Tube.gridScale cfg.δ N k ≤ cfg.δ ^ (-cfg.η) * cfg.rho2Star C₀)
    (hs : cfg.s.Nonempty) :
    (cfg.pbActiveTubeNodes 𝒰 k).Nonempty ∧
      (cfg.pbActiveTubeNodes 𝒰 k : Set cfg.ι).PairwiseDisjoint (cfg.pbTubeFibre 𝒰 k) ∧
        (cfg.pbActiveTubeNodes 𝒰 k).biUnion (cfg.pbTubeFibre 𝒰 k) = cfg.s := by
  classical
  let J := cfg.pbActiveTubeNodes 𝒰 k
  change J.Nonempty ∧ (J : Set cfg.ι).PairwiseDisjoint (cfg.pbTubeFibre 𝒰 k) ∧
    J.biUnion (cfg.pbTubeFibre 𝒰 k) = cfg.s
  have hcov : cfg.s ⊆ J.biUnion (cfg.pbTubeFibre 𝒰 k) := by
    intro i hi
    have hj : 𝒰.assign k i ∈ 𝒰.indexSet k := 𝒰.assign_mem k hk i hi
    have hinf : i ∈ cfg.pbTubeFibre 𝒰 k (𝒰.assign k i) := by
      simp [pbTubeFibre, Tube.coverClass, hi]
    have hactive : 𝒰.assign k i ∈ J := by
      simp only [J, pbActiveTubeNodes, Finset.mem_filter]
      exact ⟨hj, ⟨i, hinf⟩⟩
    exact Finset.mem_biUnion.mpr ⟨𝒰.assign k i, hactive, hinf⟩
  have hJ : J.Nonempty := by
    rcases hs with ⟨i, hi⟩
    refine ⟨𝒰.assign k i, ?_⟩
    simp only [J, pbActiveTubeNodes, Finset.mem_filter]
    exact ⟨𝒰.assign_mem k hk i hi, ⟨i, by
      simp [pbTubeFibre, Tube.coverClass, hi]⟩⟩
  refine ⟨hJ, ?_, ?_⟩
  · change ∀ ⦃j⦄, j ∈ J → ∀ ⦃j'⦄, j' ∈ J → j ≠ j' →
      Disjoint (cfg.pbTubeFibre 𝒰 k j) (cfg.pbTubeFibre 𝒰 k j')
    intro j hj j' hj' hjj'
    rw [Finset.disjoint_left]
    intro i hij hij'
    have hj_eq : 𝒰.assign k i = j := by
      simp only [pbTubeFibre, Tube.coverClass, Finset.mem_filter] at hij
      exact hij.2
    have hj'_eq : 𝒰.assign k i = j' := by
      simp only [pbTubeFibre, Tube.coverClass, Finset.mem_filter] at hij'
      exact hij'.2
    exact hjj' (hj_eq.symm.trans hj'_eq)
  · apply Finset.Subset.antisymm
    · intro i hi
      rcases Finset.mem_biUnion.mp hi with ⟨j, hj, hji⟩
      exact pbTubeFibre_subset cfg 𝒰 k j hji
    · exact hcov

open scoped Classical in
/-- **The fibre count at the hierarchy constant** (GWZ Def 2.1(iii)), over
`Tube.PartitionBrackets`: `|𝕋_ρ| · |𝕋[T_ρ]| ≤ Cu² |𝕋|`. The statement and proof of
`Kakeya.VeryNotSticky.card_indexSet_mul_card_tubeFibre_le` verbatim — it reads only
`card_class_le`, `le_card_class` and the partition. This is what populates the field
`Kakeya.VeryNotSticky.SplitInputs.fibreCount` once that field's hierarchy is loose. -/
theorem pbCard_indexSet_mul_card_tubeFibre_le (cfg : VeryNotSticky) {N : ℕ} {Cu : NNReal}
    (uniform : Tube.PartitionBrackets cfg.s N Cu) (k : ℕ)
    (hk : k ≤ N) :
    ∀ j ∈ uniform.indexSet k,
      ((uniform.indexSet k).card : ℝ) * ((cfg.pbTubeFibre uniform k j).card : ℝ) ≤
        ((Cu : ℝ) ^ 2) * (cfg.s.card : ℝ) := by
  intro j hj
  have hpart : (cfg.s.card : ℝ) =
      ∑ j' ∈ uniform.indexSet k, ((cfg.pbTubeFibre uniform k j').card : ℝ) := by
    have h := Finset.card_eq_sum_card_fiberwise (s := cfg.s) (t := uniform.indexSet k)
      (f := uniform.assign k) (fun i hi => uniform.assign_mem k hk i hi)
    rw [h]
    push_cast
    refine Finset.sum_congr rfl fun j' _ => ?_
    congr 2
  have hup : ((cfg.pbTubeFibre uniform k j).card : ℝ) ≤ (Cu : ℝ) * (uniform.branchingN k : ℝ) := by
    have h := uniform.card_class_le k hk j hj
    exact_mod_cast h
  have hlo : ∀ j' ∈ uniform.indexSet k,
      (uniform.branchingN k : ℝ) ≤ (Cu : ℝ) * ((cfg.pbTubeFibre uniform k j').card : ℝ) := by
    intro j' hj'
    have h := uniform.le_card_class k hk j' hj'
    exact_mod_cast h
  have hsum : ((uniform.indexSet k).card : ℝ) * (uniform.branchingN k : ℝ) ≤
      (Cu : ℝ) * (cfg.s.card : ℝ) := by
    rw [hpart, Finset.mul_sum]
    have := Finset.sum_le_sum hlo
    simpa [Finset.sum_const, nsmul_eq_mul] using this
  have hCu : (0 : ℝ) ≤ (Cu : ℝ) := NNReal.coe_nonneg _
  have hidx : (0 : ℝ) ≤ ((uniform.indexSet k).card : ℝ) := Nat.cast_nonneg _
  calc ((uniform.indexSet k).card : ℝ) * ((cfg.pbTubeFibre uniform k j).card : ℝ)
      ≤ ((uniform.indexSet k).card : ℝ) * ((Cu : ℝ) * (uniform.branchingN k : ℝ)) :=
        mul_le_mul_of_nonneg_left hup hidx
    _ = (Cu : ℝ) * (((uniform.indexSet k).card : ℝ) * (uniform.branchingN k : ℝ)) := by
        ring
    _ ≤ (Cu : ℝ) * ((Cu : ℝ) * (cfg.s.card : ℝ)) := mul_le_mul_of_nonneg_left hsum hCu
    _ = (Cu : ℝ) ^ 2 * (cfg.s.card : ℝ) := by ring

open scoped Classical in
/-- **The hierarchy constant is at least one once some class is nonempty**, over
`Tube.PartitionBrackets`. Statement and proof of
`Kakeya.VeryNotSticky.one_le_sq_of_mem_activeTubeNodes` verbatim. -/
theorem pbOne_le_sq_of_mem_activeTubeNodes (cfg : VeryNotSticky) {N : ℕ} {Cu : NNReal}
    (uniform : Tube.PartitionBrackets cfg.s N Cu) {k : ℕ}
    (hk : k ≤ N) {j : cfg.ι} (hj : j ∈ cfg.pbActiveTubeNodes uniform k) : 1 ≤ Cu ^ 2 := by
  have hjIdx : j ∈ uniform.indexSet k := (Finset.mem_filter.mp hj).1
  have hne : (cfg.pbTubeFibre uniform k j).Nonempty := (Finset.mem_filter.mp hj).2
  have hpos : (0 : NNReal) < ((cfg.pbTubeFibre uniform k j).card : NNReal) := by
    exact_mod_cast Finset.card_pos.mpr hne
  have hup : ((cfg.pbTubeFibre uniform k j).card : NNReal) ≤ Cu * uniform.branchingN k := by
    simpa [pbTubeFibre] using uniform.card_class_le k hk j hjIdx
  have hlo : uniform.branchingN k ≤ Cu * ((cfg.pbTubeFibre uniform k j).card : NNReal) := by
    simpa [pbTubeFibre] using uniform.le_card_class k hk j hjIdx
  have h : 1 * ((cfg.pbTubeFibre uniform k j).card : NNReal) ≤
      Cu ^ 2 * ((cfg.pbTubeFibre uniform k j).card : NNReal) := by
    calc
      1 * ((cfg.pbTubeFibre uniform k j).card : NNReal)
          = ((cfg.pbTubeFibre uniform k j).card : NNReal) := one_mul _
      _ ≤ Cu * uniform.branchingN k := hup
      _ ≤ Cu * (Cu * ((cfg.pbTubeFibre uniform k j).card : NNReal)) :=
          mul_le_mul_of_nonneg_left hlo (by positivity)
      _ = Cu ^ 2 * ((cfg.pbTubeFibre uniform k j).card : NNReal) := by ring
  exact le_of_mul_le_mul_right h hpos

/-- **Some `ρ₂*`-fibre is full** (blueprint `lem:ml2nonslabFullFibre`), over
`Tube.PartitionBrackets`. Statement and proof of
`Kakeya.VeryNotSticky.exists_full_fibre` verbatim: mediant selection over the partition, which
needs no geometry of the nodes. -/
theorem pbExists_full_fibre (cfg : VeryNotSticky) {N : ℕ} {C₀ C : NNReal}
    (𝒰 : Tube.PartitionBrackets cfg.s N C)
    (k : ℕ) (hk : k ≤ N)
    (hscale_ge : cfg.rho2Star C₀ ≤ Tube.gridScale cfg.δ N k)
    (hscale_le : Tube.gridScale cfg.δ N k ≤ cfg.δ ^ (-cfg.η) * cfg.rho2Star C₀)
    (hs : cfg.s.Nonempty) :
    ∃ j ∈ cfg.pbActiveTubeNodes 𝒰 k,
      fullness cfg.s (fun i ↦ (cfg.T i).toShadedBody) ≤
          fullness (cfg.pbTubeFibre 𝒰 k j) (fun i ↦ (cfg.T i).toShadedBody) ∧
        cfg.δ ^ (2 * cfg.η) ≤
          fullness (cfg.pbTubeFibre 𝒰 k j) (fun i ↦ (cfg.T i).toShadedBody) := by
  classical
  let V : cfg.ι → ShadedBody (EuclideanSpace ℝ (Fin 3)) := fun i ↦ (cfg.T i).toShadedBody
  let p : cfg.ι → ENNReal := fun j ↦ ∑ i ∈ cfg.pbTubeFibre 𝒰 k j, volume (V i).shade
  let q : cfg.ι → ENNReal := fun j ↦ ∑ i ∈ cfg.pbTubeFibre 𝒰 k j, volume (V i).carrier
  rcases pbNonslabFibrePartition cfg 𝒰 k hk hscale_ge hscale_le hs with ⟨hne, hdisj, hbUnion⟩
  -- `λ(𝕋, Y) = (∑ p) / (∑ q)`, by fullness over the partition.
  let J := cfg.pbActiveTubeNodes 𝒰 k
  have hfull'_s : fullness' cfg.s V =
      (∑ j ∈ J, p j) / (∑ j ∈ J, q j) := by
    have hb := ShadedBody.fullness'_biUnion (J := J)
      (f := cfg.pbTubeFibre 𝒰 k) V hdisj
    rw [hbUnion] at hb
    simpa [p, q] using hb
  -- Each `q j` is nonzero and finite.
  have hq0 : ∀ j ∈ J, q j ≠ 0 := by
    intro j hj
    have hfib_nonempty : (cfg.pbTubeFibre 𝒰 k j).Nonempty := by
      simp only [J, pbActiveTubeNodes, Finset.mem_filter] at hj
      exact hj.2
    obtain ⟨i0, hi0⟩ := hfib_nonempty
    have hpos : volume (V i0).carrier ≠ 0 := by
      change volume (cfg.T i0).carrier ≠ 0
      set n := Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) with hn
      have hLpos : (Tube.le_volume.c n : ENNReal) * (cfg.δ : ENNReal) ^ (n - 1) ≠ 0 :=
        mul_ne_zero (by exact_mod_cast (Tube.le_volume.c_pos n).ne')
          (pow_ne_zero _ (by exact_mod_cast cfg.hδ.ne'))
      exact (lt_of_lt_of_le (pos_iff_ne_zero.mpr hLpos) (Tube.le_volume (cfg.T i0).toTube)).ne'
    dsimp [q]
    intro hqj
    apply hpos
    have hle : volume (V i0).carrier ≤ (∑ i ∈ cfg.pbTubeFibre 𝒰 k j, volume (V i).carrier) := by
      exact Finset.single_le_sum (fun x _ => (zero_le : 0 ≤ volume (V x).carrier)) hi0
    exact le_antisymm (by simpa [hqj] using hle) (zero_le : 0 ≤ volume (V i0).carrier)
  have hqtop : ∀ j ∈ J, q j ≠ ⊤ := by
    intro j hj
    dsimp [q]
    exact (ENNReal.sum_ne_top (s := cfg.pbTubeFibre 𝒰 k j) (f := fun i => volume (V i).carrier)).2
      (by
        intro i hi
        change volume (cfg.T i).carrier ≠ ⊤
        exact (cfg.T i).isCompact.measure_lt_top.ne)
  -- Mediant selection gives a fibre at least as full as 𝕋.
  rcases exists_sum_div_sum_le hne p q hq0 hqtop with ⟨j, hj, hle⟩
  have hfull'_le : fullness' cfg.s V ≤ fullness' (cfg.pbTubeFibre 𝒰 k j) V := by
    calc
      fullness' cfg.s V =
          (∑ j ∈ J, p j) / (∑ j ∈ J, q j) := hfull'_s
      _ ≤ p j / q j := hle
      _ = fullness' (cfg.pbTubeFibre 𝒰 k j) V := rfl
  have hfull : fullness cfg.s V ≤ fullness (cfg.pbTubeFibre 𝒰 k j) V := by
    have hcoe : (fullness cfg.s V : ENNReal) ≤ (fullness (cfg.pbTubeFibre 𝒰 k j) V : ENNReal) := by
      rw [coe_fullness (s := cfg.s) (V := V), coe_fullness (s := cfg.pbTubeFibre 𝒰 k j) (V := V)]
      exact hfull'_le
    exact ENNReal.coe_le_coe.1 hcoe
  refine ⟨j, hj, ?_, ?_⟩
  · exact hfull
  · have hge : cfg.δ ^ (2 * cfg.η) ≤ fullness cfg.s V := by
      simpa [V] using cfg.fullness_ge
    exact hge.trans hfull

/-! ### The existing exact statements are the special case -/

/-- The existing `Kakeya.VeryNotSticky.tubeFibre` is `pbTubeFibre` at the brackets of the exact
hierarchy, definitionally. This is the tripwire for the retyping F-R18-2: if either definition
moves, it stops being `rfl`. -/
lemma tubeFibre_eq_pbTubeFibre (cfg : VeryNotSticky) {N : ℕ} {C : NNReal}
    (𝒰 : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube) N C) (k : ℕ) (j : cfg.ι) :
    cfg.tubeFibre 𝒰 k j = cfg.pbTubeFibre 𝒰.toPartitionBrackets k j := rfl

/-- Likewise for the active nodes. -/
lemma activeTubeNodes_eq_pbActiveTubeNodes (cfg : VeryNotSticky) {N : ℕ} {C : NNReal}
    (𝒰 : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube) N C) (k : ℕ) :
    cfg.activeTubeNodes 𝒰 k = cfg.pbActiveTubeNodes 𝒰.toPartitionBrackets k := rfl

end VeryNotSticky

end Kakeya
