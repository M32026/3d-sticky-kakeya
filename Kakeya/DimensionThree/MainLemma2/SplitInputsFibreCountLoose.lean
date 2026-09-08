/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.SplitInputsFibreCount
public import Kakeya.DimensionThree.MainLemma2.LooseUniform

/-!
# R18-T3: conjunct 5 of `SideDataObligations` re-proved over the LOOSE hierarchy

A loose hierarchy requires a corresponding version of conjunct 5 of
`Kakeya.VeryNotSticky.SideDataObligations`, because the existing producer leaf
`MainLemma2/SplitInputsFibreCount.lean` reads three fields the loose structures of
`MainLemma2/LooseUniform.lean` do not carry. This file is the loose re-proof, so that the
rewire costs nothing already banked.

Nothing existing is edited: every declaration here is new and sits beside its exact twin.
-/

@[expose] public section

open Filter Topology MeasureTheory Metric Set
open scoped NNReal ENNReal

namespace Kakeya.VeryNotSticky

universe u

/-! ### Part A — the bracket half: no geometry is read at all

`Kakeya.VeryNotSticky.card_indexSet_mul_branchingN_le` reads only `assign_mem` and
`le_card_class`, both of which are fields of `Tube.PartitionBrackets`. So it is a theorem of
the brackets, common to the exact and the loose hierarchy, and the existing exact statement is
its instance at `Tube.UniformTubeSet.toPartitionBrackets` by `rfl`. -/

section BracketHalf

variable {ι : Type u}

/-- **The branching number against the node count, over `Tube.PartitionBrackets`.**
The bracket-only twin of `Kakeya.VeryNotSticky.card_indexSet_mul_branchingN_le`. -/
theorem pbCard_indexSet_mul_branchingN_le {sPar : Finset ι} {N : ℕ} {C : NNReal}
    (brk : Tube.PartitionBrackets sPar N C) {k : ℕ} (hk : k ≤ N) :
    ((brk.indexSet k).card : NNReal) * brk.branchingN k ≤ C * (sPar.card : NNReal) := by
  classical
  have hmem : ∀ i ∈ sPar, brk.assign k i ∈ brk.indexSet k :=
    fun i hi => brk.assign_mem k hk i hi
  calc ((brk.indexSet k).card : NNReal) * brk.branchingN k
      = ∑ _j ∈ brk.indexSet k, brk.branchingN k := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ j ∈ brk.indexSet k,
          C * ((Tube.coverClass sPar (brk.assign k) j).card : NNReal) :=
        Finset.sum_le_sum fun j hj => brk.le_card_class k hk j hj
    _ = C * ∑ j ∈ brk.indexSet k,
          ((Tube.coverClass sPar (brk.assign k) j).card : NNReal) := by
        rw [Finset.mul_sum]
    _ = C * (sPar.card : NNReal) := by
        congr 1
        rw [show ∑ j ∈ brk.indexSet k,
              ((Tube.coverClass sPar (brk.assign k) j).card : NNReal)
            = ((∑ j ∈ brk.indexSet k,
              (Tube.coverClass sPar (brk.assign k) j).card : ℕ) : NNReal) from by
          push_cast; ring]
        rw [sum_card_coverClass sPar (brk.assign k) (brk.indexSet k) hmem]

/-- **The `rfl` bridge.** The existing exact statement
`Kakeya.VeryNotSticky.card_indexSet_mul_branchingN_le` is the bracket twin read at
`Tube.UniformTubeSet.toPartitionBrackets`: the term below type-checks with no rewriting, so no
geometry was ever involved and the loose hierarchy inherits it through
`Kakeya.LooseUniform.LooseUniformTubeSet.toPartitionBrackets`. -/
theorem card_indexSet_mul_branchingN_le_of_pb {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [Nontrivial E] {δ : NNReal} {sPar : Finset ι} {T : ι → Tube δ E} {N : ℕ} {C : NNReal}
    (𝒰 : Tube.UniformTubeSet sPar T N C) {k : ℕ} (hk : k ≤ N) :
    ((𝒰.cover.indexSet k).card : NNReal) * 𝒰.branchingN k ≤ C * (sPar.card : NNReal) :=
  pbCard_indexSet_mul_branchingN_le 𝒰.toPartitionBrackets hk

/-- The same statement for the **loose** hierarchy, through the same bracket twin. -/
theorem looseCard_indexSet_mul_branchingN_le {δ : NNReal} {sPar : Finset ι}
    {T : ι → Tube δ (EuclideanSpace ℝ (Fin 3))} {N : ℕ} {K : ℝ} {C : NNReal}
    (𝒰 : LooseUniform.LooseUniformTubeSet sPar T N K C) {k : ℕ} (hk : k ≤ N) :
    ((𝒰.cover.indexSet k).card : NNReal) * 𝒰.branchingN k ≤ C * (sPar.card : NNReal) :=
  pbCard_indexSet_mul_branchingN_le 𝒰.toPartitionBrackets hk

end BracketHalf

/-! ### Part B — the geometry half, read #1 and read #3

`Kakeya.VeryNotSticky.card_filter_le_of_uniform` reads `Tube.UniformTubeSet.boundedOverlap`
(read #1) and `Tube.GridCoverSystem.le_tube_assign` (read #3). The loose structures carry
`Kakeya.LooseUniform.LooseUniformTubeSet.boundedOverlapDil` and
`Kakeya.LooseUniform.LooseGridCoverSystem.le_dilate_tube_assign` instead, both against a
dilate. Both reads survive, at the price of one monotonicity of the dilation ratio. -/

section LooseOverlap

variable {ι : Type u}

/-- **Monotonicity of a dilate in its ratio.** The special case `σ = ρ`, `W = V` of
`Kakeya.VeryNotSticky.dilate_subset_dilate_of_core_eq`, packaged at the level of
`ConvexSpaceBody`. -/
theorem dilate_le_dilate_of_ratio_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {ρ : NNReal} (V : Tube ρ E) {c c' : ℝ} (hc : 0 < c) (hcc' : c ≤ c') :
    Kakeya.Tube.dilate V c ≤ Kakeya.Tube.dilate V c' := by
  intro x hx
  exact dilate_subset_dilate_of_core_eq V V rfl rfl hc hcc'
    (by have : (0:ℝ) ≤ (ρ : ℝ) := ρ.coe_nonneg; nlinarith) hx

/-- **The class bound for a loose hierarchy.** A *loose* hierarchy at the constant
`C` bounds the members of the family lying in the `c`-dilate of any `ρ_k`-tube, for every
`c ≤ K + 4`, by `C · (C · N_k)`.

This is `Kakeya.VeryNotSticky.card_filter_le_of_uniform` with the two geometry reads replaced:
`Tube.UniformTubeSet.boundedOverlap` by
`Kakeya.LooseUniform.LooseUniformTubeSet.boundedOverlapDil` — whose filter predicate is stated
against the `(K+4)`-dilate and does **not** mention the node tube at all, so read #2
(`cover.tube`) disappears from this lemma — and the containment of a member in its node by
`Kakeya.LooseUniform.LooseGridCoverSystem.assign_mem` alone.

The hypothesis `c ≤ K + 4` is the whole cost: the loose bounded-overlap field counts against
the `(K+4)`-dilate, so any container the consumer presents must sit inside it. Both consumers
present a container at `c = K`. -/
theorem card_filter_le_of_looseUniform {δ : NNReal} {sPar : Finset ι}
    {T : ι → Tube δ (EuclideanSpace ℝ (Fin 3))} {N : ℕ} {K : ℝ} {C : NNReal}
    (𝒰 : LooseUniform.LooseUniformTubeSet sPar T N K C)
    {k : ℕ} (hk : k ≤ N) (V : Tube (Tube.gridScale δ N k) (EuclideanSpace ℝ (Fin 3)))
    {c : ℝ} (hc : 0 < c) (hcK : c ≤ K + 4) :
    (((sPar.filter (fun i => (T i).toConvexSpaceBody ≤ Kakeya.Tube.dilate V c)).card : NNReal))
      ≤ C * (C * 𝒰.branchingN k) := by
  classical
  set F : Finset ι := (𝒰.cover.indexSet k).filter (fun j => ∃ i ∈ sPar,
    𝒰.cover.assign k i = j ∧
      (T i).toConvexSpaceBody ≤ Kakeya.Tube.dilate V (K + 4)) with hF
  have hFcard : (F.card : NNReal) ≤ C := by
    have := 𝒰.boundedOverlapDil k hk V
    simpa [hF] using this
  have hsub : sPar.filter (fun i => (T i).toConvexSpaceBody ≤ Kakeya.Tube.dilate V c) ⊆
      F.biUnion (fun j => Tube.coverClass sPar (𝒰.cover.assign k) j) := by
    intro i hi
    simp only [Finset.mem_filter] at hi
    obtain ⟨hiS, hiV⟩ := hi
    have hiV' : (T i).toConvexSpaceBody ≤ Kakeya.Tube.dilate V (K + 4) :=
      le_trans hiV (dilate_le_dilate_of_ratio_le V hc hcK)
    refine Finset.mem_biUnion.2 ⟨𝒰.cover.assign k i, ?_, ?_⟩
    · simp only [hF, Finset.mem_filter]
      exact ⟨𝒰.cover.assign_mem k hk i hiS, i, hiS, rfl, hiV'⟩
    · simp [Tube.coverClass, hiS]
  have hcard1 :
      (sPar.filter (fun i => (T i).toConvexSpaceBody ≤ Kakeya.Tube.dilate V c)).card
        ≤ ∑ j ∈ F, (Tube.coverClass sPar (𝒰.cover.assign k) j).card :=
    le_trans (Finset.card_le_card hsub) (Finset.card_biUnion_le)
  have hcast : (((sPar.filter
        (fun i => (T i).toConvexSpaceBody ≤ Kakeya.Tube.dilate V c)).card : NNReal))
      ≤ ∑ j ∈ F, ((Tube.coverClass sPar (𝒰.cover.assign k) j).card : NNReal) := by
    exact_mod_cast hcard1
  refine hcast.trans ?_
  have hterm : ∀ j ∈ F, ((Tube.coverClass sPar (𝒰.cover.assign k) j).card : NNReal)
      ≤ C * 𝒰.branchingN k := by
    intro j hj
    have hjidx : j ∈ 𝒰.cover.indexSet k := by
      simp only [hF, Finset.mem_filter] at hj; exact hj.1
    exact 𝒰.card_class_le k hk j hjidx
  calc ∑ j ∈ F, ((Tube.coverClass sPar (𝒰.cover.assign k) j).card : NNReal)
      ≤ ∑ _j ∈ F, C * 𝒰.branchingN k := Finset.sum_le_sum hterm
    _ = (F.card : NNReal) * (C * 𝒰.branchingN k) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ C * (C * 𝒰.branchingN k) := by
        gcongr

end LooseOverlap

/-! ### Part D — step 2 of the chain, fully loose (reads #1, #2 and #3 together)

`Kakeya.VeryNotSticky.card_indexSet_parent_le` reads `cover.tube` (read #2) on the *family's*
hierarchy and `le_tube_assign` (read #3) on both. Read #2 survives verbatim:
`Kakeya.LooseUniform.LooseGridCoverSystem` **does** carry a `tube` field, of exactly the exact
type `(k : ℕ) → ι → Tube (Tube.gridScale δ N k) E3`; what the loose model drops is
`tube_nested`, not `tube`. Read #3 is replaced by `le_dilate_tube_assign`, and the resulting
`K`-dilate is exactly the container `Kakeya.VeryNotSticky.card_filter_le_of_looseUniform`
accepts. -/

section LooseChaining

set_option linter.unusedSectionVars false

variable {ι : Type u}

/-- **Comparison of loose parent and family hierarchies.** With both hierarchies loose —
the parent at `(Kpar, Cpar)`, the family at `(Ks, C₀)` — and the cardinality retention
`c |sPar| ≤ |s|`, the parent's level-`k` nodes are at most `Cpar³/c` times the family's, the
*same* constant as `Kakeya.VeryNotSticky.card_indexSet_parent_le`.

The only new hypothesis is `hKs : Ks ≤ Kpar + 4`: the family's node-dilate has to fit inside
the container the parent's loose bounded overlap counts against. At a common `K` it is free. -/
theorem card_indexSet_parent_le_loose {δ : NNReal} {s sPar : Finset ι}
    {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))} {N : ℕ} {Kpar Ks : ℝ} {Cpar C₀ : NNReal}
    (𝒰par : LooseUniform.LooseUniformTubeSet sPar (fun i ↦ (T i).toTube) N Kpar Cpar)
    (𝒰s : LooseUniform.LooseUniformTubeSet s (fun i ↦ (T i).toTube) N Ks C₀)
    (hKs : 0 < Ks) (hKsKpar : Ks ≤ Kpar + 4)
    (hsub : s ⊆ sPar) (hne : sPar.Nonempty) {k : ℕ} (hk : k ≤ N)
    {c : NNReal} (hret : c * (sPar.card : NNReal) ≤ (s.card : NNReal)) :
    c * ((𝒰par.cover.indexSet k).card : NNReal)
      ≤ Cpar ^ 3 * ((𝒰s.cover.indexSet k).card : NNReal) := by
  classical
  set idxP : Finset ι := 𝒰par.cover.indexSet k with hidxP
  set idxS : Finset ι := 𝒰s.cover.indexSet k with hidxS
  set Nk : NNReal := 𝒰par.branchingN k with hNk
  have hs_le : (s.card : NNReal) ≤ (idxS.card : NNReal) * (Cpar * (Cpar * Nk)) := by
    have hmem : ∀ i ∈ s, 𝒰s.cover.assign k i ∈ idxS :=
      fun i hi => 𝒰s.cover.assign_mem k hk i hi
    have hsum := sum_card_coverClass s (𝒰s.cover.assign k) idxS hmem
    have hclass : ∀ j ∈ idxS,
        ((Tube.coverClass s (𝒰s.cover.assign k) j).card : NNReal) ≤ Cpar * (Cpar * Nk) := by
      intro j hj
      refine le_trans ?_
        (card_filter_le_of_looseUniform 𝒰par hk (𝒰s.cover.tube k j) hKs hKsKpar)
      refine Nat.cast_le.2 (Finset.card_le_card ?_)
      intro i hi
      simp only [Tube.coverClass, Finset.mem_filter] at hi
      simp only [Finset.mem_filter]
      refine ⟨hsub hi.1, ?_⟩
      have := 𝒰s.cover.le_dilate_tube_assign k hk i hi.1
      rwa [hi.2] at this
    calc (s.card : NNReal)
        = ((∑ j ∈ idxS, (Tube.coverClass s (𝒰s.cover.assign k) j).card : ℕ) : NNReal) := by
          rw [hsum]
      _ = ∑ j ∈ idxS, ((Tube.coverClass s (𝒰s.cover.assign k) j).card : NNReal) := by
          push_cast; ring
      _ ≤ ∑ _j ∈ idxS, Cpar * (Cpar * Nk) := Finset.sum_le_sum hclass
      _ = (idxS.card : NNReal) * (Cpar * (Cpar * Nk)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hpar : (idxP.card : NNReal) * Nk ≤ Cpar * (sPar.card : NNReal) :=
    looseCard_indexSet_mul_branchingN_le 𝒰par hk
  have hkey : c * (idxP.card : NNReal) * (sPar.card : NNReal)
      ≤ Cpar ^ 3 * (idxS.card : NNReal) * (sPar.card : NNReal) := by
    calc c * (idxP.card : NNReal) * (sPar.card : NNReal)
        = (idxP.card : NNReal) * (c * (sPar.card : NNReal)) := by ring
      _ ≤ (idxP.card : NNReal) * (s.card : NNReal) := by gcongr
      _ ≤ (idxP.card : NNReal) * ((idxS.card : NNReal) * (Cpar * (Cpar * Nk))) := by gcongr
      _ = (idxS.card : NNReal) * Cpar ^ 2 * ((idxP.card : NNReal) * Nk) := by ring
      _ ≤ (idxS.card : NNReal) * Cpar ^ 2 * (Cpar * (sPar.card : NNReal)) := by gcongr
      _ = Cpar ^ 3 * (idxS.card : NNReal) * (sPar.card : NNReal) := by ring
  have hpos : (0 : NNReal) < (sPar.card : NNReal) := by
    have : 0 < sPar.card := Finset.card_pos.2 hne
    exact_mod_cast this
  exact le_of_mul_le_mul_right hkey hpos

end LooseChaining

/-! ### Part C — step 1 of the chain: the cross-scale packing count, in the loose model

This comparison contributes the cross-scale packing loss. The existing
`Kakeya.VeryNotSticky.card_count_le_mul_card_indexSet` reads read #2 (`cover.tube`) and read #3
(`le_tube_assign`) and then spends the *exact* containment on a **chord argument**: the member's
`δ`-tube lies inside the node, so a chord of the member is a chord of the node, and
`Tube.norm_perp_direction_le_of_chord` pins the `ρ₂`-tube's direction to the node's.

In the loose model the member lies only in the `K`-dilate of the node, and the chord argument
is unavailable there: `Tube.norm_perp_direction_le_of_chord` and
`Tube.subset_dilate_of_norm_perp_direction_le` both want their two points in the node's
*carrier*. (The dilated forms exist only as `Kakeya.ml1Boot.norm_perp_direction_le_of_chord_dilate`
and `Kakeya.ml1Boot.subset_dilate_of_norm_perp_direction_le_dilate`, a ~540-line chain in
`MainLemma1/Rescaling/CoarseDensity.lean` that is Section 8's territory and deliberately outside
this module's import closure.)

**The loose model does not need them.** Its `dir_close_tube_assign` field carries the direction
pinning outright — that is precisely the information the exact model has to earn by a chord —
and `Kakeya.VeryNotSticky.norm_perp_le_of_dir_close` transports it from the member to the
`ρ₂`-tube. The containment into a common dilate is then a direct axial/transverse computation
(`Kakeya.VeryNotSticky.carrier_subset_dilate_of_dir_close`), with **no** side condition of the
form `K ρ ≤ 1` that the pinned-dilate route would have imposed. The ratio comes out
`(3K+60) ρ_k/ρ₂` against the exact model's `32 ρ_k/ρ₂`: the same single power of `ρ_k/ρ₂`, which
is what keeps the constant inside `δ^{-O(η)}`. -/

/-- **The perp transfer, read #2's replacement in the loose model.** If `g` is within `a` of
`±e` and the transverse part of `f` with respect to `g` is at most `b`, then the transverse part
of `f` with respect to `e` is at most `b + 2a`.

This is what makes the loose cross-scale packing work at all: the exact model recovers the
direction of a node from a *chord* of the member inside the node, which a `K`-dilate destroys;
the loose model carries the direction pinning as the field
`Kakeya.LooseUniform.LooseGridCoverSystem.dir_close_tube_assign` instead, and this lemma
transports it from the member to the `ρ₂`-tube that contains the member. Pure linear algebra:
no angle, no case split, no side condition. -/
theorem norm_perp_le_of_dir_close {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {e g f : E} (he : ‖e‖ = 1) (hg : ‖g‖ = 1) (hf : ‖f‖ = 1)
    {σ : ℝ} (hσ : |σ| = 1) {a b : ℝ}
    (hge : ‖g - σ • e‖ ≤ a)
    (hgf : ‖f - inner ℝ g f • g‖ ≤ b) :
    ‖f - inner ℝ e f • e‖ ≤ b + 2 * a := by
  have hσ2 : σ * σ = 1 := by
    rcases abs_eq (by norm_num : (0:ℝ) ≤ 1) |>.1 hσ with h | h <;> rw [h] <;> norm_num
  set e' : E := σ • e with he'
  have he'n : ‖e'‖ = 1 := by rw [he', norm_smul, Real.norm_eq_abs, hσ, he]; norm_num
  have hkey : f - inner ℝ e f • e = f - inner ℝ e' f • e' := by
    rw [he', real_inner_smul_left, smul_smul]
    congr 2
    have h : σ * (inner ℝ e f : ℝ) * σ = (σ * σ) * (inner ℝ e f : ℝ) := by ring
    rw [h, hσ2, one_mul]
  rw [hkey]
  have hdecomp : f - inner ℝ e' f • e'
      = (f - inner ℝ g f • g) + ((inner ℝ g f : ℝ) • (g - e') + (inner ℝ (g - e') f : ℝ) • e') := by
    rw [inner_sub_left]
    module
  rw [hdecomp]
  have h1 : |(inner ℝ g f : ℝ)| ≤ 1 := by
    have := abs_real_inner_le_norm g f
    rw [hg, hf] at this; simpa using this
  have h2 : |(inner ℝ (g - e') f : ℝ)| ≤ a := by
    have := abs_real_inner_le_norm (g - e') f
    rw [hf, mul_one] at this
    exact this.trans hge
  have hb1 : ‖(inner ℝ g f : ℝ) • (g - e')‖ ≤ a := by
    rw [norm_smul, Real.norm_eq_abs]
    have h0 : (0:ℝ) ≤ ‖g - e'‖ := norm_nonneg _
    have ha0 : (0:ℝ) ≤ a := le_trans h0 hge
    calc |(inner ℝ g f : ℝ)| * ‖g - e'‖ ≤ 1 * ‖g - e'‖ := by gcongr
      _ = ‖g - e'‖ := one_mul _
      _ ≤ a := hge
  have hb2 : ‖(inner ℝ (g - e') f : ℝ) • e'‖ ≤ a := by
    rw [norm_smul, Real.norm_eq_abs, he'n, mul_one]
    exact h2
  calc ‖(f - inner ℝ g f • g) + ((inner ℝ g f : ℝ) • (g - e') + (inner ℝ (g - e') f : ℝ) • e')‖
      ≤ ‖f - inner ℝ g f • g‖
          + ‖(inner ℝ g f : ℝ) • (g - e') + (inner ℝ (g - e') f : ℝ) • e'‖ := norm_add_le _ _
    _ ≤ b + (a + a) := by
        refine add_le_add hgf ((norm_add_le _ _).trans (add_le_add hb1 hb2))
    _ = b + 2 * a := by ring



/-- The transverse part of a vector has norm at most twice the vector's. (The sharp bound is
`‖y‖`; twice is all that is needed and it avoids a square-root argument.) -/
theorem norm_perp_le_two_mul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {e : E} (he : ‖e‖ = 1) (y : E) : ‖y - inner ℝ e y • e‖ ≤ 2 * ‖y‖ := by
  have h1 : |(inner ℝ e y : ℝ)| ≤ ‖y‖ := by
    have := abs_real_inner_le_norm e y
    rw [he, one_mul] at this; exact this
  calc ‖y - inner ℝ e y • e‖ ≤ ‖y‖ + ‖(inner ℝ e y : ℝ) • e‖ := norm_sub_le _ _
    _ = ‖y‖ + |(inner ℝ e y : ℝ)| * ‖e‖ := by rw [norm_smul, Real.norm_eq_abs]
    _ = ‖y‖ + |(inner ℝ e y : ℝ)| := by rw [he, mul_one]
    _ ≤ ‖y‖ + ‖y‖ := by gcongr
    _ = 2 * ‖y‖ := by ring

/-- **The loose container.** A `σ`-tube `U` that meets the `K`-dilate of a `ρ`-tube `V` in a
point and whose direction is transverse to `V`'s by at most `16 ρ` lies in the
`((3K+60) ρ/σ)`-dilate of the coaxial `σ`-tube of `V`. -/
theorem carrier_subset_dilate_of_dir_close {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [Nontrivial E] [ProperSpace E]
    {ρ σ : NNReal} (V : Tube ρ E) (U : Tube σ E)
    {K : ℝ} (hK : 1 ≤ K) (hσ0 : 0 < σ) (hσρ : (σ : ℝ) ≤ (ρ : ℝ)) (hρ1 : (ρ : ℝ) ≤ 1)
    {p : E} (hpU : p ∈ U.carrier) (hpV : p ∈ (Kakeya.Tube.dilate V K).carrier)
    {a : ℝ} (ha : ‖U.direction - inner ℝ V.direction U.direction • V.direction‖ ≤ a)
    (ha16 : a ≤ 16 * (ρ : ℝ)) :
    U.carrier ⊆ (Kakeya.Tube.dilate
      (Tube.ofMidpointDirection σ V.center V.direction V.norm_direction)
      ((3 * K + 60) * (ρ : ℝ) / (σ : ℝ))).carrier := by
  have hσ0R : (0 : ℝ) < (σ : ℝ) := NNReal.coe_pos.2 hσ0
  have hσ1 : (σ : ℝ) ≤ 1 := le_trans hσρ hρ1
  have hK0 : (0 : ℝ) < K := lt_of_lt_of_le zero_lt_one hK
  set e : E := V.direction with hedef
  have he : ‖e‖ = 1 := V.norm_direction
  set V' : Tube σ E := Tube.ofMidpointDirection σ V.center V.direction V.norm_direction with hV'
  have hV'x : V'.x = V.x := by
    rw [hV', Tube.ofMidpointDirection_x, V.x_eq_center_sub]; norm_num
  have hV'y : V'.y = V.y := by
    rw [hV', Tube.ofMidpointDirection_y, V.y_eq_center_add]; norm_num
  have hV'ctr : V'.center = V.center := by simp only [Tube.center, hV'x, hV'y]
  have hV'dir : V'.direction = e := by simp only [Tube.direction, hV'x, hV'y, hedef]
  set c : ℝ := (3 * K + 60) * (ρ : ℝ) / (σ : ℝ) with hc
  have hratio : (1 : ℝ) ≤ (ρ : ℝ) / (σ : ℝ) := by
    rw [le_div_iff₀ hσ0R]; linarith
  have hc0 : (0 : ℝ) < c := by
    rw [hc, mul_div_assoc]
    have : (0 : ℝ) < 3 * K + 60 := by linarith
    positivity
  -- the point `p` in the dilate of `V`
  have hpVd := Tube.abs_inner_and_perp_le_of_mem_dilate V hK0 hpV
  -- the tube `U` read at ratio one
  have hone : ∀ z ∈ U.carrier,
      |(inner ℝ (z - U.center) U.direction : ℝ)| ≤ 1 / 2 + 1 * (σ : ℝ) ∧
        ‖z - U.center - inner ℝ U.direction (z - U.center) • U.direction‖ ≤ 1 * (σ : ℝ) := by
    intro z hz
    exact Tube.abs_inner_and_perp_le_of_mem_dilate U one_pos
      (Tube.subset_dilate U le_rfl hz)
  intro x hx
  obtain ⟨hxa, hxw⟩ := hone x hx
  obtain ⟨hpa, hpw⟩ := hone p hpU
  set fU : E := U.direction with hfU
  have hfUn : ‖fU‖ = 1 := U.norm_direction
  set tx : ℝ := inner ℝ fU (x - U.center) with htx
  set tp : ℝ := inner ℝ fU (p - U.center) with htp
  set wx : E := x - U.center - tx • fU with hwx
  set wp : E := p - U.center - tp • fU with hwp
  have hwxn : ‖wx‖ ≤ (σ : ℝ) := by simpa [hwx, htx, hfU] using hxw
  have hwpn : ‖wp‖ ≤ (σ : ℝ) := by simpa [hwp, htp, hfU] using hpw
  have htxa : |tx| ≤ 1 / 2 + (σ : ℝ) := by
    have := hxa; rw [real_inner_comm] at this
    simpa [htx, hfU] using this
  have htpa : |tp| ≤ 1 / 2 + (σ : ℝ) := by
    have := hpa; rw [real_inner_comm] at this
    simpa [htp, hfU] using this
  have hxp : x - p = (tx - tp) • fU + (wx - wp) := by
    rw [hwx, hwp]; module
  have hdiff : ‖x - p‖ ≤ (1 + 2 * (σ : ℝ)) + 2 * (σ : ℝ) := by
    rw [hxp]
    have h1 : ‖(tx - tp) • fU‖ = |tx - tp| := by
      rw [norm_smul, Real.norm_eq_abs, hfUn, mul_one]
    have h2 : |tx - tp| ≤ 1 + 2 * (σ : ℝ) := by
      calc |tx - tp| ≤ |tx| + |tp| := abs_sub _ _
        _ ≤ (1 / 2 + (σ : ℝ)) + (1 / 2 + (σ : ℝ)) := add_le_add htxa htpa
        _ = 1 + 2 * (σ : ℝ) := by ring
    have h3 : ‖wx - wp‖ ≤ 2 * (σ : ℝ) := by
      calc ‖wx - wp‖ ≤ ‖wx‖ + ‖wp‖ := norm_sub_le _ _
        _ ≤ (σ : ℝ) + (σ : ℝ) := add_le_add hwxn hwpn
        _ = 2 * (σ : ℝ) := by ring
    calc ‖(tx - tp) • fU + (wx - wp)‖ ≤ ‖(tx - tp) • fU‖ + ‖wx - wp‖ := norm_add_le _ _
      _ = |tx - tp| + ‖wx - wp‖ := by rw [h1]
      _ ≤ (1 + 2 * (σ : ℝ)) + 2 * (σ : ℝ) := add_le_add h2 h3
  -- the axial coordinate
  set sc : ℝ := inner ℝ e (x - V.center) with hsc
  have hsplit : x - V.center = (p - V.center) + (x - p) := by module
  have hsca : |sc| ≤ (K / 2 + K * (ρ : ℝ)) + ‖x - p‖ := by
    have hin : sc = (inner ℝ e (p - V.center) : ℝ) + (inner ℝ e (x - p) : ℝ) := by
      rw [hsc, hsplit, inner_add_right]
    have h1 : |(inner ℝ e (p - V.center) : ℝ)| ≤ K / 2 + K * (ρ : ℝ) := by
      have := hpVd.1; rw [real_inner_comm] at this; simpa [hedef] using this
    have h2 : |(inner ℝ e (x - p) : ℝ)| ≤ ‖x - p‖ := by
      have := abs_real_inner_le_norm e (x - p)
      rw [he, one_mul] at this; exact this
    rw [hin]
    exact (abs_add_le _ _).trans (add_le_add h1 h2)
  -- the transverse coordinate
  have hperpV : ‖p - V.center - inner ℝ e (p - V.center) • e‖ ≤ K * (ρ : ℝ) := by
    simpa [hedef] using hpVd.2
  have hperpf : ‖fU - inner ℝ e fU • e‖ ≤ a := by simpa [hedef, hfU] using ha
  have hperpxp : ‖(x - p) - inner ℝ e (x - p) • e‖ ≤ (1 + 2 * (σ : ℝ)) * a + 2 * (2 * (σ : ℝ)) := by
    have hlin : (x - p) - inner ℝ e (x - p) • e
        = (tx - tp) • (fU - inner ℝ e fU • e) + ((wx - wp) - inner ℝ e (wx - wp) • e) := by
      rw [hxp, inner_add_right, real_inner_smul_right]
      module
    have h2 : |tx - tp| ≤ 1 + 2 * (σ : ℝ) := by
      calc |tx - tp| ≤ |tx| + |tp| := abs_sub _ _
        _ ≤ (1 / 2 + (σ : ℝ)) + (1 / 2 + (σ : ℝ)) := add_le_add htxa htpa
        _ = 1 + 2 * (σ : ℝ) := by ring
    have h3 : ‖wx - wp‖ ≤ 2 * (σ : ℝ) := by
      calc ‖wx - wp‖ ≤ ‖wx‖ + ‖wp‖ := norm_sub_le _ _
        _ ≤ (σ : ℝ) + (σ : ℝ) := add_le_add hwxn hwpn
        _ = 2 * (σ : ℝ) := by ring
    have ha0 : (0 : ℝ) ≤ a := le_trans (norm_nonneg _) hperpf
    rw [hlin]
    calc ‖(tx - tp) • (fU - inner ℝ e fU • e) + ((wx - wp) - inner ℝ e (wx - wp) • e)‖
        ≤ ‖(tx - tp) • (fU - inner ℝ e fU • e)‖ + ‖(wx - wp) - inner ℝ e (wx - wp) • e‖ :=
          norm_add_le _ _
      _ = |tx - tp| * ‖fU - inner ℝ e fU • e‖ + ‖(wx - wp) - inner ℝ e (wx - wp) • e‖ := by
          rw [norm_smul, Real.norm_eq_abs]
      _ ≤ (1 + 2 * (σ : ℝ)) * a + 2 * ‖wx - wp‖ := by
          refine add_le_add (mul_le_mul h2 hperpf (norm_nonneg _) (by linarith)) ?_
          exact norm_perp_le_two_mul he _
      _ ≤ (1 + 2 * (σ : ℝ)) * a + 2 * (2 * (σ : ℝ)) := by gcongr
  have hdist : dist x (V'.center + sc • V'.direction) ≤ c * (σ : ℝ) := by
    rw [hV'ctr, hV'dir, dist_eq_norm]
    have hid : x - (V.center + sc • e) = (p - V.center - inner ℝ e (p - V.center) • e)
        + ((x - p) - inner ℝ e (x - p) • e) := by
      have hin : sc = (inner ℝ e (p - V.center) : ℝ) + (inner ℝ e (x - p) : ℝ) := by
        rw [hsc, hsplit, inner_add_right]
      rw [hin]; module
    rw [hid]
    have hbound : ‖(p - V.center - inner ℝ e (p - V.center) • e)
        + ((x - p) - inner ℝ e (x - p) • e)‖
        ≤ K * (ρ : ℝ) + ((1 + 2 * (σ : ℝ)) * a + 2 * (2 * (σ : ℝ))) :=
      (norm_add_le _ _).trans (add_le_add hperpV hperpxp)
    refine hbound.trans ?_
    have hcσ : c * (σ : ℝ) = (3 * K + 60) * (ρ : ℝ) := by
      rw [hc]; field_simp
    rw [hcσ]
    have hρ0 : (0 : ℝ) ≤ (ρ : ℝ) := ρ.coe_nonneg
    nlinarith [ha16, hσρ, hσ1, hK0, hρ0]
  refine Tube.mem_dilate_of_dist_axis_le V' hc0 ?_ hdist
  have hhalf : c / 2 ≥ (3 * K + 60) / 2 := by
    rw [hc]
    have : (3 * K + 60) * ((ρ : ℝ) / (σ : ℝ)) ≥ (3 * K + 60) * 1 := by
      refine mul_le_mul_of_nonneg_left hratio (by linarith)
    rw [mul_div_assoc]
    linarith
  have : |sc| ≤ (3 * K + 60) / 2 := by
    have hσ1' : (σ : ℝ) ≤ 1 := hσ1
    nlinarith [hsca, hdiff, hρ1, hK0]
  linarith



/-- **The loose packing count.** -/
theorem card_le_selfDilate_of_dir_close {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [Nontrivial E] [ProperSpace E] {κ : Type*} {ρ σ : NNReal}
    (hσ0 : 0 < σ) (hσρ : (σ : ℝ) ≤ (ρ : ℝ)) (hρ1 : (ρ : ℝ) ≤ 1) {K : ℝ} (hK : 1 ≤ K)
    (V : Tube ρ E) (a : Finset κ) (U : κ → Tube σ E)
    (hED : (↑a : Set κ).Pairwise fun j l ↦ IsEssentiallyDistinct (U j).carrier (U l).carrier)
    (hmeet : ∀ j ∈ a, ∃ p ∈ (U j).carrier, p ∈ (Kakeya.Tube.dilate V K).carrier ∧
      ‖(U j).direction - inner ℝ V.direction (U j).direction • V.direction‖ ≤ 16 * (ρ : ℝ)) :
    (a.card : ℝ) ≤ (Tube.essDistinctTubesInSelfDilate.C (Module.finrank ℝ E)
        ((3 * K + 60) * (ρ : ℝ) / (σ : ℝ)) : ℝ) := by
  have hσ0R : (0 : ℝ) < (σ : ℝ) := NNReal.coe_pos.2 hσ0
  have hσ1 : σ ≤ 1 := by
    have : (σ : ℝ) ≤ 1 := le_trans hσρ hρ1
    exact_mod_cast this
  have hK0 : (0 : ℝ) < K := lt_of_lt_of_le zero_lt_one hK
  set c : ℝ := (3 * K + 60) * (ρ : ℝ) / (σ : ℝ) with hc
  have hratio : (1 : ℝ) ≤ (ρ : ℝ) / (σ : ℝ) := by
    rw [le_div_iff₀ hσ0R]; linarith
  have hc1 : (1 : ℝ) ≤ c := by
    rw [hc, mul_div_assoc]
    nlinarith [hratio, hK0]
  set V' : Tube σ E := Tube.ofMidpointDirection σ V.center V.direction V.norm_direction with hV'
  have hUT : ∀ j ∈ a, (U j).carrier ⊆ (Kakeya.Tube.dilate V' c).carrier := by
    intro j hj
    obtain ⟨p, hpU, hpV, hdir⟩ := hmeet j hj
    exact carrier_subset_dilate_of_dir_close V (U j) hK hσ0 hσρ hρ1 hpU hpV hdir le_rfl
  have h := Tube.essDistinctTubesInSelfDilate (E := E) (ι := κ) (δ := σ) (c := c)
    hc1 hσ0 hσ1 V' a U hED hUT
  have hcast : ((a.card : NNReal) : ENNReal)
      ≤ ((Tube.essDistinctTubesInSelfDilate.C (Module.finrank ℝ E) c : NNReal) : ENNReal) := by
    simpa using h
  exact_mod_cast ENNReal.coe_le_coe.mp hcast



section LooseStepOne

set_option linter.unusedSectionVars false

variable {ι : Type u}

/-- **The cross-scale packing bound for loose hierarchies.** An essentially distinct, all-used
family of `ρ₂`-tubes for `sPar` has at most `P` members per level-`k` node of the *loose* parent
hierarchy, where `P = C_{lem:essDistinctTubesInSelfDilate}(3, (3 Kpar + 60) ρ_k/ρ₂)`.

The three reads of the exact proof are replaced as follows.
* read #2 (`cover.tube`) — **unchanged**: `Kakeya.LooseUniform.LooseGridCoverSystem` carries a
  `tube` field of exactly the exact type.
* read #3 (`le_tube_assign`) — replaced by `le_dilate_tube_assign`, which puts the member in the
  `Kpar`-dilate of its node rather than in the node.
* the chord argument that the exact proof runs on top of read #3 — replaced by
  `dir_close_tube_assign` plus `Kakeya.VeryNotSticky.norm_perp_le_of_dir_close`.

The two scale hypotheses `hδρ2 : δ ≤ ρ₂` and `hρ2le : ρ₂ ≤ ρ_k` are what turn the three
transverse budgets (`ρ_k/4` from the node, `5δ + 10ρ₂` from the chord) into the single
`16 ρ_k` that `Kakeya.VeryNotSticky.carrier_subset_dilate_of_dir_close` consumes; `hδρ2` is
`Kakeya.VeryNotSticky.delta_le_rho2` at the call site. -/
theorem card_count_le_mul_card_indexSet_loose {δ ρ2 : NNReal} {sPar : Finset ι}
    {T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))} {N : ℕ} {Kpar : ℝ} {Cpar : NNReal}
    (𝒰par : LooseUniform.LooseUniformTubeSet sPar (fun i ↦ (T i).toTube) N Kpar Cpar)
    (hKpar : 1 ≤ Kpar)
    {k : ℕ} (hk : k ≤ N) (hρ20 : 0 < ρ2) (hδρ2 : (δ : ℝ) ≤ (ρ2 : ℝ))
    (hρ2le : (ρ2 : ℝ) ≤ (Tube.gridScale δ N k : ℝ))
    (hgs1 : (Tube.gridScale δ N k : ℝ) ≤ 1)
    {κ : Type u} (tρ : Finset κ) (Tρ : κ → Tube ρ2 (EuclideanSpace ℝ (Fin 3)))
    (hED : (↑tρ : Set κ).Pairwise fun j l ↦ IsEssentiallyDistinct (Tρ j).carrier (Tρ l).carrier)
    (hused : ∀ j ∈ tρ, ∃ i ∈ sPar, (T i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) :
    (tρ.card : ℝ) ≤
      (Tube.essDistinctTubesInSelfDilate.C 3
        ((3 * Kpar + 60) * (Tube.gridScale δ N k : ℝ) / (ρ2 : ℝ)) : ℝ)
        * ((𝒰par.cover.indexSet k).card : ℝ) := by
  classical
  set ρk : NNReal := Tube.gridScale δ N k with hρk
  set P : ℝ := (Tube.essDistinctTubesInSelfDilate.C 3
    ((3 * Kpar + 60) * (ρk : ℝ) / (ρ2 : ℝ)) : ℝ) with hP
  have hP0 : (0 : ℝ) ≤ P := by rw [hP]; positivity
  have hfr : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
  have hKpar0 : (0 : ℝ) < Kpar := lt_of_lt_of_le zero_lt_one hKpar
  rcases tρ.eq_empty_or_nonempty with rfl | ⟨j₀, hj₀⟩
  · simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  obtain ⟨i₀, hi₀, -⟩ := hused j₀ hj₀
  set Q : κ → ι → Prop := fun j i ↦ i ∈ sPar ∧
    (T i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody with hQ
  set g : κ → ι := fun j ↦ if h : ∃ i, Q j i then h.choose else i₀ with hg
  have hgspec : ∀ j ∈ tρ, Q j (g j) := by
    intro j hj
    obtain ⟨i, hi, hle⟩ := hused j hj
    have hex : ∃ i, Q j i := ⟨i, hi, hle⟩
    rw [hg]
    simp only [hex, dif_pos]
    exact hex.choose_spec
  set f : κ → ι := fun j ↦ 𝒰par.cover.assign k (g j) with hf
  have hmaps : ∀ j ∈ tρ, f j ∈ 𝒰par.cover.indexSet k := fun j hj =>
    𝒰par.cover.assign_mem k hk (g j) (hgspec j hj).1
  have hfib := Finset.card_eq_sum_card_fiberwise (f := f) (s := tρ)
    (t := 𝒰par.cover.indexSet k) (fun j hj => hmaps j hj)
  have hterm : ∀ q ∈ 𝒰par.cover.indexSet k, (({j ∈ tρ | f j = q}).card : ℝ) ≤ P := by
    intro q _
    refine card_le_selfDilate_of_dir_close (E := EuclideanSpace ℝ (Fin 3)) hρ20
      (by exact_mod_cast hρ2le) (by exact_mod_cast hgs1) hKpar
      (𝒰par.cover.tube k q) _ Tρ
      (hED.mono (by intro x hx; simpa using (Finset.mem_filter.1 hx).1)) ?_ |>.trans ?_
    · -- the meeting point and the direction bound
      intro j hj
      simp only [Finset.mem_filter] at hj
      obtain ⟨hjt, hjq⟩ := hj
      have hgs := hgspec j hjt
      have hi : g j ∈ sPar := hgs.1
      have hcontain : (T (g j)).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody := hgs.2
      have hnode : (T (g j)).toConvexSpaceBody
          ≤ Kakeya.Tube.dilate (𝒰par.cover.tube k q) Kpar := by
        have := 𝒰par.cover.le_dilate_tube_assign k hk (g j) hi
        rwa [show 𝒰par.cover.assign k (g j) = q from hjq] at this
      -- the chord of the member, inside the `ρ₂`-tube
      obtain ⟨pt, hpt, qt, hqt, hptqt⟩ := Tube.exists_chord_of_tube (T (g j)).toTube
      refine ⟨pt, hcontain hpt, hnode hpt, ?_⟩
      -- the direction of the `ρ₂`-tube against the member's
      have hchord : ‖(Tρ j).direction -
            inner ℝ (T (g j)).toTube.direction (Tρ j).direction • (T (g j)).toTube.direction‖
          ≤ (2 * (δ : ℝ) + 4 * (ρ2 : ℝ)) / (2 / 5 : ℝ) := by
        refine Tube.norm_perp_direction_le_of_chord (T (g j)).toTube (Tρ j)
          (d := (2 / 5 : ℝ)) (by norm_num) hptqt hpt hqt ?_ ?_
        · exact Tube.subset_dilate (Tρ j) (by norm_num) (hcontain hpt)
        · exact Tube.subset_dilate (Tρ j) (by norm_num) (hcontain hqt)
      -- the direction of the member against the node's
      obtain ⟨sg, hsg, hsgle⟩ := 𝒰par.cover.dir_close_tube_assign k hk (g j) hi
      rw [show 𝒰par.cover.assign k (g j) = q from hjq] at hsgle
      have hkey := norm_perp_le_of_dir_close
        (e := (𝒰par.cover.tube k q).direction) (g := (T (g j)).toTube.direction)
        (f := (Tρ j).direction) (𝒰par.cover.tube k q).norm_direction
        (T (g j)).toTube.norm_direction (Tρ j).norm_direction hsg hsgle hchord
      refine hkey.trans ?_
      have hδρk : (δ : ℝ) ≤ (ρk : ℝ) := le_trans hδρ2 hρ2le
      have h5 : (2 * (δ : ℝ) + 4 * (ρ2 : ℝ)) / (2 / 5 : ℝ)
          = 5 * (δ : ℝ) + 10 * (ρ2 : ℝ) := by ring
      rw [h5]
      have hρ2ρk : (ρ2 : ℝ) ≤ (ρk : ℝ) := hρ2le
      have hρk0 : (0 : ℝ) ≤ (ρk : ℝ) := ρk.coe_nonneg
      nlinarith [hδρk, hρ2ρk, hρk0]
    · rw [hP, hfr]
  calc (tρ.card : ℝ) = ((∑ q ∈ 𝒰par.cover.indexSet k, ({j ∈ tρ | f j = q}).card : ℕ) : ℝ) := by
        rw [← hfib]
    _ = ∑ q ∈ 𝒰par.cover.indexSet k, (({j ∈ tρ | f j = q}).card : ℝ) := by push_cast; ring
    _ ≤ ∑ _q ∈ 𝒰par.cover.indexSet k, P := Finset.sum_le_sum hterm
    _ = P * ((𝒰par.cover.indexSet k).card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring

end LooseStepOne


/-! ### Part E — conjunct 5 assembled in the loose model

The loose analogue of `Kakeya.VeryNotSticky.RhoParentData` — the after-shape of `F-R18-8` — is
offered here as a **hypothesis type with a conditional consumer**. -/

section LooseAssembly

/-- **The `δ`-free part of the R17 constant in the loose model.** The exact model's
`Kakeya.VeryNotSticky.fibreCountConstant` at the packing ratio `32 ρ_k/ρ₂`; here the ratio is
`(3 Kpar + 60) ρ_k/ρ₂`, so the same twelfth power is taken of
`2 (3 Kpar + 60) C_{lem:ml2bodyAngle}(C₀)`. At `Kpar = 6` this is `(156 C)¹²` against the exact
model's `(64 C)¹²`; both are `δ`-free, which is all the threshold `hthr` needs. -/
noncomputable def fibreCountConstantLoose (Kpar C₀ : NNReal) : NNReal :=
  selfDilatePrefactor * (2 * (3 * Kpar + 60) * NonSlab.bodyAngleConstant C₀) ^ 12

/-- **The loose parent datum**: `Kakeya.VeryNotSticky.RhoParentData` with the parent's Definition
2.1 bundle read in the loose model at the dilation factor `Kpar`. This is the after-text `F-R18-8`
asks for; it is a hypothesis type here, and the theorem below is its conditional consumer. -/
def LooseRhoParentData (δ : NNReal) (ζ exscalb η Kpar : ℝ) {ι : Type u} (s : Finset ι)
    (T : ι → ShadedTube δ (EuclideanSpace ℝ (Fin 3))) : Prop :=
  ∃ sPar : Finset ι, s ⊆ sPar ∧
    (∀ i ∈ sPar, (T i).carrier ⊆ Metric.closedBall 0 1) ∧
    maxDensity sPar (fun i ↦ (T i).toConvexSpaceBody) ≤ (δ : ENNReal) ^ (-η) ∧
    (δ : ENNReal) ^ (2 * η) * (sPar.card : ENNReal) ≤ (s.card : ENNReal) ∧
    (∃ Cpar : NNReal, 1 ≤ Cpar ∧ (Cpar : ENNReal) ≤ (δ : ENNReal) ^ (-η) ∧
      Nonempty (LooseUniform.LooseUniformTubeSet sPar (fun i ↦ (T i).toTube)
        (Tube.ssfGridLen δ) Kpar Cpar)) ∧
    (∀ ρ : NNReal, ρ ∈ Set.Icc (δ ^ (1 - exscalb)) (δ ^ exscalb) →
      ∃ (κ : Type u) (tρ : Finset κ) (Tρ : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
        (tρ : Set κ).Pairwise
          (fun j k ↦ IsEssentiallyDistinct (Tρ j).carrier (Tρ k).carrier) ∧
        (∀ j ∈ tρ, ∃ i ∈ sPar, (T i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) ∧
        (ρ : ℝ) ^ (-2 - ζ) ≤ (tρ.card : ℝ))

/-- The fibre-scale count from a loose parent datum and a loose family hierarchy.
This is the loose analogue of `exists_fibreScaleCount_of_rhoParentData`: the
parent bundle and family hierarchy are loose, and the resulting count
constant satisfies the same bound `∃ Ccnt ≤ δ^{-18η}`. -/
theorem exists_fibreScaleCount_of_looseParent (cfg : VeryNotSticky.{u}) (bd : BallData cfg)
    (hC₀bd : 1 ≤ bd.C₀) (hexscal : cfg.exscal ≤ 1 / 2) (hb : cfg.b = cfg.δ)
    {Kpar Ks : NNReal} (hKpar : 1 ≤ Kpar) (hKs0 : 0 < (Ks : ℝ))
    (hKsKpar : (Ks : ℝ) ≤ (Kpar : ℝ) + 4)
    (hthr : (fibreCountConstantLoose Kpar bd.C₀ : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η))
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ)
    (hge : cfg.rho2Star bd.C₀ ≤ Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k)
    (hle : Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k
      ≤ cfg.δ ^ (-cfg.η) * cfg.rho2Star bd.C₀)
    {Cs : NNReal}
    {sPar : Finset cfg.ι} (hsub : cfg.s ⊆ sPar)
    (hretE : (cfg.δ : ENNReal) ^ (2 * cfg.η) * (sPar.card : ENNReal) ≤ (cfg.s.card : ENNReal))
    {Cpar : NNReal} (hCpar1 : 1 ≤ Cpar)
    (hCparE : (Cpar : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η))
    (𝒰par : LooseUniform.LooseUniformTubeSet sPar (fun i ↦ (cfg.T i).toTube)
      (Tube.ssfGridLen cfg.δ) (Kpar : ℝ) Cpar)
    (𝒰s : LooseUniform.LooseUniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube)
      (Tube.ssfGridLen cfg.δ) (Ks : ℝ) Cs)
    (hcount : ∀ ρ : NNReal, ρ ∈ Set.Icc (cfg.δ ^ (1 - cfg.exscalb)) (cfg.δ ^ cfg.exscalb) →
      ∃ (κ : Type u) (tρ : Finset κ) (Tρ : κ → Tube ρ (EuclideanSpace ℝ (Fin 3))),
        (tρ : Set κ).Pairwise
          (fun j l ↦ IsEssentiallyDistinct (Tρ j).carrier (Tρ l).carrier) ∧
        (∀ j ∈ tρ, ∃ i ∈ sPar, (cfg.T i).toConvexSpaceBody ≤ (Tρ j).toConvexSpaceBody) ∧
        (ρ : ℝ) ^ (-2 - cfg.ζ) ≤ (tρ.card : ℝ)) :
    ∃ Ccnt : NNReal, (Ccnt : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-(18 * cfg.η)) ∧
      (cfg.rho2 : ℝ) ^ (-2 - cfg.ζ) ≤ (Ccnt : ℝ) *
        ((𝒰s.cover.indexSet k).card : ℝ) := by
  classical
  have hδ0 : 0 < cfg.δ := cfg.hδ
  have hδ1 : cfg.δ ≤ 1 := cfg.hδ1
  have hCba : (1 : NNReal) ≤ NonSlab.bodyAngleConstant bd.C₀ :=
    NonSlab.one_le_bodyAngleConstant hC₀bd
  set ρk : NNReal := Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k with hρk
  set ρ2 : NNReal := cfg.rho2 with hρ2
  have hnotslab : cfg.b ≤ cfg.δ ^ cfg.exscal * cfg.r₁ := by
    rw [hb]
    unfold r₁
    rw [← NNReal.rpow_add hδ0.ne']
    calc cfg.δ = cfg.δ ^ (1 : ℝ) := (NNReal.rpow_one _).symm
      _ ≤ cfg.δ ^ (cfg.exscal + cfg.exscal) :=
        NNReal.rpow_le_rpow_of_exponent_ge hδ0 hδ1 (by linarith)
  obtain ⟨hwin, -⟩ := rho2_range cfg hδ0 hδ1 hexscal hnotslab
  have hwinb : ρ2 ∈ Set.Icc (cfg.δ ^ (1 - cfg.exscalb)) (cfg.δ ^ cfg.exscalb) := by
    rw [← cfg.hscale]; exact hwin
  have hρ20 : 0 < ρ2 := lt_of_lt_of_le (NNReal.rpow_pos hδ0) hwinb.1
  have hρk1 : ρk ≤ 1 := Tube.gridScale_le_one hδ1 _ _
  have hρ2ρk : ρ2 ≤ ρk := (rho2_le_rho2Star cfg hC₀bd).trans hge
  have hδρ2 : cfg.δ ≤ ρ2 := delta_le_rho2 cfg
  obtain ⟨κ, tρ, Tρ, hED, hused, hcard⟩ := hcount ρ2 hwinb
  have hCpar : Cpar ≤ cfg.δ ^ (-cfg.η) := le_rpow_neg_of_coe_le hδ0 hCparE
  have hret : cfg.δ ^ (2 * cfg.η) * (sPar.card : NNReal) ≤ (cfg.s.card : NNReal) :=
    mul_le_of_coe_mul_le hδ0 hretE
  have hne : sPar.Nonempty := by
    rcases tρ.eq_empty_or_nonempty with rfl | ⟨j₀, hj₀⟩
    · exfalso
      simp only [Finset.card_empty, Nat.cast_zero] at hcard
      exact absurd hcard (not_le.2 (Real.rpow_pos_of_pos (NNReal.coe_pos.2 hρ20) _))
    · obtain ⟨i₀, hi₀, -⟩ := hused j₀ hj₀
      exact ⟨i₀, hi₀⟩
  have hKparR : (1 : ℝ) ≤ (Kpar : ℝ) := by exact_mod_cast hKpar
  -- step 1: the count on the loose parent's nodes
  have hstep1 : (tρ.card : ℝ) ≤
      (Tube.essDistinctTubesInSelfDilate.C 3
        ((3 * (Kpar : ℝ) + 60) * (ρk : ℝ) / (ρ2 : ℝ)) : ℝ)
        * ((𝒰par.cover.indexSet k).card : ℝ) :=
    card_count_le_mul_card_indexSet_loose 𝒰par hKparR hk hρ20 (by exact_mod_cast hδρ2)
      (by exact_mod_cast hρ2ρk) (by exact_mod_cast hρk1) tρ Tρ hED hused
  -- step 2: the loose parent's nodes against the loose family's
  have hstep2 : cfg.δ ^ (2 * cfg.η) * ((𝒰par.cover.indexSet k).card : NNReal)
      ≤ Cpar ^ 3 * ((𝒰s.cover.indexSet k).card : NNReal) :=
    card_indexSet_parent_le_loose 𝒰par 𝒰s hKs0 hKsKpar hsub hne hk hret
  set A : NNReal := fibreCountConstantLoose Kpar bd.C₀ with hA
  set R : NNReal := 2 * (3 * Kpar + 60) * NonSlab.bodyAngleConstant bd.C₀
      * cfg.δ ^ (-cfg.η) with hR
  have hρ20R : (0 : ℝ) < (ρ2 : ℝ) := NNReal.coe_pos.2 hρ20
  rw [rho2Star] at hle
  have hNN : (3 * Kpar + 60) * ρk ≤ R * ρ2 := by
    calc (3 * Kpar + 60) * ρk
        ≤ (3 * Kpar + 60) * (cfg.δ ^ (-cfg.η)
            * (2 * NonSlab.bodyAngleConstant bd.C₀ * ρ2)) :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = R * ρ2 := by rw [hR]; ring
  have hratio : (3 * (Kpar : ℝ) + 60) * (ρk : ℝ) / (ρ2 : ℝ) ≤ (R : ℝ) := by
    rw [div_le_iff₀ hρ20R]
    have := NNReal.coe_le_coe.2 hNN
    push_cast at this
    linarith [this]
  have hratio1 : (1 : ℝ) ≤ (3 * (Kpar : ℝ) + 60) * (ρk : ℝ) / (ρ2 : ℝ) := by
    rw [le_div_iff₀ hρ20R]
    have h : (ρ2 : ℝ) ≤ (ρk : ℝ) := by exact_mod_cast hρ2ρk
    nlinarith [hρ20R, hKparR]
  have hpow3 : (cfg.δ ^ (-cfg.η)) ^ (3 : ℕ) = cfg.δ ^ (-((3 : ℝ) * cfg.η)) := by
    rw [← NNReal.rpow_natCast (cfg.δ ^ (-cfg.η)) 3, ← NNReal.rpow_mul]
    congr 1; push_cast; ring
  have hpow12 : (cfg.δ ^ (-cfg.η)) ^ (12 : ℕ) = cfg.δ ^ (-((12 : ℝ) * cfg.η)) := by
    rw [← NNReal.rpow_natCast (cfg.δ ^ (-cfg.η)) 12, ← NNReal.rpow_mul]
    congr 1; push_cast; ring
  have hPle : Tube.essDistinctTubesInSelfDilate.C 3
        ((3 * (Kpar : ℝ) + 60) * (ρk : ℝ) / (ρ2 : ℝ))
      ≤ A * cfg.δ ^ (-((12 : ℝ) * cfg.η)) := by
    refine (essDistinctTubesInSelfDilate_C_le hratio1).trans ?_
    have hR12 : ((3 * (Kpar : ℝ) + 60) * (ρk : ℝ) / (ρ2 : ℝ)).toNNReal ^ 12 ≤ R ^ 12 := by
      refine pow_le_pow_left₀ (by positivity) ?_ 12
      have h := Real.toNNReal_le_toNNReal hratio
      rwa [Real.toNNReal_coe] at h
    refine le_trans (mul_le_mul_of_nonneg_left hR12 (by positivity)) ?_
    rw [hR, hA, fibreCountConstantLoose, mul_pow, ← mul_assoc, hpow12]
  have hc0 : (0 : NNReal) < cfg.δ ^ (2 * cfg.η) := NNReal.rpow_pos hδ0
  have hIdx : ((𝒰par.cover.indexSet k).card : NNReal)
      ≤ Cpar ^ 3 * cfg.δ ^ (-((2 : ℝ) * cfg.η)) *
          ((𝒰s.cover.indexSet k).card : NNReal) := by
    have hinv : cfg.δ ^ (-((2 : ℝ) * cfg.η)) = (cfg.δ ^ (2 * cfg.η))⁻¹ := by
      rw [← NNReal.rpow_neg]
    calc ((𝒰par.cover.indexSet k).card : NNReal)
        = (cfg.δ ^ (2 * cfg.η))⁻¹ * (cfg.δ ^ (2 * cfg.η)
            * ((𝒰par.cover.indexSet k).card : NNReal)) := by
          rw [← mul_assoc, inv_mul_cancel₀ hc0.ne', one_mul]
      _ ≤ (cfg.δ ^ (2 * cfg.η))⁻¹ * (Cpar ^ 3
            * ((𝒰s.cover.indexSet k).card : NNReal)) := by gcongr
      _ = Cpar ^ 3 * cfg.δ ^ (-((2 : ℝ) * cfg.η)) *
            ((𝒰s.cover.indexSet k).card : NNReal) := by rw [hinv]; ring
  have hCpar3 : Cpar ^ 3 ≤ cfg.δ ^ (-((3 : ℝ) * cfg.η)) := by
    refine le_trans (pow_le_pow_left₀ (by positivity) hCpar 3) ?_
    rw [hpow3]
  have hadd : cfg.δ ^ (-((12:ℝ) * cfg.η)) * (cfg.δ ^ (-((3:ℝ) * cfg.η))
      * cfg.δ ^ (-((2:ℝ) * cfg.η))) = cfg.δ ^ (-((17:ℝ) * cfg.η)) := by
    rw [← NNReal.rpow_add hδ0.ne', ← NNReal.rpow_add hδ0.ne']
    congr 1; ring
  refine ⟨A * cfg.δ ^ (-((17 : ℝ) * cfg.η)), ?_, ?_⟩
  · have hAle : A ≤ cfg.δ ^ (-cfg.η) := le_rpow_neg_of_coe_le hδ0 hthr
    have hstep : A * cfg.δ ^ (-((17 : ℝ) * cfg.η)) ≤ cfg.δ ^ (-(18 * cfg.η)) := by
      refine le_trans (mul_le_mul_of_nonneg_right hAle (by positivity)) ?_
      rw [← NNReal.rpow_add hδ0.ne']
      exact le_of_eq (by congr 1; ring)
    calc ((A * cfg.δ ^ (-((17 : ℝ) * cfg.η)) : NNReal) : ENNReal)
        ≤ ((cfg.δ ^ (-(18 * cfg.η)) : NNReal) : ENNReal) := by exact_mod_cast hstep
      _ = (cfg.δ : ENNReal) ^ (-(18 * cfg.η)) :=
          ENNReal.coe_rpow_of_ne_zero hδ0.ne' _
  · have hkeyN : Tube.essDistinctTubesInSelfDilate.C 3
          ((3 * (Kpar : ℝ) + 60) * (ρk : ℝ) / (ρ2 : ℝ))
        * ((𝒰par.cover.indexSet k).card : NNReal)
        ≤ A * cfg.δ ^ (-((17 : ℝ) * cfg.η))
          * ((𝒰s.cover.indexSet k).card : NNReal) := by
      calc Tube.essDistinctTubesInSelfDilate.C 3
              ((3 * (Kpar : ℝ) + 60) * (ρk : ℝ) / (ρ2 : ℝ))
            * ((𝒰par.cover.indexSet k).card : NNReal)
          ≤ (A * cfg.δ ^ (-((12 : ℝ) * cfg.η)))
              * (Cpar ^ 3 * cfg.δ ^ (-((2 : ℝ) * cfg.η)) *
                ((𝒰s.cover.indexSet k).card : NNReal)) := mul_le_mul' hPle hIdx
        _ ≤ (A * cfg.δ ^ (-((12 : ℝ) * cfg.η)))
              * (cfg.δ ^ (-((3 : ℝ) * cfg.η)) * cfg.δ ^ (-((2 : ℝ) * cfg.η)) *
                ((𝒰s.cover.indexSet k).card : NNReal)) := by gcongr
        _ = A * (cfg.δ ^ (-((12:ℝ) * cfg.η)) * (cfg.δ ^ (-((3:ℝ) * cfg.η))
              * cfg.δ ^ (-((2:ℝ) * cfg.η))))
              * ((𝒰s.cover.indexSet k).card : NNReal) := by ring
        _ = A * cfg.δ ^ (-((17 : ℝ) * cfg.η))
              * ((𝒰s.cover.indexSet k).card : NNReal) := by rw [hadd]
    have hkeyR : (Tube.essDistinctTubesInSelfDilate.C 3
          ((3 * (Kpar : ℝ) + 60) * (ρk : ℝ) / (ρ2 : ℝ)) : ℝ)
        * ((𝒰par.cover.indexSet k).card : ℝ)
        ≤ ((A * cfg.δ ^ (-((17 : ℝ) * cfg.η)) : NNReal) : ℝ)
          * ((𝒰s.cover.indexSet k).card : ℝ) := by
      have := NNReal.coe_le_coe.2 hkeyN
      push_cast at this ⊢
      linarith [this]
    linarith [hcard, hstep1, hkeyR]

/-- **The same, consuming `Kakeya.VeryNotSticky.LooseRhoParentData` itself.** The conclusion is conditional on this geometric datum. -/
theorem exists_fibreScaleCount_of_looseRhoParentData (cfg : VeryNotSticky.{u})
    (bd : BallData cfg) (hC₀bd : 1 ≤ bd.C₀) (hexscal : cfg.exscal ≤ 1 / 2)
    (hb : cfg.b = cfg.δ) {Kpar Ks : NNReal} (hKpar : 1 ≤ Kpar) (hKs0 : 0 < (Ks : ℝ))
    (hKsKpar : (Ks : ℝ) ≤ (Kpar : ℝ) + 4)
    (hthr : (fibreCountConstantLoose Kpar bd.C₀ : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-cfg.η))
    {k : ℕ} (hk : k ≤ Tube.ssfGridLen cfg.δ)
    (hge : cfg.rho2Star bd.C₀ ≤ Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k)
    (hle : Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k
      ≤ cfg.δ ^ (-cfg.η) * cfg.rho2Star bd.C₀)
    (hpar : LooseRhoParentData cfg.δ cfg.ζ cfg.exscalb cfg.η (Kpar : ℝ) cfg.s cfg.T)
    {Cs : NNReal}
    (𝒰s : LooseUniform.LooseUniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube)
      (Tube.ssfGridLen cfg.δ) (Ks : ℝ) Cs) :
    ∃ Ccnt : NNReal, (Ccnt : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-(18 * cfg.η)) ∧
      (cfg.rho2 : ℝ) ^ (-2 - cfg.ζ) ≤ (Ccnt : ℝ) *
        ((𝒰s.cover.indexSet k).card : ℝ) := by
  obtain ⟨sPar, hsub, -, -, hretE, ⟨Cpar, hCpar1, hCparE, ⟨𝒰par⟩⟩, hcount⟩ := hpar
  exact exists_fibreScaleCount_of_looseParent cfg bd hC₀bd hexscal hb hKpar hKs0 hKsKpar
    hthr hk hge hle hsub hretE hCpar1 hCparE 𝒰par 𝒰s hcount

/-- **The `∀ᶠ δ` form: conjunct 5 of `Kakeya.VeryNotSticky.SideDataObligations` in the loose
model**, at the same exponent `M = 18` as the existing exact discharge
`Kakeya.VeryNotSticky.eventually_exists_fibreScaleCount`. The single threshold on `δ` is the
absorption of the `δ`-free `Kakeya.VeryNotSticky.fibreCountConstantLoose Kpar C₀bd` into one
`η`, exactly as in the exact model. -/
theorem eventually_exists_fibreScaleCount_loose (exscal η : ℝ) (C₀bd Kpar : NNReal)
    (hC₀bd : 1 ≤ C₀bd) (hKpar : 1 ≤ Kpar) (hexscal : exscal ≤ 1 / 2) (hη : 0 < η) :
    ∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg),
      cfg.δ = δ → cfg.η = η → cfg.exscal = exscal → cfg.b = cfg.δ → bd.C₀ = C₀bd →
      ∀ Ks : NNReal, 0 < (Ks : ℝ) → (Ks : ℝ) ≤ (Kpar : ℝ) + 4 →
      ∀ (Cs : NNReal) (𝒰s : LooseUniform.LooseUniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube)
          (Tube.ssfGridLen cfg.δ) (Ks : ℝ) Cs),
        LooseRhoParentData cfg.δ cfg.ζ cfg.exscalb cfg.η (Kpar : ℝ) cfg.s cfg.T →
        ∀ k, k ≤ Tube.ssfGridLen cfg.δ →
          cfg.rho2Star bd.C₀ ≤ Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k →
          Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k ≤
              cfg.δ ^ (-cfg.η) * cfg.rho2Star bd.C₀ →
          ∃ Ccnt : NNReal, (Ccnt : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-(18 * cfg.η)) ∧
            (cfg.rho2 : ℝ) ^ (-2 - cfg.ζ) ≤ (Ccnt : ℝ) *
              ((𝒰s.cover.indexSet k).card : ℝ) := by
  filter_upwards [eventually_ennreal_le_rpow_neg
    (K := ((fibreCountConstantLoose Kpar C₀bd : NNReal) : ENNReal)) ENNReal.coe_ne_top hη]
    with δ hδthr
  intro cfg bd hδ hη' hex hb hC₀ Ks hKs0 hKsKpar Cs 𝒰s hpar k hk hge hle
  refine exists_fibreScaleCount_of_looseRhoParentData cfg bd (by rw [hC₀]; exact hC₀bd)
    (by rw [hex]; exact hexscal) hb hKpar hKs0 hKsKpar ?_ hk hge hle hpar 𝒰s
  rw [hC₀, hδ, hη']
  exact hδthr

/-! ### Non-vacuity of the loose bundle

The following example verifies that the hypotheses can be satisfied. The witness below is **degenerate on purpose**: it inhabits
`Kakeya.LooseUniform.LooseUniformTubeSet` on the empty family, which is all that is needed to
show the type is not `False`. It is *not* a producer, and nothing here claims that the loose
bundle of a *nonempty* Section-9 family exists; producing that is 's steps, still
open. -/

/-- **Non-vacuity, degenerate.** The loose Definition 2.1 bundle is inhabited on the empty
family, at every `N`, `K` and `C`. -/
theorem nonempty_looseUniformTubeSet_empty {δ : NNReal} {ι : Type u}
    (T : ι → Tube δ (EuclideanSpace ℝ (Fin 3))) (N : ℕ) (K : ℝ) (C : NNReal) :
    Nonempty (LooseUniform.LooseUniformTubeSet (∅ : Finset ι) T N K C) := by
  classical
  have hv : ‖(EuclideanSpace.single (0 : Fin 3) (1 : ℝ))‖ = 1 := by
    simp
  refine ⟨{
    cover := {
      indexSet := fun _ => ∅
      assign := fun _ i => i
      tube := fun k _ => Tube.ofMidpointDirection (Tube.gridScale δ N k) 0
        (EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) hv
      assign_mem := by
        intro k _ i hi
        simp at hi
      le_dilate_tube_assign := by
        intro k _ i hi
        simp at hi
      dir_close_tube_assign := by
        intro k _ i hi
        simp at hi
      nested := by
        intro k _ i hi
        simp at hi
    }
    branchingN := fun _ => 0
    tube_injOn := by
      intro k _
      simp
    boundedOverlapDil := by
      intro k _ V
      simp
    card_class_le := by
      intro k _ j hj
      simp at hj
    le_card_class := by
      intro k _ j hj
      simp at hj
  }⟩

/-! ### Tripwire: the loose after-text of conjunct 5

`Kakeya.VeryNotSticky.sideDataObligations_conjunct5_after` is the existing certificate that the
repaired conjunct 5 is producible in the **exact** model. The statement below is the same text
with the two hierarchies read loosely — i.e. what conjunct 5 becomes after `F-R18-5` and
`F-R18-8`. **That it is a theorem is the certificate that the R18 rewire does not un-discharge
conjunct 5.** The boundary `Prop` is not edited here. -/

/-- **Conjunct 5 survives the loose rewire.** The `ϱ`-pinned `∀ᶠ δ` after-text of conjunct 5,
with `cfg.splitHierarchy` and the parent's Definition 2.1 bundle read in the loose model, at the
same constant exponent `M = 18`. -/
theorem sideDataObligations_conjunct5_after_loose (exscal ϱ η : ℝ) (C₀bd Kpar : NNReal)
    (hC₀bd : 1 ≤ C₀bd) (hKpar : 1 ≤ Kpar) (hexscal : exscal ≤ 1 / 2) (hη : 0 < η) :
    ∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg),
      cfg.δ = δ → cfg.η = η → cfg.exscal = exscal → cfg.ϱ = ϱ → cfg.b = cfg.δ →
      bd.C₀ = C₀bd →
      ∀ Ks : NNReal, 0 < (Ks : ℝ) → (Ks : ℝ) ≤ (Kpar : ℝ) + 4 →
      ∀ (Cs : NNReal) (𝒰s : LooseUniform.LooseUniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube)
          (Tube.ssfGridLen cfg.δ) (Ks : ℝ) Cs),
        LooseRhoParentData cfg.δ cfg.ζ cfg.exscalb cfg.η (Kpar : ℝ) cfg.s cfg.T →
        ∀ k, k ≤ Tube.ssfGridLen cfg.δ →
          cfg.rho2Star bd.C₀ ≤ Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k →
          Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k ≤
              cfg.δ ^ (-cfg.η) * cfg.rho2Star bd.C₀ →
          ∃ Ccnt : NNReal, (Ccnt : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-(18 * cfg.η)) ∧
            (cfg.rho2 : ℝ) ^ (-2 - cfg.ζ) ≤ (Ccnt : ℝ) *
              ((𝒰s.cover.indexSet k).card : ℝ) := by
  filter_upwards [eventually_exists_fibreScaleCount_loose.{u} exscal η C₀bd Kpar hC₀bd hKpar
    hexscal hη] with δ h
  intro cfg bd hδ hη' hex _hϱ hb hC₀ Ks hKs0 hKsKpar Cs 𝒰s hpar k hk hge hle
  exact h cfg bd hδ hη' hex hb hC₀ Ks hKs0 hKsKpar Cs 𝒰s hpar k hk hge hle

/-! ### Conjunct 5 at its post-E-L3 text — re-closed, on the loose parent datum -/

/-- **Conjunct 5 of `Kakeya.VeryNotSticky.SideDataObligations`, discharged from the loose parent
datum.** The conclusion is conjunct 5 **verbatim** — the `example` below plugs it into slot 5 by
kernel `rfl` — so the retype does **not** leave conjunct 5 open in the sense of "no discharge
exists"; it moves the discharge from the configuration's own field `cfg.rho_count` to the
hypothesis `Kakeya.VeryNotSticky.LooseRhoParentData`, at the *same* measured exponent `M = 18`
and with no new constant.

**Why the antecedent cannot be dropped, measured.** The exact discharge
`Kakeya.VeryNotSticky.sideDataObligations_conjunct5_after` reads `cfg.rho_count`, whose parent
hierarchy is an **exact** `Tube.UniformTubeSet`. The loose chain consumes the parent through
`Kakeya.VeryNotSticky.card_count_le_mul_card_indexSet_loose`, which reads
`Kakeya.LooseUniform.LooseGridCoverSystem.dir_close_tube_assign` — a clause pinning a member's
direction to `ρ_k/4` of its node's. **The exact model has no such field and cannot supply it**:
exact containment of a `δ`-tube in a `ρ_k`-tube pins the directions only to `≈ 6 ρ_k`
(`Kakeya.VeryNotSticky.exists_sign_norm_direction_sub_le_of_body_le`), which is `24×` too weak,
and no dilation factor `K` repairs an *angle*. So the loose model is not a weakening of the
exact one — it trades exact containment for a dilate and demands tighter directions in return —
and the loose count needs a loose parent. Producing that datum is the parent-side twin of
conjunct 6's own obligation and belongs to the D-c producer, not here. -/
theorem sideDataObligations_conjunct5_of_looseRhoParent (exscal ϱ η : ℝ) (C₀bd Kpar : NNReal)
    (hC₀bd : 1 ≤ C₀bd) (hKpar : 1 ≤ Kpar) (hexscal : exscal ≤ 1 / 2) (hη : 0 < η)
    (hpar : ∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ cfg : VeryNotSticky.{u},
      cfg.δ = δ → cfg.η = η → cfg.exscal = exscal → cfg.ϱ = ϱ → cfg.b = cfg.δ →
      LooseRhoParentData cfg.δ cfg.ζ cfg.exscalb cfg.η (Kpar : ℝ) cfg.s cfg.T) :
    ∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ (cfg : VeryNotSticky.{u}) (bd : BallData cfg),
      cfg.δ = δ → cfg.η = η → cfg.exscal = exscal → cfg.ϱ = ϱ → cfg.b = cfg.δ →
      bd.C₀ = C₀bd →
      ∀ 𝒰s : LooseUniform.LooseUniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube)
          (Tube.ssfGridLen cfg.δ) edCoverDilateConstant (edCoverConstant cfg.C₀),
      ∀ k, k ≤ Tube.ssfGridLen cfg.δ →
        cfg.rho2Star bd.C₀ ≤ Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k →
        Tube.gridScale cfg.δ (Tube.ssfGridLen cfg.δ) k ≤
            cfg.δ ^ (-cfg.η) * cfg.rho2Star bd.C₀ →
        ∃ Ccnt : NNReal, (Ccnt : ENNReal) ≤ (cfg.δ : ENNReal) ^ (-(18 * cfg.η)) ∧
          (cfg.rho2 : ℝ) ^ (-2 - cfg.ζ) ≤ (Ccnt : ℝ) *
            ((𝒰s.cover.indexSet k).card : ℝ) := by
  have h4 : edCoverDilateConstant = ((4 : NNReal) : ℝ) := by
    rw [edCoverDilateConstant]; norm_num
  have hKb : ((4 : NNReal) : ℝ) ≤ (Kpar : ℝ) + 4 := by
    have h0 : (0 : ℝ) ≤ (Kpar : ℝ) := Kpar.coe_nonneg
    push_cast
    linarith
  filter_upwards [eventually_exists_fibreScaleCount_loose.{u} exscal η C₀bd Kpar hC₀bd hKpar
    hexscal hη, hpar] with δ h hp
  intro cfg bd hδ hη' hex hϱ hb hC₀
  rw [h4]
  intro 𝒰s k hk hge hle
  exact h cfg bd hδ hη' hex hb hC₀ 4 (by norm_num) hKb (edCoverConstant cfg.C₀) 𝒰s
    (hp cfg hδ hη' hex hϱ hb) k hk hge hle

/-! **RETIRED PLUG — fired as designed.**
Slot 5 of `Kakeya.VeryNotSticky.SideDataObligations` now carries the **exact** count text
`∀ C : NNReal, 1 ≤ C → C ≤ δ^{-η} → ∀ 𝒰s : Tube.UniformTubeSet cfg.s (fun i ↦ (cfg.T i).toTube) (Tube.ssfGridLen cfg.δ) C, …`
(conjunct 5 `84e7b55b… → d17433ba…`), so the loose conclusion of `sideDataObligations_conjunct5_of_looseRhoParent`
no longer fills it and the kernel-`rfl` plug below (its `example` source versions `301fbcc1b582cd5fef9a42014518bda6`) stopped elaborating — which is
exactly what this tripwire was for. The theorem above is untouched and still compiles; only this `example` is retired,
kept **verbatim** as text.  R2 (2026-09-04): it stays retired — no re-target, no deletion. Its drift-tripwire
role (any change to slot 5's text or position fires a declaration) is carried by the three re-cut **text pins** of the exact
slot-5 text: the `example` in `SplitInputsFibreCount.lean` (h5 := the exact text, rebuilt by anonymous constructor) and the two
`example`s in `SplitInputsFibreCountDischarge.lean` (the rebuild, and the projection `h.2.2.2.2` ascribed the exact text).
Nothing else in this module changes. Original docstring and declaration follow.

**Tripwire: the conclusion above really is conjunct 5, at its post-E-L3 text.**

It rebuilds `Kakeya.VeryNotSticky.SideDataObligations` from a hypothetical instance with its
**fifth** component replaced by
`Kakeya.VeryNotSticky.sideDataObligations_conjunct5_of_looseRhoParent`. The anonymous
constructor elaborates only if that theorem's conclusion is *definitionally* the fifth conjunct,
so this is a kernel `rfl` on both the conjunct's text and its position: any drift in either
breaks this declaration rather than passing silently. It is the post-E-L3 successor of the two
`example`s in `SplitInputsFibreCount.lean` and `SplitInputsFibreCountDischarge.lean`, which the
retype turned from discharges into text pins. (Mathematically vacuous — conjuncts 1 and 6 are
consumed opaquely — and kept as an `example` so it adds no name to the API.)

example {β exscal ϱ η τ τ' : ℝ} {C₀bd Cbias CF Cdil c₁ Cg Kpar : NNReal} {D : ℕ}
    (hC₀bd : 1 ≤ C₀bd) (hKpar : 1 ≤ Kpar) (hexscal : exscal ≤ 1 / 2) (hη : 0 < η)
    (hpar : ∀ᶠ δ : NNReal in 𝓝[>] 0, ∀ cfg : VeryNotSticky.{u},
      cfg.δ = δ → cfg.η = η → cfg.exscal = exscal → cfg.ϱ = ϱ → cfg.b = cfg.δ →
      LooseRhoParentData cfg.δ cfg.ζ cfg.exscalb cfg.η (Kpar : ℝ) cfg.s cfg.T)
    (h : SideDataObligations.{u} β exscal ϱ η τ τ' C₀bd Cbias CF Cdil c₁ Cg D) :
    SideDataObligations.{u} β exscal ϱ η τ τ' C₀bd Cbias CF Cdil c₁ Cg D :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1,
    sideDataObligations_conjunct5_of_looseRhoParent.{u} exscal ϱ η C₀bd Kpar hC₀bd hKpar
      hexscal hη hpar,
    h.2.2.2.2.2⟩
-/

end LooseAssembly

end Kakeya.VeryNotSticky
