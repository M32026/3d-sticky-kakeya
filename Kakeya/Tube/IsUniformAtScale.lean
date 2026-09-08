/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.Density

/-!
# Single-scale uniformity of a tube family (GWZ Definition 2.1)

`Tube.IsUniformAtScale s T ρ C` bundles, at one scale `ρ`, the three clauses of GWZ
Definition 2.1: every leaf sits in a parent, the parents have bounded overlap, and every parent
carries comparably many leaves.  The multiscale object built out of these — the nested system of
covers — is `Tube.UniformTubeSet` in `Kakeya.Uniform`.

This is the bottom of the uniformity development: over twenty modules read this structure, and
nothing here mentions a grid, a chain of scales or a density.
-/

@[expose] public section


open MeasureTheory

section IsUniform

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [MeasureSpace E] {ι : Type*} {δ : NNReal}

namespace Tube

open Classical in
/-- Single-scale uniformity for a family of `δ`-tubes, with the parent family
`Tρ` and the branching count `N` provided explicitly: the family `T` of
`δ`-tubes is uniform at scale `ρ` via `Tρ` with branching count `N` . -/
structure IsUniformAtScale (s : Finset ι) (T : ι → Tube δ E) (ρ : NNReal) (C : NNReal)
    (D : NNReal := C) where
  /-- The branching number. -/
  branchingN : NNReal
  /-- The parent family is indexed by a finite subset of `ι`. -/
  parent : Finset ι
  /-- The actual parent tubes: genuine *free* `ρ`-tubes (cores anywhere), not
  rescalings of the original `δ`-tubes. -/
  parentTube : ι → Tube ρ E
  /-- Every `δ`-tube of `s` lies in some parent `ρ`-tube (factor-1 containment). -/
  exists_le_rescale {i} (h : i ∈ s) :
    ∃ j ∈ parent, (T i).toConvexSpaceBody ≤ (parentTube j).toConvexSpaceBody
  /-- **Bounded overlap** (replaces the unsatisfiable pairwise essential
  distinctness of the parent family): every `ρ`-tube `V` is comparable — shares
  a `δ`-tube of `s` — with at most `C` parents. This is the `∼1`-multiplicity of
  GWZ Def 2.1(ii) and exactly the form the multiscale tree's overlap bound
  provides. -/
  boundedOverlap (V : Tube ρ E) :
    ((parent).filter (fun j => ∃ i ∈ s,
        (T i).toConvexSpaceBody ≤ (parentTube j).toConvexSpaceBody ∧
        (T i).toConvexSpaceBody ≤ V.toConvexSpaceBody)).card ≤ D
  /-- Distinct parent indices yield distinct parent tubes (formerly a by-product
  of pairwise essential distinctness). -/
  parentTube_injOn : Set.InjOn parentTube (parent : Set ι)
  /-- Number of `δ`-tubes in each parent tube is roughly the branching number. Upper bound. -/
  card_filter_le {j} (h : j ∈ parent) :
    { i ∈ s | (T i).toConvexSpaceBody ≤ (parentTube j).toConvexSpaceBody}.card ≤ C * branchingN
  /-- Number of `δ`-tubes in each parent tube is roughly the branching number. Lower bound. -/
  le_mul_card_filter {j} (h : j ∈ parent) :
    branchingN ≤ C * { i ∈ s | (T i).toConvexSpaceBody ≤ (parentTube j).toConvexSpaceBody}.card

open Classical in
omit [MeasureSpace E] in
/-- **Covering-multiplicity from `boundedOverlap`** (no separation needed).  The number of coarse
parents whose body dominates a fixed finer tube `W` is at most `C`, provided some `s`-tube `T i₀`
lies under `W`: every such parent also dominates `T i₀`, and `V := (T i₀).rescale ρ_cs` shares the
leaf `i₀` with it, so it is counted by `boundedOverlap V`. -/
theorem IsUniformAtScale.parents_containing_tube_card_le
    {s : Finset ι} {T : ι → Tube δ E} {ρ_cs : NNReal} {C : NNReal}
    (h_cs : IsUniformAtScale s T ρ_cs C) (hδρ : δ ≤ ρ_cs)
    {ρ_f : NNReal} (W : Tube ρ_f E)
    {i₀ : ι} (hi₀ : i₀ ∈ s)
    (hi₀W : (T i₀).toConvexSpaceBody ≤ W.toConvexSpaceBody) :
    ((h_cs.parent.filter
        (fun j => W.toConvexSpaceBody ≤ (h_cs.parentTube j).toConvexSpaceBody)).card : NNReal)
      ≤ C := by
  classical
  have hi₀V : (T i₀).toConvexSpaceBody ≤ ((T i₀).rescale ρ_cs).toConvexSpaceBody := by
    rw [← (T i₀).toConvexBody_cthickening_sub hδρ]
    intro x hx; exact Metric.self_subset_cthickening _ hx
  have hsub :
      h_cs.parent.filter
          (fun j => W.toConvexSpaceBody ≤ (h_cs.parentTube j).toConvexSpaceBody)
        ⊆ h_cs.parent.filter (fun j => ∃ i ∈ s,
            (T i).toConvexSpaceBody ≤ (h_cs.parentTube j).toConvexSpaceBody ∧
            (T i).toConvexSpaceBody ≤ ((T i₀).rescale ρ_cs).toConvexSpaceBody) := by
    intro j hj
    rw [Finset.mem_filter] at hj ⊢
    exact ⟨hj.1, i₀, hi₀, hi₀W.trans hj.2, hi₀V⟩
  calc ((h_cs.parent.filter
          (fun j => W.toConvexSpaceBody ≤ (h_cs.parentTube j).toConvexSpaceBody)).card : NNReal)
      ≤ ((h_cs.parent.filter (fun j => ∃ i ∈ s,
            (T i).toConvexSpaceBody ≤ (h_cs.parentTube j).toConvexSpaceBody ∧
            (T i).toConvexSpaceBody ≤ ((T i₀).rescale ρ_cs).toConvexSpaceBody)).card : NNReal) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ C := h_cs.boundedOverlap ((T i₀).rescale ρ_cs)

/-- Uniformity at a scale is monotone in its two constants: every field is an upper bound, so a
larger pair of constants is a weaker hypothesis.  The witness — parent family, parent tubes and
branching number — is unchanged, which matters at the call sites that compare the parents of two
structures. -/
@[simps! branchingN parent parentTube]
def IsUniformAtScale.mono {s : Finset ι} {T : ι → Tube δ E} {ρ C D C' D' : NNReal}
    (h : IsUniformAtScale s T ρ C D) (hC : C ≤ C') (hD : D ≤ D') :
    IsUniformAtScale s T ρ C' D' where
  branchingN := h.branchingN
  parent := h.parent
  parentTube := h.parentTube
  exists_le_rescale hi := h.exists_le_rescale hi
  boundedOverlap V := (h.boundedOverlap V).trans hD
  parentTube_injOn := h.parentTube_injOn
  card_filter_le hj := (h.card_filter_le hj).trans (mul_le_mul_left hC _)
  le_mul_card_filter hj := (h.le_mul_card_filter hj).trans (mul_le_mul_left hC _)

end Tube

end IsUniform
