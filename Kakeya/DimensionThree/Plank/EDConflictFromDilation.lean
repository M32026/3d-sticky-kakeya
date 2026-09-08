/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.EDWeightedExtraction
public import Kakeya.DimensionThree.Plank.PlankOverlapGeometry
public import Kakeya.DimensionThree.Plank.RepresentativeFrostman
public import Kakeya.DimensionThree.Plank.ThickenedGeometry

/-!
# What the essentially-distinct plank extraction actually consumes: one dilation count

`Kakeya.exists_pairwise_plank_subset_of_isThickeningNonconcentrated`
(`Kakeya/Factoring/FlatPrisms.lean`) is stated over `Plank.IsThickeningNonconcentrated`, a clause
quantified over **every** `φ ∈ [a/b, 1]`.  Its proof uses that clause at exactly one place and
exactly one value — `hNC i hi (a / b) hab1 le_rfl` — and the docstring says so: *"the point is to
test at the smallest admissible thickening `a / b`; at that scale the thickened plank is the
original plank."*

That matters for GWZ 6.6(B), because the `φ > a/b` range of the clause is **not** a volume-ratio
statement: the container there is `Λφb × Λb × Λ`, the volume ratio is `α = a / (Λ³ φ b)`, and the
bound the clause asks for is `M · φ`, i.e. *linear* in `1/α`, whereas the general convex packing
count `Kakeya.cardEssDistinctConvexInPrismConstant 3 α` is `2 ^ Θ(α⁻³)`.  A consumer that needs the
whole clause therefore needs a genuine transverse packing count; a consumer that needs only one
dilation count does not.

This file records, as named lemmas, that the extraction is a consumer of the second kind.

* `Kakeya.edConflictDegree_le_card_filter_subset_dilation` — **unconditional**: the ED conflict
  degree of a shaded plank family at `i` is at most the number of members contained in the
  `C`-dilation of `P i`, for any `C ≥ 11`.  This is the step
  `Kakeya.large_overlap_plank_subset_dilation` exists for; it was inlined in the two proofs that
  use it (`Kakeya/Factoring/FlatPrisms.lean` and
  `Kakeya/DimensionThree/Plank/InnerConflictDegree.lean`) and is exposed here.
* `Kakeya.exists_pairwise_plank_ED_subfamily_of_dilation_count` — the extraction itself, from a
  **bare dilation count at a single factor**: no `φ`, no thickening, no non-concentration
  predicate.  Same conclusion as the `Plank.IsThickeningNonconcentrated` form: an essentially distinct
  subfamily retaining cardinality and shade mass up to `d + 1`.
* `Kakeya.card_filter_subset_dilation_le_of_isThickeningNonconcentrated` — the `φ = a/b` instance
  of the full clause *is* that dilation count (`Plank.plank_thickened_self_dilation_carrier`), so
  the `Plank.IsThickeningNonconcentrated` hypothesis is strictly stronger than what is used;
* `Kakeya.exists_pairwise_plank_ED_subfamily_of_isThickeningNonconcentrated_endpoint` — the
  factorisation, proved: the existing tool's conclusion follows from the endpoint alone.

## Why this is the operative question for GWZ 6.6(B)

The Part-(B) outer family, once presented on exact planks by the homothety
`Kakeya.collarPlank`, is **not** pairwise essentially distinct — that is refuted in
`Kakeya/DimensionThree/Plank/CollarPlankEDRefutation.lean`, together with the transport from the
datum's hypothesis on the representatives — so the clause
`Kakeya.factoringAndMultPropGlobal` exports for it has to be obtained by extraction.  By the
lemmas below the extraction needs exactly one number:

`∀ i ∈ ts, card {j ∈ ts | (W j).carrier ⊆ (C-dilation of (W i))} ≤ d`,  `d` absolute,

and **nothing at `φ > a/b`**.  What is still missing for the presented family is not a packing
count at every `φ` but the pull-back of that one count through the presentation: a containment
`(W j).carrier ⊆ C · (W i)` constrains the *bodies* only through the common homothety
`Kakeya.comparablePlankEnvelope.shrink (windowConst R Cw)`, and turning it into a containment of
the corresponding **representative** planks — which *are* pairwise essentially distinct, by the
datum's own hypothesis — is a separate geometric step.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace Kakeya

variable {ι : Type*} {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1}

open Classical in
/-- **The ED conflict degree of a plank family is at most the number of members inside the
`C`-dilation of the anchor, for any `C ≥ 11`.**  Unconditional. -/
theorem edConflictDegree_le_card_filter_subset_dilation
    (s : Finset ι) (P : ι → ShadedPlank a b hab hb1) {C : ℝ≥0} (hC : 11 ≤ C) (i : ι) :
    edConflictDegree s (fun j => ((P j).carrier : Set (EuclideanSpace ℝ (Fin 3)))) i
      ≤ (s.filter fun j => ((P j).carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
          (((P i).toPrism3D.toPrismNDim.dilation C).carrier :
            Set (EuclideanSpace ℝ (Fin 3)))).card := by
  refine Finset.card_le_card ?_
  intro j hj
  have hj' := Finset.mem_filter.mp hj
  refine Finset.mem_filter.mpr ⟨hj'.1, ?_⟩
  have h11 := large_overlap_plank_subset_dilation (P i).toPrism3D (P j).toPrism3D hj'.2
  exact h11.trans (PrismNDim.dilation_carrier_mono (P i).toPrism3D.toPrismNDim hC)

open Classical in
/-- **The essentially-distinct extraction, from a bare dilation count.** -/
theorem exists_pairwise_plank_ED_subfamily_of_dilation_count
    {C : ℝ≥0} (hC : 11 ≤ C) {d : ℕ} (s : Finset ι) (P : ι → ShadedPlank a b hab hb1)
    (hcount : ∀ i ∈ s,
      (s.filter fun j => ((P j).carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
        (((P i).toPrism3D.toPrismNDim.dilation C).carrier :
          Set (EuclideanSpace ℝ (Fin 3)))).card ≤ d) :
    ∃ s' ⊆ s,
      (s' : Set ι).Pairwise
        (fun i j => _root_.IsEssentiallyDistinct (P i).carrier (P j).carrier) ∧
      s.card ≤ (d + 1) * s'.card ∧
      (∑ i ∈ s, volume (P i).shade)
        ≤ ((d : ENNReal) + 1) * ∑ i ∈ s', volume (P i).shade :=
  exists_inner_plank_ED_subfamily_weighted s P
    (fun i hi => le_trans (edConflictDegree_le_card_filter_subset_dilation s P hC i) (hcount i hi))

open Classical in
/-- **Only the endpoint `φ = a/b` of `Plank.IsThickeningNonconcentrated` is ever used.** -/
theorem card_filter_subset_dilation_le_of_isThickeningNonconcentrated
    (hb : 0 < b) {C M : ℝ≥0} (s : Finset ι) (P : ι → ShadedPlank a b hab hb1)
    (hNC : Plank.IsThickeningNonconcentrated s (fun i => (P i).toPrism3D) C M)
    (i : ι) (hi : i ∈ s) :
    ((s.filter fun j => ((P j).carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
        (((P i).toPrism3D.toPrismNDim.dilation C).carrier :
          Set (EuclideanSpace ℝ (Fin 3)))).card : ℝ≥0) ≤ M * (a / b) := by
  have hab1 : a / b ≤ 1 := (div_le_one hb).2 hab
  have h := hNC i hi (a / b) hab1 le_rfl
  rwa [Plank.plank_thickened_self_dilation_carrier hb hab1 (P i).toPrism3D C] at h

open Classical in
/-- **The existing `Plank.IsThickeningNonconcentrated` tool factors through the endpoint alone.** -/
theorem exists_pairwise_plank_ED_subfamily_of_isThickeningNonconcentrated_endpoint
    (hb : 0 < b) {C M : ℝ≥0} (hC : 11 ≤ C) (s : Finset ι) (P : ι → ShadedPlank a b hab hb1)
    (hNC : Plank.IsThickeningNonconcentrated s (fun i => (P i).toPrism3D) C M) :
    ∃ s' ⊆ s,
      (s' : Set ι).Pairwise
        (fun i j => _root_.IsEssentiallyDistinct (P i).carrier (P j).carrier) ∧
      s.card ≤ (⌈((M * (a / b) : ℝ≥0) : ℝ)⌉₊ + 1) * s'.card ∧
      (∑ i ∈ s, volume (P i).shade)
        ≤ ((⌈((M * (a / b) : ℝ≥0) : ℝ)⌉₊ : ENNReal) + 1) * ∑ i ∈ s', volume (P i).shade := by
  refine exists_pairwise_plank_ED_subfamily_of_dilation_count hC s P ?_
  intro i hi
  have h := card_filter_subset_dilation_le_of_isThickeningNonconcentrated hb s P hNC i hi
  have hR : (((s.filter fun j => ((P j).carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
      (((P i).toPrism3D.toPrismNDim.dilation C).carrier :
        Set (EuclideanSpace ℝ (Fin 3)))).card : ℝ≥0) : ℝ) ≤ ((M * (a / b) : ℝ≥0) : ℝ) := by
    exact_mod_cast h
  exact_mod_cast hR.trans (Nat.le_ceil _)

end Kakeya

end

end
