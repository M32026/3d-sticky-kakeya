/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.ShadingTransport

/-!
# The assigned slab family

`Plank.sharedSlabThickenedShadingDilation` shades a representative prism `Q` by the union of the
shadings of *all* planks of `s'` whose representative is assigned the same slab as `Q`, i.e. by the
finite set `s'.filter (fun i => slabOf (repr i) = slabOf Q)`.  That set is the object the whole
slab-local analysis of GWZ Lemma 6.13 runs on, and this file gives it a name,
`Plank.assignedSlabFamily`, together with the partition API it satisfies.

The point of naming it is that it is *exact*: the assigned families are pairwise disjoint and cover
`s'`, so a sum of slab-local mass bounds over the used slabs telescopes into a global bound with no
overlap loss at all.  This is what distinguishes it from `Plank.inSlabFamilyC`, which is a
*geometric* family — every plank comparable with the slab, whether or not it was assigned to it —
and which genuinely overlaps between slabs, so that summing over it costs the slab overlap constant
`Nov`.  The two are used for different purposes and must not be confused: `inSlabFamilyC` supplies
containment and angle information, `assignedSlabFamily` supplies the partition.

Nothing here is deep; the content is that the shading actually used by the public statement of
Lemma 6.13 is definitionally the assigned-family shading
(`Plank.sharedSlabThickenedShadingDilation_shade_assigned`), so the partition lemmas apply to it
verbatim.
-/

@[expose] public section

open MeasureTheory Convexity
open scoped NNReal Real ENNReal

noncomputable section

namespace Plank

variable {ι : Type*} {τ : Type*} {σ : Type*}

open scoped Classical in
/-- **The assigned slab family**: the planks of `s'` whose representative was assigned the slab
index `S`.

This is the exact fibre of `slabOf ∘ repr` over `S`, not the geometric family
`Plank.inSlabFamilyC`.  It is the family the shared thickened shading is built from.

The representative type `τ` is arbitrary: this family is pure `Finset` combinatorics and never
inspects the geometry of a representative, so Lemma 6.13 can instantiate it at the typed
`Plank.ThickenedPlank θ b hθ1 hb1` without erasing to `EnsemblePrism`. -/
def assignedSlabFamily (s' : Finset ι) (repr : ι → τ)
    (slabOf : τ → σ) (S : σ) : Finset ι :=
  s'.filter (fun i => slabOf (repr i) = S)

@[simp] theorem mem_assignedSlabFamily {s' : Finset ι} {repr : ι → τ}
    {slabOf : τ → σ} {S : σ} {i : ι} :
    i ∈ assignedSlabFamily s' repr slabOf S ↔ i ∈ s' ∧ slabOf (repr i) = S := by
  simp [assignedSlabFamily]

open scoped Classical in
theorem assignedSlabFamily_subset (s' : Finset ι) (repr : ι → τ)
    (slabOf : τ → σ) (S : σ) :
    assignedSlabFamily s' repr slabOf S ⊆ s' :=
  Finset.filter_subset _ _

/-- Every active index lies in the assigned family of its own slab. -/
theorem mem_assignedSlabFamily_self {s' : Finset ι} {repr : ι → τ}
    {slabOf : τ → σ} {i : ι} (hi : i ∈ s') :
    i ∈ assignedSlabFamily s' repr slabOf (slabOf (repr i)) :=
  mem_assignedSlabFamily.mpr ⟨hi, rfl⟩

/-- Assigned families of distinct slab indices are disjoint. -/
theorem assignedSlabFamily_disjoint (s' : Finset ι) (repr : ι → τ)
    (slabOf : τ → σ) {S T : σ} (hST : S ≠ T) :
    Disjoint (assignedSlabFamily s' repr slabOf S) (assignedSlabFamily s' repr slabOf T) :=
  Finset.disjoint_left.mpr fun _ hi hiT =>
    hST ((mem_assignedSlabFamily.mp hi).2.symm.trans (mem_assignedSlabFamily.mp hiT).2)

open scoped Classical in
/-- The assigned families over the *image* slab set cover `s'` exactly. -/
theorem biUnion_assignedSlabFamily (s' : Finset ι) (repr : ι → τ)
    (slabOf : τ → σ) (𝒮 : Finset σ)
    (h𝒮 : ∀ i ∈ s', slabOf (repr i) ∈ 𝒮) :
    𝒮.biUnion (fun S => assignedSlabFamily s' repr slabOf S) = s' := by
  ext i
  simp only [Finset.mem_biUnion, mem_assignedSlabFamily]
  exact ⟨fun ⟨_, _, hi, _⟩ => hi, fun hi => ⟨_, h𝒮 i hi, hi, rfl⟩⟩

open scoped Classical in
/-- The cardinalities of the assigned families sum to `|s'|`. -/
theorem sum_card_assignedSlabFamily (s' : Finset ι) (repr : ι → τ)
    (slabOf : τ → σ) (𝒮 : Finset σ)
    (h𝒮 : ∀ i ∈ s', slabOf (repr i) ∈ 𝒮) :
    ∑ S ∈ 𝒮, (assignedSlabFamily s' repr slabOf S).card = s'.card := by
  rw [← Finset.card_biUnion fun S _ T _ hST => assignedSlabFamily_disjoint s' repr slabOf hST,
    biUnion_assignedSlabFamily s' repr slabOf 𝒮 h𝒮]

open scoped Classical in
/-- The shading union of `s'` splits as the union over the assigned families. -/
theorem biUnion_shade_eq_biUnion_assignedSlabFamily (s' : Finset ι)
    (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3))) (repr : ι → τ)
    (slabOf : τ → σ) (𝒮 : Finset σ)
    (h𝒮 : ∀ i ∈ s', slabOf (repr i) ∈ 𝒮) :
    (⋃ i ∈ s', (Y' i).shade)
      = ⋃ S ∈ 𝒮, ⋃ i ∈ assignedSlabFamily s' repr slabOf S, (Y' i).shade := by
  conv_lhs => rw [← biUnion_assignedSlabFamily s' repr slabOf 𝒮 h𝒮]
  exact Finset.set_biUnion_biUnion _ _ _

/-! ## The two halves of the bounded-overlap bound

These are pure index combinatorics about a finite family of index sets, stated here because the
slab-local fullness layer and the good-box layer
(`Plank.sum_volume_sdiff_goodBoxUnionLocal_le_of_trimmed`) need them, and the latter sits upstream
of `Kakeya.plankReduction`.

They are what replaces the exact `Plank.assignedSlabFamily` partition when the families in play are
the *geometric* `Plank.inSlabFamilyC` ones, which genuinely overlap — but only `Nov`-fold,
with `Nov` uniform (`Plank.slab_index_overlap_le`).
-/

open scoped Classical in
/-- **The counting half of the overlap bound** (extra69, `note:sumCardLeMulCardOfOverlap`).

If every family `Fam S` sits inside `s` and every index of `s` lies in at most `Nov` of them, then
`∑_{S ∈ 𝒮} |Fam S| ≤ Nov · |s|`.  This is the double count that replaces the
configuration-dependent
`|𝒮|` in the slab-local fullness layer. -/
theorem sum_card_le_mul_card_of_overlap {σ' : Type*}
    (s : Finset ι) (𝒮 : Finset σ') (Fam : σ' → Finset ι) (Nov : ℕ)
    (hsub : ∀ S ∈ 𝒮, Fam S ⊆ s)
    (hov : ∀ i ∈ s, (𝒮.filter fun S => i ∈ Fam S).card ≤ Nov) :
    ∑ S ∈ 𝒮, (Fam S).card ≤ Nov * s.card := by
  classical
  calc
    ∑ S ∈ 𝒮, (Fam S).card = ∑ S ∈ 𝒮, ∑ i ∈ s, (if i ∈ Fam S then (1 : ℕ) else 0) :=
      Finset.sum_congr rfl fun S hS => by
        rw [← Finset.card_filter, Finset.filter_mem_eq_inter,
          Finset.inter_eq_right.2 (hsub S hS)]
    _ = ∑ i ∈ s, ∑ S ∈ 𝒮, (if i ∈ Fam S then (1 : ℕ) else 0) := Finset.sum_comm
    _ ≤ ∑ i ∈ s, Nov := Finset.sum_le_sum fun i hi => by
      rw [← Finset.card_filter]; exact hov i hi
    _ = Nov * s.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

open scoped Classical in
/-- **The covering half of the overlap bound** (extra69, `note:sumLeSumFamiliesOfCover`).

If every index of `s` lies in at least one family `Fam S`, `S ∈ 𝒮`, then the total weight of `s` is
at most the sum of the families' weights, for any weight function into `[0, ∞]`. -/
theorem sum_le_sum_families_of_cover {σ' : Type*}
    (s : Finset ι) (𝒮 : Finset σ') (Fam : σ' → Finset ι) (f : ι → ENNReal)
    (hsub : ∀ S ∈ 𝒮, Fam S ⊆ s)
    (hcover : ∀ i ∈ s, ∃ S ∈ 𝒮, i ∈ Fam S) :
    ∑ i ∈ s, f i ≤ ∑ S ∈ 𝒮, ∑ i ∈ Fam S, f i := by
  calc
    ∑ i ∈ s, f i ≤ ∑ i ∈ s, ∑ S ∈ 𝒮, (if i ∈ Fam S then f i else 0) :=
      Finset.sum_le_sum fun i hi => by
        obtain ⟨S, hS, hiS⟩ := hcover i hi
        calc
          f i = (if i ∈ Fam S then f i else 0 : ENNReal) := by simp [hiS]
          _ ≤ ∑ S' ∈ 𝒮, (if i ∈ Fam S' then f i else 0) :=
            Finset.single_le_sum (f := fun S' => if i ∈ Fam S' then f i else 0)
              (fun _ _ => zero_le) hS
    _ = ∑ S ∈ 𝒮, ∑ i ∈ s, (if i ∈ Fam S then f i else 0) := Finset.sum_comm
    _ = ∑ S ∈ 𝒮, ∑ i ∈ Fam S, f i :=
      Finset.sum_congr rfl fun S hS => by
        rw [← Finset.sum_filter, Finset.filter_mem_eq_inter,
          Finset.inter_eq_right.2 (hsub S hS)]

/-! ## The shared thickened shading is the assigned-family shading -/

/-- The shade of `Plank.sharedSlabThickenedShadingDilation` is, definitionally, the dilated carrier
cut against the shading union of the *assigned* family of `Q`'s slab. -/
theorem sharedSlabThickenedShadingDilation_shade_assigned (Cbox : ℝ≥0)
    (s' : Finset ι) (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (anchor : τ → EnsemblePrism) (repr : ι → τ) (slabOf : τ → σ) (Q : τ) :
    (sharedSlabThickenedShadingDilation Cbox s' Y' anchor repr slabOf Q).shade =
      (((anchor Q).dilation Cbox).carrier : Set (EuclideanSpace ℝ (Fin 3))) ∩
        ⋃ i ∈ assignedSlabFamily s' repr slabOf (slabOf Q), (Y' i).shade := rfl

/-- The shade of the shared thickened shading is contained in the assigned-family shading union.
This is the monotonicity step every slab-local mass bound needs in order to be transported to the
public shading. -/
theorem sharedSlabThickenedShadingDilation_shade_subset_assigned (Cbox : ℝ≥0)
    (s' : Finset ι) (Y' : ι → ShadedBody (EuclideanSpace ℝ (Fin 3)))
    (anchor : τ → EnsemblePrism) (repr : ι → τ) (slabOf : τ → σ) (Q : τ) :
    (sharedSlabThickenedShadingDilation Cbox s' Y' anchor repr slabOf Q).shade ⊆
      ⋃ i ∈ assignedSlabFamily s' repr slabOf (slabOf Q), (Y' i).shade :=
  Set.inter_subset_right

/-! ## Slab-complete restriction: the representative bookkeeping

The Item 2 route is allowed to delete *slabs*, through the good-slab prune of
`Plank.exists_dominantGoodSlabRefinement`, but it is not allowed to delete *representatives*: the
common fibre size `N` of the preassembly must survive without a new pigeonhole step, and the
two-sided fibre bounds `N / cN ≤ #rep⁻¹(Q) ≤ cN N` must be reusable verbatim on the restricted
family.

Slab-complete deletion is exactly what makes that work, and this section records why, in three
purely combinatorial identities.  Nothing here mentions geometry, measure, or the scale `a`;
they are `Finset` identities about the fibres of `slabOf ∘ repr`, deliberately kept apart from
the geometric
layers.

The two that carry the content are:

* `Plank.filter_repr_assignedSlabFamily_eq` — a representative's fibre inside the assigned family of
  its own slab is its *whole* fibre.  This is what preserves the fibre-size bounds.
* `Plank.assignedSlabFamily_filter_slab_mem` — restricting the index set to a set of retained slabs
  does not change the assigned family of any retained slab.  This is what "slab-complete" means.

Together they say: after a slab-complete restriction, a surviving representative sees exactly the
same fibre it saw before, so no bound about it has to be re-derived.
-/

/-! ### Representative fibres inside the assigned family -/

open scoped Classical in
/-- **A representative's fibre is not cut by passing to its own slab's assigned family.**  If
`slabOf Q = S`, then every index with representative `Q` is by definition assigned to `S`, so
intersecting with the assigned family of `S` removes nothing.

This is the identity that lets the preassembly's two-sided fibre bounds
`N / cN ≤ #rep⁻¹(Q) ≤ cN N` be reused verbatim on the assigned family — no new pigeonhole, and in
particular no representative-cardinality retention factor. -/
theorem filter_repr_assignedSlabFamily_eq (s' : Finset ι) (repr : ι → τ) (slabOf : τ → σ)
    (S : σ) {Q : τ} (hQ : slabOf Q = S) :
    (assignedSlabFamily s' repr slabOf S).filter (fun i => repr i = Q)
      = s'.filter (fun i => repr i = Q) := by
  ext i
  simp only [Finset.mem_filter, mem_assignedSlabFamily]
  exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2 ▸ hQ⟩, h.2⟩⟩

open scoped Classical in
/-- **The assigned family's representatives are exactly the canonical slab fibre.**  Taking the
`repr`-image of the assigned family of `S` gives precisely the members of the active family lying
over `S`.

This is the identity that identifies the *output* family of the C-linear route, run on the assigned
family, with the canonical public fibre `R.indexSet.filter (fun Q => slabOf Q = S)`.  Note it is an
identity of *representative* families, not of index families: no comparison between
`Plank.inSlabFamilyC` and `Plank.assignedSlabFamily` is involved. -/
theorem image_repr_assignedSlabFamily (s' : Finset ι) (repr : ι → τ) (slabOf : τ → σ) (S : σ) :
    (assignedSlabFamily s' repr slabOf S).image repr
      = (s'.image repr).filter (fun Q => slabOf Q = S) := by
  rw [assignedSlabFamily, Finset.filter_image]

/-! ### Slab-complete restriction of the index set -/

open scoped Classical in
/-- **Slab-complete restriction does not change a retained slab's assigned family.**  Deleting the
indices whose slab was rejected leaves the assigned family of every *retained* slab untouched.

This is the precise sense in which the good-slab prune is slab-complete: if a slab survives, its
whole assigned family survives, hence every surviving representative keeps its entire fibre.  It is
what separates this permitted deletion from representative-level pruning. -/
theorem assignedSlabFamily_filter_slab_mem (s' : Finset ι) (repr : ι → τ) (slabOf : τ → σ)
    (𝒮g : Finset σ) {S : σ} (hS : S ∈ 𝒮g) :
    assignedSlabFamily (s'.filter (fun i => slabOf (repr i) ∈ 𝒮g)) repr slabOf S
      = assignedSlabFamily s' repr slabOf S := by
  ext i
  simp only [mem_assignedSlabFamily, Finset.mem_filter]
  exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2 ▸ hS⟩, h.2⟩⟩

end Plank

end
