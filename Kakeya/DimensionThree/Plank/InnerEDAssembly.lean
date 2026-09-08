/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.Plank.EDWeightedExtraction
public import Kakeya.DimensionThree.Plank.InnerSlabNonconcentration
public import Kakeya.DimensionThree.Plank.SlabFibreFrostmanReduction

/-!
# The inner essentially distinct family of GWZ 6.6(B)

`Kakeya.innerFamilySlabNonconcentration` normalises the fine `δ`-tube family inside one outer plank
and returns the inner plank family `Pj` indexed by *all* of `q`, together with the fullness and
density transfers (both carrying the normalisation constant `Cnorm`) and the slab
non-concentration bound.  What it does **not** return is essential distinctness: the normalisation
is an affine map, so it cannot create it.

This module performs the missing step.  Given a bound `d` on `Kakeya.edConflictDegree` for the
inner planks, `Kakeya.exists_inner_ED_factorisation_package` extracts a pairwise essentially
distinct subfamily by `Kakeya.exists_inner_plank_ED_subfamily_weighted` and re-indexes it onto
`Fin _`, so that the resulting index type lives in `Type` — which is what the inner block of
`Kakeya.factoringAndMultPropGlobal` quantifies over.

## Where the losses go

Every loss is explicit in the conclusion; none is absorbed into a power of `δ` here, and none is
silently dropped.  There are exactly three, and they are tracked separately:

* `d + 1` on the **shade mass**, from the weighted extraction.  This is what drives the fullness
  clause, through `ShadedBody.fullness'_le_of_subset_of_sum_shade_le`, and the multiplicity clause,
  through `Kakeya.multiplicity_pigeon_transfer`.
* `d + 1` on the **cardinality**, also from the weighted extraction.  The slab clause needs it:
  restriction shrinks the left-hand side of the non-concentration bound but it shrinks `q.card` on
  the right-hand side too, so the bound only survives at the cost of this factor.
* `Cnorm` on **fullness and density**, from the affine normalisation.  `Δ_max(inner) ≤ Δ_max(𝒯)`
  with no loss is false: normalising an `a × b × 1` plank to the unit ball is anisotropic, so shade
  and body volumes rescale differently.

The fullness clause is stated in the multiplicative form

`fullness q 𝒯 ≤ Cnorm * (d + 1) * fullness qj Pj`

rather than as `(Cnorm * (d+1))⁻¹ * fullness q 𝒯 ≤ fullness qj Pj`; the two carry the same
information, and the multiplicative form avoids `ℝ≥0` inverses.  Upgrading it to the `δ`-scale form
`δ ^ ηᵢ ≤ fullness qj Pj` is the job of the caller's smallness threshold, which is where
`Cnorm * (d + 1)` gets absorbed against `δ ^ (-(ηᵢ - η))`.

## Re-indexing

There is no re-indexing API for shaded families in this repository, so the four transport lemmas
are proved here, all along a `Finset.map` by an embedding (`Finset.sum_map` and `Finset.filter_map`
need no injectivity side conditions, unlike `Finset.image`).  They are stated generically and are
reusable.
-/

@[expose] public section

open MeasureTheory Metric Convexity
open scoped NNReal Real

noncomputable section

namespace Kakeya

section Reindex

/-- **Every finite set is the image of `Fin s.card` under an embedding.**

The re-indexing device: it turns a family indexed by a `Finset ι`, where `ι` may live in any
universe, into a family indexed by `Fin s.card`, which lives in `Type`. -/
theorem exists_finEmbedding_map_univ_eq {ι : Type*} (s : Finset ι) :
    ∃ e : Fin s.card ↪ ι, Finset.univ.map e = s := by
  let e : Fin s.card ↪ ι :=
    ⟨fun k => ((s.equivFin.symm k : {x // x ∈ s}) : ι), by
      intro a b hab
      apply (s.equivFin.symm).injective
      exact Subtype.ext hab⟩
  refine ⟨e, ?_⟩
  ext x
  constructor
  · intro hx
    rcases Finset.mem_map.mp hx with ⟨k, hk, rfl⟩
    exact (s.equivFin.symm k).2
  · intro hx
    exact Finset.mem_map.mpr ⟨s.equivFin ⟨x, hx⟩, Finset.mem_univ _, by
      dsimp [e]
      simp⟩

variable {E : Type*}

/-- Fullness is invariant under re-indexing along an embedding. -/
theorem ShadedBody.fullness'_map [TopologicalSpace E] [ConvexSpace ℝ E] [MeasureSpace E]
    {ι κ : Type*} (s : Finset κ) (e : κ ↪ ι) (V : ι → ShadedBody E) :
    ShadedBody.fullness' (s.map e) V = ShadedBody.fullness' s (fun k => V (e k)) := by
  simp [ShadedBody.fullness', Finset.sum_map]

/-- Fullness (the `ℝ≥0` form) is invariant under re-indexing along an embedding. -/
theorem ShadedBody.fullness_map [TopologicalSpace E] [ConvexSpace ℝ E] [MeasureSpace E]
    {ι κ : Type*} (s : Finset κ) (e : κ ↪ ι) (V : ι → ShadedBody E) :
    ShadedBody.fullness (s.map e) V = ShadedBody.fullness s (fun k => V (e k)) := by
  rw [ShadedBody.fullness, ShadedBody.fullness, ShadedBody.fullness'_map s e V]

/-- Multiplicity is invariant under re-indexing along an embedding. -/
theorem ShadedBody.multiplicity_map [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {ι κ : Type*} (s : Finset κ) (e : κ ↪ ι) (V : ι → ShadedBody E) :
    ShadedBody.multiplicity (s.map e) V = ShadedBody.multiplicity s (fun k => V (e k)) := by
  have hsum : ∑ i ∈ s.map e, volume (V i).shade
      = ∑ k ∈ s, volume (V (e k)).shade := Finset.sum_map _ _ _
  have hU : (⋃ i ∈ s.map e, (V i).shade) = ⋃ k ∈ s, (V (e k)).shade := by
    ext y
    simp only [Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨i, hi, hy⟩
      obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hi
      exact ⟨k, hk, hy⟩
    · rintro ⟨k, hk, hy⟩
      exact ⟨e k, Finset.mem_map_of_mem e hk, hy⟩
  rw [ShadedBody.multiplicity_eq_div, ShadedBody.multiplicity_eq_div, hsum, hU]

/-- The maximal density is invariant under re-indexing along an embedding. -/
theorem maxDensity_map [TopologicalSpace E] [ConvexSpace ℝ E] [MeasureSpace E]
    {ι κ : Type*} (s : Finset κ) (e : κ ↪ ι) (W : ι → ConvexSpaceBody E) :
    maxDensity (s.map e) W = maxDensity s (fun k => W (e k)) := by
  classical
  let Wk : κ → ConvexSpaceBody E := fun k => W (e k)
  have hspec_im : density_maximizer (s.map e) W ∈ (s.map e).powerset ∧
      ∀ t ∈ (s.map e).powerset,
        densityInConvexHulliUnion W t ≤
          densityInConvexHulliUnion W (density_maximizer (s.map e) W) := by
    simpa [density_maximizer] using
      (Finset.exists_max_image (s.map e).powerset (densityInConvexHulliUnion W)
        (s.map e).powerset_nonempty).choose_spec
  have hspec_k : density_maximizer s Wk ∈ s.powerset ∧
      ∀ t ∈ s.powerset,
        densityInConvexHulliUnion Wk t ≤
          densityInConvexHulliUnion Wk (density_maximizer s Wk) := by
    simpa [density_maximizer] using
      (Finset.exists_max_image s.powerset (densityInConvexHulliUnion Wk)
        s.powerset_nonempty).choose_spec
  have hsub_im : density_maximizer (s.map e) W ⊆ s.map e :=
    Finset.mem_powerset.mp hspec_im.1
  have hsub_k : density_maximizer s Wk ⊆ s :=
    Finset.mem_powerset.mp hspec_k.1
  have hmap : ∀ t : Finset κ,
      densityInConvexHulliUnion W (t.map e) = densityInConvexHulliUnion Wk t := by
    intro t
    unfold densityInConvexHulliUnion
    have hsum : (∑ i ∈ t.map e, volume (W i).carrier) = (∑ k ∈ t, volume (W (e k)).carrier) := by
      simp
    have hunion : (⋃ i ∈ t.map e, (W i).carrier) = (⋃ k ∈ t, (W (e k)).carrier) := by
      ext x
      simp only [Set.mem_iUnion, exists_prop]
      constructor
      · rintro ⟨i, hi, hy⟩
        obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hi
        exact ⟨k, hk, hy⟩
      · rintro ⟨k, hk, hy⟩
        exact ⟨e k, Finset.mem_map_of_mem e hk, hy⟩
    rw [hsum, hunion]
  have himage : ∀ t : Finset ι, t ⊆ s.map e → t = (s.filter (fun k => e k ∈ t)).map e := by
    intro t ht
    apply Finset.Subset.antisymm
    · intro i hi
      rcases Finset.mem_map.mp (ht hi) with ⟨k, hk, rfl⟩
      exact Finset.mem_map.mpr ⟨k, Finset.mem_filter.mpr ⟨hk, hi⟩, rfl⟩
    · intro i hi
      rcases Finset.mem_map.mp hi with ⟨k, hk, rfl⟩
      exact (Finset.mem_filter.mp hk).2
  apply le_antisymm
  · calc
      maxDensity (s.map e) W
          = densityInConvexHulliUnion W (density_maximizer (s.map e) W) := rfl
      _ = densityInConvexHulliUnion W
            ((s.filter (fun k => e k ∈ density_maximizer (s.map e) W)).map e) := by
            conv_lhs => rw [himage (density_maximizer (s.map e) W) hsub_im]
      _ = densityInConvexHulliUnion Wk
            (s.filter (fun k => e k ∈ density_maximizer (s.map e) W)) := by
            rw [hmap]
      _ ≤ densityInConvexHulliUnion Wk (density_maximizer s Wk) := by
            exact hspec_k.2 _ (Finset.mem_powerset.mpr (Finset.filter_subset _ _))
      _ = maxDensity s Wk := rfl
  · calc
      maxDensity s Wk = densityInConvexHulliUnion Wk (density_maximizer s Wk) := rfl
      _ = densityInConvexHulliUnion W ((density_maximizer s Wk).map e) := by
            rw [hmap]
      _ ≤ densityInConvexHulliUnion W (density_maximizer (s.map e) W) := by
            have hu' : (density_maximizer s Wk).map e ⊆ s.map e := by
              intro x hx
              rcases Finset.mem_map.mp hx with ⟨k, hk, rfl⟩
              exact Finset.mem_map.mpr ⟨k, hsub_k hk, rfl⟩
            exact hspec_im.2 _ (Finset.mem_powerset.mpr hu')
      _ = maxDensity (s.map e) W := rfl

end Reindex

section Slab

variable {a b : ℝ≥0} {hab : a ≤ b} {hb1 : b ≤ 1} {ι : Type*}

/-- The wide slab subfamily is monotone in the index set. -/
theorem Plank.inWideSlabFamily_mono {φ R : ℝ≥0} {hφR : φ ≤ R} {s t : Finset ι}
    (hts : t ⊆ s) (V : ι → Plank a b hab hb1) (Sφ : Prism3D φ R R hφR le_rfl) :
    Plank.inWideSlabFamily t V Sφ ⊆ Plank.inWideSlabFamily s V Sφ := by
  intro i hi
  rw [Plank.mem_inWideSlabFamily] at hi ⊢
  exact ⟨hts hi.1, hi.2⟩

/-- The wide slab subfamily commutes with re-indexing along an embedding. -/
theorem Plank.inWideSlabFamily_map {φ R : ℝ≥0} {hφR : φ ≤ R} {κ : Type*}
    (s : Finset κ) (e : κ ↪ ι) (V : ι → Plank a b hab hb1) (Sφ : Prism3D φ R R hφR le_rfl) :
    Plank.inWideSlabFamily (s.map e) V Sφ
      = (Plank.inWideSlabFamily s (fun k => V (e k)) Sφ).map e := by
  classical
  simp [Plank.inWideSlabFamily, Finset.filter_map]

end Slab

/-- Provenance of a reindexed inner plank family.  This internal certificate keeps the embedding
into the pre-extraction family available for geometric estimates without identifying the fresh
index type with the source type. -/
structure InnerEDSource
    {ιq ιj : Type*} {a' b' : ℝ≥0} {ha'b' : a' ≤ b'} {hb'1 : b' ≤ 1}
    (q : Finset ιq) (Pj : ιq → ShadedPlank a' b' ha'b' hb'1)
    (qj : Finset ιj) (P : ιj → ShadedPlank a' b' ha'b' hb'1) where
  embedding : ιj ↪ ιq
  mem_source : ∀ k ∈ qj, embedding k ∈ q
  plank_eq : ∀ k, P k = Pj (embedding k)

/-- Dilated-thickening non-concentration passes to a reindexed subfamily when the provenance
embedding identifies every target plank with its source plank. -/
theorem InnerEDSource.isThickeningNonconcentrated
    {ιq ιj : Type*} {a' b' : ℝ≥0} {ha'b' : a' ≤ b'} {hb'1 : b' ≤ 1}
    {C M : ℝ≥0}
    {q : Finset ιq} {Pj : ιq → ShadedPlank a' b' ha'b' hb'1}
    {qj : Finset ιj} {P : ιj → ShadedPlank a' b' ha'b' hb'1}
    (source : InnerEDSource q Pj qj P)
    (h : Plank.IsThickeningNonconcentrated q (fun i ↦ (Pj i).toPrism3D) C M) :
    Plank.IsThickeningNonconcentrated qj (fun k ↦ (P k).toPrism3D) C M := by
  classical
  intro k hk φ hφ1 hratio
  let sk := qj.filter fun l ↦
    ((P l).carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
      (((Plank.thickened (P k).toPrism3D φ hφ1).toPrismNDim.dilation C).carrier :
        Set (EuclideanSpace ℝ (Fin 3)))
  let si := q.filter fun l ↦
    ((Pj l).carrier : Set (EuclideanSpace ℝ (Fin 3))) ⊆
      (((Plank.thickened (Pj (source.embedding k)).toPrism3D φ hφ1).toPrismNDim.dilation C).carrier :
        Set (EuclideanSpace ℝ (Fin 3)))
  have hmap : sk.map source.embedding ⊆ si := by
    intro l hl
    obtain ⟨l', hl', rfl⟩ := Finset.mem_map.mp hl
    have hl'' := Finset.mem_filter.mp hl'
    apply Finset.mem_filter.mpr
    refine ⟨source.mem_source l' hl''.1, ?_⟩
    simpa only [source.plank_eq] using hl''.2
  have hcard : sk.card ≤ si.card := by
    rw [← Finset.card_map]
    exact Finset.card_le_card hmap
  have hsource := h (source.embedding k) (source.mem_source k hk) φ hφ1 hratio
  change (sk.card : ℝ≥0) ≤ M * φ
  have hcard' : (sk.card : ℝ≥0) ≤ (si.card : ℝ≥0) := by exact_mod_cast hcard
  exact hcard'.trans (by simpa [si] using hsource)

/-- **The inner essentially distinct plank family of GWZ 6.6(B).**

Input: the inner family `Pj` produced by `Kakeya.innerFamilySlabNonconcentration` on the index set
`q` — window containment, fullness transfer with `Cnorm`, density transfer with `Cnorm`, and slab
non-concentration with an arbitrary constant `Cslab` — together with a bound `d` on the ED conflict
degree of the
inner planks.

Output: a pairwise essentially distinct subfamily, re-indexed onto a type in `Type`, retaining all
four clauses with the three explicit losses `d + 1` (mass), `d + 1` (cardinality) and `Cnorm`
(fullness and density).  Essential distinctness is *produced* by the weighted extraction; it is
never assumed, and nothing is assumed about enlarged planks. -/
theorem exists_inner_ED_factorisation_package
    {ιq : Type*} {a' b' δ : ℝ≥0} {ha'b' : a' ≤ b'} {hb'1 : b' ≤ 1}
    (q : Finset ιq) (T : ιq → ShadedTube δ (EuclideanSpace ℝ (Fin 3)))
    (Pj : ιq → ShadedPlank a' b' ha'b' hb'1)
    (Cnorm Cslab : ℝ≥0) (_hCnorm : 1 ≤ Cnorm)
    (hwindow : ∀ i ∈ q, ((Pj i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
      ⊆ Metric.closedBall 0 (plankWindowRadius : ℝ))
    (hfull : ShadedBody.fullness q (fun i => (T i).toShadedBody)
      ≤ Cnorm * ShadedBody.fullness q (fun i => (Pj i).toShadedBody))
    (hmaxd : maxDensity q (fun i => (Pj i).toConvexSpaceBody)
      ≤ (Cnorm : ENNReal) * maxDensity q (fun i => (T i).toConvexSpaceBody))
    (hslab : ∀ (φ : ℝ≥0) (hφR : φ ≤ Rslab), a' / b' ≤ φ →
      ∀ (S : Prism3D φ Rslab Rslab hφR le_rfl),
        ((Plank.inWideSlabFamily q (fun i => (Pj i).toPrism3D) S).card : ℝ≥0)
          ≤ Cslab * φ ^ (1 : ℝ) * (q.card : ℝ≥0))
    {d : ℕ} (hdeg : ∀ i ∈ q, edConflictDegree q (fun j => (Pj j).carrier) i ≤ d) :
    ∃ (ιj : Type) (qj : Finset ιj) (P : ιj → ShadedPlank a' b' ha'b' hb'1)
        (source : InnerEDSource q Pj qj P),
      (∀ k ∈ qj, source.embedding k ∈ q) ∧
      (∀ k, P k = Pj (source.embedding k)) ∧
      (∀ i ∈ qj, ((P i).carrier : Set (EuclideanSpace ℝ (Fin 3)))
        ⊆ Metric.closedBall 0 (plankWindowRadius : ℝ)) ∧
      (qj : Set ιj).Pairwise
        (fun i j => _root_.IsEssentiallyDistinct (P i).carrier (P j).carrier) ∧
      q.card ≤ (d + 1) * qj.card ∧
      qj.card ≤ q.card ∧
      (∑ i ∈ q, volume (Pj i).shade)
        ≤ ((d : ENNReal) + 1) * ∑ i ∈ qj, volume (P i).shade ∧
      ShadedBody.fullness q (fun i => (T i).toShadedBody)
        ≤ Cnorm * ((d : ℝ≥0) + 1) * ShadedBody.fullness qj (fun i => (P i).toShadedBody) ∧
      maxDensity qj (fun i => (P i).toConvexSpaceBody)
        ≤ (Cnorm : ENNReal) * maxDensity q (fun i => (T i).toConvexSpaceBody) ∧
      (∀ (φ : ℝ≥0) (hφR : φ ≤ Rslab), a' / b' ≤ φ →
        ∀ (S : Prism3D φ Rslab Rslab hφR le_rfl),
          ((Plank.inWideSlabFamily qj (fun i => (P i).toPrism3D) S).card : ℝ≥0)
            ≤ ((d : ℝ≥0) + 1) * Cslab * φ ^ (1 : ℝ) * (qj.card : ℝ≥0)) ∧
      ShadedBody.multiplicity q (fun i => (Pj i).toShadedBody)
        ≤ ((d : ENNReal) + 1) * ShadedBody.multiplicity qj (fun i => (P i).toShadedBody) := by
  obtain ⟨sED, hsq, hEDpair, hcardq, hmassq⟩ :=
    exists_inner_plank_ED_subfamily_weighted q Pj hdeg
  obtain ⟨e, hemap⟩ := exists_finEmbedding_map_univ_eq sED
  let qj : Finset (Fin sED.card) := Finset.univ
  let P : Fin sED.card → ShadedPlank a' b' ha'b' hb'1 := fun k => Pj (e k)
  let bodies : ιq → ShadedBody (EuclideanSpace ℝ (Fin 3)) := fun i => (Pj i).toShadedBody
  have hmem : ∀ k : Fin sED.card, e k ∈ sED := by
    intro k
    simpa [hemap] using (Finset.mem_map_of_mem e (Finset.mem_univ k))
  have hmemq : ∀ k : Fin sED.card, e k ∈ q := fun k => hsq (hmem k)
  have hcard_univ : qj.card = sED.card := by
    simp [qj]
  have hcard_le : qj.card ≤ q.card := by
    rw [hcard_univ]
    exact Finset.card_le_card hsq
  have hsum : (∑ k ∈ qj, volume (P k).shade) = ∑ i ∈ sED, volume (Pj i).shade := by
    simpa [qj, P, hemap] using
      (Finset.sum_map qj e (fun i => volume (Pj i).shade)).symm
  have hmassq' : (∑ i ∈ q, volume (bodies i).shade)
      ≤ ((d : ENNReal) + 1) * ∑ i ∈ sED, volume (bodies i).shade := by
    simpa [bodies] using hmassq
  have hfull' : ShadedBody.fullness' q bodies
      ≤ ((d : ENNReal) + 1) * ShadedBody.fullness' sED bodies :=
    ShadedBody.fullness'_le_of_subset_of_sum_shade_le q sED bodies hsq hmassq'
  have hfull'_map : ShadedBody.fullness' sED bodies
      = ShadedBody.fullness' qj (fun k => bodies (e k)) := by
    simpa [qj, hemap] using
      ShadedBody.fullness'_map qj e bodies
  have hfull'' : ShadedBody.fullness' q bodies
      ≤ ((d : ENNReal) + 1) * ShadedBody.fullness' qj (fun k => bodies (e k)) := by
    simpa [hfull'_map] using hfull'
  have hfullNN : ShadedBody.fullness q bodies
      ≤ ((d : ℝ≥0) + 1) * ShadedBody.fullness qj (fun k => bodies (e k)) := by
    rw [← ENNReal.coe_le_coe]
    rw [ENNReal.coe_mul]
    rw [ShadedBody.coe_fullness q bodies]
    rw [ShadedBody.coe_fullness qj (fun k => bodies (e k))]
    simpa [ENNReal.coe_add, ENNReal.coe_natCast, ENNReal.coe_one] using hfull''
  have hfull_final : ShadedBody.fullness q (fun i => (T i).toShadedBody)
      ≤ Cnorm * ((d : ℝ≥0) + 1) * ShadedBody.fullness qj (fun k => bodies (e k)) := by
    calc
      ShadedBody.fullness q (fun i => (T i).toShadedBody)
          ≤ Cnorm * ShadedBody.fullness q bodies := hfull
      _ ≤ Cnorm * (((d : ℝ≥0) + 1) * ShadedBody.fullness qj (fun k => bodies (e k))) := by
            gcongr
      _ = Cnorm * ((d : ℝ≥0) + 1) * ShadedBody.fullness qj (fun k => bodies (e k)) := by
            rw [← mul_assoc]
  have hmaxd' : maxDensity qj (fun k => (P k).toConvexSpaceBody)
      ≤ (Cnorm : ENNReal) * maxDensity q (fun i => (T i).toConvexSpaceBody) := by
    calc
      maxDensity qj (fun k => (P k).toConvexSpaceBody)
          = maxDensity sED (fun i => (Pj i).toConvexSpaceBody) := by
            simpa [qj, P, hemap] using
              (maxDensity_map qj e (fun i => (Pj i).toConvexSpaceBody)).symm
      _ ≤ maxDensity q (fun i => (Pj i).toConvexSpaceBody) :=
            maxDensity_mono (fun i => (Pj i).toConvexSpaceBody) hsq
      _ ≤ (Cnorm : ENNReal) * maxDensity q (fun i => (T i).toConvexSpaceBody) := hmaxd
  have hslab' : ∀ (φ : ℝ≥0) (hφR : φ ≤ Rslab), a' / b' ≤ φ →
      ∀ (S : Prism3D φ Rslab Rslab hφR le_rfl),
        ((Plank.inWideSlabFamily qj (fun k => (P k).toPrism3D) S).card : ℝ≥0)
          ≤ ((d : ℝ≥0) + 1) * Cslab * φ ^ (1 : ℝ) * (qj.card : ℝ≥0) := by
    intro φ hφR hratio S
    have hcard_slab_eq : (Plank.inWideSlabFamily qj (fun k => (P k).toPrism3D) S).card
        = (Plank.inWideSlabFamily sED (fun i => (Pj i).toPrism3D) S).card := by
      have h1 : (Plank.inWideSlabFamily qj (fun k => (P k).toPrism3D) S).card
          = (Plank.inWideSlabFamily (qj.map e) (fun i => (Pj i).toPrism3D) S).card := by
        rw [Plank.inWideSlabFamily_map qj e (fun i => (Pj i).toPrism3D) S]
        rw [Finset.card_map]
      simpa [qj, P, hemap] using h1
    have hcard_slab_le_q : (Plank.inWideSlabFamily qj (fun k => (P k).toPrism3D) S).card
        ≤ (Plank.inWideSlabFamily q (fun i => (Pj i).toPrism3D) S).card := by
      rw [hcard_slab_eq]
      exact Finset.card_le_card (Plank.inWideSlabFamily_mono hsq (fun i => (Pj i).toPrism3D) S)
    have hcard_slab : ((Plank.inWideSlabFamily qj (fun k => (P k).toPrism3D) S).card : ℝ≥0)
        ≤ Cslab * φ ^ (1 : ℝ) * (q.card : ℝ≥0) := by
      have hle : ((Plank.inWideSlabFamily qj (fun k => (P k).toPrism3D) S).card : ℝ≥0)
          ≤ ((Plank.inWideSlabFamily q (fun i => (Pj i).toPrism3D) S).card : ℝ≥0) := by
        exact_mod_cast hcard_slab_le_q
      exact hle.trans (hslab φ hφR hratio S)
    have hqcard : (q.card : ℝ≥0) ≤ ((d : ℝ≥0) + 1) * (qj.card : ℝ≥0) := by
      calc
        (q.card : ℝ≥0) ≤ (((d + 1) * sED.card : ℕ) : ℝ≥0) := by exact_mod_cast hcardq
        _ = ((d : ℝ≥0) + 1) * (sED.card : ℝ≥0) := by
              rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
        _ = ((d : ℝ≥0) + 1) * (qj.card : ℝ≥0) := by
              rw [hcard_univ]
    calc
      ((Plank.inWideSlabFamily qj (fun k => (P k).toPrism3D) S).card : ℝ≥0)
          ≤ Cslab * φ ^ (1 : ℝ) * (q.card : ℝ≥0) := hcard_slab
      _ ≤ Cslab * φ ^ (1 : ℝ) * (((d : ℝ≥0) + 1) * (qj.card : ℝ≥0)) := by
            gcongr
      _ = ((d : ℝ≥0) + 1) * Cslab * φ ^ (1 : ℝ) * (qj.card : ℝ≥0) := by
            ring
  have hmult : ShadedBody.multiplicity q bodies
      ≤ ((d : ENNReal) + 1) * ShadedBody.multiplicity sED bodies :=
    Kakeya.multiplicity_pigeon_transfer (E := EuclideanSpace ℝ (Fin 3)) hsq bodies hmassq'
  have hmult_map : ShadedBody.multiplicity sED bodies
      = ShadedBody.multiplicity qj (fun k => bodies (e k)) := by
    simpa [qj, hemap] using
      ShadedBody.multiplicity_map qj e bodies
  have hmult' : ShadedBody.multiplicity q bodies
      ≤ ((d : ENNReal) + 1) * ShadedBody.multiplicity qj (fun k => bodies (e k)) := by
    simpa [hmult_map] using hmult
  let source : InnerEDSource q Pj qj P :=
    ⟨e, fun k _hk ↦ hmemq k, fun k ↦ rfl⟩
  refine ⟨Fin sED.card, qj, P, source, source.mem_source, source.plank_eq,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    exact hwindow (e k) (hmemq k)
  · intro k hk l hl hkl
    exact hEDpair (Finset.mem_coe.mpr (hmem k)) (Finset.mem_coe.mpr (hmem l))
      (fun h => hkl (e.injective h))
  · simpa [hcard_univ] using hcardq
  · exact hcard_le
  · rw [hsum]
    exact hmassq
  · exact hfull_final
  · exact hmaxd'
  · exact hslab'
  · exact hmult'

end Kakeya

end

end
