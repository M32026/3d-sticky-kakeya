/-
Copyright (c) 2026 Project Numina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Numina Team
-/

module

public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFixedTowerStopping
public import Kakeya.DimensionThree.MainLemma2.Reduction.SpineFloorTwoScale

/-!
# H1 and H2 of `dividingScalesLemma` (B), on the fixed tower

The two array estimates the abstract stopping lemma needs, read on `towerDensityArray`
(`Z(k,l) = max_{S ∈ 𝕋_k} Δ_max(𝕋_l⟨S⟩)`, `SpineFixedTowerStopping.lean`).  Source l.2735-2739:

> *"The same two-scale inequality gives submultiplicativity for `X̃` with constant `300⁹C₂`; the
> assumed cardinality estimate gives the crude exponent `d = 4`, and the top-cell estimate gives
> the entry bound after transposition."*

The transposition `X̃(k,l) = Z(M-l, M-k)` turns the source's `X̃(k,m) ≤ B X̃(k,l) X̃(l,m)`
(`k < l < m`) into

  **H1**  `Z(a,c) ≤ B · Z(a,p) · Z(p,c)`   for `a ≤ p ≤ c`,

which is the form proved here.  The entry bound (H3) is already existing as
`towerGood_entry_of_topCell`.

## H1: the constant is `C₀(E)² · Cu`, not `300⁹C₂` — stated, not fitted

The source's `300⁹C₂` is *its* geometric constant: `300⁹` from its two-scale maximal-density
inequality and `C₂` from its geometric-competitor hypothesis.  The tree's rendering of the same
inequality is `Kakeya.ML2Core.twoScaleConst_spec` (GWZ Lemma 7.4 at `M = 2`, via
`MultiScaleSubmult.maxDensity_le_two_fibreDeltaMax`), whose constant is `C₀(E)²`, and the tree pays
the competitor factor as the hierarchy's own uniformity constant `Cu` through
`maxDensity_ancestors_le_mul_sup` — the containment-versus-assignment step, in which a
level-`p` ancestor of a cell inside `T_a` need not itself lie inside `T_a`.  So

  `B = C₀(E)² · Cu`,

with `C₀(E)` depending only on `E` and `Cu` the tower's uniformity constant.  **Both are `δ`-free**
, so `B^{N+1}` is a `δ`-free constant exactly as the source's `B_K^{N+1}`
is, and no `δ`-exponent account moves.  The correspondence with the source's constant is
`C₀(E)² ↔ 300⁹` and `Cu ↔ C₂`; neither is claimed to be numerically the source's.

## H1's side condition: the factor-`4` gap

`4 ρ_c ≤ ρ_p` is a tree-side condition of GWZ Lemma 7.4 that the source's lemma does not carry
(`MultiScaleSubmult.lean`'s module header: the neighbourhood step of the volume telescope forces
it, and `antitone_not_imp_four_gap` is the witness that it is strictly stronger than
`ρ_c ≤ ρ_p`).  It is carried as a binder here rather than discharged, exactly as
`exists_twoScale_nodesUnder` carries it.

## H2 is the source's own hypothesis, transported

The source *assumes* `#𝕋_l⟨S⟩ ≤ D(ρ_k/ρ_l)^4` (l.2679-2681) and reads the crude exponent off it.
`towerDensityArray_le_of_card_le` is the transport (`Δ_max ≤ #`), and
`towerDensityArray_le_crude_exponent_four` is the named `d = 4` instance.  Nothing is fitted: the
cardinality estimate is a hypothesis here as it is there.

## Family / shading / level pair

| declaration | family / shading | level pair |
|---|---|---|
| `assignFibre_subset_nodesUnder` | the tower's `s`, `T`; no shading | `(p,c)` |
| `towerDensityArray_submultiplicative` | as above | the triple `(a,p,c)`, `a ≤ p ≤ c` |
| `towerDensityArray_le_of_card_le` | as above | `(k,l)` |
| `towerDensityArray_le_crude_exponent_four` | as above | `(k,l)` |

No shading enters: the array is a maximal density of tubes.

## A1-a

Nothing here mentions `MultiScaleFac.GridUniformCore`, and nothing here is an (F)-branch interface
statement: `towerDensityArray` is the source's `Z`, on the nested/class model, and every family
named is `Tube.UniformTubeSet.nodesUnder` or a `coverClass` image.
-/

@[expose] public section

open scoped NNReal ENNReal
open MeasureTheory Tube

namespace Kakeya.ML2Core

section TowerArrayEstimates

universe u

variable {ι : Type u} {δ Cu : NNReal} {s : Finset ι}
  {T : ι → Tube δ (EuclideanSpace ℝ (Fin 3))}

open scoped Classical in
/-- **The assignment fibre of a node sits inside its containment family.**  A member of the class of
the level-`p` node `jp` has its level-`c` node inside `jp`'s tube, by
`Tube.ChainCoverSystem.tube_assign_le`.  This is the step that turns the *assignment* reading of
the second factor of `twoScaleConst_spec` into the *containment* reading `towerDensityArray` is
written over — the reading gap  asks to be stated rather than glossed.

**Duplicate of record.**  `Tube.UniformTubeSet.assignFibre_subset_nodesUnder`
(`SpineCountFloor.lean:75`) is the same inclusion, spelled on the named
`Tube.UniformTubeSet.assignFibre`.  This one is spelled on the `coverClass`-image form because that
is literally what `twoScaleConst_spec`'s second factor produces; the two are definitionally the
same set and either may be used. -/
theorem assignFibre_subset_nodesUnder (𝒰 : Tube.UniformTubeSet s T (ssfGridLen δ) Cu)
    {p c : ℕ} (hpc : p ≤ c) (hc : c ≤ ssfGridLen δ) {jp : ι} :
    (coverClass s (𝒰.cover.assign p) jp).image (𝒰.cover.assign c) ⊆ 𝒰.nodesUnder c p jp := by
  classical
  intro j' hj'
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj'
  simp only [coverClass, Finset.mem_filter] at hi
  rw [Tube.UniformTubeSet.nodesUnder_eq_nodesIn, Tube.UniformTubeSet.mem_nodesIn_iff]
  refine ⟨𝒰.cover.assign_mem c hc i hi.1, ?_⟩
  have h : (𝒰.cover.tube c (𝒰.cover.assign c i)).toConvexSpaceBody
      ≤ (𝒰.cover.tube p (𝒰.cover.assign p i)).toConvexSpaceBody :=
    𝒰.cover.toChain.tube_assign_le hpc hc hi.1
  rwa [hi.2] at h

/-- **H1: submultiplicativity of the density array** (source l.2735-2737, transposed).

`Z(a,c) ≤ C₀(E)² · Cu · Z(a,p) · Z(p,c)` for `a ≤ p ≤ c`.  The two factors on the right are the
two factors of `twoScaleConst_spec`, each read back onto `towerDensityArray`: the ancestor factor
through `maxDensity_ancestors_le_mul_sup` (which is where the `Cu` is paid), the fibre factor
through `assignFibre_subset_nodesUnder`.

**Family/shading:** the tower's `s`, `T`; no shading.  **Level pair:** the triple `(a,p,c)`. -/
theorem towerDensityArray_submultiplicative (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (𝒰 : Tube.UniformTubeSet s T (ssfGridLen δ) Cu) (hs : s.Nonempty)
    (hball : ∀ i ∈ s, (T i).carrier ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)
    {a p c : ℕ} (hap : a ≤ p) (hpc : p ≤ c) (hc : c ≤ ssfGridLen δ)
    (hgap : 4 * gridScale δ (ssfGridLen δ) c ≤ gridScale δ (ssfGridLen δ) p) :
    towerDensityArray 𝒰 a c
      ≤ ENNReal.ofReal (twoScaleConst.{u, 0} (EuclideanSpace ℝ (Fin 3))) ^ 2 * (Cu : ENNReal)
          * towerDensityArray 𝒰 a p * towerDensityArray 𝒰 p c := by
  classical
  have hp : p ≤ ssfGridLen δ := hpc.trans hc
  refine Finset.sup_le fun j _ => ?_
  have hmain := twoScaleConst_spec.{u, 0} hδ0 hδ1 𝒰 hs hball (a := a) hpc hc hgap j
  refine hmain.trans ?_
  have hanc := maxDensity_ancestors_le_mul_sup 𝒰 hs hap hpc hc j
  have hfib : ((𝒰.nodesUnder c a j).image
        (ML2Reduction.coarseNode 𝒰.cover.toChain p c)).sup
        (fun jp => Kakeya.maxDensity
          ((coverClass s (𝒰.cover.assign p) jp).image (𝒰.cover.assign c))
          (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody))
      ≤ towerDensityArray 𝒰 p c := by
    refine Finset.sup_le fun jp hjp => ?_
    have hjpidx : jp ∈ 𝒰.cover.indexSet p := by
      obtain ⟨jc, hjc, rfl⟩ := Finset.mem_image.mp hjp
      have hjcidx : jc ∈ 𝒰.cover.indexSet c := (Finset.mem_filter.mp hjc).1
      exact ML2Reduction.coarseNode_mem 𝒰.cover.toChain hp
        (Finset.mem_filter.mpr ⟨hjcidx,
          Kakeya.MultiScaleFac.coverClass_nonempty_of_mem_parent 𝒰 hc hs hjcidx⟩)
    refine le_trans (Kakeya.maxDensity_mono
      (fun j'' => (𝒰.cover.tube c j'').toConvexSpaceBody)
      (assignFibre_subset_nodesUnder 𝒰 hpc hc)) ?_
    exact Finset.le_sup (f := fun j' => Kakeya.maxDensity (𝒰.nodesUnder c p j')
      (fun j'' => (𝒰.cover.tube c j'').toConvexSpaceBody)) hjpidx
  calc ENNReal.ofReal (twoScaleConst.{u, 0} (EuclideanSpace ℝ (Fin 3))) ^ 2
          * Kakeya.maxDensity ((𝒰.nodesUnder c a j).image
              (ML2Reduction.coarseNode 𝒰.cover.toChain p c))
              (fun jp => (𝒰.cover.tube p jp).toConvexSpaceBody)
          * ((𝒰.nodesUnder c a j).image
              (ML2Reduction.coarseNode 𝒰.cover.toChain p c)).sup
              (fun jp => Kakeya.maxDensity
                ((coverClass s (𝒰.cover.assign p) jp).image (𝒰.cover.assign c))
                (fun j' => (𝒰.cover.tube c j').toConvexSpaceBody))
      ≤ ENNReal.ofReal (twoScaleConst.{u, 0} (EuclideanSpace ℝ (Fin 3))) ^ 2
          * ((Cu : ENNReal) * towerDensityArray 𝒰 a p) * towerDensityArray 𝒰 p c :=
        mul_le_mul' (mul_le_mul' le_rfl hanc) hfib
    _ = ENNReal.ofReal (twoScaleConst.{u, 0} (EuclideanSpace ℝ (Fin 3))) ^ 2 * (Cu : ENNReal)
          * towerDensityArray 𝒰 a p * towerDensityArray 𝒰 p c := by ring

/-- **The array is bounded by any uniform bound on the containment counts.**  `Δ_max ≤ #`
(`Kakeya.maxDensity_le_card`), taken to the supremum. -/
theorem towerDensityArray_le_of_card_le (𝒰 : Tube.UniformTubeSet s T (ssfGridLen δ) Cu)
    {k l : ℕ} {B : ENNReal}
    (hcard : ∀ j ∈ 𝒰.cover.indexSet k, ((𝒰.nodesUnder l k j).card : ENNReal) ≤ B) :
    towerDensityArray 𝒰 k l ≤ B :=
  Finset.sup_le fun j hj => (Kakeya.maxDensity_le_card _ _).trans (hcard j hj)

/-- **H2: the crude exponent `d = 4`** (source l.2679-2681 and l.2737).  The source *assumes* the
cardinality estimate `#𝕋_l⟨S⟩ ≤ D (ρ_k/ρ_l)^4` and reads the crude exponent off it; this is that
reading, with the estimate a hypothesis here as it is there.  Nothing is fitted — in particular
the exponent `4` is the source's own and is not chosen to make anything close. -/
theorem towerDensityArray_le_crude_exponent_four
    (𝒰 : Tube.UniformTubeSet s T (ssfGridLen δ) Cu) {k l : ℕ} {D : ENNReal}
    (hcard : ∀ j ∈ 𝒰.cover.indexSet k, ((𝒰.nodesUnder l k j).card : ENNReal)
      ≤ D * ENNReal.ofReal
          (((gridScale δ (ssfGridLen δ) k : ℝ) / (gridScale δ (ssfGridLen δ) l : ℝ)) ^ (4 : ℕ))) :
    towerDensityArray 𝒰 k l
      ≤ D * ENNReal.ofReal
          (((gridScale δ (ssfGridLen δ) k : ℝ) / (gridScale δ (ssfGridLen δ) l : ℝ)) ^ (4 : ℕ)) :=
  towerDensityArray_le_of_card_le 𝒰 hcard

end TowerArrayEstimates

end Kakeya.ML2Core

end
