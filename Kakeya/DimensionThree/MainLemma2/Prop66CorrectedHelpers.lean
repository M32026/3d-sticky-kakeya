module

public import Kakeya.DimensionThree.MainLemma2.RepresentativePlankGeometry
public import Kakeya.DimensionThree.Plank.TubeParentPacking

@[expose] public section

open MeasureTheory ConvexSpaceBody Filter ShadedBody Topology
open scoped NNReal ENNReal Real

namespace Kakeya

noncomputable section

/- Quantitative hypotheses for the factorization estimates below. -/
structure ComparableFactorizationV2 {ι : Type*} [DecidableEq ι]
    (a b : NNReal) (hab : a ≤ b) (hb1 : b ≤ 1)
    (s : Finset ι) (V : ι → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3)))
    (C₀ Cw : NNReal) extends ConvexSpaceBody.Factorization s V C₀ where
  hCw : 1 ≤ Cw
  outer_dims : ∀ part ∈ parts,
    IsPlankOfDimensions Cw a b (part.convexHull_biUnion V)

theorem ComparableFactorizationV2.part_nonempty
    {ι : Type*} [DecidableEq ι]
    {a b : NNReal} {hab : a ≤ b} {hb1 : b ≤ 1}
    {s : Finset ι} {V : ι → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    {C₀ Cw : NNReal} (F : ComparableFactorizationV2 a b hab hb1 s V C₀ Cw)
    {part : Finset ι} (hp : part ∈ F.parts) : part.Nonempty := by
  exact F.toFactorization.nonempty_of_mem_parts hp

theorem ComparableFactorizationV2.part_subset
    {ι : Type*} [DecidableEq ι]
    {a b : NNReal} {hab : a ≤ b} {hb1 : b ≤ 1}
    {s : Finset ι} {V : ι → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    {C₀ Cw : NNReal} (F : ComparableFactorizationV2 a b hab hb1 s V C₀ Cw)
    {part : Finset ι} (hp : part ∈ F.parts) : part ⊆ s := by
  exact F.toFactorization.subset hp

theorem ComparableFactorizationV2.part_hull_le
    {ι : Type*} [DecidableEq ι]
    {a b : NNReal} {hab : a ≤ b} {hb1 : b ≤ 1}
    {s : Finset ι} {V : ι → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    {C₀ Cw : NNReal} (F : ComparableFactorizationV2 a b hab hb1 s V C₀ Cw)
    {part : Finset ι} (hp : part ∈ F.parts)
    {K : ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    (hVK : ∀ i ∈ s, V i ≤ K) : part.convexHull_biUnion V ≤ K := by
  rw [(F.part_nonempty hp).convexHull_biUnion_le_iff]
  intro i hi
  exact hVK i (F.part_subset hp hi)

theorem ComparableFactorizationV2.part_hull_subset_closedBall
    {ι : Type*} [DecidableEq ι]
    {a b : NNReal} {hab : a ≤ b} {hb1 : b ≤ 1}
    {s : Finset ι} {V : ι → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    {C₀ Cw : NNReal} (F : ComparableFactorizationV2 a b hab hb1 s V C₀ Cw)
    {part : Finset ι} (hp : part ∈ F.parts)
    (hball : ∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 1) :
    (part.convexHull_biUnion V).carrier ⊆ Metric.closedBall 0 1 := by
  have hle : part.convexHull_biUnion V ≤
      ConvexSpaceBody.closedUnitBall (E := EuclideanSpace ℝ (Fin 3)) :=
    F.part_hull_le hp (fun i hi => by
      exact (SetLike.coe_subset_coe).mp (hball i hi))
  exact (SetLike.coe_subset_coe).mpr hle

/-- Exact representatives for all factor bodies.  Outside `F.parts` the value
is an irrelevant standard plank, so consumers get an ordinary total map. -/
structure ComparableFactorizationV2.RepresentativeFamily
    {ι : Type*} [DecidableEq ι]
    {a b : NNReal} {hab : a ≤ b} {hb1 : b ≤ 1}
    {s : Finset ι} {V : ι → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    {C₀ Cw : NNReal} (F : ComparableFactorizationV2 a b hab hb1 s V C₀ Cw) where
  repr : Finset ι → Plank a b hab hb1
  body_subset_dilation : ∀ part ∈ F.parts,
    (part.convexHull_biUnion V).carrier ⊆
      ((repr part).toPrismNDim.dilation Cw).carrier
  dilation_volume_le : ∀ part ∈ F.parts,
    volume (((repr part).toPrismNDim.dilation Cw).carrier : Set _) ≤
      (Prism3D.enclosureVolumeConstant Cw : ENNReal) *
        volume (part.convexHull_biUnion V).carrier
  dilation_window : ∀ part ∈ F.parts,
    ((repr part).toPrismNDim.dilation Cw).carrier ⊆
      Metric.closedBall 0 ((1 + 6 * Cw : NNReal) : ℝ)

theorem ComparableFactorizationV2.exists_representativeFamily
    {ι : Type*} [DecidableEq ι]
    {a b : NNReal} {hab : a ≤ b} {hb1 : b ≤ 1}
    {s : Finset ι} {V : ι → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    {C₀ Cw : NNReal} (F : ComparableFactorizationV2 a b hab hb1 s V C₀ Cw)
    (hball : ∀ i ∈ s, (V i).carrier ⊆ Metric.closedBall 0 1) :
    Nonempty F.RepresentativeFamily := by
  classical
  let geom : ∀ part : Finset ι, part ∈ F.parts →
      RepresentativePlankGeometry Cw a b hab hb1 (part.convexHull_biUnion V) :=
    fun part hp => Classical.choice
      (exists_representativePlankGeometry F.hCw hab hb1 (part.convexHull_biUnion V)
        (F.part_hull_subset_closedBall hp hball) (F.outer_dims part hp))
  let repr : Finset ι → Plank a b hab hb1 := fun part =>
    if hp : part ∈ F.parts then (geom part hp).plank else Classical.choice inferInstance
  let RF : F.RepresentativeFamily :=
    { repr := repr
      body_subset_dilation := by
        intro part hp
        simpa [repr, hp] using (geom part hp).body_subset_dilation
      dilation_volume_le := by
        intro part hp
        simpa [repr, hp] using (geom part hp).dilation_volume_le
      dilation_window := by
        intro part hp
        simpa [repr, hp] using (geom part hp).dilation_window }
  exact ⟨RF⟩

theorem ComparableFactorizationV2.toFactorFamily_isKatzTao
    {ι : Type*} [DecidableEq ι]
    {a b : NNReal} {hab : a ≤ b} {hb1 : b ≤ 1}
    {s : Finset ι} {V : ι → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    {C₀ Cw : NNReal} (F : ComparableFactorizationV2 a b hab hb1 s V C₀ Cw) :
    IsKatzTao F.toFactorization.toFactorFamily.outerSet
      F.toFactorization.toFactorFamily.outerBody (C₀ : ENNReal) := by
  exact F.toFactorization.toFactorFamily_isKatzTao

theorem ComparableFactorizationV2.toFactorFamily_isFrostman
    {ι : Type*} [DecidableEq ι]
    {a b : NNReal} {hab : a ≤ b} {hb1 : b ≤ 1}
    {s : Finset ι} {V : ι → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    {C₀ Cw : NNReal} (F : ComparableFactorizationV2 a b hab hb1 s V C₀ Cw) :
    ∀ t ∈ F.toFactorization.toFactorFamily.outerSet,
      IsFrostmanIn (F.toFactorization.toFactorFamily.fiber t)
        F.toFactorization.toFactorFamily.innerBody
        (F.toFactorization.toFactorFamily.outerBody t) (C₀ : ENNReal) := by
  exact F.toFactorization.toFactorFamily_isFrostman

theorem ComparableFactorizationV2.part_frostman
    {ι : Type*} [DecidableEq ι]
    {a b : NNReal} {hab : a ≤ b} {hb1 : b ≤ 1}
    {s : Finset ι} {V : ι → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    {C₀ Cw : NNReal} (F : ComparableFactorizationV2 a b hab hb1 s V C₀ Cw)
    {part : Finset ι} (hp : part ∈ F.parts) :
    IsFrostmanIn part V (part.convexHull_biUnion V) (C₀ : ENNReal) := by
  exact F.toFactorization.isFrostman part hp

theorem ComparableFactorizationV2.parts_katzTao
    {ι : Type*} [DecidableEq ι]
    {a b : NNReal} {hab : a ≤ b} {hb1 : b ≤ 1}
    {s : Finset ι} {V : ι → ConvexSpaceBody (EuclideanSpace ℝ (Fin 3))}
    {C₀ Cw : NNReal} (F : ComparableFactorizationV2 a b hab hb1 s V C₀ Cw) :
    IsKatzTao F.parts (fun part => part.convexHull_biUnion V) (C₀ : ENNReal) := by
  exact F.toFactorization.isKatzTao

end

end Kakeya
