import MyLeanRepo.Kakeya.Assouad.PropStickyFiniteParentRegularization

/-!
# Convex-Wolff transfer to a cardinality-retaining subfamily

An arbitrary subfamily does not inherit the same normalized Convex-Wolff
constant.  If the ambient-to-selected cardinality ratio is explicitly
bounded by `K`, then the selected family inherits the bound with constant
`K * C`.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

theorem wz1PaperBodyFamily_containedCount_subfamily
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (selected : Kakeya.Streamlined.TubeSubfamily family)
    (region : Set Point3) :
    (wz1PaperBodyFamily selected.family).containedCount region ≤
      (wz1PaperBodyFamily family).containedCount region := by
  classical
  let sourceIndices : Finset (Fin selected.family.card) :=
    Finset.univ.filter fun index =>
      wz1PaperTubeCarrier (selected.family.tube index) ⊆ region
  let targetIndices : Finset (Fin family.card) :=
    Finset.univ.filter fun index =>
      wz1PaperTubeCarrier (family.tube index) ⊆ region
  have hmap :
      sourceIndices.map selected.embedding ⊆ targetIndices := by
    intro ambient hambient
    rcases Finset.mem_map.mp hambient with
      ⟨source, hsourceMem, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [← selected.tube_eq source]
    exact (Finset.mem_filter.mp hsourceMem).2
  change
    (sourceIndices.card : ENNReal) ≤
      (targetIndices.card : ENNReal)
  rw [← Finset.card_map]
  exact_mod_cast Finset.card_le_card hmap

theorem WZ2PaperConvexWolffBound.subfamily_of_cardinality
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {C K : ENNReal}
    (hCWA : WZ2PaperConvexWolffBound family C)
    (selected : Kakeya.Streamlined.TubeSubfamily family)
    (hcardinality :
      family.enncard ≤ K * selected.family.enncard) :
    WZ2PaperConvexWolffBound selected.family (K * C) := by
  intro convexSet hconvex
  calc
    (wz1PaperBodyFamily selected.family).containedCount convexSet
        ≤ (wz1PaperBodyFamily family).containedCount convexSet :=
      wz1PaperBodyFamily_containedCount_subfamily selected convexSet
    _ ≤ C * volume convexSet * family.enncard :=
      hCWA convexSet hconvex
    _ ≤ C * volume convexSet *
          (K * selected.family.enncard) := by
      gcongr
    _ = (K * C) * volume convexSet *
          selected.family.enncard := by
      ring

theorem WZ2PaperConvexWolffBound.subfamily_of_weighted_cardinality
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {C weight K : ENNReal}
    (hCWA : WZ2PaperConvexWolffBound family C)
    (selected : Kakeya.Streamlined.TubeSubfamily family)
    (hweightZero : weight ≠ 0)
    (hweightTop : weight ≠ ⊤)
    (hcardinality :
      weight * family.enncard ≤
        K * selected.family.enncard) :
    WZ2PaperConvexWolffBound selected.family
      ((weight⁻¹ * K) * C) := by
  apply hCWA.subfamily_of_cardinality selected
  calc
    family.enncard =
        weight⁻¹ * (weight * family.enncard) := by
      rw [← mul_assoc,
        ENNReal.inv_mul_cancel hweightZero hweightTop,
        one_mul]
    _ ≤ weight⁻¹ *
        (K * selected.family.enncard) := by
      gcongr
    _ = (weight⁻¹ * K) *
        selected.family.enncard := by
      ring

end Kakeya.Assouad

end
