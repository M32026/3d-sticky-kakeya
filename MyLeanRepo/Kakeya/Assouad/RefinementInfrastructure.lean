import MyLeanRepo.Kakeya.Assouad.Definitions

/-!
# Subshading infrastructure for the WZ2 large-slope refinement

The paper's Steps 1--3 repeatedly discard shaded points.  These lemmas record
the exact properties inherited by such subshadings.
-/

noncomputable section

open MeasureTheory Set

namespace Kakeya.Assouad

/-- Pointwise shading containment implies containment of shaded unions. -/
lemma IsSubshading.union_subset
    {delta : ℝ} {F : Kakeya.Streamlined.TubeFamily delta}
    {Z Y : Kakeya.Streamlined.TubeShading F}
    (hZY : IsSubshading Z Y) :
    Z.union ⊆ Y.union := by
  rintro p ⟨i, hp⟩
  exact ⟨i, hZY i hp⟩

/-- Restricting a set preserves an existing finite ball cover. -/
lemma CanCoverByBalls.mono
    {E' E : Set Point3} {radius : ℝ} {N : ENNReal}
    (hsub : E' ⊆ E) (hcover : CanCoverByBalls E radius N) :
    CanCoverByBalls E' radius N := by
  rcases hcover with ⟨centers, hcard, hcenters⟩
  exact ⟨centers, hcard, fun y hy => hcenters y (hsub hy)⟩

/--
Global and local grain data is inherited by a subshading, with exactly the
same slope, plane map, exponent, and AD constant.
-/
def C2GrainStructure.mono
    {delta sigma : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {Z Y : Kakeya.Streamlined.TubeShading F}
    {C : ENNReal}
    (G : C2GrainStructure Y sigma C)
    (hZY : IsSubshading Z Y) :
    C2GrainStructure Z sigma C where
  slope := G.slope
  slope_normalized := G.slope_normalized
  planeMap := G.planeMap
  planeMap_measurable := G.planeMap_measurable
  planeMapLipschitzConstant := G.planeMapLipschitzConstant
  planeMap_lipschitz := G.planeMap_lipschitz.mono hZY.union_subset
  planeMap_unit := by
    intro p hp
    exact G.planeMap_unit p (hZY.union_subset hp)
  planeMap_incidence := by
    intro i p hp
    exact G.planeMap_incidence i p (hZY i hp)
  global_slab_ad := by
    intro z hz
    apply (G.global_slab_ad z hz).mono
    rintro value ⟨p, hp, rfl⟩
    refine ⟨p, ?_, rfl⟩
    exact ⟨⟨hZY.union_subset hp.1.1, hp.1.2⟩, hp.2⟩
  local_ad := by
    intro rho hdelta_rho hrho_one p hp
    apply
      (G.local_ad rho hdelta_rho hrho_one p
        (hZY.union_subset hp)).mono
    rintro value ⟨q, hq, rfl⟩
    exact ⟨q, ⟨hZY.union_subset hq.1, hq.2⟩, rfl⟩

end Kakeya.Assouad
