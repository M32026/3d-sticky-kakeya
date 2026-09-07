import MyLeanRepo.Kakeya.Assouad.WZ1.RootRelativeFineParentCellPullback
import MyLeanRepo.Kakeya.Assouad.WZ1.RootRelativeDirectionBound
import MyLeanRepo.Kakeya.Assouad.RefinementInfrastructure

/-!
# Root-relative fine projection pullback

The whole-cell fine pullback does not put a retained fine point literally in
the selected coarse Property-Three shading.  It supplies a Property-Three
witness in the same root spatial cell.  This module records the exact
consequences:

* the witness is within `2 * rho` of the retained fine point;
* a fine local projection lies in an explicit one-dimensional thickening of
  a Property-Three projection over the enlarged ball `tau + 4 * rho`.

The enlarged ball and projection thickening are retained in the conclusion.
No final Lemma 17 covering inequality is assumed here.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric

/--
Every retained fine point has a Property-Three witness for its own parent in
the same root spatial cell and at distance at most `2 * rho`.
-/
lemma wz1_root_relative_fine_near_propertyThree
    {delta sigma epsilon₁ epsilon₂ : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    {scaleCount depth : ℕ}
    {schedule : Fin scaleCount →
      Kakeya.Streamlined.AdmissibleScale delta}
    (cover : WZ1RootRelativeBalancedCoverData
      (sigma := sigma) (epsilon := epsilon₁)
      U Y schedule depth)
    (coordinate : Fin scaleCount)
    (propertyThree : Kakeya.Streamlined.TubeShading
      (U.coarse (schedule coordinate)))
    (hpropertyThree : IsSubshading propertyThree
      (cover.atScale coordinate).coarseShading)
    (fine : WZ1Lemma17FineParentCellPullbackData
      (epsilon₂ := epsilon₂)
      (cover.toBalancedCoverData coordinate) propertyThree) :
    ∀ i p, p ∈ fine.fineShading.carrier i →
      ∃ q,
        q ∈ propertyThree.carrier
          ((U.cover (schedule coordinate)).parent i) ∧
        (cover.atScale coordinate).cell q =
          (cover.atScale coordinate).cell p ∧
        dist p q ≤ 2 * (schedule coordinate).1 := by
  intro i p hp
  rcases fine.fine_supported_on_propertyThree_cell i p hp with
    ⟨q, hq, hcell⟩
  have hpRefined : p ∈ cover.refined.carrier i :=
    fine.fine_subshading i hp
  have hpCoarse :
      p ∈ (cover.atScale coordinate).coarseShading.carrier
        ((U.cover (schedule coordinate)).parent i) :=
    (cover.atScale coordinate).point_compatibility i p hpRefined
  have hqCoarse :
      q ∈ (cover.atScale coordinate).coarseShading.carrier
        ((U.cover (schedule coordinate)).parent i) :=
    hpropertyThree _ hq
  have hcell' :
      (cover.atScale coordinate).cell q =
        (cover.atScale coordinate).cell p := by
    simpa [WZ1RootRelativeBalancedCoverData.toBalancedCoverData] using hcell
  exact
    ⟨q, hq, hcell',
      (cover.atScale coordinate).cell_diameter p
        ⟨_, hpCoarse⟩ q ⟨_, hqCoarse⟩ hcell'.symm⟩

/--
Pull every value in a local scalar projection of the retained fine shading
back to an actual Property-Three projection value.

The explicit source-value witness is stronger than closed-thickening
membership and can therefore be fed directly into a slab-volume lower bound
without any closedness assumption on the Property-Three projection.
-/
lemma wz1_root_relative_fine_projection_pullback_witness
    {delta sigma epsilon₁ epsilon₂ : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    {scaleCount depth : ℕ}
    {schedule : Fin scaleCount →
      Kakeya.Streamlined.AdmissibleScale delta}
    (cover : WZ1RootRelativeBalancedCoverData
      (sigma := sigma) (epsilon := epsilon₁)
      U Y schedule depth)
    (coordinate : Fin scaleCount)
    (propertyThree : Kakeya.Streamlined.TubeShading
      (U.coarse (schedule coordinate)))
    (hpropertyThree : IsSubshading propertyThree
      (cover.atScale coordinate).coarseShading)
    (fine : WZ1Lemma17FineParentCellPullbackData
      (epsilon₂ := epsilon₂)
      (cover.toBalancedCoverData coordinate) propertyThree)
    (plane : WZ1PlaneMapData Y)
    (tau : ℝ) :
    ∀ p ∈ fine.fineShading.union,
      ∃ q ∈ propertyThree.union,
        (cover.atScale coordinate).cell q =
            (cover.atScale coordinate).cell p ∧
        ∀ value ∈
            scalarProjection (plane.planeMap p)
              (fine.fineShading.union ∩ closedBall p tau),
          ∃ sourceValue ∈
              scalarProjection
                (plane.planeMap
                  ((cover.atScale coordinate).representative
                    ((cover.atScale coordinate).cell q)))
                (propertyThree.union ∩
                  closedBall q
                    (tau + 4 * (schedule coordinate).1)),
            dist value sourceValue ≤
              4 * max 1 (plane.lipschitzConstant : ℝ) *
                (schedule coordinate).1 := by
  intro p hp
  rcases hp with ⟨i, hpi⟩
  rcases wz1_root_relative_fine_near_propertyThree
      cover coordinate propertyThree hpropertyThree fine i p hpi with
    ⟨q, hq, hcell, hpq⟩
  have hqUnion : q ∈ propertyThree.union := ⟨_, hq⟩
  have hqCoarse :
      q ∈ (cover.atScale coordinate).coarseShading.union :=
    hpropertyThree.union_subset hqUnion
  have hpRefined : p ∈ cover.refined.union :=
    fine.fine_subshading.union_subset ⟨i, hpi⟩
  have hpY : p ∈ Y.union := cover.subshading.union_subset hpRefined
  let representative :=
    (cover.atScale coordinate).representative
      ((cover.atScale coordinate).cell q)
  have hrepresentativeRefined : representative ∈ cover.refined.union :=
    ((cover.atScale coordinate).cell_fine_witness q hqCoarse).1
  have hrepresentativeY : representative ∈ Y.union :=
    cover.subshading.union_subset hrepresentativeRefined
  have hrepresentativeCoarse :
      representative ∈
        (cover.atScale coordinate).coarseShading.union :=
    root_refined_union_subset_coarse
      (cover.atScale coordinate) hrepresentativeRefined
  have hrepresentativeCell :
      (cover.atScale coordinate).cell representative =
        (cover.atScale coordinate).cell q :=
    ((cover.atScale coordinate).cell_fine_witness q hqCoarse).2
  have hpCoarse :
      p ∈ (cover.atScale coordinate).coarseShading.union :=
    root_refined_union_subset_coarse
      (cover.atScale coordinate) hpRefined
  have hpRepresentative :
      dist p representative ≤ 2 * (schedule coordinate).1 := by
    exact
      (cover.atScale coordinate).cell_diameter p hpCoarse
        representative hrepresentativeCoarse
        (hcell.symm.trans hrepresentativeCell.symm)
  refine ⟨q, hqUnion, hcell, ?_⟩
  intro value hvalue
  rcases hvalue with ⟨x, hx, rfl⟩
  rcases hx.1 with ⟨j, hxj⟩
  rcases wz1_root_relative_fine_near_propertyThree
      cover coordinate propertyThree hpropertyThree fine j x hxj with
    ⟨qx, hqx, _hcellx, hxqx⟩
  have hqxUnion : qx ∈ propertyThree.union := ⟨_, hqx⟩
  have hqxBall :
      qx ∈ closedBall q
        (tau + 4 * (schedule coordinate).1) := by
    change dist qx q ≤ tau + 4 * (schedule coordinate).1
    calc
      dist qx q ≤ dist qx x + dist x p + dist p q := by
        calc
          dist qx q ≤ dist qx p + dist p q := dist_triangle _ _ _
          _ ≤ dist qx x + dist x p + dist p q := by
            have htriangle : dist qx p ≤ dist qx x + dist x p :=
              dist_triangle _ _ _
            linarith
      _ ≤ 2 * (schedule coordinate).1 + tau +
          2 * (schedule coordinate).1 := by
        have hxqxsym : dist qx x ≤ 2 * (schedule coordinate).1 := by
          simpa [dist_comm] using hxqx
        have hxBall : dist x p ≤ tau := hx.2
        linarith [hxqxsym, hxBall, hpq]
      _ = tau + 4 * (schedule coordinate).1 := by ring
  let normal := plane.planeMap representative
  have hnormalUnit : ‖normal‖ = 1 :=
    plane.unit representative hrepresentativeY
  have hplaneVariation :
      dist (plane.planeMap p) normal ≤
        (plane.lipschitzConstant : ℝ) * dist p representative := by
    exact
      (lipschitzOnWith_iff_dist_le_mul.mp plane.lipschitz)
        p hpY representative hrepresentativeY
  have hxRefined : x ∈ cover.refined.union :=
    fine.fine_subshading.union_subset ⟨j, hxj⟩
  have hxWindow : x ∈ closedBall (0 : Point3) 1 :=
    cover.refined_extremal.2.2.2.1 hxRefined
  have hxNorm : ‖x‖ ≤ 1 := by
    simpa [dist_eq_norm] using hxWindow
  have hLNonneg : 0 ≤ (plane.lipschitzConstant : ℝ) := by positivity
  have hrhoPos : 0 < (schedule coordinate).1 :=
    (cover.atScale coordinate).coarse_extremal.1
  have hprojectionDistance :
      dist (inner ℝ x (plane.planeMap p)) (inner ℝ qx normal) ≤
        4 * max 1 (plane.lipschitzConstant : ℝ) *
          (schedule coordinate).1 := by
    have hfirst :
        |inner ℝ x (plane.planeMap p - normal)| ≤
          2 * (plane.lipschitzConstant : ℝ) *
            (schedule coordinate).1 := by
      calc
        |inner ℝ x (plane.planeMap p - normal)| ≤
            ‖x‖ * ‖plane.planeMap p - normal‖ :=
          abs_real_inner_le_norm _ _
        _ = ‖x‖ * dist (plane.planeMap p) normal := by
          rw [dist_eq_norm]
        _ ≤ 1 *
            ((plane.lipschitzConstant : ℝ) *
              (2 * (schedule coordinate).1)) := by
          apply mul_le_mul hxNorm
          · exact hplaneVariation.trans (by gcongr)
          · positivity
          · norm_num
        _ = 2 * (plane.lipschitzConstant : ℝ) *
            (schedule coordinate).1 := by ring
    have hsecond :
        |inner ℝ (x - qx) normal| ≤
          2 * (schedule coordinate).1 := by
      calc
        |inner ℝ (x - qx) normal| ≤ ‖x - qx‖ * ‖normal‖ :=
          abs_real_inner_le_norm _ _
        _ = dist x qx := by
          rw [dist_eq_norm, hnormalUnit]
          ring
        _ ≤ 2 * (schedule coordinate).1 := hxqx
    rw [Real.dist_eq]
    have hidentity :
        inner ℝ x (plane.planeMap p) - inner ℝ qx normal =
          inner ℝ x (plane.planeMap p - normal) +
            inner ℝ (x - qx) normal := by
      rw [inner_sub_right, inner_sub_left]
      ring
    rw [hidentity]
    calc
      |inner ℝ x (plane.planeMap p - normal) +
          inner ℝ (x - qx) normal| ≤
        |inner ℝ x (plane.planeMap p - normal)| +
          |inner ℝ (x - qx) normal| := abs_add_le _ _
      _ ≤ 2 * (plane.lipschitzConstant : ℝ) *
            (schedule coordinate).1 +
          2 * (schedule coordinate).1 := add_le_add hfirst hsecond
      _ ≤ 4 * max 1 (plane.lipschitzConstant : ℝ) *
          (schedule coordinate).1 := by
        have hone : (1 : ℝ) ≤ max 1 (plane.lipschitzConstant : ℝ) :=
          le_max_left _ _
        have hL : (plane.lipschitzConstant : ℝ) ≤
            max 1 (plane.lipschitzConstant : ℝ) := le_max_right _ _
        nlinarith
  exact
    ⟨inner ℝ qx normal,
      ⟨qx, ⟨hqxUnion, hqxBall⟩, rfl⟩,
      by simpa [normal, representative] using hprojectionDistance⟩

/--
Closed-thickening form of
`wz1_root_relative_fine_projection_pullback_witness`.
-/
lemma wz1_root_relative_fine_projection_pullback
    {delta sigma epsilon₁ epsilon₂ : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    {scaleCount depth : ℕ}
    {schedule : Fin scaleCount →
      Kakeya.Streamlined.AdmissibleScale delta}
    (cover : WZ1RootRelativeBalancedCoverData
      (sigma := sigma) (epsilon := epsilon₁)
      U Y schedule depth)
    (coordinate : Fin scaleCount)
    (propertyThree : Kakeya.Streamlined.TubeShading
      (U.coarse (schedule coordinate)))
    (hpropertyThree : IsSubshading propertyThree
      (cover.atScale coordinate).coarseShading)
    (fine : WZ1Lemma17FineParentCellPullbackData
      (epsilon₂ := epsilon₂)
      (cover.toBalancedCoverData coordinate) propertyThree)
    (plane : WZ1PlaneMapData Y)
    (tau : ℝ) :
    ∀ p ∈ fine.fineShading.union,
      ∃ q ∈ propertyThree.union,
        (cover.atScale coordinate).cell q =
            (cover.atScale coordinate).cell p ∧
        scalarProjection (plane.planeMap p)
            (fine.fineShading.union ∩ closedBall p tau) ⊆
          cthickening
            (4 * max 1 (plane.lipschitzConstant : ℝ) *
              (schedule coordinate).1)
            (scalarProjection
              (plane.planeMap
                ((cover.atScale coordinate).representative
                  ((cover.atScale coordinate).cell q)))
              (propertyThree.union ∩
                closedBall q
                  (tau + 4 * (schedule coordinate).1))) := by
  intro p hp
  rcases
      wz1_root_relative_fine_projection_pullback_witness
        cover coordinate propertyThree hpropertyThree
          fine plane tau p hp with
    ⟨q, hq, hcell, hvalues⟩
  refine ⟨q, hq, hcell, ?_⟩
  intro value hvalue
  rcases hvalues value hvalue with
    ⟨sourceValue, hsourceValue, hdistance⟩
  exact
    Metric.mem_cthickening_of_dist_le
      value sourceValue
      (4 * max 1 (plane.lipschitzConstant : ℝ) *
        (schedule coordinate).1)
      _ hsourceValue hdistance

end Kakeya.Assouad
