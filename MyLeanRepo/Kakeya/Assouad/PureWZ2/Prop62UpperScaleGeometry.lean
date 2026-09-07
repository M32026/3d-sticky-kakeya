import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62UpperScaleCover
import MyLeanRepo.Kakeya.Assouad.PureWZ2.DirectCallerScaleNet

/-!
# Proposition 6.2 metric parents: upper ancestor geometry

At an old scale `r ≥ rho`, replace every old ancestor by the centered
radius-`19r` tube on the same affine line.  This contains every assigned
centered metric parent.  The centered-doubled conflict graph has an absolute
degree bound by packing the original essentially-distinct `r`-ancestors.
-/

noncomputable section

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

def pureWZ2Prop62UpperConflictDegree : ℕ :=
  145921 ^ 5

structure PureWZ2Prop62UpperScaleGeometryInput
    {rho upper : ℝ}
    (children : Kakeya.Streamlined.TubeFamily rho)
    (oldParents : Kakeya.Streamlined.TubeFamily upper) where
  rho_pos : 0 < rho
  upper_pos : 0 < upper
  rho_le_upper : rho ≤ upper
  children_line_class : WZ1PaperIsLineClass children
  children_centered :
    ∀ child,
      wz2PaperCenteredLineTube (targetScale := rho)
          (children.tube child) =
        children.tube child
  old_line_class : WZ1PaperIsLineClass oldParents
  old_essentially_distinct :
    WZ1PaperIsEssentiallyDistinct oldParents
  ancestor : Fin children.card → Fin oldParents.card
  ancestor_surjective : Function.Surjective ancestor
  ancestor_close :
    ∀ child,
      wz1PaperLineDistance
          (children.tube child)
          (oldParents.tube (ancestor child)) ≤
        upper

namespace PureWZ2Prop62UpperScaleGeometryInput

variable
    {rho upper : ℝ}
    {children : Kakeya.Streamlined.TubeFamily rho}
    {oldParents : Kakeya.Streamlined.TubeFamily upper}
    (geometry :
      PureWZ2Prop62UpperScaleGeometryInput children oldParents)

noncomputable def modifiedParents
    (geometry :
      PureWZ2Prop62UpperScaleGeometryInput children oldParents) :
    Kakeya.Streamlined.TubeFamily (19 * upper) where
  card := oldParents.card
  tube parent :=
    wz2PaperCenteredLineTube
      (targetScale := 19 * upper)
      (oldParents.tube parent)

theorem modifiedParents_line_class :
    WZ1PaperIsLineClass geometry.modifiedParents := by
  intro parent
  exact
    wz2PaperCenteredLineTube_lineClass
      (geometry.old_line_class parent)

theorem modifiedParents_midpoint_local
    (parent : Fin geometry.modifiedParents.card) :
    ‖wz2PaperTubeMidpoint
      (geometry.modifiedParents.tube parent)‖ ≤ 1 := by
  exact
    wz2PaperCenteredLineTube_midpoint_norm_le_one
      (geometry.old_line_class parent)

theorem owner_containment
    (child : Fin children.card) :
    (children.tube child).carrier ⊆
      (geometry.modifiedParents.tube
        (geometry.ancestor child)).carrier := by
  let center : Kakeya.DeltaTube rho :=
    wz2PaperRelabelTube (targetScale := rho)
      (oldParents.tube (geometry.ancestor child))
  rw [← geometry.children_centered child]
  change
    (wz2PaperCenteredLineTube
        (targetScale := rho) (children.tube child)).carrier ⊆
      (wz2PaperCenteredLineTube
        (targetScale := 19 * upper)
        center).carrier
  exact
    wz2Paper_centered_carrier_subset_of_lineDistance
      geometry.rho_pos geometry.upper_pos geometry.rho_le_upper
      (geometry.children_line_class child)
      (wz2PaperRelabelTube_lineClass
        (geometry.old_line_class (geometry.ancestor child)))
      (by
        dsimp only [center]
        rw [wz2PaperRelabelTube_lineDistance_right]
        exact geometry.ancestor_close child)

theorem modifiedParents_lineDistance
    (first second : Fin geometry.modifiedParents.card) :
    wz1PaperLineDistance
        (geometry.modifiedParents.tube first)
        (geometry.modifiedParents.tube second) =
      wz1PaperLineDistance
        (oldParents.tube first)
        (oldParents.tube second) := by
  exact
    wz1PaperLineDistance_centeredLineTube_both
      (geometry.old_line_class first)
      (geometry.old_line_class second)

theorem conflict_lineDistance_le
    {first second : Fin geometry.modifiedParents.card}
    (overlap :
      (wz2PaperOrdinaryDilatedFiberIndices
          2 children geometry.modifiedParents first ∩
        wz2PaperOrdinaryDilatedFiberIndices
          2 children geometry.modifiedParents second).Nonempty) :
    wz1PaperLineDistance
        (oldParents.tube second)
        (oldParents.tube first) ≤
      2280 * upper := by
  rcases overlap with ⟨child, hchild⟩
  rcases Finset.mem_inter.mp hchild with
    ⟨hfirst, hsecond⟩
  rw [mem_wz2PaperOrdinaryDilatedFiberIndices_iff] at hfirst hsecond
  have firstDistance :=
    wz2_paper_bounded_centered_doubled_containment_lineDistance_le
      geometry.rho_pos
      (mul_pos (by norm_num) geometry.upper_pos)
      (geometry.children_line_class child)
      (geometry.modifiedParents_line_class first)
      1
      (by
        rw [← geometry.children_centered child]
        exact
          wz2PaperCenteredLineTube_midpoint_norm_le_one
            (geometry.children_line_class child))
      hfirst
  have secondDistance :=
    wz2_paper_bounded_centered_doubled_containment_lineDistance_le
      geometry.rho_pos
      (mul_pos (by norm_num) geometry.upper_pos)
      (geometry.children_line_class child)
      (geometry.modifiedParents_line_class second)
      1
      (by
        rw [← geometry.children_centered child]
        exact
          wz2PaperCenteredLineTube_midpoint_norm_le_one
            (geometry.children_line_class child))
      hsecond
  have triangle :=
    wz1PaperLineDistance_triangle
      (geometry.modifiedParents.tube second)
      (children.tube child)
      (geometry.modifiedParents.tube first)
  have symmetry :
      wz1PaperLineDistance
          (geometry.modifiedParents.tube second)
          (children.tube child) =
        wz1PaperLineDistance
          (children.tube child)
          (geometry.modifiedParents.tube second) :=
    wz1PaperLineDistance_symm _ _
  rw [symmetry] at triangle
  rw [geometry.modifiedParents_lineDistance second first] at triangle
  nlinarith

theorem conflict_degree
    (fixed : Fin geometry.modifiedParents.card) :
    (Finset.univ.filter fun other =>
      other ≠ fixed ∧
        (wz2PaperOrdinaryDilatedFiberIndices
            2 children geometry.modifiedParents fixed ∩
          wz2PaperOrdinaryDilatedFiberIndices
            2 children geometry.modifiedParents other).Nonempty).card ≤
      pureWZ2Prop62UpperConflictDegree := by
  let conflicts :=
    Finset.univ.filter fun other =>
      other ≠ fixed ∧
        (wz2PaperOrdinaryDilatedFiberIndices
            2 children geometry.modifiedParents fixed ∩
          wz2PaperOrdinaryDilatedFiberIndices
            2 children geometry.modifiedParents other).Nonempty
  have subset :
      conflicts ⊆
        Finset.univ.filter fun other =>
          wz1PaperLineDistance
              (oldParents.tube other)
              (oldParents.tube fixed) ≤
            2280 * upper := by
    intro other hother
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ other,
        geometry.conflict_lineDistance_le
          (Finset.mem_filter.mp hother).2.2⟩
  have packing :=
    tube_packing_bound_general
      geometry.old_essentially_distinct
      geometry.old_line_class geometry.upper_pos
      (2280 * upper)
      (mul_pos (by norm_num) geometry.upper_pos) fixed
  have ceilEq :
      Nat.ceil (8 * (2280 * upper) / upper) = 18240 := by
    have algebra :
        8 * (2280 * upper) / upper = 18240 := by
      field_simp [geometry.upper_pos.ne']
      ring
    rw [algebra]
    norm_num
  rw [ceilEq] at packing
  exact
    (Finset.card_le_card subset).trans <| by
      change
        (Finset.univ.filter fun other =>
          wz1PaperLineDistance
              (oldParents.tube other)
              (oldParents.tube fixed) ≤
            2280 * upper).card ≤
          pureWZ2Prop62UpperConflictDegree
      exact packing.trans <| by
        norm_num [pureWZ2Prop62UpperConflictDegree]

noncomputable def toUpperScaleInput :
    PureWZ2Prop62UpperScaleInput
      children geometry.modifiedParents
      pureWZ2Prop62UpperConflictDegree where
  rho_pos := geometry.rho_pos
  upper_pos := mul_pos (by norm_num) geometry.upper_pos
  owner := geometry.ancestor
  owner_surjective := geometry.ancestor_surjective
  owner_containment := geometry.owner_containment
  conflict_degree := geometry.conflict_degree

end PureWZ2Prop62UpperScaleGeometryInput

end Kakeya.Assouad

end
