import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.DirectHalfOffsetTerminalBallCover
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.OffsetProjectiveProjectionCovariance
import MyLeanRepo.Kakeya.Assouad.PureWZ2.LargeSlope.FiniteCoverLocalADCore

/-!
# Exact local AD for the direct half-offset terminal

This file is the structural layer of the terminal local-grain argument.  It
keeps the actual projective terminal normal, transports source local AD on
each occupied finite-cover piece by exact signed covariance, and recombines
the pieces using the one-Lipschitz exact normal field.  Numerical bounds for
the cover and their final power absorption are deliberately kept outside the
structural theorem.
-/

noncomputable section

namespace Kakeya.Assouad

open Metric Set

namespace PureWZ2DirectCommonYSourceAssembly

variable
    {logExponent : ℕ}
    {sigma epsilon delta : ℝ}
    (commonSource : PureWZ2DirectCommonYSourceAssembly
      logExponent sigma epsilon delta)

namespace TerminalGeometry

/-- The actual exact terminal normal field is one-Lipschitz on the exact
terminal set. -/
theorem exactPlaneMap_lipschitz (terminal : commonSource.TerminalGeometry) :
    LipschitzWith 1 (exactPlaneMap commonSource terminal) := by
  have hset : LipschitzWith 1 (exactSetPoint commonSource terminal) := by
    apply LipschitzWith.of_dist_le_mul
    intro first second
    simp only [NNReal.coe_one, one_mul]
    change dist (first : Point3) second ≤ dist (first : Point3) second
    exact le_rfl
  have hcomp := (commonSource.halfOffsetTerminalExactPlaneMap_lipschitz
    terminal.retubing terminal.box).comp hset
  change LipschitzWith 1 (fun point =>
    commonSource.halfOffsetTerminalExactPlaneMap terminal.retubing terminal.box
      (exactSetPoint commonSource terminal point))
  convert hcomp using 1
  · norm_num
  · rfl

/-- The exact terminal set localized to a ball about an occupied exact
anchor. -/
def exactLocalSet (terminal : commonSource.TerminalGeometry)
    (anchor : {point : Point3 // point ∈ terminal.exactShading.union})
    (radius : ℝ) : Set Point3 :=
  terminal.exactShading.union ∩
    Metric.closedBall (anchor : Point3) radius

/-- The exact terminal point corresponding to a genuine point of the explicit
terminal source set. -/
def targetPointOfExactSource (terminal : commonSource.TerminalGeometry)
    (point : {point : Point3 // point ∈
      exactTerminalSourceSet commonSource terminal}) :
    {point : Point3 // point ∈ terminal.exactShading.union} :=
  ⟨totalAffineMap commonSource terminal point, point.property.2⟩

/-- A genuine source point of the exact terminal, viewed in the domain of the
source local-grain plane map. -/
def exactSourcePoint (terminal : commonSource.TerminalGeometry)
    (point : {point : Point3 // point ∈
      exactTerminalSourceSet commonSource terminal}) :
    {point : Point3 // point ∈
      commonSource.halfOffsetAssembly.horizontalSource.sourceShading.union} :=
  commonSource.halfOffsetTerminalSourcePoint terminal.retubing terminal.box
    pureWZ2DirectHalfOffsetTerminalLambda_pos
    (exactSetPoint commonSource terminal
      (targetPointOfExactSource commonSource terminal point))

@[simp] theorem exactSourcePoint_coe
    (terminal : commonSource.TerminalGeometry)
    (point : {point : Point3 // point ∈
      exactTerminalSourceSet commonSource terminal}) :
    (exactSourcePoint commonSource terminal point : Point3) = point := by
  exact congrArg Subtype.val
    (halfOffsetTerminalSourcePoint_totalAffineMap commonSource terminal
      point point.property)

/-- At an occupied source anchor, the exact terminal plane map is literally
the normalized projective transport of the source plane-map normal. -/
theorem exactPlaneMap_targetPointOfExactSource
    (terminal : commonSource.TerminalGeometry)
    (point : {point : Point3 // point ∈
      exactTerminalSourceSet commonSource terminal}) :
    let source := commonSource.halfOffsetAssembly.horizontalSource
    let b := source.m * (source.d - source.c) / 2
    let S := 2 / (source.d - source.c)
    exactPlaneMap commonSource terminal
        (targetPointOfExactSource commonSource terminal point) =
      pureWZ2OffsetProjectiveTotalNormalizedNormal b S
        pureWZ2DirectHalfOffsetTerminalLambda
        (pureWZ2OffsetShearProjectiveNormal
          (PureWZ2HalfOffsetHorizontalSourceData.offset source)
          (source.sourceLocalGrains.planeMap
            (exactSourcePoint commonSource terminal point))) := by
  rfl

/-- Every point of the literal exact terminal lies in the strict coordinate
box inherited from the selected `(x,z)` terminal source. -/
theorem exact_point_coordinate_abs_le
    (terminal : commonSource.TerminalGeometry)
    (point : {point : Point3 // point ∈ terminal.exactShading.union})
    (coordinate : Fin 3) :
    |(point : Point3) coordinate| ≤ 1 / 50 := by
  have hmem : (point : Point3) ∈
      commonSource.halfOffsetTerminalExactSet terminal.retubing terminal.box
        (lambda := pureWZ2DirectHalfOffsetTerminalLambda) := by
    rw [← terminal.exact_union]
    exact point.property
  rcases hmem with ⟨sourcePoint, hsourcePoint, hpoint⟩
  rw [← hpoint]
  have hsourcePoint' : sourcePoint ∈
      (commonSource.halfOffsetLineClassTerminalSourceShading terminal.retubing
        terminal.box).union := by
    rw [commonSource.halfOffsetLineClassTerminalSourceShading_union]
    exact hsourcePoint
  exact commonSource.halfOffsetLineClass_image_coordinate_bound
    terminal.retubing terminal.box hsourcePoint' coordinate

/-- A convenient Euclidean norm bound for exact terminal points. -/
theorem exact_point_norm_le_one_div_twentyFive
    (terminal : commonSource.TerminalGeometry)
    (point : {point : Point3 // point ∈ terminal.exactShading.union}) :
    ‖(point : Point3)‖ ≤ 1 / 25 := by
  have h0 := exact_point_coordinate_abs_le commonSource terminal point (0 : Fin 3)
  have h1 := exact_point_coordinate_abs_le commonSource terminal point (1 : Fin 3)
  have h2 := exact_point_coordinate_abs_le commonSource terminal point (2 : Fin 3)
  have hnormSq := point3_coord_norm_sq (point : Point3)
  have hsq : ‖(point : Point3)‖ ^ 2 ≤ 3 / 2500 := by
    rw [hnormSq]
    nlinarith [sq_abs ((point : Point3) 0), sq_abs ((point : Point3) 1),
      sq_abs ((point : Point3) 2), abs_nonneg ((point : Point3) 0),
      abs_nonneg ((point : Point3) 1), abs_nonneg ((point : Point3) 2)]
  nlinarith [norm_nonneg (point : Point3)]

/-- Structural finite-cover theorem for exact terminal local AD.  Each source
piece carries source local AD at `sourceRho`; exact signed covariance moves it
to the corresponding terminal normal, `hbase` weakens the transported scale
to `targetRho`, and the one-Lipschitz actual normal field recenters and joins
the finitely many target pieces. -/
theorem exact_local_ad_of_finite_source_cover
    (terminal : commonSource.TerminalGeometry)
    (anchor0 : {point : Point3 // point ∈ terminal.exactShading.union})
    {ι : Type*} {indices : Finset ι}
    (sourcePieces : ι → Set Point3)
    (sourceAnchor : ι → {point : Point3 // point ∈
      exactTerminalSourceSet commonSource terminal})
    {R R0 epsilon sourceRho targetRho alpha : ℝ} {C : ENNReal}
    (hR0 : 0 ≤ R0)
    (hcover : exactLocalSet commonSource terminal anchor0 R0 ⊆
      ⋃ index ∈ indices,
        totalAffineMap commonSource terminal '' sourcePieces index)
    (hanchorBall : ∀ index ∈ indices,
      totalAffineMap commonSource terminal
          (sourceAnchor index : Point3) ∈
        Metric.closedBall (anchor0 : Point3) R0)
    (hpieces : ∀ index ∈ indices,
      totalAffineMap commonSource terminal '' sourcePieces index ⊆
        Metric.closedBall
          (totalAffineMap commonSource terminal
            (sourceAnchor index : Point3)) R)
    (hsourceAD : ∀ index ∈ indices,
      PureWZ2PaperADSet1
        (scalarProjection
          (commonSource.halfOffsetAssembly.horizontalSource.sourceLocalGrains
            |>.planeMap (exactSourcePoint commonSource terminal
              (sourceAnchor index)))
          (sourcePieces index)) sourceRho alpha C)
    (hbase : ∀ index ∈ indices,
      |pureWZ2OffsetProjectiveProjectionScale
          (PureWZ2HalfOffsetHorizontalSourceData.offset
            commonSource.halfOffsetAssembly.horizontalSource)
          (commonSource.halfOffsetAssembly.horizontalSource.m *
            (commonSource.halfOffsetAssembly.horizontalSource.d -
              commonSource.halfOffsetAssembly.horizontalSource.c) / 2)
          (2 / (commonSource.halfOffsetAssembly.horizontalSource.d -
            commonSource.halfOffsetAssembly.horizontalSource.c))
          pureWZ2DirectHalfOffsetTerminalLambda
          (commonSource.halfOffsetAssembly.horizontalSource.sourceLocalGrains
            |>.planeMap (exactSourcePoint commonSource terminal
              (sourceAnchor index)))| * sourceRho ≤ targetRho)
    (htargetRho : 0 < targetRho)
    (hR : 0 ≤ R)
    (hepsilon : 0 < epsilon)
    (herror : R * R0 ≤ epsilon) :
    PureWZ2PaperADSet1
      (scalarProjection (exactPlaneMap commonSource terminal anchor0)
        (exactLocalSet commonSource terminal anchor0 R0))
      targetRho alpha
      ((indices.card : ENNReal) *
        ((2 * (Nat.ceil (epsilon / targetRho) + 1) : ENNReal) ^ 3 * C)) := by
  classical
  let source := commonSource.halfOffsetAssembly.horizontalSource
  let a := PureWZ2HalfOffsetHorizontalSourceData.offset source
  let b := source.m * (source.d - source.c) / 2
  let S := 2 / (source.d - source.c)
  let target := exactLocalSet commonSource terminal anchor0 R0
  let localAnchor : target := ⟨anchor0, anchor0.property,
    Metric.mem_closedBall_self hR0⟩
  let field : target → Point3 := fun point =>
    exactPlaneMap commonSource terminal ⟨point, point.property.1⟩
  let pieceAnchor : ι → target := fun index =>
    if hindex : index ∈ indices then
      ⟨targetPointOfExactSource commonSource terminal (sourceAnchor index),
        (sourceAnchor index).property.2, hanchorBall index hindex⟩
    else localAnchor
  have hlengthPos : 0 < source.d - source.c := sub_pos.mpr source.ordered
  have hb : b ≠ 0 := by
    apply ne_of_gt
    dsimp only [b]
    exact div_pos (mul_pos source.slopeScale_pos hlengthPos) (by norm_num)
  have hS : S ≠ 0 := by
    dsimp only [S]
    exact div_ne_zero (by norm_num) hlengthPos.ne'
  have hlambda : pureWZ2DirectHalfOffsetTerminalLambda ≠ 0 :=
    pureWZ2DirectHalfOffsetTerminalLambda_pos.ne'
  have hfield : LipschitzWith 1 field := by
    apply LipschitzWith.of_dist_le_mul
    intro first second
    simpa only [field, NNReal.coe_one, one_mul, Subtype.dist_eq] using
      (exactPlaneMap_lipschitz commonSource terminal).dist_le_mul
        (⟨first, first.property.1⟩ :
          {point : Point3 // point ∈ terminal.exactShading.union})
        (⟨second, second.property.1⟩ :
          {point : Point3 // point ∈ terminal.exactShading.union})
  have hpieceAD : ∀ index ∈ indices,
      PureWZ2PaperADSet1
        (scalarProjection (field (pieceAnchor index))
          (totalAffineMap commonSource terminal '' sourcePieces index))
        targetRho alpha C := by
    intro index hindex
    simp only [field, pieceAnchor, hindex, ↓reduceDIte]
    let normal := source.sourceLocalGrains.planeMap
      (exactSourcePoint commonSource terminal (sourceAnchor index))
    have hw : pureWZ2OffsetShearNormal a normal 1 ≠ 0 := by
      have hchart :=
        PureWZ2HalfOffsetHorizontalSourceData.offsetShearNormal_coord_one_lower_restrict
            source commonSource.halfOffsetAssembly_compatibility
            (exactSourcePoint commonSource terminal (sourceAnchor index))
      intro hzero
      rw [hzero, abs_zero] at hchart
      norm_num at hchart
    have htransport :=
      pureWZ2OffsetProjective_projection_paperAD_of_sub
        hb hS hlambda (totalAffineMap commonSource terminal)
        (sourceAnchor index : Point3) normal
        (fun point => totalAffineMap_sub commonSource terminal point
          (sourceAnchor index : Point3))
        hw (sourcePieces index) (hsourceAD index hindex)
    have hweaken := htransport.weaken_scale htargetRho (hbase index hindex)
    rw [exactPlaneMap_targetPointOfExactSource commonSource terminal]
    exact hweaken
  apply PureWZ2PaperADSet1.finite_cover_local_lipschitz_field
    localAnchor field pieceAnchor hfield hcover
  · intro index hindex
    rw [show pieceAnchor index =
        ⟨targetPointOfExactSource commonSource terminal (sourceAnchor index),
          (sourceAnchor index).property.2, hanchorBall index hindex⟩ by
      simp only [pieceAnchor, hindex, ↓reduceDIte]]
    exact hpieces index hindex
  · exact hpieceAD
  · intro point hpoint
    exact hpoint.2
  · exact hR
  · exact hepsilon
  · exact herror

end TerminalGeometry

end PureWZ2DirectCommonYSourceAssembly

end Kakeya.Assouad

end
