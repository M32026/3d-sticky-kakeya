import MyLeanRepo.Kakeya.Assouad.WZ1.RootRelativeBalancedCoverStatements

/-!
# Dependent full-grain good-line boundary for WZ1 Lemma 18

The paper first passes from the original fine family to a balanced family of
`rho`-tubes.  It applies Lemma 17 twice on that `rho`-tube family, and only
then applies Proposition 5 again to the resulting shading at the actual
`sqrt rho` scale.

This file freezes the next geometric output on exactly that dependent chain.
In each active square-root cell it selects one actual line parallel to the
cell normal, retains every full grain met by that line, and records the
resulting mass retention.  It does not assert the final interval-covering
estimate or restore final extremality.
-/

noncomputable section

namespace Kakeya.Assouad

/-- The point at parameter `t` on the line through `anchor` in direction `normal`. -/
def wz1Lemma18LinePoint
    (anchor normal : Point3) (t : ℝ) : Point3 :=
  anchor + t • normal

/-- Parameters at which one selected line meets the supplied cell shading. -/
def wz1Lemma18LineParameters
    {cellCount : ℕ}
    (cell : Point3 → Fin cellCount)
    (source : Set Point3)
    (anchor normal : Fin cellCount → Point3)
    (c : Fin cellCount) : Set ℝ :=
  {t |
    wz1Lemma18LinePoint (anchor c) (normal c) t ∈ source ∧
      cell (wz1Lemma18LinePoint (anchor c) (normal c) t) = c}

/--
The union of the `rho`-grains in active cells that meet the selected line.

The existential parameter is required to be an actual shaded point on the
line in the same cell.  Thus this is not a single scalar slab: all grain
levels encountered along the good line are retained.
-/
def wz1Lemma18LineHitGrainRegion
    {cellCount : ℕ}
    (cell : Point3 → Fin cellCount)
    (activeCells : Finset (Fin cellCount))
    (source : Set Point3)
    (anchor normal : Fin cellCount → Point3)
    (rho : ℝ) : Set Point3 :=
  {p |
    ∃ c ∈ activeCells,
      cell p = c ∧
        ∃ t,
          t ∈ wz1Lemma18LineParameters
            cell source anchor normal c ∧
          |inner ℝ p (normal c) -
              inner ℝ
                (wz1Lemma18LinePoint (anchor c) (normal c) t)
                (normal c)| ≤ rho}

/--
Concrete pre-extremality output of the dependent full-grain/Fubini step in
WZ1 Lemma 18.

`outer` is the initial `rho`-cover of the original family.  `tauCube` and
`sqrtCube` are the two dependent Lemma 17 outputs on its `rho`-coarse family.
`innerCover` is the subsequent Proposition 5 call on exactly
`sqrtCube.shading`; its selected coordinate is the actual `sqrt rho` scale.
The supplied coarse plane map therefore carries the representative normal of
that same cell partition.
-/
structure WZ1NestedFullGrainGoodLineData
    {delta sigma outerLoss tauLoss sqrtLoss coverLoss retentionLoss : ℝ}
    {F : Kakeya.Streamlined.TubeFamily delta}
    {U : Kakeya.Streamlined.UniformTubeStructure F}
    {Y : Kakeya.Streamlined.TubeShading F}
    {rho : Kakeya.Streamlined.AdmissibleScale delta}
    (outer :
      WZ1BalancedCoverData
        (sigma := sigma) (epsilon := outerLoss) U Y rho)
    {scaleCount depth : ℕ}
    {innerSchedule :
      Fin scaleCount →
        Kakeya.Streamlined.AdmissibleScale rho.1}
    (sqrtCoordinate : Fin scaleCount)
    (rhoAtRho tauAtRho :
      Kakeya.Streamlined.AdmissibleScale rho.1)
    (plane : WZ1PlaneMapData outer.coarseShading)
    (tauCube :
      WZ1LocalGrainCubeCountData
        (sigma := sigma) (outputLoss := tauLoss)
        outer.coarseUniform outer.coarseShading
        plane rhoAtRho tauAtRho)
    (sqrtCube :
      WZ1LocalGrainCubeCountData
        (sigma := sigma) (outputLoss := sqrtLoss)
        outer.coarseUniform tauCube.shading
        tauCube.outputPlane rhoAtRho
        (innerSchedule sqrtCoordinate))
    (innerCover :
      WZ1RootRelativeBalancedCoverData
        (sigma := sigma) (epsilon := coverLoss)
        outer.coarseUniform sqrtCube.shading
        innerSchedule depth)
    (coarsePlane :
      WZ1CoarsePlaneMapData
        (incidenceScale :=
          5 * (innerSchedule sqrtCoordinate).1)
        (innerCover.toBalancedCoverData sqrtCoordinate)
        sqrtCube.outputPlane.planeMap) where
  /-- The projection resolution is the actual source `rho`. -/
  rhoAtRho_eq : rhoAtRho.1 = rho.1
  /-- The selected inner coordinate is the actual square-root scale. -/
  sqrtScale_eq :
    (innerSchedule sqrtCoordinate).1 = Real.sqrt rho.1
  /-- The first Lemma 17 spatial scale lies below the square-root scale. -/
  tau_le_sqrt :
    tauAtRho.1 ≤ (innerSchedule sqrtCoordinate).1
  /--
  Intermediate refinement on which every encountered projection level has a
  full `rho × sqrt rho × sqrt rho` grain.
  -/
  fullShading :
    Kakeya.Streamlined.TubeShading (U.coarse rho)
  full_subshading :
    IsSubshading fullShading innerCover.refined
  /-- Actual occupied cells of the dependent square-root cover. -/
  activeCells :
    Finset
      (Fin (innerCover.atScale sqrtCoordinate).cellCount)
  activeCells_spec :
    ∀ c : Fin (innerCover.atScale sqrtCoordinate).cellCount,
      c ∈ activeCells ↔
        (fullShading.union ∩
          {p |
            (innerCover.atScale sqrtCoordinate).cell p = c}).Nonempty
  /--
  Paper-scale volume floor in every retained square-root cell.
  -/
  cellVolumeLower :
    ∀ c ∈ activeCells,
      Kakeya.realRpowENN rho.1
          ((sigma + 3) / 2 + 2 * coverLoss) ≤
        MeasureTheory.volume
          (fullShading.union ∩
            {p |
              (innerCover.atScale sqrtCoordinate).cell p = c})
  /-- The representative normal attached to every square-root cell. -/
  cellNormal :
    Fin (innerCover.atScale sqrtCoordinate).cellCount → Point3
  cellNormal_eq :
    ∀ c,
      cellNormal c =
        sqrtCube.outputPlane.planeMap
          ((innerCover.atScale sqrtCoordinate).representative c)
  cellNormal_unit :
    ∀ c ∈ activeCells, ‖cellNormal c‖ = 1
  /--
  The supplied coarse plane map is constant at the representative normal on
  every active square-root cell.
  -/
  coarsePlane_eq_cellNormal :
    ∀ c ∈ activeCells,
      ∀ p ∈
          (innerCover.atScale sqrtCoordinate).coarseShading.union,
        (innerCover.atScale sqrtCoordinate).cell p = c →
          coarsePlane.planeMap.planeMap p = cellNormal c
  /-- One actual shaded anchor for the good line in each active cell. -/
  lineAnchor :
    Fin (innerCover.atScale sqrtCoordinate).cellCount → Point3
  lineAnchor_mem :
    ∀ c ∈ activeCells,
      lineAnchor c ∈ fullShading.union ∧
        (innerCover.atScale sqrtCoordinate).cell
            (lineAnchor c) = c
  /--
  Fubini lower bound for the one-dimensional set of shaded parameters on the
  selected line.
  -/
  goodLineLower :
    ∀ c ∈ activeCells,
      Kakeya.realRpowENN rho.1
          ((sigma + 3) / 2 + 2 * coverLoss) ≤
        MeasureTheory.volume
          (wz1Lemma18LineParameters
            (innerCover.atScale sqrtCoordinate).cell
            fullShading.union lineAnchor cellNormal c)
  /--
  Every projection level encountered on the good line carries a full grain.
  -/
  fullGrainLower :
    ∀ c ∈ activeCells,
      ∀ t ∈
          wz1Lemma18LineParameters
            (innerCover.atScale sqrtCoordinate).cell
            fullShading.union lineAnchor cellNormal c,
        Kakeya.realRpowENN rho.1
            (2 + 2 * coverLoss + sqrtLoss) ≤
          MeasureTheory.volume
            (fullShading.union ∩
              {p |
                (innerCover.atScale sqrtCoordinate).cell p = c} ∩
              {p |
                |inner ℝ p (cellNormal c) -
                    inner ℝ
                      (wz1Lemma18LinePoint
                        (lineAnchor c) (cellNormal c) t)
                      (cellNormal c)| ≤ rho.1})
  /-- Final coarse shading after retaining all line-hit grains. -/
  retainedShading :
    Kakeya.Streamlined.TubeShading (U.coarse rho)
  retained_subshading :
    IsSubshading retainedShading fullShading
  /--
  The retained carrier is exactly the restriction to all grains met by the
  selected good line in its actual cell.
  -/
  retained_carrier_eq :
    ∀ i,
      retainedShading.carrier i =
        fullShading.carrier i ∩
          wz1Lemma18LineHitGrainRegion
            (innerCover.atScale sqrtCoordinate).cell
            activeCells fullShading.union
            lineAnchor cellNormal rho.1
  /--
  Quantitative coarse mass preservation.  This is the output needed before
  the separate fine pullback and extremality restoration steps.
  -/
  mass_retention :
    Kakeya.realRpowENN rho.1 retentionLoss *
        innerCover.refined.mass ≤
      retainedShading.mass

/--
Select full grains meeting one good line in every occupied cell of the
dependent square-root cover.

The loss relation is the paper's
`epsilon₂ + epsilon₃ + 4 epsilon₄ ≤ outputLoss`.  Constants are absorbed by
shrinking the source `rho`; no final interval estimate or extremality
certificate occurs in the conclusion.
-/
def WZ1NestedFullGrainGoodLineSelectionStatement : Prop :=
  ∀ sigma outerLoss tauLoss sqrtLoss coverLoss retentionLoss : ℝ,
    0 < sigma → sigma < 1 →
    0 < outerLoss →
    0 < tauLoss →
    0 < sqrtLoss →
    0 < coverLoss →
    0 < retentionLoss →
    tauLoss + sqrtLoss + 4 * coverLoss < retentionLoss →
      ∃ rho₀ : ℝ,
        0 < rho₀ ∧ rho₀ ≤ 1 ∧
        ∀ {delta : ℝ}, 0 < delta →
          ∀ {F : Kakeya.Streamlined.TubeFamily delta},
            ∀ {U : Kakeya.Streamlined.UniformTubeStructure F},
              ∀ {Y : Kakeya.Streamlined.TubeShading F},
                ∀ {rho :
                    Kakeya.Streamlined.AdmissibleScale delta},
                  rho.1 ≤ rho₀ →
                  ∀ outer :
                      WZ1BalancedCoverData
                        (sigma := sigma) (epsilon := outerLoss)
                        U Y rho,
                    ∀ {scaleCount depth : ℕ},
                      ∀ {innerSchedule :
                          Fin scaleCount →
                            Kakeya.Streamlined.AdmissibleScale
                              rho.1},
                        ∀ sqrtCoordinate : Fin scaleCount,
                          ∀ rhoAtRho tauAtRho :
                              Kakeya.Streamlined.AdmissibleScale
                                rho.1,
                            rhoAtRho.1 = rho.1 →
                            (innerSchedule sqrtCoordinate).1 =
                              Real.sqrt rho.1 →
                            tauAtRho.1 ≤
                              (innerSchedule sqrtCoordinate).1 →
                            ∀ plane :
                                WZ1PlaneMapData
                                  outer.coarseShading,
                              ∀ tauCube :
                                  WZ1LocalGrainCubeCountData
                                    (sigma := sigma)
                                    (outputLoss := tauLoss)
                                    outer.coarseUniform
                                    outer.coarseShading
                                    plane rhoAtRho tauAtRho,
                                ∀ sqrtCube :
                                    WZ1LocalGrainCubeCountData
                                      (sigma := sigma)
                                      (outputLoss := sqrtLoss)
                                      outer.coarseUniform
                                      tauCube.shading
                                      tauCube.outputPlane rhoAtRho
                                      (innerSchedule
                                        sqrtCoordinate),
                                  ∀ innerCover :
                                      WZ1RootRelativeBalancedCoverData
                                        (sigma := sigma)
                                        (epsilon := coverLoss)
                                        outer.coarseUniform
                                        sqrtCube.shading
                                        innerSchedule depth,
                                    ∀ coarsePlane :
                                        WZ1CoarsePlaneMapData
                                          (incidenceScale :=
                                            5 *
                                              (innerSchedule
                                                sqrtCoordinate).1)
                                          (innerCover.toBalancedCoverData
                                            sqrtCoordinate)
                                          sqrtCube.outputPlane.planeMap,
                                      Nonempty
                                        (@WZ1NestedFullGrainGoodLineData
                                          delta sigma outerLoss
                                          tauLoss sqrtLoss coverLoss
                                          retentionLoss F U Y rho outer
                                          scaleCount depth innerSchedule
                                          sqrtCoordinate rhoAtRho tauAtRho
                                          plane tauCube sqrtCube innerCover
                                          coarsePlane)

end Kakeya.Assouad
