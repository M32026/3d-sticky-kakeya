import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63DependentTwoLevelCover
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.SelectedCardinalityCancellation
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CellMassConversion
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.LocalAD
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperMultiplicityFloorVolume

/-!
# Dependent two-cover local volume bounds for Proposition 6.3

The HIGH part of the paper's Lemma 4.11 uses a second balanced cover of the
actual first coarse pair.  The inner coarse density and multiplicity cap give
a lower bound for its union volume.  Comparing that lower bound with the
number of active cells and the outer coarse volume upper bound controls the
inner balanced cell mass, hence the local volume of the inner refined union.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set ENNReal

/-- Density and the public Node-3 pointwise multiplicity cap cancel the
cardinality of the inner coarse family. -/
theorem proposition63_sticky_coarse_union_volume_lower
    {delta sigma outputLoss : ℝ}
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading source}
    {rho : WZ2PaperRequestedScale delta}
    {logExponent : ℕ}
    (sticky : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      sourceShading rho logExponent)
    (hrhoSmall : rho.1 ≤ 1 / 12) :
    Kakeya.realRpowENN rho.1 (sigma + 2 * outputLoss) ≤
      volume sticky.croppedCoarseShading.union := by
  let all := Kakeya.Streamlined.TubeSubfamily.fromFinset
    sticky.coarse Finset.univ
  have allCard : all.family.enncard = sticky.coarse.enncard := by
    simp [all, Kakeya.Streamlined.TubeSubfamily.fromFinset,
      Kakeya.Streamlined.TubeFamily.enncard]
  have massLower :
      Kakeya.realRpowENN rho.1 (outputLoss + 2) *
          sticky.coarse.enncard ≤ sticky.croppedCoarseShading.mass := by
    have h := selected_cardinality_cancellation sticky.coarse_extremal
      sticky.cover.coarse_line_class all hrhoSmall
    rwa [allCard] at h
  have massUpper : sticky.croppedCoarseShading.mass ≤
      (Kakeya.realRpowENN rho.1 (2 - sigma - outputLoss) *
          sticky.coarse.enncard) *
        volume sticky.croppedCoarseShading.union :=
    mass_le_of_pointMultiplicity_le fun point _ =>
      sticky.coarse_multiplicity_upper point
  let common : ENNReal :=
    Kakeya.realRpowENN rho.1 (2 - sigma - outputLoss) *
      sticky.coarse.enncard
  have common_ne_zero : common ≠ 0 := by
    apply mul_ne_zero
    · simp [Kakeya.realRpowENN, Real.rpow_pos_of_pos
        sticky.coarse_extremal.delta_pos]
    · simpa [Kakeya.Streamlined.TubeFamily.enncard] using
        sticky.coarse_extremal.nonempty.ne'
  have common_ne_top : common ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by simp [Kakeya.realRpowENN])
      (by simp [Kakeya.Streamlined.TubeFamily.enncard])
  have powerSplit :
      Kakeya.realRpowENN rho.1 (outputLoss + 2) =
        Kakeya.realRpowENN rho.1 (sigma + 2 * outputLoss) *
          Kakeya.realRpowENN rho.1 (2 - sigma - outputLoss) := by
    rw [← realRpowENN_add sticky.coarse_extremal.delta_pos]
    congr 1
    ring
  have bounded :
      Kakeya.realRpowENN rho.1 (sigma + 2 * outputLoss) * common ≤
        volume sticky.croppedCoarseShading.union * common := by
    calc
      Kakeya.realRpowENN rho.1 (sigma + 2 * outputLoss) * common =
          Kakeya.realRpowENN rho.1 (outputLoss + 2) *
            sticky.coarse.enncard := by
        rw [powerSplit]
        simp only [common]
        ring
      _ ≤ sticky.croppedCoarseShading.mass := massLower
      _ ≤ common * volume sticky.croppedCoarseShading.union := massUpper
      _ = volume sticky.croppedCoarseShading.union * common := by ring
  exact (ENNReal.mul_le_mul_iff_left common_ne_zero common_ne_top).mp bounded

/-- The inner balanced-cell mass in a dependent two-level cover is bounded
by the outer coarse volume budget times one inner grid-cube volume, divided
by the inner coarse volume floor.  This is the exact cancellation used before
the paper's Fubini good-line selection. -/
theorem Proposition63DependentTwoLevelCoverData.inner_cellMass_upper
    {delta sigma outerLoss reentryLoss innerLoss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {fineShading : WZ1PaperTubeShading fine}
    {rho : WZ2PaperRequestedScale delta}
    {normalizationExponent outerLogExponent innerLogExponent : ℕ}
    {outer : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outerLoss)
      fineShading rho outerLogExponent}
    {reentry : Proposition63DependentCoarseReentryData
      (reentryLoss := reentryLoss) outer normalizationExponent}
    {tau : WZ2PaperRequestedScale rho.1}
    (data : Proposition63DependentTwoLevelCoverData
      (innerLoss := innerLoss) (innerLogExponent := innerLogExponent)
      reentry tau)
    (htauSmall : tau.1 ≤ 1 / 12) :
    data.inner.balanced.cellMass ≤
      (Kakeya.realRpowENN rho.1 (sigma - outerLoss) *
          volume (wz1PaperGridCube tau.1 (0, 0, 0))) /
        Kakeya.realRpowENN tau.1 (sigma + 2 * innerLoss) := by
  let active : ENNReal := data.inner.balanced.activeCells.card
  let cubeVolume : ENNReal :=
    volume (wz1PaperGridCube tau.1 (0, 0, 0))
  let lower : ENNReal :=
    Kakeya.realRpowENN tau.1 (sigma + 2 * innerLoss)
  let upper : ENNReal :=
    Kakeya.realRpowENN rho.1 (sigma - outerLoss)
  have coarseLower : lower ≤
      volume data.inner.croppedCoarseShading.union := by
    exact proposition63_sticky_coarse_union_volume_lower
      data.inner htauSmall
  have coarseVolume : volume data.inner.croppedCoarseShading.union =
      active * cubeVolume := by
    simpa only [active, cubeVolume] using
      balanced_cover_coarse_volume data.inner.balanced
        data.inner.coarse_extremal.delta_pos
  have fineVolume : volume data.inner.refined.union =
      active * data.inner.balanced.cellMass := by
    simpa only [active] using
      balanced_cover_fine_union_volume data.inner.balanced
        data.inner.coarse_extremal.delta_pos
  have fineUpper : volume data.inner.refined.union ≤ upper := by
    have innerSubOuter : data.inner.refined.union ⊆
        outer.croppedCoarseShading.union := by
      rintro point ⟨index, hpoint⟩
      exact ⟨data.outerCoarseEmbedding index,
        data.inner_refined_sub_outer_coarse index hpoint⟩
    exact (measure_mono innerSubOuter).trans
      outer.coarse_extremal.volume_upper
  have activeCellUpper :
      active * data.inner.balanced.cellMass ≤ upper := by
    rw [← fineVolume]
    exact fineUpper
  have cellScaled : data.inner.balanced.cellMass * lower ≤
      upper * cubeVolume := by
    calc
      data.inner.balanced.cellMass * lower ≤
          data.inner.balanced.cellMass * (active * cubeVolume) := by
        gcongr
        simpa only [coarseVolume] using coarseLower
      _ = (active * data.inner.balanced.cellMass) * cubeVolume := by ring
      _ ≤ upper * cubeVolume := by gcongr
  have lower_ne_zero : lower ≠ 0 := by
    simp [lower, Kakeya.realRpowENN, Real.rpow_pos_of_pos
      data.inner.coarse_extremal.delta_pos]
  have lower_ne_top : lower ≠ ⊤ := by
    simp [lower, Kakeya.realRpowENN]
  apply (ENNReal.le_div_iff_mul_le
    (Or.inl lower_ne_zero) (Or.inl lower_ne_top)).2
  exact cellScaled

/-- Power-form corollary of `inner_cellMass_upper`.  The exact volume of one
inner grid cube cancels the inner coarse-volume floor. -/
theorem Proposition63DependentTwoLevelCoverData.inner_cellMass_power_upper
    {delta sigma outerLoss reentryLoss innerLoss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {fineShading : WZ1PaperTubeShading fine}
    {rho : WZ2PaperRequestedScale delta}
    {normalizationExponent outerLogExponent innerLogExponent : ℕ}
    {outer : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outerLoss)
      fineShading rho outerLogExponent}
    {reentry : Proposition63DependentCoarseReentryData
      (reentryLoss := reentryLoss) outer normalizationExponent}
    {tau : WZ2PaperRequestedScale rho.1}
    (data : Proposition63DependentTwoLevelCoverData
      (innerLoss := innerLoss) (innerLogExponent := innerLogExponent)
      reentry tau)
    (htauSmall : tau.1 ≤ 1 / 12) :
    data.inner.balanced.cellMass ≤
      Kakeya.realRpowENN rho.1 (sigma - outerLoss) *
        Kakeya.realRpowENN tau.1 (3 - sigma - 2 * innerLoss) := by
  apply (data.inner_cellMass_upper htauSmall).trans_eq
  rw [wz1PaperGridCube_volume_exact
    data.inner.coarse_extremal.delta_pos]
  have cubePower : ENNReal.ofReal (tau.1 ^ 3) =
      Kakeya.realRpowENN tau.1 3 := by
    simp only [Kakeya.realRpowENN]
    congr 1
    exact (Real.rpow_natCast tau.1 3).symm
  rw [cubePower]
  have powerQuotient : Kakeya.realRpowENN tau.1 3 /
        Kakeya.realRpowENN tau.1 (sigma + 2 * innerLoss) =
      Kakeya.realRpowENN tau.1 (3 - sigma - 2 * innerLoss) := by
    have denominatorPos :
        0 < Real.rpow tau.1 (sigma + 2 * innerLoss) :=
      Real.rpow_pos_of_pos data.inner.coarse_extremal.delta_pos _
    have exponent : 3 - sigma - 2 * innerLoss =
        3 - (sigma + 2 * innerLoss) := by ring
    simp only [Kakeya.realRpowENN]
    calc
      ENNReal.ofReal (Real.rpow tau.1 3) /
          ENNReal.ofReal (Real.rpow tau.1 (sigma + 2 * innerLoss)) =
          ENNReal.ofReal (Real.rpow tau.1 3 /
            Real.rpow tau.1 (sigma + 2 * innerLoss)) :=
        (ENNReal.ofReal_div_of_pos denominatorPos).symm
      _ = ENNReal.ofReal
          (Real.rpow tau.1 (3 - (sigma + 2 * innerLoss))) :=
        congrArg ENNReal.ofReal <|
          (Real.rpow_sub data.inner.coarse_extremal.delta_pos 3
            (sigma + 2 * innerLoss)).symm
      _ = ENNReal.ofReal
          (Real.rpow tau.1 (3 - sigma - 2 * innerLoss)) := by
        rw [exponent]
  rw [mul_div_assoc, powerQuotient]

/-- Local volume upper bound on the actual inner refinement.  Both covers are
visible in the statement: `rho` is the first coarse scale, `tau` is the
dependent second scale, and `radius` is the local Fubini window. -/
theorem Proposition63DependentTwoLevelCoverData.inner_local_volume_upper
    {delta sigma outerLoss reentryLoss innerLoss radius : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {fineShading : WZ1PaperTubeShading fine}
    {rho : WZ2PaperRequestedScale delta}
    {normalizationExponent outerLogExponent innerLogExponent : ℕ}
    {outer : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outerLoss)
      fineShading rho outerLogExponent}
    {reentry : Proposition63DependentCoarseReentryData
      (reentryLoss := reentryLoss) outer normalizationExponent}
    {tau : WZ2PaperRequestedScale rho.1}
    (data : Proposition63DependentTwoLevelCoverData
      (innerLoss := innerLoss) (innerLogExponent := innerLogExponent)
      reentry tau)
    (htauSmall : tau.1 ≤ 1 / 12)
    (hradiusPos : 0 < radius)
    (htauRadius : tau.1 ≤ radius)
    (q : Point3) :
    volume (data.inner.refined.union ∩ Metric.closedBall q radius) ≤
      (8 * 27 : ENNReal) * ENNReal.ofReal ((radius / tau.1) ^ 3) *
        ((Kakeya.realRpowENN rho.1 (sigma - outerLoss) *
            volume (wz1PaperGridCube tau.1 (0, 0, 0))) /
          Kakeya.realRpowENN tau.1 (sigma + 2 * innerLoss)) := by
  exact (Kakeya.Assouad.pureWz2_local_volume_upper
    (sigma := sigma) data.inner.balanced
    data.inner.coarse_extremal.delta_pos hradiusPos htauRadius q).trans
      (mul_le_mul_left' (data.inner_cellMass_upper htauSmall) _)

/-- The paper's local `3 * tau` window bound in power form.  The fixed
constant `5832 = 8 * 27 * 3^3` comes only from grid geometry. -/
theorem Proposition63DependentTwoLevelCoverData.inner_three_tau_volume_upper
    {delta sigma outerLoss reentryLoss innerLoss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {fineShading : WZ1PaperTubeShading fine}
    {rho : WZ2PaperRequestedScale delta}
    {normalizationExponent outerLogExponent innerLogExponent : ℕ}
    {outer : PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outerLoss)
      fineShading rho outerLogExponent}
    {reentry : Proposition63DependentCoarseReentryData
      (reentryLoss := reentryLoss) outer normalizationExponent}
    {tau : WZ2PaperRequestedScale rho.1}
    (data : Proposition63DependentTwoLevelCoverData
      (innerLoss := innerLoss) (innerLogExponent := innerLogExponent)
      reentry tau)
    (htauSmall : tau.1 ≤ 1 / 12)
    (q : Point3) :
    volume (data.inner.refined.union ∩
        Metric.closedBall q (3 * tau.1)) ≤
      (5832 : ENNReal) *
        (Kakeya.realRpowENN rho.1 (sigma - outerLoss) *
          Kakeya.realRpowENN tau.1 (3 - sigma - 2 * innerLoss)) := by
  have radiusPos : 0 < 3 * tau.1 := by
    nlinarith [data.inner.coarse_extremal.delta_pos]
  have tauRadius : tau.1 ≤ 3 * tau.1 := by
    linarith [data.inner.coarse_extremal.delta_pos]
  have hlocal : volume (data.inner.refined.union ∩
        Metric.closedBall q (3 * tau.1)) ≤
      (8 * 27 : ENNReal) *
        ENNReal.ofReal (((3 * tau.1) / tau.1) ^ 3) *
          data.inner.balanced.cellMass :=
    Kakeya.Assouad.pureWz2_local_volume_upper
      (delta := rho.1) (sigma := sigma) (L := tau.1)
      (tau := 3 * tau.1) (fine := data.inner.selected.family)
      (coarse := data.inner.coarse) (cover := data.inner.cover)
      (fineShading := data.inner.refined)
      (coarseShading := data.inner.croppedCoarseShading)
      data.inner.balanced data.inner.coarse_extremal.delta_pos
      radiusPos tauRadius q
  have ratio : (3 * tau.1) / tau.1 = 3 := by
    field_simp [data.inner.coarse_extremal.delta_pos.ne']
  rw [ratio] at hlocal
  norm_num at hlocal
  calc
    volume (data.inner.refined.union ∩
        Metric.closedBall q (3 * tau.1)) ≤
        (5832 : ENNReal) * data.inner.balanced.cellMass := by
      simpa only [ratio] using hlocal
    _ ≤ (5832 : ENNReal) *
        (Kakeya.realRpowENN rho.1 (sigma - outerLoss) *
          Kakeya.realRpowENN tau.1 (3 - sigma - 2 * innerLoss)) := by
      gcongr
      exact data.inner_cellMass_power_upper htauSmall
    _ = (5832 : ENNReal) *
        (Kakeya.realRpowENN rho.1 (sigma - outerLoss) *
          Kakeya.realRpowENN tau.1 (3 - sigma - 2 * innerLoss)) := by
      norm_num

end Kakeya.Assouad.PureWZ2

end
