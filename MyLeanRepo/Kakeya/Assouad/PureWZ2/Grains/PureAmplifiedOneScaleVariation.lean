import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PureAmplifiedParentPairRefinement
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PureCarrierDirectionAlignment
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PaperOrientedCellRefinement
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.NearbyCellResidueRefinement

/-!
# One-scale variation from a pure Definition 2.12 cover

The pure cover supplies ordinary strict-carrier parents rather than the
Section 6 line-cover relation.  The pure carrier direction lemmas transfer
transversality and plane incidence to those parents, with losses `8 * rho`
and `4 * rho`.  The weighted parent-pair selector, orientation refinement,
and fixed residue refinement then give the paper one-scale variation bound.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- One-scale nearby variation using only a literal pure partitioning cover. -/
theorem paper_pure_amplified_one_scale_nearby_variation
    {delta parentRadius spatialScale variationScale kappa incidence : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily parentRadius}
    (cover : WZ2PaperPurePartitioningCover fine coarse)
    {S : WZ1PaperTubeShading fine}
    (hfineNonempty : fine.Nonempty)
    (hline : WZ1PaperIsLineClass fine)
    (hSCubical : WZ1PaperIsCubicalShading S)
    (planeMap : PaperWZ1WeakPlaneMapData S incidence)
    (hplaneCell : ∀ first second,
      wz1PaperGridIndex delta first =
        wz1PaperGridIndex delta second →
      planeMap.planeMap first = planeMap.planeMap second)
    (fineMultiplicity : ℕ)
    (hFineMultiplicity : ∀ p ∈ S.union,
      fineMultiplicity ≤ S.pointMultiplicity p)
    (hclose : ∀ p ∈ S.union, ∀ i, p ∈ S.carrier i →
      2 * paperCloseDirectionCount S p i kappa ≤ fineMultiplicity)
    (hincidenceNonnegative : 0 ≤ incidence)
    (hparentRadius : 0 < parentRadius)
    (hparentRadiusSmall : parentRadius < 1 / 8)
    (hspatialScale : 0 < spatialScale)
    (hvariationScale : 0 < variationScale)
    (hkappa : 8 * parentRadius < kappa)
    (K : ℕ) (hK : 0 < K)
    (hspatialScaleAligned : spatialScale = (K : ℝ) * delta) :
    ∃ selected : WZ1PaperTubeShading fine,
      PaperIsSubshading selected S ∧
      WZ1PaperIsCubicalShading selected ∧
      (∀ p ∈ selected.union, ∀ q ∈ selected.union,
        dist p q ≤ spatialScale →
          dist (planeMap.planeMap p) (planeMap.planeMap q) ≤
            variationScale) ∧
      (∀ p ∈ selected.union,
        selected.pointMultiplicity p = S.pointMultiplicity p) ∧
      (fineMultiplicity : ENNReal) ^ 2 * S.mass ≤
        27 * (2 * fine.enncard ^ 2 *
          (wz1OrientationCapCount
            (10 * (incidence + 4 * parentRadius) /
              (kappa - 8 * parentRadius)) variationScale :
              ENNReal)) * selected.mass := by
  have hcoarseNonempty : coarse.Nonempty := by
    let source : Fin fine.card := ⟨0, hfineNonempty⟩
    exact (Nat.zero_le (cover.parent source).1).trans_lt
      (cover.parent source).isLt
  rcases paper_pure_amplified_parent_pair_refinement
      cover hSCubical hcoarseNonempty fineMultiplicity hFineMultiplicity
      hclose hparentRadius hspatialScale K hK hspatialScaleAligned with
    ⟨chosen, paired, hpairedSub, hpairedCubical, hpairedGood,
      hpairedMultiplicity, hpairedMass⟩
  let pairedCells : Finset (ℤ × ℤ × ℤ) :=
    (wz1PaperGridIndicesInWindow spatialScale hspatialScale).filter fun c =>
      ∃ p ∈ paired.union, wz1PaperGridIndex spatialScale p = c
  have hpairedSupport : ∀ p ∈ paired.union,
      wz1PaperGridIndex spatialScale p ∈ pairedCells := by
    intro p hp
    apply Finset.mem_filter.mpr
    refine ⟨?_, p, hp, rfl⟩
    rcases hp with ⟨index, hindex⟩
    have hpointS : p ∈ S.carrier index := hpairedSub index hindex
    exact paper_point_gridIndex_in_window hspatialScale
      (S.subset_body index hpointS).2
  let firstDirection : (ℤ × ℤ × ℤ) → Point3 := fun c =>
    wz1PaperDirection (coarse.tube (chosen c).1)
  let secondDirection : (ℤ × ℤ × ℤ) → Point3 := fun c =>
    wz1PaperDirection (coarse.tube (chosen c).2)
  have hfirstUnit : ∀ c, ‖firstDirection c‖ = 1 := fun _ =>
    wz1PaperDirection_norm _
  have hsecondUnit : ∀ c, ‖secondDirection c‖ = 1 := fun _ =>
    wz1PaperDirection_norm _
  have hdelta : 0 < delta := by
    have hKreal : 0 < (K : ℝ) := by exact_mod_cast hK
    rw [hspatialScaleAligned] at hspatialScale
    exact pos_of_mul_pos_right hspatialScale hKreal.le
  have htransverse : ∀ c ∈ pairedCells,
      kappa - 8 * parentRadius ≤
        ‖wz1Cross (firstDirection c) (secondDirection c)‖ := by
    intro c hc
    rcases (Finset.mem_filter.mp hc).2 with ⟨p, hp, hpcell⟩
    rcases hpairedGood p hp with
      ⟨first, second, hfirst, hsecond, hp1, hp2, hfineRaw⟩
    have hfirstParent : cover.parent first = (chosen c).1 := by
      simpa [hpcell] using hp1
    have hsecondParent : cover.parent second = (chosen c).2 := by
      simpa [hpcell] using hp2
    have hfirstContained :
        (fine.tube first).carrier ⊆ (coarse.tube (chosen c).1).carrier := by
      have hmem := cover.parent_mem_fullFiber first
      rw [mem_wz2PaperOrdinaryFullFiberIndices_iff] at hmem
      simpa [hfirstParent] using hmem
    have hsecondContained :
        (fine.tube second).carrier ⊆ (coarse.tube (chosen c).2).carrier := by
      have hmem := cover.parent_mem_fullFiber second
      rw [mem_wz2PaperOrdinaryFullFiberIndices_iff] at hmem
      simpa [hsecondParent] using hmem
    have hfinePaper : kappa ≤
        ‖wz1Cross (wz1PaperDirection (fine.tube first))
          (wz1PaperDirection (fine.tube second))‖ := by
      rw [← raw_cross_norm_eq_paper_cross_norm]
      exact hfineRaw
    simpa [firstDirection, secondDirection] using
      PureWZ2.pure_carrier_parent_pair_transverse
        hdelta.le hparentRadius hparentRadiusSmall
        (hline first) (hline second)
        hfirstContained hsecondContained hfinePaper
  have hplaneUnit : ∀ p ∈ paired.union, ‖planeMap.planeMap p‖ = 1 := by
    intro p hp
    apply planeMap.unit p
    rcases hp with ⟨index, hindex⟩
    exact ⟨index, hpairedSub index hindex⟩
  have hparentWitness : ∀ p ∈ paired.union,
      ∃ first second : Fin fine.card,
        p ∈ S.carrier first ∧ p ∈ S.carrier second ∧
        (fine.tube first).carrier ⊆
          (coarse.tube
            (chosen (wz1PaperGridIndex spatialScale p)).1).carrier ∧
        (fine.tube second).carrier ⊆
          (coarse.tube
            (chosen (wz1PaperGridIndex spatialScale p)).2).carrier := by
    intro p hp
    rcases hpairedGood p hp with
      ⟨first, second, hfirst, hsecond, hp1, hp2, _⟩
    refine ⟨first, second, hfirst, hsecond, ?_, ?_⟩
    · have hmem := cover.parent_mem_fullFiber first
      rw [mem_wz2PaperOrdinaryFullFiberIndices_iff] at hmem
      simpa [hp1] using hmem
    · have hmem := cover.parent_mem_fullFiber second
      rw [mem_wz2PaperOrdinaryFullFiberIndices_iff] at hmem
      simpa [hp2] using hmem
  have hfirstIncidence : ∀ p ∈ paired.union,
      |inner ℝ (planeMap.planeMap p)
        (firstDirection (wz1PaperGridIndex spatialScale p))| ≤
          incidence + 4 * parentRadius := by
    intro p hp
    rcases hparentWitness p hp with
      ⟨first, _, hfirst, _, hfirstContained, _⟩
    have hfineIncidence :
        |inner ℝ (wz1PaperDirection (fine.tube first))
          (planeMap.planeMap p)| ≤ incidence := by
      rw [← abs_inner_raw_eq_paperDirection]
      exact planeMap.incidence first p hfirst
    have hcoarse := PureWZ2.pure_carrier_parent_incidence
      hdelta.le hparentRadius hparentRadiusSmall
      (hline first) hfirstContained
      (hplaneUnit p hp) hfineIncidence
    rw [real_inner_comm]
    simpa [firstDirection] using hcoarse
  have hsecondIncidence : ∀ p ∈ paired.union,
      |inner ℝ (planeMap.planeMap p)
        (secondDirection (wz1PaperGridIndex spatialScale p))| ≤
          incidence + 4 * parentRadius := by
    intro p hp
    rcases hparentWitness p hp with
      ⟨_, second, _, hsecond, _, hsecondContained⟩
    have hfineIncidence :
        |inner ℝ (wz1PaperDirection (fine.tube second))
          (planeMap.planeMap p)| ≤ incidence := by
      rw [← abs_inner_raw_eq_paperDirection]
      exact planeMap.incidence second p hsecond
    have hcoarse := PureWZ2.pure_carrier_parent_incidence
      hdelta.le hparentRadius hparentRadiusSmall
      (hline second) hsecondContained
      (hplaneUnit p hp) hfineIncidence
    rw [real_inner_comm]
    simpa [secondDirection] using hcoarse
  have hgridMeasurable : Measurable (wz1PaperGridIndex spatialScale) := by
    have h : Measurable (fun p : Point3 =>
        (⌊p 0 / spatialScale⌋, ⌊p 1 / spatialScale⌋,
          ⌊p 2 / spatialScale⌋)) := by
      fun_prop
    convert h using 1
    funext p
    simp [wz1PaperGridIndex, gridIndex]
  have hgridFine : ∀ first second,
      wz1PaperGridIndex delta first =
        wz1PaperGridIndex delta second →
      wz1PaperGridIndex spatialScale first =
        wz1PaperGridIndex spatialScale second :=
    fun first second hgrid =>
      wz1PaperGridIndex_fine_to_coarse
        K hK hspatialScaleAligned hgrid
  have hkappaDifference : 0 < kappa - 8 * parentRadius :=
    sub_pos.mpr hkappa
  have hincidenceCoarse : 0 ≤ incidence + 4 * parentRadius := by
    positivity
  rcases paper_oriented_cell_refinement
      paired hpairedCubical planeMap.planeMap planeMap.measurable
      (wz1PaperGridIndex spatialScale) hgridMeasurable hgridFine hplaneCell
      pairedCells hpairedSupport firstDirection secondDirection
      hkappaDifference hincidenceCoarse hvariationScale
      hfirstUnit hsecondUnit
      htransverse hplaneUnit hfirstIncidence hsecondIncidence with
    ⟨oriented, horientedSub, horientedCubical, hcellVariation,
      horientedMultiplicity, horientedMass⟩
  rcases paper_aligned_nearby_cell_residue_refinement_cubical
      planeMap.planeMap hdelta hspatialScale horientedCubical
      K hK hspatialScaleAligned
      hcellVariation with
    ⟨selected, hselectedSubOriented, hselectedCubical, hnearbyVariation,
      hselectedMultiplicityOriented, hresidueMass⟩
  have hselectedSubS : PaperIsSubshading selected S := fun index =>
    (hselectedSubOriented index).trans
      ((horientedSub index).trans (hpairedSub index))
  have hselectedMultiplicity : ∀ p ∈ selected.union,
      selected.pointMultiplicity p = S.pointMultiplicity p := by
    intro p hp
    have hpOriented : p ∈ oriented.union := by
      rcases hp with ⟨index, hindex⟩
      exact ⟨index, hselectedSubOriented index hindex⟩
    have hpPaired : p ∈ paired.union := by
      rcases hpOriented with ⟨index, hindex⟩
      exact ⟨index, horientedSub index hindex⟩
    exact (hselectedMultiplicityOriented p hp).trans
      ((horientedMultiplicity p hpOriented).trans
        (hpairedMultiplicity p hpPaired))
  refine ⟨selected, hselectedSubS, hselectedCubical, hnearbyVariation,
    hselectedMultiplicity, ?_⟩
  let orientation : ENNReal :=
    (wz1OrientationCapCount
      (10 * (incidence + 4 * parentRadius) /
        (kappa - 8 * parentRadius)) variationScale : ENNReal)
  calc
    (fineMultiplicity : ENNReal) ^ 2 * S.mass ≤
        2 * fine.enncard ^ 2 * paired.mass := hpairedMass
    _ ≤ 2 * fine.enncard ^ 2 * (orientation * oriented.mass) := by
      gcongr
    _ ≤ 2 * fine.enncard ^ 2 *
        (orientation * (27 * selected.mass)) := by gcongr
    _ = 27 * (2 * fine.enncard ^ 2 * orientation) * selected.mass := by
      ring

/-- Cancel the square of the fine cardinality against a pointwise density
floor. -/
theorem paper_pure_amplified_one_scale_nearby_variation_cancel_cardinality
    {delta parentRadius spatialScale variationScale kappa incidence : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily parentRadius}
    (cover : WZ2PaperPurePartitioningCover fine coarse)
    {S : WZ1PaperTubeShading fine}
    (hfineNonempty : fine.Nonempty)
    (hline : WZ1PaperIsLineClass fine)
    (hSCubical : WZ1PaperIsCubicalShading S)
    (planeMap : PaperWZ1WeakPlaneMapData S incidence)
    (hplaneCell : ∀ first second,
      wz1PaperGridIndex delta first =
        wz1PaperGridIndex delta second →
      planeMap.planeMap first = planeMap.planeMap second)
    (fineMultiplicity : ℕ)
    (hFineMultiplicity : ∀ p ∈ S.union,
      fineMultiplicity ≤ S.pointMultiplicity p)
    (hclose : ∀ p ∈ S.union, ∀ i, p ∈ S.carrier i →
      2 * paperCloseDirectionCount S p i kappa ≤ fineMultiplicity)
    (densityPower : ENNReal)
    (hdensity : densityPower * fine.enncard ≤
      (fineMultiplicity : ENNReal))
    (hincidenceNonnegative : 0 ≤ incidence)
    (hparentRadius : 0 < parentRadius)
    (hparentRadiusSmall : parentRadius < 1 / 8)
    (hspatialScale : 0 < spatialScale)
    (hvariationScale : 0 < variationScale)
    (hkappa : 8 * parentRadius < kappa)
    (K : ℕ) (hK : 0 < K)
    (hspatialScaleAligned : spatialScale = (K : ℝ) * delta) :
    ∃ selected : WZ1PaperTubeShading fine,
      PaperIsSubshading selected S ∧
      WZ1PaperIsCubicalShading selected ∧
      (∀ p ∈ selected.union, ∀ q ∈ selected.union,
        dist p q ≤ spatialScale →
          dist (planeMap.planeMap p) (planeMap.planeMap q) ≤
            variationScale) ∧
      (∀ p ∈ selected.union,
        selected.pointMultiplicity p = S.pointMultiplicity p) ∧
      densityPower ^ 2 * S.mass ≤
        27 * (2 *
          (wz1OrientationCapCount
            (10 * (incidence + 4 * parentRadius) /
              (kappa - 8 * parentRadius)) variationScale :
              ENNReal)) * selected.mass := by
  rcases paper_pure_amplified_one_scale_nearby_variation
      cover hfineNonempty hline hSCubical planeMap hplaneCell
      fineMultiplicity hFineMultiplicity hclose hincidenceNonnegative
      hparentRadius hparentRadiusSmall hspatialScale hvariationScale
      hkappa K hK hspatialScaleAligned with
    ⟨selected, hselectedSub, hselectedCubical, hvariation,
      hselectedMultiplicity, hmass⟩
  refine ⟨selected, hselectedSub, hselectedCubical, hvariation,
    hselectedMultiplicity, ?_⟩
  let orientation : ENNReal :=
    (wz1OrientationCapCount
      (10 * (incidence + 4 * parentRadius) /
        (kappa - 8 * parentRadius)) variationScale : ENNReal)
  have hdensitySq :
      densityPower ^ 2 * fine.enncard ^ 2 ≤
        (fineMultiplicity : ENNReal) ^ 2 := by
    simpa [mul_pow] using pow_le_pow_left' hdensity 2
  have hscaled :
      fine.enncard ^ 2 * (densityPower ^ 2 * S.mass) ≤
        fine.enncard ^ 2 *
          (27 * (2 * orientation) * selected.mass) := by
    calc
      fine.enncard ^ 2 * (densityPower ^ 2 * S.mass) =
          (densityPower ^ 2 * fine.enncard ^ 2) * S.mass := by ring
      _ ≤ (fineMultiplicity : ENNReal) ^ 2 * S.mass := by gcongr
      _ ≤ 27 * (2 * fine.enncard ^ 2 * orientation) *
          selected.mass := hmass
      _ = fine.enncard ^ 2 *
          (27 * (2 * orientation) * selected.mass) := by ring
  have hcardZero : fine.enncard ^ 2 ≠ 0 := by
    apply pow_ne_zero
    change (fine.card : ENNReal) ≠ 0
    exact_mod_cast Nat.one_le_iff_ne_zero.mp hfineNonempty
  have hcardTop : fine.enncard ^ 2 ≠ ⊤ := by
    simp [Kakeya.Streamlined.TubeFamily.enncard]
  have hcancel :=
    (ENNReal.mul_le_mul_iff_right hcardZero hcardTop).mp hscaled
  simpa [orientation] using hcancel

end Kakeya.Assouad

end
