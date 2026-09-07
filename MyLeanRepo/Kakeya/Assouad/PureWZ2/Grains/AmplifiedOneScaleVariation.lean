import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.AmplifiedParentPairRefinement
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PaperOrientedCellRefinement
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.NearbyCellResidueRefinement
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.OneScaleVariationGeometry

/-!
# Multiplicity-amplified one-scale plane-map variation

This is the mass-efficient paper Lemma 14 and Corollary 15 assembly.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

theorem paper_amplified_one_scale_nearby_variation
    {delta rho kappa incidence : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading S : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (balanced : PureWZ2BalancedCoverData cover fineShading coarseShading)
    (hcoarseNonempty : coarse.Nonempty)
    (hSSubFine : PaperIsSubshading S fineShading)
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
    (fiberPower : ENNReal)
    (hfiber : ∀ parent p,
      (((Finset.univ.filter fun i : Fin fine.card =>
        PureWZ2.selectParent cover i = parent ∧ p ∈ S.carrier i).card : ℕ) :
        ENNReal) ≤ fiberPower *
          ((wz2PaperFullFiberIndices fine coarse parent).card : ENNReal))
    (hincidenceNonneg : 0 ≤ incidence)
    (hrho : 0 < rho) (hkappa : rho < kappa)
    (K : ℕ) (hK : 0 < K) (hrhoAligned : rho = (K : ℝ) * delta) :
    ∃ (selected : WZ1PaperTubeShading fine),
      PaperIsSubshading selected S ∧
      WZ1PaperIsCubicalShading selected ∧
      (∀ p ∈ selected.union, ∀ q ∈ selected.union,
        dist p q ≤ rho →
          dist (planeMap.planeMap p) (planeMap.planeMap q) ≤ rho) ∧
      (∀ p ∈ selected.union,
        selected.pointMultiplicity p = S.pointMultiplicity p) ∧
      (fineMultiplicity : ENNReal) ^ 2 * S.mass ≤
        27 * ((2 * fiberPower ^ 2) * fine.enncard ^ 2 *
          (wz1OrientationCapCount
            (10 * (incidence + rho / 2) / (kappa - rho)) rho : ENNReal)) *
          selected.mass := by
  rcases paper_amplified_parent_pair_refinement
      balanced hSSubFine hSCubical hcoarseNonempty
      fineMultiplicity hFineMultiplicity hclose fiberPower hfiber
      K hK hrhoAligned with
    ⟨chosen, paired, hpairedSub, hpairedCubical, hpairedGood, hpairedMultiplicity,
      hpairedMass⟩
  let pairedCells : Finset (ℤ × ℤ × ℤ) :=
    balanced.activeCells.filter fun c =>
      ∃ p ∈ paired.union, wz1PaperGridIndex rho p = c
  have hpairedSupport : ∀ p ∈ paired.union,
      wz1PaperGridIndex rho p ∈ pairedCells := by
    intro p hp
    apply Finset.mem_filter.mpr
    refine ⟨?_, p, hp, rfl⟩
    have hpFine : p ∈ fineShading.union := by
      rcases hp with ⟨i, hi⟩
      exact ⟨i, hSSubFine i (hpairedSub i hi)⟩
    exact paperBalanced_fine_point_active balanced p hpFine
  let firstDirection : (ℤ × ℤ × ℤ) → Point3 := fun c =>
    wz1PaperDirection (coarse.tube (chosen c).1)
  let secondDirection : (ℤ × ℤ × ℤ) → Point3 := fun c =>
    wz1PaperDirection (coarse.tube (chosen c).2)
  have hfirstUnit : ∀ c, ‖firstDirection c‖ = 1 := fun _ =>
    wz1PaperDirection_norm _
  have hsecondUnit : ∀ c, ‖secondDirection c‖ = 1 := fun _ =>
    wz1PaperDirection_norm _
  have htransverse : ∀ c ∈ pairedCells,
      kappa - rho ≤ ‖wz1Cross (firstDirection c) (secondDirection c)‖ := by
    intro c hc
    rcases (Finset.mem_filter.mp hc).2 with ⟨p, hp, hpcell⟩
    rcases hpairedGood p hp with
      ⟨first, second, hfirst, hsecond, hp1, hp2, hfineTransverseRaw⟩
    have hfirstCover : WZ1PaperTubeCovers
        (fine.tube first) (coarse.tube (chosen c).1) := by
      have h := PureWZ2.selectedParent_covers cover first
      simpa [hp1, hpcell] using h
    have hsecondCover : WZ1PaperTubeCovers
        (fine.tube second) (coarse.tube (chosen c).2) := by
      have h := PureWZ2.selectedParent_covers cover second
      simpa [hp2, hpcell] using h
    have hfineTransversePaper : kappa ≤
        ‖wz1Cross (wz1PaperDirection (fine.tube first))
          (wz1PaperDirection (fine.tube second))‖ := by
      rw [← raw_cross_norm_eq_paper_cross_norm]
      exact hfineTransverseRaw
    simpa [firstDirection, secondDirection] using
      paper_cover_parent_pair_transverse hfirstCover hsecondCover
        hfineTransversePaper
  have hplaneUnit : ∀ p ∈ paired.union, ‖planeMap.planeMap p‖ = 1 := by
    intro p hp
    apply planeMap.unit p
    rcases hp with ⟨i, hi⟩
    exact ⟨i, hpairedSub i hi⟩
  have hparentCovers : ∀ p ∈ paired.union,
      ∃ first second : Fin fine.card,
        p ∈ S.carrier first ∧ p ∈ S.carrier second ∧
        WZ1PaperTubeCovers (fine.tube first)
          (coarse.tube (chosen (wz1PaperGridIndex rho p)).1) ∧
        WZ1PaperTubeCovers (fine.tube second)
          (coarse.tube (chosen (wz1PaperGridIndex rho p)).2) := by
    intro p hp
    rcases hpairedGood p hp with
      ⟨first, second, hfirst, hsecond, hp1, hp2, _⟩
    exact ⟨first, second, hfirst, hsecond, by
      simpa [hp1] using PureWZ2.selectedParent_covers cover first, by
      simpa [hp2] using PureWZ2.selectedParent_covers cover second⟩
  have hfirstIncidence : ∀ p ∈ paired.union,
      |inner ℝ (planeMap.planeMap p)
        (firstDirection (wz1PaperGridIndex rho p))| ≤ incidence + rho / 2 := by
    intro p hp
    rcases hparentCovers p hp with
      ⟨first, _, hfirst, _, hfirstCover, _⟩
    have hincRaw := planeMap.incidence first p hfirst
    have hincPaper :
        |inner ℝ (wz1PaperDirection (fine.tube first))
          (planeMap.planeMap p)| ≤ incidence := by
      rw [← abs_inner_raw_eq_paperDirection]
      exact hincRaw
    have hcoarse := paper_cover_parent_incidence
      hfirstCover (hplaneUnit p hp) hincPaper
    rw [real_inner_comm]
    simpa [firstDirection] using hcoarse
  have hsecondIncidence : ∀ p ∈ paired.union,
      |inner ℝ (planeMap.planeMap p)
        (secondDirection (wz1PaperGridIndex rho p))| ≤ incidence + rho / 2 := by
    intro p hp
    rcases hparentCovers p hp with
      ⟨_, second, _, hsecond, _, hsecondCover⟩
    have hincRaw := planeMap.incidence second p hsecond
    have hincPaper :
        |inner ℝ (wz1PaperDirection (fine.tube second))
          (planeMap.planeMap p)| ≤ incidence := by
      rw [← abs_inner_raw_eq_paperDirection]
      exact hincRaw
    have hcoarse := paper_cover_parent_incidence
      hsecondCover (hplaneUnit p hp) hincPaper
    rw [real_inner_comm]
    simpa [secondDirection] using hcoarse
  have hgridMeasurable : Measurable (wz1PaperGridIndex rho) := by
    have h : Measurable (fun p : Point3 =>
        (⌊p 0 / rho⌋, ⌊p 1 / rho⌋, ⌊p 2 / rho⌋)) := by
      fun_prop
    convert h using 1
    funext p
    simp [wz1PaperGridIndex, gridIndex]
  have hgridFine : ∀ first second,
      wz1PaperGridIndex delta first =
        wz1PaperGridIndex delta second →
      wz1PaperGridIndex rho first = wz1PaperGridIndex rho second :=
    fun first second hgrid =>
      wz1PaperGridIndex_fine_to_coarse K hK hrhoAligned hgrid
  have hkappaDifference : 0 < kappa - rho := sub_pos.mpr hkappa
  have hincidenceCoarse : 0 ≤ incidence + rho / 2 := by
    linarith
  rcases paper_oriented_cell_refinement
      paired hpairedCubical planeMap.planeMap planeMap.measurable
      (wz1PaperGridIndex rho) hgridMeasurable hgridFine hplaneCell
      pairedCells hpairedSupport
      firstDirection secondDirection hkappaDifference hincidenceCoarse hrho
      hfirstUnit hsecondUnit htransverse hplaneUnit
      hfirstIncidence hsecondIncidence with
    ⟨oriented, horientedSub, horientedCubical, hcellVariation, horientedMultiplicity,
      horientedMass⟩
  have hdelta : 0 < delta := by
    have hKreal : 0 < (K : ℝ) := by exact_mod_cast hK
    rw [hrhoAligned] at hrho
    exact pos_of_mul_pos_right hrho hKreal.le
  rcases paper_aligned_nearby_cell_residue_refinement_cubical
      planeMap.planeMap hdelta hrho horientedCubical K hK hrhoAligned
      hcellVariation with
    ⟨selected, hselectedSubOriented, hselectedCubical, hnearbyVariation,
      hresidueMultiplicity,
      hresidueMass⟩
  have hselectedSubS : PaperIsSubshading selected S := fun i =>
    (hselectedSubOriented i).trans ((horientedSub i).trans (hpairedSub i))
  have hselectedMultiplicity : ∀ p ∈ selected.union,
      selected.pointMultiplicity p = S.pointMultiplicity p := by
    intro p hp
    have hpOriented : p ∈ oriented.union := by
      rcases hp with ⟨i, hi⟩
      exact ⟨i, hselectedSubOriented i hi⟩
    have hpPaired : p ∈ paired.union := by
      rcases hpOriented with ⟨i, hi⟩
      exact ⟨i, horientedSub i hi⟩
    exact (hresidueMultiplicity p hp).trans
      ((horientedMultiplicity p hpOriented).trans
        (hpairedMultiplicity p hpPaired))
  refine ⟨selected, hselectedSubS, hselectedCubical, hnearbyVariation,
    hselectedMultiplicity, ?_⟩
  let orientation : ENNReal :=
    (wz1OrientationCapCount
      (10 * (incidence + rho / 2) / (kappa - rho)) rho : ENNReal)
  calc
    (fineMultiplicity : ENNReal) ^ 2 * S.mass ≤
        (2 * fiberPower ^ 2) * fine.enncard ^ 2 * paired.mass := hpairedMass
    _ ≤ (2 * fiberPower ^ 2) * fine.enncard ^ 2 *
        (orientation * oriented.mass) := by gcongr
    _ ≤ (2 * fiberPower ^ 2) * fine.enncard ^ 2 *
        (orientation * (27 * selected.mass)) := by gcongr
    _ = 27 * ((2 * fiberPower ^ 2) * fine.enncard ^ 2 * orientation) *
        selected.mass := by ring

end Kakeya.Assouad

end
