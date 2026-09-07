import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CellwiseFiniteLabelMassRefinement
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.CubicalRefinement
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.RobustCloseCountPhase1

/-!
# Cellwise coarse-parent-pair refinement

The ordered pair of selected fine directions determines an ordered pair of
coarse parents.  In each active coarse cell we retain the heaviest parent-pair
class.  The number of available parents is bounded by the coarse point
multiplicity at the balanced cell representative, so the loss is the square
of that local multiplicity bound rather than the square of the entire coarse
family cardinality.

When `rho = K * delta`, coarse-cell membership is constant on fine grid cells;
therefore this whole-cell refinement preserves the paper cubical convention.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- Coarse parents whose carrier meets a given coarse grid cell. -/
def paperBalancedCellParents
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (_balanced : PureWZ2BalancedCoverData cover fineShading coarseShading)
    (cell : ℤ × ℤ × ℤ) : Finset (Fin coarse.card) :=
  Finset.univ.filter fun parent =>
    ∃ p ∈ wz1PaperGridCube rho cell, p ∈ coarseShading.carrier parent

/-- Cubicality turns meeting a coarse carrier into whole-cell containment. -/
lemma paperBalancedCellParents_whole_cell
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (balanced : PureWZ2BalancedCoverData cover fineShading coarseShading)
    {cell : ℤ × ℤ × ℤ} {parent : Fin coarse.card}
    (hparent : parent ∈ paperBalancedCellParents balanced cell) :
    ∀ p ∈ wz1PaperGridCube rho cell, p ∈ coarseShading.carrier parent := by
  have hmeet :
      ∃ p ∈ wz1PaperGridCube rho cell, p ∈ coarseShading.carrier parent := by
    simpa [paperBalancedCellParents, Finset.mem_filter] using hparent
  rcases hmeet with ⟨witness, hwitnessCell, hwitnessCarrier⟩
  have hwhole := balanced.coarse_cubical parent witness hwitnessCarrier
  have hwitnessIndex : wz1PaperGridIndex rho witness = cell :=
    (mem_wz1PaperGridCube rho cell witness).mp hwitnessCell
  intro p hpCell
  have hpIndex : wz1PaperGridIndex rho p = cell :=
    (mem_wz1PaperGridCube rho cell p).mp hpCell
  have hpInWitnessCell :
      p ∈ wz1PaperGridCube rho (wz1PaperGridIndex rho witness) := by
    rw [mem_wz1PaperGridCube]
    exact hpIndex.trans hwitnessIndex.symm
  exact hwhole hpInWitnessCell

/-- Every balanced fine point lies in an active coarse cell. -/
lemma paperBalanced_fine_point_active
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (balanced : PureWZ2BalancedCoverData cover fineShading coarseShading) :
    ∀ p ∈ fineShading.union,
      wz1PaperGridIndex rho p ∈ balanced.activeCells := by
  intro p hp
  have hpCoarse : p ∈ coarseShading.union := by
    rcases hp with ⟨i, hi⟩
    exact ⟨PureWZ2.selectParent cover i,
      balanced.point_compatibility i (PureWZ2.selectParent cover i)
        (PureWZ2.selectedParent_covers cover i) p hi⟩
  rw [balanced.coarse_union_eq] at hpCoarse
  simpa [Set.mem_iUnion] using hpCoarse

/-- The selected parent of a fine tube through a cell belongs to that cell's
parent set. -/
lemma selectedParent_mem_paperBalancedCellParents
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (balanced : PureWZ2BalancedCoverData cover fineShading coarseShading)
    {source : Fin fine.card} {p : Point3}
    (hp : p ∈ fineShading.carrier source) :
    PureWZ2.selectParent cover source ∈
      paperBalancedCellParents balanced (wz1PaperGridIndex rho p) := by
  simp only [paperBalancedCellParents, Finset.mem_filter, Finset.mem_univ,
    true_and]
  refine ⟨p, ?_, ?_⟩
  · rw [mem_wz1PaperGridCube]
  · exact balanced.point_compatibility source
      (PureWZ2.selectParent cover source)
      (PureWZ2.selectedParent_covers cover source) p hp

/-- The number of parents meeting an active cell is bounded by coarse
point multiplicity at the balanced representative. -/
lemma paperBalancedCellParents_card_le_multiplicity
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (balanced : PureWZ2BalancedCoverData cover fineShading coarseShading)
    {cell : ℤ × ℤ × ℤ} (hcell : cell ∈ balanced.activeCells) :
    (paperBalancedCellParents balanced cell).card ≤
      coarseShading.pointMultiplicity (balanced.cellRep cell hcell) := by
  change (paperBalancedCellParents balanced cell).card ≤
    ((Finset.univ : Finset (Fin coarse.card)).filter fun parent =>
      balanced.cellRep cell hcell ∈ coarseShading.carrier parent).card
  apply Finset.card_le_card
  intro parent hparent
  have hrepCell :
      balanced.cellRep cell hcell ∈ wz1PaperGridCube rho cell :=
    balanced.cellRep_in_cell cell hcell
  have hrepCarrier :
      balanced.cellRep cell hcell ∈ coarseShading.carrier parent :=
    paperBalancedCellParents_whole_cell balanced hparent
      (balanced.cellRep cell hcell) hrepCell
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ parent, hrepCarrier⟩

/-- Retain in every active coarse cell one ordered selected-parent pair. -/
theorem paper_cellwise_parent_pair_mass_refinement
    {delta rho kappa coarseCap : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {fineShading source selected : WZ1PaperTubeShading fine}
    {coarseShading : WZ1PaperTubeShading coarse}
    (balanced : PureWZ2BalancedCoverData cover fineShading coarseShading)
    (selection : PaperWZ1NarrowDirectionSelection source kappa)
    (hselectedSubFine : PaperIsSubshading selected fineShading)
    (hfirstFine : ∀ p ∈ selected.union,
      p ∈ fineShading.carrier (selection.first p))
    (hsecondFine : ∀ p ∈ selected.union,
      p ∈ fineShading.carrier (selection.second p))
    (hselectedCubical : WZ1PaperIsCubicalShading selected)
    (hselectionCell : ∀ p q,
      wz1PaperGridIndex delta p = wz1PaperGridIndex delta q →
        selection.first p = selection.first q ∧
        selection.second p = selection.second q)
    (hcoarseCap : ∀ p,
      (coarseShading.pointMultiplicity p : ENNReal) ≤
        ENNReal.ofReal coarseCap)
    (K : ℕ) (hK : 0 < K) (hrho : rho = (K : ℝ) * delta) :
    ∃ (chosen : (ℤ × ℤ × ℤ) →
        Fin coarse.card × Fin coarse.card)
      (refined : WZ1PaperTubeShading fine),
      PaperIsSubshading refined selected ∧
      WZ1PaperIsCubicalShading refined ∧
      (∀ p ∈ refined.union,
        PureWZ2.selectParent cover (selection.first p) =
            (chosen (wz1PaperGridIndex rho p)).1 ∧
          PureWZ2.selectParent cover (selection.second p) =
            (chosen (wz1PaperGridIndex rho p)).2) ∧
      selected.mass ≤ (ENNReal.ofReal coarseCap) ^ 2 * refined.mass := by
  classical
  let fineIndex : Fin fine.card := selection.first 0
  let coarseIndex : Fin coarse.card := PureWZ2.selectParent cover fineIndex
  letI : Nonempty (Fin coarse.card) := ⟨coarseIndex⟩
  let parentPair : Point3 → Fin coarse.card × Fin coarse.card := fun p =>
    (PureWZ2.selectParent cover (selection.first p),
      PureWZ2.selectParent cover (selection.second p))
  have hparentPairMeasurable : Measurable parentPair := by
    have hparent : Measurable (PureWZ2.selectParent cover) :=
      measurable_of_finite _
    exact (hparent.comp selection.first_measurable).prod
      (hparent.comp selection.second_measurable)
  let cell : Point3 → ℤ × ℤ × ℤ := wz1PaperGridIndex rho
  have hcellMeasurable : Measurable cell := by
    have h : Measurable (fun p : Point3 =>
        (⌊p 0 / rho⌋, ⌊p 1 / rho⌋, ⌊p 2 / rho⌋)) := by
      fun_prop
    convert h using 1
    funext p
    simp [cell, wz1PaperGridIndex, gridIndex]
  let allowed : (ℤ × ℤ × ℤ) →
      Finset (Fin coarse.card × Fin coarse.card) := fun c =>
    (paperBalancedCellParents balanced c).product
      (paperBalancedCellParents balanced c)
  have hsupport : ∀ p ∈ selected.union, cell p ∈ balanced.activeCells := by
    intro p hp
    exact paperBalanced_fine_point_active balanced p
      (by
        rcases hp with ⟨i, hi⟩
        exact ⟨i, hselectedSubFine i hi⟩)
  have hallowedNonempty : ∀ c ∈ balanced.activeCells,
      (allowed c).Nonempty := by
    intro c hc
    rcases balanced.cellIntersection_nonempty c hc with ⟨p, hpFine, hpCell⟩
    rcases hpFine with ⟨i, hi⟩
    have hparent : PureWZ2.selectParent cover i ∈
        paperBalancedCellParents balanced c := by
      have hpc : wz1PaperGridIndex rho p = c :=
        (mem_wz1PaperGridCube rho c p).mp hpCell
      simpa [hpc] using
        selectedParent_mem_paperBalancedCellParents balanced hi
    exact ⟨(PureWZ2.selectParent cover i, PureWZ2.selectParent cover i),
      Finset.mem_product.mpr ⟨hparent, hparent⟩⟩
  have hlabelAllowed : ∀ p ∈ selected.union,
      parentPair p ∈ allowed (cell p) := by
    intro p hp
    exact Finset.mem_product.mpr
      ⟨selectedParent_mem_paperBalancedCellParents balanced
          (hfirstFine p hp),
        selectedParent_mem_paperBalancedCellParents balanced
          (hsecondFine p hp)⟩
  have hlabelBound : ∀ c ∈ balanced.activeCells,
      ((allowed c).card : ENNReal) ≤ (ENNReal.ofReal coarseCap) ^ 2 := by
    intro c hc
    have hparentCardNat :=
      paperBalancedCellParents_card_le_multiplicity balanced hc
    have hparentCard :
        ((paperBalancedCellParents balanced c).card : ENNReal) ≤
          (coarseShading.pointMultiplicity (balanced.cellRep c hc) : ENNReal) := by
      exact_mod_cast hparentCardNat
    have hcap := hcoarseCap (balanced.cellRep c hc)
    have hlocal :
        ((paperBalancedCellParents balanced c).card : ENNReal) ≤
          ENNReal.ofReal coarseCap := hparentCard.trans hcap
    have hcardEq :
        ((allowed c).card : ENNReal) =
          ((paperBalancedCellParents balanced c).card : ENNReal) ^ 2 := by
      simp [allowed, Finset.card_product, pow_two]
    rw [hcardEq]
    exact pow_le_pow_left' hlocal 2
  have hchosenMeasurable : ∀ chosen : (ℤ × ℤ × ℤ) →
      Fin coarse.card × Fin coarse.card, Measurable chosen := fun _ =>
    Measurable.of_discrete
  rcases paper_cellwise_bounded_label_mass_refinement
      selected cell hcellMeasurable balanced.activeCells hsupport
      parentPair hparentPairMeasurable allowed hallowedNonempty
      hlabelAllowed ((ENNReal.ofReal coarseCap) ^ 2) hlabelBound
      hchosenMeasurable with
    ⟨chosen, refined, hsub, hrefinedEq, _hchosenAllowed, hpairs, hmass⟩
  have hcellConst : ∀ p q,
      wz1PaperGridIndex delta p = wz1PaperGridIndex delta q →
        cell p = cell q := by
    intro p q hgrid
    exact wz1PaperGridIndex_fine_to_coarse K hK hrho hgrid
  have hparentPairConst : ∀ p q,
      wz1PaperGridIndex delta p = wz1PaperGridIndex delta q →
        parentPair p = parentPair q := by
    intro p q hgrid
    rcases hselectionCell p q hgrid with ⟨hfirst, hsecond⟩
    simp [parentPair, hfirst, hsecond]
  have hrefinedCubical : WZ1PaperIsCubicalShading refined := by
    rw [hrefinedEq]
    exact paperCellwiseLabelRestriction_cubical hselectedCubical
      cell hcellMeasurable parentPair hparentPairMeasurable chosen
      (hchosenMeasurable chosen) hcellConst hparentPairConst
  refine ⟨chosen, refined, hsub, hrefinedCubical, ?_, hmass⟩
  intro p hp
  have heq := hpairs p hp
  exact ⟨congrArg Prod.fst heq, congrArg Prod.snd heq⟩

end Kakeya.Assouad

end
