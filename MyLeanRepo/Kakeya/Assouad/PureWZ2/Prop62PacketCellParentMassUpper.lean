import MyLeanRepo.Kakeya.Assouad.PureWZ2.Prop62ParentClassSelection
import MyLeanRepo.Kakeya.Assouad.PropStickyExactCellBalancingHelpers
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperShadingMassUpper

/-!
# Proposition 6.2 packet-cell parent-mass upper bound

For one metric parent, the selected packet-cell incidence weight counts only
whole shaded cells carried by sources in its complete metric fiber. Double
counting these incidences by source, followed by the cubical carrier identity,
bounds the parent-class mass by the shaded mass of that complete fiber.
The standard quadratic tube-carrier estimate then gives the required absolute
constant `55296 * deltaTubeVolume 1`.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

private theorem card_relation_eq_sum_left
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (left : Finset α) (right : Finset β)
    (relation : α → β → Prop) [DecidableRel relation] :
    ((left ×ˢ right).filter fun pair =>
        relation pair.1 pair.2).card =
      ∑ first ∈ left,
        (right.filter fun second =>
          relation first second).card := by
  rw [Finset.card_filter, Finset.sum_product]
  simp_rw [Finset.card_filter]

private theorem card_relation_eq_sum_right
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (left : Finset α) (right : Finset β)
    (relation : α → β → Prop) [DecidableRel relation] :
    ((left ×ˢ right).filter fun pair =>
        relation pair.1 pair.2).card =
      ∑ second ∈ right,
        (left.filter fun first =>
          relation first second).card := by
  rw [Finset.card_filter, Finset.sum_product]
  rw [Finset.sum_comm]
  simp_rw [Finset.card_filter]

namespace PureWZ2Prop62PacketCellInput

variable
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {coarse : Kakeya.Streamlined.TubeFamily rho}
    {cover : PureWZ2Section6Cover fine coarse}
    {shading : WZ1PaperTubeShading fine}
    (input : PureWZ2Prop62PacketCellInput cover shading)
    (multiplicity : input.FineMultiplicityClassData)

private def sourceCellsForParent
    (parent : Fin coarse.card)
    (source : Fin fine.card) :
    Finset WZ2PaperCellIndex :=
  input.fineCells.filter fun cell =>
    source ∈ input.packetCellSources parent cell

private theorem selectedPairsAt_second_injective
    (parent : Fin coarse.card) :
    Set.InjOn
      (fun pair : Fin coarse.card × WZ2PaperCellIndex => pair.2)
      (↑(input.selectedPairsAt multiplicity parent) :
        Set (Fin coarse.card × WZ2PaperCellIndex)) := by
  intro first firstMem second secondMem cellEq
  have firstParent :
      first.1 = parent :=
    (Finset.mem_filter.mp firstMem).2
  have secondParent :
      second.1 = parent :=
    (Finset.mem_filter.mp secondMem).2
  exact Prod.ext (firstParent.trans secondParent.symm) cellEq

private theorem sourceIncidenceCount_le_carrierCellCount
    (parent : Fin coarse.card)
    (source : Fin fine.card) :
    ((input.selectedPairsAt multiplicity parent).filter fun pair =>
        source ∈ input.packetCellSources pair.1 pair.2).card ≤
      (input.sourceCellsForParent parent source).card := by
  let incident :=
    (input.selectedPairsAt multiplicity parent).filter fun pair =>
      source ∈ input.packetCellSources pair.1 pair.2
  have secondInjective :
      Set.InjOn
        (fun pair : Fin coarse.card × WZ2PaperCellIndex => pair.2)
        (↑incident :
          Set (Fin coarse.card × WZ2PaperCellIndex)) := by
    exact
      (input.selectedPairsAt_second_injective multiplicity parent).mono <| by
        intro pair pairMem
        exact (Finset.mem_filter.mp pairMem).1
  have imageSubset :
      Finset.image Prod.snd incident ⊆
        input.sourceCellsForParent parent source := by
    intro cell cellMem
    rcases Finset.mem_image.mp cellMem with ⟨pair, pairMem, rfl⟩
    have pairSelectedAt :=
      (Finset.mem_filter.mp pairMem).1
    have pairParent : pair.1 = parent :=
      (Finset.mem_filter.mp pairSelectedAt).2
    have sourceMem :=
      (Finset.mem_filter.mp pairMem).2
    have pairData :=
      (input.mem_packetCellSources_iff
        pair.1 pair.2 source).mp sourceMem
    exact
      Finset.mem_filter.mpr
        ⟨pairData.1, by simpa [pairParent] using sourceMem⟩
  calc
    ((input.selectedPairsAt multiplicity parent).filter fun pair =>
        source ∈ input.packetCellSources pair.1 pair.2).card =
        (Finset.image Prod.snd incident).card := by
      exact (Finset.card_image_iff.mpr secondInjective).symm
    _ ≤
        (input.sourceCellsForParent parent source).card :=
      Finset.card_le_card imageSubset

private theorem sourceCellsForParent_mass_le
    (parent : Fin coarse.card)
    (source : Fin fine.card) :
    ((input.sourceCellsForParent parent source).card : ENNReal) *
        volume (wz1PaperGridCube delta (0, 0, 0)) ≤
      volume (shading.carrier source) := by
  rw [← wz1PaperGridCube_volume_biUnion input.delta_pos]
  apply measure_mono
  intro point pointMem
  rcases Set.mem_iUnion₂.mp pointMem with
    ⟨cell, cellMem, pointCell⟩
  have sourceMem :
      source ∈ input.packetCellSources parent cell :=
    (Finset.mem_filter.mp cellMem).2
  exact
    ((input.mem_packetCellSources_iff parent cell source).mp
      sourceMem).2.2 pointCell

private theorem parentIncidenceWeight_le_sourceCellCount
    (parent : Fin coarse.card) :
    input.parentIncidenceWeight multiplicity parent ≤
      ∑ source ∈ wz2PaperFullFiberIndices fine coarse parent,
        (input.sourceCellsForParent parent source).card := by
  let pairs := input.selectedPairsAt multiplicity parent
  let sources := wz2PaperFullFiberIndices fine coarse parent
  let relation :
      (Fin coarse.card × WZ2PaperCellIndex) →
        Fin fine.card → Prop :=
    fun pair source =>
      source ∈ input.packetCellSources pair.1 pair.2
  have leftCount :=
    card_relation_eq_sum_left pairs sources relation
  have rightCount :=
    card_relation_eq_sum_right pairs sources relation
  calc
    input.parentIncidenceWeight multiplicity parent =
        ∑ pair ∈ pairs,
          (sources.filter fun source =>
            relation pair source).card := by
      apply Finset.sum_congr rfl
      intro pair pairMem
      change
        (input.packetCellSources pair.1 pair.2).card =
          (sources.filter fun source =>
            source ∈ input.packetCellSources pair.1 pair.2).card
      congr 1
      ext source
      have pairParent : pair.1 = parent :=
        (Finset.mem_filter.mp pairMem).2
      constructor
      · intro sourceMem
        have sourceFiber :=
          (input.mem_packetCellSources_iff
            pair.1 pair.2 source).mp sourceMem |>.2.1
        exact
          Finset.mem_filter.mpr
            ⟨by simpa [sources, pairParent] using sourceFiber, sourceMem⟩
      · exact fun sourceMem => (Finset.mem_filter.mp sourceMem).2
    _ =
        ((pairs ×ˢ sources).filter fun incidence =>
          relation incidence.1 incidence.2).card :=
      leftCount.symm
    _ =
        ∑ source ∈ sources,
          (pairs.filter fun pair =>
            relation pair source).card :=
      rightCount
    _ ≤
        ∑ source ∈ sources,
          (input.sourceCellsForParent parent source).card := by
      exact Finset.sum_le_sum fun source _ =>
        input.sourceIncidenceCount_le_carrierCellCount
          multiplicity parent source

/--
The selected packet-cell mass at any parent is bounded by the shaded mass of
the complete metric fiber over that parent.
-/
theorem parentClassMass_le_actualFiberShadedMass
    (parent : Fin coarse.card) :
    input.parentClassMass multiplicity parent ≤
      ∑ source ∈ wz2PaperFullFiberIndices fine coarse parent,
        volume (shading.carrier source) := by
  have countBound :=
    input.parentIncidenceWeight_le_sourceCellCount multiplicity parent
  have countBoundENN :
      (input.parentIncidenceWeight multiplicity parent : ENNReal) ≤
        ((∑ source ∈ wz2PaperFullFiberIndices fine coarse parent,
          (input.sourceCellsForParent parent source).card : ℕ) : ENNReal) := by
    exact_mod_cast countBound
  calc
    input.parentClassMass multiplicity parent =
        (input.parentIncidenceWeight multiplicity parent : ENNReal) *
          volume (wz1PaperGridCube delta (0, 0, 0)) := rfl
    _ ≤
        ((∑ source ∈ wz2PaperFullFiberIndices fine coarse parent,
          (input.sourceCellsForParent parent source).card : ℕ) : ENNReal) *
          volume (wz1PaperGridCube delta (0, 0, 0)) := by
      exact mul_le_mul_right' countBoundENN _
    _ =
        ∑ source ∈ wz2PaperFullFiberIndices fine coarse parent,
          ((input.sourceCellsForParent parent source).card : ENNReal) *
            volume (wz1PaperGridCube delta (0, 0, 0)) := by
      rw [Nat.cast_sum, Finset.sum_mul]
    _ ≤
        ∑ source ∈ wz2PaperFullFiberIndices fine coarse parent,
          volume (shading.carrier source) := by
      exact Finset.sum_le_sum fun source _ =>
        input.sourceCellsForParent_mass_le parent source

/--
Uniform absolute upper bound for the selected packet-cell mass of any metric
parent. No membership in the selected parent class is required.
-/
theorem selectedParentMassUpper
    (delta_le_one_twenty_four : delta ≤ 1 / 24)
    (parent : Fin coarse.card) :
    input.parentClassMass multiplicity parent ≤
      input.parentFiberCard parent *
        (55296 * Kakeya.deltaTubeVolume 1) *
        Kakeya.realRpowENN delta 2 := by
  let fiber :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset
      fine (wz2PaperFullFiberIndices fine coarse parent)
  let fiberShading := restrictPaperShading fiber shading
  have fiberMassEq :
      (∑ source ∈ wz2PaperFullFiberIndices fine coarse parent,
          volume (shading.carrier source)) =
        fiberShading.mass := by
    rw [restrictPaperShading_mass]
    let equivalence :
        Fin fiber.family.card ≃
          wz2PaperFullFiberIndices fine coarse parent :=
      (wz2PaperFullFiberIndices fine coarse parent)
        |>.orderIsoOfFin rfl |>.toEquiv
    exact
      ((Fintype.sum_equiv equivalence
          (fun index : Fin fiber.family.card =>
            volume (shading.carrier (fiber.embedding index)))
          (fun source :
            wz2PaperFullFiberIndices fine coarse parent =>
            volume (shading.carrier source.1))
          (fun _ => rfl)).trans
        (Finset.sum_coe_sort
          (wz2PaperFullFiberIndices fine coarse parent)
          (fun source => volume (shading.carrier source)))).symm
  have fiberMassUpper :
      fiberShading.mass ≤
        (55296 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN delta 2 *
          fiber.family.enncard :=
    wz2_paper_shading_mass_upper
      input.delta_pos delta_le_one_twenty_four
      (cover.fine_line_class.subfamily fiber) fiberShading
  calc
    input.parentClassMass multiplicity parent ≤
        ∑ source ∈ wz2PaperFullFiberIndices fine coarse parent,
          volume (shading.carrier source) :=
      input.parentClassMass_le_actualFiberShadedMass multiplicity parent
    _ = fiberShading.mass := fiberMassEq
    _ ≤
        ((55296 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN delta 2) *
          fiber.family.enncard := fiberMassUpper
    _ =
        input.parentFiberCard parent *
          (55296 * Kakeya.deltaTubeVolume 1) *
          Kakeya.realRpowENN delta 2 := by
      unfold parentFiberCard
      change
        (55296 * Kakeya.deltaTubeVolume 1) *
            Kakeya.realRpowENN delta 2 *
            (wz2PaperFullFiberIndices fine coarse parent).card =
          (wz2PaperFullFiberIndices fine coarse parent).card *
            (55296 * Kakeya.deltaTubeVolume 1) *
            Kakeya.realRpowENN delta 2
      ring

end PureWZ2Prop62PacketCellInput

end Kakeya.Assouad

end
