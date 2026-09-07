import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.SelectedScaleFactoring
import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.SelectedScaleParameters
import MyLeanRepo.Kakeya.Streamlined.Statements

/-!
# Lift a selected envelope subfamily back to tube blocks

The generic GWZ factoring theorem may retain only a subfamily of the certified
convex envelopes.  This module selects exactly the corresponding fixed
four-tube blocks and lifts the retained envelope shading to those tubes.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Assouad

namespace SelectedScaleFourBlockData

/-- Flatten the four tube blocks corresponding to one envelope subfamily. -/
def selectedEnvelopeBlockFamily
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (data : SelectedScaleFourBlockData fine rho)
    (S : Kakeya.Streamlined.Subfamily data.envelopeFamily) :
    Kakeya.Streamlined.TubeFamily rho :=
  flattenFixedBlocks
    (fun j => data.block (S.embedding j))
    (fun j => data.block_card (S.embedding j))

/-- A lifted block tube is the corresponding tube in the ambient flattened family. -/
lemma selectedEnvelopeBlockFamily_tube_eq_coarse
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (data : SelectedScaleFourBlockData fine rho)
    (S : Kakeya.Streamlined.Subfamily data.envelopeFamily)
    (q : Fin (data.selectedEnvelopeBlockFamily S).card) :
    (data.selectedEnvelopeBlockFamily S).tube q =
      data.coarse.tube
        (finProdFinEquiv
          (S.embedding (fixedBlockIndex q), fixedBlockSlot q)) := by
  change
    ((flattenFixedBlocks
      (fun j => data.block (S.embedding j))
      (fun j => data.block_card (S.embedding j))).tube q) =
      ((flattenFixedBlocks data.block data.block_card).tube
        (finProdFinEquiv
          (S.embedding (fixedBlockIndex q), fixedBlockSlot q)))
  rw [flattenFixedBlocks_tube_block_slot, flattenFixedBlocks_tube]

/-- Intersect each retained envelope shade with each tube in its block. -/
def selectedEnvelopeBlockShading
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (data : SelectedScaleFourBlockData fine rho)
    (S : Kakeya.Streamlined.Subfamily data.envelopeFamily)
    (Z : Kakeya.Streamlined.Shading S.family) :
    Kakeya.Streamlined.TubeShading
      (data.selectedEnvelopeBlockFamily S) where
  carrier q :=
    Z.carrier (fixedBlockIndex q) ∩
      ((data.selectedEnvelopeBlockFamily S).tube q).carrier
  measurable_carrier q :=
    (Z.measurable_carrier (fixedBlockIndex q)).inter
      Metric.isClosed_cthickening.measurableSet
  subset_body q := Set.inter_subset_right

/-- One retained envelope shade is the union of its four lifted tube shades. -/
lemma selectedEnvelopeBlockShading_decomposition
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (data : SelectedScaleFourBlockData fine rho)
    (S : Kakeya.Streamlined.Subfamily data.envelopeFamily)
    (Z : Kakeya.Streamlined.Shading S.family)
    (j : Fin S.family.card) :
    Z.carrier j =
      ⋃ k : Fin 4,
        (data.selectedEnvelopeBlockShading S Z).carrier
          (finProdFinEquiv (j, k)) := by
  ext point
  constructor
  · intro hpoint
    have hbody : point ∈ (S.family.body j).carrier :=
      Z.subset_body j hpoint
    have henvelope :
        point ∈ (data.envelope (S.embedding j)).carrier := by
      have hcarrier := S.carrier_eq j
      change
        (S.family.body j).carrier =
          (data.envelope (S.embedding j)).carrier at hcarrier
      rw [← hcarrier]
      exact hbody
    have hblock :
        point ∈ (data.block (S.embedding j)).toBodyFamily.union := by
      rw [← data.envelope_eq_union]
      exact henvelope
    rcases hblock with ⟨k, hk⟩
    change point ∈ ((data.block (S.embedding j)).tube k).carrier at hk
    let slot : Fin 4 :=
      Fin.cast (data.block_card (S.embedding j)) k
    refine Set.mem_iUnion.mpr ⟨slot, ?_⟩
    change
      point ∈
        Z.carrier (fixedBlockIndex (finProdFinEquiv (j, slot))) ∩
          ((data.selectedEnvelopeBlockFamily S).tube
            (finProdFinEquiv (j, slot))).carrier
    rw [fixedBlockIndex_finProdFinEquiv]
    refine ⟨hpoint, ?_⟩
    change point ∈
      ((flattenFixedBlocks
        (fun l => data.block (S.embedding l))
        (fun l => data.block_card (S.embedding l))).tube
          (finProdFinEquiv (j, slot))).carrier
    rw [flattenFixedBlocks_tube]
    simpa [slot] using hk
  · intro hpoint
    rcases Set.mem_iUnion.mp hpoint with ⟨k, hk⟩
    simpa using hk.1

/-- The lifted tube shading has exactly the retained envelope shaded union. -/
lemma selectedEnvelopeBlockShading_union_eq
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (data : SelectedScaleFourBlockData fine rho)
    (S : Kakeya.Streamlined.Subfamily data.envelopeFamily)
    (Z : Kakeya.Streamlined.Shading S.family) :
    (data.selectedEnvelopeBlockShading S Z).union = Z.union := by
  ext point
  constructor
  · rintro ⟨q, hq⟩
    exact ⟨fixedBlockIndex q, hq.1⟩
  · rintro ⟨j, hj⟩
    have hdecomp :=
      Set.ext_iff.mp
        (data.selectedEnvelopeBlockShading_decomposition S Z j)
        point
    have hunion : point ∈
        ⋃ k : Fin 4,
          (data.selectedEnvelopeBlockShading S Z).carrier
            (finProdFinEquiv (j, k)) :=
      hdecomp.mp hj
    rcases Set.mem_iUnion.mp hunion with ⟨k, hk⟩
    exact ⟨finProdFinEquiv (j, k), hk⟩

/--
An induced retained envelope shading, after lifting to its four tube blocks,
stays in the prescribed thickening of the original fine shaded union.
-/
lemma selectedEnvelopeBlockShading_union_subset_thickening
    {delta rho r : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (data : SelectedScaleFourBlockData fine rho)
    (Y : Kakeya.Streamlined.TubeShading fine)
    (R :
      Kakeya.Streamlined.FactoringRefinement
        data.toEnvelopeFactoring Y)
    (hInduced :
      R.factoring.IsInducedSubshading
        R.fineRefinement.shading R.coarseShading r) :
    (data.selectedEnvelopeBlockShading
        R.coarseSubfamily R.coarseShading).union ⊆
      Metric.cthickening r Y.union := by
  rw [data.selectedEnvelopeBlockShading_union_eq]
  intro point hpoint
  rcases hpoint with ⟨j, hj⟩
  have hthick := (hInduced j hj).2
  apply Metric.cthickening_subset_of_subset r _ hthick
  intro x hx
  rcases hx with ⟨i, _hparent, hxi⟩
  exact
    ⟨R.fineRefinement.subfamily.embedding i,
      R.fineRefinement.shading_subset i hxi⟩

/-- Lifting to tube blocks cannot lose shaded mass. -/
lemma selectedEnvelopeBlockShading_mass_lower
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (data : SelectedScaleFourBlockData fine rho)
    (S : Kakeya.Streamlined.Subfamily data.envelopeFamily)
    (Z : Kakeya.Streamlined.Shading S.family) :
    Z.mass ≤ (data.selectedEnvelopeBlockShading S Z).mass := by
  have hblock :
      ∀ j : Fin S.family.card,
        volume (Z.carrier j) ≤
          ∑ k : Fin 4,
            volume
              ((data.selectedEnvelopeBlockShading S Z).carrier
                (finProdFinEquiv (j, k))) := by
    intro j
    rw [data.selectedEnvelopeBlockShading_decomposition S Z j]
    exact MeasureTheory.measure_iUnion_fintype_le
      volume
      (fun k : Fin 4 =>
        (data.selectedEnvelopeBlockShading S Z).carrier
          (finProdFinEquiv (j, k)))
  calc
    Z.mass ≤
        ∑ j : Fin S.family.card, ∑ k : Fin 4,
          volume
            ((data.selectedEnvelopeBlockShading S Z).carrier
              (finProdFinEquiv (j, k))) :=
      Finset.sum_le_sum fun j _ => hblock j
    _ = ∑ pair : Fin S.family.card × Fin 4,
          volume
            ((data.selectedEnvelopeBlockShading S Z).carrier
              (finProdFinEquiv pair)) := by
      rw [Fintype.sum_prod_type]
    _ = (data.selectedEnvelopeBlockShading S Z).mass := by
      exact Equiv.sum_comp finProdFinEquiv
        (fun q =>
          volume ((data.selectedEnvelopeBlockShading S Z).carrier q))

/-- Lifting to four tubes costs at most the block-cardinality factor four. -/
lemma selectedEnvelopeBlockShading_mass_upper
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (data : SelectedScaleFourBlockData fine rho)
    (S : Kakeya.Streamlined.Subfamily data.envelopeFamily)
    (Z : Kakeya.Streamlined.Shading S.family) :
    (data.selectedEnvelopeBlockShading S Z).mass ≤
      (4 : ENNReal) * Z.mass := by
  change
    (∑ q : Fin (S.family.card * 4),
      volume
        ((data.selectedEnvelopeBlockShading S Z).carrier q)) ≤
      (4 : ENNReal) * ∑ j : Fin S.family.card, volume (Z.carrier j)
  calc
    (∑ q : Fin (S.family.card * 4),
        volume ((data.selectedEnvelopeBlockShading S Z).carrier q)) =
        ∑ pair : Fin S.family.card × Fin 4,
          volume
            ((data.selectedEnvelopeBlockShading S Z).carrier
              (finProdFinEquiv pair)) := by
      exact (Equiv.sum_comp finProdFinEquiv
        (fun q =>
          volume ((data.selectedEnvelopeBlockShading S Z).carrier q))).symm
    _ = ∑ j : Fin S.family.card, ∑ k : Fin 4,
          volume
            ((data.selectedEnvelopeBlockShading S Z).carrier
              (finProdFinEquiv (j, k))) := by
      rw [Fintype.sum_prod_type]
    _ ≤ ∑ j : Fin S.family.card, ∑ _k : Fin 4,
          volume (Z.carrier j) := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      apply MeasureTheory.measure_mono
      intro point hpoint
      simpa using hpoint.1
    _ = ∑ j : Fin S.family.card,
          (4 : ENNReal) * volume (Z.carrier j) := by
      simp
    _ = (4 : ENNReal) * ∑ j : Fin S.family.card,
          volume (Z.carrier j) := by
      rw [Finset.mul_sum]

/-- The lifted tube family's nominal mass is at most four envelope masses. -/
lemma selectedEnvelopeBlockFamily_mass_le_four_mul
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (data : SelectedScaleFourBlockData fine rho)
    (S : Kakeya.Streamlined.Subfamily data.envelopeFamily) :
    (data.selectedEnvelopeBlockFamily S).toBodyFamily.mass ≤
      (4 : ENNReal) * S.family.mass := by
  change
    (∑ q : Fin (S.family.card * 4),
      volume
        ((data.selectedEnvelopeBlockFamily S).tube q).carrier) ≤
      (4 : ENNReal) *
        ∑ j : Fin S.family.card, volume (S.family.body j).carrier
  have hmember :
      ∀ j : Fin S.family.card, ∀ k : Fin 4,
        volume
            ((data.selectedEnvelopeBlockFamily S).tube
              (finProdFinEquiv (j, k))).carrier ≤
          volume (S.family.body j).carrier := by
    intro j k
    apply MeasureTheory.measure_mono
    have hblock :
        ((data.block (S.embedding j)).tube
          (Fin.cast (data.block_card (S.embedding j)).symm k)).carrier ⊆
          (data.block (S.embedding j)).toBodyFamily.union := by
      intro point hpoint
      exact ⟨Fin.cast (data.block_card (S.embedding j)).symm k, hpoint⟩
    have henvelope :
        (data.block (S.embedding j)).toBodyFamily.union ⊆
          (data.envelope (S.embedding j)).carrier := by
      rw [data.envelope_eq_union]
    have hselected :
        (data.envelope (S.embedding j)).carrier =
          (S.family.body j).carrier := by
      exact (S.carrier_eq j).symm
    change
      ((flattenFixedBlocks
        (fun l => data.block (S.embedding l))
        (fun l => data.block_card (S.embedding l))).tube
          (finProdFinEquiv (j, k))).carrier ⊆
        (S.family.body j).carrier
    rw [flattenFixedBlocks_tube]
    rw [← hselected]
    exact hblock.trans henvelope
  calc
    (∑ q : Fin (S.family.card * 4),
        volume ((data.selectedEnvelopeBlockFamily S).tube q).carrier) =
        ∑ pair : Fin S.family.card × Fin 4,
          volume
            ((data.selectedEnvelopeBlockFamily S).tube
              (finProdFinEquiv pair)).carrier := by
      exact (Equiv.sum_comp finProdFinEquiv
        (fun q =>
          volume ((data.selectedEnvelopeBlockFamily S).tube q).carrier)).symm
    _ = ∑ j : Fin S.family.card, ∑ k : Fin 4,
          volume
            ((data.selectedEnvelopeBlockFamily S).tube
              (finProdFinEquiv (j, k))).carrier := by
      rw [Fintype.sum_prod_type]
    _ ≤ ∑ j : Fin S.family.card, ∑ _k : Fin 4,
          volume (S.family.body j).carrier := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      exact hmember j k
    _ = ∑ j : Fin S.family.card,
          (4 : ENNReal) * volume (S.family.body j).carrier := by
      simp
    _ = (4 : ENNReal) *
        ∑ j : Fin S.family.card, volume (S.family.body j).carrier := by
      rw [Finset.mul_sum]

/-- Transfer a cancellation-free envelope density inequality to lifted tubes. -/
lemma selectedEnvelopeBlockShading_density_transfer
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (data : SelectedScaleFourBlockData fine rho)
    (S : Kakeya.Streamlined.Subfamily data.envelopeFamily)
    (Z : Kakeya.Streamlined.Shading S.family)
    (lambda L : ENNReal)
    (hdensity : lambda * S.family.mass ≤ L * Z.mass) :
    lambda *
        (data.selectedEnvelopeBlockFamily S).toBodyFamily.mass ≤
      (4 * L) * (data.selectedEnvelopeBlockShading S Z).mass := by
  calc
    lambda * (data.selectedEnvelopeBlockFamily S).toBodyFamily.mass
        ≤ lambda * ((4 : ENNReal) * S.family.mass) := by
      gcongr
      exact data.selectedEnvelopeBlockFamily_mass_le_four_mul S
    _ = 4 * (lambda * S.family.mass) := by ring
    _ ≤ 4 * (L * Z.mass) := by gcongr
    _ ≤ 4 * (L *
        (data.selectedEnvelopeBlockShading S Z).mass) := by
      gcongr
      exact data.selectedEnvelopeBlockShading_mass_lower S Z
    _ = (4 * L) *
        (data.selectedEnvelopeBlockShading S Z).mass := by ring

/-- The lifted block family inherits the source vertical chart. -/
lemma selectedEnvelopeBlockFamily_isInVerticalChart
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (data : SelectedScaleFourBlockData fine rho)
    (S : Kakeya.Streamlined.Subfamily data.envelopeFamily)
    (hvertical : IsInVerticalChart fine) :
    IsInVerticalChart (data.selectedEnvelopeBlockFamily S) := by
  intro q
  change
    (1 / 2 : ℝ) ≤
      |((flattenFixedBlocks
        (fun j => data.block (S.embedding j))
        (fun j => data.block_card (S.embedding j))).tube q).direction 2|
  rw [flattenFixedBlocks_tube_block_slot]
  rw [data.block_vertical]
  exact hvertical
    (data.selected.equivFin.symm
      (S.embedding (fixedBlockIndex q))).1

/-- The lifted family keeps the source representative supporting line. -/
lemma selectedEnvelopeBlockFamily_axis
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (data : SelectedScaleFourBlockData fine rho)
    (S : Kakeya.Streamlined.Subfamily data.envelopeFamily)
    (q : Fin (data.selectedEnvelopeBlockFamily S).card) :
    tubeAxisLine ((data.selectedEnvelopeBlockFamily S).tube q) =
      tubeAxisLine
        (fine.tube
          (data.selected.equivFin.symm
            (S.embedding (fixedBlockIndex q))).1) := by
  change
    tubeAxisLine
      ((flattenFixedBlocks
        (fun j => data.block (S.embedding j))
        (fun j => data.block_card (S.embedding j))).tube q) =
      _
  rw [flattenFixedBlocks_tube_block_slot]
  exact data.block_axis _ _

/-- Every lifted block member has its selected source representative's line parameters. -/
lemma selectedEnvelopeBlockFamily_tubeParams_eq_representative
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (data : SelectedScaleFourBlockData fine rho)
    (S : Kakeya.Streamlined.Subfamily data.envelopeFamily)
    (hsourceVertical : IsInVerticalChart fine)
    (q : Fin (data.selectedEnvelopeBlockFamily S).card) :
    tubeParamsOfTube ((data.selectedEnvelopeBlockFamily S).tube q) =
      tubeParams
        (F := fine)
        (data.selected.equivFin.symm
          (S.embedding (fixedBlockIndex q))).1 := by
  rw [data.selectedEnvelopeBlockFamily_tube_eq_coarse S q]
  have h := data.coarse_tubeParams_eq_representative hsourceVertical
    (finProdFinEquiv
      (S.embedding (fixedBlockIndex q), fixedBlockSlot q))
  simpa [fixedBlockIndex_finProdFinEquiv] using h

/-- The inherited source parameter box remains valid after envelope selection. -/
lemma selectedEnvelopeBlockFamily_tubeParams_bounds
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (data : SelectedScaleFourBlockData fine rho)
    (S : Kakeya.Streamlined.Subfamily data.envelopeFamily)
    (hbase : HasBoundedBase fine 4)
    (hvertical : IsInVerticalChart fine)
    (q : Fin (data.selectedEnvelopeBlockFamily S).card) :
    |(tubeParamsOfTube ((data.selectedEnvelopeBlockFamily S).tube q)).a| ≤ 12 ∧
      |(tubeParamsOfTube ((data.selectedEnvelopeBlockFamily S).tube q)).b| ≤ 12 ∧
      |(tubeParamsOfTube ((data.selectedEnvelopeBlockFamily S).tube q)).c| ≤ 2 ∧
      |(tubeParamsOfTube ((data.selectedEnvelopeBlockFamily S).tube q)).d| ≤ 2 := by
  rw [data.selectedEnvelopeBlockFamily_tube_eq_coarse S q]
  exact data.coarse_tubeParams_bounds hbase hvertical
    (finProdFinEquiv
      (S.embedding (fixedBlockIndex q), fixedBlockSlot q))

end SelectedScaleFourBlockData

end Kakeya.Assouad
