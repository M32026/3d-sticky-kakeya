import MyLeanRepo.Kakeya.Assouad.AnisotropicRescaling.FixedBlockFamily

/-!
# Selected-scale convex-parent factoring

The four consecutive tube members in each selected block have one certified
convex envelope.  This module exposes those envelopes as a body family and
constructs the genuine single-parent factoring required by the GWZ
induced-shading density theorem.  The flattened tube family remains available
separately for the twisted-projection geometry.
-/

noncomputable section

namespace Kakeya.Assouad

namespace SelectedScaleFourBlockData

/-- The certified convex envelope attached to each selected representative. -/
def envelopeFamily
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (data : SelectedScaleFourBlockData fine rho) :
    Kakeya.Streamlined.BodyFamily where
  card := data.selected.card
  body := data.envelope

/-- The source family genuinely factors through the certified block envelopes. -/
def toEnvelopeFactoring
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (data : SelectedScaleFourBlockData fine rho) :
    Kakeya.Streamlined.Factoring
      fine.toBodyFamily data.envelopeFamily where
  parent := data.parent
  parent_surjective := data.parent_surjective
  contained := data.cover

/-- Every certified envelope is measurable. -/
lemma envelopeFamily_isMeasurable
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (data : SelectedScaleFourBlockData fine rho) :
    data.envelopeFamily.IsMeasurable :=
  data.envelope_measurable

/-- Every certified envelope is convex. -/
lemma envelopeFamily_isConvex
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (data : SelectedScaleFourBlockData fine rho) :
    data.envelopeFamily.IsConvex :=
  data.envelope_convex

/-- The certified envelopes have common `rho × rho × 4` dimensions. -/
lemma envelopeFamily_hasComparableDimensions
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (data : SelectedScaleFourBlockData fine rho) :
    data.envelopeFamily.HasComparableDimensions rho rho 4 3 :=
  data.envelope_dimensions

/-- The four indexed tubes in each block cost at most four envelope volumes. -/
lemma coarse_mass_le_four_mul_envelope_mass
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (data : SelectedScaleFourBlockData fine rho) :
    data.coarse.toBodyFamily.mass ≤
      (4 : ENNReal) * data.envelopeFamily.mass := by
  change
    (∑ q : Fin (data.selected.card * 4),
      MeasureTheory.volume
        ((flattenFixedBlocks data.block data.block_card).tube q).carrier) ≤
      (4 : ENNReal) *
        ∑ j : Fin data.selected.card,
          MeasureTheory.volume (data.envelope j).carrier
  have hmember :
      ∀ j : Fin data.selected.card, ∀ k : Fin 4,
        MeasureTheory.volume
            ((flattenFixedBlocks data.block data.block_card).tube
              (finProdFinEquiv (j, k))).carrier ≤
          MeasureTheory.volume (data.envelope j).carrier := by
    intro j k
    apply MeasureTheory.measure_mono
    have hsubset :
        ((data.block j).tube
          (Fin.cast (data.block_card j).symm k)).carrier ⊆
          (data.block j).toBodyFamily.union := by
      intro point hpoint
      exact ⟨Fin.cast (data.block_card j).symm k, hpoint⟩
    have henvelope :
        (data.block j).toBodyFamily.union ⊆
          (data.envelope j).carrier := by
      rw [data.envelope_eq_union]
    change
      (data.coarse.tube (finProdFinEquiv (j, k))).carrier ⊆
        (data.envelope j).carrier
    change
      ((flattenFixedBlocks data.block data.block_card).tube
        (finProdFinEquiv (j, k))).carrier ⊆
        (data.envelope j).carrier
    rw [flattenFixedBlocks_tube]
    exact hsubset.trans henvelope
  calc
    (∑ q : Fin (data.selected.card * 4),
        MeasureTheory.volume
          ((flattenFixedBlocks data.block data.block_card).tube q).carrier) =
        ∑ pair : Fin data.selected.card × Fin 4,
          MeasureTheory.volume
            ((flattenFixedBlocks data.block data.block_card).tube
              (finProdFinEquiv pair)).carrier := by
      exact (Equiv.sum_comp finProdFinEquiv
        (fun q =>
          MeasureTheory.volume
            ((flattenFixedBlocks data.block data.block_card).tube q).carrier)).symm
    _ = ∑ j : Fin data.selected.card, ∑ k : Fin 4,
          MeasureTheory.volume
            ((flattenFixedBlocks data.block data.block_card).tube
              (finProdFinEquiv (j, k))).carrier := by
      rw [Fintype.sum_prod_type]
    _ ≤ ∑ j : Fin data.selected.card, ∑ _k : Fin 4,
          MeasureTheory.volume (data.envelope j).carrier := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      exact hmember j k
    _ = ∑ j : Fin data.selected.card,
          (4 : ENNReal) *
            MeasureTheory.volume (data.envelope j).carrier := by
      simp
    _ = (4 : ENNReal) *
        ∑ j : Fin data.selected.card,
          MeasureTheory.volume (data.envelope j).carrier := by
      rw [Finset.mul_sum]

/--
The exact envelope shading induced by the single-parent factoring.

No slope-window clipping is performed here: this is precisely the exact
shading interface consumed by the GWZ density theorem.
-/
def exactEnvelopeInducedShading
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (data : SelectedScaleFourBlockData fine rho)
    (Y : Kakeya.Streamlined.TubeShading fine)
    (r : ℝ) :
    Kakeya.Streamlined.Shading data.envelopeFamily where
  carrier j :=
    (data.envelope j).carrier ∩
      Metric.cthickening r
        {x | ∃ i : Fin fine.card,
          data.parent i = j ∧ x ∈ Y.carrier i}
  measurable_carrier j :=
    (data.envelope_measurable j).inter
      Metric.isClosed_cthickening.measurableSet
  subset_body j := Set.inter_subset_left

/-- The constructed envelope shading is exact for the certified factoring. -/
lemma exactEnvelopeInducedShading_isExact
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (data : SelectedScaleFourBlockData fine rho)
    (Y : Kakeya.Streamlined.TubeShading fine)
    (r : ℝ) :
    data.toEnvelopeFactoring.IsExactInducedShading
      Y (data.exactEnvelopeInducedShading Y r) r := by
  intro j
  rfl

/--
Unwindowed induced shading on the flattened four-tube family.

This uses the block relation but does not clip to the slope window.  It is the
tube-valued object whose mass can receive the envelope density estimate.
-/
def exactTubeRelationInducedShading
    {delta rho : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (data : SelectedScaleFourBlockData fine rho)
    (Y : Kakeya.Streamlined.TubeShading fine)
    (r : ℝ) :
    Kakeya.Streamlined.TubeShading data.coarse where
  carrier q :=
    (data.coarse.tube q).carrier ∩
      Metric.cthickening r
        {x | ∃ i : Fin fine.card,
          data.relation i q ∧ x ∈ Y.carrier i}
  measurable_carrier q :=
    Metric.isClosed_cthickening.measurableSet.inter
      Metric.isClosed_cthickening.measurableSet
  subset_body q := Set.inter_subset_left

/--
The unwindowed relation-induced tube shading remains in the prescribed
thickening of the original fine shaded union.
-/
lemma exactTubeRelationInducedShading_union_subset_thickening
    {delta rho r : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (data : SelectedScaleFourBlockData fine rho)
    (Y : Kakeya.Streamlined.TubeShading fine) :
    (data.exactTubeRelationInducedShading Y r).union ⊆
      Metric.cthickening r Y.union := by
  intro point hpoint
  rcases hpoint with ⟨q, hq⟩
  have hthick := hq.2
  apply Metric.cthickening_subset_of_subset r _ hthick
  intro x hx
  rcases hx with ⟨i, _hrelation, hxi⟩
  exact ⟨i, hxi⟩

/--
One exact envelope shaded piece is covered by the four corresponding exact
tube shaded pieces.
-/
lemma exactEnvelopeInducedShading_carrier_subset_block
    {delta rho r : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (data : SelectedScaleFourBlockData fine rho)
    (Y : Kakeya.Streamlined.TubeShading fine)
    (j : Fin data.selected.card) :
    (data.exactEnvelopeInducedShading Y r).carrier j ⊆
      ⋃ k : Fin 4,
        (data.exactTubeRelationInducedShading Y r).carrier
          (finProdFinEquiv (j, k)) := by
  intro point hpoint
  have hblock :
      point ∈ (data.block j).toBodyFamily.union := by
    rw [← data.envelope_eq_union]
    exact hpoint.1
  rcases hblock with ⟨k, hk⟩
  change point ∈ ((data.block j).tube k).carrier at hk
  let slot : Fin 4 := Fin.cast (data.block_card j) k
  refine Set.mem_iUnion.mpr ⟨slot, ?_⟩
  have hcoarse :
      point ∈
        (data.coarse.tube (finProdFinEquiv (j, slot))).carrier := by
    change point ∈
      ((flattenFixedBlocks data.block data.block_card).tube
        (finProdFinEquiv (j, slot))).carrier
    rw [flattenFixedBlocks_tube]
    simpa [slot] using hk
  refine ⟨hcoarse, ?_⟩
  apply Metric.cthickening_subset_of_subset r _ hpoint.2
  intro x hx
  rcases hx with ⟨i, hparent, hxi⟩
  refine ⟨i, ?_, hxi⟩
  change fixedBlockIndex (finProdFinEquiv (j, slot)) = data.parent i
  rw [fixedBlockIndex_finProdFinEquiv, hparent]

/-- The envelope shaded mass is bounded by the flattened tube shaded mass. -/
lemma exactEnvelopeInducedShading_mass_le_tube_mass
    {delta rho r : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    (data : SelectedScaleFourBlockData fine rho)
    (Y : Kakeya.Streamlined.TubeShading fine) :
    (data.exactEnvelopeInducedShading Y r).mass ≤
      (data.exactTubeRelationInducedShading Y r).mass := by
  have hblock :
      ∀ j : Fin data.selected.card,
        MeasureTheory.volume
            ((data.exactEnvelopeInducedShading Y r).carrier j) ≤
          ∑ k : Fin 4,
            MeasureTheory.volume
              ((data.exactTubeRelationInducedShading Y r).carrier
                (finProdFinEquiv (j, k))) := by
    intro j
    exact (MeasureTheory.measure_mono
      (data.exactEnvelopeInducedShading_carrier_subset_block Y j)).trans
        (MeasureTheory.measure_iUnion_fintype_le
          MeasureTheory.volume
          (fun k : Fin 4 =>
            (data.exactTubeRelationInducedShading Y r).carrier
              (finProdFinEquiv (j, k))))
  calc
    (data.exactEnvelopeInducedShading Y r).mass
        ≤ ∑ j : Fin data.selected.card, ∑ k : Fin 4,
            MeasureTheory.volume
              ((data.exactTubeRelationInducedShading Y r).carrier
                (finProdFinEquiv (j, k))) :=
      Finset.sum_le_sum fun j _ => hblock j
    _ = ∑ pair : Fin data.selected.card × Fin 4,
          MeasureTheory.volume
            ((data.exactTubeRelationInducedShading Y r).carrier
              (finProdFinEquiv pair)) := by
      rw [Fintype.sum_prod_type]
    _ = (data.exactTubeRelationInducedShading Y r).mass := by
      exact Equiv.sum_comp finProdFinEquiv
        (fun q =>
          MeasureTheory.volume
            ((data.exactTubeRelationInducedShading Y r).carrier q))

end SelectedScaleFourBlockData

end Kakeya.Assouad
