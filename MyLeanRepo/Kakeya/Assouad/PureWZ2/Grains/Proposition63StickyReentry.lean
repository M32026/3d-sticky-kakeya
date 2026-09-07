import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63Lemma44
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.DenseCubicalizationRestriction
import MyLeanRepo.Kakeya.Assouad.PureWZ2.DenseCubicalTrace
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Node4DenseCubicalTrace
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63ChartNormalization
import MyLeanRepo.Kakeya.Assouad.PureWZ2.NormalizationCriticalWitnessAdapter
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PureExternalWeightRegularization
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PureNearbyToTopLevelCWA
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Provenance-preserving re-entry into Proposition 6.2

The second invocation of Proposition 6.2 in the proof of Proposition 6.3 is
dependent: its input is the actual whole-cell refinement produced by the
preceding Lemma 4.3 step.  This file records the exact adapter needed by the
frozen cropped `prop: sticky` interface.

The adapter deliberately does not identify a cubical saturation with the
dense cubicalization.  Instead it uses the ordinary trace inside the retained
whole cells.  Positivity on every retained tube and the aggregate trace-mass
bound are explicit hypotheses; these are the quantitative facts that the
paper's refinement and loss hierarchy must supply.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set

/-- Node 4 compatibility adapter from the ordinary witness retained by the
rescaled-fiber API to the extremal configuration used by the grain route. -/
noncomputable def criticalRescaledFiberToExtremalConfiguration
    {delta rho sigma loss : ℝ}
    {fine : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading fine}
    {parentTube : Kakeya.DeltaTube rho}
    {hrho : 0 < rho}
    (witness : PureWZ2CriticalRescaledFiberWitness
      (sigma := sigma) (loss := loss) sourceShading parentTube hrho) :
    PureWZ2ExtremalConfiguration sigma loss (delta / rho) where
  family := witness.ordinaryFamily
  shading := witness.ordinaryShading
  extremal :=
    { delta_pos := witness.output.extremal.delta_pos
      delta_le_one := witness.output.extremal.delta_le_one
      nonempty := witness.ordinary_nonempty
      cwa_nearby_scales := witness.ordinary_cwa
      dense := witness.ordinary_dense
      volume_upper := by
        calc
          volume witness.ordinaryShading.union ≤
              volume witness.output.literalShading.targetShading.union :=
            measure_mono witness.ordinary_union_subset_target
          _ = volume
              (witness.output.rescalingCertificate.publicShading
                witness.output.literalShading.targetShading).union := by
            rw [witness.output.rescalingCertificate.publicShading_union_eq]
          _ ≤ Kakeya.realRpowENN (delta / rho) (sigma - loss) :=
            witness.output.extremal.volume_upper }

/-- The identity tube subfamily, used when a second normalization changes
only the shading and not the indexed family. -/
def proposition63IdentitySubfamily
    {delta : ℝ} (family : Kakeya.Streamlined.TubeFamily delta) :
    Kakeya.Streamlined.TubeSubfamily family where
  family := family
  embedding := (Equiv.refl (Fin family.card)).toEmbedding
  tube_eq := fun _ => rfl

@[simp] lemma proposition63IdentitySubfamily_embedding
    {delta : ℝ} (family : Kakeya.Streamlined.TubeFamily delta)
    (index : Fin family.card) :
    (proposition63IdentitySubfamily family).embedding index = index :=
  rfl

/-- The index equivalence associated to the identity subfamily.  It is named
explicitly to keep dependent record projections reducible. -/
def proposition63IdentityIndexEquiv
    {delta : ℝ} (family : Kakeya.Streamlined.TubeFamily delta) :
    Fin (proposition63IdentitySubfamily family).family.card ≃
      Fin family.card where
  toFun index := ⟨index.1, by
    simpa [proposition63IdentitySubfamily] using index.2⟩
  invFun index := ⟨index.1, by
    simpa [proposition63IdentitySubfamily] using index.2⟩
  left_inv index := Fin.ext rfl
  right_inv index := Fin.ext rfl

@[simp] lemma proposition63IdentityIndexEquiv_apply
    {delta : ℝ} (family : Kakeya.Streamlined.TubeFamily delta)
    (index : Fin (proposition63IdentitySubfamily family).family.card) :
    proposition63IdentityIndexEquiv family index =
      ⟨index.1, by simpa [proposition63IdentitySubfamily] using index.2⟩ :=
  rfl

/-- The ordinary part of a cropped whole-cell shading.  This remains an
ordinary tube shading because the first factor is ordinary. -/
def proposition63OrdinaryTrace
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (ordinary : Kakeya.Streamlined.TubeShading family)
    (cropped : WZ1PaperTubeShading family) :
    Kakeya.Streamlined.TubeShading family where
  carrier index := ordinary.carrier index ∩ cropped.carrier index
  measurable_carrier index :=
    (ordinary.measurable_carrier index).inter
      (cropped.measurable_carrier index)
  subset_body index := Set.inter_subset_left.trans
    (ordinary.subset_body index)

@[simp] lemma proposition63OrdinaryTrace_carrier
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (ordinary : Kakeya.Streamlined.TubeShading family)
    (cropped : WZ1PaperTubeShading family)
    (index : Fin family.card) :
    (proposition63OrdinaryTrace ordinary cropped).carrier index =
      ordinary.carrier index ∩ cropped.carrier index :=
  rfl

/-- Ordinary trace after selecting a genuine tube subfamily. -/
def proposition63SubfamilyOrdinaryTrace
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (ordinary : Kakeya.Streamlined.TubeShading family)
    (selected : Kakeya.Streamlined.TubeSubfamily family)
    (cropped : WZ1PaperTubeShading selected.family) :
    Kakeya.Streamlined.TubeShading selected.family where
  carrier index :=
    ordinary.carrier (selected.embedding index) ∩ cropped.carrier index
  measurable_carrier index :=
    (ordinary.measurable_carrier
      (selected.embedding index)).inter
        (cropped.measurable_carrier index)
  subset_body index := by
    intro point hpoint
    have hbody :=
      ordinary.subset_body (selected.embedding index) hpoint.1
    change point ∈ (selected.family.tube index).carrier
    rw [selected.tube_eq index]
    exact hbody

@[simp] lemma proposition63SubfamilyOrdinaryTrace_carrier
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (ordinary : Kakeya.Streamlined.TubeShading family)
    (selected : Kakeya.Streamlined.TubeSubfamily family)
    (cropped : WZ1PaperTubeShading selected.family)
    (index : Fin selected.family.card) :
    (proposition63SubfamilyOrdinaryTrace
      ordinary selected cropped).carrier index =
      ordinary.carrier (selected.embedding index) ∩
        cropped.carrier index :=
  rfl

/-- The indices on which the actual ordinary trace of a cropped refinement
has positive volume.  This is the canonical whole-tube deletion used before
the second Proposition 6.2 call. -/
def proposition63PositiveTraceIndices
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (ordinary : Kakeya.Streamlined.TubeShading family)
    (cropped : WZ1PaperTubeShading family) :
    Finset (Fin family.card) :=
  Finset.univ.filter fun index =>
    volume ((proposition63OrdinaryTrace ordinary cropped).carrier index) ≠ 0

/-- Delete exactly the tubes whose ordinary trace has zero volume. -/
def proposition63PositiveTraceSubfamily
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (ordinary : Kakeya.Streamlined.TubeShading family)
    (cropped : WZ1PaperTubeShading family) :
    Kakeya.Streamlined.TubeSubfamily family :=
  Kakeya.Streamlined.TubeSubfamily.fromFinset family
    (proposition63PositiveTraceIndices ordinary cropped)

/-- Forget only the ordinary shaded set, keeping the same selected indices
and ordinary tube family. -/
def proposition63PositiveOrdinaryMassSubfamily
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (ordinary : Kakeya.Streamlined.TubeShading family) :
    Kakeya.Streamlined.TubeSubfamily family :=
  Kakeya.Streamlined.TubeSubfamily.fromFinset family
    (Finset.univ.filter fun index =>
      volume (ordinary.carrier index) ≠ 0)

lemma proposition63PositiveOrdinaryMass_volume_pos
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (ordinary : Kakeya.Streamlined.TubeShading family)
    (index : Fin
      (proposition63PositiveOrdinaryMassSubfamily ordinary).family.card) :
    0 < volume (ordinary.carrier
      ((proposition63PositiveOrdinaryMassSubfamily ordinary).embedding
        index)) := by
  apply bot_lt_iff_ne_bot.mpr
  exact
    (Finset.mem_filter.mp
      (Finset.orderEmbOfFin_mem
        (Finset.univ.filter fun source =>
          volume (ordinary.carrier source) ≠ 0) rfl index)).2

/-- Discarding zero-mass ordinary carriers preserves ordinary shaded mass. -/
lemma proposition63PositiveOrdinaryMass_mass_eq
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (ordinary : Kakeya.Streamlined.TubeShading family) :
    (Kakeya.Streamlined.TubeSubfamily.restrictShading
      (proposition63PositiveOrdinaryMassSubfamily ordinary) ordinary).mass =
      ordinary.mass := by
  let indices : Finset (Fin family.card) :=
    Finset.univ.filter fun index => volume (ordinary.carrier index) ≠ 0
  let equivalence : Fin indices.card ≃ indices :=
    (indices.orderIsoOfFin rfl).toEquiv
  change
    (∑ index : Fin indices.card,
      volume (ordinary.carrier (indices.orderEmbOfFin rfl index))) =
      ∑ index : Fin family.card, volume (ordinary.carrier index)
  calc
    (∑ index : Fin indices.card,
        volume (ordinary.carrier (indices.orderEmbOfFin rfl index))) =
        ∑ source : indices, volume (ordinary.carrier source.1) := by
      exact Fintype.sum_equiv equivalence
        (fun index : Fin indices.card =>
          volume (ordinary.carrier (indices.orderEmbOfFin rfl index)))
        (fun source : indices => volume (ordinary.carrier source.1))
        (fun _ => rfl)
    _ = ∑ source ∈ indices, volume (ordinary.carrier source) := by
      exact Finset.sum_coe_sort indices
        (fun source => volume (ordinary.carrier source))
    _ = ∑ source : Fin family.card, volume (ordinary.carrier source) := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro source _ hsource
      have hzero : ¬ volume (ordinary.carrier source) ≠ 0 := by
        simpa [indices] using hsource
      exact not_ne_iff.mp hzero

/-- Every positive-mass selected ordinary carrier is nonempty. -/
lemma proposition63PositiveOrdinaryMass_carrier_nonempty
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (ordinary : Kakeya.Streamlined.TubeShading family)
    (index : Fin
      (proposition63PositiveOrdinaryMassSubfamily ordinary).family.card) :
    (ordinary.carrier
      ((proposition63PositiveOrdinaryMassSubfamily ordinary).embedding
        index)).Nonempty := by
  apply Set.nonempty_iff_ne_empty.mpr
  intro hempty
  have hpositive := proposition63PositiveOrdinaryMass_volume_pos ordinary index
  rw [hempty, measure_empty] at hpositive
  exact (lt_irrefl 0) hpositive

/-- A positive trace family is in particular a positive ordinary-mass
subfamily.  This explicit inclusion is used to transport finite nearby-CWA
regularization to the exact trace support. -/
def proposition63PositiveTraceToPositiveOrdinaryEmbedding
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (ordinary : Kakeya.Streamlined.TubeShading family)
    (cropped : WZ1PaperTubeShading family) :
    Fin (proposition63PositiveTraceSubfamily ordinary cropped).family.card ↪
      Fin (proposition63PositiveOrdinaryMassSubfamily ordinary).family.card :=
  Kakeya.Streamlined.TubeSubfamily.fromFinsetInclusion family
    (proposition63PositiveTraceIndices ordinary cropped)
    (Finset.univ.filter fun index => volume (ordinary.carrier index) ≠ 0)
    (by
      intro index hindex
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      have htrace :
          volume ((proposition63OrdinaryTrace ordinary cropped).carrier
            index) ≠ 0 := (Finset.mem_filter.mp hindex).2
      intro hzero
      apply htrace
      have hsubset :
          (proposition63OrdinaryTrace ordinary cropped).carrier index ⊆
            ordinary.carrier index := Set.inter_subset_left
      exact measure_mono_null hsubset hzero)

lemma proposition63PositiveTraceToPositiveOrdinaryEmbedding_ambient
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (ordinary : Kakeya.Streamlined.TubeShading family)
    (cropped : WZ1PaperTubeShading family)
    (index : Fin
      (proposition63PositiveTraceSubfamily ordinary cropped).family.card) :
    (proposition63PositiveOrdinaryMassSubfamily ordinary).embedding
        (proposition63PositiveTraceToPositiveOrdinaryEmbedding
          ordinary cropped index) =
      (proposition63PositiveTraceSubfamily ordinary cropped).embedding
        index := by
  apply Kakeya.Streamlined.TubeSubfamily.fromFinsetInclusion_ambient

/-- Restrict the actual Lemma 4.3 shading to its positive ordinary-trace
tubes.  The spatial carriers are unchanged on retained indices. -/
def proposition63PositiveTraceCroppedShading
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (ordinary : Kakeya.Streamlined.TubeShading family)
    (cropped : WZ1PaperTubeShading family) :
    WZ1PaperTubeShading
      (proposition63PositiveTraceSubfamily ordinary cropped).family :=
  restrictPaperShading
    (proposition63PositiveTraceSubfamily ordinary cropped) cropped

lemma proposition63PositiveTrace_volume_pos
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (ordinary : Kakeya.Streamlined.TubeShading family)
    (cropped : WZ1PaperTubeShading family)
    (index : Fin
      (proposition63PositiveTraceSubfamily ordinary cropped).family.card) :
    0 < volume
      ((proposition63SubfamilyOrdinaryTrace ordinary
        (proposition63PositiveTraceSubfamily ordinary cropped)
        (proposition63PositiveTraceCroppedShading ordinary cropped)).carrier
          index) := by
  change 0 < volume
    ((proposition63OrdinaryTrace ordinary cropped).carrier
      ((proposition63PositiveTraceSubfamily ordinary cropped).embedding
        index))
  apply bot_lt_iff_ne_bot.mpr
  exact
    (Finset.mem_filter.mp
      (Finset.orderEmbOfFin_mem
        (proposition63PositiveTraceIndices ordinary cropped) rfl index)).2

/-- Removing zero ordinary traces preserves the total ordinary trace mass. -/
lemma proposition63PositiveTrace_mass_eq
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (ordinary : Kakeya.Streamlined.TubeShading family)
    (cropped : WZ1PaperTubeShading family) :
    (proposition63SubfamilyOrdinaryTrace ordinary
        (proposition63PositiveTraceSubfamily ordinary cropped)
        (proposition63PositiveTraceCroppedShading ordinary cropped)).mass =
      (proposition63OrdinaryTrace ordinary cropped).mass := by
  let indices := proposition63PositiveTraceIndices ordinary cropped
  let equivalence : Fin indices.card ≃ indices :=
    (indices.orderIsoOfFin rfl).toEquiv
  let trace := proposition63OrdinaryTrace ordinary cropped
  change
    (∑ index : Fin indices.card,
      volume (trace.carrier (indices.orderEmbOfFin rfl index))) =
      ∑ index : Fin family.card, volume (trace.carrier index)
  calc
    (∑ index : Fin indices.card,
        volume (trace.carrier (indices.orderEmbOfFin rfl index))) =
        ∑ source : indices, volume (trace.carrier source.1) := by
      exact Fintype.sum_equiv equivalence
        (fun index : Fin indices.card =>
          volume (trace.carrier (indices.orderEmbOfFin rfl index)))
        (fun source : indices => volume (trace.carrier source.1))
        (fun _ => rfl)
    _ = ∑ source ∈ indices, volume (trace.carrier source) := by
      exact Finset.sum_coe_sort indices
        (fun source => volume (trace.carrier source))
    _ = ∑ source : Fin family.card, volume (trace.carrier source) := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro source _ hsource
      have hzero : ¬ volume (trace.carrier source) ≠ 0 := by
        change ¬ volume
          ((proposition63OrdinaryTrace ordinary cropped).carrier source) ≠ 0
        simpa [indices, proposition63PositiveTraceIndices] using hsource
      exact not_ne_iff.mp hzero

/-- Restrict the actual Lemma 4.3 weak plane map to the tubes with positive
ordinary trace.  Its pointwise function is literally unchanged. -/
noncomputable def proposition63PositiveTracePlaneMap
    {delta incidence : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {ordinary : Kakeya.Streamlined.TubeShading family}
    {cropped : WZ1PaperTubeShading family}
    (planeMap : PaperWZ1WeakPlaneMapData cropped incidence) :
    PaperWZ1WeakPlaneMapData
      (proposition63PositiveTraceCroppedShading ordinary cropped)
      incidence where
  planeMap := planeMap.planeMap
  measurable := planeMap.measurable
  unit := by
    intro point hpoint
    rcases hpoint with ⟨index, hindex⟩
    exact planeMap.unit point
      ⟨(proposition63PositiveTraceSubfamily ordinary cropped).embedding index,
        hindex⟩
  incidence := by
    intro index point hpoint
    have hraw := planeMap.incidence
      ((proposition63PositiveTraceSubfamily ordinary cropped).embedding index)
      point hpoint
    simpa only [Kakeya.Streamlined.TubeSubfamily.tube_eq] using hraw

/-- Reindex a Lemma 4.3 output along a genuine tube subfamily.  The caller
must supply the reindexed mass account and extremality; neither is silently
inherited by an arbitrary subfamily. -/
noncomputable def Proposition63Lemma43Data.restrictSubfamily
    {delta sigma sourceLoss targetLoss incidenceBudget : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    (lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := sourceLoss)
      (targetLoss := targetLoss) source incidenceBudget)
    (selected : Kakeya.Streamlined.TubeSubfamily family)
    (hmass :
      lemma43.leftFactor *
          (restrictPaperShading selected source).mass ≤
        lemma43.rightFactor *
          (restrictPaperShading selected lemma43.shading).mass)
    (hextremal : WZ2PaperCroppedIsExtremal sigma targetLoss
      selected.family
      (restrictPaperShading selected lemma43.shading)) :
    Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := sourceLoss)
      (targetLoss := targetLoss)
      (restrictPaperShading selected source) incidenceBudget where
  shading := restrictPaperShading selected lemma43.shading
  subshading := fun index point hpoint => lemma43.subshading _ hpoint
  cubical := restrictPaperShading_cubical selected lemma43.cubical
  planeMap :=
    { planeMap := lemma43.planeMap.planeMap
      measurable := lemma43.planeMap.measurable
      unit := by
        intro point hpoint
        rcases hpoint with ⟨index, hindex⟩
        exact lemma43.planeMap.unit point
          ⟨selected.embedding index, hindex⟩
      incidence := by
        intro index point hpoint
        have hraw := lemma43.planeMap.incidence
          (selected.embedding index) point hpoint
        simpa only [selected.tube_eq] using hraw }
  leftFactor := lemma43.leftFactor
  rightFactor := lemma43.rightFactor
  leftFactor_pos := lemma43.leftFactor_pos
  leftFactor_ne_top := lemma43.leftFactor_ne_top
  rightFactor_ne_top := lemma43.rightFactor_ne_top
  mass_retention := hmass
  extremal := hextremal

@[simp] lemma Proposition63Lemma43Data.restrictSubfamily_planeMap
    {delta sigma sourceLoss targetLoss incidenceBudget : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    (lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := sourceLoss)
      (targetLoss := targetLoss) source incidenceBudget)
    (selected : Kakeya.Streamlined.TubeSubfamily family)
    (hmass :
      lemma43.leftFactor *
          (restrictPaperShading selected source).mass ≤
        lemma43.rightFactor *
          (restrictPaperShading selected lemma43.shading).mass)
    (hextremal : WZ2PaperCroppedIsExtremal sigma targetLoss
      selected.family
      (restrictPaperShading selected lemma43.shading)) :
    (lemma43.restrictSubfamily selected hmass hextremal).planeMap.planeMap =
      lemma43.planeMap.planeMap :=
  rfl

/-- Rebase the restricted Lemma 4.3 output on itself.  This records exactly
the object consumed by Lemma 4.4: the same retained shading and the same weak
plane-map function, with no second use of the already-paid Lemma 4.3 mass
inequality. -/
noncomputable def Proposition63Lemma43Data.restrictAsSource
    {delta sigma sourceLoss targetLoss outputLoss incidenceBudget : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    (lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := sourceLoss)
      (targetLoss := targetLoss) source incidenceBudget)
    (selected : Kakeya.Streamlined.TubeSubfamily family)
    (hextremal : WZ2PaperCroppedIsExtremal sigma outputLoss
      selected.family
      (restrictPaperShading selected lemma43.shading)) :
    Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := outputLoss)
      (targetLoss := outputLoss)
      (restrictPaperShading selected lemma43.shading) incidenceBudget where
  shading := restrictPaperShading selected lemma43.shading
  subshading := fun _ => Set.Subset.rfl
  cubical := restrictPaperShading_cubical selected lemma43.cubical
  planeMap :=
    { planeMap := lemma43.planeMap.planeMap
      measurable := lemma43.planeMap.measurable
      unit := by
        intro point hpoint
        rcases hpoint with ⟨index, hindex⟩
        exact lemma43.planeMap.unit point
          ⟨selected.embedding index, hindex⟩
      incidence := by
        intro index point hpoint
        have hraw := lemma43.planeMap.incidence
          (selected.embedding index) point hpoint
        simpa only [selected.tube_eq] using hraw }
  leftFactor := 1
  rightFactor := 1
  leftFactor_pos := by norm_num
  leftFactor_ne_top := by norm_num
  rightFactor_ne_top := by norm_num
  mass_retention := by simp
  extremal := hextremal

@[simp] lemma Proposition63Lemma43Data.restrictAsSource_planeMap
    {delta sigma sourceLoss targetLoss outputLoss incidenceBudget : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    (lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := sourceLoss)
      (targetLoss := targetLoss) source incidenceBudget)
    (selected : Kakeya.Streamlined.TubeSubfamily family)
    (hextremal : WZ2PaperCroppedIsExtremal sigma outputLoss
      selected.family
      (restrictPaperShading selected lemma43.shading)) :
    (lemma43.restrictAsSource selected hextremal).planeMap.planeMap =
      lemma43.planeMap.planeMap :=
  rfl

/-- Rebase a further whole-cell refinement of Lemma 4.3 on itself while
retaining the very same weak plane-map function.  This is the form consumed
after the second dense-cubicalization step. -/
noncomputable def Proposition63Lemma43Data.refineAsSource
    {delta sigma sourceLoss targetLoss outputLoss incidenceBudget : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    (lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := sourceLoss)
      (targetLoss := targetLoss) source incidenceBudget)
    (selected : Kakeya.Streamlined.TubeSubfamily family)
    (refined : WZ1PaperTubeShading selected.family)
    (hrefined : PaperIsSubshading refined
      (restrictPaperShading selected lemma43.shading))
    (hextremal : WZ2PaperCroppedIsExtremal sigma outputLoss
      selected.family refined) :
    Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := outputLoss)
      (targetLoss := outputLoss) refined incidenceBudget where
  shading := refined
  subshading := fun _ => Set.Subset.rfl
  cubical := hextremal.cubical
  planeMap :=
    { planeMap := lemma43.planeMap.planeMap
      measurable := lemma43.planeMap.measurable
      unit := by
        intro point hpoint
        rcases hpoint with ⟨index, hindex⟩
        exact lemma43.planeMap.unit point
          ⟨selected.embedding index, hrefined index hindex⟩
      incidence := by
        intro index point hpoint
        have hraw := lemma43.planeMap.incidence
          (selected.embedding index) point (hrefined index hpoint)
        simpa only [selected.tube_eq] using hraw }
  leftFactor := 1
  rightFactor := 1
  leftFactor_pos := by norm_num
  leftFactor_ne_top := by norm_num
  rightFactor_ne_top := by norm_num
  mass_retention := by simp
  extremal := hextremal

@[simp] lemma Proposition63Lemma43Data.refineAsSource_planeMap
    {delta sigma sourceLoss targetLoss outputLoss incidenceBudget : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    (lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := sourceLoss)
      (targetLoss := targetLoss) source incidenceBudget)
    (selected : Kakeya.Streamlined.TubeSubfamily family)
    (refined : WZ1PaperTubeShading selected.family)
    (hrefined : PaperIsSubshading refined
      (restrictPaperShading selected lemma43.shading))
    (hextremal : WZ2PaperCroppedIsExtremal sigma outputLoss
      selected.family refined) :
    (lemma43.refineAsSource selected refined hrefined
      hextremal).planeMap.planeMap = lemma43.planeMap.planeMap :=
  rfl

lemma proposition63SubfamilyOrdinaryTrace_mass_le_cropped
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (ordinary : Kakeya.Streamlined.TubeShading family)
    (selected : Kakeya.Streamlined.TubeSubfamily family)
    (cropped : WZ1PaperTubeShading selected.family) :
    (proposition63SubfamilyOrdinaryTrace
      ordinary selected cropped).mass ≤ cropped.mass := by
  apply Finset.sum_le_sum
  intro index _
  exact measure_mono Set.inter_subset_right

lemma proposition63SubfamilyOrdinaryTrace_union_subset
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (ordinary : Kakeya.Streamlined.TubeShading family)
    (selected : Kakeya.Streamlined.TubeSubfamily family)
    (cropped : WZ1PaperTubeShading selected.family) :
    (proposition63SubfamilyOrdinaryTrace
      ordinary selected cropped).union ⊆ cropped.union := by
  rintro point ⟨index, hpoint⟩
  exact ⟨index, hpoint.2⟩

/-- A subfamily trace is already contained in the cropped shading from which
it was cut, so taking its ordinary trace once more changes no carrier. -/
lemma proposition63SubfamilyOrdinaryTrace_idem_carrier
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (ordinary : Kakeya.Streamlined.TubeShading family)
    (selected : Kakeya.Streamlined.TubeSubfamily family)
    (cropped : WZ1PaperTubeShading selected.family)
    (index : Fin selected.family.card) :
    (proposition63OrdinaryTrace
      (proposition63SubfamilyOrdinaryTrace ordinary selected cropped)
      cropped).carrier index =
        (proposition63SubfamilyOrdinaryTrace ordinary selected cropped).carrier
          index := by
  change
    (ordinary.carrier (selected.embedding index) ∩ cropped.carrier index) ∩
        cropped.carrier index =
      ordinary.carrier (selected.embedding index) ∩ cropped.carrier index
  ext point
  simp only [Set.mem_inter_iff]
  tauto

lemma proposition63SubfamilyOrdinaryTrace_idem_mass
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (ordinary : Kakeya.Streamlined.TubeShading family)
    (selected : Kakeya.Streamlined.TubeSubfamily family)
    (cropped : WZ1PaperTubeShading selected.family) :
    (proposition63OrdinaryTrace
      (proposition63SubfamilyOrdinaryTrace ordinary selected cropped)
      cropped).mass =
        (proposition63SubfamilyOrdinaryTrace ordinary selected cropped).mass := by
  apply Finset.sum_congr rfl
  intro index _
  rw [proposition63SubfamilyOrdinaryTrace_idem_carrier]

/-- External tube weight used by the second Proposition 6.2 preparation:
the actual ordinary mass surviving inside the Lemma 4.3 shading. -/
def proposition63Lemma43TraceWeight
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (ordinary : Kakeya.Streamlined.TubeShading family)
    (cropped : WZ1PaperTubeShading family)
    (index : Fin family.card) : ENNReal :=
  volume ((proposition63OrdinaryTrace ordinary cropped).carrier index)

lemma proposition63Lemma43TraceWeight_sum
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (ordinary : Kakeya.Streamlined.TubeShading family)
    (cropped : WZ1PaperTubeShading family) :
    (∑ index : Fin family.card,
      proposition63Lemma43TraceWeight ordinary cropped index) =
        (proposition63OrdinaryTrace ordinary cropped).mass :=
  rfl

lemma proposition63Lemma43SelectedTraceWeight_sum
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (ordinary : Kakeya.Streamlined.TubeShading family)
    (cropped : WZ1PaperTubeShading family)
    (selected : Kakeya.Streamlined.TubeSubfamily family) :
    (∑ index : Fin selected.family.card,
      proposition63Lemma43TraceWeight ordinary cropped
        (selected.embedding index)) =
      (proposition63SubfamilyOrdinaryTrace ordinary selected
        (restrictPaperShading selected cropped)).mass :=
  rfl

/-- The total external trace weight retained by a pure finite
regularization is exactly the mass of the corresponding ordinary trace
shading. -/
lemma proposition63RegularizedTrace_mass_eq
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (ordinary : Kakeya.Streamlined.TubeShading family)
    (cropped : WZ1PaperTubeShading family)
    {ambientConstant outputConstant normalizationWeight weightUpper : ENNReal}
    {levelCount : ℕ}
    (schedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := family) ambientConstant outputConstant levelCount)
    (regularized : WZ2PaperPureExternalWeightRegularizationData
      schedule normalizationWeight weightUpper
      (proposition63Lemma43TraceWeight ordinary cropped)) :
    (proposition63SubfamilyOrdinaryTrace ordinary regularized.selected
      (restrictPaperShading regularized.selected cropped)).mass =
      ∑ index : Fin regularized.selected.family.card,
        proposition63Lemma43TraceWeight ordinary cropped
          (regularized.selected.embedding index) :=
  rfl

/-- The external-weight regularizer never selects a zero ordinary trace.
Thus the whole-cell dense-normalization restriction lemma applies on every
retained tube. -/
lemma proposition63RegularizedTrace_volume_pos
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (ordinary : Kakeya.Streamlined.TubeShading family)
    (cropped : WZ1PaperTubeShading family)
    {ambientConstant outputConstant normalizationWeight weightUpper : ENNReal}
    {levelCount : ℕ}
    (schedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := family) ambientConstant outputConstant levelCount)
    (regularized : WZ2PaperPureExternalWeightRegularizationData
      schedule normalizationWeight weightUpper
      (proposition63Lemma43TraceWeight ordinary cropped))
    (index : Fin regularized.selected.family.card) :
    0 < volume
      ((proposition63SubfamilyOrdinaryTrace ordinary regularized.selected
        (restrictPaperShading regularized.selected cropped)).carrier
          index) := by
  apply regularized.weightLevel_pos.trans_le
  exact (regularized.weight_band index).1

/-- The retained external trace weight is the exact aggregate trace mass
needed by the second frozen normalization. -/
theorem proposition63RegularizedTrace_retained
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (ordinary : Kakeya.Streamlined.TubeShading family)
    (cropped : WZ1PaperTubeShading family)
    {ambientConstant outputConstant normalizationWeight weightUpper : ENNReal}
    {levelCount : ℕ}
    (schedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := family) ambientConstant outputConstant levelCount)
    (regularized : WZ2PaperPureExternalWeightRegularizationData
      schedule normalizationWeight weightUpper
      (proposition63Lemma43TraceWeight ordinary cropped))
    (normalizationExponent : ℕ)
    (hretained :
      wz2PaperPureRefinementFraction delta normalizationExponent *
          (proposition63SubfamilyOrdinaryTrace ordinary regularized.selected
            (restrictPaperShading regularized.selected cropped)).mass ≤
        (proposition63SubfamilyOrdinaryTrace ordinary regularized.selected
          (restrictPaperShading regularized.selected cropped)).mass) :
    wz2PaperPureRefinementFraction delta normalizationExponent *
        (proposition63SubfamilyOrdinaryTrace ordinary regularized.selected
          (restrictPaperShading regularized.selected cropped)).mass ≤
      (proposition63OrdinaryTrace
        (proposition63SubfamilyOrdinaryTrace ordinary regularized.selected
          (restrictPaperShading regularized.selected cropped))
        (restrictPaperShading regularized.selected cropped)).mass := by
  rw [proposition63SubfamilyOrdinaryTrace_idem_mass]
  exact hretained

/-- The trace-weight regularizer's global retained-weight estimate is exactly
an aggregate ordinary-trace estimate. -/
theorem proposition63RegularizedTrace_mass_retention
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (ordinary : Kakeya.Streamlined.TubeShading family)
    (cropped : WZ1PaperTubeShading family)
    {ambientConstant outputConstant normalizationWeight weightUpper : ENNReal}
    {levelCount : ℕ}
    (schedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := family) ambientConstant outputConstant levelCount)
    (regularized : WZ2PaperPureExternalWeightRegularizationData
      schedule normalizationWeight weightUpper
      (proposition63Lemma43TraceWeight ordinary cropped)) :
    (proposition63OrdinaryTrace ordinary cropped).mass ≤
      regularized.regularizationLoss *
        (proposition63SubfamilyOrdinaryTrace ordinary regularized.selected
          (restrictPaperShading regularized.selected cropped)).mass := by
  rw [← proposition63Lemma43TraceWeight_sum,
    proposition63RegularizedTrace_mass_eq]
  exact regularized.retained_weight

/-- If the parameter hierarchy absorbs the finite regularization loss, the
selected trace is a valid frozen-refinement input relative to the entire
ordinary source. -/
theorem proposition63RegularizedTrace_normalization_retained
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (ordinary : Kakeya.Streamlined.TubeShading family)
    (cropped : WZ1PaperTubeShading family)
    {ambientConstant outputConstant normalizationWeight weightUpper : ENNReal}
    {levelCount : ℕ}
    (schedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := family) ambientConstant outputConstant levelCount)
    (regularized : WZ2PaperPureExternalWeightRegularizationData
      schedule normalizationWeight weightUpper
      (proposition63Lemma43TraceWeight ordinary cropped))
    (normalizationExponent : ℕ)
    (hsourceTrace :
      wz2PaperPureRefinementFraction delta normalizationExponent *
          regularized.regularizationLoss * ordinary.mass ≤
        (proposition63OrdinaryTrace ordinary cropped).mass) :
    wz2PaperPureRefinementFraction delta normalizationExponent *
        ordinary.mass ≤
      (proposition63SubfamilyOrdinaryTrace ordinary regularized.selected
        (restrictPaperShading regularized.selected cropped)).mass := by
  let selectedTrace := proposition63SubfamilyOrdinaryTrace ordinary
    regularized.selected
    (restrictPaperShading regularized.selected cropped)
  have hregularization :=
    proposition63RegularizedTrace_mass_retention ordinary cropped
      schedule regularized
  have hregularizationPos : 0 < regularized.regularizationLoss := by
    rw [regularized.regularizationLoss_eq]
    positivity
  have hregularizationTop : regularized.regularizationLoss ≠ ⊤ := by
    rw [regularized.regularizationLoss_eq]
    exact ENNReal.mul_ne_top (by norm_num) (by simp)
  have hscaled :
      regularized.regularizationLoss *
          (wz2PaperPureRefinementFraction delta
            normalizationExponent * ordinary.mass) ≤
        regularized.regularizationLoss * selectedTrace.mass := by
    calc
      regularized.regularizationLoss *
            (wz2PaperPureRefinementFraction delta
              normalizationExponent * ordinary.mass) =
          wz2PaperPureRefinementFraction delta normalizationExponent *
            regularized.regularizationLoss * ordinary.mass := by ring
      _ ≤ (proposition63OrdinaryTrace ordinary cropped).mass :=
        hsourceTrace
      _ ≤ regularized.regularizationLoss * selectedTrace.mass :=
        hregularization
  apply (ENNReal.mul_le_mul_iff_left
    hregularizationPos.ne' hregularizationTop).mp
  simpa [mul_comm] using hscaled

/-- A common positive lower trace weight gives ordinary density on the
selected family. -/
theorem proposition63SelectedTrace_dense
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (ordinary : Kakeya.Streamlined.TubeShading family)
    (cropped : WZ1PaperTubeShading family)
    (selected : Kakeya.Streamlined.TubeSubfamily family)
    (weightLevel lambda : ENNReal)
    (hweight : ∀ index : Fin selected.family.card,
      weightLevel ≤ proposition63Lemma43TraceWeight ordinary cropped
        (selected.embedding index))
    (hlevel : lambda * Kakeya.deltaTubeVolume delta ≤ weightLevel) :
    (proposition63SubfamilyOrdinaryTrace ordinary selected
      (restrictPaperShading selected cropped)).IsLambdaDense lambda := by
  rw [Kakeya.Streamlined.Shading.IsLambdaDense,
    tubeFamily_mass_eq_nominal]
  change
    lambda * (selected.family.enncard * Kakeya.deltaTubeVolume delta) ≤
      ∑ index : Fin selected.family.card,
        proposition63Lemma43TraceWeight ordinary cropped
          (selected.embedding index)
  calc
    lambda * (selected.family.enncard * Kakeya.deltaTubeVolume delta) =
        ∑ _index : Fin selected.family.card,
          lambda * Kakeya.deltaTubeVolume delta := by
      simp [Kakeya.Streamlined.TubeFamily.enncard, Finset.sum_const]
      ring
    _ ≤ ∑ _index : Fin selected.family.card, weightLevel := by
      exact Finset.sum_le_sum fun _ _ => hlevel
    _ ≤ ∑ index : Fin selected.family.card,
        proposition63Lemma43TraceWeight ordinary cropped
          (selected.embedding index) := by
      exact Finset.sum_le_sum fun index _ => hweight index

/-- A common lower bound for trace weight against the cropped paper-body
volume gives density of the retained cropped Lemma 4.3 shading. -/
theorem proposition63SelectedCropped_dense
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (ordinary : Kakeya.Streamlined.TubeShading family)
    (cropped : WZ1PaperTubeShading family)
    (selected : Kakeya.Streamlined.TubeSubfamily family)
    (weightLevel lambda : ENNReal)
    (hweight : ∀ index : Fin selected.family.card,
      weightLevel ≤ proposition63Lemma43TraceWeight ordinary cropped
        (selected.embedding index))
    (hpaperLevel : ∀ index : Fin selected.family.card,
      lambda *
          volume (wz1PaperTubeCarrier (selected.family.tube index)) ≤
        weightLevel) :
    (restrictPaperShading selected cropped).IsLambdaDense lambda := by
  rw [Kakeya.Streamlined.Shading.IsLambdaDense]
  change
    lambda *
        (∑ index : Fin selected.family.card,
          volume (wz1PaperTubeCarrier (selected.family.tube index))) ≤
      ∑ index : Fin selected.family.card,
        volume (cropped.carrier (selected.embedding index))
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro index _
  calc
    lambda * volume (wz1PaperTubeCarrier (selected.family.tube index)) ≤
        weightLevel := hpaperLevel index
    _ ≤ proposition63Lemma43TraceWeight ordinary cropped
          (selected.embedding index) := hweight index
    _ ≤ volume (cropped.carrier (selected.embedding index)) :=
      measure_mono Set.inter_subset_right

/-- External trace-weight regularization supplies ordinary density on the
exact selected family once its common dyadic weight level absorbs the desired
power density. -/
theorem proposition63RegularizedTrace_dense
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (ordinary : Kakeya.Streamlined.TubeShading family)
    (cropped : WZ1PaperTubeShading family)
    {ambientConstant outputConstant normalizationWeight weightUpper : ENNReal}
    {levelCount : ℕ}
    (schedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := family) ambientConstant outputConstant levelCount)
    (regularized : WZ2PaperPureExternalWeightRegularizationData
      schedule normalizationWeight weightUpper
      (proposition63Lemma43TraceWeight ordinary cropped))
    (lambda : ENNReal)
    (hlevel : lambda * Kakeya.deltaTubeVolume delta ≤
      regularized.weightLevel) :
    (proposition63SubfamilyOrdinaryTrace ordinary regularized.selected
      (restrictPaperShading regularized.selected cropped)).IsLambdaDense
        lambda :=
  proposition63SelectedTrace_dense ordinary cropped regularized.selected
    regularized.weightLevel lambda
    (fun index => (regularized.weight_band index).1) hlevel

/-- A positive, dense ordinary trace on a genuine tube subfamily is a pure
extremal configuration once pure nearby CWA has been restored on that
subfamily.  Its volume bound comes from the actual Lemma 4.3 refinement. -/
noncomputable def proposition63TraceExtremalConfiguration
    {delta sigma sourceLoss lemma43Loss targetLoss incidenceBudget : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    (lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := sourceLoss)
      (targetLoss := lemma43Loss) source incidenceBudget)
    (selected : Kakeya.Streamlined.TubeSubfamily family)
    (ordinary : Kakeya.Streamlined.TubeShading family)
    (hselectedNonempty : selected.family.Nonempty)
    (hcwa : WZ2PaperPureCWAAtNearbyScales selected.family
      (Kakeya.realRpowENN delta (-targetLoss)))
    (hloss : lemma43Loss ≤ targetLoss)
    (hdense :
      (proposition63SubfamilyOrdinaryTrace ordinary selected
        (restrictPaperShading selected lemma43.shading)).IsLambdaDense
          (Kakeya.realRpowENN delta targetLoss)) :
    PureWZ2ExtremalConfiguration sigma targetLoss delta where
  family := selected.family
  shading := proposition63SubfamilyOrdinaryTrace ordinary selected
    (restrictPaperShading selected lemma43.shading)
  extremal :=
    { delta_pos := lemma43.extremal.delta_pos
      delta_le_one := lemma43.extremal.delta_le_one
      nonempty := hselectedNonempty
      cwa_nearby_scales := hcwa
      dense := hdense
      volume_upper := by
        calc
          volume
              (proposition63SubfamilyOrdinaryTrace ordinary selected
                (restrictPaperShading selected lemma43.shading)).union ≤
              volume (restrictPaperShading selected lemma43.shading).union :=
            measure_mono
              (proposition63SubfamilyOrdinaryTrace_union_subset
                ordinary selected
                (restrictPaperShading selected lemma43.shading))
          _ ≤ volume lemma43.shading.union := by
            apply measure_mono
            rintro point ⟨index, hpoint⟩
            exact ⟨selected.embedding index, hpoint⟩
          _ ≤ Kakeya.realRpowENN delta (sigma - targetLoss) :=
            (lemma43.extremal.mono_loss hloss).volume_upper }

/-- Upgrade the same selected Lemma 4.3 shading to cropped extremality once
the paper-body density bound and the restored pure nearby CWA on the selected
family have been paid. -/
theorem proposition63SelectedTraceCroppedExtremal
    {delta sigma sourceLoss lemma43Loss targetLoss incidenceBudget : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    (lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := sourceLoss)
      (targetLoss := lemma43Loss) source incidenceBudget)
    (selected : Kakeya.Streamlined.TubeSubfamily family)
    (hselectedNonempty : selected.family.Nonempty)
    (hcwa : WZ2PaperPureCWAAtNearbyScales selected.family
      (Kakeya.realRpowENN delta (-targetLoss)))
    (hloss : lemma43Loss ≤ targetLoss)
    (hcroppedDense :
      (restrictPaperShading selected lemma43.shading).IsLambdaDense
        (Kakeya.realRpowENN delta targetLoss)) :
    WZ2PaperCroppedIsExtremal sigma targetLoss selected.family
      (restrictPaperShading selected lemma43.shading) := by
  refine
    { delta_pos := lemma43.extremal.delta_pos
      delta_le_one := lemma43.extremal.delta_le_one
      nonempty := hselectedNonempty
      cwa_nearby_scales := hcwa
      cubical := restrictPaperShading_cubical selected lemma43.cubical
      dense := hcroppedDense
      volume_upper := ?_ }
  apply (measure_mono ?_).trans
    (lemma43.extremal.mono_loss hloss).volume_upper
  rintro point ⟨index, hpoint⟩
  exact ⟨selected.embedding index, hpoint⟩

/-- A finite trace-weight regularization with an absorbed output constant
produces the exact pure extremal source used for the second Proposition 6.2
call.  The selected source remains the actual ordinary trace of Lemma 4.3. -/
noncomputable def proposition63RegularizedTraceExtremal
    {delta sigma sourceLoss lemma43Loss targetLoss incidenceBudget : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    (lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := sourceLoss)
      (targetLoss := lemma43Loss) source incidenceBudget)
    (ordinary : Kakeya.Streamlined.TubeShading family)
    {ambientConstant outputConstant normalizationWeight weightUpper : ENNReal}
    {levelCount : ℕ}
    (schedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := family) ambientConstant outputConstant levelCount)
    (regularized : WZ2PaperPureExternalWeightRegularizationData
      schedule normalizationWeight weightUpper
      (proposition63Lemma43TraceWeight ordinary lemma43.shading))
    (houtput : outputConstant ≤
      Kakeya.realRpowENN delta (-targetLoss))
    (houtputFinite : Kakeya.realRpowENN delta (-targetLoss) ≠ ⊤)
    (hloss : lemma43Loss ≤ targetLoss)
    (htraceLevel :
      Kakeya.realRpowENN delta targetLoss *
          Kakeya.deltaTubeVolume delta ≤ regularized.weightLevel) :
    PureWZ2ExtremalConfiguration sigma targetLoss delta := by
  have hcwa : WZ2PaperPureCWAAtNearbyScales regularized.selected.family
      (Kakeya.realRpowENN delta (-targetLoss)) :=
    regularized.pure_cwa_nearby.mono houtput houtputFinite
  have htraceDense := proposition63RegularizedTrace_dense
    ordinary lemma43.shading schedule regularized
    (Kakeya.realRpowENN delta targetLoss) htraceLevel
  exact proposition63TraceExtremalConfiguration lemma43
    regularized.selected ordinary regularized.selected_nonempty hcwa
    hloss htraceDense

/-- The corresponding cropped Lemma 4.3 pair on the same selected family. -/
theorem proposition63RegularizedCroppedExtremal
    {delta sigma sourceLoss lemma43Loss targetLoss incidenceBudget : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    (lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := sourceLoss)
      (targetLoss := lemma43Loss) source incidenceBudget)
    (ordinary : Kakeya.Streamlined.TubeShading family)
    {ambientConstant outputConstant normalizationWeight weightUpper : ENNReal}
    {levelCount : ℕ}
    (schedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := family) ambientConstant outputConstant levelCount)
    (regularized : WZ2PaperPureExternalWeightRegularizationData
      schedule normalizationWeight weightUpper
      (proposition63Lemma43TraceWeight ordinary lemma43.shading))
    (houtput : outputConstant ≤
      Kakeya.realRpowENN delta (-targetLoss))
    (houtputFinite : Kakeya.realRpowENN delta (-targetLoss) ≠ ⊤)
    (hloss : lemma43Loss ≤ targetLoss)
    (hpaperLevel : ∀ index : Fin regularized.selected.family.card,
      Kakeya.realRpowENN delta targetLoss *
          volume (wz1PaperTubeCarrier
            (regularized.selected.family.tube index)) ≤
        regularized.weightLevel) :
    WZ2PaperCroppedIsExtremal sigma targetLoss
      regularized.selected.family
      (restrictPaperShading regularized.selected lemma43.shading) := by
  have hcwa : WZ2PaperPureCWAAtNearbyScales regularized.selected.family
      (Kakeya.realRpowENN delta (-targetLoss)) :=
    regularized.pure_cwa_nearby.mono houtput houtputFinite
  have hcroppedDense := proposition63SelectedCropped_dense
    ordinary lemma43.shading regularized.selected regularized.weightLevel
    (Kakeya.realRpowENN delta targetLoss)
    (fun index => (regularized.weight_band index).1) hpaperLevel
  exact proposition63SelectedTraceCroppedExtremal lemma43
    regularized.selected regularized.selected_nonempty hcwa hloss
    hcroppedDense

/-- Assemble both extremal views needed for the dependent second
Proposition 6.2 call from one external trace-weight regularization. -/
theorem proposition63RegularizedTraceExtremalPair
    {delta sigma sourceLoss lemma43Loss targetLoss incidenceBudget : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    (lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := sourceLoss)
      (targetLoss := lemma43Loss) source incidenceBudget)
    (ordinary : Kakeya.Streamlined.TubeShading family)
    {ambientConstant outputConstant normalizationWeight weightUpper : ENNReal}
    {levelCount : ℕ}
    (schedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := family) ambientConstant outputConstant levelCount)
    (regularized : WZ2PaperPureExternalWeightRegularizationData
      schedule normalizationWeight weightUpper
      (proposition63Lemma43TraceWeight ordinary lemma43.shading))
    (houtput : outputConstant ≤
      Kakeya.realRpowENN delta (-targetLoss))
    (houtputFinite :
      Kakeya.realRpowENN delta (-targetLoss) ≠ ⊤)
    (hloss : lemma43Loss ≤ targetLoss)
    (htraceLevel :
      Kakeya.realRpowENN delta targetLoss *
          Kakeya.deltaTubeVolume delta ≤ regularized.weightLevel)
    (hpaperLevel : ∀ index : Fin regularized.selected.family.card,
      Kakeya.realRpowENN delta targetLoss *
          volume (wz1PaperTubeCarrier
            (regularized.selected.family.tube index)) ≤
        regularized.weightLevel) :
    ∃ _ordinarySource : PureWZ2ExtremalConfiguration sigma targetLoss delta,
      WZ2PaperCroppedIsExtremal sigma targetLoss
        regularized.selected.family
        (restrictPaperShading regularized.selected lemma43.shading) := by
  let selected := regularized.selected
  let cropped := restrictPaperShading selected lemma43.shading
  have hcwa : WZ2PaperPureCWAAtNearbyScales selected.family
      (Kakeya.realRpowENN delta (-targetLoss)) :=
    regularized.pure_cwa_nearby.mono houtput houtputFinite
  have htraceDense :
      (proposition63SubfamilyOrdinaryTrace ordinary selected cropped
        ).IsLambdaDense (Kakeya.realRpowENN delta targetLoss) :=
    proposition63RegularizedTrace_dense ordinary lemma43.shading
      schedule regularized (Kakeya.realRpowENN delta targetLoss)
      htraceLevel
  have hcroppedDense : cropped.IsLambdaDense
      (Kakeya.realRpowENN delta targetLoss) :=
    proposition63SelectedCropped_dense ordinary lemma43.shading selected
      regularized.weightLevel
      (Kakeya.realRpowENN delta targetLoss)
      (fun index => (regularized.weight_band index).1) hpaperLevel
  exact
    ⟨proposition63TraceExtremalConfiguration lemma43 selected ordinary
        regularized.selected_nonempty hcwa hloss htraceDense,
      proposition63SelectedTraceCroppedExtremal lemma43 selected
        regularized.selected_nonempty hcwa hloss hcroppedDense⟩

/-- Transport an ordinary pure extremal configuration through the same
horizontal chart used by the global-slice argument. -/
noncomputable def proposition63TransportPureExtremal
    {sigma loss delta : ℝ}
    (chart : WZ1HorizontalChart)
    (source : PureWZ2ExtremalConfiguration sigma loss delta) :
    PureWZ2ExtremalConfiguration sigma loss delta where
  family := transportFamily chart.isometry source.family
  shading := transportShading chart.isometry source.shading
  extremal := by
    refine
      { delta_pos := source.extremal.delta_pos
        delta_le_one := source.extremal.delta_le_one
        nonempty := source.extremal.nonempty
        cwa_nearby_scales := ?_
        dense := ?_
        volume_upper := ?_ }
    · simpa [WZ1HorizontalChart.imageTubeFamily_eq_transportFamily] using
        pureCWAAtNearbyScales_image chart.affineIsometry
          source.extremal.cwa_nearby_scales
    · change Kakeya.realRpowENN delta loss *
          (transportFamily chart.isometry
            source.family).toBodyFamily.mass ≤
        (transportShading chart.isometry source.shading).mass
      rw [transportFamily_mass chart.isometry
          (isometry_volume_image chart.affineIsometry),
        transportShading_mass chart.isometry
          (isometry_volume_image chart.affineIsometry)]
      exact source.extremal.dense
    · rw [transportShading_union chart.isometry,
        show volume (chart.isometry '' source.shading.union) =
          volume source.shading.union by
            exact volume_image chart.isometry source.shading.union]
      exact source.extremal.volume_upper

/-- Transport a tube subfamily through the same horizontal chart, keeping
the dependent index map unchanged. -/
def proposition63TransportSubfamily
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (chart : WZ1HorizontalChart)
    (selected : Kakeya.Streamlined.TubeSubfamily family) :
    Kakeya.Streamlined.TubeSubfamily
      (transportFamily chart.isometry family) where
  family := transportFamily chart.isometry selected.family
  embedding := selected.embedding
  tube_eq index := by
    change transportTube chart.isometry (selected.family.tube index) =
      transportTube chart.isometry (family.tube (selected.embedding index))
    rw [selected.tube_eq index]

/-- Restriction and horizontal-chart transport commute definitionally on
each retained carrier. -/
lemma proposition63Transport_restrictPaperShading_carrier
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (chart : WZ1HorizontalChart)
    (selected : Kakeya.Streamlined.TubeSubfamily family)
    (shading : WZ1PaperTubeShading family)
    (index : Fin selected.family.card) :
    (chart.transportPaperShading
      (restrictPaperShading selected shading)).carrier index =
      (restrictPaperShading
        (proposition63TransportSubfamily chart selected)
        (chart.transportPaperShading shading)).carrier index :=
  rfl

/-- The ordinary trace commutes exactly with a horizontal chart. -/
lemma proposition63Transport_ordinaryTrace_carrier
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (chart : WZ1HorizontalChart)
    (ordinary : Kakeya.Streamlined.TubeShading family)
    (cropped : WZ1PaperTubeShading family)
    (index : Fin family.card) :
    (proposition63OrdinaryTrace
      (transportShading chart.isometry ordinary)
      (chart.transportPaperShading cropped)).carrier index =
        chart.isometry ''
          (proposition63OrdinaryTrace ordinary cropped).carrier index := by
  change (chart.isometry '' ordinary.carrier index) ∩
      (chart.isometry '' cropped.carrier index) =
    chart.isometry '' (ordinary.carrier index ∩ cropped.carrier index)
  exact (Set.image_inter chart.isometry.injective).symm

/-- Horizontal-chart transport preserves the total ordinary trace mass. -/
lemma proposition63Transport_ordinaryTrace_mass
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (chart : WZ1HorizontalChart)
    (ordinary : Kakeya.Streamlined.TubeShading family)
    (cropped : WZ1PaperTubeShading family) :
    (proposition63OrdinaryTrace
      (transportShading chart.isometry ordinary)
      (chart.transportPaperShading cropped)).mass =
        (proposition63OrdinaryTrace ordinary cropped).mass := by
  change
    (∑ index : Fin family.card,
      volume ((chart.isometry '' ordinary.carrier index) ∩
        (chart.isometry '' cropped.carrier index))) =
      ∑ index : Fin family.card,
        volume (ordinary.carrier index ∩ cropped.carrier index)
  apply Finset.sum_congr rfl
  intro index _
  rw [← Set.image_inter chart.isometry.injective]
  exact volume_image chart.isometry
    (ordinary.carrier index ∩ cropped.carrier index)

/-- Literal unit rescaling followed by a horizontal chart puts every exact
ordinary-image point in a fixed strict axial window.  The estimate uses only
the cropped source box, the line-class bound for the common parent axis, and
the literal map's `1 / 100` longitudinal compression. -/
theorem proposition63_literal_exact_image_chart_axial_window
    {delta rho : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (cropped : WZ1PaperTubeShading family)
    (ordinary : Kakeya.Streamlined.TubeShading family)
    (ordinary_sub : ∀ index,
      ordinary.carrier index ⊆ cropped.carrier index)
    (parentTube : Kakeya.DeltaTube rho)
    (hrho : 0 < rho)
    (parentLine : WZ1PaperTubeInLineClass parentTube)
    {normalization : WZ2PaperAssouadUnitRescalingData parentTube}
    {literal : WZ2PaperLiteralUnitRescaledFamilyData
      family parentTube hrho}
    {jacobianConstant : ENNReal}
    (certificate : WZ2PaperAssouadToLiteralRescalingCertificate
      hrho normalization literal jacobianConstant)
    (chart : WZ1HorizontalChart)
    (index : Fin certificate.publicFamily.card)
    (point : Point3)
    (point_mem : point ∈
      (transportShading chart.isometry
        (certificate.literalExactImageShading ordinary)).carrier index) :
    |point (2 : Fin 3)| ≤ 1 / 25 := by
  rcases point_mem with ⟨literalPoint, literalPointMem, rfl⟩
  rcases literalPointMem with ⟨sourcePoint, sourcePointMem, rfl⟩
  have sourcePointCropped : sourcePoint ∈ cropped.union := by
    exact ⟨literal.sourceIndex (certificate.section6Index.symm index),
      ordinary_sub _ sourcePointMem⟩
  have sourcePointNorm : ‖sourcePoint‖ ≤ 3 :=
    paperShadingPoint_norm_le_three sourcePointCropped
  have parentZeroNorm : ‖wz1TubeAxisZeroPoint parentTube‖ ≤ 1 :=
    paperAxisZeroPoint_norm_le_one parentLine
  have differenceNorm :
      ‖sourcePoint - wz1TubeAxisZeroPoint parentTube‖ ≤ 4 := by
    calc
      ‖sourcePoint - wz1TubeAxisZeroPoint parentTube‖ ≤
          ‖sourcePoint‖ + ‖wz1TubeAxisZeroPoint parentTube‖ :=
        norm_sub_le _ _
      _ ≤ 3 + 1 := by gcongr
      _ = 4 := by norm_num
  have innerBound :
      |inner ℝ (sourcePoint - wz1TubeAxisZeroPoint parentTube)
          (wz1PaperDirection parentTube)| ≤ 4 := by
    calc
      |inner ℝ (sourcePoint - wz1TubeAxisZeroPoint parentTube)
          (wz1PaperDirection parentTube)| ≤
          ‖sourcePoint - wz1TubeAxisZeroPoint parentTube‖ *
            ‖wz1PaperDirection parentTube‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ 4 * 1 := by
        gcongr
        exact (wz1PaperDirection_norm parentTube).le
      _ = 4 := by norm_num
  rw [chart.isometry_preserves_coord2,
    wz2PaperLiteralUnitRescalingMap_coord2]
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 100)]
  nlinarith

/-- Recover the ordinary pure extremal source used by the second Proposition
6.2 call from the first normalization's final trace on the actual
chart-selected metric fibre.  The only quantitative assumptions are exactly
the per-tube trace floor and scalar Jacobian absorption used by the generic
critical-witness adapter. -/
noncomputable def proposition63ChartOrdinaryExtremalSource
    {sigma initialInputLoss initialOutputLoss fineDelta rho outputLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration
      sigma initialInputLoss fineDelta}
    {normalizationExponent : ℕ}
    (initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := initialOutputLoss) initialSource
      normalizationExponent)
    (selected : Kakeya.Streamlined.TubeSubfamily
      initialNormalized.croppedFamily)
    (finalShading : WZ1PaperTubeShading selected.family)
    (parentTube : Kakeya.DeltaTube rho)
    (hrho : 0 < rho)
    (output : WZ2PaperPureRescaledFullFiberOutput
      (sigma := sigma) (loss := outputLoss)
      finalShading parentTube hrho)
    (finalCubical : WZ1PaperIsCubicalShading finalShading)
    (finalSubset : ∀ index,
      finalShading.carrier index ⊆
        initialNormalized.croppedRefined.carrier
          (selected.embedding index))
    (density : ENNReal)
    (ordinaryPerTube : ∀ index : Fin selected.family.card,
      density *
          volume (initialNormalized.croppedFamily.tube
            (selected.embedding index)).carrier ≤
        volume (initialNormalized.frame ''
          initialNormalized.ordinaryRefined.carrier
            (PureWZ2CroppedCriticalNormalizationData.ordinaryIndex
              initialNormalized selected index)))
    (scalar :
      Kakeya.realRpowENN (fineDelta / rho) outputLoss *
            output.rescalingCertificate.publicFamily.toBodyFamily.mass ≤
        (ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
            ENNReal.ofReal ((1 / rho : ℝ) ^ 2)) *
          ((100 : ENNReal)⁻¹ * density * finalShading.mass))
    (chart : WZ1HorizontalChart) :
    PureWZ2ExtremalConfiguration sigma outputLoss (fineDelta / rho) :=
  proposition63TransportPureExtremal chart
    (criticalRescaledFiberToExtremalConfiguration
      (output.withNormalizationFinalOrdinaryTraceOfPerTube
      initialNormalized selected finalShading parentTube hrho
      finalCubical finalSubset density ordinaryPerTube scalar
      ))

/-- Aggregate-mass version of the charted ordinary source used for the
second Proposition 6.2 call.  This is the appropriate interface after the
non-aligned common-slice restriction: the ordinary trace is taken before
the literal rescaling, and its exact Jacobian is paid explicitly. -/
noncomputable def proposition63ChartOrdinaryExtremalSourceOfTraceMass
    {sigma initialInputLoss initialOutputLoss fineDelta rho outputLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration
      sigma initialInputLoss fineDelta}
    {normalizationExponent : ℕ}
    (initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := initialOutputLoss) initialSource
      normalizationExponent)
    (selected : Kakeya.Streamlined.TubeSubfamily
      initialNormalized.croppedFamily)
    (finalShading : WZ1PaperTubeShading selected.family)
    (parentTube : Kakeya.DeltaTube rho)
    (hrho : 0 < rho)
    (output : WZ2PaperPureRescaledFullFiberOutput
      (sigma := sigma) (loss := outputLoss)
      finalShading parentTube hrho)
    (massLower :
      Kakeya.realRpowENN (fineDelta / rho) outputLoss *
            output.rescalingCertificate.publicFamily.toBodyFamily.mass ≤
        (ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
            ENNReal.ofReal ((1 / rho : ℝ) ^ 2)) *
          (initialNormalized.finalOrdinaryTrace
            selected finalShading).mass)
    (chart : WZ1HorizontalChart) :
    PureWZ2ExtremalConfiguration sigma outputLoss (fineDelta / rho) :=
  proposition63TransportPureExtremal chart
    (criticalRescaledFiberToExtremalConfiguration
      (output.withNormalizationFinalOrdinaryTraceOfMass
      initialNormalized selected finalShading parentTube hrho massLower
      ))

/-- The concrete charted ordinary extremal source used before the second
Proposition 6.2 call inherits the fixed `1 / 25` axial window from its exact
literal-image provenance. -/
theorem proposition63ChartOrdinaryExtremalSourceOfTraceMass_axial_window
    {sigma initialInputLoss initialOutputLoss fineDelta rho outputLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration
      sigma initialInputLoss fineDelta}
    {normalizationExponent : ℕ}
    (initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := initialOutputLoss) initialSource
      normalizationExponent)
    (selected : Kakeya.Streamlined.TubeSubfamily
      initialNormalized.croppedFamily)
    (finalShading : WZ1PaperTubeShading selected.family)
    (parentTube : Kakeya.DeltaTube rho)
    (hrho : 0 < rho)
    (parentLine : WZ1PaperTubeInLineClass parentTube)
    (output : WZ2PaperPureRescaledFullFiberOutput
      (sigma := sigma) (loss := outputLoss)
      finalShading parentTube hrho)
    (massLower :
      Kakeya.realRpowENN (fineDelta / rho) outputLoss *
            output.rescalingCertificate.publicFamily.toBodyFamily.mass ≤
        (ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
            ENNReal.ofReal ((1 / rho : ℝ) ^ 2)) *
          (initialNormalized.finalOrdinaryTrace
            selected finalShading).mass)
    (chart : WZ1HorizontalChart) :
    ∀ index point,
      point ∈ (proposition63ChartOrdinaryExtremalSourceOfTraceMass
        initialNormalized selected finalShading parentTube hrho output
        massLower chart).shading.carrier index →
      |point (2 : Fin 3)| ≤ 1 / 25 := by
  intro index point pointMem
  exact proposition63_literal_exact_image_chart_axial_window
    finalShading
    (initialNormalized.finalOrdinaryTrace selected finalShading)
    (fun _ _ hpoint => hpoint.2) parentTube hrho parentLine
    output.rescalingCertificate chart index point pointMem

/-- A whole-cell subshading of a dense cubicalization is recovered exactly
from its ordinary trace, provided that trace has positive measure on every
retained tube. -/
theorem proposition63OrdinaryTrace_denseCubicalization
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (ordinary : Kakeya.Streamlined.TubeShading family)
    (cropped : WZ1PaperTubeShading family)
    (hdelta : 0 < delta)
    (hcubical : WZ1PaperIsCubicalShading cropped)
    (hdenseSubset : ∀ index,
      cropped.carrier index ⊆
        pureWZ2DenseCubicalization
          (family.tube index) (ordinary.carrier index))
    (htracePositive : ∀ index,
      0 < volume
        ((proposition63OrdinaryTrace ordinary cropped).carrier index))
    (index : Fin family.card) :
    pureWZ2DenseCubicalization
        (family.tube index)
        ((proposition63OrdinaryTrace ordinary cropped).carrier index) =
      cropped.carrier index := by
  apply pureWZ2DenseCubicalization_inter_whole_cells
      (family.tube index) (ordinary.carrier index)
      (cropped.carrier index) hdelta
      (hdenseSubset index)
  · exact hcubical index
  · simpa only [proposition63OrdinaryTrace_carrier] using
      htracePositive index

/-- Repackage a genuine ordinary extremal configuration and a dependent
whole-cell dense crop as a frozen normalization.  No family, index, or point
is changed: the frame and both index equivalences are identities. -/
noncomputable def proposition63IdentityDenseNormalization
    {sigma sourceLoss normalizationLoss delta : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    (sourceLoss_le_half : sourceLoss ≤ normalizationLoss / 2)
    (normalizationExponent : ℕ)
    (cropped : WZ1PaperTubeShading source.family)
    (hcubical : WZ1PaperIsCubicalShading cropped)
    (hdenseSubset : ∀ index,
      cropped.carrier index ⊆
        pureWZ2DenseCubicalization
          (source.family.tube index)
          (source.shading.carrier index))
    (htracePositive : ∀ index,
      0 < volume
        ((proposition63OrdinaryTrace
          source.shading cropped).carrier index))
    (hretained :
      wz2PaperPureRefinementFraction delta normalizationExponent *
          source.shading.mass ≤
        (proposition63OrdinaryTrace source.shading cropped).mass)
    (hordinaryPerTube : ∀ index,
      (Kakeya.realRpowENN delta sourceLoss / 2) *
            volume (source.family.tube index).carrier ≤
        volume ((proposition63OrdinaryTrace
          source.shading cropped).carrier index))
    (hordinaryAxialWindow : ∀ index point,
      point ∈ (proposition63OrdinaryTrace
          source.shading cropped).carrier index →
        |point (2 : Fin 3)| ≤ 1 / 4)
    (hline : WZ1PaperIsLineClass source.family)
    (htopLevel : WZ2PaperConvexWolffBound source.family
      (Kakeya.realRpowENN delta (-normalizationLoss)))
    (hextremal : WZ2PaperCroppedIsExtremal
      sigma normalizationLoss source.family cropped)
    (hcellContained : ∀ index (cell : ℤ × ℤ × ℤ),
      (((proposition63OrdinaryTrace source.shading cropped).carrier index) ∩
          wz1PaperGridCube delta cell).Nonempty →
        wz1PaperGridCube delta cell ⊆
          wz1PaperTubeCarrier (source.family.tube index))
    (hboundedBase : HasBoundedBase source.family 4) :
    PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent where
  input_loss_le_half := sourceLoss_le_half
  selected := proposition63IdentitySubfamily source.family
  selected_nonempty := source.extremal.nonempty
  ordinaryRefined := proposition63OrdinaryTrace source.shading cropped
  ordinary_subshading := by
    intro index point hpoint
    exact hpoint.1
  retained_mass := hretained
  frame := AffineIsometryEquiv.refl ℝ Point3
  croppedFamily := source.family
  indexEquiv := proposition63IdentityIndexEquiv source.family
  ordinary_carrier_image_eq := by
    intro index
    change (source.family.tube index).carrier =
      (AffineIsometryEquiv.refl ℝ Point3) ''
        (source.family.tube index).carrier
    simp
  ordinary_per_tube := hordinaryPerTube
  ordinary_axial_window := by
    intro index point hpoint
    rcases hpoint with ⟨sourcePoint, hsourcePoint, hpoint⟩
    subst point
    simpa using hordinaryAxialWindow index sourcePoint hsourcePoint
  croppedRefined := cropped
  cropped_carrier_eq_dense_cubicalization := by
    intro index
    let sourceIndex : Fin source.family.card :=
      ⟨index.1, by simpa [proposition63IdentitySubfamily] using index.2⟩
    change cropped.carrier sourceIndex =
      pureWZ2DenseCubicalization (source.family.tube sourceIndex)
        ((AffineIsometryEquiv.refl ℝ Point3) ''
          (proposition63OrdinaryTrace
            source.shading cropped).carrier index)
    have hindex : index = sourceIndex := Fin.ext rfl
    subst sourceIndex
    rw [show (AffineIsometryEquiv.refl ℝ Point3) ''
        (proposition63OrdinaryTrace source.shading cropped).carrier
          index =
        (proposition63OrdinaryTrace source.shading cropped).carrier
          index by simp]
    exact (proposition63OrdinaryTrace_denseCubicalization
      source.shading cropped source.extremal.delta_pos hcubical
      hdenseSubset htracePositive index).symm
  cropped_cubical := hcubical
  line_class := hline
  cropped_top_level_cwa := htopLevel
  final_extremal := hextremal
  ordinary_cell_containment := by
    intro index cell hcell
    rcases hcell with ⟨point, ⟨sourcePoint, hsourcePoint, hpoint⟩, hpointCell⟩
    subst point
    exact hcellContained index cell ⟨sourcePoint, hsourcePoint, hpointCell⟩
  ordinary_bounded_base := hboundedBase

/-- Repackage a genuine ordinary extremal configuration while retaining its
entire ordinary shading.  Only the cropped output is dense-cubicalized.  This
is the normalization used by recursive re-entry: it is compatible with
normalization exponent zero because no dense-crop loss is charged to the
ordinary refinement field. -/
noncomputable def proposition63IdentityFullOrdinaryNormalization
    {sigma sourceLoss normalizationLoss delta : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    (sourceLoss_le_half : sourceLoss ≤ normalizationLoss / 2)
    (normalizationExponent : ℕ)
    (cropped : WZ1PaperTubeShading source.family)
    (hcubical : WZ1PaperIsCubicalShading cropped)
    (hcropped : ∀ index,
      cropped.carrier index =
        pureWZ2DenseCubicalization
          (source.family.tube index) (source.shading.carrier index))
    (hretained :
      wz2PaperPureRefinementFraction delta normalizationExponent *
          source.shading.mass ≤ source.shading.mass)
    (hordinaryPerTube : ∀ index,
      (Kakeya.realRpowENN delta sourceLoss / 2) *
            volume (source.family.tube index).carrier ≤
        volume (source.shading.carrier index))
    (hordinaryAxialWindow : ∀ index point,
      point ∈ source.shading.carrier index →
        |point (2 : Fin 3)| ≤ 1 / 4)
    (hline : WZ1PaperIsLineClass source.family)
    (htopLevel : WZ2PaperConvexWolffBound source.family
      (Kakeya.realRpowENN delta (-normalizationLoss)))
    (hextremal : WZ2PaperCroppedIsExtremal
      sigma normalizationLoss source.family cropped)
    (hcellContained : ∀ index (cell : ℤ × ℤ × ℤ),
      (source.shading.carrier index ∩
          wz1PaperGridCube delta cell).Nonempty →
        wz1PaperGridCube delta cell ⊆
          wz1PaperTubeCarrier (source.family.tube index))
    (hboundedBase : HasBoundedBase source.family 4) :
    PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent where
  input_loss_le_half := sourceLoss_le_half
  selected := proposition63IdentitySubfamily source.family
  selected_nonempty := source.extremal.nonempty
  ordinaryRefined := source.shading
  ordinary_subshading := fun _ => Set.Subset.rfl
  retained_mass := hretained
  frame := AffineIsometryEquiv.refl ℝ Point3
  croppedFamily := source.family
  indexEquiv := proposition63IdentityIndexEquiv source.family
  ordinary_carrier_image_eq := by
    intro index
    change (source.family.tube index).carrier =
      (AffineIsometryEquiv.refl ℝ Point3) ''
        (source.family.tube index).carrier
    simp
  ordinary_per_tube := hordinaryPerTube
  ordinary_axial_window := by
    intro index point hpoint
    rcases hpoint with ⟨sourcePoint, hsourcePoint, hpoint⟩
    subst point
    simpa using hordinaryAxialWindow index sourcePoint hsourcePoint
  croppedRefined := cropped
  cropped_carrier_eq_dense_cubicalization := by
    intro index
    simpa [proposition63IdentityIndexEquiv] using hcropped index
  cropped_cubical := hcubical
  line_class := hline
  cropped_top_level_cwa := htopLevel
  final_extremal := hextremal
  ordinary_cell_containment := by
    intro index cell hcell
    rcases hcell with ⟨point, ⟨sourcePoint, hsourcePoint, hpoint⟩, hpointCell⟩
    subst point
    exact hcellContained index cell ⟨sourcePoint, hsourcePoint, hpointCell⟩
  ordinary_bounded_base := hboundedBase

/-- The normalization adapter after a whole-tube pruning.  Each retained
tube has a positive ordinary trace, so the dense cubicalization restriction
recovers the exact cropped carrier; discarded tubes are absent from the
selected family rather than represented by an invalid empty dense crop. -/
noncomputable def proposition63SubfamilyDenseNormalization
    {sigma sourceLoss normalizationLoss delta : ℝ}
    {source : PureWZ2ExtremalConfiguration sigma sourceLoss delta}
    (sourceLoss_le_half : sourceLoss ≤ normalizationLoss / 2)
    (normalizationExponent : ℕ)
    (selected : Kakeya.Streamlined.TubeSubfamily source.family)
    (cropped : WZ1PaperTubeShading selected.family)
    (hcubical : WZ1PaperIsCubicalShading cropped)
    (hdenseSubset : ∀ index,
      cropped.carrier index ⊆
        pureWZ2DenseCubicalization
          (selected.family.tube index)
          (source.shading.carrier (selected.embedding index)))
    (htracePositive : ∀ index,
      0 < volume
        ((proposition63SubfamilyOrdinaryTrace
          source.shading selected cropped).carrier index))
    (hretained :
      wz2PaperPureRefinementFraction delta normalizationExponent *
          source.shading.mass ≤
        (proposition63SubfamilyOrdinaryTrace
          source.shading selected cropped).mass)
    (hordinaryPerTube : ∀ index,
      (Kakeya.realRpowENN delta sourceLoss / 2) *
            volume (selected.family.tube index).carrier ≤
        volume ((proposition63SubfamilyOrdinaryTrace
          source.shading selected cropped).carrier index))
    (hordinaryAxialWindow : ∀ index point,
      point ∈ (proposition63SubfamilyOrdinaryTrace
          source.shading selected cropped).carrier index →
        |point (2 : Fin 3)| ≤ 1 / 4)
    (hline : WZ1PaperIsLineClass selected.family)
    (htopLevel : WZ2PaperConvexWolffBound selected.family
      (Kakeya.realRpowENN delta (-normalizationLoss)))
    (hextremal : WZ2PaperCroppedIsExtremal
      sigma normalizationLoss selected.family cropped)
    (hcellContained : ∀ index (cell : ℤ × ℤ × ℤ),
      (((proposition63SubfamilyOrdinaryTrace
          source.shading selected cropped).carrier index) ∩
          wz1PaperGridCube delta cell).Nonempty →
        wz1PaperGridCube delta cell ⊆
          wz1PaperTubeCarrier (selected.family.tube index))
    (hboundedBase : HasBoundedBase selected.family 4) :
    PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent where
  input_loss_le_half := sourceLoss_le_half
  selected := selected
  selected_nonempty := hextremal.nonempty
  ordinaryRefined :=
    proposition63SubfamilyOrdinaryTrace source.shading selected cropped
  ordinary_subshading := by
    intro index point hpoint
    exact hpoint.1
  retained_mass := hretained
  frame := AffineIsometryEquiv.refl ℝ Point3
  croppedFamily := selected.family
  indexEquiv := Equiv.refl _
  ordinary_carrier_image_eq := by
    intro index
    change (selected.family.tube index).carrier =
      (AffineIsometryEquiv.refl ℝ Point3) ''
        (selected.family.tube index).carrier
    simp
  ordinary_per_tube := hordinaryPerTube
  ordinary_axial_window := by
    intro index point hpoint
    rcases hpoint with ⟨sourcePoint, hsourcePoint, hpoint⟩
    subst point
    simpa using hordinaryAxialWindow index sourcePoint hsourcePoint
  croppedRefined := cropped
  cropped_carrier_eq_dense_cubicalization := by
    intro index
    change cropped.carrier index =
      pureWZ2DenseCubicalization (selected.family.tube index)
        ((AffineIsometryEquiv.refl ℝ Point3) ''
          (proposition63SubfamilyOrdinaryTrace
            source.shading selected cropped).carrier index)
    rw [show (AffineIsometryEquiv.refl ℝ Point3) ''
        (proposition63SubfamilyOrdinaryTrace
          source.shading selected cropped).carrier index =
        (proposition63SubfamilyOrdinaryTrace
          source.shading selected cropped).carrier index by simp]
    apply Eq.symm
    apply pureWZ2DenseCubicalization_inter_whole_cells
        (selected.family.tube index)
        (source.shading.carrier (selected.embedding index))
        (cropped.carrier index) source.extremal.delta_pos
        (hdenseSubset index)
    · exact hcubical index
    · simpa only [proposition63SubfamilyOrdinaryTrace_carrier] using
        htracePositive index
  cropped_cubical := hcubical
  line_class := hline
  cropped_top_level_cwa := htopLevel
  final_extremal := hextremal
  ordinary_cell_containment := by
    intro index cell hcell
    rcases hcell with ⟨point, ⟨sourcePoint, hsourcePoint, hpoint⟩, hpointCell⟩
    subst point
    exact hcellContained index cell ⟨sourcePoint, hsourcePoint, hpointCell⟩
  ordinary_bounded_base := hboundedBase

/-- Identity-frame normalization when the caller already proved the exact
dense-cubicalization equality for its ordinary source. -/
noncomputable def proposition63IdentityExactNormalization
    {sigma sourceLoss normalizationLoss delta : ℝ}
    (source : PureWZ2ExtremalConfiguration sigma sourceLoss delta)
    (sourceLoss_le_half : sourceLoss ≤ normalizationLoss / 2)
    (normalizationExponent : ℕ)
    (cropped : WZ1PaperTubeShading source.family)
    (hcubical : WZ1PaperIsCubicalShading cropped)
    (hexact : ∀ index,
      cropped.carrier index =
        pureWZ2DenseCubicalization
          (source.family.tube index) (source.shading.carrier index))
    (hretained :
      wz2PaperPureRefinementFraction delta normalizationExponent *
          source.shading.mass ≤ source.shading.mass)
    (hordinaryPerTube : ∀ index,
      (Kakeya.realRpowENN delta sourceLoss / 2) *
            volume (source.family.tube index).carrier ≤
        volume (source.shading.carrier index))
    (hordinaryAxialWindow : ∀ index point,
      point ∈ source.shading.carrier index →
        |point (2 : Fin 3)| ≤ 1 / 4)
    (hline : WZ1PaperIsLineClass source.family)
    (htopLevel : WZ2PaperConvexWolffBound source.family
      (Kakeya.realRpowENN delta (-normalizationLoss)))
    (hextremal : WZ2PaperCroppedIsExtremal
      sigma normalizationLoss source.family cropped)
    (hcellContained : ∀ index (cell : ℤ × ℤ × ℤ),
      (source.shading.carrier index ∩
          wz1PaperGridCube delta cell).Nonempty →
        wz1PaperGridCube delta cell ⊆
          wz1PaperTubeCarrier (source.family.tube index))
    (hboundedBase : HasBoundedBase source.family 4) :
    PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) source normalizationExponent where
  input_loss_le_half := sourceLoss_le_half
  selected := proposition63IdentitySubfamily source.family
  selected_nonempty := source.extremal.nonempty
  ordinaryRefined := source.shading
  ordinary_subshading := fun _ => Set.Subset.rfl
  retained_mass := hretained
  frame := AffineIsometryEquiv.refl ℝ Point3
  croppedFamily := source.family
  indexEquiv := proposition63IdentityIndexEquiv source.family
  ordinary_carrier_image_eq := by
    intro index
    change (source.family.tube index).carrier =
      (AffineIsometryEquiv.refl ℝ Point3) ''
        (source.family.tube index).carrier
    simp
  ordinary_per_tube := hordinaryPerTube
  ordinary_axial_window := by
    intro index point hpoint
    rcases hpoint with ⟨sourcePoint, hsourcePoint, hpoint⟩
    subst point
    simpa using hordinaryAxialWindow index sourcePoint hsourcePoint
  croppedRefined := cropped
  cropped_carrier_eq_dense_cubicalization := by
    intro index
    let sourceIndex : Fin source.family.card :=
      ⟨index.1, by
        simpa [proposition63IdentitySubfamily] using index.2⟩
    change cropped.carrier sourceIndex =
      pureWZ2DenseCubicalization (source.family.tube sourceIndex)
        ((AffineIsometryEquiv.refl ℝ Point3) ''
          source.shading.carrier index)
    have hindex : index = sourceIndex := Fin.ext rfl
    subst sourceIndex
    simpa using hexact index
  cropped_cubical := hcubical
  line_class := hline
  cropped_top_level_cwa := htopLevel
  final_extremal := hextremal
  ordinary_cell_containment := by
    intro index cell hcell
    rcases hcell with ⟨point, ⟨sourcePoint, hsourcePoint, hpoint⟩, hpointCell⟩
    subst point
    exact hcellContained index cell ⟨sourcePoint, hsourcePoint, hpointCell⟩
  ordinary_bounded_base := hboundedBase

/-- Exact dense-cubicalization equality for the selected ordinary trace. -/
theorem proposition63SelectedTrace_denseCubicalization
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    (ordinary : Kakeya.Streamlined.TubeShading family)
    (cropped : WZ1PaperTubeShading family)
    (selected : Kakeya.Streamlined.TubeSubfamily family)
    (hdelta : 0 < delta)
    (hcubical : WZ1PaperIsCubicalShading cropped)
    (hdenseSubset : ∀ index, cropped.carrier index ⊆
      pureWZ2DenseCubicalization
        (family.tube index) (ordinary.carrier index))
    (hpositive : ∀ index : Fin selected.family.card,
      0 < volume
        ((proposition63SubfamilyOrdinaryTrace ordinary selected
          (restrictPaperShading selected cropped)).carrier index))
    (index : Fin selected.family.card) :
    pureWZ2DenseCubicalization (selected.family.tube index)
        ((proposition63SubfamilyOrdinaryTrace ordinary selected
          (restrictPaperShading selected cropped)).carrier index) =
      (restrictPaperShading selected cropped).carrier index := by
  apply pureWZ2DenseCubicalization_inter_whole_cells
      (selected.family.tube index)
      (ordinary.carrier (selected.embedding index))
      (cropped.carrier (selected.embedding index)) hdelta
  · rw [selected.tube_eq index]
    exact hdenseSubset (selected.embedding index)
  · exact hcubical (selected.embedding index)
  · exact hpositive index

/-- Convert the regularized pure nearby CWA into the exact cropped top-level
constant required by the frozen normalization. -/
theorem proposition63RegularizedTrace_topLevelCWA
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant outputConstant normalizationWeight weightUpper : ENNReal}
    {levelCount : ℕ}
    {externalWeight : Fin family.card → ENNReal}
    (schedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := family) ambientConstant outputConstant levelCount)
    (regularized : WZ2PaperPureExternalWeightRegularizationData
      schedule normalizationWeight weightUpper externalWeight)
    (hdelta : 0 < delta) (hdeltaSmall : delta ≤ 1 / 24)
    (hsupport : regularized.selected.family.IsInUnitBall)
    (targetLoss normalizationLoss : ℝ)
    (habsorb : 4 * outputConstant ≤
      Kakeya.realRpowENN delta (-targetLoss)) :
    WZ2PaperConvexWolffBound regularized.selected.family
      (Kakeya.realRpowENN delta (-targetLoss)) :=
  weaken_convex_wolff_bound
    (pure_nearby_to_top_level hdelta hdeltaSmall hsupport
      regularized.pure_cwa_nearby) habsorb

/-- Transfer an already available cropped top-level CWA through the same
external-weight regularization.  This is the paper-faithful route for the
second Proposition 6.2 call: deleting tubes is paid by the recorded weighted
cardinality retention, with no support property inferred from an abstract
rescaling certificate. -/
theorem proposition63RegularizedTrace_topLevelCWA_from_ambient
    {delta : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {ambientConstant outputConstant normalizationWeight weightUpper
      topLevelConstant targetConstant : ENNReal}
    {levelCount : ℕ}
    {externalWeight : Fin family.card → ENNReal}
    (schedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := family) ambientConstant outputConstant levelCount)
    (regularized : WZ2PaperPureExternalWeightRegularizationData
      schedule normalizationWeight weightUpper externalWeight)
    (hnormalizationZero : normalizationWeight ≠ 0)
    (hnormalizationTop : normalizationWeight ≠ ⊤)
    (hambient : WZ2PaperConvexWolffBound family topLevelConstant)
    (habsorb :
      (normalizationWeight⁻¹ *
          (regularized.regularizationLoss * weightUpper)) *
          topLevelConstant ≤ targetConstant) :
    WZ2PaperConvexWolffBound regularized.selected.family
      targetConstant :=
  weaken_convex_wolff_bound
    (hambient.subfamily_of_weighted_cardinality regularized.selected
      hnormalizationZero hnormalizationTop
      regularized.cardinality_retention) habsorb

/-- Below the logarithmic threshold, a frozen polylogarithmic refinement
factor can be paid without changing an already selected shading. -/
lemma proposition63PureRefinementFraction_mul_le_self
    {delta : ℝ} (normalizationExponent : ℕ)
    (hlog : 1 ≤ Real.log (1 / delta)) (mass : ENNReal) :
    wz2PaperPureRefinementFraction delta normalizationExponent * mass ≤
      mass := by
  have hbase :
      (ENNReal.ofReal (Real.log (1 / delta)))⁻¹ ≤ 1 := by
    apply ENNReal.inv_le_one.mpr
    simpa [ENNReal.one_le_ofReal] using hlog
  have hfraction :
      wz2PaperPureRefinementFraction delta normalizationExponent ≤ 1 := by
    simp only [wz2PaperPureRefinementFraction]
    exact pow_le_one₀ (by positivity) hbase
  calc
    wz2PaperPureRefinementFraction delta normalizationExponent * mass ≤
        1 * mass := by gcongr
    _ = mass := one_mul mass

/-
/-- Construct the exact normalization needed for the second Proposition 6.2
call after trace-weight finite regularization.

The ordinary source is the selected Lemma 4.3 trace, the cropped output is
the corresponding selected Lemma 4.3 shading, and the weak plane map is the
same function.  Pure nearby CWA and cropped top-level CWA are recovered from
the same regularized family with explicit constant absorption. -/
theorem proposition63RegularizedLemma43Normalization
    {delta sigma sourceLoss targetLoss incidenceBudget : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    (lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := sourceLoss)
      (targetLoss := targetLoss) source incidenceBudget)
    (ordinary : Kakeya.Streamlined.TubeShading family)
    {ambientConstant outputConstant normalizationWeight weightUpper : ENNReal}
    {levelCount normalizationExponent : ℕ}
    (schedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := family) ambientConstant outputConstant levelCount)
    (regularized : WZ2PaperPureExternalWeightRegularizationData
      schedule normalizationWeight weightUpper
      (proposition63Lemma43TraceWeight ordinary lemma43.shading))
    (houtput : outputConstant ≤
      Kakeya.realRpowENN delta (-targetLoss))
    (houtputFinite : Kakeya.realRpowENN delta (-targetLoss) ≠ ⊤)
    (htraceLevel :
      Kakeya.realRpowENN delta targetLoss *
          Kakeya.deltaTubeVolume delta ≤ regularized.weightLevel)
    (hpaperLevel : ∀ index : Fin regularized.selected.family.card,
      Kakeya.realRpowENN delta targetLoss *
          volume (wz1PaperTubeCarrier
            (regularized.selected.family.tube index)) ≤
        regularized.weightLevel)
    (hdenseSubset : ∀ index,
      lemma43.shading.carrier index ⊆
        pureWZ2DenseCubicalization
          (family.tube index) (ordinary.carrier index))
    (hline : WZ1PaperIsLineClass family)
    (hsupport : regularized.selected.family.IsInUnitBall)
    (hdeltaSmall : delta ≤ 1 / 24)
    (htopAbsorb :
      4 * Kakeya.realRpowENN delta (-targetLoss) ≤
        Kakeya.realRpowENN delta (-targetLoss))
    (hlog : 1 ≤ Real.log (1 / delta)) :
    let selected := regularized.selected
    let cropped := restrictPaperShading selected lemma43.shading
    let ordinarySource := proposition63RegularizedTraceExtremal
      lemma43 ordinary schedule regularized houtput houtputFinite
      htraceLevel
    let croppedExtremal := proposition63RegularizedCroppedExtremal
      lemma43 ordinary schedule regularized houtput houtputFinite
      hpaperLevel
    ∃ normalized : PureWZ2CroppedCriticalNormalizationData
        (outputLoss := targetLoss) ordinarySource normalizationExponent,
      HEq normalized.croppedRefined
          (lemma43.restrictAsSource selected croppedExtremal).shading ∧
        (lemma43.restrictAsSource selected
          croppedExtremal).planeMap.planeMap =
            lemma43.planeMap.planeMap := by
  let selected := regularized.selected
  let cropped := restrictPaperShading selected lemma43.shading
  let ordinarySource := proposition63RegularizedTraceExtremal
    lemma43 ordinary schedule regularized houtput houtputFinite htraceLevel
  let croppedExtremal := proposition63RegularizedCroppedExtremal
    lemma43 ordinary schedule regularized houtput houtputFinite hpaperLevel
  let restrictedLemma43 :=
    lemma43.restrictAsSource selected croppedExtremal
  have hselectedDense : ∀ index,
      cropped.carrier index ⊆
        pureWZ2DenseCubicalization
          (selected.family.tube index)
          (ordinary.carrier (selected.embedding index)) := by
    intro index point hpoint
    rw [selected.tube_eq index]
    exact hdenseSubset (selected.embedding index) hpoint
  have hexact : ∀ index,
      pureWZ2DenseCubicalization (selected.family.tube index)
          (ordinarySource.shading.carrier index) =
        cropped.carrier index := by
    intro index
    exact pureWZ2DenseCubicalization_inter_whole_cells
      (selected.family.tube index)
      (ordinary.carrier (selected.embedding index))
      (cropped.carrier index) lemma43.extremal.delta_pos
      (hselectedDense index)
      (restrictPaperShading_cubical selected lemma43.cubical index)
      (proposition63RegularizedTrace_volume_pos
        ordinary lemma43.shading schedule regularized index)
  have hdenseTrace : ∀ index, cropped.carrier index ⊆
      pureWZ2DenseCubicalization
        (ordinarySource.family.tube index)
        (ordinarySource.shading.carrier index) := by
    intro index
    exact (hexact index).symm.subset
  have htracePositive : ∀ index,
      0 < volume
        ((proposition63OrdinaryTrace ordinarySource.shading cropped).carrier
          index) := by
    intro index
    change 0 < volume
      (((ordinary.carrier (selected.embedding index) ∩
        cropped.carrier index) ∩ cropped.carrier index))
    rw [show
      (ordinary.carrier (selected.embedding index) ∩
        cropped.carrier index) ∩ cropped.carrier index =
          ordinary.carrier (selected.embedding index) ∩
            cropped.carrier index by
      ext point
      simp only [Set.mem_inter_iff]
      tauto]
    exact proposition63RegularizedTrace_volume_pos
      ordinary lemma43.shading schedule regularized index
  have hretained :
      wz2PaperPureRefinementFraction delta normalizationExponent *
          ordinarySource.shading.mass ≤
        (proposition63OrdinaryTrace ordinarySource.shading cropped).mass := by
    have hself := proposition63PureRefinementFraction_mul_le_self
      normalizationExponent hlog ordinarySource.shading.mass
    exact hself.trans_eq <| by
      apply Finset.sum_congr rfl
      intro index _
      rw [show
        (proposition63OrdinaryTrace ordinarySource.shading cropped).carrier
            index = ordinarySource.shading.carrier index by
        change
          (ordinary.carrier (selected.embedding index) ∩
              cropped.carrier index) ∩ cropped.carrier index =
            ordinary.carrier (selected.embedding index) ∩
              cropped.carrier index
        ext point
        simp only [Set.mem_inter_iff]
        tauto]
  have htopRaw : WZ2PaperConvexWolffBound selected.family
      (4 * Kakeya.realRpowENN delta (-targetLoss)) :=
    pure_nearby_to_top_level lemma43.extremal.delta_pos hdeltaSmall
      hsupport ordinarySource.extremal.cwa_nearby_scales
  have htop : WZ2PaperConvexWolffBound selected.family
      (Kakeya.realRpowENN delta (-targetLoss)) :=
    weaken_convex_wolff_bound htopRaw htopAbsorb
  let normalized := proposition63IdentityDenseNormalization
    normalizationExponent cropped
    (restrictPaperShading_cubical selected lemma43.cubical)
    hdenseTrace htracePositive hretained (hline.subfamily selected)
    htop croppedExtremal
  exact ⟨normalized, HEq.rfl, rfl⟩

/-- Second Proposition 6.2 after finite regularization of the genuine
ordinary trace.  Compared with the lower-level trace theorem, the ordinary
source, selected-family pure CWA, and cropped extremality are all constructed
here from one external-weight regularization certificate. -/
theorem proposition63_paper_lemma44_of_frozen_sticky_regularized
    {sigma stickyLoss outputLoss : ℝ}
    {normalizationExponent logExponent : ℕ}
    (critical : PureWZ2CriticalPackage sigma)
    (hStickyAt :
      PureWZ2CroppedPropStickyAt normalizationExponent logExponent)
    (hstickyLoss : 0 < stickyLoss)
    (hstickyOutput : stickyLoss ≤ outputLoss)
    (houtputLoss : 0 < outputLoss) :
    ∃ sourceLoss normalizationLoss deltaBound : ℝ,
      0 < sourceLoss ∧ 0 < normalizationLoss ∧
      sourceLoss ≤ normalizationLoss / 2 ∧
      normalizationLoss < stickyLoss ∧
      0 < deltaBound ∧ deltaBound ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ deltaBound →
        ∀ rho : WZ2PaperRequestedScale delta,
          Real.rpow delta (1 - stickyLoss) ≤ rho.1 →
          rho.1 ≤ Real.rpow delta stickyLoss →
          ∀ lemma43SourceLoss : ℝ,
            ∀ family : Kakeya.Streamlined.TubeFamily delta,
              ∀ lemma43Source : WZ1PaperTubeShading family,
                ∀ lemma43 : Proposition63Lemma43Data
                  (sigma := sigma)
                  (sourceLoss := lemma43SourceLoss)
                  (targetLoss := inputLoss) lemma43Source
                  (rho.1 / 2),
                  ∀ ordinary : Kakeya.Streamlined.TubeShading family,
                    ∀ ambientConstant outputConstant
                        normalizationWeight weightUpper : ENNReal,
                      ∀ levelCount : ℕ,
                        ∀ schedule : WZ2PaperPureFiniteNearbyScheduleData
                          (fine := family) ambientConstant outputConstant
                          levelCount,
                          ∀ regularized :
                            WZ2PaperPureExternalWeightRegularizationData
                              schedule normalizationWeight weightUpper
                              (proposition63Lemma43TraceWeight
                                ordinary lemma43.shading),
                            outputConstant ≤
                              Kakeya.realRpowENN delta (-inputLoss) →
                            Kakeya.realRpowENN delta (-inputLoss) ≠ ⊤ →
                            Kakeya.realRpowENN delta inputLoss *
                                Kakeya.deltaTubeVolume delta ≤
                              regularized.weightLevel →
                            (∀ index : Fin regularized.selected.family.card,
                              Kakeya.realRpowENN delta inputLoss *
                                  volume (wz1PaperTubeCarrier
                                    (regularized.selected.family.tube
                                      index)) ≤
                                regularized.weightLevel) →
                            (∀ index, lemma43.shading.carrier index ⊆
                              pureWZ2DenseCubicalization
                                (family.tube index)
                                (ordinary.carrier index)) →
                            WZ1PaperIsLineClass family →
                            regularized.selected.family.IsInUnitBall →
                            delta ≤ 1 / 24 →
                            4 * Kakeya.realRpowENN delta (-inputLoss) ≤
                              Kakeya.realRpowENN delta (-inputLoss) →
                            1 ≤ Real.log (1 / delta) →
                            (∀ sticky : PureWZ2PropStickyData
                              (sigma := sigma) (outputLoss := stickyLoss)
                              (restrictPaperShading regularized.selected
                                lemma43.shading) rho logExponent,
                              (Kakeya.realRpowENN rho.1
                                  (2 - sigma - stickyLoss) *
                                sticky.coarse.enncard) *
                                  Kakeya.realRpowENN rho.1 outputLoss ≤
                                Kakeya.realRpowENN rho.1 stickyLoss) →
                              ∃ sticky : PureWZ2PropStickyData
                                  (sigma := sigma)
                                  (outputLoss := stickyLoss)
                                  (restrictPaperShading regularized.selected
                                    lemma43.shading) rho logExponent,
                                Nonempty
                                  (Proposition63Lemma44Data
                                    (lemma43.restrictAsSource
                                      regularized.selected
                                      (proposition63RegularizedCroppedExtremal
                                        lemma43 ordinary schedule regularized
                                        (by assumption) (by assumption)
                                        (by assumption)))
                                    sticky outputLoss) := by
  rcases hStickyAt sigma critical stickyLoss hstickyLoss with
    ⟨inputLoss, deltaBound, hinputLoss, hdeltaBound,
      hdeltaBoundOne, hSticky⟩
  refine ⟨inputLoss, deltaBound, hinputLoss, hdeltaBound,
    hdeltaBoundOne, ?_⟩
  intro delta hdelta hdeltaBound' rho hrhoLower hrhoUpper
    lemma43SourceLoss family lemma43Source lemma43 ordinary
    ambientConstant outputConstant normalizationWeight weightUpper
    levelCount schedule regularized houtput houtputFinite htraceLevel
    hpaperLevel hdenseSubset hline hsupport hdeltaSmall htopAbsorb hlog
    hrestore
  let ordinarySource := proposition63RegularizedTraceExtremal
    lemma43 ordinary schedule regularized houtput houtputFinite htraceLevel
  let croppedExtremal := proposition63RegularizedCroppedExtremal
    lemma43 ordinary schedule regularized houtput houtputFinite hpaperLevel
  let restrictedLemma43 :=
    lemma43.restrictAsSource regularized.selected croppedExtremal
  rcases proposition63RegularizedLemma43Normalization lemma43 ordinary
      schedule regularized houtput houtputFinite htraceLevel hpaperLevel
      hdenseSubset hline hsupport hdeltaSmall htopAbsorb hlog with
    ⟨normalized, hnormalized, _hsameMap⟩
  have hnormalizedEq : normalized.croppedRefined =
      restrictedLemma43.shading := eq_of_heq hnormalized
  rcases hSticky delta hdelta hdeltaBound' ordinarySource normalized rho
      hrhoLower hrhoUpper with ⟨sticky⟩
  rw [hnormalizedEq] at sticky
  exact ⟨sticky, proposition63_paper_lemma44_coarse_pair
    restrictedLemma43 sticky hstickyOutput houtputLoss (hrestore sticky)⟩
-/

/-- Explicit paper-side preparation for the second Proposition 6.2 call.
All fields are quantitative consequences to be discharged by the outer
parameter hierarchy; the dependent objects themselves are fixed here. -/
structure Proposition63RegularizedReentryData
    {delta sigma sourceLoss lemma43Loss incidenceBudget : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    (lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := sourceLoss)
      (targetLoss := lemma43Loss) source incidenceBudget)
    (ordinary : Kakeya.Streamlined.TubeShading family)
    (targetLoss : ℝ)
    (normalizationLoss : ℝ)
    (normalizationExponent : ℕ) where
  ambientConstant : ENNReal
  outputConstant : ENNReal
  normalizationWeight : ENNReal
  weightUpper : ENNReal
  levelCount : ℕ
  schedule : WZ2PaperPureFiniteNearbyScheduleData
    (fine := family) ambientConstant outputConstant levelCount
  regularized : WZ2PaperPureExternalWeightRegularizationData
    schedule normalizationWeight weightUpper
    (proposition63Lemma43TraceWeight ordinary lemma43.shading)
  lemma43_loss_le : lemma43Loss ≤ targetLoss
  target_loss_pos : 0 < targetLoss
  normalization_loss_pos : 0 < normalizationLoss
  target_loss_le_half : targetLoss ≤ normalizationLoss / 2
  normalization_weight_ne_zero : normalizationWeight ≠ 0
  normalization_weight_ne_top : normalizationWeight ≠ ⊤
  output_le : outputConstant ≤
    Kakeya.realRpowENN delta (-targetLoss)
  trace_level :
    Kakeya.realRpowENN delta targetLoss *
        Kakeya.deltaTubeVolume delta ≤ regularized.weightLevel
  dense_level : ∀ index : Fin regularized.selected.family.card,
    Kakeya.realRpowENN delta targetLoss *
        volume (wz1PaperTubeCarrier
          (regularized.selected.family.tube index)) ≤
      (73 / 100 : ENNReal) * regularized.weightLevel
  line_class : WZ1PaperIsLineClass family
  ordinary_axial_window : ∀ index point,
    point ∈ (proposition63SubfamilyOrdinaryTrace ordinary
        regularized.selected
        (restrictPaperShading regularized.selected lemma43.shading)).carrier
          index →
      |point (2 : Fin 3)| ≤ 1 / 4
  ordinary_bounded_base : HasBoundedBase regularized.selected.family 4
  delta_small : delta ≤ 1 / 24
  ambient_top_level_constant : ENNReal
  ambient_top_level_cwa :
    WZ2PaperConvexWolffBound family ambient_top_level_constant
  top_level_absorb :
    (normalizationWeight⁻¹ *
        (regularized.regularizationLoss * weightUpper)) *
        ambient_top_level_constant ≤
      Kakeya.realRpowENN delta (-targetLoss)

/-- Construct the full second-call re-entry package from one finite nearby
schedule and the scalar receipts consumed by external-weight
regularization.  The ordinary axial bound and bounded-base property pass to
the selected subfamily without any new geometric choice. -/
theorem proposition63_regularized_reentry
    {delta sigma sourceLoss lemma43Loss targetLoss normalizationLoss
      incidenceBudget : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    (lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := sourceLoss)
      (targetLoss := lemma43Loss) source incidenceBudget)
    (ordinary : Kakeya.Streamlined.TubeShading family)
    {ambientConstant outputConstant normalizationWeight weightUpper : ENNReal}
    {levelCount normalizationExponent : ℕ}
    (schedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := family) ambientConstant outputConstant levelCount)
    (ambient_cwa : WZ2PaperPureCWAAtNearbyScales family ambientConstant)
    (lemma43_loss_le : lemma43Loss ≤ targetLoss)
    (target_loss_pos : 0 < targetLoss)
    (normalization_loss_pos : 0 < normalizationLoss)
    (target_loss_le_half : targetLoss ≤ normalizationLoss / 2)
    (normalization_weight_ne_zero : normalizationWeight ≠ 0)
    (normalization_weight_ne_top : normalizationWeight ≠ ⊤)
    (weightUpper_ne_top : weightUpper ≠ ⊤)
    (regularization_mass_lower :
      normalizationWeight * family.enncard ≤
        ∑ index : Fin family.card,
          proposition63Lemma43TraceWeight ordinary lemma43.shading index)
    (weight_upper : ∀ index : Fin family.card,
      proposition63Lemma43TraceWeight ordinary lemma43.shading index ≤
        weightUpper)
    (output_finite : WZ2PaperFiniteErrorConstant outputConstant)
    (regularization_absorb :
      let degreeConstant :=
        16 * (schedule.scaleCount : ENNReal) *
          (Nat.log 2 (2 * family.card) + 1 : ENNReal) ^
            schedule.scaleCount
      let regularizationLoss :=
        (8 : ENNReal) *
          (Nat.log 2 (2 * family.card) + 1 : ENNReal) ^
            (schedule.scaleCount + 1)
      max degreeConstant
          ((normalizationWeight⁻¹ *
              (ambientConstant *
                (regularizationLoss * weightUpper) *
                degreeConstant)) *
            ambientConstant) ≤
        outputConstant)
    (output_le : outputConstant ≤
      Kakeya.realRpowENN delta (-targetLoss))
    (trace_scale_absorb :
      4 * (Kakeya.realRpowENN delta targetLoss *
        Kakeya.deltaTubeVolume delta) ≤ normalizationWeight)
    (paper_scale_absorb : ∀ index : Fin family.card,
      4 * (Kakeya.realRpowENN delta targetLoss *
          volume (wz1PaperTubeCarrier (family.tube index))) ≤
        (73 / 100 : ENNReal) * normalizationWeight)
    (line_class : WZ1PaperIsLineClass family)
    (ordinary_axial_window : ∀ index point,
      point ∈ ordinary.carrier index → |point (2 : Fin 3)| ≤ 1 / 4)
    (ordinary_bounded_base : HasBoundedBase family 4)
    (delta_small : delta ≤ 1 / 24)
    (ambient_top_level_constant : ENNReal)
    (ambient_top_level_cwa :
      WZ2PaperConvexWolffBound family ambient_top_level_constant)
    (top_level_absorb :
      (normalizationWeight⁻¹ *
          (((8 : ENNReal) *
              (Nat.log 2 (2 * family.card) + 1 : ENNReal) ^
                (schedule.scaleCount + 1)) * weightUpper)) *
          ambient_top_level_constant ≤
        Kakeya.realRpowENN delta (-targetLoss)) :
    Nonempty (Proposition63RegularizedReentryData
      lemma43 ordinary targetLoss normalizationLoss normalizationExponent) := by
  rcases schedule.regularizeExternalWeight ambient_cwa
      lemma43.extremal.nonempty
      (proposition63Lemma43TraceWeight ordinary lemma43.shading)
      normalization_weight_ne_zero normalization_weight_ne_top
      weightUpper_ne_top regularization_mass_lower weight_upper
      output_finite regularization_absorb with
    ⟨regularized⟩
  have four_ne_zero : (4 : ENNReal) ≠ 0 := by norm_num
  have four_ne_top : (4 : ENNReal) ≠ ⊤ := by norm_num
  have trace_level :
      Kakeya.realRpowENN delta targetLoss *
          Kakeya.deltaTubeVolume delta ≤ regularized.weightLevel := by
    apply (ENNReal.mul_le_mul_iff_right four_ne_zero four_ne_top).mp
    exact trace_scale_absorb.trans
      regularized.normalizationWeight_le_four_weightLevel
  have dense_level : ∀ index : Fin regularized.selected.family.card,
      Kakeya.realRpowENN delta targetLoss *
          volume (wz1PaperTubeCarrier
            (regularized.selected.family.tube index)) ≤
        (73 / 100 : ENNReal) * regularized.weightLevel := by
    intro index
    apply (ENNReal.mul_le_mul_iff_right four_ne_zero four_ne_top).mp
    calc
      4 * (Kakeya.realRpowENN delta targetLoss *
            volume (wz1PaperTubeCarrier
              (regularized.selected.family.tube index))) ≤
          (73 / 100 : ENNReal) * normalizationWeight := by
        rw [regularized.selected.tube_eq]
        exact paper_scale_absorb (regularized.selected.embedding index)
      _ ≤ (73 / 100 : ENNReal) *
          (4 * regularized.weightLevel) := by
        gcongr
        exact regularized.normalizationWeight_le_four_weightLevel
      _ = 4 * ((73 / 100 : ENNReal) * regularized.weightLevel) := by
        ring
  exact ⟨{
    ambientConstant := ambientConstant
    outputConstant := outputConstant
    normalizationWeight := normalizationWeight
    weightUpper := weightUpper
    levelCount := levelCount
    schedule := schedule
    regularized := regularized
    lemma43_loss_le := lemma43_loss_le
    target_loss_pos := target_loss_pos
    normalization_loss_pos := normalization_loss_pos
    target_loss_le_half := target_loss_le_half
    normalization_weight_ne_zero := normalization_weight_ne_zero
    normalization_weight_ne_top := normalization_weight_ne_top
    output_le := output_le
    trace_level := trace_level
    dense_level := dense_level
    line_class := line_class
    ordinary_axial_window := by
      intro index point pointMem
      exact ordinary_axial_window
        (regularized.selected.embedding index) point pointMem.1
    ordinary_bounded_base := fun index => by
      rw [regularized.selected.tube_eq]
      exact ordinary_bounded_base (regularized.selected.embedding index)
    delta_small := delta_small
    ambient_top_level_constant := ambient_top_level_constant
    ambient_top_level_cwa := ambient_top_level_cwa
    top_level_absorb := by
      rw [regularized.regularizationLoss_eq]
      exact top_level_absorb
  }⟩

namespace Proposition63RegularizedReentryData

noncomputable def ordinarySource
    {delta sigma sourceLoss lemma43Loss targetLoss normalizationLoss
      incidenceBudget : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := sourceLoss)
      (targetLoss := lemma43Loss) source incidenceBudget}
    {ordinary : Kakeya.Streamlined.TubeShading family}
    {normalizationExponent : ℕ}
    (data : Proposition63RegularizedReentryData
      lemma43 ordinary targetLoss normalizationLoss normalizationExponent) :
    PureWZ2ExtremalConfiguration sigma targetLoss delta :=
  proposition63RegularizedTraceExtremal lemma43 ordinary data.schedule
    data.regularized data.output_le (by simp [Kakeya.realRpowENN])
    data.lemma43_loss_le data.trace_level

noncomputable def denseShading
    {delta sigma sourceLoss lemma43Loss targetLoss normalizationLoss
      incidenceBudget : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := sourceLoss)
      (targetLoss := lemma43Loss) source incidenceBudget}
    {ordinary : Kakeya.Streamlined.TubeShading family}
    {normalizationExponent : ℕ}
    (data : Proposition63RegularizedReentryData
      lemma43 ordinary targetLoss normalizationLoss normalizationExponent) :
    WZ1PaperTubeShading data.regularized.selected.family :=
  pureWZ2DenseCubicalShading data.ordinarySource.shading

theorem cellContained
    {delta sigma sourceLoss lemma43Loss targetLoss normalizationLoss
      incidenceBudget : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := sourceLoss)
      (targetLoss := lemma43Loss) source incidenceBudget}
    {ordinary : Kakeya.Streamlined.TubeShading family}
    {normalizationExponent : ℕ}
    (data : Proposition63RegularizedReentryData
      lemma43 ordinary targetLoss normalizationLoss normalizationExponent)
    (index : Fin data.regularized.selected.family.card)
    (cell : ℤ × ℤ × ℤ)
    (hcell :
      (data.ordinarySource.shading.carrier index ∩
        wz1PaperGridCube delta cell).Nonempty) :
    wz1PaperGridCube delta cell ⊆
      wz1PaperTubeCarrier
        (data.regularized.selected.family.tube index) := by
  apply pureWZ2GridCube_subset_paperTube_of_sub_cubical
    data.ordinarySource.shading
    (restrictPaperShading data.regularized.selected lemma43.shading)
    (fun _ _ hpoint => hpoint.2)
    (restrictPaperShading_cubical data.regularized.selected lemma43.cubical)
    index cell hcell

theorem denseSubshading
    {delta sigma sourceLoss lemma43Loss targetLoss normalizationLoss
      incidenceBudget : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := sourceLoss)
      (targetLoss := lemma43Loss) source incidenceBudget}
    {ordinary : Kakeya.Streamlined.TubeShading family}
    {normalizationExponent : ℕ}
    (data : Proposition63RegularizedReentryData
      lemma43 ordinary targetLoss normalizationLoss normalizationExponent) :
    PaperIsSubshading data.denseShading
      (restrictPaperShading data.regularized.selected lemma43.shading) := by
  apply pureWZ2DenseCubicalShading_sub_cubical
    data.ordinarySource.shading
    (restrictPaperShading data.regularized.selected lemma43.shading)
    lemma43.extremal.delta_pos
  · intro index point hpoint
    exact hpoint.2
  · exact restrictPaperShading_cubical data.regularized.selected
      lemma43.cubical
  · exact proposition63RegularizedTrace_volume_pos ordinary lemma43.shading
      data.schedule data.regularized

theorem denseMassRetention
    {delta sigma sourceLoss lemma43Loss targetLoss normalizationLoss
      incidenceBudget : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := sourceLoss)
      (targetLoss := lemma43Loss) source incidenceBudget}
    {ordinary : Kakeya.Streamlined.TubeShading family}
    {normalizationExponent : ℕ}
    (data : Proposition63RegularizedReentryData
      lemma43 ordinary targetLoss normalizationLoss normalizationExponent) :
    (73 / 100 : ENNReal) * data.ordinarySource.shading.mass ≤
      (proposition63OrdinaryTrace data.ordinarySource.shading
        data.denseShading).mass := by
  apply pureWZ2DenseCubicalShading_mass_retention
    lemma43.extremal.delta_pos
  · have hsqrt : Real.sqrt 3 ≤ 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
        Real.sqrt_nonneg 3]
    calc
      delta * (1 + Real.sqrt 3) ≤ delta * 3 := by
        apply mul_le_mul_of_nonneg_left (by linarith)
        exact lemma43.extremal.delta_pos.le
      _ ≤ 1 := by nlinarith [data.delta_small]
  · exact data.cellContained

theorem denseCroppedDense
    {delta sigma sourceLoss lemma43Loss targetLoss normalizationLoss
      incidenceBudget : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := sourceLoss)
      (targetLoss := lemma43Loss) source incidenceBudget}
    {ordinary : Kakeya.Streamlined.TubeShading family}
    {normalizationExponent : ℕ}
    (data : Proposition63RegularizedReentryData
      lemma43 ordinary targetLoss normalizationLoss normalizationExponent) :
    data.denseShading.IsLambdaDense
      (Kakeya.realRpowENN delta targetLoss) := by
  rw [Kakeya.Streamlined.Shading.IsLambdaDense]
  change
    Kakeya.realRpowENN delta targetLoss *
        (∑ index : Fin data.regularized.selected.family.card,
          volume (wz1PaperTubeCarrier
            (data.regularized.selected.family.tube index))) ≤
      ∑ index : Fin data.regularized.selected.family.card,
        volume (data.denseShading.carrier index)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro index _
  calc
    Kakeya.realRpowENN delta targetLoss *
          volume (wz1PaperTubeCarrier
            (data.regularized.selected.family.tube index)) ≤
        (73 / 100 : ENNReal) * data.regularized.weightLevel :=
      data.dense_level index
    _ ≤ (73 / 100 : ENNReal) *
          volume (data.ordinarySource.shading.carrier index) := by
      gcongr
      exact (data.regularized.weight_band index).1
    _ ≤ volume (data.denseShading.carrier index) := by
      apply (pureWZ2DenseCubicalization_trace_retention
        lemma43.extremal.delta_pos
        (by
          have hsqrt : Real.sqrt 3 ≤ 2 := by
            nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
              Real.sqrt_nonneg 3]
          calc
            delta * (1 + Real.sqrt 3) ≤ delta * 3 := by
              apply mul_le_mul_of_nonneg_left (by linarith)
              exact lemma43.extremal.delta_pos.le
            _ ≤ 1 := by nlinarith [data.delta_small])
        (data.ordinarySource.family.tube index)
        (data.ordinarySource.shading.carrier index)
        (data.ordinarySource.shading.measurable_carrier index)
        (data.ordinarySource.shading.subset_body index)
        (data.cellContained index)).trans
      exact measure_mono Set.inter_subset_right

theorem croppedExtremal
    {delta sigma sourceLoss lemma43Loss targetLoss normalizationLoss
      incidenceBudget : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := sourceLoss)
      (targetLoss := lemma43Loss) source incidenceBudget}
    {ordinary : Kakeya.Streamlined.TubeShading family}
    {normalizationExponent : ℕ}
    (data : Proposition63RegularizedReentryData
      lemma43 ordinary targetLoss normalizationLoss normalizationExponent) :
    WZ2PaperCroppedIsExtremal sigma targetLoss
      data.regularized.selected.family
      data.denseShading := by
  refine
    { delta_pos := lemma43.extremal.delta_pos
      delta_le_one := lemma43.extremal.delta_le_one
      nonempty := data.regularized.selected_nonempty
      cwa_nearby_scales := data.regularized.pure_cwa_nearby.mono
        data.output_le (by simp [Kakeya.realRpowENN])
      cubical := pureWZ2DenseCubicalShading_cubical
        data.ordinarySource.shading
      dense := data.denseCroppedDense
      volume_upper := ?_ }
  apply (measure_mono ?_).trans
    (lemma43.extremal.mono_loss data.lemma43_loss_le).volume_upper
  rintro point ⟨index, hpoint⟩
  exact ⟨data.regularized.selected.embedding index,
    data.denseSubshading index hpoint⟩

noncomputable def restrictedLemma43
    {delta sigma sourceLoss lemma43Loss targetLoss normalizationLoss
      incidenceBudget : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := sourceLoss)
      (targetLoss := lemma43Loss) source incidenceBudget}
    {ordinary : Kakeya.Streamlined.TubeShading family}
    {normalizationExponent : ℕ}
    (data : Proposition63RegularizedReentryData
      lemma43 ordinary targetLoss normalizationLoss normalizationExponent) :
    Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := targetLoss)
      (targetLoss := targetLoss)
      data.denseShading
      incidenceBudget :=
  lemma43.refineAsSource data.regularized.selected data.denseShading
    data.denseSubshading data.croppedExtremal

/-- The second regularized Lemma 4.3 source is still a genuine subshading of
the original Lemma 4.3 output.  The selected-family embedding is the exact
ancestry map; no geometric enlargement or comparison of unrelated families is
used here. -/
theorem restrictedLemma43_union_subset_source
    {delta sigma sourceLoss lemma43Loss targetLoss normalizationLoss
      incidenceBudget : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := sourceLoss)
      (targetLoss := lemma43Loss) source incidenceBudget}
    {ordinary : Kakeya.Streamlined.TubeShading family}
    {normalizationExponent : ℕ}
    (data : Proposition63RegularizedReentryData
      lemma43 ordinary targetLoss normalizationLoss normalizationExponent) :
    data.restrictedLemma43.shading.union ⊆ source.union := by
  rintro point ⟨index, hpoint⟩
  exact ⟨data.regularized.selected.embedding index,
    lemma43.subshading _ (data.denseSubshading index hpoint)⟩

noncomputable def normalization
    {delta sigma sourceLoss lemma43Loss targetLoss normalizationLoss
      incidenceBudget : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := sourceLoss)
      (targetLoss := lemma43Loss) source incidenceBudget}
    {ordinary : Kakeya.Streamlined.TubeShading family}
    {normalizationExponent : ℕ}
    (data : Proposition63RegularizedReentryData
      lemma43 ordinary targetLoss normalizationLoss normalizationExponent) :
    PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) data.ordinarySource
      normalizationExponent := by
  let selected := data.regularized.selected
  have hlog : 1 ≤ Real.log (1 / delta) := by
    apply (Real.le_log_iff_exp_le (one_div_pos.mpr
      lemma43.extremal.delta_pos)).2
    have htwentyFour : (24 : ℝ) ≤ 1 / delta := by
      apply (le_div_iff₀ lemma43.extremal.delta_pos).2
      nlinarith [data.delta_small]
    exact (Real.exp_one_lt_three.trans (by norm_num)).le.trans htwentyFour
  have hretained :
      wz2PaperPureRefinementFraction delta normalizationExponent *
          data.ordinarySource.shading.mass ≤
        data.ordinarySource.shading.mass :=
    proposition63PureRefinementFraction_mul_le_self
      normalizationExponent hlog data.ordinarySource.shading.mass
  have htopSource : WZ2PaperConvexWolffBound selected.family
      (Kakeya.realRpowENN delta (-targetLoss)) :=
    proposition63RegularizedTrace_topLevelCWA_from_ambient data.schedule
      data.regularized data.normalization_weight_ne_zero
      data.normalization_weight_ne_top data.ambient_top_level_cwa
      data.top_level_absorb
  have htargetLeNormalization : targetLoss ≤ normalizationLoss := by
    linarith [data.target_loss_le_half, data.normalization_loss_pos]
  have htop : WZ2PaperConvexWolffBound selected.family
      (Kakeya.realRpowENN delta (-normalizationLoss)) := by
    apply weaken_convex_wolff_bound htopSource
    apply ENNReal.ofReal_mono
    exact Real.rpow_le_rpow_of_exponent_ge
      lemma43.extremal.delta_pos lemma43.extremal.delta_le_one (by linarith)
  have hcroppedExtremal : WZ2PaperCroppedIsExtremal sigma normalizationLoss
      data.regularized.selected.family data.denseShading :=
    data.croppedExtremal.mono_loss htargetLeNormalization
  apply proposition63IdentityFullOrdinaryNormalization
    (source := data.ordinarySource) data.target_loss_le_half
    normalizationExponent data.denseShading
    (pureWZ2DenseCubicalShading_cubical data.ordinarySource.shading)
  · intro index
    rfl
  · exact hretained
  · intro index
    have htubeVolume :
        volume (data.ordinarySource.family.tube index).carrier =
          Kakeya.deltaTubeVolume delta :=
      tube_volume_scaling.1 delta (data.ordinarySource.family.tube index)
    have hsourceLower : data.regularized.weightLevel ≤
        volume (data.ordinarySource.shading.carrier index) :=
      (data.regularized.weight_band index).1
    calc
      (Kakeya.realRpowENN delta targetLoss / 2) *
            volume (data.ordinarySource.family.tube index).carrier ≤
          Kakeya.realRpowENN delta targetLoss *
            volume (data.ordinarySource.family.tube index).carrier := by
        apply mul_le_mul_right'
        rw [div_eq_mul_inv]
        exact mul_le_of_le_one_right bot_le (by norm_num)
      _ = Kakeya.realRpowENN delta targetLoss *
            Kakeya.deltaTubeVolume delta := by rw [htubeVolume]
      _ ≤ data.regularized.weightLevel := data.trace_level
      _ ≤ volume (data.ordinarySource.shading.carrier index) := hsourceLower
  · exact data.ordinary_axial_window
  · exact data.line_class.subfamily selected
  · exact htop
  · exact hcroppedExtremal
  · exact data.cellContained
  · exact data.ordinary_bounded_base

@[simp] lemma normalization_croppedFamily
    {delta sigma sourceLoss lemma43Loss targetLoss normalizationLoss
      incidenceBudget : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := sourceLoss)
      (targetLoss := lemma43Loss) source incidenceBudget}
    {ordinary : Kakeya.Streamlined.TubeShading family}
    {normalizationExponent : ℕ}
    (data : Proposition63RegularizedReentryData
      lemma43 ordinary targetLoss normalizationLoss normalizationExponent) :
    data.normalization.croppedFamily = data.regularized.selected.family :=
  rfl

@[simp] lemma normalization_croppedRefined
    {delta sigma sourceLoss lemma43Loss targetLoss normalizationLoss
      incidenceBudget : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := sourceLoss)
      (targetLoss := lemma43Loss) source incidenceBudget}
    {ordinary : Kakeya.Streamlined.TubeShading family}
    {normalizationExponent : ℕ}
    (data : Proposition63RegularizedReentryData
      lemma43 ordinary targetLoss normalizationLoss normalizationExponent) :
    data.normalization.croppedRefined = data.restrictedLemma43.shading :=
  rfl

end Proposition63RegularizedReentryData

/--
The exact second-call preparation boundary used by the M9 assembly.

The external-weight regularization and the strict axial margin are stored on
one dependent object.  In particular, the margin refers to the ordinary
trace, frame, selected family, and dense crop of `prepared`; it cannot be
supplied by an unrelated normalized extremizer.  Constructing this record
from the first chart/Lemma 4.3 output is the remaining geometric
localization leaf.
-/
structure Proposition63SecondCallPreparationData
    {delta sigma sourceLoss lemma43Loss incidenceBudget : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    (lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := sourceLoss)
      (targetLoss := lemma43Loss) source incidenceBudget)
    (ordinary : Kakeya.Streamlined.TubeShading family)
    (targetLoss normalizationLoss : ℝ)
    (normalizationExponent : ℕ)
    (rho : WZ2PaperRequestedScale delta) where
  prepared : Proposition63RegularizedReentryData
    lemma43 ordinary targetLoss normalizationLoss normalizationExponent
  root_axial_margin : ∀ index point,
    point ∈
        (prepared.normalization.toPropStickyReentryData
          prepared.target_loss_pos
          prepared.normalization_loss_pos).geometry.frame ''
      (prepared.normalization.toPropStickyReentryData
          prepared.target_loss_pos
          prepared.normalization_loss_pos).geometry.ordinaryRefined.carrier
        index →
      |point (2 : Fin 3)| + rho.1 ≤ 1 / 8

/-- The literal-image `1 / 25` window leaves enough room for one second-call
coarse cell whenever the requested scale is at most `1 / 24`. -/
noncomputable def Proposition63SecondCallPreparationData.ofPrepared
    {delta sigma sourceLoss lemma43Loss targetLoss normalizationLoss
      incidenceBudget : ℝ}
    {family : Kakeya.Streamlined.TubeFamily delta}
    {source : WZ1PaperTubeShading family}
    {lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := sourceLoss)
      (targetLoss := lemma43Loss) source incidenceBudget}
    {ordinary : Kakeya.Streamlined.TubeShading family}
    {normalizationExponent : ℕ}
    {rho : WZ2PaperRequestedScale delta}
    (prepared : Proposition63RegularizedReentryData
      lemma43 ordinary targetLoss normalizationLoss normalizationExponent)
    (ordinary_axial_window : ∀ index point,
      point ∈ ordinary.carrier index → |point (2 : Fin 3)| ≤ 1 / 25)
    (rho_le : rho.1 ≤ 1 / 24) :
    Proposition63SecondCallPreparationData
      lemma43 ordinary targetLoss normalizationLoss normalizationExponent rho := by
  refine { prepared := prepared, root_axial_margin := ?_ }
  intro index point pointMem
  change point ∈ (AffineIsometryEquiv.refl ℝ Point3) ''
      prepared.ordinarySource.shading.carrier index at pointMem
  rcases pointMem with ⟨sourcePoint, sourcePointMem, rfl⟩
  have sourceBound : |sourcePoint (2 : Fin 3)| ≤ 1 / 25 :=
    ordinary_axial_window
      (prepared.regularized.selected.embedding index) sourcePoint
      sourcePointMem.1
  simpa using (show
    |sourcePoint (2 : Fin 3)| + rho.1 ≤ 1 / 8 by
      linarith)

/-- Specialize `ofPrepared` to the exact charted ordinary source coming from
the first normalized metric fibre.  The strict margin is now generated
internally from literal-image provenance and the second requested-scale
bound. -/
noncomputable def Proposition63SecondCallPreparationData.ofChartOrdinarySource
    {sigma initialInputLoss initialOutputLoss fineDelta firstScale
      ordinaryLoss lemma43SourceLoss lemma43Loss targetLoss
      normalizationLoss incidenceBudget : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration
      sigma initialInputLoss fineDelta}
    {initialNormalizationExponent : ℕ}
    (initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := initialOutputLoss) initialSource
      initialNormalizationExponent)
    (selected : Kakeya.Streamlined.TubeSubfamily
      initialNormalized.croppedFamily)
    (finalShading : WZ1PaperTubeShading selected.family)
    (parentTube : Kakeya.DeltaTube firstScale)
    (hfirstScale : 0 < firstScale)
    (parentLine : WZ1PaperTubeInLineClass parentTube)
    (output : WZ2PaperPureRescaledFullFiberOutput
      (sigma := sigma) (loss := ordinaryLoss)
      finalShading parentTube hfirstScale)
    (massLower :
      Kakeya.realRpowENN (fineDelta / firstScale) ordinaryLoss *
            output.rescalingCertificate.publicFamily.toBodyFamily.mass ≤
        (ENNReal.ofReal ((1 / 100 : ℝ) ^ 3) *
            ENNReal.ofReal ((1 / firstScale : ℝ) ^ 2)) *
          (initialNormalized.finalOrdinaryTrace
            selected finalShading).mass)
    (chart : WZ1HorizontalChart)
    {lemma43Source : WZ1PaperTubeShading
      (proposition63ChartOrdinaryExtremalSourceOfTraceMass
        initialNormalized selected finalShading parentTube hfirstScale
        output massLower chart).family}
    {lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := lemma43SourceLoss)
      (targetLoss := lemma43Loss) lemma43Source incidenceBudget}
    {normalizationExponent : ℕ}
    {rho : WZ2PaperRequestedScale (fineDelta / firstScale)}
    (prepared : Proposition63RegularizedReentryData lemma43
      (proposition63ChartOrdinaryExtremalSourceOfTraceMass
        initialNormalized selected finalShading parentTube hfirstScale
        output massLower chart).shading
      targetLoss normalizationLoss normalizationExponent)
    (rho_le : rho.1 ≤ 1 / 24) :
    Proposition63SecondCallPreparationData lemma43
      (proposition63ChartOrdinaryExtremalSourceOfTraceMass
        initialNormalized selected finalShading parentTube hfirstScale
        output massLower chart).shading
      targetLoss normalizationLoss normalizationExponent rho :=
  Proposition63SecondCallPreparationData.ofPrepared prepared
    (proposition63ChartOrdinaryExtremalSourceOfTraceMass_axial_window
      initialNormalized selected finalShading parentTube hfirstScale
      parentLine output massLower chart) rho_le

/-- Quantifier-correct second Proposition 6.2 call from one explicit
trace-regularized re-entry certificate.  The certificate is constructed only
after Node 3 exposes its required input loss. -/
theorem proposition63_paper_lemma44_of_regularized_reentry
    {sigma stickyLoss outputLoss : ℝ}
    {normalizationExponent logExponent : ℕ}
    (critical : PureWZ2CriticalPackage sigma)
    (hStickyAt :
      PureWZ2CroppedPropStickyAt normalizationExponent logExponent)
    (hstickyLoss : 0 < stickyLoss)
    (hstickyOutput : stickyLoss ≤ outputLoss)
    (houtputLoss : 0 < outputLoss) :
    ∃ sourceLoss normalizationLoss deltaBound : ℝ,
      0 < sourceLoss ∧ 0 < normalizationLoss ∧
      sourceLoss ≤ normalizationLoss / 2 ∧
      normalizationLoss < stickyLoss ∧
      0 < deltaBound ∧ deltaBound ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ deltaBound →
        ∀ rho : WZ2PaperRequestedScale delta,
          Real.rpow delta (1 - stickyLoss) ≤ rho.1 →
          rho.1 ≤ Real.rpow delta stickyLoss →
          ∀ lemma43SourceLoss : ℝ,
            ∀ family : Kakeya.Streamlined.TubeFamily delta,
              ∀ lemma43Source : WZ1PaperTubeShading family,
                ∀ lemma43 : Proposition63Lemma43Data
                  (sigma := sigma)
                  (sourceLoss := lemma43SourceLoss)
                  (targetLoss := sourceLoss) lemma43Source
                  (rho.1 / 2),
                  ∀ ordinary : Kakeya.Streamlined.TubeShading family,
                    ∀ prepared : Proposition63RegularizedReentryData
                      lemma43 ordinary sourceLoss normalizationLoss
                        normalizationExponent,
                    (∀ sticky : PureWZ2PropStickyData
                      (sigma := sigma) (outputLoss := stickyLoss)
                      prepared.restrictedLemma43.shading rho logExponent,
                      (Kakeya.realRpowENN rho.1
                          (2 - sigma - stickyLoss) *
                        sticky.coarse.enncard) *
                          Kakeya.realRpowENN rho.1 outputLoss ≤
                        Kakeya.realRpowENN rho.1 stickyLoss) →
                      ∃ sticky : PureWZ2PropStickyData
                          (sigma := sigma) (outputLoss := stickyLoss)
                          prepared.restrictedLemma43.shading rho logExponent,
                        Nonempty
                          (Proposition63Lemma44Data
                            prepared.restrictedLemma43 sticky outputLoss) := by
  rcases hStickyAt sigma critical stickyLoss hstickyLoss with
    ⟨sourceLoss, normalizationLoss, deltaBound, hsourceLoss,
      hnormalizationLoss, hlossGap, hnormalizationSticky,
      hdeltaBound, hdeltaBoundOne, hSticky⟩
  refine ⟨sourceLoss, normalizationLoss, deltaBound, hsourceLoss,
    hnormalizationLoss, hlossGap, hnormalizationSticky, hdeltaBound,
    hdeltaBoundOne, ?_⟩
  intro delta hdelta hdeltaBound' rho hrhoLower hrhoUpper
    lemma43SourceLoss family lemma43Source lemma43 ordinary prepared
    hrestore
  rcases hSticky delta hdelta hdeltaBound' prepared.ordinarySource
      prepared.normalization rho hrhoLower hrhoUpper with ⟨sticky⟩
  have hnormalized := prepared.normalization_croppedRefined
  rw [hnormalized] at sticky
  exact ⟨sticky, proposition63_paper_lemma44_coarse_pair
    prepared.restrictedLemma43 sticky hstickyOutput houtputLoss
    (hrestore sticky)⟩

/-!
The historical same-loss normalization wrappers below are intentionally kept
out of the compiled API.  Node 3 now requires two pre-runtime losses with a
strict half-gap; the active Node 4 route uses the dual-loss regularized re-entry
above and the current-shading re-entry adapters.
-/
/-

/-- The complete dependent input to the second Proposition 6.2 call.

The frozen normalization and the reindexed Lemma 4.3 output are stored in
one record, with the normalization output tied to that exact restricted
shading and with the weak plane-map function preserved. -/
structure Proposition63Lemma43DependentNormalizationData
    {delta sigma sourceLoss targetLoss incidenceBudget : ℝ}
    (ordinarySource :
      PureWZ2ExtremalConfiguration sigma targetLoss delta)
    {lemma43Source : WZ1PaperTubeShading ordinarySource.family}
    (lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := sourceLoss)
      (targetLoss := targetLoss) lemma43Source incidenceBudget)
    (normalizationExponent : ℕ) where
  restrictedLemma43 : Proposition63Lemma43Data
    (sigma := sigma) (sourceLoss := sourceLoss)
    (targetLoss := targetLoss)
    (restrictPaperShading
      (proposition63PositiveTraceSubfamily
        ordinarySource.shading lemma43.shading) lemma43Source)
    incidenceBudget
  normalization : PureWZ2CroppedCriticalNormalizationData
    (outputLoss := targetLoss) ordinarySource normalizationExponent
  selected_eq : normalization.selected =
    proposition63PositiveTraceSubfamily
      ordinarySource.shading lemma43.shading
  ordinary_trace_eq : HEq normalization.ordinaryRefined
    (proposition63SubfamilyOrdinaryTrace ordinarySource.shading
      (proposition63PositiveTraceSubfamily
        ordinarySource.shading lemma43.shading)
      (proposition63PositiveTraceCroppedShading
        ordinarySource.shading lemma43.shading))
  normalized_shading : HEq normalization.croppedRefined
    restrictedLemma43.shading
  same_plane_map : restrictedLemma43.planeMap.planeMap =
    lemma43.planeMap.planeMap

/-- Assemble the dependent normalization from the exact quantitative facts
provided by the Lemma 4.3 pruning and ordinary trace. -/
noncomputable def proposition63Lemma43DependentNormalization
    {delta sigma sourceLoss targetLoss incidenceBudget : ℝ}
    (ordinarySource :
      PureWZ2ExtremalConfiguration sigma targetLoss delta)
    {lemma43Source : WZ1PaperTubeShading ordinarySource.family}
    (lemma43 : Proposition63Lemma43Data
      (sigma := sigma) (sourceLoss := sourceLoss)
      (targetLoss := targetLoss) lemma43Source incidenceBudget)
    (normalizationExponent : ℕ)
    (hdenseSubset : ∀ index,
      lemma43.shading.carrier index ⊆
        pureWZ2DenseCubicalization
          (ordinarySource.family.tube index)
          (ordinarySource.shading.carrier index))
    (hretained :
      wz2PaperPureRefinementFraction delta normalizationExponent *
          ordinarySource.shading.mass ≤
        (proposition63OrdinaryTrace
          ordinarySource.shading lemma43.shading).mass)
    (hreindexedMass :
      lemma43.leftFactor *
          (restrictPaperShading
            (proposition63PositiveTraceSubfamily
              ordinarySource.shading lemma43.shading)
            lemma43Source).mass ≤
        lemma43.rightFactor *
          (proposition63PositiveTraceCroppedShading
            ordinarySource.shading lemma43.shading).mass)
    (hline : WZ1PaperIsLineClass
      (proposition63PositiveTraceSubfamily
        ordinarySource.shading lemma43.shading).family)
    (htopLevel : WZ2PaperConvexWolffBound
      (proposition63PositiveTraceSubfamily
        ordinarySource.shading lemma43.shading).family
      (Kakeya.realRpowENN delta (-targetLoss)))
    (hextremal : WZ2PaperCroppedIsExtremal sigma targetLoss
      (proposition63PositiveTraceSubfamily
        ordinarySource.shading lemma43.shading).family
      (proposition63PositiveTraceCroppedShading
        ordinarySource.shading lemma43.shading)) :
    Proposition63Lemma43DependentNormalizationData
      ordinarySource lemma43 normalizationExponent := by
  let selected := proposition63PositiveTraceSubfamily
    ordinarySource.shading lemma43.shading
  let cropped := proposition63PositiveTraceCroppedShading
    ordinarySource.shading lemma43.shading
  let restrictedLemma43 := lemma43.restrictSubfamily
    selected hreindexedMass hextremal
  have hrestrictedDense : ∀ index,
      cropped.carrier index ⊆
        pureWZ2DenseCubicalization
          (selected.family.tube index)
          (ordinarySource.shading.carrier (selected.embedding index)) := by
    intro index point hpoint
    rw [selected.tube_eq index]
    exact hdenseSubset (selected.embedding index) hpoint
  have hretainedSelected :
      wz2PaperPureRefinementFraction delta normalizationExponent *
          ordinarySource.shading.mass ≤
        (proposition63SubfamilyOrdinaryTrace
          ordinarySource.shading selected cropped).mass := by
    rw [proposition63PositiveTrace_mass_eq]
    exact hretained
  let normalization := proposition63SubfamilyDenseNormalization
    normalizationExponent selected cropped
    (restrictPaperShading_cubical selected lemma43.cubical)
    hrestrictedDense
    (proposition63PositiveTrace_volume_pos
      ordinarySource.shading lemma43.shading)
    hretainedSelected hline htopLevel hextremal
  exact
    { restrictedLemma43 := restrictedLemma43
      normalization := normalization
      selected_eq := rfl
      ordinary_trace_eq := HEq.rfl
      normalized_shading := HEq.rfl
      same_plane_map := rfl }

/-- Quantifier-correct second use of the frozen Proposition 6.2 interface.

The input loss chosen by `hStickyAt` is exposed before the caller constructs
the Lemma 4.3 output.  Thus the caller can arrange that the latter is
extremal at exactly this loss and can build the dependent normalization on
that actual output.  This is the paper order; no equality between two
independently chosen losses is assumed. -/
theorem proposition63_paper_lemma44_of_frozen_sticky
    {sigma stickyLoss outputLoss : ℝ}
    {normalizationExponent logExponent : ℕ}
    (critical : PureWZ2CriticalPackage sigma)
    (hStickyAt :
      PureWZ2CroppedPropStickyAt normalizationExponent logExponent)
    (hstickyLoss : 0 < stickyLoss)
    (hstickyOutput : stickyLoss ≤ outputLoss)
    (houtputLoss : 0 < outputLoss) :
    ∃ inputLoss deltaBound : ℝ,
      0 < inputLoss ∧
      0 < deltaBound ∧ deltaBound ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ deltaBound →
        ∀ source : PureWZ2ExtremalConfiguration sigma inputLoss delta,
          ∀ normalized : PureWZ2CroppedCriticalNormalizationData
              (outputLoss := inputLoss) source normalizationExponent,
            ∀ rho : WZ2PaperRequestedScale delta,
              Real.rpow delta (1 - stickyLoss) ≤ rho.1 →
              rho.1 ≤ Real.rpow delta stickyLoss →
              ∀ lemma43SourceLoss : ℝ,
                ∀ lemma43Source :
                    WZ1PaperTubeShading normalized.croppedFamily,
                ∀ lemma43 : Proposition63Lemma43Data
                  (sigma := sigma) (sourceLoss := lemma43SourceLoss)
                  (targetLoss := inputLoss) lemma43Source
                  (rho.1 / 2),
                  normalized.croppedRefined = lemma43.shading →
                  (∀ sticky : PureWZ2PropStickyData
                    (sigma := sigma) (outputLoss := stickyLoss)
                    lemma43.shading rho logExponent,
                    (Kakeya.realRpowENN rho.1
                        (2 - sigma - stickyLoss) *
                      sticky.coarse.enncard) *
                        Kakeya.realRpowENN rho.1 outputLoss ≤
                      Kakeya.realRpowENN rho.1 stickyLoss) →
                    ∃ sticky : PureWZ2PropStickyData
                        (sigma := sigma) (outputLoss := stickyLoss)
                        lemma43.shading rho logExponent,
                      Nonempty
                        (Proposition63Lemma44Data
                          lemma43 sticky outputLoss) := by
  rcases hStickyAt sigma critical stickyLoss hstickyLoss with
    ⟨inputLoss, deltaBound, hinputLoss, hdeltaBound,
      hdeltaBoundOne, hSticky⟩
  refine ⟨inputLoss, deltaBound, hinputLoss, hdeltaBound,
    hdeltaBoundOne, ?_⟩
  intro delta hdelta hdeltaBound' source normalized rho
    hrhoLower hrhoUpper lemma43SourceLoss lemma43Source lemma43
    hnormalizedShading hrestore
  rcases hSticky delta hdelta hdeltaBound' source normalized rho
      hrhoLower hrhoUpper with ⟨sticky⟩
  rw [hnormalizedShading] at sticky
  exact ⟨sticky, proposition63_paper_lemma44_coarse_pair
    lemma43 sticky hstickyOutput houtputLoss (hrestore sticky)⟩

/-- The paper-faithful second Proposition 6.2 call on the actual Lemma 4.3
output.

Node 3 first chooses `inputLoss`.  Only then does the caller provide an
ordinary extremal source at that loss, the genuine Lemma 4.3 output, and the
quantitative trace facts.  The theorem deletes precisely the zero-trace
tubes, restricts the same weak plane map, constructs the frozen
normalization, invokes sticky at the requested scale, and finally applies
Lemma 4.4. -/
theorem proposition63_paper_lemma44_of_frozen_sticky_trace
    {sigma stickyLoss outputLoss : ℝ}
    {normalizationExponent logExponent : ℕ}
    (critical : PureWZ2CriticalPackage sigma)
    (hStickyAt :
      PureWZ2CroppedPropStickyAt normalizationExponent logExponent)
    (hstickyLoss : 0 < stickyLoss)
    (hstickyOutput : stickyLoss ≤ outputLoss)
    (houtputLoss : 0 < outputLoss) :
    ∃ inputLoss deltaBound : ℝ,
      0 < inputLoss ∧
      0 < deltaBound ∧ deltaBound ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ deltaBound →
        ∀ ordinarySource :
            PureWZ2ExtremalConfiguration sigma inputLoss delta,
          ∀ rho : WZ2PaperRequestedScale delta,
            Real.rpow delta (1 - stickyLoss) ≤ rho.1 →
            rho.1 ≤ Real.rpow delta stickyLoss →
            ∀ lemma43SourceLoss : ℝ,
              ∀ lemma43Source :
                  WZ1PaperTubeShading ordinarySource.family,
                ∀ lemma43 : Proposition63Lemma43Data
                  (sigma := sigma)
                  (sourceLoss := lemma43SourceLoss)
                  (targetLoss := inputLoss) lemma43Source
                  (rho.1 / 2),
                  (∀ index,
                    lemma43.shading.carrier index ⊆
                      pureWZ2DenseCubicalization
                        (ordinarySource.family.tube index)
                        (ordinarySource.shading.carrier index)) →
                  wz2PaperPureRefinementFraction delta
                        normalizationExponent *
                      ordinarySource.shading.mass ≤
                    (proposition63OrdinaryTrace
                      ordinarySource.shading lemma43.shading).mass →
                  ∀ hreindexedMass : lemma43.leftFactor *
                        (restrictPaperShading
                          (proposition63PositiveTraceSubfamily
                            ordinarySource.shading lemma43.shading)
                          lemma43Source).mass ≤
                      lemma43.rightFactor *
                        (proposition63PositiveTraceCroppedShading
                          ordinarySource.shading lemma43.shading).mass,
                  WZ1PaperIsLineClass
                    (proposition63PositiveTraceSubfamily
                      ordinarySource.shading lemma43.shading).family →
                  WZ2PaperConvexWolffBound
                    (proposition63PositiveTraceSubfamily
                      ordinarySource.shading lemma43.shading).family
                    (Kakeya.realRpowENN delta (-inputLoss)) →
                  ∀ hextremal : WZ2PaperCroppedIsExtremal sigma inputLoss
                    (proposition63PositiveTraceSubfamily
                      ordinarySource.shading lemma43.shading).family
                    (proposition63PositiveTraceCroppedShading
                      ordinarySource.shading lemma43.shading),
                  (∀ sticky : PureWZ2PropStickyData
                    (sigma := sigma) (outputLoss := stickyLoss)
                    (proposition63PositiveTraceCroppedShading
                      ordinarySource.shading lemma43.shading)
                    rho logExponent,
                    (Kakeya.realRpowENN rho.1
                        (2 - sigma - stickyLoss) *
                      sticky.coarse.enncard) *
                        Kakeya.realRpowENN rho.1 outputLoss ≤
                      Kakeya.realRpowENN rho.1 stickyLoss) →
                    ∃ sticky : PureWZ2PropStickyData
                        (sigma := sigma) (outputLoss := stickyLoss)
                        (proposition63PositiveTraceCroppedShading
                          ordinarySource.shading lemma43.shading)
                        rho logExponent,
                      let restrictedLemma43 :=
                        lemma43.restrictSubfamily
                            (proposition63PositiveTraceSubfamily
                              ordinarySource.shading lemma43.shading)
                            hreindexedMass hextremal
                      Nonempty
                        (Proposition63Lemma44Data
                          restrictedLemma43 sticky outputLoss) := by
  rcases hStickyAt sigma critical stickyLoss hstickyLoss with
    ⟨inputLoss, deltaBound, hinputLoss, hdeltaBound,
      hdeltaBoundOne, hSticky⟩
  refine ⟨inputLoss, deltaBound, hinputLoss, hdeltaBound,
    hdeltaBoundOne, ?_⟩
  intro delta hdelta hdeltaBound' ordinarySource rho
    hrhoLower hrhoUpper lemma43SourceLoss lemma43Source lemma43
    hdenseSubset hretained hreindexedMass hline htopLevel
    hextremal hrestore
  let selected := proposition63PositiveTraceSubfamily
    ordinarySource.shading lemma43.shading
  let cropped := proposition63PositiveTraceCroppedShading
    ordinarySource.shading lemma43.shading
  let restrictedLemma43 := lemma43.restrictSubfamily
    selected hreindexedMass hextremal
  have hrestrictedDense : ∀ index,
      cropped.carrier index ⊆
        pureWZ2DenseCubicalization
          (selected.family.tube index)
          (ordinarySource.shading.carrier (selected.embedding index)) := by
    intro index point hpoint
    rw [selected.tube_eq index]
    exact hdenseSubset (selected.embedding index) hpoint
  have hretainedSelected :
      wz2PaperPureRefinementFraction delta normalizationExponent *
          ordinarySource.shading.mass ≤
        (proposition63SubfamilyOrdinaryTrace
          ordinarySource.shading selected cropped).mass := by
    rw [proposition63PositiveTrace_mass_eq]
    exact hretained
  let normalization := proposition63SubfamilyDenseNormalization
    normalizationExponent selected cropped
    (restrictPaperShading_cubical selected lemma43.cubical)
    hrestrictedDense
    (proposition63PositiveTrace_volume_pos
      ordinarySource.shading lemma43.shading)
    hretainedSelected hline htopLevel hextremal
  rcases hSticky delta hdelta hdeltaBound' ordinarySource
      normalization rho hrhoLower hrhoUpper with ⟨sticky⟩
  refine ⟨sticky, ?_⟩
  exact proposition63_paper_lemma44_coarse_pair restrictedLemma43 sticky
    hstickyOutput houtputLoss (hrestore sticky)

-/

end Kakeya.Assouad.PureWZ2

end
