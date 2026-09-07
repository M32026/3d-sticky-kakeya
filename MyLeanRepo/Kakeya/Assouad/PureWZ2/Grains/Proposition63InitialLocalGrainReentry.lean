import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.PropertyThreeSelectedLocalGrain
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63StickyReentry
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.Proposition63RichStickyKernel
import MyLeanRepo.Kakeya.Assouad.PureWZ2.Grains.FiniteIntervalGridOneScaleLocalAD
import MyLeanRepo.Kakeya.Assouad.PropStickyPaperShadingMassUpper

/-!
# Initial local-grain re-entry for Proposition 6.3

The preliminary Lemmas 4.8/4.12 step precedes the first use of Proposition
6.2.  Its local-grain refinement is therefore converted back to an ordinary
critical source before stickiness is invoked.  This file implements the same
ordinary-trace, whole-tube regularization, and exact dense normalization used
later for the Lemma 4.3 re-entry, but without introducing a Lemma 4.3 object.
-/

noncomputable section

namespace Kakeya.Assouad.PureWZ2

open MeasureTheory Set

/-- Quantitative ordinary-trace preparation of a current cropped shading for
one fresh Proposition 6.2 call.  This record deliberately does not assume
that the current shading already carries every-scale local grains: during the
paper's finite Lemma 4.12 iteration it is also used after only finitely many
scales have been established. -/
structure Proposition63CurrentShadingReentryData
    {delta sigma initialInputLoss normalizationLoss reentryLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    (initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent)
    (current : WZ1PaperTubeShading initialNormalized.croppedFamily) where
  ambientConstant : ENNReal
  outputConstant : ENNReal
  normalizationWeight : ENNReal
  weightUpper : ENNReal
  levelCount : ℕ
  schedule : WZ2PaperPureFiniteNearbyScheduleData
    (fine := initialNormalized.croppedFamily) ambientConstant outputConstant
      levelCount
  regularized : WZ2PaperPureExternalWeightRegularizationData
    schedule normalizationWeight weightUpper
      (proposition63Lemma43TraceWeight
        (initialNormalized.finalOrdinaryTrace
          (proposition63IdentitySubfamily initialNormalized.croppedFamily)
          current) current)
  reentry_extremal : WZ2PaperCroppedIsExtremal sigma reentryLoss
    initialNormalized.croppedFamily current
  reentryNormalizationLoss : ℝ
  reentry_normalization_loss_pos : 0 < reentryNormalizationLoss
  reentry_loss_le_half : reentryLoss ≤ reentryNormalizationLoss / 2
  normalization_weight_ne_zero : normalizationWeight ≠ 0
  normalization_weight_ne_top : normalizationWeight ≠ ⊤
  weightUpper_ne_top : weightUpper ≠ ⊤
  output_le : outputConstant ≤
    Kakeya.realRpowENN delta (-reentryLoss)
  trace_level :
    Kakeya.realRpowENN delta reentryLoss *
        Kakeya.deltaTubeVolume delta ≤ regularized.weightLevel
  dense_level : ∀ index : Fin regularized.selected.family.card,
    Kakeya.realRpowENN delta reentryLoss *
        volume (wz1PaperTubeCarrier
          (regularized.selected.family.tube index)) ≤
      (73 / 100 : ENNReal) * regularized.weightLevel
  current_sub_normalized : PaperIsSubshading current
    initialNormalized.croppedRefined
  current_cubical : WZ1PaperIsCubicalShading current
  current_trace_mass :
    normalizationWeight * current.mass ≤
      (proposition63OrdinaryTrace
        (initialNormalized.finalOrdinaryTrace
          (proposition63IdentitySubfamily initialNormalized.croppedFamily)
          current) current).mass
  line_class : WZ1PaperIsLineClass initialNormalized.croppedFamily
  delta_small : delta ≤ 1 / 24
  ambient_top_level_constant : ENNReal
  ambient_top_level_cwa : WZ2PaperConvexWolffBound
    initialNormalized.croppedFamily ambient_top_level_constant
  top_level_absorb :
    (normalizationWeight⁻¹ *
        (regularized.regularizationLoss * weightUpper)) *
        ambient_top_level_constant ≤
      Kakeya.realRpowENN delta (-reentryLoss)

/-- Backwards-compatible specialization used at the first re-entry.  The
local-grain payload is intentionally phantom: it is restricted only after
the generic current-shading re-entry has completed. -/
abbrev Proposition63InitialLocalGrainReentryData
    {delta sigma initialInputLoss normalizationLoss reentryLoss localLoss
      localIncidence : ℝ}
    {L : NNReal}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    (initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent)
    (localShading : WZ1PaperTubeShading initialNormalized.croppedFamily)
    (_localGrains : Proposition63InitialWeakLocalGrainData
      (incidence := localIncidence) localShading sigma
      (Kakeya.realRpowENN delta (-localLoss)) L) :=
  Proposition63CurrentShadingReentryData
    (reentryLoss := reentryLoss) initialNormalized localShading

/-- The exact-family ordinary trace underlying a current-shading re-entry.
Naming it separately hides the dependent index cast introduced by the
identity subfamily. -/
noncomputable def proposition63CurrentOrdinaryTrace
    {delta sigma initialInputLoss normalizationLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    (initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent)
    (current : WZ1PaperTubeShading initialNormalized.croppedFamily) :
    Kakeya.Streamlined.TubeShading initialNormalized.croppedFamily :=
  initialNormalized.finalOrdinaryTrace
    (proposition63IdentitySubfamily initialNormalized.croppedFamily) current

/-- The extra geometric provenance needed by Proposition 6.3 from its
initial critical normalization.  This is deliberately a companion record,
not a change to the frozen Node 3 normalization API. -/
structure Proposition63NormalizationTraceProvenance
    {delta sigma initialInputLoss normalizationLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    (initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent) :
    Prop where
  ordinary_cell_containment :
    ∀ index (cell : ℤ × ℤ × ℤ),
      ((initialNormalized.frame ''
            initialNormalized.ordinaryRefined.carrier index) ∩
          wz1PaperGridCube delta cell).Nonempty →
        wz1PaperGridCube delta cell ⊆
          wz1PaperTubeCarrier
            (initialNormalized.croppedFamily.tube
              (initialNormalized.indexEquiv index))

/-- The initial dense crop retains a fixed fraction of the ordinary mass
whenever the normalization carries the genuine cell-containment provenance.
This is the aggregate overlap certificate needed to start finite re-entry. -/
theorem proposition63_initial_normalization_trace_mass_lower
    {delta sigma initialInputLoss normalizationLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    (initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent)
    (provenance : Proposition63NormalizationTraceProvenance
      initialNormalized)
    (hdeltaSmall : delta * (1 + Real.sqrt 3) ≤ 1) :
    (73 / 100 : ENNReal) * initialNormalized.ordinaryRefined.mass ≤
      (proposition63CurrentOrdinaryTrace initialNormalized
        initialNormalized.croppedRefined).mass := by
  have hperTube :
      ∀ index : Fin initialNormalized.croppedFamily.card,
        (73 / 100 : ENNReal) *
            volume (initialNormalized.frame ''
              initialNormalized.ordinaryRefined.carrier
                (initialNormalized.indexEquiv.symm index)) ≤
          volume ((proposition63CurrentOrdinaryTrace initialNormalized
            initialNormalized.croppedRefined).carrier index) := by
    intro index
    let ordinary := initialNormalized.indexEquiv.symm index
    have hindex : initialNormalized.indexEquiv ordinary = index :=
      initialNormalized.indexEquiv.apply_symm_apply index
    have hsourceSubset :
        initialNormalized.frame ''
            initialNormalized.ordinaryRefined.carrier ordinary ⊆
          (initialNormalized.croppedFamily.tube index).carrier := by
      rw [← hindex, initialNormalized.ordinary_carrier_image_eq ordinary]
      exact Set.image_mono
        (initialNormalized.ordinaryRefined.subset_body ordinary)
    have hretained := pureWZ2DenseCubicalization_trace_retention
      initialSource.extremal.delta_pos hdeltaSmall
      (initialNormalized.croppedFamily.tube index)
      (initialNormalized.frame ''
        initialNormalized.ordinaryRefined.carrier ordinary)
      (by
        let measurableFrame : Point3 ≃ᵐ Point3 :=
          { toFun := initialNormalized.frame
            invFun := initialNormalized.frame.symm
            left_inv := initialNormalized.frame.left_inv
            right_inv := initialNormalized.frame.right_inv
            measurable_toFun :=
              initialNormalized.frame.continuous_of_finiteDimensional.measurable
            measurable_invFun :=
              initialNormalized.frame.symm.continuous_of_finiteDimensional.measurable }
        exact (measurableFrame.measurableSet_image).mpr
          (initialNormalized.ordinaryRefined.measurable_carrier ordinary))
      hsourceSubset
      (by
        intro cell hcell
        simpa only [hindex] using
          provenance.ordinary_cell_containment ordinary cell hcell)
    have hdenseEq :=
      initialNormalized.cropped_carrier_eq_dense_cubicalization ordinary
    rw [hindex] at hdenseEq
    change
      (73 / 100 : ENNReal) *
            volume (initialNormalized.frame ''
              initialNormalized.ordinaryRefined.carrier ordinary) ≤
        volume
          ((initialNormalized.frame ''
              initialNormalized.ordinaryRefined.carrier ordinary) ∩
            initialNormalized.croppedRefined.carrier index)
    rwa [hdenseEq]
  change
    (73 / 100 : ENNReal) *
          (∑ ordinary : Fin initialNormalized.selected.family.card,
            volume (initialNormalized.ordinaryRefined.carrier ordinary)) ≤
      ∑ index : Fin initialNormalized.croppedFamily.card,
        volume ((proposition63CurrentOrdinaryTrace initialNormalized
          initialNormalized.croppedRefined).carrier index)
  rw [Finset.mul_sum]
  calc
    (∑ ordinary : Fin initialNormalized.selected.family.card,
        (73 / 100 : ENNReal) *
          volume (initialNormalized.ordinaryRefined.carrier ordinary)) =
      ∑ ordinary : Fin initialNormalized.selected.family.card,
        (73 / 100 : ENNReal) *
          volume (initialNormalized.frame ''
            initialNormalized.ordinaryRefined.carrier ordinary) := by
        apply Finset.sum_congr rfl
        intro ordinary _
        rw [Kakeya.Streamlined.AffineIsometryEquiv.volume_image
          initialNormalized.frame
          (initialNormalized.ordinaryRefined.carrier ordinary)
          (initialNormalized.ordinaryRefined.measurable_carrier ordinary)]
    _ = ∑ index : Fin initialNormalized.croppedFamily.card,
        (73 / 100 : ENNReal) *
          volume (initialNormalized.frame ''
            initialNormalized.ordinaryRefined.carrier
              (initialNormalized.indexEquiv.symm index)) := by
        exact (Equiv.sum_comp initialNormalized.indexEquiv.symm _).symm
    _ ≤ ∑ index : Fin initialNormalized.croppedFamily.card,
        volume ((proposition63CurrentOrdinaryTrace initialNormalized
          initialNormalized.croppedRefined).carrier index) :=
      Finset.sum_le_sum fun index _ => hperTube index

/-- The canonical aggregate ordinary-trace density available at the initial
normalization.  Its factors are, in order, dense-cell trace retention,
normalization mass retention, the original extremal density, and one ordinary
tube volume. -/
def proposition63InitialTraceAverage
    {delta sigma initialInputLoss normalizationLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    (_initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent) :
    ENNReal :=
  (73 / 100 : ENNReal) *
    wz2PaperPureRefinementFraction delta normalizationExponent *
      Kakeya.realRpowENN delta initialInputLoss *
        Kakeya.deltaTubeVolume delta

/-- A provenance-correct initial normalization supplies the aggregate trace
average needed for the first current-shading re-entry. -/
theorem proposition63_initial_trace_average_lower
    {delta sigma initialInputLoss normalizationLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    (initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent)
    (provenance : Proposition63NormalizationTraceProvenance
      initialNormalized)
    (hdeltaSmall : delta * (1 + Real.sqrt 3) ≤ 1) :
    proposition63InitialTraceAverage initialNormalized *
        initialNormalized.croppedFamily.enncard ≤
      (proposition63CurrentOrdinaryTrace initialNormalized
        initialNormalized.croppedRefined).mass := by
  have hselectedCard :
      initialNormalized.selected.family.enncard =
        initialNormalized.croppedFamily.enncard := by
    simp only [Kakeya.Streamlined.TubeFamily.enncard]
    simpa using Fintype.card_congr initialNormalized.indexEquiv
  have hcroppedCard : initialNormalized.croppedFamily.enncard ≤
      initialSource.family.enncard := by
    rw [← hselectedCard]
    exact tubeSubfamily_enncard_le initialNormalized.selected
  have hsourceDensity :
      Kakeya.realRpowENN delta initialInputLoss *
          (initialSource.family.enncard * Kakeya.deltaTubeVolume delta) ≤
        initialSource.shading.mass := by
    rw [← Kakeya.Streamlined.TubeFamily.nominalMass,
      ← tubeFamily_mass_eq_nominal]
    exact initialSource.extremal.dense
  have hcroppedDensity :
      Kakeya.realRpowENN delta initialInputLoss *
          (initialNormalized.croppedFamily.enncard *
            Kakeya.deltaTubeVolume delta) ≤
        initialSource.shading.mass := by
    apply le_trans ?_ hsourceDensity
    gcongr
  calc
    proposition63InitialTraceAverage initialNormalized *
          initialNormalized.croppedFamily.enncard =
        (73 / 100 : ENNReal) *
          wz2PaperPureRefinementFraction delta normalizationExponent *
            (Kakeya.realRpowENN delta initialInputLoss *
              (initialNormalized.croppedFamily.enncard *
                Kakeya.deltaTubeVolume delta)) := by
      simp only [proposition63InitialTraceAverage]
      ring
    _ ≤ (73 / 100 : ENNReal) *
          (wz2PaperPureRefinementFraction delta normalizationExponent *
            initialSource.shading.mass) := by
      have hscaled := mul_le_mul_left'
        (mul_le_mul_left' hcroppedDensity
          (wz2PaperPureRefinementFraction delta normalizationExponent))
        (73 / 100 : ENNReal)
      simpa only [mul_assoc] using hscaled
    _ ≤ (73 / 100 : ENNReal) *
          initialNormalized.ordinaryRefined.mass := by
      gcongr
      exact initialNormalized.retained_mass
    _ ≤ (proposition63CurrentOrdinaryTrace initialNormalized
          initialNormalized.croppedRefined).mass :=
      proposition63_initial_normalization_trace_mass_lower
        initialNormalized provenance hdeltaSmall

/-- Intersecting the current ordinary trace with the same current cropped
shading a second time does not change its mass. -/
lemma proposition63CurrentOrdinaryTrace_idem_mass
    {delta sigma initialInputLoss normalizationLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    (initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent)
    (current : WZ1PaperTubeShading initialNormalized.croppedFamily) :
    (proposition63OrdinaryTrace
        (proposition63CurrentOrdinaryTrace initialNormalized current)
        current).mass =
      (proposition63CurrentOrdinaryTrace initialNormalized current).mass := by
  apply Finset.sum_congr rfl
  intro index _
  have hcarrier :
      (proposition63OrdinaryTrace
          (proposition63CurrentOrdinaryTrace initialNormalized current)
          current).carrier index =
        (proposition63CurrentOrdinaryTrace initialNormalized current).carrier
          index := by
    ext point
    simp only [proposition63OrdinaryTrace_carrier, Set.mem_inter_iff]
    constructor
    · exact fun pointMem => pointMem.1
    · intro pointMem
      exact ⟨pointMem, pointMem.2⟩
  rw [hcarrier]

/-- Each ordinary-trace external weight is bounded by the uniform paper-tube
carrier volume.  This removes the only current-shading-dependent upper-bound
input from the finite external-weight regularizer. -/
theorem proposition63_current_trace_weight_upper
    {delta sigma initialInputLoss normalizationLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    (initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent)
    (current : WZ1PaperTubeShading initialNormalized.croppedFamily)
    (delta_small : delta ≤ 1 / 24)
    (index : Fin initialNormalized.croppedFamily.card) :
    proposition63Lemma43TraceWeight
        (proposition63CurrentOrdinaryTrace initialNormalized current)
        current index ≤
      (55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
        Kakeya.realRpowENN delta 2 := by
  have traceSubset :
      (proposition63OrdinaryTrace
        (proposition63CurrentOrdinaryTrace initialNormalized current)
        current).carrier index ⊆
      wz1PaperTubeCarrier (initialNormalized.croppedFamily.tube index) := by
    intro point pointMem
    exact current.subset_body index pointMem.2
  exact (measure_mono traceSubset).trans
    ((wz2PaperTubeCarrier_convex_and_volume_quadratic
      wz2_paper_tube_carrier_geometry initialSource.extremal.delta_pos
      delta_small (initialNormalized.croppedFamily.tube index)
      (initialNormalized.line_class index)).2)

/-- The normalization's synchronized per-tube ordinary density gives the
aggregate current-trace lower bound needed by re-entry.  The scalar
`normalizationWeight` may be any value absorbed by the universal trace loss
`100⁻¹ * density`. -/
theorem proposition63_current_trace_mass_of_per_tube_density
    {delta sigma initialInputLoss normalizationLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    (initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent)
    (current : WZ1PaperTubeShading initialNormalized.croppedFamily)
    (current_sub_normalized : PaperIsSubshading current
      initialNormalized.croppedRefined)
    (current_cubical : WZ1PaperIsCubicalShading current)
    (density normalizationWeight : ENNReal)
    (ordinaryPerTube :
      ∀ index : Fin initialNormalized.croppedFamily.card,
        density *
            volume (initialNormalized.croppedFamily.tube index).carrier ≤
          volume (initialNormalized.frame ''
            initialNormalized.ordinaryRefined.carrier
              (PureWZ2CroppedCriticalNormalizationData.ordinaryIndex
                initialNormalized
                (proposition63IdentitySubfamily
                  initialNormalized.croppedFamily) index)))
    (normalizationWeight_le :
      normalizationWeight ≤ (100 : ENNReal)⁻¹ * density) :
    normalizationWeight * current.mass ≤
      (proposition63OrdinaryTrace
        (proposition63CurrentOrdinaryTrace initialNormalized current)
        current).mass := by
  rw [proposition63CurrentOrdinaryTrace_idem_mass]
  apply (mul_le_mul_right' normalizationWeight_le current.mass).trans
  exact initialNormalized.finalOrdinaryTrace_mass_lower
    (proposition63IdentitySubfamily initialNormalized.croppedFamily) current
    initialSource.extremal.delta_pos current_cubical
    (fun index => by
      simpa only [proposition63IdentitySubfamily_embedding] using
        current_sub_normalized index)
    density ordinaryPerTube

/-- One aggregate ordinary-trace average supplies both mass inequalities
consumed by the external-weight re-entry.  The first component says that the
chosen normalization weight is a valid average external weight.  The second
uses the uniform paper-carrier mass upper bound to compare the same weight
with the whole current cropped shading. -/
theorem proposition63_current_trace_bounds_of_average
    {delta sigma initialInputLoss normalizationLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    (initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent)
    (current : WZ1PaperTubeShading initialNormalized.croppedFamily)
    (traceAverage normalizationWeight : ENNReal)
    (hdeltaSmall : delta ≤ 1 / 24)
    (line_class : WZ1PaperIsLineClass initialNormalized.croppedFamily)
    (trace_average_lower :
      traceAverage * initialNormalized.croppedFamily.enncard ≤
        (proposition63CurrentOrdinaryTrace initialNormalized current).mass)
    (normalizationWeight_absorb :
      max normalizationWeight
          (normalizationWeight *
            ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
              Kakeya.realRpowENN delta 2)) ≤
        traceAverage) :
    normalizationWeight * initialNormalized.croppedFamily.enncard ≤
        ∑ index : Fin initialNormalized.croppedFamily.card,
          proposition63Lemma43TraceWeight
            (proposition63CurrentOrdinaryTrace initialNormalized current)
            current index ∧
      normalizationWeight * current.mass ≤
        (proposition63OrdinaryTrace
          (proposition63CurrentOrdinaryTrace initialNormalized current)
          current).mass := by
  have hweight : normalizationWeight ≤ traceAverage :=
    (le_max_left normalizationWeight
      (normalizationWeight *
        ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
          Kakeya.realRpowENN delta 2))).trans normalizationWeight_absorb
  have hweightedCarrier :
      normalizationWeight *
          ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
            Kakeya.realRpowENN delta 2) ≤
        traceAverage :=
    (le_max_right normalizationWeight
      (normalizationWeight *
        ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
          Kakeya.realRpowENN delta 2))).trans normalizationWeight_absorb
  have htraceIdem :=
    proposition63CurrentOrdinaryTrace_idem_mass initialNormalized current
  constructor
  · rw [proposition63Lemma43TraceWeight_sum, htraceIdem]
    exact (mul_le_mul_right' hweight
      initialNormalized.croppedFamily.enncard).trans trace_average_lower
  · rw [htraceIdem]
    have hcurrentUpper := wz2_paper_shading_mass_upper
      initialSource.extremal.delta_pos hdeltaSmall line_class current
    calc
      normalizationWeight * current.mass ≤
          normalizationWeight *
            (((55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
              Kakeya.realRpowENN delta 2) *
                initialNormalized.croppedFamily.enncard) := by gcongr
      _ = (normalizationWeight *
            ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
              Kakeya.realRpowENN delta 2)) *
          initialNormalized.croppedFamily.enncard := by ring
      _ ≤ traceAverage * initialNormalized.croppedFamily.enncard := by
        gcongr
      _ ≤ (proposition63CurrentOrdinaryTrace initialNormalized current).mass :=
        trace_average_lower

/-- Transfer the initial normalized cropped extremality to a current
subshading using exactly the accumulated finite-iteration mass ledger. -/
theorem proposition63_current_extremal_of_mass_ledger
    {delta sigma initialInputLoss normalizationLoss reentryLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    (initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent)
    (current : WZ1PaperTubeShading initialNormalized.croppedFamily)
    {leftProduct rightProduct : ENNReal}
    (leftProduct_pos : 0 < leftProduct)
    (leftProduct_ne_top : leftProduct ≠ ⊤)
    (rightProduct_ne_top : rightProduct ≠ ⊤)
    (current_sub_normalized : PaperIsSubshading current
      initialNormalized.croppedRefined)
    (current_cubical : WZ1PaperIsCubicalShading current)
    (current_mass_ledger :
      leftProduct * initialNormalized.croppedRefined.mass ≤
        rightProduct * current.mass)
    (normalizationLoss_le : normalizationLoss ≤ reentryLoss)
    (reentryLoss_pos : 0 < reentryLoss)
    (mass_loss_absorb :
      proposition63Lemma43MassLoss leftProduct rightProduct *
          Kakeya.realRpowENN delta reentryLoss ≤
        Kakeya.realRpowENN delta normalizationLoss) :
    WZ2PaperCroppedIsExtremal sigma reentryLoss
      initialNormalized.croppedFamily current := by
  apply transfer_cropped_extremal_to_subshading
    (proposition63Lemma43MassLoss leftProduct rightProduct)
    (proposition63Lemma43MassLoss_pos leftProduct rightProduct)
    (proposition63Lemma43MassLoss_ne_top leftProduct_pos
      rightProduct_ne_top)
    initialNormalized.final_extremal current_sub_normalized
    (proposition63Lemma43MassLoss_inv_mul_le leftProduct_pos
      leftProduct_ne_top rightProduct_ne_top current_mass_ledger)
    current_cubical normalizationLoss_le mass_loss_absorb
    initialNormalized.final_extremal.delta_pos
    initialNormalized.final_extremal.delta_le_one reentryLoss_pos

/-- For a normalized source with synchronized per-tube ordinary density,
current cropped extremality supplies the missing average trace-weight bound.
Thus one sufficiently small normalization weight simultaneously satisfies
the external regularizer's total-weight premise and the re-entry trace-mass
premise. -/
theorem proposition63_current_trace_bounds_of_per_tube_density_and_extremal
    {delta sigma initialInputLoss normalizationLoss currentLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    (initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent)
    (current : WZ1PaperTubeShading initialNormalized.croppedFamily)
    (current_sub_normalized : PaperIsSubshading current
      initialNormalized.croppedRefined)
    (current_cubical : WZ1PaperIsCubicalShading current)
    (current_extremal : WZ2PaperCroppedIsExtremal sigma currentLoss
      initialNormalized.croppedFamily current)
    (currentLoss_pos : 0 < currentLoss)
    (line_class : WZ1PaperIsLineClass initialNormalized.croppedFamily)
    (delta_small : delta ≤ 1 / 24)
    (density normalizationWeight : ENNReal)
    (ordinaryPerTube :
      ∀ index : Fin initialNormalized.croppedFamily.card,
        density *
            volume (initialNormalized.croppedFamily.tube index).carrier ≤
          volume (initialNormalized.frame ''
            initialNormalized.ordinaryRefined.carrier
              (PureWZ2CroppedCriticalNormalizationData.ordinaryIndex
                initialNormalized
                (proposition63IdentitySubfamily
                  initialNormalized.croppedFamily) index)))
    (normalizationWeight_le :
      normalizationWeight ≤
        (100 : ENNReal)⁻¹ * density *
          Kakeya.realRpowENN delta (currentLoss + 2)) :
    normalizationWeight * initialNormalized.croppedFamily.enncard ≤
        ∑ index : Fin initialNormalized.croppedFamily.card,
          proposition63Lemma43TraceWeight
            (proposition63CurrentOrdinaryTrace initialNormalized current)
            current index ∧
      normalizationWeight * current.mass ≤
        (proposition63OrdinaryTrace
          (proposition63CurrentOrdinaryTrace initialNormalized current)
          current).mass := by
  have htrace := initialNormalized.finalOrdinaryTrace_mass_lower
    (proposition63IdentitySubfamily initialNormalized.croppedFamily) current
    initialSource.extremal.delta_pos current_cubical
    (fun index => by
      simpa only [proposition63IdentitySubfamily_embedding] using
        current_sub_normalized index)
    density ordinaryPerTube
  have hcurrentFloor :
      Kakeya.realRpowENN delta (currentLoss + 2) *
          initialNormalized.croppedFamily.enncard ≤ current.mass := by
    have hselected := selected_cardinality_cancellation current_extremal
      line_class
      (proposition63IdentitySubfamily initialNormalized.croppedFamily)
      (delta_small.trans (by norm_num))
    simpa [proposition63IdentitySubfamily] using hselected
  have hpowerLeOne :
      Kakeya.realRpowENN delta (currentLoss + 2) ≤ 1 := by
    simp only [Kakeya.realRpowENN, ENNReal.ofReal_le_one]
    exact Real.rpow_le_one current_extremal.delta_pos.le
      current_extremal.delta_le_one (by linarith [currentLoss_pos])
  have hweightLeTraceCoefficient :
      normalizationWeight ≤ (100 : ENNReal)⁻¹ * density := by
    apply normalizationWeight_le.trans
    calc
      (100 : ENNReal)⁻¹ * density *
            Kakeya.realRpowENN delta (currentLoss + 2) ≤
          (100 : ENNReal)⁻¹ * density * 1 := by gcongr
      _ = (100 : ENNReal)⁻¹ * density := mul_one _
  have hweightTrace :
      normalizationWeight * current.mass ≤
        (proposition63CurrentOrdinaryTrace initialNormalized current).mass := by
    exact (mul_le_mul_right' hweightLeTraceCoefficient current.mass).trans
      htrace
  constructor
  · rw [proposition63Lemma43TraceWeight_sum,
      proposition63CurrentOrdinaryTrace_idem_mass]
    calc
      normalizationWeight * initialNormalized.croppedFamily.enncard ≤
          ((100 : ENNReal)⁻¹ * density *
              Kakeya.realRpowENN delta (currentLoss + 2)) *
            initialNormalized.croppedFamily.enncard := by gcongr
      _ = (100 : ENNReal)⁻¹ * density *
          (Kakeya.realRpowENN delta (currentLoss + 2) *
            initialNormalized.croppedFamily.enncard) := by ring
      _ ≤ (100 : ENNReal)⁻¹ * density * current.mass := by gcongr
      _ ≤ (proposition63CurrentOrdinaryTrace initialNormalized current).mass :=
        htrace
  · rw [proposition63CurrentOrdinaryTrace_idem_mass]
    exact hweightTrace

/-- Construct one current-shading re-entry from a finite pure nearby schedule
and explicit scalar absorptions.  The ordinary trace is regularized exactly
once.  Its selected dyadic weight level is bounded below using the global
normalization weight exported by the regularizer, so the caller need not
predict that data-dependent level. -/
theorem proposition63_current_shading_reentry
    {delta sigma initialInputLoss normalizationLoss reentryLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    (initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent)
    (current : WZ1PaperTubeShading initialNormalized.croppedFamily)
    {ambientConstant outputConstant normalizationWeight weightUpper : ENNReal}
    {levelCount : ℕ}
    (schedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := initialNormalized.croppedFamily) ambientConstant outputConstant
      levelCount)
    (ambient_cwa : WZ2PaperPureCWAAtNearbyScales
      initialNormalized.croppedFamily ambientConstant)
    (reentry_extremal : WZ2PaperCroppedIsExtremal sigma reentryLoss
      initialNormalized.croppedFamily current)
    (reentryNormalizationLoss : ℝ)
    (reentry_normalization_loss_pos : 0 < reentryNormalizationLoss)
    (reentry_loss_le_half : reentryLoss ≤ reentryNormalizationLoss / 2)
    (normalization_weight_ne_zero : normalizationWeight ≠ 0)
    (normalization_weight_ne_top : normalizationWeight ≠ ⊤)
    (weightUpper_ne_top : weightUpper ≠ ⊤)
    (regularization_mass_lower :
      normalizationWeight * initialNormalized.croppedFamily.enncard ≤
        ∑ index : Fin initialNormalized.croppedFamily.card,
          proposition63Lemma43TraceWeight
            (proposition63CurrentOrdinaryTrace initialNormalized current)
            current index)
    (weight_upper : ∀ index : Fin initialNormalized.croppedFamily.card,
      proposition63Lemma43TraceWeight
          (proposition63CurrentOrdinaryTrace initialNormalized current)
          current index ≤ weightUpper)
    (output_finite : WZ2PaperFiniteErrorConstant outputConstant)
    (regularization_absorb :
      let degreeConstant :=
        16 * (schedule.scaleCount : ENNReal) *
          (Nat.log 2 (2 * initialNormalized.croppedFamily.card) + 1 : ENNReal) ^
            schedule.scaleCount
      let regularizationLoss :=
        (8 : ENNReal) *
          (Nat.log 2 (2 * initialNormalized.croppedFamily.card) + 1 : ENNReal) ^
            (schedule.scaleCount + 1)
      max degreeConstant
          ((normalizationWeight⁻¹ *
              (ambientConstant *
                (regularizationLoss * weightUpper) *
                degreeConstant)) *
            ambientConstant) ≤
        outputConstant)
    (output_le : outputConstant ≤
      Kakeya.realRpowENN delta (-reentryLoss))
    (trace_scale_absorb :
      4 * (Kakeya.realRpowENN delta reentryLoss *
        Kakeya.deltaTubeVolume delta) ≤ normalizationWeight)
    (paper_scale_absorb : ∀ index,
      4 * (Kakeya.realRpowENN delta reentryLoss *
          volume (wz1PaperTubeCarrier
            (initialNormalized.croppedFamily.tube index))) ≤
        (73 / 100 : ENNReal) * normalizationWeight)
    (current_sub_normalized : PaperIsSubshading current
      initialNormalized.croppedRefined)
    (current_cubical : WZ1PaperIsCubicalShading current)
    (current_trace_mass :
      normalizationWeight * current.mass ≤
        (proposition63OrdinaryTrace
          (proposition63CurrentOrdinaryTrace initialNormalized current)
          current).mass)
    (line_class : WZ1PaperIsLineClass initialNormalized.croppedFamily)
    (delta_small : delta ≤ 1 / 24)
    (ambient_top_level_constant : ENNReal)
    (ambient_top_level_cwa : WZ2PaperConvexWolffBound
      initialNormalized.croppedFamily ambient_top_level_constant)
    (top_level_absorb :
      (normalizationWeight⁻¹ *
          (((8 : ENNReal) *
              (Nat.log 2 (2 * initialNormalized.croppedFamily.card) + 1 :
                ENNReal) ^ (schedule.scaleCount + 1)) * weightUpper)) *
          ambient_top_level_constant ≤
        Kakeya.realRpowENN delta (-reentryLoss)) :
    ∃ data : Proposition63CurrentShadingReentryData
        (reentryLoss := reentryLoss) initialNormalized current,
      data.normalizationWeight = normalizationWeight ∧
        data.weightUpper = weightUpper ∧
        data.levelCount = levelCount ∧
        data.reentryNormalizationLoss = reentryNormalizationLoss := by
  rcases schedule.regularizeExternalWeight
      ambient_cwa
      reentry_extremal.nonempty
      (proposition63Lemma43TraceWeight
        (proposition63CurrentOrdinaryTrace initialNormalized current) current)
      normalization_weight_ne_zero normalization_weight_ne_top
      weightUpper_ne_top regularization_mass_lower weight_upper output_finite
      regularization_absorb with
    ⟨regularized⟩
  have hfourZero : (4 : ENNReal) ≠ 0 := by norm_num
  have hfourTop : (4 : ENNReal) ≠ ⊤ := by norm_num
  have htraceLevel :
      Kakeya.realRpowENN delta reentryLoss *
          Kakeya.deltaTubeVolume delta ≤ regularized.weightLevel := by
    apply (ENNReal.mul_le_mul_iff_right hfourZero hfourTop).mp
    calc
      4 * (Kakeya.realRpowENN delta reentryLoss *
            Kakeya.deltaTubeVolume delta) ≤ normalizationWeight :=
        trace_scale_absorb
      _ ≤ 4 * regularized.weightLevel :=
        regularized.normalizationWeight_le_four_weightLevel
  have hdenseLevel : ∀ index : Fin regularized.selected.family.card,
      Kakeya.realRpowENN delta reentryLoss *
          volume (wz1PaperTubeCarrier
            (regularized.selected.family.tube index)) ≤
        (73 / 100 : ENNReal) * regularized.weightLevel := by
    intro index
    apply (ENNReal.mul_le_mul_iff_right hfourZero hfourTop).mp
    calc
      4 * (Kakeya.realRpowENN delta reentryLoss *
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
  exact
    ⟨{ ambientConstant := ambientConstant
       outputConstant := outputConstant
       normalizationWeight := normalizationWeight
       weightUpper := weightUpper
       levelCount := levelCount
       schedule := schedule
       regularized := regularized
       reentry_extremal := reentry_extremal
       reentryNormalizationLoss := reentryNormalizationLoss
       reentry_normalization_loss_pos := reentry_normalization_loss_pos
       reentry_loss_le_half := reentry_loss_le_half
       normalization_weight_ne_zero := normalization_weight_ne_zero
       normalization_weight_ne_top := normalization_weight_ne_top
       weightUpper_ne_top := weightUpper_ne_top
       output_le := output_le
       trace_level := htraceLevel
       dense_level := hdenseLevel
       current_sub_normalized := current_sub_normalized
       current_cubical := current_cubical
       current_trace_mass := current_trace_mass
       line_class := line_class
       delta_small := delta_small
       ambient_top_level_constant := ambient_top_level_constant
       ambient_top_level_cwa := ambient_top_level_cwa
       top_level_absorb := by
        rw [regularized.regularizationLoss_eq]
        exact top_level_absorb }, rfl, rfl, rfl, rfl⟩

/-- Finite-iteration entry point for current-shading re-entry.  It derives
cropped extremality from the accumulated mass ledger and derives the
ordinary-trace mass comparison from the normalization's synchronized
per-tube density. -/
theorem proposition63_current_shading_reentry_of_density_and_mass_ledger
    {delta sigma initialInputLoss normalizationLoss currentLoss reentryLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    (initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent)
    (current : WZ1PaperTubeShading initialNormalized.croppedFamily)
    {leftProduct rightProduct density : ENNReal}
    {ambientConstant outputConstant normalizationWeight weightUpper : ENNReal}
    {levelCount : ℕ}
    (schedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := initialNormalized.croppedFamily) ambientConstant outputConstant
      levelCount)
    (ambient_cwa : WZ2PaperPureCWAAtNearbyScales
      initialNormalized.croppedFamily ambientConstant)
    (leftProduct_pos : 0 < leftProduct)
    (leftProduct_ne_top : leftProduct ≠ ⊤)
    (rightProduct_ne_top : rightProduct ≠ ⊤)
    (current_mass_ledger :
      leftProduct * initialNormalized.croppedRefined.mass ≤
        rightProduct * current.mass)
    (normalizationLoss_le : normalizationLoss ≤ currentLoss)
    (currentLoss_le : currentLoss ≤ reentryLoss)
    (currentLoss_pos : 0 < currentLoss)
    (reentryNormalizationLoss : ℝ)
    (reentry_normalization_loss_pos : 0 < reentryNormalizationLoss)
    (reentry_loss_le_half : reentryLoss ≤ reentryNormalizationLoss / 2)
    (mass_loss_absorb :
      proposition63Lemma43MassLoss leftProduct rightProduct *
          Kakeya.realRpowENN delta currentLoss ≤
        Kakeya.realRpowENN delta normalizationLoss)
    (ordinaryPerTube :
      ∀ index : Fin initialNormalized.croppedFamily.card,
        density *
            volume (initialNormalized.croppedFamily.tube index).carrier ≤
          volume (initialNormalized.frame ''
            initialNormalized.ordinaryRefined.carrier
              (PureWZ2CroppedCriticalNormalizationData.ordinaryIndex
                initialNormalized
                (proposition63IdentitySubfamily
                  initialNormalized.croppedFamily) index)))
    (normalizationWeight_le :
      normalizationWeight ≤
        (100 : ENNReal)⁻¹ * density *
          Kakeya.realRpowENN delta (currentLoss + 2))
    (normalization_weight_ne_zero : normalizationWeight ≠ 0)
    (normalization_weight_ne_top : normalizationWeight ≠ ⊤)
    (weightUpper_ne_top : weightUpper ≠ ⊤)
    (weight_upper : ∀ index : Fin initialNormalized.croppedFamily.card,
      proposition63Lemma43TraceWeight
          (proposition63CurrentOrdinaryTrace initialNormalized current)
          current index ≤ weightUpper)
    (output_finite : WZ2PaperFiniteErrorConstant outputConstant)
    (regularization_absorb :
      let degreeConstant :=
        16 * (schedule.scaleCount : ENNReal) *
          (Nat.log 2 (2 * initialNormalized.croppedFamily.card) + 1 : ENNReal) ^
            schedule.scaleCount
      let regularizationLoss :=
        (8 : ENNReal) *
          (Nat.log 2 (2 * initialNormalized.croppedFamily.card) + 1 : ENNReal) ^
            (schedule.scaleCount + 1)
      max degreeConstant
          ((normalizationWeight⁻¹ *
              (ambientConstant *
                (regularizationLoss * weightUpper) *
                degreeConstant)) *
            ambientConstant) ≤
        outputConstant)
    (output_le : outputConstant ≤
      Kakeya.realRpowENN delta (-reentryLoss))
    (trace_scale_absorb :
      4 * (Kakeya.realRpowENN delta reentryLoss *
        Kakeya.deltaTubeVolume delta) ≤ normalizationWeight)
    (paper_scale_absorb : ∀ index,
      4 * (Kakeya.realRpowENN delta reentryLoss *
          volume (wz1PaperTubeCarrier
            (initialNormalized.croppedFamily.tube index))) ≤
        (73 / 100 : ENNReal) * normalizationWeight)
    (current_sub_normalized : PaperIsSubshading current
      initialNormalized.croppedRefined)
    (current_cubical : WZ1PaperIsCubicalShading current)
    (line_class : WZ1PaperIsLineClass initialNormalized.croppedFamily)
    (delta_small : delta ≤ 1 / 24)
    (ambient_top_level_constant : ENNReal)
    (ambient_top_level_cwa : WZ2PaperConvexWolffBound
      initialNormalized.croppedFamily ambient_top_level_constant)
    (top_level_absorb :
      (normalizationWeight⁻¹ *
          (((8 : ENNReal) *
              (Nat.log 2 (2 * initialNormalized.croppedFamily.card) + 1 :
                ENNReal) ^ (schedule.scaleCount + 1)) * weightUpper)) *
          ambient_top_level_constant ≤
        Kakeya.realRpowENN delta (-reentryLoss)) :
    ∃ data : Proposition63CurrentShadingReentryData
        (reentryLoss := reentryLoss) initialNormalized current,
      data.normalizationWeight = normalizationWeight ∧
        data.levelCount = levelCount ∧
        data.reentryNormalizationLoss = reentryNormalizationLoss := by
  have current_extremal : WZ2PaperCroppedIsExtremal sigma currentLoss
      initialNormalized.croppedFamily current :=
    proposition63_current_extremal_of_mass_ledger initialNormalized current
      leftProduct_pos leftProduct_ne_top rightProduct_ne_top
      current_sub_normalized current_cubical current_mass_ledger
      normalizationLoss_le currentLoss_pos mass_loss_absorb
  have reentry_extremal : WZ2PaperCroppedIsExtremal sigma reentryLoss
      initialNormalized.croppedFamily current :=
    current_extremal.mono_loss currentLoss_le
  have traceBounds :=
    proposition63_current_trace_bounds_of_per_tube_density_and_extremal
      initialNormalized current current_sub_normalized current_cubical
      current_extremal currentLoss_pos line_class delta_small density
      normalizationWeight ordinaryPerTube normalizationWeight_le
  rcases proposition63_current_shading_reentry initialNormalized current
      schedule ambient_cwa reentry_extremal reentryNormalizationLoss
      reentry_normalization_loss_pos reentry_loss_le_half
      normalization_weight_ne_zero
      normalization_weight_ne_top weightUpper_ne_top traceBounds.1
      weight_upper output_finite regularization_absorb output_le
      trace_scale_absorb paper_scale_absorb current_sub_normalized
      current_cubical traceBounds.2 line_class delta_small
      ambient_top_level_constant ambient_top_level_cwa top_level_absorb with
    ⟨data, weight_eq, _weightUpperEq, levelCount_eq,
      normalizationLoss_eq⟩
  exact ⟨data, weight_eq, levelCount_eq, normalizationLoss_eq⟩

/-- Aggregate-mass specialization of current-shading re-entry.  One lower
bound for the total ordinary trace supplies both mass premises of the
external-weight regularizer; no pointwise ordinary-density hypothesis is
needed at this interface. -/
theorem proposition63_current_shading_reentry_of_average_and_mass_ledger
    {delta sigma initialInputLoss normalizationLoss reentryLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    (initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent)
    (current : WZ1PaperTubeShading initialNormalized.croppedFamily)
    {leftProduct rightProduct traceAverage : ENNReal}
    {ambientConstant outputConstant normalizationWeight weightUpper : ENNReal}
    {levelCount : ℕ}
    (schedule : WZ2PaperPureFiniteNearbyScheduleData
      (fine := initialNormalized.croppedFamily) ambientConstant outputConstant
      levelCount)
    (ambient_cwa : WZ2PaperPureCWAAtNearbyScales
      initialNormalized.croppedFamily ambientConstant)
    (leftProduct_pos : 0 < leftProduct)
    (leftProduct_ne_top : leftProduct ≠ ⊤)
    (rightProduct_ne_top : rightProduct ≠ ⊤)
    (current_mass_ledger :
      leftProduct * initialNormalized.croppedRefined.mass ≤
        rightProduct * current.mass)
    (normalizationLoss_le : normalizationLoss ≤ reentryLoss)
    (reentryLoss_pos : 0 < reentryLoss)
    (reentryNormalizationLoss : ℝ)
    (reentry_normalization_loss_pos : 0 < reentryNormalizationLoss)
    (reentry_loss_le_half : reentryLoss ≤ reentryNormalizationLoss / 2)
    (mass_loss_absorb :
      proposition63Lemma43MassLoss leftProduct rightProduct *
          Kakeya.realRpowENN delta reentryLoss ≤
        Kakeya.realRpowENN delta normalizationLoss)
    (trace_average_lower :
      traceAverage * initialNormalized.croppedFamily.enncard ≤
        (proposition63CurrentOrdinaryTrace initialNormalized current).mass)
    (normalizationWeight_absorb :
      max normalizationWeight
          (normalizationWeight *
            ((55296 : ENNReal) * Kakeya.deltaTubeVolume 1 *
              Kakeya.realRpowENN delta 2)) ≤
        traceAverage)
    (normalization_weight_ne_zero : normalizationWeight ≠ 0)
    (normalization_weight_ne_top : normalizationWeight ≠ ⊤)
    (weightUpper_ne_top : weightUpper ≠ ⊤)
    (weight_upper : ∀ index : Fin initialNormalized.croppedFamily.card,
      proposition63Lemma43TraceWeight
          (proposition63CurrentOrdinaryTrace initialNormalized current)
          current index ≤ weightUpper)
    (output_finite : WZ2PaperFiniteErrorConstant outputConstant)
    (regularization_absorb :
      let degreeConstant :=
        16 * (schedule.scaleCount : ENNReal) *
          (Nat.log 2 (2 * initialNormalized.croppedFamily.card) + 1 : ENNReal) ^
            schedule.scaleCount
      let regularizationLoss :=
        (8 : ENNReal) *
          (Nat.log 2 (2 * initialNormalized.croppedFamily.card) + 1 : ENNReal) ^
            (schedule.scaleCount + 1)
      max degreeConstant
          ((normalizationWeight⁻¹ *
              (ambientConstant *
                (regularizationLoss * weightUpper) *
                degreeConstant)) *
            ambientConstant) ≤
        outputConstant)
    (output_le : outputConstant ≤
      Kakeya.realRpowENN delta (-reentryLoss))
    (trace_scale_absorb :
      4 * (Kakeya.realRpowENN delta reentryLoss *
        Kakeya.deltaTubeVolume delta) ≤ normalizationWeight)
    (paper_scale_absorb : ∀ index,
      4 * (Kakeya.realRpowENN delta reentryLoss *
          volume (wz1PaperTubeCarrier
            (initialNormalized.croppedFamily.tube index))) ≤
        (73 / 100 : ENNReal) * normalizationWeight)
    (current_sub_normalized : PaperIsSubshading current
      initialNormalized.croppedRefined)
    (current_cubical : WZ1PaperIsCubicalShading current)
    (line_class : WZ1PaperIsLineClass initialNormalized.croppedFamily)
    (delta_small : delta ≤ 1 / 24)
    (ambient_top_level_constant : ENNReal)
    (ambient_top_level_cwa : WZ2PaperConvexWolffBound
      initialNormalized.croppedFamily ambient_top_level_constant)
    (top_level_absorb :
      (normalizationWeight⁻¹ *
          (((8 : ENNReal) *
              (Nat.log 2 (2 * initialNormalized.croppedFamily.card) + 1 :
                ENNReal) ^ (schedule.scaleCount + 1)) * weightUpper)) *
          ambient_top_level_constant ≤
        Kakeya.realRpowENN delta (-reentryLoss)) :
    Nonempty (Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) initialNormalized current) := by
  have reentry_extremal : WZ2PaperCroppedIsExtremal sigma reentryLoss
      initialNormalized.croppedFamily current :=
    proposition63_current_extremal_of_mass_ledger initialNormalized current
      leftProduct_pos leftProduct_ne_top rightProduct_ne_top
      current_sub_normalized current_cubical current_mass_ledger
      normalizationLoss_le reentryLoss_pos mass_loss_absorb
  have traceBounds := proposition63_current_trace_bounds_of_average
    initialNormalized current traceAverage normalizationWeight delta_small
    line_class trace_average_lower normalizationWeight_absorb
  rcases proposition63_current_shading_reentry initialNormalized current
      schedule ambient_cwa reentry_extremal reentryNormalizationLoss
      reentry_normalization_loss_pos reentry_loss_le_half
      normalization_weight_ne_zero
      normalization_weight_ne_top weightUpper_ne_top traceBounds.1
      weight_upper output_finite regularization_absorb output_le
      trace_scale_absorb paper_scale_absorb current_sub_normalized
      current_cubical traceBounds.2 line_class delta_small
      ambient_top_level_constant ambient_top_level_cwa top_level_absorb with
    ⟨data, _, _, _, _⟩
  exact ⟨data⟩

namespace Proposition63CurrentShadingReentryData

noncomputable def ordinary
    {delta sigma initialInputLoss normalizationLoss reentryLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (data : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) initialNormalized current) :
    Kakeya.Streamlined.TubeShading initialNormalized.croppedFamily :=
  initialNormalized.finalOrdinaryTrace
    (proposition63IdentitySubfamily initialNormalized.croppedFamily)
    current

/-- The selected ordinary trace is a genuine pure extremizer. -/
noncomputable def ordinarySource
    {delta sigma initialInputLoss normalizationLoss reentryLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (data : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) initialNormalized current) :
    PureWZ2ExtremalConfiguration sigma reentryLoss delta := by
  let selected := data.regularized.selected
  let cropped := restrictPaperShading selected current
  let trace := proposition63SubfamilyOrdinaryTrace data.ordinary selected cropped
  refine
    { family := selected.family
      shading := trace
      extremal := {
        delta_pos := data.reentry_extremal.delta_pos
        delta_le_one := data.reentry_extremal.delta_le_one
        nonempty := data.regularized.selected_nonempty
        cwa_nearby_scales := data.regularized.pure_cwa_nearby.mono
          data.output_le (by simp [Kakeya.realRpowENN])
        dense := proposition63RegularizedTrace_dense data.ordinary
          current data.schedule data.regularized
          (Kakeya.realRpowENN delta reentryLoss) data.trace_level
        volume_upper := ?_ } }
  calc
    volume trace.union ≤ volume cropped.union :=
      measure_mono (proposition63SubfamilyOrdinaryTrace_union_subset
        data.ordinary selected cropped)
    _ ≤ volume current.union := by
      apply measure_mono
      rintro point ⟨index, hpoint⟩
      exact ⟨selected.embedding index, hpoint⟩
    _ ≤ Kakeya.realRpowENN delta (sigma - reentryLoss) :=
      data.reentry_extremal.volume_upper

noncomputable def denseShading
    {delta sigma initialInputLoss normalizationLoss reentryLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (data : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) initialNormalized current) :
    WZ1PaperTubeShading data.ordinarySource.family :=
  pureWZ2DenseCubicalShading data.ordinarySource.shading

theorem cellContained
    {delta sigma initialInputLoss normalizationLoss reentryLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (data : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) initialNormalized current)
    (index : Fin data.regularized.selected.family.card)
    (cell : ℤ × ℤ × ℤ)
    (hcell : (data.ordinarySource.shading.carrier index ∩
      wz1PaperGridCube delta cell).Nonempty) :
    wz1PaperGridCube delta cell ⊆
      wz1PaperTubeCarrier (data.regularized.selected.family.tube index) := by
  apply pureWZ2GridCube_subset_paperTube_of_sub_cubical
    data.ordinarySource.shading
    (restrictPaperShading data.regularized.selected current)
    (fun _ _ hpoint => hpoint.2)
    (restrictPaperShading_cubical data.regularized.selected
      data.current_cubical) index cell hcell

theorem denseSubshading
    {delta sigma initialInputLoss normalizationLoss reentryLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (data : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) initialNormalized current) :
    PaperIsSubshading data.denseShading
      (restrictPaperShading data.regularized.selected current) := by
  apply pureWZ2DenseCubicalShading_sub_cubical
    data.ordinarySource.shading
    (restrictPaperShading data.regularized.selected current)
    data.reentry_extremal.delta_pos
  · intro index point hpoint
    exact hpoint.2
  · exact restrictPaperShading_cubical data.regularized.selected
      data.current_cubical
  · exact proposition63RegularizedTrace_volume_pos data.ordinary
      current data.schedule data.regularized

theorem denseMassRetention
    {delta sigma initialInputLoss normalizationLoss reentryLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (data : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) initialNormalized current) :
    (73 / 100 : ENNReal) * data.ordinarySource.shading.mass ≤
      (proposition63OrdinaryTrace data.ordinarySource.shading
        data.denseShading).mass := by
  apply pureWZ2DenseCubicalShading_mass_retention
    data.reentry_extremal.delta_pos
  · have hsqrt : Real.sqrt 3 ≤ 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
        Real.sqrt_nonneg 3]
    calc
      delta * (1 + Real.sqrt 3) ≤ delta * 3 := by
        apply mul_le_mul_of_nonneg_left (by linarith)
        exact data.reentry_extremal.delta_pos.le
      _ ≤ 1 := by nlinarith [data.delta_small]
  · exact data.cellContained

theorem denseCroppedDense
    {delta sigma initialInputLoss normalizationLoss reentryLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (data : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) initialNormalized current) :
    data.denseShading.IsLambdaDense
      (Kakeya.realRpowENN delta reentryLoss) := by
  rw [Kakeya.Streamlined.Shading.IsLambdaDense]
  change
    Kakeya.realRpowENN delta reentryLoss *
        (∑ index : Fin data.regularized.selected.family.card,
          volume (wz1PaperTubeCarrier
            (data.regularized.selected.family.tube index))) ≤
      ∑ index : Fin data.regularized.selected.family.card,
        volume (data.denseShading.carrier index)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro index _
  calc
    Kakeya.realRpowENN delta reentryLoss *
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
        data.reentry_extremal.delta_pos
        (by
          have hsqrt : Real.sqrt 3 ≤ 2 := by
            nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
              Real.sqrt_nonneg 3]
          calc
            delta * (1 + Real.sqrt 3) ≤ delta * 3 := by
              apply mul_le_mul_of_nonneg_left (by linarith)
              exact data.reentry_extremal.delta_pos.le
            _ ≤ 1 := by nlinarith [data.delta_small])
        (data.ordinarySource.family.tube index)
        (data.ordinarySource.shading.carrier index)
        (data.ordinarySource.shading.measurable_carrier index)
        (data.ordinarySource.shading.subset_body index)
        (data.cellContained index)).trans
      exact measure_mono Set.inter_subset_right

theorem croppedExtremal
    {delta sigma initialInputLoss normalizationLoss reentryLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (data : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) initialNormalized current) :
    WZ2PaperCroppedIsExtremal sigma reentryLoss
      data.regularized.selected.family data.denseShading := by
  refine
    { delta_pos := data.reentry_extremal.delta_pos
      delta_le_one := data.reentry_extremal.delta_le_one
      nonempty := data.regularized.selected_nonempty
      cwa_nearby_scales := data.regularized.pure_cwa_nearby.mono
        data.output_le (by simp [Kakeya.realRpowENN])
      cubical := pureWZ2DenseCubicalShading_cubical
        data.ordinarySource.shading
      dense := data.denseCroppedDense
      volume_upper := ?_ }
  apply (measure_mono ?_).trans data.reentry_extremal.volume_upper
  rintro point ⟨index, hpoint⟩
  exact ⟨data.regularized.selected.embedding index,
    data.denseSubshading index hpoint⟩

/-- Any axial-window certificate on the incoming normalization passes to the
ordinary trace selected by current-shading re-entry. -/
theorem ordinaryAxialWindowOf
    {delta sigma initialInputLoss normalizationLoss reentryLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (data : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) initialNormalized current)
    {bound : ℝ}
    (initialAxialWindow : ∀ index point,
      point ∈ initialNormalized.frame ''
          initialNormalized.ordinaryRefined.carrier index →
        |point (2 : Fin 3)| ≤ bound) :
    ∀ index point, point ∈ data.ordinarySource.shading.carrier index →
      |point (2 : Fin 3)| ≤ bound := by
  intro index point hpoint
  have hordinary : point ∈
      data.ordinary.carrier (data.regularized.selected.embedding index) :=
    hpoint.1
  exact initialAxialWindow _ point hordinary.1

/-- The ordinary trace selected by re-entry stays in the axial window already
certified by the incoming Node 3 normalization. -/
theorem ordinaryAxialWindow
    {delta sigma initialInputLoss normalizationLoss reentryLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (data : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) initialNormalized current) :
    ∀ index point, point ∈ data.ordinarySource.shading.carrier index →
      |point (2 : Fin 3)| ≤ 1 / 4 :=
  data.ordinaryAxialWindowOf initialNormalized.ordinary_axial_window

/-- Bounded basepoints pass to the tube subfamily selected by the external
weight regularizer. -/
theorem ordinaryBoundedBase
    {delta sigma initialInputLoss normalizationLoss reentryLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (data : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) initialNormalized current) :
    HasBoundedBase data.regularized.selected.family 4 := by
  intro index
  rw [data.regularized.selected.tube_eq]
  exact initialNormalized.ordinary_bounded_base _

noncomputable def normalization
    {delta sigma initialInputLoss normalizationLoss reentryLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (data : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) initialNormalized current) :
    PureWZ2CroppedCriticalNormalizationData
      (outputLoss := data.reentryNormalizationLoss) data.ordinarySource
        normalizationExponent := by
  have hlog : 1 ≤ Real.log (1 / delta) := by
    apply (Real.le_log_iff_exp_le (one_div_pos.mpr
      data.reentry_extremal.delta_pos)).2
    have htwentyFour : (24 : ℝ) ≤ 1 / delta := by
      apply (le_div_iff₀ data.reentry_extremal.delta_pos).2
      nlinarith [data.delta_small]
    exact (Real.exp_one_lt_three.trans (by norm_num)).le.trans htwentyFour
  have hretained :
      wz2PaperPureRefinementFraction delta normalizationExponent *
          data.ordinarySource.shading.mass ≤
        data.ordinarySource.shading.mass :=
    proposition63PureRefinementFraction_mul_le_self
      normalizationExponent hlog data.ordinarySource.shading.mass
  have htopSource : WZ2PaperConvexWolffBound data.regularized.selected.family
      (Kakeya.realRpowENN delta (-reentryLoss)) :=
    proposition63RegularizedTrace_topLevelCWA_from_ambient data.schedule
      data.regularized data.normalization_weight_ne_zero
      data.normalization_weight_ne_top data.ambient_top_level_cwa
      data.top_level_absorb
  have hsourceLeNormalization : reentryLoss ≤ data.reentryNormalizationLoss := by
    linarith [data.reentry_loss_le_half,
      data.reentry_normalization_loss_pos]
  have htop : WZ2PaperConvexWolffBound data.regularized.selected.family
      (Kakeya.realRpowENN delta (-data.reentryNormalizationLoss)) := by
    apply weaken_convex_wolff_bound htopSource
    apply ENNReal.ofReal_mono
    exact Real.rpow_le_rpow_of_exponent_ge
      data.reentry_extremal.delta_pos data.reentry_extremal.delta_le_one
      (by linarith)
  have hcroppedExtremal : WZ2PaperCroppedIsExtremal sigma
      data.reentryNormalizationLoss data.regularized.selected.family
      data.denseShading :=
    data.croppedExtremal.mono_loss hsourceLeNormalization
  apply proposition63IdentityFullOrdinaryNormalization
    (source := data.ordinarySource) data.reentry_loss_le_half
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
      (Kakeya.realRpowENN delta reentryLoss / 2) *
            volume (data.ordinarySource.family.tube index).carrier ≤
          Kakeya.realRpowENN delta reentryLoss *
            volume (data.ordinarySource.family.tube index).carrier := by
        apply mul_le_mul_right'
        rw [div_eq_mul_inv]
        exact mul_le_of_le_one_right bot_le (by norm_num)
      _ = Kakeya.realRpowENN delta reentryLoss *
            Kakeya.deltaTubeVolume delta := by rw [htubeVolume]
      _ ≤ data.regularized.weightLevel := data.trace_level
      _ ≤ volume (data.ordinarySource.shading.carrier index) := hsourceLower
  · exact data.ordinaryAxialWindow
  · exact data.line_class.subfamily data.regularized.selected
  · exact htop
  · exact hcroppedExtremal
  · exact data.cellContained
  · exact data.ordinaryBoundedBase

@[simp] theorem normalization_croppedFamily
    {delta sigma initialInputLoss normalizationLoss reentryLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (data : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) initialNormalized current) :
    data.normalization.croppedFamily = data.regularized.selected.family :=
  rfl

@[simp] theorem normalization_croppedRefined_current
    {delta sigma initialInputLoss normalizationLoss reentryLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (data : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) initialNormalized current) :
    data.normalization.croppedRefined = data.denseShading :=
  rfl

/-- The freshly normalized cropped shading remains inside the actual current
shading.  This is the provenance needed to restrict one root plane map at
every finite re-entry step. -/
theorem normalization_croppedRefined_union_subset_current
    {delta sigma initialInputLoss normalizationLoss reentryLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (data : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) initialNormalized current) :
    data.normalization.croppedRefined.union ⊆ current.union := by
  rw [data.normalization_croppedRefined_current]
  rintro point ⟨index, hpoint⟩
  have hrestricted : point ∈
      (restrictPaperShading data.regularized.selected current).carrier index :=
    data.denseSubshading index hpoint
  exact ⟨data.regularized.selected.embedding index, hrestricted⟩

/-- A point-centered estimate on the current ambient shading survives the
ordinary-trace re-entry.  The proof first reindexes to the selected tube
family and then uses the genuine dense-cubical subshading relation; no
geometric covering factor is introduced. -/
theorem pointCenteredCovering
    {delta sigma initialInputLoss normalizationLoss reentryLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (data : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) initialNormalized current)
    {planeMap : Point3 → Point3}
    {resolutionScale : NNReal} {spatialRadius : ℝ} {constant : ENNReal}
    (hcover : PureWZ2PointCenteredCoveringAt current planeMap
      resolutionScale spatialRadius constant) :
    PureWZ2PointCenteredCoveringAt data.normalization.croppedRefined planeMap
      resolutionScale spatialRadius constant := by
  have hselected := pureWZ2PointCenteredCoveringAt_restrictSubfamily
    data.regularized.selected hcover
  apply pureWZ2PointCenteredCoveringAt_mono data.denseSubshading
  simpa only [Proposition63CurrentShadingReentryData.ordinarySource] using
    hselected

/-- Every normalization produced by current-shading re-entry carries the
cell-containment provenance needed to start the next ordinary-trace step. -/
theorem normalizationTraceProvenance
    {delta sigma initialInputLoss normalizationLoss reentryLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (data : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) initialNormalized current) :
    Proposition63NormalizationTraceProvenance data.normalization := by
  refine ⟨?_⟩
  intro index cell hcell
  dsimp [Proposition63CurrentShadingReentryData.normalization,
    proposition63IdentityFullOrdinaryNormalization,
    proposition63IdentitySubfamily,
    proposition63IdentityIndexEquiv] at hcell ⊢
  apply data.cellContained index cell
  simpa using hcell

/-- The re-entry normalization has a uniform ordinary per-tube density.
The common external-weight band gives the source trace lower bound.  Since the
re-entry normalization stores the full ordinary source, no additional
dense-cubical factor is charged to this certificate. -/
theorem normalizationOrdinaryPerTube
    {delta sigma initialInputLoss normalizationLoss reentryLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (data : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) initialNormalized current) :
    ∀ index : Fin data.normalization.croppedFamily.card,
      Kakeya.realRpowENN delta reentryLoss *
          volume (data.normalization.croppedFamily.tube index).carrier ≤
        volume (data.normalization.frame ''
          data.normalization.ordinaryRefined.carrier
            (PureWZ2CroppedCriticalNormalizationData.ordinaryIndex
              data.normalization
              (proposition63IdentitySubfamily
                data.normalization.croppedFamily) index)) := by
  intro index
  have htubeVolume :
      volume (data.regularized.selected.family.tube index).carrier =
        Kakeya.deltaTubeVolume delta :=
    tube_volume_scaling.1 delta (data.regularized.selected.family.tube index)
  have hsourceLower : data.regularized.weightLevel ≤
      volume (data.ordinarySource.shading.carrier index) :=
    (data.regularized.weight_band index).1
  change
    Kakeya.realRpowENN delta reentryLoss *
          volume (data.regularized.selected.family.tube index).carrier ≤
      volume ((AffineIsometryEquiv.refl ℝ Point3) ''
        data.ordinarySource.shading.carrier index)
  rw [Kakeya.Streamlined.AffineIsometryEquiv.volume_image
    (AffineIsometryEquiv.refl ℝ Point3)
    (data.ordinarySource.shading.carrier index)
    (data.ordinarySource.shading.measurable_carrier index), htubeVolume]
  exact data.trace_level.trans hsourceLower

/-- The complete mass ledger for one ordinary-trace re-entry.  The first
factor is the certified mass surviving the initial-normalization trace; the
right factor is exactly the finite external-weight regularization loss.  The
fixed `73 / 100` factor is the dense-cubical trace retention used by the
second normalization. -/
theorem reentryMassRetention
    {delta sigma initialInputLoss normalizationLoss reentryLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (data : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) initialNormalized current) :
    ((73 / 100 : ENNReal) * data.normalizationWeight) * current.mass ≤
      data.regularized.regularizationLoss *
        data.normalization.croppedRefined.mass := by
  have hregularized : data.normalizationWeight * current.mass ≤
      data.regularized.regularizationLoss *
        data.ordinarySource.shading.mass := by
    calc
      data.normalizationWeight * current.mass ≤
          (proposition63OrdinaryTrace data.ordinary current).mass := by
        exact data.current_trace_mass
      _ ≤ data.regularized.regularizationLoss *
          data.ordinarySource.shading.mass := by
        simpa only [ordinarySource] using
          proposition63RegularizedTrace_mass_retention data.ordinary current
            data.schedule data.regularized
  have hdense : (73 / 100 : ENNReal) *
        data.ordinarySource.shading.mass ≤
      data.normalization.croppedRefined.mass := by
    calc
      (73 / 100 : ENNReal) * data.ordinarySource.shading.mass ≤
          (proposition63OrdinaryTrace data.ordinarySource.shading
            data.denseShading).mass := data.denseMassRetention
      _ ≤ data.denseShading.mass := by
        apply Finset.sum_le_sum
        intro index _
        exact measure_mono Set.inter_subset_right
      _ = data.normalization.croppedRefined.mass := rfl
  calc
    ((73 / 100 : ENNReal) * data.normalizationWeight) * current.mass =
        (73 / 100 : ENNReal) *
          (data.normalizationWeight * current.mass) := by ring
    _ ≤ (73 / 100 : ENNReal) *
        (data.regularized.regularizationLoss *
          data.ordinarySource.shading.mass) :=
      mul_le_mul_left' hregularized _
    _ = data.regularized.regularizationLoss *
        ((73 / 100 : ENNReal) *
          data.ordinarySource.shading.mass) := by ring
    _ ≤ data.regularized.regularizationLoss *
        data.normalization.croppedRefined.mass :=
      mul_le_mul_left' hdense _

/-- The preliminary local-grain map restricted to the exact normalized
shading used by the first sticky call. -/
noncomputable def normalizedLocalGrains
    {delta sigma initialInputLoss normalizationLoss reentryLoss localLoss
      localIncidence : ℝ}
    {L : NNReal}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {localShading : WZ1PaperTubeShading initialNormalized.croppedFamily}
    {localGrains : Proposition63InitialWeakLocalGrainData
      (incidence := localIncidence) localShading sigma
      (Kakeya.realRpowENN delta (-localLoss)) L}
    (data : Proposition63InitialLocalGrainReentryData
      (reentryLoss := reentryLoss)
      initialNormalized localShading localGrains) :
    Proposition63InitialWeakLocalGrainData
      (incidence := localIncidence) data.normalization.croppedRefined sigma
      (Kakeya.realRpowENN delta (-localLoss)) L :=
  (localGrains.restrictSubfamily data.regularized.selected).restrict
    data.denseSubshading

@[simp] theorem normalization_croppedRefined
    {delta sigma initialInputLoss normalizationLoss reentryLoss localLoss
      localIncidence : ℝ}
    {L : NNReal}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {localShading : WZ1PaperTubeShading initialNormalized.croppedFamily}
    {localGrains : Proposition63InitialWeakLocalGrainData
      (incidence := localIncidence) localShading sigma
      (Kakeya.realRpowENN delta (-localLoss)) L}
    (data : Proposition63InitialLocalGrainReentryData
      (reentryLoss := reentryLoss)
      initialNormalized localShading localGrains) :
    data.normalization.croppedRefined = data.denseShading :=
  rfl

end Proposition63CurrentShadingReentryData

/-- Invoke Proposition 6.2 on an arbitrary current cropped shading after the
ordinary-trace, whole-tube regularization, and dense normalization recorded
by `Proposition63CurrentShadingReentryData`.  This is the re-entry boundary
used between successive scales of the finite Lemma 4.12 iteration. -/
theorem proposition63CurrentShadingReentry_sticky
    {delta sigma initialInputLoss normalizationLoss reentryLoss stickyLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent logExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (data : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) initialNormalized current)
    (hSticky : ∀ source : PureWZ2ExtremalConfiguration sigma reentryLoss delta,
      ∀ normalized : PureWZ2CroppedCriticalNormalizationData
        (outputLoss := data.reentryNormalizationLoss) source
          normalizationExponent,
      ∀ rho : WZ2PaperRequestedScale delta,
        Real.rpow delta (1 - stickyLoss) ≤ rho.1 →
        rho.1 ≤ Real.rpow delta stickyLoss →
        Nonempty (PureWZ2PropStickyData
          (sigma := sigma) (outputLoss := stickyLoss)
          normalized.croppedRefined rho logExponent))
    (rho : WZ2PaperRequestedScale delta)
    (hrhoLower : Real.rpow delta (1 - stickyLoss) ≤ rho.1)
    (hrhoUpper : rho.1 ≤ Real.rpow delta stickyLoss) :
    Nonempty (PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      data.normalization.croppedRefined rho logExponent) := by
  exact hSticky data.ordinarySource data.normalization rho
    hrhoLower hrhoUpper

/-- Execute the third preselected kernel in the paper's Lemma 4.11 chain on
the current refinement of the outer `rho`-family.  This is the Proposition
6.2 call used to prove the second point-centered estimate at `sqrt rho`; the
later whole-cell balancing for full-grain selection remains a separate step. -/
theorem proposition63CurrentShadingReentry_thirdSticky
    {delta sigma initialInputLoss normalizationLoss reentryLoss
      outputLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (data : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) initialNormalized current)
    (schedule : Proposition63RichThreeCallScheduleData sigma outputLoss)
    (hreentryLoss : reentryLoss = schedule.third.sourceLoss)
    (hnormalizationLoss :
      data.reentryNormalizationLoss = schedule.third.normalizationLoss)
    (hdeltaSchedule : delta ≤ schedule.third.delta₀)
    (requested : WZ2PaperRequestedScale delta)
    (requestedLower : Real.rpow delta (1 - outputLoss) ≤ requested.1)
    (requestedUpper : requested.1 ≤ Real.rpow delta outputLoss) :
    Nonempty (PureWZ2PropStickyData
      (sigma := sigma) (outputLoss := outputLoss)
      data.normalization.croppedRefined requested 61) := by
  have hsourceLoss : 0 < reentryLoss := by
    rw [hreentryLoss]
    exact schedule.third.sourceLoss_pos
  have run := schedule.third.runPlain delta data.reentry_extremal.delta_pos
    hdeltaSchedule
  rw [← hreentryLoss, ← hnormalizationLoss] at run
  exact run data.normalization.croppedFamily
    data.normalization.croppedRefined
    (data.normalization.toPropStickyReentryData hsourceLoss
      data.reentry_normalization_loss_pos)
    requested requestedLower requestedUpper

/-- Exact first-sticky invocation after the preliminary Lemmas 4.8/4.12
refinement has been re-entered through its ordinary trace.  The local-grain
map returned here is the restriction of the pre-sticky map to the exact
sticky source shading. -/
theorem proposition63InitialLocalGrainReentry_sticky
    {delta sigma initialInputLoss normalizationLoss reentryLoss localLoss
      localIncidence stickyLoss : ℝ}
    {L : NNReal}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent logExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource normalizationExponent}
    {localShading : WZ1PaperTubeShading initialNormalized.croppedFamily}
    {localGrains : Proposition63InitialWeakLocalGrainData
      (incidence := localIncidence) localShading sigma
      (Kakeya.realRpowENN delta (-localLoss)) L}
    (data : Proposition63InitialLocalGrainReentryData
      (reentryLoss := reentryLoss)
      initialNormalized localShading localGrains)
    (hSticky : ∀ source : PureWZ2ExtremalConfiguration sigma reentryLoss delta,
      ∀ normalized : PureWZ2CroppedCriticalNormalizationData
        (outputLoss := data.reentryNormalizationLoss) source
          normalizationExponent,
      ∀ rho : WZ2PaperRequestedScale delta,
        Real.rpow delta (1 - stickyLoss) ≤ rho.1 →
        rho.1 ≤ Real.rpow delta stickyLoss →
        Nonempty (PureWZ2PropStickyData
          (sigma := sigma) (outputLoss := stickyLoss)
          normalized.croppedRefined rho logExponent))
    (rho : WZ2PaperRequestedScale delta)
    (hrhoLower : Real.rpow delta (1 - stickyLoss) ≤ rho.1)
    (hrhoUpper : rho.1 ≤ Real.rpow delta stickyLoss) :
    ∃ sticky : PureWZ2PropStickyData
        (sigma := sigma) (outputLoss := stickyLoss)
        data.normalization.croppedRefined rho logExponent,
      Nonempty (Proposition63InitialWeakLocalGrainData
        (incidence := localIncidence) data.normalization.croppedRefined sigma
        (Kakeya.realRpowENN delta (-localLoss)) L) := by
  rcases proposition63CurrentShadingReentry_sticky data hSticky rho
      hrhoLower hrhoUpper with ⟨sticky⟩
  exact ⟨sticky, ⟨data.normalizedLocalGrains⟩⟩

/-- Run the Node 4 rich terminal kernel on an arbitrary current-shading
re-entry.  The result keeps the public sticky output and the terminal
multiplicity certificate generated by the same Node 3 producer. -/
theorem proposition63CurrentShadingReentry_richTerminalSticky
    {delta sigma initialInputLoss normalizationLoss reentryLoss
      stickyLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {normalizationExponent : ℕ}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource
      normalizationExponent}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (data : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) initialNormalized current)
    (schedule : Proposition63RichStickyKernelScheduleData sigma stickyLoss)
    (hreentryLoss : reentryLoss = schedule.sourceLoss)
    (hnormalizationLoss :
      data.reentryNormalizationLoss = schedule.normalizationLoss)
    (hdeltaSchedule : delta ≤ schedule.delta₀)
    (rho : WZ2PaperRequestedScale delta)
    (rho_lower : Real.rpow delta (1 - stickyLoss) ≤ rho.1)
    (rho_upper : rho.1 ≤ Real.rpow delta stickyLoss) :
    Nonempty (Proposition63RichTerminalStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      data.normalization.croppedRefined
      (data.normalization.toPropStickyReentryData
        (by rw [hreentryLoss]; exact schedule.sourceLoss_pos)
        data.reentry_normalization_loss_pos) rho) := by
  have reentryLoss_pos : 0 < reentryLoss := by
    rw [hreentryLoss]
    exact schedule.sourceLoss_pos
  have produce := schedule.runTerminal delta data.reentry_extremal.delta_pos
    hdeltaSchedule
  rw [← hreentryLoss, ← hnormalizationLoss] at produce
  exact produce data.normalization.croppedFamily
    data.normalization.croppedRefined
    (data.normalization.toPropStickyReentryData
      reentryLoss_pos data.reentry_normalization_loss_pos)
    rho rho_lower rho_upper

/-- Compatibility projection of the rich terminal call.  This retains the
exact coarse ordinary normalization needed by a dependent second call while
allowing existing Node 4 consumers to ignore the multiplicity certificate. -/
theorem proposition63CurrentShadingReentry_richSticky
    {delta sigma initialInputLoss normalizationLoss reentryLoss
      stickyLoss : ℝ}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource 0}
    {current : WZ1PaperTubeShading initialNormalized.croppedFamily}
    (data : Proposition63CurrentShadingReentryData
      (reentryLoss := reentryLoss) initialNormalized current)
    (schedule : Proposition63RichStickyKernelScheduleData sigma stickyLoss)
    (hreentryLoss : reentryLoss = schedule.sourceLoss)
    (hnormalizationLoss :
      data.reentryNormalizationLoss = schedule.normalizationLoss)
    (hdeltaSchedule : delta ≤ schedule.delta₀)
    (initialAxialWindow : ∀ index point,
      point ∈ initialNormalized.frame ''
          initialNormalized.ordinaryRefined.carrier index →
        |point (2 : Fin 3)| ≤ 1 / 8)
    (rho : WZ2PaperRequestedScale delta)
    (rho_lower : Real.rpow delta (1 - stickyLoss) ≤ rho.1)
    (rho_upper : rho.1 ≤ Real.rpow delta stickyLoss) :
    Nonempty (PureWZ2ReentrantPropStickyData
      (sigma := sigma) (outputLoss := stickyLoss)
      data.normalization.croppedRefined rho 0 61) := by
  rcases proposition63CurrentShadingReentry_richTerminalSticky data schedule
      hreentryLoss hnormalizationLoss hdeltaSchedule rho rho_lower rho_upper
    with ⟨rich⟩
  have axialWindow : ∀ index point,
      point ∈ data.normalization.frame ''
          data.normalization.ordinaryRefined.carrier index →
        |point (2 : Fin 3)| ≤ 1 / 8 := by
    intro index point hpoint
    dsimp [Proposition63CurrentShadingReentryData.normalization,
      proposition63IdentityFullOrdinaryNormalization] at hpoint
    exact data.ordinaryAxialWindowOf initialAxialWindow index point <| by
      simpa using hpoint
  exact ⟨rich.toReentrant <| by
    simpa [PureWZ2CroppedCriticalNormalizationData.toPropStickyReentryData]
      using axialWindow⟩

/-- Rich first sticky invocation after preliminary local-grain re-entry.  In
addition to the ordinary sticky output, this retains the exact ordinary
normalization of the produced coarse pair for the dependent second call. -/
theorem proposition63InitialLocalGrainReentry_richSticky
    {delta sigma initialInputLoss normalizationLoss reentryLoss localLoss
      localIncidence stickyLoss : ℝ}
    {L : NNReal}
    {initialSource : PureWZ2ExtremalConfiguration sigma initialInputLoss delta}
    {initialNormalized : PureWZ2CroppedCriticalNormalizationData
      (outputLoss := normalizationLoss) initialSource 0}
    {localShading : WZ1PaperTubeShading initialNormalized.croppedFamily}
    {localGrains : Proposition63InitialWeakLocalGrainData
      (incidence := localIncidence) localShading sigma
      (Kakeya.realRpowENN delta (-localLoss)) L}
    (data : Proposition63InitialLocalGrainReentryData
      (reentryLoss := reentryLoss) initialNormalized localShading localGrains)
    (schedule : Proposition63RichStickyKernelScheduleData sigma stickyLoss)
    (hreentryLoss : reentryLoss = schedule.sourceLoss)
    (hnormalizationLoss :
      data.reentryNormalizationLoss = schedule.normalizationLoss)
    (hdeltaSchedule : delta ≤ schedule.delta₀)
    (initialAxialWindow : ∀ index point,
      point ∈ initialNormalized.frame ''
          initialNormalized.ordinaryRefined.carrier index →
        |point (2 : Fin 3)| ≤ 1 / 8)
    (rho : WZ2PaperRequestedScale delta)
    (rho_lower : Real.rpow delta (1 - stickyLoss) ≤ rho.1)
    (rho_upper : rho.1 ≤ Real.rpow delta stickyLoss) :
    ∃ sticky : PureWZ2ReentrantPropStickyData
        (sigma := sigma) (outputLoss := stickyLoss)
        data.normalization.croppedRefined rho 0 61,
      Nonempty (Proposition63InitialWeakLocalGrainData
        (incidence := localIncidence) data.normalization.croppedRefined sigma
        (Kakeya.realRpowENN delta (-localLoss)) L) := by
  rcases proposition63CurrentShadingReentry_richSticky data schedule
      hreentryLoss hnormalizationLoss hdeltaSchedule initialAxialWindow rho
      rho_lower rho_upper with ⟨sticky⟩
  exact ⟨sticky, ⟨data.normalizedLocalGrains⟩⟩

end Kakeya.Assouad.PureWZ2

end
