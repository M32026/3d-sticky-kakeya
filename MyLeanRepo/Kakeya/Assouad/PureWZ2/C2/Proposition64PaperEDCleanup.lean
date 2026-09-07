import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.Proposition64Lemma35LocalCleanup
import MyLeanRepo.Kakeya.Assouad.PureWZ2.C2.GrainRestriction
import MyLeanRepo.Kakeya.Assouad.Targets.WeightedEssentiallyDistinctSelection
import MyLeanRepo.Kakeya.Assouad.AnisotropicRescaling.SelectedTubeFamily
import MyLeanRepo.Kakeya.Assouad.Targets.TubeParameterPrismGeometry

/-!
# Paper essential-distinctness cleanup for Proposition 6.4

The paper's final cleanup uses Definition 2.12 essential distinctness, namely
the symmetric centered-doubled-carrier non-containment relation.  This file
keeps that relation separate from the older volume-overlap notion and performs
the weighted finite selection on the actual final cubical shading.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory Set

attribute [local instance] Classical.propDecidable

/-- Conflict relation complementary to ordinary paper essential
distinctness, with unequal indices built in to make it irreflexive. -/
def pureWZ2Proposition64PaperConflict
    {delta : ℝ} (family : Kakeya.Streamlined.TubeFamily delta)
    (first second : Fin family.card) : Prop :=
  first ≠ second ∧
    ¬(¬(family.tube first).carrier ⊆
        wz2PaperCenteredDilatedCarrier 2 (family.tube second) ∧
      ¬(family.tube second).carrier ⊆
        wz2PaperCenteredDilatedCarrier 2 (family.tube first))

theorem pureWZ2Proposition64PaperConflict_symm
    {delta : ℝ} (family : Kakeya.Streamlined.TubeFamily delta) :
    ∀ first second,
      pureWZ2Proposition64PaperConflict family first second →
        pureWZ2Proposition64PaperConflict family second first := by
  intro first second hconflict
  refine ⟨hconflict.1.symm, ?_⟩
  intro hcompatible
  exact hconflict.2 ⟨hcompatible.2, hcompatible.1⟩

theorem pureWZ2Proposition64PaperConflict_irrefl
    {delta : ℝ} (family : Kakeya.Streamlined.TubeFamily delta) :
    ∀ index, ¬pureWZ2Proposition64PaperConflict family index index := by
  intro index hconflict
  exact hconflict.1 rfl

/-- A cluster in the four vertical-line parameters has all of its cropped
paper carriers in one convex parameter prism. -/
theorem pureWZ2Proposition64_paperParameterCluster_prism
    {delta radius : ℝ} (hdelta : 0 < delta) (hdeltaRadius : delta ≤ radius)
    (family : Kakeya.Streamlined.TubeFamily delta)
    (hline : WZ1PaperIsLineClass family)
    (indices : Finset (Fin family.card)) (reference : Fin family.card)
    (hcluster : ∀ index ∈ indices,
      |(tubeParams (F := family) index).a -
          (tubeParams (F := family) reference).a| ≤ radius ∧
      |(tubeParams (F := family) index).b -
          (tubeParams (F := family) reference).b| ≤ radius ∧
      |(tubeParams (F := family) index).c -
          (tubeParams (F := family) reference).c| ≤ radius ∧
      |(tubeParams (F := family) index).d -
          (tubeParams (F := family) reference).d| ≤ radius) :
    ∀ index ∈ indices,
      wz1PaperTubeCarrier (family.tube index) ⊆
        tubeParameterPrism (tubeParams (F := family) reference)
          (20 * radius) := by
  intro index hindex point hpoint
  let tube := family.tube index
  let sourceParams := tubeParams (F := family) index
  let referenceParams := tubeParams (F := family) reference
  have hheightAbs : |point 2| ≤ 1 := by
    simpa [Kakeya.Streamlined.axisBox] using hpoint.2.2.2
  have hheight : point 2 ∈ Set.Icc (-1 : ℝ) 1 := abs_le.mp hheightAbs
  rcases exists_dist_le_of_mem_cthickening_closed
      (isClosed_tubeAxisLine tube)
      (mul_nonneg (by norm_num) hdelta.le) hpoint.1 with
    ⟨axisPoint, haxisPoint, hdistance⟩
  have htubeVertical : tube.direction 2 ≠ 0 := by
    intro hzero
    have h := (hline index).vertical
    rw [hzero, abs_zero] at h
    norm_num at h
  have haxisZero : axisPoint 0 =
      sourceParams.a + sourceParams.c * axisPoint 2 :=
    tubeAxisLine_coord_zero tube htubeVertical haxisPoint
  have haxisOne : axisPoint 1 =
      sourceParams.b + sourceParams.d * axisPoint 2 :=
    tubeAxisLine_coord_one tube htubeVertical haxisPoint
  have hcoordinateDistance : ∀ coordinate : Fin 3,
      |point coordinate - axisPoint coordinate| ≤ 6 * delta := by
    intro coordinate
    have hcoord := PiLp.norm_apply_le (point - axisPoint) coordinate
    have hcoord' : |point coordinate - axisPoint coordinate| ≤
        ‖point - axisPoint‖ := by
      simpa [Real.norm_eq_abs] using hcoord
    exact hcoord'.trans (by simpa [dist_eq_norm] using hdistance)
  have hsourceSlope := tubeParams_cd_bounds hline.vertical index
  have hclusterIndex := hcluster index hindex
  have hcoordinateBound :
      ∀ (coordinate : Fin 3)
        (sourceIntercept referenceIntercept sourceSlope referenceSlope : ℝ),
        axisPoint coordinate = sourceIntercept + sourceSlope * axisPoint 2 →
        |sourceIntercept - referenceIntercept| ≤ radius →
        |sourceSlope| ≤ 2 →
        |sourceSlope - referenceSlope| ≤ radius →
        |point coordinate -
          (referenceIntercept + referenceSlope * point 2)| ≤ 20 * radius := by
    intro coordinate sourceIntercept referenceIntercept sourceSlope
      referenceSlope haxisCoordinate hintercept hslope hslopeDifference
    have haxisHeight : |axisPoint 2 - point 2| ≤ 6 * delta := by
      simpa [abs_sub_comm] using hcoordinateDistance (2 : Fin 3)
    have hradiusNonneg : 0 ≤ radius := hdelta.le.trans hdeltaRadius
    have hdecompose : point coordinate -
        (referenceIntercept + referenceSlope * point 2) =
      (point coordinate - axisPoint coordinate) +
        (sourceIntercept - referenceIntercept) +
        sourceSlope * (axisPoint 2 - point 2) +
        (sourceSlope - referenceSlope) * point 2 := by
      rw [haxisCoordinate]
      ring
    rw [hdecompose]
    calc
      |(point coordinate - axisPoint coordinate) +
          (sourceIntercept - referenceIntercept) +
          sourceSlope * (axisPoint 2 - point 2) +
          (sourceSlope - referenceSlope) * point 2| ≤
        |point coordinate - axisPoint coordinate| +
          |sourceIntercept - referenceIntercept| +
          |sourceSlope| * |axisPoint 2 - point 2| +
          |sourceSlope - referenceSlope| * |point 2| := by
            calc
              _ ≤ |(point coordinate - axisPoint coordinate) +
                    (sourceIntercept - referenceIntercept) +
                    sourceSlope * (axisPoint 2 - point 2)| +
                    |(sourceSlope - referenceSlope) * point 2| :=
                  abs_add_le _ _
              _ ≤ (|(point coordinate - axisPoint coordinate) +
                    (sourceIntercept - referenceIntercept)| +
                    |sourceSlope * (axisPoint 2 - point 2)|) +
                    |(sourceSlope - referenceSlope) * point 2| := by
                  gcongr
                  exact abs_add_le _ _
              _ ≤ ((|point coordinate - axisPoint coordinate| +
                    |sourceIntercept - referenceIntercept|) +
                    |sourceSlope * (axisPoint 2 - point 2)|) +
                    |(sourceSlope - referenceSlope) * point 2| := by
                  gcongr
                  exact abs_add_le _ _
              _ = _ := by rw [abs_mul, abs_mul]
      _ ≤ 6 * delta + radius + 2 * (6 * delta) + radius * 1 := by
        exact add_le_add
          (add_le_add
            (add_le_add (hcoordinateDistance coordinate) hintercept)
            (mul_le_mul hslope haxisHeight (abs_nonneg _) (by norm_num)))
          (mul_le_mul hslopeDifference hheightAbs (abs_nonneg _)
            hradiusNonneg)
      _ ≤ 20 * radius := by linarith
  have hzero : |point 0 -
      (referenceParams.a + referenceParams.c * point 2)| ≤ 20 * radius :=
    hcoordinateBound 0 sourceParams.a referenceParams.a
      sourceParams.c referenceParams.c haxisZero hclusterIndex.1
      hsourceSlope.1 hclusterIndex.2.2.1
  have hone : |point 1 -
      (referenceParams.b + referenceParams.d * point 2)| ≤ 20 * radius :=
    hcoordinateBound 1 sourceParams.b referenceParams.b
      sourceParams.d referenceParams.d haxisOne hclusterIndex.2.1
      hsourceSlope.2 hclusterIndex.2.2.2
  exact ⟨hheight, hzero, hone⟩

/-- Cropped top-level CWA implies the indexed four-parameter Frostman bound
needed for the exact-image conflict-degree estimate. -/
theorem pureWZ2Proposition64_parameterFrostman_of_croppedCWA
    {delta : ℝ} (hdelta : 0 < delta)
    (family : Kakeya.Streamlined.TubeFamily delta)
    (hline : WZ1PaperIsLineClass family) (C : ENNReal)
    (hcwa : WZ2PaperConvexWolffBound family C) :
    TubeParameterFrostmanBound family (3200 * C) := by
  intro radius hdeltaRadius hradiusOne reference
  let indices : Finset (Fin family.card) :=
    Finset.univ.filter fun index =>
      |(tubeParams index).a - (tubeParams reference).a| ≤ radius ∧
      |(tubeParams index).b - (tubeParams reference).b| ≤ radius ∧
      |(tubeParams index).c - (tubeParams reference).c| ≤ radius ∧
      |(tubeParams index).d - (tubeParams reference).d| ≤ radius
  have hradius : 0 < radius := hdelta.trans_le hdeltaRadius
  have hcluster : ∀ index ∈ indices,
      |(tubeParams index).a - (tubeParams reference).a| ≤ radius ∧
      |(tubeParams index).b - (tubeParams reference).b| ≤ radius ∧
      |(tubeParams index).c - (tubeParams reference).c| ≤ radius ∧
      |(tubeParams index).d - (tubeParams reference).d| ≤ radius := by
    intro index hindex
    exact (Finset.mem_filter.mp hindex).2
  let prism := tubeParameterPrism (tubeParams reference) (20 * radius)
  have hcontained : ∀ index ∈ indices,
      wz1PaperTubeCarrier (family.tube index) ⊆ prism :=
    pureWZ2Proposition64_paperParameterCluster_prism hdelta hdeltaRadius
      family hline indices reference hcluster
  have hindicesSubset : indices ⊆
      (wz1PaperBodyFamily family).containedIndices prism := by
    intro index hindex
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcontained index hindex⟩
  have hcard : (indices.card : ENNReal) ≤
      (wz1PaperBodyFamily family).containedCount prism := by
    change (indices.card : ENNReal) ≤
      ((wz1PaperBodyFamily family).containedIndices prism).card
    exact_mod_cast Finset.card_le_card hindicesSubset
  have hprism := tube_parameter_prism_geometry
    (tubeParams reference) (20 * radius) (by positivity)
  have hvolume : volume prism ≤ ENNReal.ofReal (3200 * radius ^ 2) := by
    have h := hprism.2
    have heq : (8 : ℝ) * (20 * radius) ^ 2 = 3200 * radius ^ 2 := by ring
    simpa [prism, heq] using h
  have hmain : (indices.card : ENNReal) ≤
      C * ENNReal.ofReal (3200 * radius ^ 2) * family.enncard := by
    calc
      (indices.card : ENNReal) ≤
          (wz1PaperBodyFamily family).containedCount prism := hcard
      _ ≤ C * volume prism * family.enncard := hcwa prism hprism.1
      _ ≤ C * ENNReal.ofReal (3200 * radius ^ 2) * family.enncard := by
        gcongr
  have hrpow : ENNReal.ofReal (3200 * radius ^ 2) =
      3200 * Kakeya.realRpowENN radius 2 := by
    simp only [Kakeya.realRpowENN]
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3200)]
    norm_num
  rw [hrpow] at hmain
  simpa [indices, mul_assoc, mul_left_comm, mul_comm] using hmain

/-- Weighted Definition-2.12 essentially-distinct cleanup of a paper shading.
The sole geometric input is the conflict degree; all mass and reindexing
conclusions are deterministic. -/
theorem pureWZ2Proposition64_weightedPaperEDSelection
    {delta : ℝ} (family : Kakeya.Streamlined.TubeFamily delta)
    (shading : WZ1PaperTubeShading family) (D : ℕ)
    (hdegree : ∀ index,
      (Finset.univ.filter fun other =>
        pureWZ2Proposition64PaperConflict family index other).card ≤ D) :
    ∃ selected : Finset (Fin family.card),
      let subfamily :=
        Kakeya.Streamlined.TubeSubfamily.fromFinset family selected
      let selectedShading := restrictPaperShading subfamily shading
      WZ2PaperOrdinaryIsEssentiallyDistinct subfamily.family ∧
        selectedShading.union ⊆ shading.union ∧
        shading.mass ≤ (D + 1 : ENNReal) * selectedShading.mass := by
  let weight : Fin family.card → ENNReal := fun index =>
    volume (shading.carrier index)
  rcases weighted_symmetric_irreflexive_selection weight
      (pureWZ2Proposition64PaperConflict family)
      (pureWZ2Proposition64PaperConflict_symm family)
      (pureWZ2Proposition64PaperConflict_irrefl family) hdegree with
    ⟨selected, hselected, hmass⟩
  let subfamily :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset family selected
  let selectedShading := restrictPaperShading subfamily shading
  refine ⟨selected, ?_, ?_, ?_⟩
  · intro first second hne
    have hfirst : subfamily.embedding first ∈ selected :=
      Finset.orderEmbOfFin_mem selected rfl first
    have hsecond : subfamily.embedding second ∈ selected :=
      Finset.orderEmbOfFin_mem selected rfl second
    have hindexNe : subfamily.embedding first ≠ subfamily.embedding second :=
      subfamily.embedding.injective.ne hne
    have hcompatible := hselected _ hfirst _ hsecond hindexNe
    unfold pureWZ2Proposition64PaperConflict at hcompatible
    by_contra hnot
    apply hcompatible
    refine ⟨hindexNe, ?_⟩
    intro hambient
    apply hnot
    constructor
    · rw [subfamily.tube_eq first, subfamily.tube_eq second]
      exact hambient.1
    · rw [subfamily.tube_eq first, subfamily.tube_eq second]
      exact hambient.2
  · rintro point ⟨index, hpoint⟩
    exact ⟨subfamily.embedding index, hpoint⟩
  · change (∑ index, volume (shading.carrier index)) ≤
      (D + 1 : ENNReal) *
        ∑ index : Fin subfamily.family.card,
          volume (shading.carrier (subfamily.embedding index))
    have hselectedSum :
        (∑ index : Fin subfamily.family.card,
          volume (shading.carrier (subfamily.embedding index))) =
        ∑ index ∈ selected, volume (shading.carrier index) := by
      change (∑ index : Fin selected.card,
          volume (shading.carrier (selected.orderEmbOfFin rfl index))) = _
      let e := selected.orderIsoOfFin rfl
      calc
        (∑ index : Fin selected.card,
            volume (shading.carrier ((e index : selected) : Fin family.card))) =
          ∑ index : selected, volume (shading.carrier index.1) :=
            Equiv.sum_comp e.toEquiv
              (fun index : selected => volume (shading.carrier index.1))
        _ = ∑ index ∈ selected, volume (shading.carrier index) := by
          simpa using Finset.sum_attach selected
            (fun index => volume (shading.carrier index))
    rw [hselectedSum]
    change (∑ index : Fin family.card, volume (shading.carrier index)) ≤ _
    simpa only [weight] using hmass

/-- Paper-ED cleanup with an ENNReal conflict bound, performed after deleting
zero-mass carriers.  This is the order used by Proposition 6.4: every tube
entering the geometric degree estimate has an occupied shaded carrier, and
the preliminary deletion costs no mass. -/
theorem pureWZ2Proposition64_weightedPositivePaperEDSelection
    {delta : ℝ} (family : Kakeya.Streamlined.TubeFamily delta)
    (shading : WZ1PaperTubeShading family) (K : ENNReal)
    (hdegree : ∀ index : Fin (paperPositiveMassSubfamily shading).family.card,
      (((Finset.univ.filter fun other =>
        pureWZ2Proposition64PaperConflict
          (paperPositiveMassSubfamily shading).family index other).card :
          ENNReal)) ≤ K) :
    ∃ selected : Finset (Fin (paperPositiveMassSubfamily shading).family.card),
      let positive := paperPositiveMassSubfamily shading
      let positiveShading := restrictPaperShading positive shading
      let subfamily := Kakeya.Streamlined.TubeSubfamily.fromFinset
        positive.family selected
      let selectedShading := restrictPaperShading subfamily positiveShading
      WZ2PaperOrdinaryIsEssentiallyDistinct subfamily.family ∧
        selectedShading.union ⊆ shading.union ∧
        shading.mass ≤ (K + 1) * selectedShading.mass ∧
        ∀ index, 0 < volume (selectedShading.carrier index) := by
  let positive := paperPositiveMassSubfamily shading
  let positiveShading := restrictPaperShading positive shading
  let weight : Fin positive.family.card → ENNReal := fun index =>
    volume (positiveShading.carrier index)
  rcases weighted_symmetric_irreflexive_selection_of_ennreal_degree weight
      (pureWZ2Proposition64PaperConflict positive.family)
      (pureWZ2Proposition64PaperConflict_symm positive.family)
      (pureWZ2Proposition64PaperConflict_irrefl positive.family) K hdegree with
    ⟨selected, hselected, hmass⟩
  let subfamily := Kakeya.Streamlined.TubeSubfamily.fromFinset
    positive.family selected
  let selectedShading := restrictPaperShading subfamily positiveShading
  refine ⟨selected, ?_, ?_, ?_, ?_⟩
  · intro first second hne
    have hfirst : subfamily.embedding first ∈ selected :=
      Finset.orderEmbOfFin_mem selected rfl first
    have hsecond : subfamily.embedding second ∈ selected :=
      Finset.orderEmbOfFin_mem selected rfl second
    have hindexNe : subfamily.embedding first ≠ subfamily.embedding second :=
      subfamily.embedding.injective.ne hne
    have hnoconflict := hselected _ hfirst _ hsecond hindexNe
    unfold pureWZ2Proposition64PaperConflict at hnoconflict
    by_contra hnot
    apply hnoconflict
    refine ⟨hindexNe, ?_⟩
    intro hambient
    apply hnot
    constructor
    · rw [subfamily.tube_eq first, subfamily.tube_eq second]
      exact hambient.1
    · rw [subfamily.tube_eq first, subfamily.tube_eq second]
      exact hambient.2
  · rintro point ⟨index, hpoint⟩
    exact ⟨positive.embedding (subfamily.embedding index), hpoint⟩
  · have hpositiveMass : positiveShading.mass = shading.mass := by
      exact restrictPaperShading_positiveMass_mass shading
    have hselectedSum :
        selectedShading.mass =
          ∑ index ∈ selected, volume (positiveShading.carrier index) := by
      rw [restrictPaperShading_mass]
      let equivalence := selected.orderIsoOfFin rfl
      calc
        (∑ index : Fin selected.card,
            volume (positiveShading.carrier
              (selected.orderEmbOfFin rfl index))) =
            ∑ index : selected, volume (positiveShading.carrier index.1) :=
          Equiv.sum_comp equivalence.toEquiv
            (fun index : selected => volume (positiveShading.carrier index.1))
        _ = ∑ index ∈ selected, volume (positiveShading.carrier index) := by
          simpa using Finset.sum_attach selected
            (fun index => volume (positiveShading.carrier index))
    calc
      shading.mass = positiveShading.mass := hpositiveMass.symm
      _ = ∑ index, weight index := rfl
      _ ≤ (K + 1) * ∑ index ∈ selected, weight index := hmass
      _ = (K + 1) * selectedShading.mass := by rw [hselectedSum]
  · intro index
    change 0 < volume
      (positiveShading.carrier (subfamily.embedding index))
    have hpositive :
        volume (positiveShading.carrier (subfamily.embedding index)) ≠ 0 := by
      change volume (shading.carrier
        (positive.embedding (subfamily.embedding index))) ≠ 0
      exact (Finset.mem_filter.mp
        (Finset.orderEmbOfFin_mem (paperPositiveMassIndices shading) rfl
          (subfamily.embedding index))).2
    exact bot_lt_iff_ne_bot.mpr hpositive

/-- Data retained after the paper-ED weighted selection. -/
structure PureWZ2Proposition64PaperEDCleanupData
    {delta : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    (sourceShading : WZ1PaperTubeShading family) (K : ENNReal) where
  subfamily : Kakeya.Streamlined.TubeSubfamily family
  finalShading : WZ1PaperTubeShading subfamily.family
  shading_eq : finalShading = restrictPaperShading subfamily sourceShading
  essentially_distinct : WZ2PaperOrdinaryIsEssentiallyDistinct subfamily.family
  union_subset : finalShading.union ⊆ sourceShading.union
  mass_retention : sourceShading.mass ≤
    (K + 1) * finalShading.mass
  carrier_volume_pos : ∀ index,
    0 < volume (finalShading.carrier index)
  sourceParent : Fin subfamily.family.card → Fin family.card
  sourceParent_eq : sourceParent = subfamily.embedding
  tube_provenance : ∀ index,
    subfamily.family.tube index = family.tube (sourceParent index)

/-- Package the weighted paper-ED selection and retain the exact source
index of each selected tube. -/
theorem pureWZ2Proposition64_paperEDCleanup
    {delta : ℝ} (family : Kakeya.Streamlined.TubeFamily delta)
    (shading : WZ1PaperTubeShading family) (D : ℕ)
    (hdegree : ∀ index,
      (Finset.univ.filter fun other =>
        pureWZ2Proposition64PaperConflict family index other).card ≤ D) :
    Nonempty (PureWZ2Proposition64PaperEDCleanupData shading (D : ENNReal)) := by
  rcases pureWZ2Proposition64_weightedPaperEDSelection family shading D
      hdegree with ⟨selected, hdistinct, hunion, hmass⟩
  let retained := selected.filter fun index =>
    volume (shading.carrier index) ≠ 0
  let retainedSubfamily :=
    Kakeya.Streamlined.TubeSubfamily.fromFinset family retained
  have hretainedDistinct :
      WZ2PaperOrdinaryIsEssentiallyDistinct retainedSubfamily.family := by
    intro first second hne
    let inclusion : Fin retainedSubfamily.family.card ↪
        Fin (Kakeya.Streamlined.TubeSubfamily.fromFinset family selected).family.card :=
      Kakeya.Streamlined.TubeSubfamily.fromFinsetInclusion family retained selected
        (Finset.filter_subset _ _)
    have hinclusionNe : inclusion first ≠ inclusion second := inclusion.injective.ne hne
    have h := hdistinct (inclusion first) (inclusion second) hinclusionNe
    simpa only [retainedSubfamily, inclusion,
      Kakeya.Streamlined.TubeSubfamily.fromFinsetInclusion_ambient,
      Kakeya.Streamlined.TubeSubfamily.tube_eq] using h
  have hretainedMass : shading.mass ≤ (D + 1 : ENNReal) *
      (restrictPaperShading retainedSubfamily shading).mass := by
    have hsum : (∑ index ∈ retained, volume (shading.carrier index)) =
        ∑ index ∈ selected, volume (shading.carrier index) := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro index hselectedIndex hnotRetained
      have hzero : ¬volume (shading.carrier index) ≠ 0 := by
        simpa [retained, hselectedIndex] using hnotRetained
      exact not_ne_iff.mp hzero
    have hselectedMass :
        (restrictPaperShading
          (Kakeya.Streamlined.TubeSubfamily.fromFinset family selected)
            shading).mass =
        ∑ index ∈ retained, volume (shading.carrier index) := by
      rw [restrictPaperShading_mass]
      let e := selected.orderIsoOfFin rfl
      calc
        (∑ index : Fin selected.card, volume
            (shading.carrier (selected.orderEmbOfFin rfl index))) =
          ∑ index : selected, volume (shading.carrier index.1) :=
            Equiv.sum_comp e.toEquiv
              (fun index : selected => volume (shading.carrier index.1))
        _ = ∑ index ∈ selected, volume (shading.carrier index) := by
          simpa using Finset.sum_attach selected
            (fun index => volume (shading.carrier index))
        _ = ∑ index ∈ retained, volume (shading.carrier index) := hsum.symm
    have hretainedMassEq :
        (restrictPaperShading retainedSubfamily shading).mass =
          ∑ index ∈ retained, volume (shading.carrier index) := by
      rw [restrictPaperShading_mass]
      let e := retained.orderIsoOfFin rfl
      calc
        (∑ index : Fin retained.card, volume
            (shading.carrier (retained.orderEmbOfFin rfl index))) =
          ∑ index : retained, volume (shading.carrier index.1) :=
            Equiv.sum_comp e.toEquiv
              (fun index : retained => volume (shading.carrier index.1))
        _ = ∑ index ∈ retained, volume (shading.carrier index) := by
          simpa using Finset.sum_attach retained
            (fun index => volume (shading.carrier index))
    calc
      shading.mass ≤ (D + 1 : ENNReal) *
          (restrictPaperShading
            (Kakeya.Streamlined.TubeSubfamily.fromFinset family selected)
              shading).mass := hmass
      _ = (D + 1 : ENNReal) *
          (restrictPaperShading retainedSubfamily shading).mass := by
        rw [hselectedMass, hretainedMassEq]
  exact ⟨{
    subfamily := retainedSubfamily
    finalShading := restrictPaperShading
      retainedSubfamily shading
    shading_eq := rfl
    essentially_distinct := hretainedDistinct
    union_subset := by
      rintro point ⟨index, hpoint⟩
      exact ⟨retainedSubfamily.embedding index, hpoint⟩
    mass_retention := hretainedMass
    carrier_volume_pos := by
      intro index
      change 0 < volume (shading.carrier (retainedSubfamily.embedding index))
      have hmem : retainedSubfamily.embedding index ∈ retained :=
        Finset.orderEmbOfFin_mem retained rfl index
      have hne : volume (shading.carrier (retainedSubfamily.embedding index)) ≠ 0 :=
        (Finset.mem_filter.mp hmem).2
      exact bot_lt_iff_ne_bot.mpr hne
    sourceParent := retainedSubfamily.embedding
    sourceParent_eq := rfl
    tube_provenance := fun index =>
      retainedSubfamily.tube_eq index }⟩

/-- Package the exact weighted positive-carrier selection used by Proposition
6.4.  The final family is the genuine composite of zero-mass deletion and the
weighted conflict-free selection; the loss remains the ENNReal factor `K`. -/
theorem pureWZ2Proposition64_paperEDCleanup_of_ennreal_degree
    {delta : ℝ} (family : Kakeya.Streamlined.TubeFamily delta)
    (shading : WZ1PaperTubeShading family) (K : ENNReal)
    (hdegree : ∀ index : Fin (paperPositiveMassSubfamily shading).family.card,
      (((Finset.univ.filter fun other =>
        pureWZ2Proposition64PaperConflict
          (paperPositiveMassSubfamily shading).family index other).card :
          ENNReal)) ≤ K) :
    Nonempty (PureWZ2Proposition64PaperEDCleanupData shading K) := by
  rcases pureWZ2Proposition64_weightedPositivePaperEDSelection
      family shading K hdegree with
    ⟨selected, hdistinct, hunion, hmass, hpositive⟩
  let positive := paperPositiveMassSubfamily shading
  let positiveShading := restrictPaperShading positive shading
  let inner := Kakeya.Streamlined.TubeSubfamily.fromFinset
    positive.family selected
  let finalSubfamily := positive.comp inner
  let finalShading := restrictPaperShading finalSubfamily shading
  have hfinalShading : finalShading =
      restrictPaperShading inner positiveShading := rfl
  refine ⟨{
    subfamily := finalSubfamily
    finalShading := finalShading
    shading_eq := rfl
    essentially_distinct := ?_
    union_subset := ?_
    mass_retention := ?_
    carrier_volume_pos := ?_
    sourceParent := finalSubfamily.embedding
    sourceParent_eq := rfl
    tube_provenance := finalSubfamily.tube_eq }⟩
  · exact hdistinct
  · rw [hfinalShading]
    exact hunion
  · rw [hfinalShading]
    exact hmass
  · intro index
    rw [hfinalShading]
    exact hpositive index

namespace PureWZ2Proposition64PaperEDCleanupData

/-- Cubicality survives the paper-ED tube selection because each selected
carrier is retained literally. -/
theorem cubical
    {delta : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading family} {K : ENNReal}
    (data : PureWZ2Proposition64PaperEDCleanupData sourceShading K)
    (hsourceCubical : WZ1PaperIsCubicalShading sourceShading) :
    WZ1PaperIsCubicalShading data.finalShading := by
  rw [data.shading_eq]
  exact restrictPaperShading_cubical data.subfamily hsourceCubical

/-- A source line-class certificate restricts to the selected final family. -/
theorem lineClass
    {delta : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading family} {K : ENNReal}
    (data : PureWZ2Proposition64PaperEDCleanupData sourceShading K)
    (hsourceLine : WZ1PaperIsLineClass family) :
    WZ1PaperIsLineClass data.subfamily.family := by
  exact hsourceLine.subfamily data.subfamily

/-- It is enough to know the line-class condition on positive-mass source
carriers.  This is the form produced by the Proposition 6.4 conflict-degree
argument: zero-mass ambient tubes are discarded before the ED selection, and
the final cleanup records positivity of every retained carrier. -/
theorem lineClass_of_positiveSource
    {delta : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading family} {K : ENNReal}
    (data : PureWZ2Proposition64PaperEDCleanupData sourceShading K)
    (hpositive : WZ1PaperIsLineClass
      (paperPositiveMassSubfamily sourceShading).family) :
    WZ1PaperIsLineClass data.subfamily.family := by
  intro index
  have hsourcePositive :
      data.sourceParent index ∈ paperPositiveMassIndices sourceShading := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    have hvolume := data.carrier_volume_pos index
    rw [data.shading_eq] at hvolume
    change 0 < MeasureTheory.volume
      (sourceShading.carrier (data.subfamily.embedding index)) at hvolume
    rw [data.sourceParent_eq]
    exact hvolume.ne'
  let positiveIndex : Fin (paperPositiveMassSubfamily sourceShading).family.card :=
    (paperPositiveMassIndices sourceShading).orderIsoOfFin rfl |>.symm
      ⟨data.sourceParent index, hsourcePositive⟩
  have hpositiveIndex :
      (paperPositiveMassSubfamily sourceShading).embedding positiveIndex =
        data.sourceParent index := by
    exact congrArg Subtype.val
      ((paperPositiveMassIndices sourceShading).orderIsoOfFin rfl
        |>.apply_symm_apply ⟨data.sourceParent index, hsourcePositive⟩)
  rw [data.tube_provenance index]
  rw [← hpositiveIndex]
  simpa only [Kakeya.Streamlined.TubeSubfamily.tube_eq] using
    hpositive positiveIndex

/-- Local grains restrict to the same paper-ED selected family. -/
noncomputable def restrictLocalGrains
    {delta sigma : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading family} {K C : ENNReal}
    (data : PureWZ2Proposition64PaperEDCleanupData sourceShading K)
    (sourceLocal : PureWZ2LocalGrainData sourceShading sigma C) :
    PureWZ2LocalGrainData data.finalShading sigma C := by
  rw [data.shading_eq]
  exact sourceLocal.restrictSubfamilyWithShading data.subfamily
    (restrictPaperShading data.subfamily sourceShading)
    (fun _ _ hpoint => hpoint)

/-- A vertical normal bound restricts together with the local grains. -/
theorem restrictLocalGrains_vertical_bound
    {delta sigma : ℝ} {family : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : WZ1PaperTubeShading family} {K C : ENNReal}
    (data : PureWZ2Proposition64PaperEDCleanupData sourceShading K)
    (sourceLocal : PureWZ2LocalGrainData sourceShading sigma C)
    (hvertical : ∀ point, |sourceLocal.planeMap point 2| ≤ 1 / 2) :
    ∀ point : {point : Point3 // point ∈ data.finalShading.union},
      |(data.restrictLocalGrains sourceLocal).planeMap point 2| ≤ 1 / 2 := by
  rcases data with ⟨subfamily, finalShading, hshading, hdistinct, hunion,
    hmass, hpositive, sourceParent, hparent, htube⟩
  dsimp only at hshading ⊢
  subst finalShading
  intro point
  dsimp [restrictLocalGrains]
  exact hvertical ⟨point, by
    rcases point.property with ⟨index, hpoint⟩
    exact ⟨subfamily.embedding index, hpoint⟩⟩

end PureWZ2Proposition64PaperEDCleanupData

end Kakeya.Assouad

end
