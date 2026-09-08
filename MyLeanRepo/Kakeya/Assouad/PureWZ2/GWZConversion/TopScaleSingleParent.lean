import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.LocalizedDistinctReanchoring
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.ActiveParentGeometry
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.UnitScaleAggregateFrostman
import MyLeanRepo.Kakeya.Assouad.PureWZ2.GWZConversion.FrostmanConvexWolff

/-!
# Top-scale single-parent cover

Every localized reanchored tube has midpoint within the localization radius
of the common center.  A single radius-`8*A` tube whose axis segment passes
through that center therefore contains the whole final family.  The exact
GWZ scale-one structure supplies aggregate Frostman control for this one
complete literal strict fiber.
-/

noncomputable section

namespace Kakeya.Assouad

open MeasureTheory

attribute [local instance] Classical.propDecidable

/-- The fixed top parent through the localization center. -/
def pureWZ2TopParent
    (A : ℝ) (center : Point3) :
    Kakeya.DeltaTube (8 * A) where
  base := center
  direction := EuclideanSpace.single (0 : Fin 3) 1
  direction_unit := by simp

/-- All localized reanchored tubes lie in the fixed top parent. -/
theorem pureWZ2_localized_family_subset_top_parent
    {delta A : ℝ}
    (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1)
    (hA : 1 ≤ A)
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : Kakeya.Streamlined.TubeShading source}
    (fine : PureWZ2LocalizedDistinctReanchoringData sourceShading)
    (hfineRadius : fine.radius ≤ 1 / 4) :
    ∀ index,
      (fine.family.tube index).carrier ⊆
        (pureWZ2TopParent A fine.center).carrier := by
  intro index
  have hmidpointDistance :
      dist
          (wz2PaperTubeMidpoint (fine.family.tube index))
          fine.center ≤
        fine.radius + delta := by
    rcases fine.source_meets_ball index with
      ⟨point, hpointShading, hpointBall⟩
    have hpointSource :
        point ∈
          (source.tube (fine.sourceIndex index)).carrier :=
      sourceShading.subset_body
        (fine.sourceIndex index) hpointShading
    have hdistance :=
      pureWZ2_active_parent_center_distance
        hdelta hdelta (show (1 : ℝ) ≤ 1 by norm_num)
        (show delta ≤ (1 : ℝ) * delta by simp)
        hpointSource hpointBall
        (show
          (source.tube (fine.sourceIndex index)).carrier ⊆
            wz2PaperCenteredDilatedCarrier 1
              (source.tube (fine.sourceIndex index)) by
            simpa [wz2PaperCenteredDilatedCarrier,
              AffineMap.homothety])
    rw [fine.tube_eq_reanchored,
      pureWZ2ReanchoredTube_midpoint]
    simpa using hdistance
  intro point hpoint
  have hball :=
    pureWZ2_tube_carrier_subset_midpoint_ball
      hdelta.le (fine.family.tube index) hpoint
  have hpointCenter :
      dist point fine.center ≤
        delta + 1 / 2 + (fine.radius + delta) := by
    calc
      dist point fine.center ≤
          dist point
              (wz2PaperTubeMidpoint (fine.family.tube index)) +
            dist
              (wz2PaperTubeMidpoint (fine.family.tube index))
              fine.center :=
        dist_triangle _ _ _
      _ ≤ (delta + 1 / 2) + (fine.radius + delta) := by
        gcongr
        simpa [Metric.mem_closedBall] using hball
  have htopRadius :
      delta + 1 / 2 + (fine.radius + delta) ≤ 8 * A := by
    nlinarith
  exact
    Metric.mem_cthickening_of_dist_le
      point fine.center (8 * A)
      (Kakeya.unitSegment
        (pureWZ2TopParent A fine.center).base
        (pureWZ2TopParent A fine.center).direction)
      ⟨0, by norm_num, by simp [pureWZ2TopParent]⟩
      (hpointCenter.trans htopRadius)

/-- Final top-scale actual-John CWA constant. -/
def pureWZ2TopScaleConstant
    (inputConstant overlapConstant globalRetention : ENNReal) : ENNReal :=
  max 1
    (27 * pureWZ2UnitScaleAggregateFrostmanConstant
      inputConstant overlapConstant globalRetention)

/--
Package the top range as one literal single-parent scale witness.
-/
theorem pureWZ2_top_scale_single_parent
    {delta A : ℝ}
    (hdelta : 0 < delta)
    (hdeltaOne : delta ≤ 1)
    (hA : 1 ≤ A)
    {source : Kakeya.Streamlined.TubeFamily delta}
    {sourceShading : Kakeya.Streamlined.TubeShading source}
    (fine : PureWZ2LocalizedDistinctReanchoringData sourceShading)
    (hfineRadius : fine.radius ≤ 1 / 4)
    (selected :
      WZ2PaperPureTubeSubfamily fine.family)
    {inputConstant : ENNReal}
    {scale : Kakeya.Streamlined.AdmissibleScale delta}
    (scaleData :
      PureWZ2GWZScaleData
        (A := A) source scale inputConstant)
    (hscale : scale.1 = 1)
    (globalRetention : ENNReal)
    (global_cardinality_ratio :
      source.enncard ≤ globalRetention * selected.family.enncard) :
    Nonempty
      (WZ2PaperPureScaleCoverData
        selected.family (8 * A)
        (pureWZ2TopScaleConstant
          inputConstant
          (pureWZ2UnitScaleCompleteFiberOverlapBound A)
          globalRetention)) := by
  let topParent := pureWZ2TopParent A fine.center
  let coarse : Kakeya.Streamlined.TubeFamily (8 * A) :=
    {
      card := 1
      tube := fun _ => topParent
    }
  have hselectedTop :
      ∀ index,
        (selected.family.tube index).carrier ⊆ topParent.carrier := by
    intro index
    rw [selected.tube_eq]
    exact
      pureWZ2_localized_family_subset_top_parent
        hdelta hdeltaOne hA fine hfineRadius
        (selected.embedding index)
  let cover :
      WZ2PaperPurePartitioningCover
        selected.family coarse :=
    {
      covers := by
        intro index
        refine ⟨0, ?_⟩
        rw [mem_wz2PaperOrdinaryFullFiberIndices_iff]
        exact hselectedTop index
      doubled_fibers_disjoint := by
        intro first second hne
        exact (hne (Fin.eq_zero first |>.trans (Fin.eq_zero second).symm)).elim
    }
  have hfullFiber :
      wz2PaperOrdinaryFullFiberIndices
          selected.family coarse 0 =
        Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro index
    rw [mem_wz2PaperOrdinaryFullFiberIndices_iff]
    exact hselectedTop index
  have huniform :
      WZ2PaperPureFullFibersAreCUniform
        selected.family coarse
        (pureWZ2TopScaleConstant
          inputConstant
          (pureWZ2UnitScaleCompleteFiberOverlapBound A)
          globalRetention) := by
    intro first second
    have hfirst : first = 0 := Fin.eq_zero first
    have hsecond : second = 0 := Fin.eq_zero second
    subst first
    subst second
    rw [wz2PaperOrdinaryFullFiberCount, hfullFiber]
    have hone :
        (1 : ENNReal) ≤
          pureWZ2TopScaleConstant
            inputConstant
            (pureWZ2UnitScaleCompleteFiberOverlapBound A)
            globalRetention := by
      exact le_max_left _ _
    simpa using
      mul_le_mul_right' hone
        (selected.family.card : ENNReal)
  have htopVolume :
      ∀ parent : Fin scaleData.coarse.card,
        volume topParent.carrier ≤
          (1280 : ENNReal) *
            volume
              (wz2PaperCenteredDilatedCarrier A
                (scaleData.coarse.tube parent)) := by
    intro parent
    let scaledTopParent : Kakeya.DeltaTube (8 * A * scale.1) :=
      {
        base := fine.center
        direction := EuclideanSpace.single (0 : Fin 3) 1
        direction_unit := by simp
      }
    have hratio :=
      pureWZ2_reanchored_parent_volume_ratio
        hA (show 0 < scale.1 by
          have := scale.property.1
          linarith)
        scale.property.2 scaledTopParent
        (scaleData.coarse.tube parent)
    have hvolume :
        volume topParent.carrier =
          volume scaledTopParent.carrier := by
      let canonicalTop : Kakeya.DeltaTube (8 * A) :=
        {
          base := 0
          direction := EuclideanSpace.single (0 : Fin 3) 1
          direction_unit := by simp
        }
      let canonicalScaled : Kakeya.DeltaTube (8 * A * scale.1) :=
        {
          base := 0
          direction := EuclideanSpace.single (0 : Fin 3) 1
          direction_unit := by simp
        }
      calc
        volume topParent.carrier =
            Kakeya.deltaTubeVolume (8 * A) :=
          Kakeya.Streamlined.tube_volume_eq
            topParent canonicalTop
        _ = Kakeya.deltaTubeVolume (8 * A * scale.1) := by
          rw [hscale]
          ring_nf
        _ = volume scaledTopParent.carrier :=
          (Kakeya.Streamlined.tube_volume_eq
            scaledTopParent canonicalScaled).symm
    rwa [hvolume]
  have haggregate :=
    pureWZ2_unit_scale_aggregate_frostman
      hdelta hA
      (selected.embedding.trans fine.sourceIndex)
      (fun index => fine.axialShift (selected.embedding index))
      (by
        intro index
        rw [selected.tube_eq]
        exact fine.direction_eq (selected.embedding index))
      (by
        intro index
        rw [selected.tube_eq]
        exact fine.source_base_eq (selected.embedding index))
      (fun index =>
        fine.axialShift_bound (selected.embedding index))
      scaleData hscale globalRetention
      global_cardinality_ratio topParent htopVolume
  have htopPos : 0 < 8 * A := by positivity
  let normalization :=
    WZ2PaperAssouadUnitRescalingData.ofTube topParent htopPos
  let identitySub :
      Kakeya.Streamlined.TubeSubfamily selected.family :=
    {
      family := selected.family
      embedding := (Equiv.refl _).toEmbedding
      tube_eq := fun _ => rfl
    }
  have hraw :=
    gwz_frostman_to_john_rescaled_convex_wolff
      hdelta htopPos (show (1 : ℝ) ≤ 1 by norm_num)
      (0 : Fin coarse.card)
      identitySub
      (by
        intro index
        have hdilated :
            wz2PaperCenteredDilatedCarrier 1 topParent =
              topParent.carrier := by
          simp [wz2PaperCenteredDilatedCarrier,
            AffineMap.homothety]
        rw [hdilated]
        exact hselectedTop index)
      normalization
      (pureWZ2UnitScaleAggregateFrostmanConstant
        inputConstant
        (pureWZ2UnitScaleCompleteFiberOverlapBound A)
        globalRetention)
      (by
        intro convexSet hconvex hsubset
        have hdilated :
            wz2PaperCenteredDilatedCarrier 1 topParent =
              topParent.carrier := by
          simp [wz2PaperCenteredDilatedCarrier,
            AffineMap.homothety]
        rw [hdilated] at hsubset ⊢
        exact haggregate convexSet hconvex hsubset)
  let allSource :
      Fin identitySub.family.card ≃
        {sourceIndex : Fin selected.family.card //
          sourceIndex ∈
            wz2PaperOrdinaryFullFiberIndices
              selected.family coarse 0} :=
    {
      toFun := fun index =>
        ⟨index, by rw [hfullFiber]; simp⟩
      invFun := fun sourceIndex => sourceIndex.1
      left_inv := fun _ => rfl
      right_inv := fun _ => by ext; rfl
    }
  let fullFiberEquiv :
      Fin identitySub.family.card ≃
        Fin
          (wz2PaperOrdinaryFullFiberIndices
            selected.family coarse 0).card :=
    allSource.trans
      (wz2PaperOrdinaryFullFiberIndexEquiv
        (fine := selected.family) (coarse := coarse) 0).symm
  have hbody :
      ∀ index : Fin identitySub.family.card,
        ({
          card := identitySub.family.card
          body := fun index : Fin identitySub.family.card =>
            ⟨normalization.map ''
              (identitySub.family.tube index).carrier⟩
        } : Kakeya.Streamlined.BodyFamily).body index =
          (wz2PaperPureUnitRescaledFullFiberBodyFamily
            (fine := selected.family) (coarse := coarse)
            0 normalization).body (fullFiberEquiv index) := by
    intro index
    simp only [identitySub,
      wz2PaperPureUnitRescaledFullFiberBodyFamily]
    have hambient :
        ((wz2PaperOrdinaryFullFiberIndexEquiv
          (fine := selected.family) (coarse := coarse) 0)
          (fullFiberEquiv index)).1 = index := by
      exact congrArg Subtype.val
        ((wz2PaperOrdinaryFullFiberIndexEquiv
          (fine := selected.family) (coarse := coarse) 0)
          |>.apply_symm_apply (allSource index))
    rw [hambient]
  have hcanonical :
      WZ2PaperBodyConvexWolffBound
        (wz2PaperPureUnitRescaledFullFiberBodyFamily
          (fine := selected.family) (coarse := coarse)
          0 normalization)
        (27 *
          pureWZ2UnitScaleAggregateFrostmanConstant
            inputConstant
            (pureWZ2UnitScaleCompleteFiberOverlapBound A)
            globalRetention) :=
    cwb_transfer_reindex fullFiberEquiv hbody hraw
  refine
    ⟨{
      delta_pos := hdelta
      rho_pos := htopPos
      coarse := coarse
      cover := cover
      full_fiber_uniform := huniform
      rescaledFiber := ?_
    }⟩
  intro parent
  have hparent : parent = 0 := Fin.eq_zero parent
  subst parent
  exact
    ⟨{
      normalization := normalization
      convex_wolff := by
        intro convexSet hconvex
        exact (hcanonical convexSet hconvex).trans <| by
          gcongr
          exact le_max_right _ _
    }⟩

end Kakeya.Assouad

end
