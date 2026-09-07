import MyLeanRepo.Kakeya.Assouad.TwistedProjectionScale.NonessentialTubeAxisAlignment
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12
import MyLeanRepo.Kakeya.Assouad.TubeVolumeScaling

/-!
# Analytic conflict degree from maximal convex density

Nonessential overlap places a tube inside the centered factor-3000 dilation
of the reference tube.  That convex container has exactly `3000^3` times the
ordinary tube volume, so `deltaMax ≤ D` gives a conflict degree at most
`27,000,000,000 * D`.
-/

noncomputable section

open MeasureTheory Set Finset
open Kakeya.Streamlined

namespace Kakeya.Assouad

attribute [local instance] Classical.propDecidable

private lemma nonessential_carrier_subset_centered_dilate
    {delta : ℝ} (hdelta : 0 < delta) (hdelta_small : delta ≤ 1 / 1000)
    (source reference : Kakeya.DeltaTube delta)
    (hconflict : ¬source.EssentiallyDistinct reference) :
    source.carrier ⊆ wz2PaperCenteredDilatedCarrier 3000 reference := by
  intro point hpoint
  rcases nonessential_tube_axis_alignment delta hdelta hdelta_small
      source reference hconflict with
    ⟨sign, anchor, horientation, hdirection, shift, hshift, hbase⟩
  have hsegment : IsCompact
      (Kakeya.unitSegment source.base source.direction) := by
    apply IsCompact.image isCompact_Icc
    fun_prop
  change point ∈ Metric.cthickening delta
    (Kakeya.unitSegment source.base source.direction) at hpoint
  rw [hsegment.cthickening_eq_biUnion_closedBall hdelta.le] at hpoint
  rcases Set.mem_iUnion₂.mp hpoint with ⟨axisPoint, haxis, hpointAxis⟩
  rcases haxis with ⟨parameter, hparameter, rfl⟩
  let signedDirection : Point3 := sign • reference.direction
  let targetPoint : Point3 :=
    anchor + (shift + parameter) • signedDirection
  have haxisTarget :
      dist (source.base + parameter • source.direction) targetPoint ≤
        2002 * delta := by
    rw [dist_eq_norm]
    have hid :
        source.base + parameter • source.direction - targetPoint =
          (source.base - (anchor + shift • signedDirection)) +
            parameter • (source.direction - signedDirection) := by
      dsimp only [targetPoint]
      rw [add_smul]
      module
    rw [hid]
    calc
      ‖(source.base - (anchor + shift • signedDirection)) +
          parameter • (source.direction - signedDirection)‖
          ≤ ‖source.base - (anchor + shift • signedDirection)‖ +
              ‖parameter • (source.direction - signedDirection)‖ :=
                norm_add_le _ _
      _ = ‖source.base - (anchor + shift • signedDirection)‖ +
              |parameter| * ‖source.direction - signedDirection‖ := by
                rw [norm_smul, Real.norm_eq_abs]
      _ ≤ 1002 * delta + 1 * (1000 * delta) := by
            have hparameterAbs : |parameter| ≤ 1 :=
              abs_le.mpr ⟨by linarith [hparameter.1], hparameter.2⟩
            have hbase' :
                ‖source.base - (anchor + shift • signedDirection)‖ ≤
                  1002 * delta := by
              simpa [signedDirection] using hbase
            have hdir' :
                ‖source.direction - signedDirection‖ ≤ 1000 * delta := by
              simpa [signedDirection] using hdirection
            exact add_le_add hbase'
              (mul_le_mul hparameterAbs hdir' (norm_nonneg _) (by norm_num))
      _ = 2002 * delta := by ring
  have hpointTarget : dist point targetPoint ≤ 2003 * delta := by
    have hpointAxis' :
        dist point (source.base + parameter • source.direction) ≤ delta := by
      simpa [Metric.mem_closedBall] using hpointAxis
    exact (dist_triangle _ _ _).trans (by linarith)
  rcases horientation with horientation | horientation
  · rcases horientation with ⟨hsign, hanchor⟩
    have htarget : targetPoint =
        reference.base + (shift + parameter) • reference.direction := by
      simp [targetPoint, signedDirection, hsign, hanchor]
    let contractedParameter : ℝ :=
      1 / 2 + ((shift + parameter) - 1 / 2) / 3000
    let contractedAxis : Point3 :=
      reference.base + contractedParameter • reference.direction
    let contractedPoint : Point3 :=
      wz2PaperTubeMidpoint reference +
        (1 / 3000 : ℝ) •
          (point - wz2PaperTubeMidpoint reference)
    have hcontractedParameter : contractedParameter ∈ Set.Icc (0 : ℝ) 1 := by
      dsimp only [contractedParameter]
      constructor <;> linarith [hshift.1, hshift.2, hparameter.1, hparameter.2]
    have hcontractedAxis : contractedAxis ∈
        Kakeya.unitSegment reference.base reference.direction :=
      ⟨contractedParameter, hcontractedParameter, rfl⟩
    have hcontractedDist : dist contractedPoint contractedAxis ≤ delta := by
      have haxisEq : contractedAxis =
          wz2PaperTubeMidpoint reference +
            (1 / 3000 : ℝ) •
              (targetPoint - wz2PaperTubeMidpoint reference) := by
        rw [htarget]
        dsimp only [contractedAxis, contractedParameter]
        simp [wz2PaperTubeMidpoint]
        module
      rw [haxisEq, dist_eq_norm]
      have hid : contractedPoint -
          (wz2PaperTubeMidpoint reference +
            (1 / 3000 : ℝ) •
              (targetPoint - wz2PaperTubeMidpoint reference)) =
          (1 / 3000 : ℝ) • (point - targetPoint) := by
        dsimp only [contractedPoint]
        module
      rw [hid, norm_smul, Real.norm_eq_abs]
      norm_num
      simpa [dist_eq_norm] using
        (mul_le_mul_of_nonneg_left hpointTarget (by norm_num :
          (0 : ℝ) ≤ 1 / 3000)) |>.trans (by linarith)
    have hcontractedCarrier : contractedPoint ∈ reference.carrier :=
      Metric.mem_cthickening_of_dist_le contractedPoint contractedAxis
        delta _ hcontractedAxis hcontractedDist
    refine ⟨contractedPoint, hcontractedCarrier, ?_⟩
    simp only [AffineMap.homothety_apply]
    ext coordinate
    simp [contractedPoint]
  · rcases horientation with ⟨hsign, hanchor⟩
    have htarget : targetPoint =
        reference.base + (1 - shift - parameter) • reference.direction := by
      simp [targetPoint, signedDirection, hsign, hanchor, sub_smul]
      module
    let contractedParameter : ℝ :=
      1 / 2 + ((1 - shift - parameter) - 1 / 2) / 3000
    let contractedAxis : Point3 :=
      reference.base + contractedParameter • reference.direction
    let contractedPoint : Point3 :=
      wz2PaperTubeMidpoint reference +
        (1 / 3000 : ℝ) •
          (point - wz2PaperTubeMidpoint reference)
    have hcontractedParameter : contractedParameter ∈ Set.Icc (0 : ℝ) 1 := by
      dsimp only [contractedParameter]
      constructor <;> linarith [hshift.1, hshift.2, hparameter.1, hparameter.2]
    have hcontractedAxis : contractedAxis ∈
        Kakeya.unitSegment reference.base reference.direction :=
      ⟨contractedParameter, hcontractedParameter, rfl⟩
    have hcontractedDist : dist contractedPoint contractedAxis ≤ delta := by
      have haxisEq : contractedAxis =
          wz2PaperTubeMidpoint reference +
            (1 / 3000 : ℝ) •
              (targetPoint - wz2PaperTubeMidpoint reference) := by
        rw [htarget]
        dsimp only [contractedAxis, contractedParameter]
        simp [wz2PaperTubeMidpoint]
        module
      rw [haxisEq, dist_eq_norm]
      have hid : contractedPoint -
          (wz2PaperTubeMidpoint reference +
            (1 / 3000 : ℝ) •
              (targetPoint - wz2PaperTubeMidpoint reference)) =
          (1 / 3000 : ℝ) • (point - targetPoint) := by
        dsimp only [contractedPoint]
        module
      rw [hid, norm_smul, Real.norm_eq_abs]
      norm_num
      simpa [dist_eq_norm] using
        (mul_le_mul_of_nonneg_left hpointTarget (by norm_num :
          (0 : ℝ) ≤ 1 / 3000)) |>.trans (by linarith)
    have hcontractedCarrier : contractedPoint ∈ reference.carrier :=
      Metric.mem_cthickening_of_dist_le contractedPoint contractedAxis
        delta _ hcontractedAxis hcontractedDist
    refine ⟨contractedPoint, hcontractedCarrier, ?_⟩
    simp only [AffineMap.homothety_apply]
    ext coordinate
    simp [contractedPoint]

lemma tubeFamily_nonessential_degree_le_deltaMax
    {delta : ℝ} (hdelta : 0 < delta) (hdelta_small : delta ≤ 1 / 1000)
    (F : Kakeya.Streamlined.TubeFamily delta)
    (D : ENNReal) (hD : F.toBodyFamily.deltaMax ≤ D) :
    ∀ i,
      ((Finset.univ.filter fun j =>
        ¬(F.tube i).EssentiallyDistinct (F.tube j)).card : ENNReal) ≤
        27000000000 * D := by
  intro reference
  let container :=
    wz2PaperCenteredDilatedCarrier 3000 (F.tube reference)
  have hcontainerConvex : Convex ℝ container := by
    exact (wz2_paper_ordinary_tube_carrier_convex
      (F.tube reference)).affine_image _
  have hneighbors :
      (Finset.univ.filter fun j =>
        ¬(F.tube reference).EssentiallyDistinct (F.tube j)) ⊆
      F.toBodyFamily.containedIndices container := by
    intro j hj
    have hconflict := (Finset.mem_filter.mp hj).2
    have hreverse : ¬(F.tube j).EssentiallyDistinct
        (F.tube reference) := by
      simpa [Kakeya.DeltaTube.EssentiallyDistinct, Set.inter_comm, max_comm]
        using hconflict
    exact BodyFamily.mem_containedIndices_iff.mpr
      (nonessential_carrier_subset_centered_dilate
        hdelta hdelta_small (F.tube j) (F.tube reference) hreverse)
  have hcount :
      (((Finset.univ.filter fun j =>
        ¬(F.tube reference).EssentiallyDistinct (F.tube j)).card : ℕ) :
          ENNReal) ≤ F.toBodyFamily.containedCount container := by
    change (((Finset.univ.filter fun j =>
      ¬(F.tube reference).EssentiallyDistinct (F.tube j)).card : ℕ) :
        ENNReal) ≤ ((F.toBodyFamily.containedIndices container).card : ENNReal)
    exact_mod_cast Finset.card_le_card hneighbors
  have hdensity : F.toBodyFamily.density container ≤ D := by
    have hbdd : BddAbove
        {d : ENNReal | ∃ K : Set Point3, Convex ℝ K ∧
          d = F.toBodyFamily.density K} := ⟨⊤, fun _ _ => le_top⟩
    exact (le_csSup hbdd ⟨container, hcontainerConvex, rfl⟩).trans hD
  have hdelta_one : delta ≤ 1 := hdelta_small.trans (by norm_num)
  have hVpos : 0 < Kakeya.deltaTubeVolume delta :=
    (tube_volume_scaling.2.1 delta hdelta hdelta_one).1
  have hVtop : Kakeya.deltaTubeVolume delta ≠ ⊤ :=
    (tube_volume_scaling.2.1 delta hdelta hdelta_one).2
  have hvolume : volume container =
      27000000000 * Kakeya.deltaTubeVolume delta := by
    rw [wz2_paper_centeredDilatedCarrier_volume]
    norm_num
    change 27000000000 * (F.tube reference).volume =
      27000000000 * Kakeya.deltaTubeVolume delta
    rw [tube_volume_scaling.1 delta (F.tube reference)]
  have hvolumePos : 0 < volume container := by rw [hvolume]; positivity
  have hvolumeTop : volume container ≠ ⊤ := by
    rw [hvolume]
    exact ENNReal.mul_ne_top (by norm_num) hVtop
  have hmass : F.toBodyFamily.containedMass container ≤
      D * volume container := by
    rw [BodyFamily.density] at hdensity
    exact (ENNReal.div_le_iff hvolumePos.ne' hvolumeTop).mp hdensity
  have hmassEq : F.toBodyFamily.containedMass container =
      F.toBodyFamily.containedCount container *
        Kakeya.deltaTubeVolume delta := by
    dsimp only [BodyFamily.containedMass, BodyFamily.containedCount]
    calc
      (∑ i ∈ F.toBodyFamily.containedIndices container,
          (F.toBodyFamily.body i).volume) =
          ∑ _i ∈ F.toBodyFamily.containedIndices container,
            Kakeya.deltaTubeVolume delta := by
              apply Finset.sum_congr rfl
              intro i _
              exact tube_volume_scaling.1 delta (F.tube i)
      _ = ((F.toBodyFamily.containedIndices container).card : ENNReal) *
          Kakeya.deltaTubeVolume delta := by simp [Finset.sum_const]
  have hwithV :
      (((Finset.univ.filter fun j =>
        ¬(F.tube reference).EssentiallyDistinct (F.tube j)).card : ℕ) :
          ENNReal) * Kakeya.deltaTubeVolume delta ≤
        (27000000000 * D) * Kakeya.deltaTubeVolume delta := by
    calc
      _ ≤ F.toBodyFamily.containedCount container *
          Kakeya.deltaTubeVolume delta := by gcongr
      _ = F.toBodyFamily.containedMass container := hmassEq.symm
      _ ≤ D * volume container := hmass
      _ = (27000000000 * D) * Kakeya.deltaTubeVolume delta := by
            rw [hvolume]
            ring
  have hwithV' : Kakeya.deltaTubeVolume delta *
      (((Finset.univ.filter fun j =>
        ¬(F.tube reference).EssentiallyDistinct (F.tube j)).card : ℕ) :
          ENNReal) ≤
      Kakeya.deltaTubeVolume delta * (27000000000 * D) := by
    simpa [mul_comm] using hwithV
  exact (ENNReal.mul_le_mul_iff_right hVpos.ne' hVtop).mp hwithV'

end Kakeya.Assouad

end
