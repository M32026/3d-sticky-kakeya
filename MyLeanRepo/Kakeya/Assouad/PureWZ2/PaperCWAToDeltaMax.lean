import MyLeanRepo.Kakeya.Assouad.PureWZ2.PaperCarrierJohnEnvelope
import MyLeanRepo.Kakeya.Assouad.PureWZ2.BoundedDeltaMax
import MyLeanRepo.Kakeya.Assouad.PropStickyDefinition2_12NestedJohnCWATransport
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.TubeDensityTestNet.GeometricLemmas

/-!
# Cropped paper CWA controls ordinary maximal convex density

For a bounded line-class family, enlarge a maximizing ordinary convex set by
its outer John ellipsoid.  Every ordinary tube contained in the set has its
cropped paper carrier inside the factor-70 John enlargement, whose volume is
at most `27 * 70^3` times the original set.
-/

noncomputable section

open MeasureTheory Set
open Kakeya.Streamlined

namespace Kakeya.Assouad

lemma paper_cwa_to_ordinary_deltaMax
    {delta : ℝ} (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    (F : Kakeya.Streamlined.TubeFamily delta)
    (hline : WZ1PaperIsLineClass F)
    (hbase : HasBoundedBase F 4)
    (C : ENNReal)
    (hCWA : WZ2PaperConvexWolffBound F C) :
    F.toBodyFamily.deltaMax ≤
      9261000 * C * F.enncard * Kakeya.deltaTubeVolume delta := by
  classical
  rcases Kakeya.Streamlined.deltaMax_attained F.toBodyFamily with
    ⟨K, hKconvex, hKmax⟩
  rw [← hKmax]
  have hsupport : ∀ i, (F.tube i).carrier ⊆
      Metric.closedBall (0 : Point3) 10 := by
    intro i
    exact (tube_carrier_subset_closedBall_six hdelta.le hdelta_one
      (F.tube i) (hbase i)).trans
        (Metric.closedBall_subset_closedBall (by norm_num : (6 : ℝ) ≤ 10))
  rcases Kakeya.Streamlined.RandomTranslation.density_reduction_to_ball
      F hsupport K hKconvex with
    ⟨H, hHconvex, hHcompact, _hHball, _hHK, hcontainedIff,
      hmassEqKH, hvolumeHK⟩
  have hdensityKH : F.toBodyFamily.density K ≤
      F.toBodyFamily.density H := by
    dsimp only [BodyFamily.density]
    rw [hmassEqKH]
    exact ENNReal.div_le_div le_rfl hvolumeHK
  by_cases hindices : F.toBodyFamily.containedIndices K = ∅
  · simp [BodyFamily.density, BodyFamily.containedMass, hindices]
  · have hindicesNonempty :
        (F.toBodyFamily.containedIndices K).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hindices
    rcases hindicesNonempty with ⟨reference, hreference⟩
    have hrefSubset : (F.tube reference).carrier ⊆ K :=
      BodyFamily.mem_containedIndices_iff.mp hreference
    have hrefSubsetH : (F.tube reference).carrier ⊆ H :=
      (hcontainedIff reference).mp hrefSubset
    have hHinterior : (interior H).Nonempty := by
      have htubeInterior :=
        Kakeya.Streamlined.RandomTranslation.deltaTube_nonempty_interior
          hdelta (F.tube reference)
      have hinteriorSubset : interior (F.tube reference).carrier ⊆
          interior H := interior_mono hrefSubsetH
      exact htubeInterior.mono hinteriorSubset
    let hbody : JohnEllipsoid.IsConvexBody H :=
      ⟨hHconvex, hHcompact, hHinterior⟩
    let center : Point3 := hbody.outerJohnEllipsoidCenter
    let linear : Point3 ≃ₗ[ℝ] Point3 := hbody.outerJohnEllipsoidMap
    let E : Set Point3 := JohnEllipsoid.ellipsoid center linear
    have hH_E : H ⊆ E := hbody.outerJohnEllipsoid_spec.1
    let enlarged : Set Point3 := AffineMap.homothety center (70 : ℝ) '' E
    have henlargedConvex : Convex ℝ enlarged :=
      (JohnEllipsoid.ellipsoid_convex center linear).affine_image _
    have hpaperIndices : F.toBodyFamily.containedIndices H ⊆
        (wz1PaperBodyFamily F).containedIndices enlarged := by
      intro i hi
      have hiSubset : (F.tube i).carrier ⊆ E :=
        (BodyFamily.mem_containedIndices_iff.mp hi).trans hH_E
      exact BodyFamily.mem_containedIndices_iff.mpr
        (wz2PaperTubeCarrier_subset_ellipsoid_homothety_seventy
          hdelta hdelta_one (F.tube i) (hline i) (hbase i)
          center linear hiSubset)
    have hcount : F.toBodyFamily.containedCount H ≤
        (wz1PaperBodyFamily F).containedCount enlarged := by
      change ((F.toBodyFamily.containedIndices H).card : ENNReal) ≤
        (((wz1PaperBodyFamily F).containedIndices enlarged).card : ENNReal)
      exact_mod_cast Finset.card_le_card hpaperIndices
    have hpaperCount : (wz1PaperBodyFamily F).containedCount enlarged ≤
        C * volume enlarged * F.enncard :=
      hCWA enlarged henlargedConvex
    have hEvolume : volume E ≤ 27 * volume H := by
      exact wz2Paper_outerJohn_volume_le_twentySeven hbody
    have henlargedVolume : volume enlarged ≤ 9261000 * volume H := by
      calc
        volume enlarged = ENNReal.ofReal (|(70 : ℝ)| ^ 3) * volume E := by
          exact JohnEllipsoid.volume_homothety center 70 E
        _ = 343000 * volume E := by norm_num
        _ ≤ 343000 * (27 * volume H) := by gcongr
        _ = 9261000 * volume H := by ring
    have hcountBound : F.toBodyFamily.containedCount H ≤
        9261000 * C * F.enncard * volume H := by
      calc
        F.toBodyFamily.containedCount H
            ≤ (wz1PaperBodyFamily F).containedCount enlarged := hcount
        _ ≤ C * volume enlarged * F.enncard := hpaperCount
        _ ≤ C * (9261000 * volume H) * F.enncard := by gcongr
        _ = 9261000 * C * F.enncard * volume H := by ring
    have hmassEq : F.toBodyFamily.containedMass H =
        F.toBodyFamily.containedCount H * Kakeya.deltaTubeVolume delta := by
      dsimp only [BodyFamily.containedMass, BodyFamily.containedCount]
      calc
        (∑ i ∈ F.toBodyFamily.containedIndices H,
            (F.toBodyFamily.body i).volume) =
            ∑ _i ∈ F.toBodyFamily.containedIndices H,
              Kakeya.deltaTubeVolume delta := by
                apply Finset.sum_congr rfl
                intro i _
                exact tube_volume_scaling.1 delta (F.tube i)
        _ = ((F.toBodyFamily.containedIndices H).card : ENNReal) *
              Kakeya.deltaTubeVolume delta := by simp [Finset.sum_const]
    have hvolumePos : 0 < volume H := by
      have hvolTube : 0 < (F.tube reference).volume := by
        rw [tube_volume_scaling.1 delta (F.tube reference)]
        exact (tube_volume_scaling.2.1 delta hdelta hdelta_one).1
      exact hvolTube.trans_le (measure_mono hrefSubsetH)
    have hvolumeTop : volume H ≠ ⊤ := hHcompact.measure_ne_top
    have hHbound : F.toBodyFamily.density H ≤
        9261000 * C * F.enncard * Kakeya.deltaTubeVolume delta := by
      rw [BodyFamily.density, hmassEq]
      rw [ENNReal.div_le_iff hvolumePos.ne' hvolumeTop]
      simpa [mul_assoc, mul_comm, mul_left_comm] using
        (mul_le_mul_right' hcountBound (Kakeya.deltaTubeVolume delta))
    exact hdensityKH.trans hHbound

end Kakeya.Assouad

end
