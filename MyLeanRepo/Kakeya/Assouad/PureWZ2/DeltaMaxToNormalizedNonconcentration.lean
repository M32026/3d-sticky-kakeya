import MyLeanRepo.Kakeya.Assouad.PureWZ2.WideParameterPrism
import MyLeanRepo.Kakeya.Assouad.TubeVolumeLowerBound
import MyLeanRepo.Kakeya.Streamlined.GeometricLemmas.CapsuleBounds

/-!
# Normalize absolute convex density using a cardinality lower bound
-/

noncomputable section

open MeasureTheory Set Finset
open Kakeya.Streamlined

namespace Kakeya.Assouad

private lemma containedCount_mul_volume_le_deltaMax
    {delta : ℝ} (F : Kakeya.Streamlined.TubeFamily delta)
    (K : Set Point3) (hconvex : Convex ℝ K)
    (hvolume_pos : 0 < volume K) (hvolume_top : volume K ≠ ⊤) :
    F.toBodyFamily.containedCount K * Kakeya.deltaTubeVolume delta ≤
      F.toBodyFamily.deltaMax * volume K := by
  have hmass : F.toBodyFamily.containedMass K =
      F.toBodyFamily.containedCount K * Kakeya.deltaTubeVolume delta := by
    dsimp only [BodyFamily.containedMass, BodyFamily.containedCount]
    calc
      (∑ i ∈ F.toBodyFamily.containedIndices K,
          (F.toBodyFamily.body i).volume) =
          ∑ _i ∈ F.toBodyFamily.containedIndices K,
            Kakeya.deltaTubeVolume delta := by
              apply Finset.sum_congr rfl
              intro i _
              exact tube_volume_scaling.1 delta (F.tube i)
      _ = ((F.toBodyFamily.containedIndices K).card : ENNReal) *
          Kakeya.deltaTubeVolume delta := by simp [Finset.sum_const]
  have hdensity : F.toBodyFamily.density K ≤
      F.toBodyFamily.deltaMax := by
    rw [BodyFamily.deltaMax]
    exact le_csSup (⟨⊤, fun _ _ => le_top⟩) ⟨K, hconvex, rfl⟩
  rw [BodyFamily.density, hmass] at hdensity
  exact (ENNReal.div_le_iff hvolume_pos.ne' hvolume_top).mp hdensity

lemma deltaMax_to_normalized_tubeWolff
    {delta : ℝ} (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    (F : Kakeya.Streamlined.TubeFamily delta)
    (densityBound cardinalityFloor normalizedConstant : ENNReal)
    (hdeltaMax : F.toBodyFamily.deltaMax ≤ densityBound)
    (hcard : cardinalityFloor ≤ F.enncard)
    (habsorb :
      24 * Kakeya.deltaTubeVolume 1 * densityBound *
          (Kakeya.realRpowENN delta 2)⁻¹ ≤
        normalizedConstant * cardinalityFloor) :
    TubeWolffBound F normalizedConstant := by
  intro r hdelta_r hr_one tube
  have hr_pos : 0 < r := hdelta.trans_le hdelta_r
  have hconvex : Convex ℝ tube.carrier :=
    wz2_paper_ordinary_tube_carrier_convex tube
  have htubeVolumePos : 0 < volume tube.carrier := by
    change 0 < tube.volume
    rw [tube_volume_scaling.1 r tube]
    exact (tube_volume_scaling.2.1 r hr_pos hr_one).1
  have htubeVolumeTop : volume tube.carrier ≠ ⊤ := by
    change tube.volume ≠ ⊤
    rw [tube_volume_scaling.1 r tube]
    exact (tube_volume_scaling.2.1 r hr_pos hr_one).2
  have hcountV := containedCount_mul_volume_le_deltaMax
    F tube.carrier hconvex htubeVolumePos htubeVolumeTop
  have htubeVolume : volume tube.carrier ≤
      24 * Kakeya.realRpowENN r 2 * Kakeya.deltaTubeVolume 1 :=
    tube_volume_scaling.2.2 r hr_pos hr_one tube
  have hVlower : Kakeya.realRpowENN delta 2 ≤
      Kakeya.deltaTubeVolume delta := by
    simpa [Kakeya.realRpowENN, Real.rpow_two] using
      canonical_volume_lower hdelta
  have hcountPower : F.toBodyFamily.containedCount tube.carrier *
      Kakeya.realRpowENN delta 2 ≤
      densityBound * (24 * Kakeya.realRpowENN r 2 *
        Kakeya.deltaTubeVolume 1) := by
    calc
      F.toBodyFamily.containedCount tube.carrier *
          Kakeya.realRpowENN delta 2
          ≤ F.toBodyFamily.containedCount tube.carrier *
              Kakeya.deltaTubeVolume delta := by gcongr
      _ ≤ F.toBodyFamily.deltaMax * volume tube.carrier := hcountV
      _ ≤ densityBound * volume tube.carrier := by gcongr
      _ ≤ densityBound *
          (24 * Kakeya.realRpowENN r 2 * Kakeya.deltaTubeVolume 1) := by gcongr
  let scale := Kakeya.realRpowENN delta 2
  have hscaleZero : scale ≠ 0 := by
    exact (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hdelta _)).ne'
  have hscaleTop : scale ≠ ⊤ := ENNReal.ofReal_ne_top
  have hcountAbsolute : F.toBodyFamily.containedCount tube.carrier ≤
      (24 * Kakeya.deltaTubeVolume 1 * densityBound * scale⁻¹) *
        Kakeya.realRpowENN r 2 := by
    calc
      F.toBodyFamily.containedCount tube.carrier =
          (F.toBodyFamily.containedCount tube.carrier * scale) *
            scale⁻¹ := by
              rw [mul_assoc, ENNReal.mul_inv_cancel hscaleZero hscaleTop, mul_one]
      _ ≤ (densityBound *
          (24 * Kakeya.realRpowENN r 2 * Kakeya.deltaTubeVolume 1)) *
            scale⁻¹ := by gcongr
      _ = (24 * Kakeya.deltaTubeVolume 1 * densityBound * scale⁻¹) *
          Kakeya.realRpowENN r 2 := by ring
  calc
    F.toBodyFamily.containedCount tube.carrier
        ≤ (24 * Kakeya.deltaTubeVolume 1 * densityBound * scale⁻¹) *
          Kakeya.realRpowENN r 2 := hcountAbsolute
    _ ≤ (normalizedConstant * cardinalityFloor) *
          Kakeya.realRpowENN r 2 := by gcongr
    _ ≤ (normalizedConstant * F.enncard) *
          Kakeya.realRpowENN r 2 := by gcongr
    _ = normalizedConstant * Kakeya.realRpowENN r 2 * F.enncard := by ring

lemma deltaMax_to_normalized_parameterFrostman
    {delta : ℝ} (hdelta : 0 < delta)
    (F : Kakeya.Streamlined.TubeFamily delta)
    (hbase : HasBoundedBase F 4) (hvertical : IsInVerticalChart F)
    (densityBound cardinalityFloor normalizedConstant : ENNReal)
    (hdeltaMax : F.toBodyFamily.deltaMax ≤ densityBound)
    (hcard : cardinalityFloor ≤ F.enncard)
    (habsorb : 4800 * densityBound *
      (Kakeya.deltaTubeVolume delta)⁻¹ ≤
        normalizedConstant * cardinalityFloor) :
    TubeParameterFrostmanBound F normalizedConstant := by
  intro r hdelta_r hr_one reference
  have hr_pos : 0 < r := hdelta.trans_le hdelta_r
  let indices : Finset (Fin F.card) :=
    Finset.univ.filter fun index =>
      |(tubeParams index).a - (tubeParams reference).a| ≤ r ∧
      |(tubeParams index).b - (tubeParams reference).b| ≤ r ∧
      |(tubeParams index).c - (tubeParams reference).c| ≤ r ∧
      |(tubeParams index).d - (tubeParams reference).d| ≤ r
  let prism := wideTubeParameterPrism (tubeParams reference) (10 * r)
  have hsubset : indices ⊆ F.toBodyFamily.containedIndices prism := by
    intro i hi
    exact BodyFamily.mem_containedIndices_iff.mpr
      (parameter_cluster_carrier_subset_widePrism
        hdelta hdelta_r hr_one hbase hvertical reference i
          (Finset.mem_filter.mp hi).2)
  have hcount : (indices.card : ENNReal) ≤
      F.toBodyFamily.containedCount prism := by
    change (indices.card : ENNReal) ≤
      ((F.toBodyFamily.containedIndices prism).card : ENNReal)
    exact_mod_cast Finset.card_le_card hsubset
  have hgeo := wideTubeParameterPrism_geometry
    (tubeParams reference) (10 * r) (by positivity)
  have hvolume : volume prism ≤ ENNReal.ofReal (4800 * r ^ 2) := by
    calc
      volume prism ≤ ENNReal.ofReal (48 * (10 * r) ^ 2) := hgeo.2
      _ = ENNReal.ofReal (4800 * r ^ 2) := by congr 1 <;> ring
  have hvolumePos : 0 < volume prism := by
    have hsubReference : (F.tube reference).carrier ⊆ prism :=
      parameter_cluster_carrier_subset_widePrism
        hdelta hdelta_r hr_one hbase hvertical reference reference
        ⟨by simp [abs_zero, hr_pos.le],
          by simp [abs_zero, hr_pos.le],
          by simp [abs_zero, hr_pos.le],
          by simp [abs_zero, hr_pos.le]⟩
    have hTubePos : 0 < volume (F.tube reference).carrier := by
      change 0 < (F.tube reference).volume
      rw [tube_volume_scaling.1 delta (F.tube reference)]
      exact (tube_volume_scaling.2.1 delta hdelta
        (hdelta_r.trans hr_one)).1
    exact hTubePos.trans_le (measure_mono hsubReference)
  have hvolumeTop : volume prism ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hvolume
  have hcountV := containedCount_mul_volume_le_deltaMax
    F prism hgeo.1 hvolumePos hvolumeTop
  have hrpow : ENNReal.ofReal (4800 * r ^ 2) =
      4800 * Kakeya.realRpowENN r 2 := by
    simp [Kakeya.realRpowENN, Real.rpow_two,
      ENNReal.ofReal_mul (show (0 : ℝ) ≤ 4800 by norm_num)]
  have hVpos :=
    (tube_volume_scaling.2.1 delta hdelta (hdelta_r.trans hr_one)).1
  have hVtop :=
    (tube_volume_scaling.2.1 delta hdelta (hdelta_r.trans hr_one)).2
  have hcountAbsolute : F.toBodyFamily.containedCount prism ≤
      (4800 * densityBound * (Kakeya.deltaTubeVolume delta)⁻¹) *
        Kakeya.realRpowENN r 2 := by
    calc
      F.toBodyFamily.containedCount prism =
          (F.toBodyFamily.containedCount prism *
            Kakeya.deltaTubeVolume delta) *
              (Kakeya.deltaTubeVolume delta)⁻¹ := by
                rw [mul_assoc, ENNReal.mul_inv_cancel hVpos.ne' hVtop, mul_one]
      _ ≤ (F.toBodyFamily.deltaMax * volume prism) *
            (Kakeya.deltaTubeVolume delta)⁻¹ := by gcongr
      _ ≤ (densityBound * ENNReal.ofReal (4800 * r ^ 2)) *
            (Kakeya.deltaTubeVolume delta)⁻¹ := by gcongr
      _ = (4800 * densityBound * (Kakeya.deltaTubeVolume delta)⁻¹) *
            Kakeya.realRpowENN r 2 := by rw [hrpow] <;> ring
  change (indices.card : ENNReal) ≤
    normalizedConstant * Kakeya.realRpowENN r 2 * F.enncard
  calc
    (indices.card : ENNReal) ≤ F.toBodyFamily.containedCount prism := hcount
    _ ≤ (4800 * densityBound * (Kakeya.deltaTubeVolume delta)⁻¹) *
          Kakeya.realRpowENN r 2 := hcountAbsolute
    _ ≤ (normalizedConstant * cardinalityFloor) *
          Kakeya.realRpowENN r 2 := by gcongr
    _ ≤ (normalizedConstant * F.enncard) *
          Kakeya.realRpowENN r 2 := by gcongr
    _ = normalizedConstant * Kakeya.realRpowENN r 2 * F.enncard := by ring

end Kakeya.Assouad

end
