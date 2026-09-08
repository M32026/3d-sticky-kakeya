import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.AllScaleBalancedFromDilatedCover
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.FrostmanFromDeltaMax
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.KatzTaoGoodShifts.Extraction
import MyLeanRepo.Kakeya.Streamlined.IndependentDilatedCoverFullFiberMass
import MyLeanRepo.Kakeya.Streamlined.DividingScales.ConvexThickeningGrowth
import MyLeanRepo.Kakeya.Streamlined.GeneralizedFrostman.FromNormalizationSelection.AlgebraFixes
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.FullContainmentFiberFrostman
import MyLeanRepo.Kakeya.Streamlined.FlatPrismFactoring.FromSection5AndPlankEstimates.FactoringComposition
import MyLeanRepo.Kakeya.Streamlined.ProfileUniformRefinement.DilatedTubeBodyGeometry
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.FrostmanInterpolationTheorem
import MyLeanRepo.Kakeya.Streamlined.DividingScales.ReferenceDensity

/-!
# Frostman control for all-scale structures from dilated covers

The all-scale balanced construction preserves a lower-grid assigned anchor
inside every real-scale assigned anchor.  Its mass lower bound then gives
Frostman control of the complete geometric containment fiber at every scale.

Unlike the historical consumer, this module does not hard-code dilation
`2000`.  The actual output dilation of the all-scale package appears in the
container-volume factor.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Streamlined.RandomTranslation

/-- Volume factor contributed by a positive homothetic tube dilation. -/
def dilatedCoverVolumeFactor (A : ℝ) : ENNReal :=
  ENNReal.ofReal (A ^ 3)

/-- Fixed loss for transporting grid assigned-fiber Frostman control through
the nearby-scale enlargement and the final ED parent merge. -/
def allScaleAssignedFrostmanTransportLoss (A : ℝ) (K : ENNReal) : ENNReal :=
  K * dilatedCoverVolumeFactor (dominatingUpperFromDilatedCoverDilation A)

/--
One assigned fiber of an `A`-dilated cover is Frostman once its cardinality
supplies the mass required by ambient `deltaMax`.
-/
theorem assigned_fiber_frostman_of_dilated_cover_cluster_mass
    {delta rho eta A : ℝ}
    (hdelta : 0 < delta)
    (hrho : 0 < rho)
    (hA : 0 < A)
    {fine : TubeFamily delta}
    {coarse : TubeFamily rho}
    (P : DilatedTubeCover A fine coarse)
    (parent : Fin coarse.card)
    {C : ENNReal}
    (hCpos : 0 < C)
    (hCtop : C ≠ ⊤)
    (hdeltaMax : fine.toBodyFamily.deltaMax ≤ C)
    (hcluster :
      C * dilatedCoverVolumeFactor A *
            Kakeya.deltaTubeVolume rho *
          Kakeya.realRpowENN delta eta ≤
        P.toFactoring.fiberCount parent *
          Kakeya.deltaTubeVolume delta) :
    P.assignedFiberFrostmanConstant parent ≤
      Kakeya.realRpowENN delta (-eta) := by
  let fiber := P.assignedFiberSubfamily parent
  let container :=
    dilatedTubeCarrier A (coarse.tube parent)
  let power := Kakeya.realRpowENN delta eta
  let containerVolume := volume container
  let minimumMass := C * containerVolume * power

  have hpower_pos : 0 < power := by
    dsimp only [power, Kakeya.realRpowENN]
    exact ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos hdelta eta)
  have hpower_top : power ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  have hcontainer_volume :
      containerVolume =
        dilatedCoverVolumeFactor A *
          Kakeya.deltaTubeVolume rho := by
    dsimp only [containerVolume, container,
      dilatedCoverVolumeFactor]
    rw [Kakeya.Streamlined.volume_dilatedTubeCarrier
      hA.ne' (coarse.tube parent), abs_of_pos hA]
  have hcontainer_pos : 0 < containerVolume := by
    rw [hcontainer_volume]
    exact ENNReal.mul_pos
      (ENNReal.ofReal_pos.mpr (by positivity)).ne'
      (deltaTubeVolume_pos hrho).ne'
  have hcontainer_top : containerVolume ≠ ⊤ := by
    rw [hcontainer_volume]
    exact ENNReal.mul_ne_top
      ENNReal.ofReal_ne_top deltaTubeVolume_ne_top
  have hminimum_pos : 0 < minimumMass := by
    dsimp only [minimumMass]
    positivity
  have hminimum_top : minimumMass ≠ ⊤ := by
    dsimp only [minimumMass]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top hCtop hcontainer_top)
      hpower_top

  have hfiber_deltaMax :
      fiber.family.toBodyFamily.deltaMax ≤ C := by
    exact
      (tubeSubfamily_deltaMax_le fiber).trans hdeltaMax
  have hfiber_contained :
      ∀ index,
        (fiber.family.toBodyFamily.body index).carrier ⊆
          container := by
    intro index
    change
      (fiber.family.tube index).carrier ⊆
        container
    rw [fiber.tube_eq index]
    have hindex :
        fiber.embedding index ∈
          P.toFactoring.fiberIndices parent :=
      Finset.orderEmbOfFin_mem
        (P.toFactoring.fiberIndices parent) rfl index
    have hparent :
        P.parent (fiber.embedding index) = parent :=
      (Finset.mem_filter.mp hindex).2
    have hnested := P.nested (fiber.embedding index)
    simpa [container, hparent] using hnested
  have hfiber_mass :
      fiber.family.toBodyFamily.mass =
        P.toFactoring.fiberCount parent *
          Kakeya.deltaTubeVolume delta := by
    rw [TubeFamily.bodyMass_eq_nominalMass]
    change
      ((P.toFactoring.fiberIndices parent).card : ENNReal) *
          Kakeya.deltaTubeVolume delta =
        P.toFactoring.fiberCount parent *
          Kakeya.deltaTubeVolume delta
    rfl
  have hfiber_contained_mass :
      fiber.family.toBodyFamily.containedMass container =
        fiber.family.toBodyFamily.mass :=
    BodyFamily.containedMass_eq_mass_of_all_contained
      fiber.family.toBodyFamily container hfiber_contained
  have hmass :
      minimumMass ≤
        fiber.family.toBodyFamily.containedMass container := by
    rw [hfiber_contained_mass, hfiber_mass]
    change
      C * containerVolume * power ≤
        P.toFactoring.fiberCount parent *
          Kakeya.deltaTubeVolume delta
    rw [hcontainer_volume]
    dsimp only [power]
    simpa [mul_assoc] using hcluster

  have hfrostman :
      fiber.family.toBodyFamily.IsCFrostmanIn container
        (C * containerVolume / minimumMass) :=
    BodyFamily.frostman_from_deltaMax
      hminimum_pos hminimum_top
      hcontainer_pos hcontainer_top
      hfiber_deltaMax hmass
  have hbase_pos : 0 < C * containerVolume := by
    positivity
  have hbase_top : C * containerVolume ≠ ⊤ :=
    ENNReal.mul_ne_top hCtop hcontainer_top
  have hcancel :
      C * containerVolume / minimumMass =
        power⁻¹ := by
    dsimp only [minimumMass]
    let base := C * containerVolume
    change base / (base * power) = power⁻¹
    have hinverse :
        (base * power)⁻¹ =
          base⁻¹ * power⁻¹ :=
      ENNReal.mul_inv
        (Or.inl hbase_pos.ne')
        (Or.inl hbase_top)
    calc
      base / (base * power)
          = base * (base * power)⁻¹ := by rfl
      _ = base * (base⁻¹ * power⁻¹) := by
            rw [hinverse]
      _ = (base * base⁻¹) * power⁻¹ := by
            ring
      _ = (base / base) * power⁻¹ := by rfl
      _ = power⁻¹ := by
            rw [ENNReal.div_self hbase_pos.ne' hbase_top]
            simp
  have hpower_inverse :
      power⁻¹ =
        Kakeya.realRpowENN delta (-eta) := by
    dsimp only [power]
    exact
      (Kakeya.Streamlined.GeneralizedFrostman.realRpowENN_neg
        hdelta).symm
  rw [hcancel, hpower_inverse] at hfrostman
  exact hfrostman

/--
Finite-grid lower-fiber mass bounds imply all-real-scale Frostman control for
the all-scale structure built from dilated covers.
-/
theorem all_scale_balanced_from_dilated_cover_frostman
    {delta eta A : ℝ}
    (hdelta : 0 < delta)
    {G : TubeFamily delta}
    {N : ℕ}
    (sigma : Fin (N + 1) → AdmissibleScale delta)
    (lower : (cut : Fin N) →
      TubeFamily (sigma (Fin.castSucc cut)).1)
    (cover : (cut : Fin N) →
      DilatedTubeCover A G (lower cut))
    (K Cbase : ENNReal)
    (degree : Fin N → ℕ)
    (package :
      AllScaleBalancedFromDilatedCoverPackage
        G sigma lower cover K Cbase degree)
    (houtput :
      0 < dominatingUpperFromDilatedCoverDilation A)
    {C : ENNReal}
    (hCpos : 0 < C)
    (hCtop : C ≠ ⊤)
    (hdeltaMax : G.toBodyFamily.deltaMax ≤ C)
    (hcluster :
      ∀ (cut : Fin N)
        (parent : Fin (lower cut).card),
        C *
              dilatedCoverVolumeFactor
                (dominatingUpperFromDilatedCoverDilation A) *
              Kakeya.deltaTubeVolume
                (sigma (Fin.succ cut)).1 *
            Kakeya.realRpowENN delta eta ≤
          (cover cut).toFactoring.fiberCount parent *
            Kakeya.deltaTubeVolume delta) :
    package.uts.toDilatedUniformTubeStructure.IsFrostmanAtEveryScale
      (Kakeya.realRpowENN delta (-eta)) := by
  intro rho parent
  let cut := package.bracket rho
  let lowerParent := package.lowerFiber rho parent
  have hvolume :
      Kakeya.deltaTubeVolume rho.1 ≤
        Kakeya.deltaTubeVolume
          (sigma (Fin.succ cut)).1 :=
    deltaTubeVolume_mono (package.bracket_upper rho)
  have hlower :=
    hcluster cut lowerParent
  have hcurrent :
      C *
            dilatedCoverVolumeFactor
              (dominatingUpperFromDilatedCoverDilation A) *
            Kakeya.deltaTubeVolume rho.1 *
          Kakeya.realRpowENN delta eta ≤
        (package.uts.cover rho).toFactoring.fiberCount parent *
          Kakeya.deltaTubeVolume delta := by
    calc
      C *
              dilatedCoverVolumeFactor
                (dominatingUpperFromDilatedCoverDilation A) *
              Kakeya.deltaTubeVolume rho.1 *
            Kakeya.realRpowENN delta eta
          ≤
          C *
              dilatedCoverVolumeFactor
                (dominatingUpperFromDilatedCoverDilation A) *
              Kakeya.deltaTubeVolume
                (sigma (Fin.succ cut)).1 *
            Kakeya.realRpowENN delta eta := by
              gcongr
      _ ≤
          (cover cut).toFactoring.fiberCount lowerParent *
            Kakeya.deltaTubeVolume delta := hlower
      _ ≤
          (package.uts.cover rho).toFactoring.fiberCount parent *
            Kakeya.deltaTubeVolume delta := by
              gcongr
              exact package.factoringFiberCount_lower rho parent
  exact
    full_containment_fiber_frostman_of_dilated_cover_cluster_mass
      hdelta
      (hdelta.trans_le rho.2.1)
      (package.uts.cover rho) parent
      hCpos hCtop
      (ENNReal.ofReal_pos.mpr (by
        positivity))
      ENNReal.ofReal_ne_top
      hdeltaMax
      (by
        rw [Kakeya.Streamlined.volume_dilatedTubeCarrier
          houtput.ne' ((package.uts.coarse rho).tube parent),
          abs_of_pos houtput])
      hcurrent

/--
Transport assigned-fiber Frostman control from every lower grid cover to the
all-real assigned covers produced by `all_scale_balanced_from_dilated_cover`.

The final parent map is an explicit regrouping of the lower-grid parent map.
The nearby-scale tube-volume loss is bounded by `K`, and the final fixed
dilation contributes its cubic volume factor.  No ambient `deltaMax` or
cluster-mass premise is used.
-/
theorem all_scale_balanced_from_dilated_cover_assigned_frostman
    {delta A : ℝ}
    (hdelta : 0 < delta)
    {G : TubeFamily delta}
    {N : ℕ}
    (sigma : Fin (N + 1) → AdmissibleScale delta)
    (lower : (cut : Fin N) →
      TubeFamily (sigma (Fin.castSucc cut)).1)
    (cover : (cut : Fin N) →
      DilatedTubeCover A G (lower cut))
    (K Cbase : ENNReal)
    (degree : Fin N → ℕ)
    (package :
      AllScaleBalancedFromDilatedCoverPackage
        G sigma lower cover K Cbase degree)
    (hA : 1 ≤ A)
    (hK :
      ∀ cut : Fin N,
        2 * ENNReal.ofReal
            (WithShading.cVol
              ((sigma (Fin.succ cut)).1 /
                (sigma (Fin.castSucc cut)).1)) ≤
          K)
    {Cgrid : ENNReal}
    (hgridFrostman :
      ∀ cut, (cover cut).toFactoring.FibersAreCFrostman Cgrid) :
    ∀ rho, (package.uts.cover rho).toFactoring.FibersAreCFrostman
      (allScaleAssignedFrostmanTransportLoss A K * Cgrid) := by
  intro rho
  let cut := package.bracket rho
  let low : ℝ := (sigma (Fin.castSucc cut)).1
  let high : ℝ := (sigma (Fin.succ cut)).1
  let outputDilation := dominatingUpperFromDilatedCoverDilation A
  have hlow : 0 < low :=
    hdelta.trans_le (sigma (Fin.castSucc cut)).2.1
  have hrho : 0 < rho.1 := hdelta.trans_le rho.2.1
  have hhigh : 0 < high := hdelta.trans_le (sigma (Fin.succ cut)).2.1
  have hratioPositive : 0 < high / low := div_pos hhigh hlow
  have hhighRatio : high ≤ (high / low) * low := by
    rw [div_mul_cancel₀ high hlow.ne']
  have hvolumeRatio :
      Kakeya.deltaTubeVolume rho.1 ≤
        ENNReal.ofReal (WithShading.cVol (high / low)) *
          Kakeya.deltaTubeVolume low := by
    simpa [low, high, WithShading.cVol] using
      scale_volume_ratio hlow hrho
        (package.bracket_lower rho) (package.bracket_upper rho)
        hhighRatio hratioPositive (sigma (Fin.succ cut)).2.2
  have hcoefficient : ENNReal.ofReal (WithShading.cVol (high / low)) ≤ K := by
    calc
      ENNReal.ofReal (WithShading.cVol (high / low)) ≤
          2 * ENNReal.ofReal (WithShading.cVol (high / low)) := by
        exact le_mul_of_one_le_left (by positivity) (by norm_num)
      _ ≤ K := by simpa [low, high] using hK cut
  have hvolumeScale :
      Kakeya.deltaTubeVolume rho.1 ≤
        K * Kakeya.deltaTubeVolume low :=
    hvolumeRatio.trans <| by gcongr
  have houtput : 0 < outputDilation := by
    dsimp only [outputDilation, dominatingUpperFromDilatedCoverDilation]
    nlinarith
  have hAfactor : 1 ≤ ENNReal.ofReal (A ^ 3) := by
    apply ENNReal.one_le_ofReal.mpr
    nlinarith [sq_nonneg A]
  apply Factoring.regroup_frostman_of_parent_volume_ratio
      (P1 := (cover cut).toFactoring)
      (Q := (package.uts.cover rho).toFactoring)
      (group := package.lowerParent rho)
      (C := Cgrid)
      (Cvol := allScaleAssignedFrostmanTransportLoss A K)
  · exact package.cover_parent rho
  · exact hgridFrostman cut
  · exact dilatedTubeBodyFamily_convex
      (lt_of_lt_of_le zero_lt_one hA) hlow.le (lower cut)
  · intro finalParent middleParent _hgroup
    change
      volume
          (dilatedTubeCarrier outputDilation
            ((package.uts.coarse rho).tube finalParent)) ≤
        allScaleAssignedFrostmanTransportLoss A K *
          volume
            (dilatedTubeCarrier A
              ((lower cut).tube middleParent))
    rw [volume_dilatedTubeCarrier houtput.ne',
      volume_dilatedTubeCarrier (ne_of_gt (zero_lt_one.trans_le hA)),
      abs_of_pos houtput, abs_of_pos (zero_lt_one.trans_le hA)]
    dsimp only [allScaleAssignedFrostmanTransportLoss,
      dilatedCoverVolumeFactor, outputDilation]
    calc
      ENNReal.ofReal
            (dominatingUpperFromDilatedCoverDilation A ^ 3) *
          Kakeya.deltaTubeVolume rho.1
          ≤ ENNReal.ofReal
              (dominatingUpperFromDilatedCoverDilation A ^ 3) *
            (K * Kakeya.deltaTubeVolume low) := by
        gcongr
      _ = (K * ENNReal.ofReal
              (dominatingUpperFromDilatedCoverDilation A ^ 3)) *
            Kakeya.deltaTubeVolume low := by ring
      _ ≤ (K * ENNReal.ofReal
              (dominatingUpperFromDilatedCoverDilation A ^ 3)) *
            (ENNReal.ofReal (A ^ 3) *
              Kakeya.deltaTubeVolume low) := by
        gcongr
        exact le_mul_of_one_le_left (by positivity) hAfactor

end Kakeya.Streamlined.RandomTranslation

end
