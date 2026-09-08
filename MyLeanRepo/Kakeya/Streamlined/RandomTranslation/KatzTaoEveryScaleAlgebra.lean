import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.FineDeltaMax
import MyLeanRepo.Kakeya.Streamlined.RandomTranslation.AssemblyHelpers
import MyLeanRepo.Kakeya.Streamlined.IndependentDilatedCoverFullFiberMass
import MyLeanRepo.Kakeya.Streamlined.DividingScales.ParentEnvelopeCounting
import MyLeanRepo.Kakeya.Streamlined.GeneralizedFrostman.AlgebraHelpers

/-!
# Shared algebra for Katz--Tao-at-every-scale assemblies

These lemmas are independent of whether the sticky input is expressed with
strict assigned fibers or fixed-dilation full geometric containment fibers.
They are kept outside the retired bounded-ball compatibility assembly so the
canonical corrected theorem does not import an invalid cover conversion.
-/

noncomputable section

open MeasureTheory

namespace Kakeya.Streamlined

/-- Bound nominal tube mass using the Katz--Tao-at-every-scale hypothesis. -/
lemma nominalMass_le_katzTao_bound
    {delta : ℝ} {F : TubeFamily delta}
    {U : UniformTubeStructure F} {eta : ℝ}
    (hdelta : 0 < delta) (hdeltaOne : delta ≤ 1)
    (heta : 0 < eta)
    (hFBall : F.IsInUnitBall)
    (hFED : F.IsEssentiallyDistinct)
    (hUUniform : U.uniformity ≤ Kakeya.realRpowENN delta (-eta))
    (hUKT :
      U.IsKatzTaoAtEveryScale
        (Kakeya.realRpowENN delta (-eta))) :
    F.nominalMass ≤
      volume unitBall.carrier *
        Kakeya.realRpowENN delta (-3 * eta) := by
  have hdeltaMax :
      F.toBodyFamily.deltaMax ≤
        U.uniformity ^ 2 *
          Kakeya.realRpowENN delta (-eta) :=
    fine_deltaMax_from_coarse_at_delta
      hdelta hdeltaOne hFED U hUKT
  have huniformity :
      U.uniformity ^ 2 ≤
        Kakeya.realRpowENN delta (-2 * eta) := by
    have hpow :
        Kakeya.realRpowENN delta (-eta) ^ 2 =
          Kakeya.realRpowENN delta (-eta) *
            Kakeya.realRpowENN delta (-eta) := by
      ring
    calc
      U.uniformity ^ 2
          ≤ Kakeya.realRpowENN delta (-eta) ^ 2 := by
            gcongr
      _ =
          Kakeya.realRpowENN delta (-eta) *
            Kakeya.realRpowENN delta (-eta) := hpow
      _ =
          Kakeya.realRpowENN delta ((-eta) + (-eta)) :=
        (GeneralizedFrostman.realRpowENN_add hdelta).symm
      _ = Kakeya.realRpowENN delta (-2 * eta) := by ring_nf
  have hdeltaMaxFinal :
      F.toBodyFamily.deltaMax ≤
        Kakeya.realRpowENN delta (-3 * eta) := by
    calc
      F.toBodyFamily.deltaMax
          ≤ U.uniformity ^ 2 *
              Kakeya.realRpowENN delta (-eta) :=
        hdeltaMax
      _ ≤
          Kakeya.realRpowENN delta (-2 * eta) *
            Kakeya.realRpowENN delta (-eta) := by
        gcongr
      _ =
          Kakeya.realRpowENN delta ((-2 * eta) + (-eta)) :=
        (GeneralizedFrostman.realRpowENN_add hdelta).symm
      _ = Kakeya.realRpowENN delta (-3 * eta) := by ring_nf
  let ballVolume : ENNReal := volume unitBall.carrier
  have hBallTop : ballVolume ≠ ⊤ :=
    unitBall_volume_pos_and_lt_top.2
  have hBallPos : 0 < ballVolume :=
    unitBall_volume_pos_and_lt_top.1
  have hAllIn :
      ∀ index,
        (F.toBodyFamily.body index).carrier ⊆
          unitBall.carrier := by
    intro index
    exact hFBall index
  have hIndices :
      F.toBodyFamily.containedIndices unitBall.carrier =
        Finset.univ := by
    ext index
    simp [BodyFamily.containedIndices, hAllIn]
  have hContainedAll :
      F.toBodyFamily.containedMass unitBall.carrier =
        F.toBodyFamily.mass := by
    rw [BodyFamily.containedMass, hIndices]
    rfl
  have hContained :
      F.toBodyFamily.containedMass unitBall.carrier ≤
        F.toBodyFamily.deltaMax * ballVolume :=
    BodyFamily.containedMass_le_deltaMax_mul_volume
      F.toBodyFamily
      (convex_closedBall (0 : Point3) 1)
      hBallPos.ne' hBallTop
  have hMass :
      F.toBodyFamily.mass ≤
        F.toBodyFamily.deltaMax * ballVolume := by
    rw [← hContainedAll]
    exact hContained
  calc
    F.nominalMass = F.toBodyFamily.mass :=
      F.bodyMass_eq_nominalMass.symm
    _ ≤ F.toBodyFamily.deltaMax * ballVolume := hMass
    _ ≤
        Kakeya.realRpowENN delta (-3 * eta) *
          ballVolume := by
      gcongr
    _ =
        ballVolume *
          Kakeya.realRpowENN delta (-3 * eta) := by ring

/-- For positive finite `a`, multiplying `max 1 a⁻¹` by `a` gives `max a 1`. -/
lemma ennreal_mul_max_inv
    (a : ENNReal) (haZero : a ≠ 0) (haTop : a ≠ ⊤) :
    a * max 1 a⁻¹ = max a 1 := by
  by_cases h : a ≤ 1
  · have hinv : 1 ≤ a⁻¹ := by
      have h' : a⁻¹ ≥ 1⁻¹ := by gcongr
      simpa using h'
    rw [max_eq_right hinv, ENNReal.mul_inv_cancel haZero haTop,
      max_eq_right h]
  · have ha : 1 < a := lt_of_not_ge h
    have hinv : a⁻¹ ≤ 1 := by
      have h' : a⁻¹ ≤ 1⁻¹ := by gcongr
      simpa using h'
    rw [max_eq_left hinv, mul_one, max_eq_left ha.le]

/-- Weaken an assigned-fiber Frostman-at-every-scale bound. -/
lemma frostman_at_every_scale_weaken
    {delta : ℝ} {F : TubeFamily delta}
    {U : UniformTubeStructure F} {C₁ C₂ : ENNReal}
    (hC : C₁ ≤ C₂)
    (h : U.IsFrostmanAtEveryScale C₁) :
    U.IsFrostmanAtEveryScale C₂ := by
  intro rho
  intro parent
  intro K hK hContained
  exact (h rho parent K hK hContained).trans (by gcongr)

/-- Weaken the density parameter of a shading. -/
lemma isLambdaDense_weaken
    {delta : ℝ} {F : TubeFamily delta}
    {Y : TubeShading F} {lambda₁ lambda₂ : ENNReal}
    (hlambda : lambda₂ ≤ lambda₁)
    (h : Y.IsLambdaDense lambda₁) :
    Y.IsLambdaDense lambda₂ :=
  (mul_le_mul_right' hlambda F.toBodyFamily.mass).trans h

end Kakeya.Streamlined

end
