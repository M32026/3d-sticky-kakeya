module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.AxisFootNormalizationGeometryW103
public import Kakeya.ConvexBody.ContainerChange

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody
open scoped ENNReal NNReal

namespace Kakeya.ml1Boot.TrialRestartW94

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
attribute [local instance] Classical.propDecidable

universe uE uI

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

theorem axisFoot_family_frostman_w103 (hdim : Module.finrank Real E = 3)
    {iota : Type uI} {r theta R : NNReal} (hr : 0 < r) (hrt : r <= theta)
    (ht1 : theta <= 1) (hR : 1 <= R)
    (hRn : Tube.normalization.C (Module.finrank Real E) <= R)
    (top : Tube theta E) (F : Finset iota) (T : iota -> Tube r E)
    (P : ConvexSpaceBody E) (hPpos : volume P.carrier ≠ 0)
    (hPtop : P <= top.toConvexSpaceBody) (hTP : ∀ i ∈ F, (T i).toConvexSpaceBody <= P)
    (L : E ≃ᵃ[Real] E) (hL : L.toAffineMap = top.rescaleMap (R : Real))
    (Cext : NNReal) (hCext : (192 * R) ^ (3 : Nat) * 6 <= Cext)
    (K : ConvexSpaceBody E)
    (hPK : P.affineImage L.toAffineMap L.toContinuousAffineEquiv.continuous <= K)
    (hVK : ∀ i ∈ F, (axisFootTubeW103 (r / theta) L (T i)).toConvexSpaceBody <= K)
    (hKvol : volume K.carrier <= (Cext : ENNReal) * volume (L '' P.carrier)) :
    let C : ENNReal := Cext
    frostmanConstIn F (fun i => (T i).toConvexSpaceBody) P <= C ^ (2 : Nat) *
      frostmanConstIn F (fun i => (axisFootTubeW103 (r / theta) L (T i)).toConvexSpaceBody) K ∧
    frostmanConstIn F (fun i => (axisFootTubeW103 (r / theta) L (T i)).toConvexSpaceBody) K <=
      C ^ (2 : Nat) * frostmanConstIn F (fun i => (T i).toConvexSpaceBody) P := by
  let C : ENNReal := Cext
  let W := fun i => (T i).toConvexSpaceBody.affineImage L.toAffineMap L.toContinuousAffineEquiv.continuous
  let V := fun i => (axisFootTubeW103 (r / theta) L (T i)).toConvexSpaceBody
  let P' := P.affineImage L.toAffineMap L.toContinuousAffineEquiv.continuous
  have hC : (1 : ENNReal) <= C := by
    dsimp only [C]
    norm_cast
    have hmul : (1 : NNReal) <= 192 * R := by nlinarith
    have hp : (1 : NNReal) <= (192 * R) ^ (3 : Nat) := one_le_pow₀ hmul
    nlinarith
  have hTtop : ∀ i ∈ F, (T i).toConvexSpaceBody <= top.toConvexSpaceBody := fun i hi => (hTP i hi).trans hPtop
  have hWV : ∀ i ∈ F, W i <= V i := fun i hi =>
    (axisFootTube_image_w103 hr hrt ht1 hR hRn top (T i) (hTtop i hi) L hL).1
  have hWvol : ∀ i ∈ F, volume (V i).carrier <= C * volume (W i).carrier := by
    intro i hi
    refine (axisFootTube_volume_w103 hdim hr hrt ht1 hR hRn top (T i) (hTtop i hi) L hL).2.trans ?_
    apply mul_le_mul_right'
    change (((48 * R) ^ (3 : Nat) : NNReal) : ENNReal) <= C
    dsimp only [C]
    norm_cast
    have hh : (48 * R : NNReal) <= 192 * R := by nlinarith
    have hp := pow_le_pow_left₀ (by positivity) hh (3 : Nat)
    nlinarith
  have hD : ∀ K' : ConvexSpaceBody E, K' <= K -> ∃ D : ConvexSpaceBody E,
      K' <= D ∧ volume D.carrier <= C * volume K'.carrier ∧ ∀ i ∈ F, W i <= K' -> V i <= D := by
    intro K' hK'
    let Dold := K'.affineImage L.symm.toAffineMap L.symm.toContinuousAffineEquiv.continuous
    obtain ⟨D, hDD, hvolD, hVD⟩ := axisFoot_family_forward_test_w103 hdim hr hrt ht1 hR hRn
      top F T hTtop L hL Dold
    have him : Dold.affineImage L.toAffineMap L.toContinuousAffineEquiv.continuous = K' :=
      ConvexSpaceBody.affineImage_symm_affineImage K' L _ _
    refine ⟨D, him ▸ hDD, ?_, ?_⟩
    · change volume D.carrier <= (((192 * R) ^ (3 : Nat) * 6 : NNReal) : ENNReal) *
        volume (Dold.affineImage L.toAffineMap L.toContinuousAffineEquiv.continuous).carrier at hvolD
      rw [him] at hvolD
      exact hvolD.trans (mul_le_mul_right' (ENNReal.coe_le_coe.mpr hCext) _)
    · intro i hi hiK
      apply hVD i hi
      apply (ConvexSpaceBody.affineImage_le_affineImage_iff L.toAffineMap
        L.toContinuousAffineEquiv.continuous L.injective).mp
      change W i <= Dold.affineImage L.toAffineMap L.toContinuousAffineEquiv.continuous
      rwa [him]
  have hcompare := ConvexSpaceBody.frostmanConstIn_ge_of_comparable_of_enlargement
    hC hVK hWV hWvol hD
  have hWP : ∀ i ∈ F, W i <= P' := fun i hi =>
    (ConvexSpaceBody.affineImage_le_affineImage_iff L.toAffineMap
      L.toContinuousAffineEquiv.continuous L.injective).mpr (hTP i hi)
  have hP'pos : volume P'.carrier ≠ 0 := by
    rw [ConvexSpaceBody.volume_affineImage]
    exact mul_ne_zero (Kakeya.ofReal_abs_det_affineEquiv_ne_zero L) hPpos
  have hratio : volume K.carrier / volume P'.carrier <= C := by
    exact (ENNReal.div_le_iff hP'pos P'.isCompact'.measure_ne_top).mpr hKvol
  have hCFold : frostmanConstIn F W P' = frostmanConstIn F (fun i => (T i).toConvexSpaceBody) P :=
    ConvexSpaceBody.frostmanConstIn_affineImage F _ P L _
  constructor
  · rw [← hCFold]
    exact (ConvexSpaceBody.frostmanConstIn_le_of_container_le hPK hWP).trans hcompare.1
  · calc
      frostmanConstIn F V K <= C * frostmanConstIn F W K := hcompare.2
      _ <= C * (volume K.carrier / volume P'.carrier * frostmanConstIn F W P') :=
        mul_le_mul_left' (ConvexSpaceBody.frostmanConstIn_ambient_mono hPK hP'pos hWP) _
      _ <= C * (C * frostmanConstIn F W P') := by gcongr
      _ = _ := by rw [hCFold]; ring

end

end Kakeya.ml1Boot.TrialRestartW94
