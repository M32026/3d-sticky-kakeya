module

public import Kakeya.DimensionThree.MainLemma1.RevisedSource.AxisFootNormalizationGeometryW103

@[expose] public section

open MeasureTheory ConvexSpaceBody ShadedBody
open scoped ENNReal NNReal

namespace Kakeya.ml1Boot.TrialRestartW94

noncomputable section
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

universe uE uI

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]

theorem exists_axisFoot_shading_transport_w103 {iota : Type uI} {r s : NNReal}
    (F : Finset iota) (T : iota -> Tube r E) (Z : iota -> ShadedTube r E)
    (hZT : ∀ i ∈ F, (Z i).toTube = T i) (L : E ≃ᵃ[Real] E)
    (himage : ∀ i ∈ F, L '' (T i).carrier ⊆ (axisFootTubeW103 s L (T i)).carrier)
    (C : NNReal) (hC : 1 <= C)
    (hvolume : ∀ i ∈ F, volume (axisFootTubeW103 s L (T i)).carrier <=
      (C : ENNReal) * volume (L '' (T i).carrier)) :
    ∃ V : iota -> ShadedTube s E,
      (∀ i, (V i).toTube = axisFootTubeW103 s L (T i)) ∧
      (∀ i ∈ F, (V i).shade = L '' (Z i).shade) ∧
      (C : ENNReal)⁻¹ * fullness' F (fun i => (Z i).toShadedBody) <=
        fullness' F (fun i => (V i).toShadedBody) ∧
      ShadedBody.multiplicity F (fun i => (V i).toShadedBody) =
        ShadedBody.multiplicity F (fun i => (Z i).toShadedBody) := by
  let W := fun i => axisFootTubeW103 s L (T i)
  let V : iota -> ShadedTube s E := fun i =>
    { toTube := W i
      shade := (L '' (Z i).shade) ∩ (W i).carrier
      measurableSet_shade := ((Kakeya.measurableEmbedding_affineEquiv L).measurableSet_image'
        (Z i).measurableSet_shade).inter (W i).isCompact.measurableSet
      shade_subset := Set.inter_subset_right }
  have hVt : ∀ i, (V i).toTube = W i := fun _ => rfl
  have hVs : ∀ i ∈ F, (V i).shade = L '' (Z i).shade := by
    intro i hi
    apply Set.inter_eq_left.mpr
    refine (Set.image_mono (Z i).shade_subset).trans ?_
    change L '' (Z i).toTube.carrier ⊆ (W i).carrier
    rw [hZT i hi]
    exact himage i hi
  let Zimage := fun i => (Z i).toShadedBody.affineImage L.toAffineMap
    L.toContinuousAffineEquiv.continuous (Kakeya.measurableEmbedding_affineEquiv L)
  have hshade : ∀ i ∈ F, (V i).shade = (Zimage i).shade := by
    intro i hi
    exact hVs i hi
  have hvol : ∀ i ∈ F, volume (V i).carrier <= (C : ENNReal) * volume (Zimage i).carrier := by
    intro i hi
    have heq : (Z i).toTube.carrier = (T i).carrier := congrArg (fun U : Tube r E => U.carrier) (hZT i hi)
    change volume (W i).carrier <= (C : ENNReal) * volume (L '' (Z i).carrier)
    rw [heq]
    exact hvolume i hi
  have hfull := Tube.le_fullness_of_volume_le hC F Zimage (fun i => (V i).toShadedBody) hshade hvol
  have hfullEq : fullness F Zimage = fullness F (fun i => (Z i).toShadedBody) :=
    ShadedBody.fullness_affineImage F (fun i => (Z i).toShadedBody) L _ _
  rw [hfullEq] at hfull
  have hfull' := ENNReal.coe_le_coe.mpr hfull
  rw [ENNReal.coe_mul, ENNReal.coe_inv (zero_lt_one.trans_le hC).ne',
    ShadedBody.coe_fullness, ShadedBody.coe_fullness] at hfull'
  refine ⟨V, hVt, hVs, hfull', ?_⟩
  calc
    ShadedBody.multiplicity F (fun i => (V i).toShadedBody) = ShadedBody.multiplicity F Zimage :=
      Tube.multiplicity_congr_of_shading_eq F Zimage (fun i => (V i).toShadedBody) hshade
    _ = ShadedBody.multiplicity F (fun i => (Z i).toShadedBody) :=
      ShadedBody.multiplicity_affineImage F (fun i => (Z i).toShadedBody) L _ _

end

end Kakeya.ml1Boot.TrialRestartW94
