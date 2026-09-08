import MyLeanRepo.Kakeya.Integration.CompetitorStickySpace3
import Kakeya.DimensionThree.IsometryTransport

/-!
# The competitor Sticky theorem in an arbitrary real three-space

This file transports the coordinate-space theorem along the canonical linear
isometry associated to an orthonormal basis.  The index type, source family,
shading, and hierarchy assignments are unchanged.
-/

noncomputable section

open MeasureTheory

namespace Tube.UniformTubeSet.IsFrostmanAtEveryScale

variable
  {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [Nontrivial F] [MeasurableSpace F] [BorelSpace F]
  {ι : Type*}

/-- The every-scale Frostman condition is invariant under simultaneous
isometric transport of the leaves and every node of the same hierarchy. -/
theorem mapLinearIsometryEquiv {delta : NNReal} {s : Finset ι}
    {T : ι → Tube delta E} {N : ℕ} {uniformity : NNReal}
    {frostman : ENNReal} (U : Tube.UniformTubeSet s T N uniformity)
    (h : U.IsFrostmanAtEveryScale frostman) (f : E ≃ₗᵢ[ℝ] F) :
    (U.mapLinearIsometryEquiv f).IsFrostmanAtEveryScale frostman := by
  intro k hk j hj
  simpa only [Tube.UniformTubeSet.mapLinearIsometryEquiv_cover,
    Tube.GridCoverSystem.mapLinearIsometryEquiv_indexSet,
    Tube.GridCoverSystem.mapLinearIsometryEquiv_assign,
    Tube.GridCoverSystem.mapLinearIsometryEquiv_tube,
    Tube.mapLinearIsometryEquiv_toConvexSpaceBody] using
    (h k hk j hj).mapLinearIsometryEquiv f

end Tube.UniformTubeSet.IsFrostmanAtEveryScale

namespace Kakeya.Integration

universe uE uI

/-- The coordinate-space competitor theorem transported to every real inner-product
space of dimension three. -/
theorem stickyFrostmanEstimate_of_finrank_three
    {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
    (hdim : Module.finrank ℝ E = 3) :
    StickyKakeya.StickyFrostmanEstimate.{uE, uI} (E := E) := by
  intro epsilon hepsilon
  rcases stickyFrostmanEstimate_space3.{uI} epsilon hepsilon with
    ⟨eta, delta0, heta, hdelta0, hspace3⟩
  refine ⟨eta, delta0, heta, hdelta0, ?_⟩
  intro delta hdelta hdeltaSmall ι s V hsupport hED C hC hierarchy
    hfullness hFrostman
  let f : E ≃ₗᵢ[ℝ] Space3 := Kakeya.dimThreeLinearIsometryEquiv E hdim
  let V' : ι → ShadedTube delta Space3 :=
    fun i => (V i).mapLinearIsometryEquiv f
  let hierarchy' : ShadedTube.ShadedUniformTubeSet s V'
      (Tube.ssfGridLen delta) C := hierarchy.mapLinearIsometryEquiv f
  have hsupport' : ∀ i ∈ s, (V' i).carrier ⊆
      Metric.closedBall (0 : Space3) 1 := by
    intro i hi
    dsimp only [V']
    rw [ShadedTube.mapLinearIsometryEquiv_carrier]
    calc
      f '' (V i).carrier ⊆ f '' Metric.closedBall (0 : E) 1 :=
        Set.image_mono (hsupport i hi)
      _ = Metric.closedBall (0 : Space3) 1 := by
        simpa using f.image_closedBall (0 : E) 1
  have hED' : (s : Set ι).Pairwise
      (fun i j => IsEssentiallyDistinct (V' i).carrier (V' j).carrier) := by
    intro i hi j hj hij
    simpa only [V', ShadedTube.mapLinearIsometryEquiv_carrier] using
      (hED hi hj hij).mapLinearIsometryEquiv f
  have hC' : C ≤ ShadedTube.ssfUniformConst
      (Module.finrank ℝ Space3) := by
    simpa [hdim] using hC
  have hfullness' : ENNReal.ofReal ((delta : ℝ) ^ eta) ≤
      ShadedBody.fullness' s (fun i => (V' i).toShadedBody) := by
    simpa only [V', ShadedTube.fullness'_mapLinearIsometryEquiv] using hfullness
  have hFrostman' : hierarchy'.tubeUniform.IsFrostmanAtEveryScale
      (ENNReal.ofReal ((delta : ℝ) ^ (-eta))) := by
    exact hFrostman.mapLinearIsometryEquiv hierarchy.tubeUniform f
  have hresult := hspace3 hdelta hdeltaSmall s V' hsupport' hED' hC'
    hierarchy' hfullness' hFrostman'
  simpa only [V', ShadedTube.volume_iUnion_mapLinearIsometryEquiv_shade] using hresult

end Kakeya.Integration

end
