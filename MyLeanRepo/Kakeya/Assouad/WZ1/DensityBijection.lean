import MyLeanRepo.Kakeya.Assouad.WZ1.ProjectionTheoremFirstLayerStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma49ActualAffineTripleTransportStatements
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Density preservation under coordinatewise bijections

Uniform tripartite density is preserved exactly under bijections of the three
vertex classes.  The main application is the literal affine normalization in
PDF Lemma 8.13.
-/

namespace Kakeya.Assouad

open scoped ENNReal

/-- The contragredient action attached to a linear equivalence. -/
noncomputable def contragredientEquiv
    (linear : Point2 ≃ₗ[ℝ] Point2) :
    Point2 ≃ₗ[ℝ] Point2 :=
  let forward : Point2 →ₗ[ℝ] Point2 :=
    linear.toLinearMap
  let inverse : Point2 →ₗ[ℝ] Point2 :=
    linear.symm.toLinearMap
  let forwardAdjoint : Point2 →ₗ[ℝ] Point2 :=
    forward.adjoint
  let inverseAdjoint : Point2 →ₗ[ℝ] Point2 :=
    inverse.adjoint
  have hleft :
      forwardAdjoint.comp inverseAdjoint =
        LinearMap.id := by
    have hcomposition :
        (inverse.comp forward).adjoint =
          forwardAdjoint.comp inverseAdjoint := by
      rw [LinearMap.adjoint_comp]
    have hinverse :
        inverse.comp forward = LinearMap.id := by
      apply LinearMap.ext
      intro point
      exact linear.symm_apply_apply point
    rw [← hcomposition, hinverse]
    simp
  have hright :
      inverseAdjoint.comp forwardAdjoint =
        LinearMap.id := by
    have hcomposition :
        (forward.comp inverse).adjoint =
          inverseAdjoint.comp forwardAdjoint := by
      rw [LinearMap.adjoint_comp]
    have hinverse :
        forward.comp inverse = LinearMap.id := by
      apply LinearMap.ext
      intro point
      exact linear.apply_symm_apply point
    rw [← hcomposition, hinverse]
    simp
  { toFun := inverseAdjoint
    invFun := forwardAdjoint
    left_inv := fun point => by
      have h := congrArg
        (fun map : Point2 →ₗ[ℝ] Point2 => map point) hleft
      simpa using h
    right_inv := fun point => by
      have h := congrArg
        (fun map : Point2 →ₗ[ℝ] Point2 => map point) hright
      simpa using h
    map_add' := inverseAdjoint.map_add
    map_smul' := inverseAdjoint.map_smul }

/-- The endpoint affine map as an equivalence of points. -/
def affineEndpointEquiv
    (linear : Point2 ≃ₗ[ℝ] Point2)
    (translation : Point2) :
    Point2 ≃ Point2 where
  toFun point := linear point + translation
  invFun point := linear.symm (point - translation)
  left_inv point := by
    simp
  right_inv point := by
    simp

/-- Uniform density is invariant under coordinatewise equivalences. -/
lemma density_under_coordinate_equivalences
    {F G₁ G₂ : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    {density : ENNReal}
    (hDensity :
      WZ1UniformTripleDensity density F G₁ G₂ H)
    (firstEquiv secondEquiv thirdEquiv :
      Point2 ≃ Point2) :
    WZ1UniformTripleDensity density
      (F.image firstEquiv)
      (G₁.image secondEquiv)
      (G₂.image thirdEquiv)
      (H.image fun edge =>
        (firstEquiv edge.1,
          secondEquiv edge.2.1,
          thirdEquiv edge.2.2)) := by
  classical
  let coordinateEquiv :
      Fin 3 → Point2 ≃ Point2
    | 0 => firstEquiv
    | 1 => secondEquiv
    | 2 => thirdEquiv
  let encodedEquiv :
      (Fin 3 → Point2) ≃ (Fin 3 → Point2) :=
    Equiv.piCongrRight coordinateEquiv
  let classes :=
    wz1TripleVertexClasses F G₁ G₂
  let transformedClasses :=
    wz1TripleVertexClasses
      (F.image firstEquiv)
      (G₁.image secondEquiv)
      (G₂.image thirdEquiv)
  let encoded := wz1EncodeTriples H
  let tripleMap :
      Point2 × Point2 × Point2 →
        Point2 × Point2 × Point2 :=
    fun edge =>
      (firstEquiv edge.1,
        secondEquiv edge.2.1,
        thirdEquiv edge.2.2)
  let transformed :=
    H.image tripleMap
  let transformedEncoded :=
    wz1EncodeTriples transformed
  have hcommute :
      wz1TripleCoordinate ∘ tripleMap =
        encodedEquiv ∘ wz1TripleCoordinate := by
    funext edge
    funext index
    fin_cases index <;> rfl
  have himage :
      transformedEncoded =
        encoded.image encodedEquiv := by
    calc
      transformedEncoded =
          (H.image tripleMap).image
            wz1TripleCoordinate := by rfl
      _ =
          H.image
            (wz1TripleCoordinate ∘ tripleMap) := by
        rw [Finset.image_image]
      _ =
          H.image
            (encodedEquiv ∘ wz1TripleCoordinate) := by
        rw [hcommute]
      _ =
          (H.image wz1TripleCoordinate).image
            encodedEquiv := by
        rw [← Finset.image_image]
      _ = encoded.image encodedEquiv := by rfl
  have hfiber :
      ∀ edge : Fin 3 → Point2,
        ∀ coordinates : Finset (Fin 3),
          wz1HypergraphFiber
              transformedEncoded coordinates
              (encodedEquiv edge) =
            (wz1HypergraphFiber
              encoded coordinates edge).image
                encodedEquiv := by
    intro edge coordinates
    ext candidate
    simp only [wz1HypergraphFiber,
      Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨hcandidate, hagree⟩
      rcases Finset.mem_image.mp (himage ▸ hcandidate) with
        ⟨source, hsource, rfl⟩
      have hagreeSource :
          ∀ index ∈ coordinates,
            source index = edge index := by
        intro index hindex
        have hcoordinate :
            coordinateEquiv index (source index) =
              coordinateEquiv index (edge index) := by
          simpa [encodedEquiv] using
            hagree index hindex
        exact (coordinateEquiv index).injective hcoordinate
      exact
        ⟨source, ⟨hsource, hagreeSource⟩, rfl⟩
    · rintro ⟨source, ⟨hsource, hagree⟩, rfl⟩
      have hsourceImage :
          encodedEquiv source ∈ transformedEncoded := by
        rw [himage]
        exact Finset.mem_image.mpr
          ⟨source, hsource, rfl⟩
      have hagreeImage :
          ∀ index ∈ coordinates,
            encodedEquiv source index =
              encodedEquiv edge index := by
        intro index hindex
        simp [encodedEquiv, hagree index hindex]
      exact ⟨hsourceImage, hagreeImage⟩
  have hvertexCard :
      ∀ coordinates : Finset (Fin 3),
        wz1VertexCardProduct
            transformedClasses coordinates =
          wz1VertexCardProduct classes coordinates := by
    intro coordinates
    have hcoordinate :
        ∀ index ∈ coordinates,
          ((transformedClasses index).card : ENNReal) =
            ((classes index).card : ENNReal) := by
      intro index _
      have heq :
          transformedClasses index =
            (classes index).image
              (coordinateEquiv index) := by
        fin_cases index <;> rfl
      rw [heq,
        Finset.card_image_of_injective _
          (coordinateEquiv index).injective]
    simp only [wz1VertexCardProduct]
    exact Finset.prod_congr rfl hcoordinate
  rcases hDensity with
    ⟨hNonempty, hsupport, hFiberBound⟩
  have htransformedNonempty :
      transformed.Nonempty := by
    rcases hNonempty with ⟨edge, hedge⟩
    exact
      ⟨tripleMap edge,
        Finset.mem_image.mpr ⟨edge, hedge, rfl⟩⟩
  have hsupportTransformed :
      ∀ edge ∈ transformedEncoded,
        ∀ index,
          edge index ∈ transformedClasses index := by
    intro edge hedge index
    rcases Finset.mem_image.mp (himage ▸ hedge) with
      ⟨source, hsource, rfl⟩
    have hsourceClass :
        source index ∈ classes index :=
      hsupport source hsource index
    have heq :
        transformedClasses index =
          (classes index).image
            (coordinateEquiv index) := by
      fin_cases index <;> rfl
    rw [heq]
    exact Finset.mem_image.mpr
      ⟨source index, hsourceClass, rfl⟩
  have hfiberTransformed :
      ∀ edge ∈ transformedEncoded,
        ∀ coordinates : Finset (Fin 3),
          density *
              wz1VertexCardProduct transformedClasses
                (Finset.univ \ coordinates) ≤
            ((wz1HypergraphFiber
              transformedEncoded coordinates edge).card :
              ENNReal) := by
    intro edge hedge coordinates
    rcases Finset.mem_image.mp (himage ▸ hedge) with
      ⟨source, hsource, rfl⟩
    rw [hfiber source coordinates,
      Finset.card_image_of_injective _
        encodedEquiv.injective,
      hvertexCard]
    exact hFiberBound source hsource coordinates
  exact
    ⟨htransformedNonempty,
      hsupportTransformed, hfiberTransformed⟩

/-- Exact density preservation for the Lemma 8.13 affine triple map. -/
lemma wz1Lemma8_13_density_under_bijection
    {F G₁ G₂ : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    {density : ENNReal}
    (hDensity :
      WZ1UniformTripleDensity density F G₁ G₂ H)
    (linear : Point2 ≃ₗ[ℝ] Point2)
    (translation : Point2) :
    WZ1UniformTripleDensity density
      (F.image (wz1ContragredientPoint linear))
      (G₁.image
        (wz1AffineEndpoint linear translation))
      (G₂.image
        (wz1AffineEndpoint linear translation))
      (H.image (wz1AffineTriple linear translation)) := by
  let firstEquiv : Point2 ≃ Point2 :=
    (contragredientEquiv linear).toEquiv
  let endpointEquiv : Point2 ≃ Point2 :=
    affineEndpointEquiv linear translation
  have hmain :=
    density_under_coordinate_equivalences
      hDensity firstEquiv endpointEquiv endpointEquiv
  have hfirst :
      ⇑firstEquiv =
        wz1ContragredientPoint linear := by
    funext point
    rfl
  have hendpoint :
      ⇑endpointEquiv =
        wz1AffineEndpoint linear translation := by
    funext point
    rfl
  convert hmain using 1
  · rw [← hfirst]
  · rw [← hendpoint]
  · rw [← hendpoint]
  · apply Finset.image_congr
    intro edge _
    simp [hfirst, hendpoint, wz1AffineTriple]

end Kakeya.Assouad
