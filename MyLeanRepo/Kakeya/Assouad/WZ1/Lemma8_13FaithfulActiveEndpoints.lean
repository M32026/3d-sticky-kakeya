import MyLeanRepo.Kakeya.Assouad.WZ1.InducedTripleRefinement

/-!
# Active endpoint classes at the faithful Lemma 8.13 final graph

Replacing only the two endpoint ambient classes by the active endpoint
projections preserves the original uniform density constant.  The first
ambient class is deliberately left unchanged because it is the actual
representative class consumed by Kaufman's theorem.
-/

namespace Kakeya.Assouad

open scoped ENNReal

/-- Uniform triple density survives replacement of the endpoint ambient
classes by the active endpoint projections of the same graph. -/
lemma uniform_density_on_active_endpoints
    {c : ENNReal}
    {F G₁ G₂ : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    (hDensity : WZ1UniformTripleDensity c F G₁ G₂ H) :
    WZ1UniformTripleDensity c
      F
      (wz1ActiveTripleProjection H 1)
      (wz1ActiveTripleProjection H 2)
      H := by
  let activeClasses : Fin 3 → DiscreteSet 2 :=
    fun i =>
      match i with
      | 0 => F
      | 1 => wz1ActiveTripleProjection H 1
      | 2 => wz1ActiveTripleProjection H 2
  have hactiveSubset :
      ∀ i,
        activeClasses i ⊆
          wz1TripleVertexClasses F G₁ G₂ i := by
    intro i
    fin_cases i
    · exact Finset.Subset.rfl
    · exact active_triple_projection_subset hDensity 1
    · exact active_triple_projection_subset hDensity 2
  refine ⟨hDensity.1, ?_⟩
  refine ⟨?_, ?_⟩
  · intro encodedEdge hencodedEdge i
    rcases Finset.mem_image.mp hencodedEdge with
      ⟨edge, hedge, rfl⟩
    fin_cases i
    · exact
        hDensity.2.1
          (wz1TripleCoordinate edge)
          (Finset.mem_image.mpr ⟨edge, hedge, rfl⟩)
          0
    · exact Finset.mem_image.mpr ⟨edge, hedge, rfl⟩
    · exact Finset.mem_image.mpr ⟨edge, hedge, rfl⟩
  · intro encodedEdge hencodedEdge coordinates
    have hold :=
      hDensity.2.2 encodedEdge hencodedEdge coordinates
    have hproduct :
        wz1VertexCardProduct activeClasses
            (Finset.univ \ coordinates) ≤
          wz1VertexCardProduct
            (wz1TripleVertexClasses F G₁ G₂)
            (Finset.univ \ coordinates) := by
      simp only [wz1VertexCardProduct]
      apply Finset.prod_le_prod'
      intro i hi
      simpa using
        (show
          ((activeClasses i).card : ENNReal) ≤
            ((wz1TripleVertexClasses F G₁ G₂ i).card :
              ENNReal) by
          exact_mod_cast
            Finset.card_le_card (hactiveSubset i))
    have hscaled :
        c *
            wz1VertexCardProduct activeClasses
              (Finset.univ \ coordinates) ≤
          c *
            wz1VertexCardProduct
              (wz1TripleVertexClasses F G₁ G₂)
              (Finset.univ \ coordinates) :=
      mul_le_mul_left' hproduct c
    have hclasses :
        wz1TripleVertexClasses
            F
            (wz1ActiveTripleProjection H 1)
            (wz1ActiveTripleProjection H 2) =
          activeClasses := by
      funext i
      fin_cases i <;> rfl
    rw [hclasses]
    exact hscaled.trans hold

end Kakeya.Assouad
