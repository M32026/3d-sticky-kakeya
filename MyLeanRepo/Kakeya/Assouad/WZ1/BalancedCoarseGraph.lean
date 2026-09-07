import MyLeanRepo.Kakeya.Assouad.WZ1.AnisotropicSelectedImageFrostman
import MyLeanRepo.Kakeya.Assouad.WZ1.HypergraphRefinementHelpers

/-!
# Balanced coarse graph for the wide branch

Three anisotropic Frostman rescalings assign retained source vertices to
balanced coarse cells.  This module pushes a supported actual graph to those
cells, controls the collapse multiplicity, and applies the tripartite
refinement lemma to recover uniform density on the coarse graph.

Every refined coarse edge retains an actual source-edge witness together with
coordinatewise closeness to its affine image.  No equality of dot-difference
values is asserted after snapping to coarse cells.
-/

namespace Kakeya.Assouad

open scoped ENNReal

/-- Apply three vertex assignments coordinatewise to a tripartite edge. -/
def wz1CoordinatewiseTripleMap
    (first second third : Point2 → Point2)
    (edge : Point2 × Point2 × Point2) :
    Point2 × Point2 × Point2 :=
  (first edge.1, second edge.2.1, third edge.2.2)

/--
The graph-theoretic bridge from three balanced anisotropic rescalings to a
uniform graph on their coarse vertex sets.

The source-cardinality bound records the complete loss caused by snapping:
each coarse triple has at most
`(2 m_F) (2 m_G₁) (2 m_G₂)` actual preimages.
-/
theorem anisotropic_balanced_coarse_graph_refinement
    {E_F E_G₁ E_G₂ : DiscreteSet 2}
    {phi_F phi_G₁ phi_G₂ : Point2 ≃ᵃ[ℝ] Point2}
    {delta w epsilon_r : ℝ}
    {C_F C_G₁ C_G₂ : ENNReal}
    (rescaleF :
      WZ1AnisotropicFrostmanRescalingData
        E_F phi_F delta w epsilon_r C_F)
    (rescaleG₁ :
      WZ1AnisotropicFrostmanRescalingData
        E_G₁ phi_G₁ delta w epsilon_r C_G₁)
    (rescaleG₂ :
      WZ1AnisotropicFrostmanRescalingData
        E_G₂ phi_G₂ delta w epsilon_r C_G₂)
    {H : Finset (Point2 × Point2 × Point2)}
    (hsupport :
      ∀ edge ∈ H,
        edge.1 ∈ rescaleF.selected ∧
        edge.2.1 ∈ rescaleG₁.selected ∧
        edge.2.2 ∈ rescaleG₂.selected)
    (hH : H.Nonempty)
    (hRefine : WZ1TripartiteHypergraphRefinementStatement) :
    ∃ coarseH refinedH : Finset (Point2 × Point2 × Point2),
      coarseH =
        H.image
          (wz1CoordinatewiseTripleMap
            rescaleF.assignment
            rescaleG₁.assignment
            rescaleG₂.assignment) ∧
      H.card ≤
        ((2 * rescaleF.fiberMultiplicity) *
          (2 * rescaleG₁.fiberMultiplicity) *
          (2 * rescaleG₂.fiberMultiplicity)) *
          coarseH.card ∧
      refinedH ⊆ coarseH ∧
      (1 - (1 / 2 : ENNReal)) * (coarseH.card : ENNReal) ≤
        (refinedH.card : ENNReal) ∧
      WZ1UniformTripleDensity
        (((1 / 2 : ENNReal) / (2 : ENNReal) ^ (3 : ℕ)) *
          ((coarseH.card : ENNReal) /
            (rescaleF.coarse.enncard *
              rescaleG₁.coarse.enncard *
              rescaleG₂.coarse.enncard)))
        rescaleF.coarse rescaleG₁.coarse rescaleG₂.coarse refinedH ∧
      ∀ edge ∈ refinedH,
        ∃ source ∈ H,
          source.1 ∈ rescaleF.selected ∧
          source.2.1 ∈ rescaleG₁.selected ∧
          source.2.2 ∈ rescaleG₂.selected ∧
          wz1CoordinatewiseTripleMap
              rescaleF.assignment
              rescaleG₁.assignment
              rescaleG₂.assignment source = edge ∧
          dist (phi_F source.1) edge.1 ≤ delta / w ∧
          dist (phi_G₁ source.2.1) edge.2.1 ≤ delta / w ∧
          dist (phi_G₂ source.2.2) edge.2.2 ≤ delta / w := by
  classical
  let tripleMap :=
    wz1CoordinatewiseTripleMap
      rescaleF.assignment
      rescaleG₁.assignment
      rescaleG₂.assignment
  let coarseH := H.image tripleMap
  let capF := 2 * rescaleF.fiberMultiplicity
  let capG₁ := 2 * rescaleG₁.fiberMultiplicity
  let capG₂ := 2 * rescaleG₂.fiberMultiplicity
  let cap := capF * capG₁ * capG₂
  have hcoarseSupport :
      ∀ edge ∈ coarseH,
        edge.1 ∈ rescaleF.coarse ∧
        edge.2.1 ∈ rescaleG₁.coarse ∧
        edge.2.2 ∈ rescaleG₂.coarse := by
    intro edge hedge
    rcases Finset.mem_image.mp hedge with
      ⟨source, hsource, rfl⟩
    have hsourceSupport := hsupport source hsource
    exact
      ⟨rescaleF.assignment_mem source.1 hsourceSupport.1,
        rescaleG₁.assignment_mem source.2.1 hsourceSupport.2.1,
        rescaleG₂.assignment_mem source.2.2 hsourceSupport.2.2⟩
  have hcoarseNonempty : coarseH.Nonempty :=
    Finset.Nonempty.image hH tripleMap
  have hfiber :
      ∀ edge ∈ coarseH,
        (H.filter fun source => tripleMap source = edge).card ≤ cap := by
    intro edge hedge
    rcases Finset.mem_image.mp hedge with
      ⟨sourceEdge, hsourceEdge, hedgeEq⟩
    have hedgeSupport := hcoarseSupport edge hedge
    let firstFiber :=
      rescaleF.selected.filter
        (fun point => rescaleF.assignment point = edge.1)
    let secondFiber :=
      rescaleG₁.selected.filter
        (fun point => rescaleG₁.assignment point = edge.2.1)
    let thirdFiber :=
      rescaleG₂.selected.filter
        (fun point => rescaleG₂.assignment point = edge.2.2)
    have hsubset :
        H.filter (fun source => tripleMap source = edge) ⊆
          firstFiber ×ˢ secondFiber ×ˢ thirdFiber := by
      intro source hsource
      have hsourceH := (Finset.mem_filter.mp hsource).1
      have hmap := (Finset.mem_filter.mp hsource).2
      have hsourceSupport := hsupport source hsourceH
      have hfirst :
          rescaleF.assignment source.1 = edge.1 := by
        exact congrArg Prod.fst hmap
      have hsecond :
          rescaleG₁.assignment source.2.1 = edge.2.1 := by
        exact congrArg (Prod.fst ∘ Prod.snd) hmap
      have hthird :
          rescaleG₂.assignment source.2.2 = edge.2.2 := by
        exact congrArg (Prod.snd ∘ Prod.snd) hmap
      simp only [Finset.mem_product]
      exact
        ⟨Finset.mem_filter.mpr ⟨hsourceSupport.1, hfirst⟩,
          Finset.mem_filter.mpr ⟨hsourceSupport.2.1, hsecond⟩,
          Finset.mem_filter.mpr ⟨hsourceSupport.2.2, hthird⟩⟩
    have hfirstCard : firstFiber.card ≤ capF := by
      exact
        (rescaleF.fiber_comparable edge.1 hedgeSupport.1).2
    have hsecondCard : secondFiber.card ≤ capG₁ := by
      exact
        (rescaleG₁.fiber_comparable edge.2.1 hedgeSupport.2.1).2
    have hthirdCard : thirdFiber.card ≤ capG₂ := by
      exact
        (rescaleG₂.fiber_comparable edge.2.2 hedgeSupport.2.2).2
    calc
      (H.filter fun source => tripleMap source = edge).card ≤
          (firstFiber ×ˢ secondFiber ×ˢ thirdFiber).card :=
        Finset.card_le_card hsubset
      _ = firstFiber.card * secondFiber.card * thirdFiber.card := by
        simp [Nat.mul_assoc]
      _ ≤ capF * capG₁ * capG₂ := by
        exact Nat.mul_le_mul
          (Nat.mul_le_mul hfirstCard hsecondCard) hthirdCard
      _ = cap := rfl
  have hsourceCard :
      H.card ≤ cap * coarseH.card := by
    exact Finset.card_le_mul_card_image H cap hfiber
  rcases
      tripartite_refinement_apply
        (hRef := hRefine)
        hcoarseSupport hcoarseNonempty
        (epsilon := (1 / 2 : ENNReal))
        (by norm_num) (by norm_num)
    with
      ⟨refinedH, hrefinedSubset, hrefinedCard, hrefinedUniform⟩
  refine
    ⟨coarseH, refinedH, rfl, ?_, hrefinedSubset,
      hrefinedCard, hrefinedUniform, ?_⟩
  · simpa [cap, capF, capG₁, capG₂] using hsourceCard
  · intro edge hedge
    have hedgeCoarse := hrefinedSubset hedge
    rcases Finset.mem_image.mp hedgeCoarse with
      ⟨source, hsource, hsourceMap⟩
    have hsourceSupport := hsupport source hsource
    refine
      ⟨source, hsource,
        hsourceSupport.1, hsourceSupport.2.1,
        hsourceSupport.2.2, hsourceMap, ?_, ?_, ?_⟩
    · rw [← hsourceMap]
      exact rescaleF.assignment_close source.1 hsourceSupport.1
    · rw [← hsourceMap]
      exact
        rescaleG₁.assignment_close
          source.2.1 hsourceSupport.2.1
    · rw [← hsourceMap]
      exact
        rescaleG₂.assignment_close
          source.2.2 hsourceSupport.2.2

/--
If the actual selected graph already has uniform density `c`, then the
refined coarse graph has uniform density `c / 128`.

The loss is `8` from the three balanced assignment fibers and `16` from the
tripartite refinement at parameter `1/2`.
-/
theorem anisotropic_balanced_coarse_graph_uniform
    {E_F E_G₁ E_G₂ : DiscreteSet 2}
    {phi_F phi_G₁ phi_G₂ : Point2 ≃ᵃ[ℝ] Point2}
    {delta w epsilon_r : ℝ}
    {C_F C_G₁ C_G₂ c : ENNReal}
    (rescaleF :
      WZ1AnisotropicFrostmanRescalingData
        E_F phi_F delta w epsilon_r C_F)
    (rescaleG₁ :
      WZ1AnisotropicFrostmanRescalingData
        E_G₁ phi_G₁ delta w epsilon_r C_G₁)
    (rescaleG₂ :
      WZ1AnisotropicFrostmanRescalingData
        E_G₂ phi_G₂ delta w epsilon_r C_G₂)
    {H : Finset (Point2 × Point2 × Point2)}
    (hsupport :
      ∀ edge ∈ H,
        edge.1 ∈ rescaleF.selected ∧
        edge.2.1 ∈ rescaleG₁.selected ∧
        edge.2.2 ∈ rescaleG₂.selected)
    (hDensity :
      WZ1UniformTripleDensity c
        rescaleF.selected rescaleG₁.selected
        rescaleG₂.selected H)
    (hRefine : WZ1TripartiteHypergraphRefinementStatement) :
    ∃ coarseH refinedH : Finset (Point2 × Point2 × Point2),
      coarseH =
        H.image
          (wz1CoordinatewiseTripleMap
            rescaleF.assignment
            rescaleG₁.assignment
            rescaleG₂.assignment) ∧
      refinedH ⊆ coarseH ∧
      WZ1UniformTripleDensity (c / 128)
        rescaleF.coarse rescaleG₁.coarse rescaleG₂.coarse
        refinedH ∧
      ∀ edge ∈ refinedH,
        ∃ source ∈ H,
          source.1 ∈ rescaleF.selected ∧
          source.2.1 ∈ rescaleG₁.selected ∧
          source.2.2 ∈ rescaleG₂.selected ∧
          wz1CoordinatewiseTripleMap
              rescaleF.assignment
              rescaleG₁.assignment
              rescaleG₂.assignment source = edge ∧
          dist (phi_F source.1) edge.1 ≤ delta / w ∧
          dist (phi_G₁ source.2.1) edge.2.1 ≤ delta / w ∧
          dist (phi_G₂ source.2.2) edge.2.2 ≤ delta / w := by
  classical
  rcases
      anisotropic_balanced_coarse_graph_refinement
        rescaleF rescaleG₁ rescaleG₂
        hsupport hDensity.1 hRefine
    with
      ⟨coarseH, refinedH, hcoarseH, hcollapseNat,
        hrefinedSubset, _hrefinedCard, hrefinedDensity,
        hwitness⟩
  let M : ENNReal :=
    (rescaleF.fiberMultiplicity : ENNReal) *
      (rescaleG₁.fiberMultiplicity : ENNReal) *
      (rescaleG₂.fiberMultiplicity : ENNReal)
  let Q : ENNReal :=
    rescaleF.coarse.enncard *
      rescaleG₁.coarse.enncard *
      rescaleG₂.coarse.enncard
  let S : ENNReal :=
    rescaleF.selected.enncard *
      rescaleG₁.selected.enncard *
      rescaleG₂.selected.enncard
  have hMQ : M * Q ≤ S := by
    calc
      M * Q =
          ((rescaleF.fiberMultiplicity : ENNReal) *
            rescaleF.coarse.enncard) *
          ((rescaleG₁.fiberMultiplicity : ENNReal) *
            rescaleG₁.coarse.enncard) *
          ((rescaleG₂.fiberMultiplicity : ENNReal) *
            rescaleG₂.coarse.enncard) := by
        simp only [M, Q]
        ring
      _ ≤ S := by
        simp only [S]
        gcongr
        · exact
            anisotropic_coarse_card_weighted_le_selected rescaleF
        · exact
            anisotropic_coarse_card_weighted_le_selected rescaleG₁
        · exact
            anisotropic_coarse_card_weighted_le_selected rescaleG₂
  rcases hDensity.1 with ⟨sourceEdge, hsourceEdge⟩
  have hsourceEncoded :
      wz1TripleCoordinate sourceEdge ∈ wz1EncodeTriples H :=
    Finset.mem_image.mpr ⟨sourceEdge, hsourceEdge, rfl⟩
  have htotalRaw :=
    hDensity.2.2
      (wz1TripleCoordinate sourceEdge)
      hsourceEncoded
      (∅ : Finset (Fin 3))
  have hvertexProduct :
      wz1VertexCardProduct
          (wz1TripleVertexClasses
            rescaleF.selected rescaleG₁.selected
            rescaleG₂.selected)
          (Finset.univ \ (∅ : Finset (Fin 3))) =
        S := by
    have h_univ :
        (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by
      decide
    rw [Finset.sdiff_empty, h_univ]
    simp [wz1VertexCardProduct, wz1TripleVertexClasses,
      Finset.prod_insert, DiscreteSet.enncard, S]
    ring
  have hfiberAll :
      wz1HypergraphFiber
          (wz1EncodeTriples H)
          (∅ : Finset (Fin 3))
          (wz1TripleCoordinate sourceEdge) =
        wz1EncodeTriples H := by
    simp [wz1HypergraphFiber]
  have htotal : c * S ≤ (H.card : ENNReal) := by
    rw [hvertexProduct, hfiberAll] at htotalRaw
    simpa [wz1HypergraphEncodeTriples_card] using htotalRaw
  have hcollapse :
      (H.card : ENNReal) ≤
        8 * M * (coarseH.card : ENNReal) := by
    have hcast :
        (H.card : ENNReal) ≤
          (((2 * rescaleF.fiberMultiplicity) *
              (2 * rescaleG₁.fiberMultiplicity) *
              (2 * rescaleG₂.fiberMultiplicity) *
              coarseH.card : ℕ) : ENNReal) := by
      exact_mod_cast hcollapseNat
    calc
      (H.card : ENNReal) ≤
          (((2 * rescaleF.fiberMultiplicity) *
              (2 * rescaleG₁.fiberMultiplicity) *
              (2 * rescaleG₂.fiberMultiplicity) *
              coarseH.card : ℕ) : ENNReal) :=
        hcast
      _ = 8 * M * (coarseH.card : ENNReal) := by
        simp only [Nat.cast_mul, Nat.cast_ofNat, M]
        ring
  have hMne : M ≠ 0 := by
    simp [M,
      Nat.ne_of_gt rescaleF.fiberMultiplicity_pos,
      Nat.ne_of_gt rescaleG₁.fiberMultiplicity_pos,
      Nat.ne_of_gt rescaleG₂.fiberMultiplicity_pos]
  have hMtop : M ≠ ⊤ := by
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.natCast_ne_top rescaleF.fiberMultiplicity)
        (ENNReal.natCast_ne_top rescaleG₁.fiberMultiplicity))
      (ENNReal.natCast_ne_top rescaleG₂.fiberMultiplicity)
  have hcancelled : c * Q ≤ 8 * (coarseH.card : ENNReal) := by
    apply (ENNReal.mul_le_mul_iff_left hMne hMtop).mp
    calc
      c * Q * M = c * (M * Q) := by ring
      _ ≤ c * S := by gcongr
      _ ≤ (H.card : ENNReal) := htotal
      _ ≤ 8 * M * (coarseH.card : ENNReal) := hcollapse
      _ = (8 * (coarseH.card : ENNReal)) * M := by ring
  have hQne : Q ≠ 0 := by
    simp [Q, DiscreteSet.enncard,
      Finset.card_ne_zero.mpr rescaleF.coarse_nonempty,
      Finset.card_ne_zero.mpr rescaleG₁.coarse_nonempty,
      Finset.card_ne_zero.mpr rescaleG₂.coarse_nonempty]
  have hQtop : Q ≠ ⊤ := by
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top
        (ENNReal.natCast_ne_top rescaleF.coarse.card)
        (ENNReal.natCast_ne_top rescaleG₁.coarse.card))
      (ENNReal.natCast_ne_top rescaleG₂.coarse.card)
  have hratio :
      c ≤ 8 * ((coarseH.card : ENNReal) / Q) := by
    have hratio' :
        c ≤ (8 * (coarseH.card : ENNReal)) / Q :=
      (ENNReal.le_div_iff_mul_le
        (Or.inl hQne) (Or.inl hQtop)).2 hcancelled
    simpa [div_eq_mul_inv, mul_assoc] using hratio'
  have hdensityLower :
      c / 128 ≤
        ((1 / 2 : ENNReal) / (2 : ENNReal) ^ (3 : ℕ)) *
          ((coarseH.card : ENNReal) / Q) := by
    calc
      c / 128 ≤
          (8 * ((coarseH.card : ENNReal) / Q)) / 128 := by
        gcongr
      _ =
          ((1 / 2 : ENNReal) / (2 : ENNReal) ^ (3 : ℕ)) *
            ((coarseH.card : ENNReal) / Q) := by
        have hconstant :
            (8 : ENNReal) / 128 =
              (1 / 2 : ENNReal) /
                (2 : ENNReal) ^ (3 : ℕ) := by
          have hleft : (8 : ENNReal) / 128 ≠ ⊤ := by
            rw [div_eq_mul_inv]
            exact ENNReal.mul_ne_top (by norm_num) (by norm_num)
          have hright :
              (1 / 2 : ENNReal) /
                  (2 : ENNReal) ^ (3 : ℕ) ≠ ⊤ := by
            simp only [div_eq_mul_inv]
            exact ENNReal.mul_ne_top
              (ENNReal.mul_ne_top
                (by norm_num) (by norm_num))
              (by norm_num)
          apply
            (ENNReal.toReal_eq_toReal_iff' hleft hright).mp
          norm_num
        rw [div_eq_mul_inv]
        calc
          8 * ((coarseH.card : ENNReal) / Q) * 128⁻¹ =
              (8 / 128 : ENNReal) *
                ((coarseH.card : ENNReal) / Q) := by
            rw [div_eq_mul_inv]
            rw [mul_assoc 8
              ((coarseH.card : ENNReal) * Q⁻¹) 128⁻¹]
            rw [mul_comm
              ((coarseH.card : ENNReal) * Q⁻¹) 128⁻¹]
            rw [← mul_assoc 8 128⁻¹
              ((coarseH.card : ENNReal) * Q⁻¹)]
            rfl
          _ =
              ((1 / 2 : ENNReal) /
                  (2 : ENNReal) ^ (3 : ℕ)) *
                ((coarseH.card : ENNReal) / Q) := by
            rw [hconstant]
  have hrefinedDensity' :
      WZ1UniformTripleDensity (c / 128)
        rescaleF.coarse rescaleG₁.coarse rescaleG₂.coarse
        refinedH := by
    apply hrefinedDensity.mono
    simpa [Q] using hdensityLower
  exact
    ⟨coarseH, refinedH, hcoarseH, hrefinedSubset,
      hrefinedDensity', hwitness⟩

end Kakeya.Assouad
