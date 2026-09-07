import MyLeanRepo.Kakeya.Assouad.WZ1.HypergraphRefinementHelpers
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma40Absorption
import MyLeanRepo.Kakeya.Assouad.WZ1.ThinTubesLargeDotProduct
import MyLeanRepo.Kakeya.Assouad.WZ1.WellSeparatedRestriction

/-!
# Induced tripartite refinement for WZ1 Proposition 8.9

This is the graph-theoretic operation used after each two-ends selection in
the paper: restrict one active coordinate class, then apply Lemma 8.1 to
recover uniform triple density.
-/

namespace Kakeya.Assouad

open scoped ENNReal

/-- Every active coordinate lies in its prescribed ambient vertex class. -/
lemma active_triple_projection_subset
    {c : ENNReal}
    {F G₁ G₂ : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    (hDensity : WZ1UniformTripleDensity c F G₁ G₂ H)
    (i : Fin 3) :
    wz1ActiveTripleProjection H i ⊆
      wz1TripleVertexClasses F G₁ G₂ i := by
  intro point hpoint
  rcases Finset.mem_image.mp hpoint with
    ⟨edge, hedge, rfl⟩
  exact
    hDensity.2.1
      (wz1TripleCoordinate edge)
      (Finset.mem_image.mpr ⟨edge, hedge, rfl⟩)
      i

/-- Every active coordinate projection of a nonempty graph is nonempty. -/
lemma active_triple_projection_nonempty
    {c : ENNReal}
    {F G₁ G₂ : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    (hDensity : WZ1UniformTripleDensity c F G₁ G₂ H)
    (i : Fin 3) :
    (wz1ActiveTripleProjection H i).Nonempty := by
  rcases hDensity.1 with ⟨edge, hedge⟩
  exact
    ⟨wz1TripleCoordinate edge i,
      Finset.mem_image.mpr ⟨edge, hedge, rfl⟩⟩

/--
Replacing all ambient vertex classes by the actual coordinate projections
preserves the same uniform density constant.
-/
lemma uniform_density_on_active_projections
    {c : ENNReal}
    {F G₁ G₂ : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    (hDensity : WZ1UniformTripleDensity c F G₁ G₂ H) :
    WZ1UniformTripleDensity c
      (wz1ActiveTripleProjection H 0)
      (wz1ActiveTripleProjection H 1)
      (wz1ActiveTripleProjection H 2)
      H := by
  let activeClasses : Fin 3 → DiscreteSet 2 :=
    fun i => wz1ActiveTripleProjection H i
  have hactiveClasses :
      ∀ i,
        activeClasses i =
          wz1ActiveTripleProjection H i := by
    intro i
    rfl
  have hactiveSubset :
      ∀ i,
        activeClasses i ⊆
          wz1TripleVertexClasses F G₁ G₂ i := by
    intro i
    exact active_triple_projection_subset hDensity i
  refine ⟨hDensity.1, ?_⟩
  refine ⟨?_, ?_⟩
  · intro encodedEdge hencodedEdge i
    rcases Finset.mem_image.mp hencodedEdge with
      ⟨edge, hedge, rfl⟩
    fin_cases i <;>
      exact Finset.mem_image.mpr
        ⟨edge, hedge, rfl⟩
  · intro encodedEdge hencodedEdge coordinates
    have hold :=
      hDensity.2.2
        encodedEdge hencodedEdge coordinates
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
    have hgoal :
        c *
            wz1VertexCardProduct
              (wz1TripleVertexClasses
                (wz1ActiveTripleProjection H 0)
                (wz1ActiveTripleProjection H 1)
                (wz1ActiveTripleProjection H 2))
              (Finset.univ \ coordinates) ≤
          ((wz1HypergraphFiber
            (wz1EncodeTriples H)
            coordinates encodedEdge).card : ENNReal) := by
      have hclasses :
          wz1TripleVertexClasses
              (wz1ActiveTripleProjection H 0)
              (wz1ActiveTripleProjection H 1)
              (wz1ActiveTripleProjection H 2) =
            activeClasses := by
        funext i
        fin_cases i <;>
          rfl
      rw [hclasses]
      exact hscaled.trans hold
    exact hgoal

/--
Every active coordinate projection of a uniformly dense tripartite graph
retains at least the density fraction of its ambient vertex class.
-/
lemma active_triple_projection_card_lower
    {c : ENNReal}
    {F G₁ G₂ : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    (hDensity : WZ1UniformTripleDensity c F G₁ G₂ H)
    (i : Fin 3) :
    c * (wz1TripleVertexClasses F G₁ G₂ i).enncard ≤
      (wz1ActiveTripleProjection H i).enncard := by
  classical
  rcases hDensity.1 with ⟨sourceEdge, hsourceEdge⟩
  let encoded := wz1EncodeTriples H
  let classes := wz1TripleVertexClasses F G₁ G₂
  let encodedEdge := wz1TripleCoordinate sourceEdge
  let fixedCoordinates : Finset (Fin 3) := Finset.univ.erase i
  let fiber :=
    wz1HypergraphFiber encoded fixedCoordinates encodedEdge
  have hencodedEdge : encodedEdge ∈ encoded :=
    Finset.mem_image.mpr ⟨sourceEdge, hsourceEdge, rfl⟩
  have hcomplement :
      (Finset.univ : Finset (Fin 3)) \ fixedCoordinates = {i} := by
    ext index
    simp [fixedCoordinates]
  have hproduct :
      wz1VertexCardProduct classes ({i} : Finset (Fin 3)) =
        (classes i).enncard := by
    simp [wz1VertexCardProduct, DiscreteSet.enncard]
  have hfiberLower :
      c * (classes i).enncard ≤ (fiber.card : ENNReal) := by
    have h :=
      hDensity.2.2 encodedEdge hencodedEdge fixedCoordinates
    rw [hcomplement, hproduct] at h
    exact h
  let coordinate : (Fin 3 → Point2) → Point2 :=
    fun edge => edge i
  have hcoordinateMaps :
      fiber.image coordinate ⊆ wz1ActiveTripleProjection H i := by
    intro point hpoint
    rcases Finset.mem_image.mp hpoint with
      ⟨encodedOther, hencodedOther, rfl⟩
    have hotherInEncoded : encodedOther ∈ encoded :=
      (Finset.mem_filter.mp hencodedOther).1
    rcases Finset.mem_image.mp hotherInEncoded with
      ⟨other, hother, hotherEq⟩
    exact Finset.mem_image.mpr
      ⟨other, hother, congr_fun hotherEq i⟩
  have hcoordinateInjective :
      Set.InjOn coordinate (fiber : Set (Fin 3 → Point2)) := by
    intro first hfirst second hsecond hequal
    apply funext
    intro index
    by_cases hindex : index = i
    · simpa [coordinate, hindex] using hequal
    · have hfirstFixed :=
        (Finset.mem_filter.mp hfirst).2 index
          (by simp [fixedCoordinates, hindex])
      have hsecondFixed :=
        (Finset.mem_filter.mp hsecond).2 index
          (by simp [fixedCoordinates, hindex])
      exact hfirstFixed.trans hsecondFixed.symm
  have hfiberCard :
      fiber.card = (fiber.image coordinate).card :=
    (Finset.card_image_of_injOn hcoordinateInjective).symm
  calc
    c * (wz1TripleVertexClasses F G₁ G₂ i).enncard
        = c * (classes i).enncard := rfl
    _ ≤ (fiber.card : ENNReal) := hfiberLower
    _ = ((fiber.image coordinate).card : ENNReal) := by
      exact_mod_cast hfiberCard
    _ ≤ (wz1ActiveTripleProjection H i).enncard := by
      simpa [DiscreteSet.enncard] using
        (show
          ((fiber.image coordinate).card : ENNReal) ≤
            ((wz1ActiveTripleProjection H i).card : ENNReal) by
          exact_mod_cast Finset.card_le_card hcoordinateMaps)

/--
Restrict a uniformly dense graph to an active `F` subset and recover uniform
density.  The refined density is at least `c / 16`.
-/
lemma restrict_zeroth_vertex_and_refine
    {c : ENNReal}
    {F G₁ G₂ selected : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    (hDensity : WZ1UniformTripleDensity c F G₁ G₂ H)
    (_hselected : selected ⊆ F)
    (hactive :
      ∀ vertex ∈ selected, ∃ edge ∈ H, edge.1 = vertex)
    (hselectedNonempty : selected.Nonempty)
    (hRefine : WZ1TripartiteHypergraphRefinementStatement) :
    ∃ refined : Finset (Point2 × Point2 × Point2),
      refined ⊆ H ∧
      refined.Nonempty ∧
      WZ1UniformTripleDensity (c / 16) selected G₁ G₂ refined := by
  classical
  let induced :=
    H.filter fun edge => edge.1 ∈ selected
  have hinduced : induced ⊆ H :=
    Finset.filter_subset _ _
  have hcard :
      c * selected.enncard * G₁.enncard * G₂.enncard ≤
        (induced.card : ENNReal) := by
    simpa [induced, DiscreteSet.enncard] using
      restrict_f_card_lower hDensity hactive
  have hinducedNonempty : induced.Nonempty := by
    rcases hselectedNonempty with ⟨vertex, hvertex⟩
    rcases hactive vertex hvertex with ⟨edge, hedge, hedgeVertex⟩
    exact
      ⟨edge, Finset.mem_filter.mpr
        ⟨hedge, by simpa [hedgeVertex] using hvertex⟩⟩
  have hsupport :
      ∀ edge ∈ induced,
        edge.1 ∈ selected ∧ edge.2.1 ∈ G₁ ∧ edge.2.2 ∈ G₂ := by
    intro edge hedge
    have hedgeH : edge ∈ H := hinduced hedge
    have hsupported :=
      density_vertex_containment hDensity edge hedgeH
    exact
      ⟨(Finset.mem_filter.mp hedge).2,
        hsupported.2.1, hsupported.2.2⟩
  rcases
      tripartite_refinement_apply
        (hRef := hRefine)
        hsupport hinducedNonempty
        (epsilon := (1 / 2 : ENNReal))
        (by norm_num) (by norm_num)
    with
      ⟨refined, hrefined, _hretained, hUniform⟩
  let denominator :=
    selected.enncard * G₁.enncard * G₂.enncard
  have hdenominator : denominator ≠ 0 := by
    have hG₁ : G₁.Nonempty := by
      rcases hDensity.1 with ⟨edge, hedge⟩
      exact
        ⟨edge.2.1,
          (density_vertex_containment hDensity edge hedge).2.1⟩
    have hG₂ : G₂.Nonempty := by
      rcases hDensity.1 with ⟨edge, hedge⟩
      exact
        ⟨edge.2.2,
          (density_vertex_containment hDensity edge hedge).2.2⟩
    simp [denominator, DiscreteSet.enncard,
      Finset.card_ne_zero.mpr hselectedNonempty,
      Finset.card_ne_zero.mpr hG₁,
      Finset.card_ne_zero.mpr hG₂]
  have hdensityLower :
      c / 16 ≤
        ((1 / 2 : ENNReal) / (2 : ENNReal) ^ (3 : ℕ)) *
          ((induced.card : ENNReal) / denominator) := by
    have hratio :
        c ≤ (induced.card : ENNReal) / denominator := by
      rw [ENNReal.le_div_iff_mul_le
        (Or.inl hdenominator)
        (Or.inr (by simp))]
      simpa [denominator, mul_assoc] using hcard
    have hconstant :
        (1 / 2 : ENNReal) / (2 : ENNReal) ^ (3 : ℕ) =
          1 / 16 := by
      have hpow : (2 : ENNReal) ^ (3 : ℕ) = 8 := by norm_num
      rw [hpow, div_eq_mul_inv]
      rw [show (1 / 2 : ENNReal) = (2 : ENNReal)⁻¹ by
        simp [one_div]]
      rw [show (8 : ENNReal)⁻¹ = (1 / 8 : ENNReal) by
        simp [one_div]]
      have hmul :
          (2 : ENNReal)⁻¹ * (1 / 8 : ENNReal) =
            (16 : ENNReal)⁻¹ := by
        rw [show (1 / 8 : ENNReal) = (8 : ENNReal)⁻¹ by
          simp [one_div]]
        rw [← ENNReal.mul_inv] <;> norm_num
      rw [hmul]
      simp [one_div]
    rw [hconstant]
    simpa [div_eq_mul_inv, one_div, mul_comm] using
      mul_le_mul_right hratio (16 : ENNReal)⁻¹
  have hweakened :
      WZ1UniformTripleDensity (c / 16)
        selected G₁ G₂ refined :=
    uniform_triple_density_mono hUniform hdensityLower
  exact
    ⟨refined, hrefined.trans hinduced, hUniform.1, hweakened⟩

/--
Restrict a uniformly dense graph to an active `G₁` subset and recover uniform
density.  The refined density is at least `c / 16`.
-/
lemma restrict_first_endpoint_and_refine
    {c : ENNReal}
    {F G₁ G₂ selected : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    (hDensity : WZ1UniformTripleDensity c F G₁ G₂ H)
    (hselected : selected ⊆ G₁)
    (hactive :
      ∀ vertex ∈ selected, ∃ edge ∈ H, edge.2.1 = vertex)
    (hselectedNonempty : selected.Nonempty)
    (hRefine : WZ1TripartiteHypergraphRefinementStatement) :
    ∃ refined : Finset (Point2 × Point2 × Point2),
      refined ⊆ H ∧
      refined.Nonempty ∧
      WZ1UniformTripleDensity (c / 16) F selected G₂ refined := by
  classical
  let induced :=
    H.filter fun edge => edge.2.1 ∈ selected
  have hinduced : induced ⊆ H :=
    Finset.filter_subset _ _
  have hcard :
      c * F.enncard * selected.enncard * G₂.enncard ≤
        (induced.card : ENNReal) := by
    simpa [induced, DiscreteSet.enncard] using
      restrict_g1_card_lower hDensity hactive
  have hinducedNonempty : induced.Nonempty := by
    rcases hselectedNonempty with ⟨vertex, hvertex⟩
    rcases hactive vertex hvertex with ⟨edge, hedge, hedgeVertex⟩
    exact
      ⟨edge, Finset.mem_filter.mpr
        ⟨hedge, by simpa [hedgeVertex] using hvertex⟩⟩
  have hsupport :
      ∀ edge ∈ induced,
        edge.1 ∈ F ∧ edge.2.1 ∈ selected ∧ edge.2.2 ∈ G₂ := by
    intro edge hedge
    have hedgeH : edge ∈ H := hinduced hedge
    have hsupported :=
      density_vertex_containment hDensity edge hedgeH
    exact
      ⟨hsupported.1, (Finset.mem_filter.mp hedge).2,
        hsupported.2.2⟩
  rcases
      tripartite_refinement_apply
        (hRef := hRefine)
        hsupport hinducedNonempty
        (epsilon := (1 / 2 : ENNReal))
        (by norm_num) (by norm_num)
    with
      ⟨refined, hrefined, _hretained, hUniform⟩
  let denominator :=
    F.enncard * selected.enncard * G₂.enncard
  have hdenominator : denominator ≠ 0 := by
    have hF : F.Nonempty := by
      rcases hDensity.1 with ⟨edge, hedge⟩
      exact
        ⟨edge.1,
          (density_vertex_containment hDensity edge hedge).1⟩
    have hG₂ : G₂.Nonempty := by
      rcases hDensity.1 with ⟨edge, hedge⟩
      exact
        ⟨edge.2.2,
          (density_vertex_containment hDensity edge hedge).2.2⟩
    simp [denominator, DiscreteSet.enncard,
      Finset.card_ne_zero.mpr hF,
      Finset.card_ne_zero.mpr hselectedNonempty,
      Finset.card_ne_zero.mpr hG₂]
  have hdensityLower :
      c / 16 ≤
        ((1 / 2 : ENNReal) / (2 : ENNReal) ^ (3 : ℕ)) *
          ((induced.card : ENNReal) / denominator) := by
    have hratio :
        c ≤ (induced.card : ENNReal) / denominator := by
      rw [ENNReal.le_div_iff_mul_le
        (Or.inl hdenominator)
        (Or.inr (by simp [denominator]))]
      simpa [denominator, mul_assoc] using hcard
    have hconstant :
        (1 / 2 : ENNReal) / (2 : ENNReal) ^ (3 : ℕ) =
          1 / 16 := by
      have hpow : (2 : ENNReal) ^ (3 : ℕ) = 8 := by norm_num
      rw [hpow, div_eq_mul_inv]
      rw [show (1 / 2 : ENNReal) = (2 : ENNReal)⁻¹ by
        simp [one_div]]
      rw [show (8 : ENNReal)⁻¹ = (1 / 8 : ENNReal) by
        simp [one_div]]
      have hmul :
          (2 : ENNReal)⁻¹ * (1 / 8 : ENNReal) =
            (16 : ENNReal)⁻¹ := by
        rw [show (1 / 8 : ENNReal) = (8 : ENNReal)⁻¹ by
          simp [one_div]]
        rw [← ENNReal.mul_inv] <;> norm_num
      rw [hmul]
      simp [one_div]
    rw [hconstant]
    simpa [div_eq_mul_inv, one_div, mul_comm] using
      mul_le_mul_left' hratio (16 : ENNReal)⁻¹
  have hweakened :
      WZ1UniformTripleDensity (c / 16)
        F selected G₂ refined :=
    uniform_triple_density_mono hUniform hdensityLower
  exact
    ⟨refined, hrefined.trans hinduced, hUniform.1, hweakened⟩

/--
Symmetric restriction of the second endpoint class.
-/
lemma restrict_second_endpoint_and_refine
    {c : ENNReal}
    {F G₁ G₂ selected : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    (hDensity : WZ1UniformTripleDensity c F G₁ G₂ H)
    (hselected : selected ⊆ G₂)
    (hactive :
      ∀ vertex ∈ selected, ∃ edge ∈ H, edge.2.2 = vertex)
    (hselectedNonempty : selected.Nonempty)
    (hRefine : WZ1TripartiteHypergraphRefinementStatement) :
    ∃ refined : Finset (Point2 × Point2 × Point2),
      refined ⊆ H ∧
      refined.Nonempty ∧
      WZ1UniformTripleDensity (c / 16) F G₁ selected refined := by
  classical
  let induced :=
    H.filter fun edge => edge.2.2 ∈ selected
  have hinduced : induced ⊆ H :=
    Finset.filter_subset _ _
  have hcard :
      c * F.enncard * G₁.enncard * selected.enncard ≤
        (induced.card : ENNReal) := by
    simpa [induced, DiscreteSet.enncard] using
      restrict_g2_card_lower hDensity hactive
  have hinducedNonempty : induced.Nonempty := by
    rcases hselectedNonempty with ⟨vertex, hvertex⟩
    rcases hactive vertex hvertex with ⟨edge, hedge, hedgeVertex⟩
    exact
      ⟨edge, Finset.mem_filter.mpr
        ⟨hedge, by simpa [hedgeVertex] using hvertex⟩⟩
  have hsupport :
      ∀ edge ∈ induced,
        edge.1 ∈ F ∧ edge.2.1 ∈ G₁ ∧ edge.2.2 ∈ selected := by
    intro edge hedge
    have hedgeH : edge ∈ H := hinduced hedge
    have hsupported :=
      density_vertex_containment hDensity edge hedgeH
    exact
      ⟨hsupported.1, hsupported.2.1,
        (Finset.mem_filter.mp hedge).2⟩
  rcases
      tripartite_refinement_apply
        (hRef := hRefine)
        hsupport hinducedNonempty
        (epsilon := (1 / 2 : ENNReal))
        (by norm_num) (by norm_num)
    with
      ⟨refined, hrefined, _hretained, hUniform⟩
  let denominator :=
    F.enncard * G₁.enncard * selected.enncard
  have hdenominator : denominator ≠ 0 := by
    have hF : F.Nonempty := by
      rcases hDensity.1 with ⟨edge, hedge⟩
      exact
        ⟨edge.1,
          (density_vertex_containment hDensity edge hedge).1⟩
    have hG₁ : G₁.Nonempty := by
      rcases hDensity.1 with ⟨edge, hedge⟩
      exact
        ⟨edge.2.1,
          (density_vertex_containment hDensity edge hedge).2.1⟩
    simp [denominator, DiscreteSet.enncard,
      Finset.card_ne_zero.mpr hF,
      Finset.card_ne_zero.mpr hG₁,
      Finset.card_ne_zero.mpr hselectedNonempty]
  have hdensityLower :
      c / 16 ≤
        ((1 / 2 : ENNReal) / (2 : ENNReal) ^ (3 : ℕ)) *
          ((induced.card : ENNReal) / denominator) := by
    have hratio :
        c ≤ (induced.card : ENNReal) / denominator := by
      rw [ENNReal.le_div_iff_mul_le
        (Or.inl hdenominator)
        (Or.inr (by simp [denominator]))]
      simpa [denominator, mul_assoc] using hcard
    have hconstant :
        (1 / 2 : ENNReal) / (2 : ENNReal) ^ (3 : ℕ) =
          1 / 16 := by
      have hpow : (2 : ENNReal) ^ (3 : ℕ) = 8 := by norm_num
      rw [hpow, div_eq_mul_inv]
      rw [show (1 / 2 : ENNReal) = (2 : ENNReal)⁻¹ by
        simp [one_div]]
      rw [show (8 : ENNReal)⁻¹ = (1 / 8 : ENNReal) by
        simp [one_div]]
      have hmul :
          (2 : ENNReal)⁻¹ * (1 / 8 : ENNReal) =
            (16 : ENNReal)⁻¹ := by
        rw [show (1 / 8 : ENNReal) = (8 : ENNReal)⁻¹ by
          simp [one_div]]
        rw [← ENNReal.mul_inv] <;> norm_num
      rw [hmul]
      simp [one_div]
    rw [hconstant]
    simpa [div_eq_mul_inv, one_div, mul_comm] using
      mul_le_mul_left' hratio (16 : ENNReal)⁻¹
  have hweakened :
      WZ1UniformTripleDensity (c / 16)
        F G₁ selected refined :=
    uniform_triple_density_mono hUniform hdensityLower
  exact
    ⟨refined, hrefined.trans hinduced, hUniform.1, hweakened⟩

end Kakeya.Assouad
