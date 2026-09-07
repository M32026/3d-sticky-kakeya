import MyLeanRepo.Kakeya.Assouad.WZ1.InducedTripleRefinement
import MyLeanRepo.Kakeya.Assouad.WZ1.Proposition45TwoEndsInfrastructure
import MyLeanRepo.Kakeya.Assouad.WZ1.ThinTubesLargeDotProduct
import MyLeanRepo.Kakeya.Assouad.WZ1.Theorem5_2LeafStatements

/-!
# Two-ends preparation for PDF Proposition 8.9

This theorem performs exactly the first paragraph of the paper proof:
restrict the first endpoint class by Lemma 8.10, refine the induced graph,
then repeat for the second endpoint class.
-/

namespace Kakeya.Assouad

theorem wz1_proposition8_9_two_ends_preparation :
    WZ1Proposition8_9TwoEndsPreparationStatement := by
  intro hRefine delta eta zeta
    hdelta hdeltaOne heta hzeta
    F G₁ G₂ hF hG₁ hG₂
    hFball hG₁ball hG₂ball
    hFsep hG₁sep hG₂sep
    hFfrost hG₁frost hG₂frost
    hstandard H hDensity
  classical
  let activeG₁ : DiscreteSet 2 :=
    wz1ActiveTripleProjection H 1
  have hactiveG₁Sub : activeG₁ ⊆ G₁ := by
    intro point hpoint
    rcases Finset.mem_image.mp hpoint with
      ⟨edge, hedge, rfl⟩
    exact
      (density_vertex_containment hDensity edge hedge).2.1
  have hactiveG₁ : activeG₁.Nonempty := by
    rcases hDensity.1 with ⟨edge, hedge⟩
    exact
      ⟨edge.2.1,
        Finset.mem_image.mpr ⟨edge, hedge, rfl⟩⟩
  rcases
      two_ends_reduction
        hdelta hdeltaOne hzeta hactiveG₁
        (fun point hpoint =>
          hG₁ball point (hactiveG₁Sub hpoint))
        1 (by norm_num) (by norm_num)
    with
      ⟨firstNormal, firstLevel, firstWidth,
        hfirstNormal, hfirstWidthLower, hfirstWidthUpper,
        hfirstDensity, hfirstNonconcentration⟩
  let firstSelected : DiscreteSet 2 :=
    activeG₁.filter fun point =>
      |inner ℝ point firstNormal - firstLevel| ≤ firstWidth
  rcases
      two_ends_to_raw_strip_nonconcentration
        firstNormal firstLevel hfirstNormal
        hdelta hzeta hfirstWidthLower hfirstWidthUpper
        hactiveG₁ (by norm_num)
        hfirstDensity hfirstNonconcentration
    with
      ⟨hfirstSelected, hfirstRaw⟩
  have hfirstActiveRetention :
      Kakeya.realRpowENN delta eta * G₁.enncard ≤
        activeG₁.enncard := by
    simpa [activeG₁, wz1TripleVertexClasses] using
      (active_triple_projection_card_lower hDensity 1)
  have hfirstStripRetention :
      ENNReal.ofReal (Real.rpow firstWidth zeta) *
          activeG₁.enncard ≤
        firstSelected.enncard := by
    apply real_card_retention_to_ennreal
    · exact Real.rpow_nonneg
        (hdelta.le.trans hfirstWidthLower) zeta
    · simpa [firstSelected, mul_assoc] using hfirstDensity
  have hfirstSelectedRetention :
      Kakeya.realRpowENN delta (eta + zeta) *
          G₁.enncard ≤
        firstSelected.enncard := by
    simpa using
      (two_ends_selected_retention
        (coefficient := (1 : ENNReal))
        hdelta hzeta hfirstWidthLower
        (by simpa using hfirstActiveRetention)
        hfirstStripRetention)
  have hfirstSelectedSub : firstSelected ⊆ G₁ := by
    intro point hpoint
    exact
      hactiveG₁Sub (Finset.mem_filter.mp hpoint).1
  have hfirstSelectedActive :
      ∀ point ∈ firstSelected,
        ∃ edge ∈ H, edge.2.1 = point := by
    intro point hpoint
    have hactive :=
      (Finset.mem_filter.mp hpoint).1
    rcases Finset.mem_image.mp hactive with
      ⟨edge, hedge, hedgePoint⟩
    exact ⟨edge, hedge, hedgePoint⟩
  rcases
      restrict_first_endpoint_and_refine
        hDensity hfirstSelectedSub hfirstSelectedActive
        hfirstSelected hRefine
    with
      ⟨firstRefinedGraph, hfirstRefinedSubset,
        hfirstRefinedNonempty, hfirstUniform⟩
  let firstDensity : ENNReal :=
    Kakeya.realRpowENN delta eta / 16
  have hfirstUniform' :
      WZ1UniformTripleDensity firstDensity
        F firstSelected G₂ firstRefinedGraph := by
    simpa [firstDensity] using hfirstUniform
  let activeG₂ : DiscreteSet 2 :=
    wz1ActiveTripleProjection firstRefinedGraph 2
  have hactiveG₂Sub : activeG₂ ⊆ G₂ := by
    intro point hpoint
    rcases Finset.mem_image.mp hpoint with
      ⟨edge, hedge, rfl⟩
    exact
      (density_vertex_containment hfirstUniform' edge hedge).2.2
  have hactiveG₂ : activeG₂.Nonempty := by
    rcases hfirstRefinedNonempty with ⟨edge, hedge⟩
    exact
      ⟨edge.2.2,
        Finset.mem_image.mpr ⟨edge, hedge, rfl⟩⟩
  rcases
      two_ends_reduction
        hdelta hdeltaOne hzeta hactiveG₂
        (fun point hpoint =>
          hG₂ball point (hactiveG₂Sub hpoint))
        1 (by norm_num) (by norm_num)
    with
      ⟨secondNormal, secondLevel, secondWidth,
        hsecondNormal, hsecondWidthLower, hsecondWidthUpper,
        hsecondDensity, hsecondNonconcentration⟩
  let secondSelected : DiscreteSet 2 :=
    activeG₂.filter fun point =>
      |inner ℝ point secondNormal - secondLevel| ≤ secondWidth
  rcases
      two_ends_to_raw_strip_nonconcentration
        secondNormal secondLevel hsecondNormal
        hdelta hzeta hsecondWidthLower hsecondWidthUpper
        hactiveG₂ (by norm_num)
        hsecondDensity hsecondNonconcentration
    with
      ⟨hsecondSelected, hsecondRaw⟩
  have hsecondActiveRaw :
      firstDensity * G₂.enncard ≤ activeG₂.enncard := by
    simpa [activeG₂, wz1TripleVertexClasses] using
      (active_triple_projection_card_lower hfirstUniform' 2)
  have hsecondActiveRetention :
      (1 / 16 : ENNReal) *
          Kakeya.realRpowENN delta eta * G₂.enncard ≤
        activeG₂.enncard := by
    calc
      (1 / 16 : ENNReal) *
          Kakeya.realRpowENN delta eta * G₂.enncard
          ≤ firstDensity * G₂.enncard := by
            gcongr
            simp [firstDensity, div_eq_mul_inv, mul_comm]
      _ ≤ activeG₂.enncard := hsecondActiveRaw
  have hsecondStripRetention :
      ENNReal.ofReal (Real.rpow secondWidth zeta) *
          activeG₂.enncard ≤
        secondSelected.enncard := by
    apply real_card_retention_to_ennreal
    · exact Real.rpow_nonneg
        (hdelta.le.trans hsecondWidthLower) zeta
    · simpa [secondSelected, mul_assoc] using hsecondDensity
  have hsecondSelectedRetention :
      (1 / 16 : ENNReal) *
          Kakeya.realRpowENN delta (eta + zeta) *
          G₂.enncard ≤
        secondSelected.enncard := by
    simpa using
      (two_ends_selected_retention
        (coefficient := (1 / 16 : ENNReal))
        hdelta hzeta hsecondWidthLower
        hsecondActiveRetention hsecondStripRetention)
  have hsecondSelectedSub : secondSelected ⊆ G₂ := by
    intro point hpoint
    exact
      hactiveG₂Sub (Finset.mem_filter.mp hpoint).1
  have hsecondSelectedActive :
      ∀ point ∈ secondSelected,
        ∃ edge ∈ firstRefinedGraph, edge.2.2 = point := by
    intro point hpoint
    have hactive :=
      (Finset.mem_filter.mp hpoint).1
    rcases Finset.mem_image.mp hactive with
      ⟨edge, hedge, hedgePoint⟩
    exact ⟨edge, hedge, hedgePoint⟩
  rcases
      restrict_second_endpoint_and_refine
        hfirstUniform' hsecondSelectedSub
        hsecondSelectedActive hsecondSelected hRefine
    with
      ⟨refinedGraph, hrefinedGraph,
        hrefinedNonempty, hrefinedUniform⟩
  let density : ENNReal := firstDensity / 16
  have hrefinedUniform' :
      WZ1UniformTripleDensity density
        F firstSelected secondSelected refinedGraph := by
    simpa [density] using hrefinedUniform
  exact
    ⟨{
      firstNormal := firstNormal
      firstLevel := firstLevel
      firstWidth := firstWidth
      firstNormal_unit := hfirstNormal
      firstWidth_lower := hfirstWidthLower
      firstWidth_upper := hfirstWidthUpper
      firstSelected := firstSelected
      firstSelected_subset := hfirstSelectedSub
      firstSelected_nonempty := hfirstSelected
      firstSelected_retention := hfirstSelectedRetention
      firstSelected_strip := by
        intro point hpoint
        exact (Finset.mem_filter.mp hpoint).2
      firstRawNonconcentration := hfirstRaw
      firstRefinedGraph := firstRefinedGraph
      firstRefinedGraph_subset := hfirstRefinedSubset
      firstDensity := firstDensity
      firstDensity_lower := by
        simp [firstDensity, div_eq_mul_inv, mul_comm]
      firstUniform := hfirstUniform'
      secondNormal := secondNormal
      secondLevel := secondLevel
      secondWidth := secondWidth
      secondNormal_unit := hsecondNormal
      secondWidth_lower := hsecondWidthLower
      secondWidth_upper := hsecondWidthUpper
      secondSelected := secondSelected
      secondSelected_subset := hsecondSelectedSub
      secondSelected_nonempty := hsecondSelected
      secondSelected_retention := hsecondSelectedRetention
      secondSelected_strip := by
        intro point hpoint
        exact (Finset.mem_filter.mp hpoint).2
      secondRawNonconcentration := hsecondRaw
      refinedGraph := refinedGraph
      refinedGraph_subset := hrefinedGraph
      density := density
      density_lower := by
        exact le_rfl
      uniform := hrefinedUniform'
    }⟩

end Kakeya.Assouad
