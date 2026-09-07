import MyLeanRepo.Kakeya.Assouad.WZ1.IncidenceGraph
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma49StripProjectionGeometry
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma8_13ActualRepresentativeSelection
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma8_13FaithfulActiveEndpoints
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma8_13FaithfulAffineTransport
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma8_13FaithfulKaufmanArithmetic
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma8_13FaithfulEndpointConstruction
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma8_13FineScaleLogAbsorption
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma8_13FaithfulG1Cardinality
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma8_13FaithfulSupportingLemmas
import MyLeanRepo.Kakeya.Assouad.WZ1.ProjectionDichotomyFromLeaves

namespace Kakeya.Assouad

open scoped ENNReal

/-- Convert uniform density encoded-edge support to raw edge support. -/
lemma wz1UniformTripleDensity_rawSupport
    {F G₁ G₂ : DiscreteSet 2} {H : Finset (Point2 × Point2 × Point2)} {c : ENNReal}
    (h : WZ1UniformTripleDensity c F G₁ G₂ H)
    {edge : Point2 × Point2 × Point2} (hedge : edge ∈ H) :
    edge.1 ∈ F ∧ edge.2.1 ∈ G₁ ∧ edge.2.2 ∈ G₂ := by
  let enc := wz1TripleCoordinate edge
  have h_enc : enc ∈ wz1EncodeTriples H :=
    Finset.mem_image.mpr ⟨edge, hedge, rfl⟩
  have h_sup : ∀ (i : Fin 3), enc i ∈ wz1TripleVertexClasses F G₁ G₂ i :=
    h.2.1 enc h_enc
  have h0 : enc 0 ∈ F := by
    have h : enc 0 ∈ wz1TripleVertexClasses F G₁ G₂ 0 := h_sup 0
    simpa [wz1TripleVertexClasses] using h
  have h1 : enc 1 ∈ G₁ := by
    have h : enc 1 ∈ wz1TripleVertexClasses F G₁ G₂ 1 := h_sup 1
    simpa [wz1TripleVertexClasses] using h
  have h2 : enc 2 ∈ G₂ := by
    have h : enc 2 ∈ wz1TripleVertexClasses F G₁ G₂ 2 := h_sup 2
    simpa [wz1TripleVertexClasses] using h
  have heq0 : enc 0 = edge.1 := by simp [enc, wz1TripleCoordinate]
  have heq1 : enc 1 = edge.2.1 := by simp [enc, wz1TripleCoordinate]
  have heq2 : enc 2 = edge.2.2 := by simp [enc, wz1TripleCoordinate]
  rw [heq0] at h0
  rw [heq1] at h1
  rw [heq2] at h2
  exact ⟨h0, h1, h2⟩

theorem wz1_lemma8_13_faithful_kaufman_input :
    WZ1Lemma8_13FaithfulKaufmanInputStatement := by
  intro epsilon hepsilon hepsilon1
  -- Budget delta₀ for graph weakening and circle constant
  rcases wz1Lemma8_13_faithful_kaufman_budget epsilon hepsilon hepsilon1 with
    ⟨deltaBudget, hdeltaBudget_pos, hdeltaBudget_one, hbudget⟩
  -- Log absorption delta₀ from bacon
  rcases wz1Lemma8_13_fineScale_log_absorption epsilon hepsilon hepsilon1 with
    ⟨logDelta₀, hlogDelta₀_pos, hlogDelta₀_one, hlogAbsorb⟩
  let delta₀ := min deltaBudget logDelta₀
  have hdelta₀_pos : 0 < delta₀ := by
    simp [delta₀, hdeltaBudget_pos, hlogDelta₀_pos]
  have hdelta₀_one : delta₀ ≤ 1 :=
    (min_le_left _ _).trans hdeltaBudget_one
  refine ⟨delta₀, hdelta₀_pos, hdelta₀_one, ?_⟩
  intro delta hdelta hdeltaSmall input affine
  have hdeltaOne : delta ≤ 1 := hdeltaSmall.trans hdelta₀_one
  have hdeltaBudget : delta ≤ deltaBudget := hdeltaSmall.trans (min_le_left _ _)
  have hdeltaLog : delta ≤ logDelta₀ := hdeltaSmall.trans (min_le_right _ _)
  let hbudgetAt := hbudget delta hdelta hdeltaBudget
  let eta := wz1Lemma8_13FaithfulEta epsilon
  let normalizedEta := wz1Lemma8_13FaithfulNormalizedEta epsilon
  let epsilonOne := wz1Lemma8_13FaithfulEpsilonOne epsilon
  have hgraphWeaken : 256 * Real.rpow delta normalizedEta ≤ Real.rpow delta eta :=
    hbudgetAt.1
  have hcircle : 2 + (4 / Real.sqrt 3 + 1) / wz1Lemma8_13FaithfulDirectionKappa delta epsilon ≤
      Real.rpow delta (-normalizedEta) := hbudgetAt.2.2
  -- normalizedF nonempty
  have hnormalizedF_nonempty : affine.normalizedF.Nonempty := by
    have hH : affine.normalizedH.Nonempty := affine.normalizedUniform.1
    rcases hH with ⟨edge, hedge⟩
    have h_sup := affine.normalizedSupport edge hedge
    exact ⟨edge.1, h_sup.1⟩
  -- Coarsening
  have hfineScale_pos := affine.fineScale_pos
  have hfineScale_le_angular := affine.fineScale_le_angular
  have hangularScale_le_quarter := affine.angularScale_le_quarter
  have hfineScale_le_half : wz1Lemma8_13FaithfulFineScale input ≤ 1 / 2 :=
    hfineScale_le_angular.trans (hangularScale_le_quarter.trans (by norm_num))
  have hangularScale_le_one : wz1Lemma8_13FaithfulAngularScale input ≤ 1 :=
    hangularScale_le_quarter.trans (by norm_num)
  have hfineConstant_ge_one := affine.fineConstant_ge_one
  have hfineConstant_one : (1 : ENNReal) ≤ ENNReal.ofReal affine.fineConstant := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_mono hfineConstant_ge_one
  rcases wz1_frostman_coarsening
      (wz1Lemma8_13FaithfulFineScale input)
      (wz1Lemma8_13FaithfulAngularScale input)
      1 hfineScale_pos hfineScale_le_half
      hfineScale_le_angular hangularScale_le_one
      (by norm_num) (by norm_num)
      affine.normalizedF hnormalizedF_nonempty
      affine.normalizedF_ball affine.normalizedF_separated
      (ENNReal.ofReal affine.fineConstant)
      hfineConstant_one affine.normalizedF_frostman with
    ⟨coarsening⟩
  -- Selected active: every selected point is first coord of some normalizedH edge
  have hcoarsening_selected_active :
      ∀ point ∈ coarsening.selected, ∃ edge ∈ affine.normalizedH, edge.1 = point := by
    intro point hpoint
    have hpoint_in_F : point ∈ affine.normalizedF := coarsening.selected_subset hpoint
    rw [affine.normalizedF_eq] at hpoint_in_F
    rcases Finset.mem_image.mp hpoint_in_F with ⟨q, hq_sourceF, hq_eq⟩
    rw [affine.sourceF_eq] at hq_sourceF
    rcases Finset.mem_image.mp hq_sourceF with ⟨srcEdge, hsrcEdge_in, hsrcEdge_eq⟩
    have hsrcEdge1 : srcEdge.1 = q := by
      simpa [wz1TripleCoordinate] using hsrcEdge_eq
    let normEdge := wz1Lemma8_13FaithfulTripleMap input affine.normalizationWidth_pos srcEdge
    have hnormEdge_in : normEdge ∈ affine.normalizedH := by
      rw [affine.normalizedH_eq]
      exact Finset.mem_image.mpr ⟨srcEdge, hsrcEdge_in, rfl⟩
    have hnormEdge1 : normEdge.1 = point := by
      dsimp only [normEdge, wz1Lemma8_13FaithfulTripleMap]
      rw [hsrcEdge1, hq_eq]
    exact ⟨normEdge, hnormEdge_in, hnormEdge1⟩
  -- Representative selection
  let density : ENNReal := Kakeya.realRpowENN delta eta / 16
  have hdensity_pos : 0 < density := by
    apply ENNReal.div_pos
    · simp [Kakeya.realRpowENN, Real.rpow_pos_of_pos hdelta]
    · norm_num
  rcases wz1_lemma8_13_actual_representative_selection
      (hcoarseScale := affine.angularScale_pos)
      (hcoarseScaleOne := hangularScale_le_one)
      (hsourceConstant := affine.fineConstant_ge_one)
      (hFball := affine.normalizedF_ball)
      coarsening (hdensity := hdensity_pos)
      (hUniform := affine.normalizedUniform)
      (hselectedActive := hcoarsening_selected_active)
      wz1_tripartite_hypergraph_refinement with
    ⟨representatives⟩
  -- Final sets
  let finalF := representatives.normalizedF
  let finalH := representatives.normalizedH
  let finalG₁ := wz1ActiveTripleProjection finalH 1
  let finalG₂ := wz1ActiveTripleProjection finalH 2
  -- Density equality: (x / 16) / 16 = x / 256
  have h16_ne_zero : (16 : ENNReal) ≠ 0 := by norm_num
  have h16_ne_top : (16 : ENNReal) ≠ ⊤ := by norm_num
  have h_inv : ((16 : ENNReal) * (16 : ENNReal))⁻¹ = (16 : ENNReal)⁻¹ * (16 : ENNReal)⁻¹ :=
    ENNReal.mul_inv (Or.inl h16_ne_zero) (Or.inl h16_ne_top)
  have hdensity16 : density / 16 = Kakeya.realRpowENN delta eta / 256 := by
    dsimp only [density]
    have h16_ne_zero : (16 : ENNReal) ≠ 0 := by norm_num
    have h16_ne_top : (16 : ENNReal) ≠ ⊤ := by norm_num
    simp only [div_eq_mul_inv]
    have h_assoc : Kakeya.realRpowENN delta eta * (16 : ENNReal)⁻¹ * (16 : ENNReal)⁻¹ =
        Kakeya.realRpowENN delta eta * ((16 : ENNReal)⁻¹ * (16 : ENNReal)⁻¹) := by
      rw [mul_assoc]
    rw [h_assoc]
    have h_inv : ((16 : ENNReal) * (16 : ENNReal))⁻¹ = (16 : ENNReal)⁻¹ * (16 : ENNReal)⁻¹ :=
      ENNReal.mul_inv (Or.inl h16_ne_zero) (Or.inl h16_ne_top)
    rw [← h_inv]
    have h2 : (16 : ENNReal) * (16 : ENNReal) = (256 : ENNReal) := by norm_num
    rw [h2]
  have huniformOrig : WZ1UniformTripleDensity
      (Kakeya.realRpowENN delta eta / 256) finalF affine.normalizedG₁ affine.normalizedG₂ finalH := by
    rw [← hdensity16]
    exact representatives.normalizedUniform
  have hfinalUniformRaw : WZ1UniformTripleDensity
      (Kakeya.realRpowENN delta eta / 256) finalF finalG₁ finalG₂ finalH :=
    uniform_density_on_active_endpoints huniformOrig
  -- finalH subset
  have hfinalH_subset : finalH ⊆ affine.normalizedH := representatives.normalizedH_subset
  -- normalizedG₂ is singleton
  have hnormalizedG₂_singleton : affine.normalizedG₂ = {affine.normalizedViewpoint} := by
    rw [affine.normalizedG₂_eq, affine.sourceG₂_eq_singleton]
    simp [affine.normalizedViewpoint_eq]
  -- finalG₁ subset
  have hfinalG₁_subset : finalG₁ ⊆ affine.normalizedG₁ := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨edge, hedge, rfl⟩
    have h_sup := wz1UniformTripleDensity_rawSupport huniformOrig hedge
    exact h_sup.2.1
  -- finalG₂ singleton
  have hfinalG₂_eq_singleton : finalG₂ = {affine.normalizedViewpoint} := by
    ext x
    simp only [finalG₂, wz1ActiveTripleProjection, Finset.mem_image, Finset.mem_singleton]
    constructor
    · rintro ⟨edge, hedge, rfl⟩
      have h_sup := wz1UniformTripleDensity_rawSupport huniformOrig hedge
      have h_in_G₂ : (wz1TripleCoordinate edge 2) ∈ affine.normalizedG₂ := h_sup.2.2
      rw [hnormalizedG₂_singleton] at h_in_G₂
      simpa using h_in_G₂
    · intro hx
      have hx_eq : x = affine.normalizedViewpoint := by simpa [Finset.mem_singleton] using hx
      have h_nonempty : finalH.Nonempty := huniformOrig.1
      rcases h_nonempty with ⟨edge, hedge⟩
      have h_sup := wz1UniformTripleDensity_rawSupport huniformOrig hedge
      have h_third : (wz1TripleCoordinate edge 2) = x := by
        have h_in_G₂ : (wz1TripleCoordinate edge 2) ∈ affine.normalizedG₂ := h_sup.2.2
        rw [hnormalizedG₂_singleton] at h_in_G₂
        have h_vp : (wz1TripleCoordinate edge 2) = affine.normalizedViewpoint := by simpa using h_in_G₂
        rw [h_vp, hx_eq]
      exact ⟨edge, hedge, h_third⟩
  have hfinalH_nonempty : finalH.Nonempty := huniformOrig.1
  have hfinalG₁_nonempty : finalG₁.Nonempty := by
    rcases hfinalH_nonempty with ⟨edge, hedge⟩
    exact ⟨wz1TripleCoordinate edge 1, Finset.mem_image.mpr ⟨edge, hedge, rfl⟩⟩
  have hfinalG₁_ball : finalG₁.IsInUnitBall := by
    intro x hx; exact affine.normalizedG₁_ball x (hfinalG₁_subset hx)
  have hfinalG₂_ball : finalG₂.IsInUnitBall := by
    rw [hfinalG₂_eq_singleton]
    intro x hx
    simp only [Finset.mem_singleton] at hx
    rw [hx]
    exact affine.normalizedG₂_ball affine.normalizedViewpoint affine.normalizedViewpoint_mem
  have hfinalG₁_separated : finalG₁.IsDeltaSeparated (wz1Lemma8_13FaithfulSourceScale input) := by
    intro x hx y hy hne
    exact affine.normalizedSource_separated (hfinalG₁_subset hx) (hfinalG₁_subset hy) hne
  have hfinalG₁_strip : ∀ point ∈ finalG₁,
      |inner ℝ (point - affine.normalizedBase) (wz1Perp2 affine.viewpoint.orientedDirection)| ≤
        wz1Lemma8_13FaithfulAngularScale input / 2 := by
    intro point hpoint
    exact affine.normalizedSource_strip point (hfinalG₁_subset hpoint)
  have hfinalG₁_side : ∀ point ∈ finalG₁,
      wz1Lemma8_13FaithfulSide input / 2 ≤
        inner ℝ (point - affine.normalizedViewpoint) (wz1Perp2 affine.viewpoint.orientedDirection) := by
    intro point hpoint
    exact affine.normalizedSource_side point (hfinalG₁_subset hpoint)
  -- commonConstant = max of representative constant and radial constant
  let radialConstant : ℝ := 2 + (4 / Real.sqrt 3 + 1) / wz1Lemma8_13FaithfulDirectionKappa delta epsilon
  let commonConstant : ℝ := max representatives.constant radialConstant
  have hcommonConstant_eq : commonConstant = max representatives.constant radialConstant := rfl
  have hrep_const_le : representatives.constant ≤ commonConstant := le_max_left _ _
  have hradial_const_le : radialConstant ≤ commonConstant := le_max_right _ _
  have hcommonConstant_ge_one : 1 ≤ commonConstant := by
    have h1 : 1 ≤ representatives.constant := by
      rw [representatives.constant_eq]
      exact wz1Representative_constant_ge_one coarsening hnormalizedF_nonempty affine.fineConstant_ge_one
    exact h1.trans (le_max_left _ _)
  have hrep_bound : representatives.constant ≤ Real.rpow delta (-normalizedEta) := by
    rw [representatives.constant_eq]
    exact hlogAbsorb delta hdelta hdeltaLog
      (wz1Lemma8_13FaithfulAspect input)
      coarsening.logarithmicLoss affine.fineConstant
      (le_max_left _ _)
      affine.aspect_upper
      coarsening.logarithmicLoss_pos.le
      coarsening.logarithmicLoss_bound
      (by linarith [affine.fineConstant_ge_one])
      affine.fineConstant_bound
  have hradial_bound : radialConstant ≤ Real.rpow delta (-normalizedEta) := hcircle
  have hcommonConstant_bound : commonConstant ≤ Real.rpow delta (-normalizedEta) :=
    max_le_iff.mpr ⟨hrep_bound, hradial_bound⟩
  -- Weaken finalF Frostman to commonConstant
  have hfinalF_frostman : finalF.IsFrostman
      (wz1Lemma8_13FaithfulAngularScale input) 1
      (ENNReal.ofReal commonConstant) :=
    representatives.normalizedF_frostman.mono_const
      (ENNReal.ofReal_le_ofReal hrep_const_le)
  -- finalUniform weakening
  have hgraphDensity_le : ENNReal.ofReal (wz1Lemma8_13FaithfulGraphDensity delta epsilon) ≤
      Kakeya.realRpowENN delta eta / 256 := by
    have h1 : wz1Lemma8_13FaithfulGraphDensity delta epsilon = Real.rpow delta normalizedEta := by rfl
    rw [h1]
    have h_nonneg : 0 ≤ Real.rpow delta normalizedEta := Real.rpow_nonneg hdelta.le _
    have h_enn : (256 : ENNReal) * ENNReal.ofReal (Real.rpow delta normalizedEta) ≤
        ENNReal.ofReal (Real.rpow delta eta) := by
      have h256 : (256 : ENNReal) = ENNReal.ofReal (256 : ℝ) := by simp
      rw [h256]
      have h_mul : ENNReal.ofReal (256 : ℝ) * ENNReal.ofReal (Real.rpow delta normalizedEta) =
          ENNReal.ofReal ((256 : ℝ) * Real.rpow delta normalizedEta) :=
        (ENNReal.ofReal_mul (show (0 : ℝ) ≤ (256 : ℝ) by norm_num)).symm
      rw [h_mul]
      exact ENNReal.ofReal_le_ofReal hgraphWeaken
    have h_enn' : ENNReal.ofReal (Real.rpow delta normalizedEta) * (256 : ENNReal) ≤
        ENNReal.ofReal (Real.rpow delta eta) := by
      rw [mul_comm] at h_enn
      exact h_enn
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inl (by norm_num))]
    exact h_enn'
  have hfinalUniform : WZ1UniformTripleDensity
      (ENNReal.ofReal (wz1Lemma8_13FaithfulGraphDensity delta epsilon))
      finalF finalG₁ finalG₂ finalH :=
    wz1UniformTripleDensity_weaken hfinalUniformRaw hgraphDensity_le
  -- finalF properties
  have hfinalF_nonempty : finalF.Nonempty := representatives.normalizedF_nonempty
  have hfinalF_ball : finalF.IsInUnitBall := representatives.normalizedF_ball
  have hfinalF_separated : finalF.IsDeltaSeparated (wz1Lemma8_13FaithfulAngularScale input) :=
    representatives.normalizedF_separated
  -- Cardinality bound from cobalt's lemma
  have hcard_final : wz1Lemma8_13FaithfulDirectionKappa delta epsilon /
        wz1Lemma8_13FaithfulAngularScale input ≤ (finalG₁.card : ℝ) :=
    wz1Lemma8_13FaithfulG1_cardinality_bound delta epsilon hepsilon input hdelta affine coarsening representatives
  -- Radial projection
  have hviewpointBall : ‖affine.normalizedViewpoint‖ ≤ 1 := by
    have h : dist affine.normalizedViewpoint 0 ≤ 1 :=
      affine.normalizedG₂_ball affine.normalizedViewpoint affine.normalizedViewpoint_mem
    simpa [dist_zero_right] using h
  rcases strip_radial_projection_frostman
      (base := affine.normalizedBase)
      (direction := affine.viewpoint.orientedDirection)
      (viewpoint := affine.normalizedViewpoint)
      (hdirection := affine.viewpoint.orientedDirection_unit)
      (hwidth := affine.angularScale_pos)
      (hside := affine.side_pos)
      (hsourceScale := affine.sourceScale_pos)
      (hangularScale := affine.angularScale_pos)
      (hangularScaleHalf := hangularScale_le_quarter.trans (by norm_num))
      (hkappa := wz1Lemma8_13_directionKappa_pos hdelta)
      (hsourceNonempty := hfinalG₁_nonempty)
      (hsourceSeparated := hfinalG₁_separated)
      (hsourceStrip := hfinalG₁_strip)
      (hsourceSide := hfinalG₁_side)
      (hsourceBall := hfinalG₁_ball)
      (hviewpointBall := hviewpointBall)
      (hthreshold := affine.radial_threshold)
      (hangularBound := affine.radial_angular_bound)
      (hcardinality := hcard_final) with
    ⟨radialRaw⟩
  -- Weaken radial Frostman to commonConstant
  let radial : WZ1Lemma49RadialProjectionData
      finalG₁ affine.normalizedViewpoint
      (wz1Lemma8_13FaithfulAngularScale input) commonConstant :=
    { directions := radialRaw.directions,
      directions_nonempty := radialRaw.directions_nonempty,
      unit := radialRaw.unit,
      separated := radialRaw.separated,
      frostman := radialRaw.frostman.mono_const
        (ENNReal.ofReal_le_ofReal hradial_const_le),
      source_image := radialRaw.source_image }
  -- Endpoints
  rcases wz1Lemma8_13_faithful_endpoint_construction affine radial hfinalG₁_subset with
    ⟨firstEndpoint, secondEndpoint, hfirstEndpoint_mem, hsecondEndpoint_eq,
     hsecondEndpoint_mem_affine, hdirection_eq, hendpointDistance_lower, hendpointDistance_upper⟩
  have hsecondEndpoint_mem : ∀ direction ∈ radial.directions, secondEndpoint direction ∈ finalG₂ := by
    intro direction _
    have h1 : secondEndpoint direction = affine.normalizedViewpoint := hsecondEndpoint_eq direction
    rw [h1, hfinalG₂_eq_singleton] <;> simp
  -- finalSupport
  have hfinalSupport : ∀ edge ∈ finalH,
      edge.1 ∈ finalF ∧ edge.2.1 ∈ finalG₁ ∧ edge.2.2 ∈ finalG₂ := by
    intro edge hedge
    exact wz1UniformTripleDensity_rawSupport hfinalUniformRaw hedge
  -- fiber_density
  have hfiber_density : ∀ direction ∈ radial.directions,
      ((kaufmanFiber finalH (firstEndpoint direction) (secondEndpoint direction)).card : ENNReal) ≥
        ENNReal.ofReal (wz1Lemma8_13FaithfulGraphDensity delta epsilon) * finalF.enncard := by
    intro direction hdir
    have h1 : firstEndpoint direction ∈ finalG₁ := hfirstEndpoint_mem direction hdir
    rcases Finset.mem_image.mp h1 with ⟨edge, hedge, h_eq1⟩
    have h_e1 : edge.2.1 = firstEndpoint direction := by
      simpa [wz1TripleCoordinate] using h_eq1
    have h_e2 : edge.2.2 = secondEndpoint direction := by
      have h_in_G₂ : edge.2.2 ∈ finalG₂ := (hfinalSupport edge hedge).2.2
      rw [hfinalG₂_eq_singleton] at h_in_G₂
      have h_vp : edge.2.2 = affine.normalizedViewpoint := by simpa using h_in_G₂
      rw [h_vp, hsecondEndpoint_eq direction]
    have hbound := uniform_density_fiber_bound hfinalUniform edge hedge
    rw [h_e1, h_e2] at hbound
    exact hbound
  -- sourceWitness
  have hsourceWitness : ∀ finalEdge ∈ finalH,
      ∃ sourceEdge ∈ input.H, sourceEdge.2.2 = affine.viewpoint.viewpoint ∧
        finalEdge = wz1Lemma8_13FaithfulTripleMap input affine.normalizationWidth_pos sourceEdge := by
    intro finalEdge hfinalEdge
    have h1 : finalEdge ∈ affine.normalizedH := hfinalH_subset hfinalEdge
    exact affine.sourceWitness finalEdge h1
  have hsourceDot_eq := affine.sourceDot_eq
  have hnormalizedEta_pos : 0 < normalizedEta := by
    dsimp only [normalizedEta, wz1Lemma8_13FaithfulNormalizedEta] <;> positivity
  have hnormalizedEta_lt_quarter : normalizedEta < epsilon / 4 :=
    wz1Lemma8_13_normalizedEta_lt_quarter hepsilon hepsilon1
  have hdirectionKappa_pos : 0 < wz1Lemma8_13FaithfulDirectionKappa delta epsilon :=
    wz1Lemma8_13_directionKappa_pos hdelta
  exact ⟨{
    normalizedEta_pos := hnormalizedEta_pos
    normalizedEta_lt_epsilon_quarter := hnormalizedEta_lt_quarter
    directionKappa_pos := hdirectionKappa_pos
    coarsening := coarsening
    coarsening_selected_active := hcoarsening_selected_active
    representatives := representatives
    finalF_eq := rfl
    finalH_eq := rfl
    finalG₁_eq := rfl
    finalG₂_eq := rfl
    finalH_subset := hfinalH_subset
    finalG₁_subset := hfinalG₁_subset
    finalG₂_eq_singleton := hfinalG₂_eq_singleton
    commonConstant := commonConstant
    commonConstant_ge_one := hcommonConstant_ge_one
    commonConstant_bound := hcommonConstant_bound
    graphDensity_eq := rfl
    finalUniformRaw := hfinalUniformRaw
    finalUniform := hfinalUniform
    finalF_nonempty := hfinalF_nonempty
    finalF_ball := hfinalF_ball
    finalF_separated := hfinalF_separated
    finalF_frostman := hfinalF_frostman
    finalG₁_nonempty := hfinalG₁_nonempty
    finalG₁_ball := hfinalG₁_ball
    finalG₂_ball := hfinalG₂_ball
    finalG₁_separated := hfinalG₁_separated
    finalG₁_strip := hfinalG₁_strip
    finalG₁_side := hfinalG₁_side
    finalG₁_cardinality := hcard_final
    radial := radial
    firstEndpoint := firstEndpoint
    secondEndpoint := secondEndpoint
    firstEndpoint_mem := hfirstEndpoint_mem
    secondEndpoint_eq := hsecondEndpoint_eq
    secondEndpoint_mem := hsecondEndpoint_mem
    direction_eq := hdirection_eq
    endpointDistance_lower := hendpointDistance_lower
    endpointDistance_upper := hendpointDistance_upper
    finalSupport := hfinalSupport
    fiber_density := hfiber_density
    sourceWitness := hsourceWitness
    sourceDot_eq := hsourceDot_eq
  }⟩

end Kakeya.Assouad
