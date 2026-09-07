import MyLeanRepo.Kakeya.Assouad.WZ1.Definitions
import MyLeanRepo.Kakeya.Assouad.WZ1.ProjectionTheoremFirstLayerStatements
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma49ActiveViewpoint
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma49StripProjectionGeometry
import MyLeanRepo.Kakeya.Assouad.WZ1.Lemma49StripNormalization

/-!
# Arithmetic and geometric bridging lemmas for WZ1 Lemma 8.13 Step 2
-/

namespace Kakeya.Assouad

open scoped ENNReal

/-- The active common width is bounded by 3 when all vertex sets lie in the
unit ball. -/
lemma wz1Lemma49_activeWidth_le_three
    {delta width : ℝ}
    {F G₁ G₂ : DiscreteSet 2}
    {H : Finset (Point2 × Point2 × Point2)}
    {c : ENNReal}
    (hDensity : WZ1UniformTripleDensity c F G₁ G₂ H)
    (base direction : Point2)
    (hdirection : ‖direction‖ = 1)
    (hwidth : 0 < width) (hwidthOne : width ≤ 1)
    (hdeltaOne : delta ≤ 1)
    (hG1_nonempty : G₁.Nonempty)
    (hG1_ball : G₁.IsInUnitBall)
    (hG2_ball : G₂.IsInUnitBall)
    (hG1strip : ∀ second ∈ G₁,
      second ∈ wz1LineNeighborhood base direction width) :
    wz1ActiveCommonWidth delta H hDensity.1 base direction ≤ 3 := by
  let perpendicular := wz1Perp2 direction
  have hpernorm : ‖perpendicular‖ = 1 := by
    have h := wz1Lemma49_norm_perp direction
    simpa [perpendicular, hdirection] using h
  rcases hG1_nonempty with ⟨p, hp⟩
  have hpStrip : |inner ℝ (p - base) perpendicular| ≤ width :=
    hG1strip p hp
  have hbasePerp : |inner ℝ base perpendicular| ≤ 1 + width := by
    calc
      |inner ℝ base perpendicular|
        = |inner ℝ p perpendicular - inner ℝ (p - base) perpendicular| := by
          simp [inner_sub_left]
      _ ≤ |inner ℝ p perpendicular| + |inner ℝ (p - base) perpendicular| :=
        abs_sub _ _
      _ ≤ ‖p‖ * ‖perpendicular‖ + width := by
        gcongr
        · exact abs_real_inner_le_norm p perpendicular
      _ ≤ 1 + width := by
        have hpnorm : ‖p‖ ≤ 1 := by
          simpa [dist_zero_right] using hG1_ball p hp
        rw [hpernorm] <;> linarith
  have hbound : ∀ (q : Point2), (q ∈ G₁ ∨ q ∈ G₂) →
      |inner ℝ (q - base) perpendicular| ≤ 3 := by
    intro q hq
    have hqball : ‖q‖ ≤ 1 := by
      rcases hq with (h | h)
      · simpa [dist_zero_right] using hG1_ball q h
      · simpa [dist_zero_right] using hG2_ball q h
    have h_eq : inner ℝ (q - base) perpendicular = inner ℝ q perpendicular - inner ℝ base perpendicular := by
      rw [inner_sub_left]
    calc
      |inner ℝ (q - base) perpendicular|
        = |inner ℝ q perpendicular - inner ℝ base perpendicular| := by rw [h_eq]
      _ ≤ |inner ℝ q perpendicular| + |inner ℝ base perpendicular| := abs_sub _ _
      _ ≤ ‖q‖ * ‖perpendicular‖ + (1 + width) := by
        gcongr
        · exact abs_real_inner_le_norm q perpendicular
      _ ≤ 1 + (1 + width) := by
        rw [hpernorm] <;> linarith [hwidthOne]
      _ ≤ 3 := by linarith [hwidthOne]
  have hH_nonempty : H.Nonempty := hDensity.1
  let widths : Finset ℝ :=
    H.image fun edge =>
      max |inner ℝ (edge.2.1 - base) perpendicular|
          |inner ℝ (edge.2.2 - base) perpendicular|
  have hwidths_nonempty : widths.Nonempty :=
    hH_nonempty.image _
  have h_all_le_three : ∀ w ∈ widths, w ≤ 3 := by
    intro w hw
    rcases Finset.mem_image.mp hw with ⟨edge, hedge, rfl⟩
    have h1 : edge.2.1 ∈ G₁ := by
      let encoded := wz1TripleCoordinate edge
      have henc : encoded ∈ wz1EncodeTriples H :=
        Finset.mem_image.mpr ⟨edge, hedge, rfl⟩
      have hsupported := hDensity.2.1 encoded henc 1
      simpa [encoded, wz1TripleCoordinate, wz1TripleVertexClasses] using hsupported
    have h2 : edge.2.2 ∈ G₂ := by
      let encoded := wz1TripleCoordinate edge
      have henc : encoded ∈ wz1EncodeTriples H :=
        Finset.mem_image.mpr ⟨edge, hedge, rfl⟩
      have hsupported := hDensity.2.1 encoded henc 2
      simpa [encoded, wz1TripleCoordinate, wz1TripleVertexClasses] using hsupported
    have hb1 := hbound edge.2.1 (Or.inl h1)
    have hb2 := hbound edge.2.2 (Or.inr h2)
    exact max_le hb1 hb2
  have hmax_le_three : widths.max' hwidths_nonempty ≤ 3 :=
    Finset.max'_le widths hwidths_nonempty 3 h_all_le_three
  simp only [wz1ActiveCommonWidth]
  exact max_le (by linarith [hdeltaOne]) hmax_le_three

/-- For small enough delta, the normalized side parameter D exceeds K.
Given the large-width condition for a specific delta', the conclusion follows. -/
lemma wz1Lemma49_D_lower_bound
    {epsilon width activeWidth : ℝ}
    (hepsilon : 0 < epsilon) (hepsilonOne : epsilon < 1)
    (hwidth : 0 < width)
    (K : ℝ) (hK : 0 < K) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ (delta' : ℝ), 0 < delta' → delta' ≤ delta₀ →
        (Real.rpow delta' (-epsilon + wz1Lemma49AuxiliaryEpsilon epsilon) * width < activeWidth →
          K < 2 * (activeWidth / width - 1)) := by
  let epsAux := wz1Lemma49AuxiliaryEpsilon epsilon
  have h_exp_pos : 0 < epsilon - epsAux := by
    dsimp only [epsAux, wz1Lemma49AuxiliaryEpsilon] <;> nlinarith
  let threshold : ℝ := K / 2 + 1
  have hthreshold_pos : 0 < threshold := by
    dsimp only [threshold]
    have h1 : 0 < K / 2 := by exact half_pos hK
    linarith
  set y : ℝ := (-(1 : ℝ) / (epsilon - epsAux)) with hy_def
  set z : ℝ := (-(epsilon - epsAux)) with hz_def
  have hz_nonpos : z ≤ 0 := by
    simp [hz_def] <;> linarith
  have hprod : y * z = 1 := by
    simp [hy_def, hz_def] <;> field_simp <;> ring
  let delta₀ : ℝ := min 1 (threshold ^ y)
  have hdelta₀_pos : 0 < delta₀ := by positivity
  have hdelta₀_one : delta₀ ≤ 1 := min_le_left _ _
  refine ⟨delta₀, hdelta₀_pos, hdelta₀_one, ?_⟩
  intro delta' hdelta' hdelta'₀ hlarge
  have h_small : delta' ≤ threshold ^ y :=
    (le_min_iff).mp hdelta'₀ |>.2
  have h1 : (threshold ^ y) ^ z ≤ delta' ^ z :=
    Real.rpow_le_rpow_of_nonpos hdelta' h_small hz_nonpos
  have hmul : (threshold ^ y) ^ z = threshold := by
    have h : threshold ^ (y * z) = (threshold ^ y) ^ z := Real.rpow_mul (by positivity) _ _
    have h' : (threshold ^ y) ^ z = threshold ^ (y * z) := h.symm
    rw [h', hprod, Real.rpow_one]
  have h_rpow : threshold ≤ delta' ^ z := by
    rw [hmul] at h1; exact h1
  have h3 : Real.rpow delta' (-epsilon + epsAux) = delta' ^ z := by
    simp [hz_def] <;> ring_nf
  have h4 : threshold * width < activeWidth := by
    have h5 : Real.rpow delta' (-epsilon + epsAux) = delta' ^ z := h3
    rw [h5] at hlarge
    calc threshold * width
      ≤ (delta' ^ z) * width := by gcongr
    _ < activeWidth := hlarge
  have h6 : threshold < activeWidth / width := by
    have h_pos : 0 < width := hwidth
    calc threshold
      = (threshold * width) / width := by field_simp [h_pos.ne'] <;> ring
    _ < activeWidth / width := by gcongr
  dsimp only [threshold] at h6
  linarith

/-- Width upper bound from active width inequality and unit-ball geometry.
Given the large-width condition for a specific delta', width < B follows. -/
lemma wz1Lemma49_width_upper_bound
    {epsilon width activeWidth : ℝ}
    (hepsilon : 0 < epsilon) (hepsilonOne : epsilon < 1)
    (hwidth : 0 < width)
    (hactiveWidth_le_three : activeWidth ≤ 3)
    (B : ℝ) (hB : 0 < B) :
    ∃ delta₀ : ℝ, 0 < delta₀ ∧ delta₀ ≤ 1 ∧
      ∀ (delta' : ℝ), 0 < delta' → delta' ≤ delta₀ →
        (Real.rpow delta' (-epsilon + wz1Lemma49AuxiliaryEpsilon epsilon) * width < activeWidth →
          width < B) := by
  let epsAux := wz1Lemma49AuxiliaryEpsilon epsilon
  have h_exp_pos : 0 < epsilon - epsAux := by
    dsimp only [epsAux, wz1Lemma49AuxiliaryEpsilon] <;> nlinarith
  set y : ℝ := 1 / (epsilon - epsAux) with hy_def
  set z : ℝ := epsilon - epsAux with hz_def
  have hz_pos : 0 < z := h_exp_pos
  have hprod : y * z = 1 := by
    rw [hy_def]
    have h_ne : z ≠ 0 := hz_pos.ne'
    field_simp [h_ne] <;> ring
  let delta₀ : ℝ := min 1 ((B / 3) ^ y)
  have hdelta₀_pos : 0 < delta₀ := by positivity
  have hdelta₀_one : delta₀ ≤ 1 := min_le_left _ _
  refine ⟨delta₀, hdelta₀_pos, hdelta₀_one, ?_⟩
  intro delta' hdelta' hdelta'₀ hlarge
  have h_small : delta' ≤ (B / 3) ^ y :=
    (le_min_iff).mp hdelta'₀ |>.2
  have h_rpow : Real.rpow delta' z ≤ B / 3 := by
    have h1 : Real.rpow delta' z ≤ Real.rpow ((B / 3) ^ y) z :=
      Real.rpow_le_rpow hdelta'.le h_small (by linarith)
    have h2 : Real.rpow ((B / 3) ^ y) z = B / 3 := by
      have hmul : Real.rpow (B / 3) (y * z) = Real.rpow (Real.rpow (B / 3) y) z :=
        Real.rpow_mul (by positivity) y z
      have h3 : Real.rpow ((B / 3) ^ y) z = Real.rpow (B / 3) (y * z) := by
        exact hmul.symm
      rw [h3, hprod]
      exact Real.rpow_one (B / 3)
    rw [h2] at h1
    exact h1
  have h3 : Real.rpow delta' (-epsilon + epsAux) =
      (Real.rpow delta' z)⁻¹ := by
    have h4 : -epsilon + epsAux = -z := by
      simp [hz_def] <;> ring
    have h5 : Real.rpow delta' (-z) = (Real.rpow delta' z)⁻¹ := by
      have h : delta' ^ (-z) = (delta' ^ z)⁻¹ := Real.rpow_neg hdelta'.le z
      exact h
    rw [h4]
    exact h5
  have h4 : width / Real.rpow delta' z < activeWidth := by
    have h5 : Real.rpow delta' (-epsilon + epsAux) = (Real.rpow delta' z)⁻¹ := h3
    rw [h5] at hlarge
    have h6 : (Real.rpow delta' z)⁻¹ * width = width * (Real.rpow delta' z)⁻¹ := by ring
    rw [h6] at hlarge
    simpa [div_eq_mul_inv] using hlarge
  have h_pos : 0 < Real.rpow delta' z := Real.rpow_pos_of_pos hdelta' z
  have h5 : width < activeWidth * Real.rpow delta' z := by
    have h_eq : width = (width / Real.rpow delta' z) * Real.rpow delta' z := by
      field_simp [h_pos.ne'] <;> ring
    rw [h_eq]
    gcongr
  have h6 : width < 3 * Real.rpow delta' z := by
    calc width
      < activeWidth * Real.rpow delta' z := h5
    _ ≤ 3 * Real.rpow delta' z := by gcongr
  have h7 : width < B := by
    calc width
      < 3 * Real.rpow delta' z := h6
    _ ≤ 3 * (B / 3) := by gcongr
    _ = B := by ring
  exact h7

/-- Transfer strip membership from active-viewpoint convention (`|inner| ≤ width`)
to radial-projection convention (`|inner| ≤ W / 2`) by setting `W := 2 * width`. -/
lemma wz1Lemma49_strip_convention_adapter
    {base direction : Point2} {width : ℝ}
    {source : DiscreteSet 2}
    (hsource : ∀ second ∈ source,
      |inner ℝ (second - base) (wz1Perp2 direction)| ≤ width) :
    ∀ second ∈ source,
      |inner ℝ (second - base) (wz1Perp2 direction)| ≤ (2 * width) / 2 := by
  intro second hsecond
  have h := hsource second hsecond
  have h_eq : (2 * width) / 2 = width := by ring
  rw [h_eq]
  exact h

/-- A subset of G₁ inherits diameter ≤ 1/10 from standard separation. -/
lemma wz1Lemma49_source_diameter
    {F G₁ G₂ : DiscreteSet 2} {source : DiscreteSet 2}
    (hsource_subset : source ⊆ G₁)
    (hstandard : WZ1StandardSeparation F G₁ G₂) :
    ∀ first ∈ source, ∀ second ∈ source, dist first second ≤ 1 / 10 := by
  intro first hfirst second hsecond
  have h1 : first ∈ G₁ := hsource_subset hfirst
  have h2 : second ∈ G₁ := hsource_subset hsecond
  exact hstandard.2.1 first h1 second h2

/-- If width ≤ 1/50, then 4*width ≤ 1/10. -/
lemma wz1Lemma49_sourceScale_le_diameter
    {width : ℝ} (hwidth_le : width ≤ 1 / 50) :
    4 * width ≤ 1 / 10 := by
  linarith

end Kakeya.Assouad
