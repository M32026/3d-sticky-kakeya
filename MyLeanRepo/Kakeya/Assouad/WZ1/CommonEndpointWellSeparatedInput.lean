import MyLeanRepo.Kakeya.Assouad.WZ1.CommonEndpointAffineNormalization
import MyLeanRepo.Kakeya.Assouad.WZ1.ProjectionDichotomyFromLeaves
import MyLeanRepo.Kakeya.Assouad.WZ1.ProjectionParameterTuning

/-!
# Proposition-45 input from a normalized common-endpoint block
-/

namespace Kakeya.Assouad

noncomputable section

open scoped ENNReal

private lemma ofReal_mul_ofReal
    {first second : ℝ} (hfirst : 0 ≤ first) :
    ENNReal.ofReal first * ENNReal.ofReal second =
      ENNReal.ofReal (first * second) :=
  (ENNReal.ofReal_mul hfirst).symm

private lemma ofReal_product_pow_three
    {first second : ℝ} (hfirst : 0 ≤ first) (hsecond : 0 ≤ second) :
    (ENNReal.ofReal first * ENNReal.ofReal second) ^ 3 =
      ENNReal.ofReal ((first * second) ^ 3) := by
  rw [ofReal_mul_ofReal hfirst]
  exact (ENNReal.ofReal_pow (mul_nonneg hfirst hsecond) 3).symm

/-- Decode a function-valued three-edge back to a triple. -/
def wz1DecodeTriple (edge : Fin 3 → Point2) :
    Point2 × Point2 × Point2 :=
  (edge 0, edge 1, edge 2)

@[simp] lemma wz1DecodeTriple_encode (edge : Point2 × Point2 × Point2) :
    wz1DecodeTriple (wz1TripleCoordinate edge) = edge := by
  exact Prod.ext rfl (Prod.ext rfl rfl)

@[simp] lemma wz1TripleCoordinate_decode (edge : Fin 3 → Point2) :
    wz1TripleCoordinate (wz1DecodeTriple edge) = edge := by
  funext index
  fin_cases index <;> rfl

lemma wz1DecodeTriple_injective : Function.Injective wz1DecodeTriple := by
  intro first second heq
  have h := congr_arg wz1TripleCoordinate heq
  simpa using h

lemma wz1EncodeTriples_card
    (H : Finset (Point2 × Point2 × Point2)) :
    (wz1EncodeTriples H).card = H.card := by
  rw [wz1EncodeTriples, Finset.card_image_of_injective]
  intro first second heq
  have h0 := congr_fun heq 0
  have h1 := congr_fun heq 1
  have h2 := congr_fun heq 2
  exact Prod.ext h0 (Prod.ext h1 h2)

/-- The complete well-separated input at common scale `deltaGraph/2`. -/
structure WZ1CommonEndpointWellSeparatedInput
    {rho eta : ℝ}
    {sourceF sourceG₁ sourceG₂ : DiscreteSet 2}
    {sourceH : Finset (Point2 × Point2 × Point2)}
    {unitBall :
      WZ1Lemma23UnitBallGraph rho sourceF sourceG₁ sourceG₂ sourceH}
    {ready : WZ1Lemma23Theorem22ReadyGraph rho eta unitBall}
    {raw : WZ1CommonEndpointRawLocalization ready}
    (affine : WZ1CommonEndpointAffineNormalization raw) where
  delta : ℝ := ready.deltaGraph / 2
  delta_eq : delta = ready.deltaGraph / 2
  refinedH : Finset (Point2 × Point2 × Point2)
  refinedH_subset : refinedH ⊆ affine.H
  refinedH_card :
    (1 - Kakeya.realRpowENN ready.deltaGraph (20 * eta)) *
        (affine.H.card : ENNReal) ≤
      (refinedH.card : ENNReal)
  F_frostman :
    affine.F.IsFrostman delta 1
      (Kakeya.realRpowENN delta (-100 * eta))
  G₁_frostman :
    affine.G₁.IsFrostman delta 1
      (Kakeya.realRpowENN delta (-100 * eta))
  G₂_frostman :
    affine.G₂.IsFrostman delta 1
      (Kakeya.realRpowENN delta (-100 * eta))
  uniform :
    WZ1UniformTripleDensity
      (Kakeya.realRpowENN delta (100 * eta))
      affine.F affine.G₁ affine.G₂ refinedH

/-- Construct the full Proposition-45 input. -/
theorem WZ1CommonEndpointAffineNormalization.toWellSeparatedInput
    {rho eta : ℝ}
    {sourceF sourceG₁ sourceG₂ : DiscreteSet 2}
    {sourceH : Finset (Point2 × Point2 × Point2)}
    {unitBall :
      WZ1Lemma23UnitBallGraph rho sourceF sourceG₁ sourceG₂ sourceH}
    {ready : WZ1Lemma23Theorem22ReadyGraph rho eta unitBall}
    {raw : WZ1CommonEndpointRawLocalization ready}
    (affine : WZ1CommonEndpointAffineNormalization raw)
    (heta : 0 < eta)
    (budget : WZ1CommonEndpointParameterBudget eta ready.deltaGraph) :
    Nonempty (WZ1CommonEndpointWellSeparatedInput affine) := by
  let delta := ready.deltaGraph
  let delta' := delta / 2
  let C := Kakeya.realRpowENN delta (-eta)
  let epsilonRef := Kakeya.realRpowENN delta (20 * eta)
  have hdelta : 0 < delta := ready.deltaGraph_pos
  have hdeltaOne : delta ≤ 1 := budget.delta_half.trans (by norm_num)
  have hdelta' : 0 < delta' := by positivity
  have hdelta'One : delta' ≤ 1 := (div_le_self hdelta.le (by norm_num)).trans hdeltaOne
  have hC : 1 ≤ C := by
    dsimp only [C]
    exact ENNReal.one_le_ofReal.mpr
      (Real.one_le_rpow_of_pos_of_le_one_of_nonpos
        hdelta hdeltaOne (by linarith))
  have hsourceFkt : raw.localized.selectedF.IsKatzTao delta 1 C :=
    ready.F_katzTao.mono_set raw.localized.selectedF_subset
  have hsourceG₁kt : raw.localized.selectedG₁.IsKatzTao delta 1 C :=
    ready.G₁_katzTao.mono_set raw.localized.selectedG₁_subset
  have hsourceG₂kt : raw.localized.selectedG₂.IsKatzTao delta 1 C :=
    ready.G₁_katzTao.mono_set raw.localized.selectedG₂_subset
  have hsourceSep :
      raw.localized.selectedF.IsDeltaSeparated delta ∧
      raw.localized.selectedG₁.IsDeltaSeparated delta ∧
      raw.localized.selectedG₂.IsDeltaSeparated delta := by
    have hF := unitBall.F_separated.mono raw.localized.selectedF_subset
    have hG₁ := unitBall.G₁_separated.mono raw.localized.selectedG₁_subset
    have hG₂ := unitBall.G₁_separated.mono raw.localized.selectedG₂_subset
    simpa [delta, ready.deltaGraph_eq, wz1Lemma23Theorem22Scale] using
      And.intro hF (And.intro hG₁ hG₂)
  have hsourceFunit : raw.localized.selectedF.IsInUnitBall :=
    fun point hpoint => unitBall.F_unit point
      (raw.localized.selectedF_subset hpoint)
  have hsourceG₁unit : raw.localized.selectedG₁.IsInUnitBall :=
    fun point hpoint => unitBall.G₁_unit point
      (raw.localized.selectedG₁_subset hpoint)
  have hsourceG₂unit : raw.localized.selectedG₂.IsInUnitBall :=
    fun point hpoint => unitBall.G₁_unit point
      (raw.localized.selectedG₂_subset hpoint)
  have hFkt : affine.F.IsKatzTao delta' 1 C := by
    rw [affine.F_eq, affine.mapF_eq]
    exact hsourceFkt.image_positiveSimilarity_halfScale
      hdelta hdeltaOne affine.scaleF_pos affine.scaleF_half
      hC hsourceFunit hsourceSep.1
  have hG₁kt : affine.G₁.IsKatzTao delta' 1 C := by
    rw [affine.G₁_eq, affine.mapG_eq]
    exact hsourceG₁kt.image_positiveSimilarity_halfScale
      hdelta hdeltaOne affine.scaleG_pos affine.scaleG_half
      hC hsourceG₁unit hsourceSep.2.1
  have hG₂kt : affine.G₂.IsKatzTao delta' 1 C := by
    rw [affine.G₂_eq, affine.mapG_eq]
    exact hsourceG₂kt.image_positiveSimilarity_halfScale
      hdelta hdeltaOne affine.scaleG_pos affine.scaleG_half
      hC hsourceG₂unit hsourceSep.2.2
  have hcardUpperF : affine.F.enncard ≤ C * Kakeya.realRpowENN (1 / delta') 1 :=
    katzTao_unit_ball_card hdelta' hdelta'One affine.F_unit hFkt
  have hcardUpperG₁ : affine.G₁.enncard ≤ C * Kakeya.realRpowENN (1 / delta') 1 :=
    katzTao_unit_ball_card hdelta' hdelta'One affine.G₁_unit hG₁kt
  have hcardUpperG₂ : affine.G₂.enncard ≤ C * Kakeya.realRpowENN (1 / delta') 1 :=
    katzTao_unit_ball_card hdelta' hdelta'One affine.G₂_unit hG₂kt
  have hedge :
      Kakeya.realRpowENN delta (38 * eta - 3) ≤
        (affine.H.card : ENNReal) := by
    rw [affine.edge_card]
    simpa [delta] using raw.block_threshold
  have hactiveF := supported_first_card_lower affine.edge_support
    hedge hcardUpperG₁ hcardUpperG₂
  have hactiveG₁ := supported_second_card_lower affine.edge_support
    hedge hcardUpperF hcardUpperG₂
  have hactiveG₂ := supported_third_card_lower affine.edge_support
    hedge hcardUpperF hcardUpperG₁
  let upper := C * ENNReal.ofReal (1 / delta')
  let normalized := Kakeya.realRpowENN delta' (-100 * eta)
  have hupperEq :
      C * Kakeya.realRpowENN (1 / delta') 1 = upper := by
    rw [common_endpoint_realRpowENN_one]
  have hactiveF' :
      Kakeya.realRpowENN delta (38 * eta - 3) ≤
        affine.F.enncard * upper ^ 2 := by
    rw [hupperEq] at hactiveF
    exact hactiveF
  have hactiveG₁' :
      Kakeya.realRpowENN delta (38 * eta - 3) ≤
        upper * affine.G₁.enncard * upper := by
    rw [hupperEq] at hactiveG₁
    exact hactiveG₁
  have hactiveG₂' :
      Kakeya.realRpowENN delta (38 * eta - 3) ≤
        upper * upper * affine.G₂.enncard := by
    rw [hupperEq] at hactiveG₂
    exact hactiveG₂
  have hupperPos : 0 < upper := by
    dsimp only [upper, C]
    exact ENNReal.mul_pos
      (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hdelta _)).ne'
      (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hupperTop : upper ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by simp [C, Kakeya.realRpowENN])
      (by simp)
  have hcubic :
      upper ^ 3 ≤ normalized *
        Kakeya.realRpowENN delta (38 * eta - 3) := by
    have hreal := budget.frostman_cubic_real heta
    dsimp only [upper, normalized, C]
    rw [Kakeya.realRpowENN, Kakeya.realRpowENN, Kakeya.realRpowENN]
    have hleft :
        (ENNReal.ofReal (Real.rpow delta (-eta)) *
          ENNReal.ofReal (1 / delta')) ^ 3 =
        ENNReal.ofReal
          ((Real.rpow delta (-eta) * (1 / delta')) ^ 3) := by
      exact ofReal_product_pow_three
        (Real.rpow_nonneg hdelta.le _) (by positivity)
    have hright :
        ENNReal.ofReal (Real.rpow delta' (-100 * eta)) *
          ENNReal.ofReal (Real.rpow delta (38 * eta - 3)) =
        ENNReal.ofReal (Real.rpow delta' (-100 * eta) *
          Real.rpow delta (38 * eta - 3)) := by
      exact ofReal_mul_ofReal
        (Real.rpow_nonneg hdelta'.le (-100 * eta))
    rw [hleft, hright]
    exact ENNReal.ofReal_mono hreal
  have hcoefficient :
      C * ENNReal.ofReal (1 / delta') ≤
        Kakeya.realRpowENN delta' (-100 * eta) * affine.F.enncard ∧
      C * ENNReal.ofReal (1 / delta') ≤
        Kakeya.realRpowENN delta' (-100 * eta) * affine.G₁.enncard ∧
      C * ENNReal.ofReal (1 / delta') ≤
        Kakeya.realRpowENN delta' (-100 * eta) * affine.G₂.enncard := by
    have hF : upper ≤ normalized * affine.F.enncard :=
      coefficient_of_active_cubic hupperPos.ne' hupperTop hactiveF' hcubic
    have hG₁ : upper ≤ normalized * affine.G₁.enncard := by
      apply coefficient_of_active_cubic hupperPos.ne' hupperTop
        (card := affine.G₁.enncard) (edge := Kakeya.realRpowENN delta (38 * eta - 3))
      · simpa [mul_assoc, mul_comm, mul_left_comm, pow_two] using hactiveG₁'
      · exact hcubic
    have hG₂ : upper ≤ normalized * affine.G₂.enncard := by
      apply coefficient_of_active_cubic hupperPos.ne' hupperTop
        (card := affine.G₂.enncard) (edge := Kakeya.realRpowENN delta (38 * eta - 3))
      · simpa [mul_assoc, mul_comm, mul_left_comm, pow_two] using hactiveG₂'
      · exact hcubic
    simpa [upper, normalized] using And.intro hF (And.intro hG₁ hG₂)
  have hFfrost : affine.F.IsFrostman delta' 1
      (Kakeya.realRpowENN delta' (-100 * eta)) := by
    apply hFkt.toFrostman_of_coefficient hdelta'
    exact hcoefficient.1
  have hG₁frost : affine.G₁.IsFrostman delta' 1
      (Kakeya.realRpowENN delta' (-100 * eta)) := by
    apply hG₁kt.toFrostman_of_coefficient hdelta'
    exact hcoefficient.2.1
  have hG₂frost : affine.G₂.IsFrostman delta' 1
      (Kakeya.realRpowENN delta' (-100 * eta)) := by
    apply hG₂kt.toFrostman_of_coefficient hdelta'
    exact hcoefficient.2.2
  have hepsilonPos : 0 < epsilonRef := by
    exact ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hdelta _)
  have hepsilonLt : epsilonRef < 1 := by
    have hstrict : delta < 1 := budget.delta_half.trans_lt (by norm_num)
    exact ENNReal.ofReal_lt_one.mpr
      (Real.rpow_lt_one hdelta.le hstrict (by positivity))
  have hsupportEncoded :
      ∀ edge ∈ wz1EncodeTriples affine.H,
        ∀ index, edge index ∈
          wz1TripleVertexClasses affine.F affine.G₁ affine.G₂ index :=
    (show WZ1UniformHypergraphDensity 0
      (wz1TripleVertexClasses affine.F affine.G₁ affine.G₂)
      (wz1EncodeTriples affine.H) from
        ⟨by
          intro encoded hencoded index
          rcases Finset.mem_image.mp hencoded with ⟨edge, hedge, rfl⟩
          have hs := affine.edge_support edge hedge
          fin_cases index <;> simpa [wz1TripleVertexClasses, wz1TripleCoordinate] using
            (show _ from (by first | exact hs.1 | exact hs.2.1 | exact hs.2.2)),
         by simp⟩).1
  rcases wz1_tripartite_hypergraph_refinement
      (wz1TripleVertexClasses affine.F affine.G₁ affine.G₂)
      (wz1EncodeTriples affine.H) hsupportEncoded
      epsilonRef hepsilonPos hepsilonLt with
    ⟨encodedRefined, hrefinedSubset, hrefinedCard, hrefinedUniform⟩
  let refinedH := encodedRefined.image wz1DecodeTriple
  have hrefinedHSubset : refinedH ⊆ affine.H := by
    intro edge hedge
    rcases Finset.mem_image.mp hedge with ⟨encoded, hencoded, rfl⟩
    have hencodedAmbient := hrefinedSubset hencoded
    rcases Finset.mem_image.mp hencodedAmbient with ⟨source, hsource, heq⟩
    have hdecode := congr_arg wz1DecodeTriple heq
    simpa using hdecode ▸ hsource
  have hencodeRefined : wz1EncodeTriples refinedH = encodedRefined := by
    ext encoded
    simp only [wz1EncodeTriples, refinedH, Finset.mem_image]
    constructor
    · rintro ⟨triple, ⟨source, hsource, rfl⟩, rfl⟩
      simpa using hsource
    · intro hsource
      exact ⟨wz1DecodeTriple encoded,
        ⟨encoded, hsource, rfl⟩, by simp⟩
  have hrefinedHcard : refinedH.card = encodedRefined.card :=
    Finset.card_image_of_injective _ wz1DecodeTriple_injective
  have hencodedAmbientCard :
      (wz1EncodeTriples affine.H).card = affine.H.card :=
    wz1EncodeTriples_card affine.H
  have hrefinedCard' :
      (1 - epsilonRef) * (affine.H.card : ENNReal) ≤
        (encodedRefined.card : ENNReal) := by
    rwa [hencodedAmbientCard] at hrefinedCard
  have hrefinedNonempty : refinedH.Nonempty := by
    have hretentionPos :
        0 < (1 - epsilonRef) * (affine.H.card : ENNReal) := by
      have hHpos : 0 < (affine.H.card : ENNReal) := by
        rw [affine.edge_card]
        exact (ENNReal.ofReal_pos.mpr
          (Real.rpow_pos_of_pos hdelta _)).trans_le raw.block_threshold
      exact ENNReal.mul_pos (tsub_pos_iff_lt.mpr hepsilonLt).ne' hHpos.ne'
    have hcardPos : 0 < (encodedRefined.card : ENNReal) :=
      hretentionPos.trans_le hrefinedCard'
    rw [← hrefinedHcard] at hcardPos
    exact Finset.card_pos.mp (by exact_mod_cast hcardPos)
  have huniformRaw :
      WZ1UniformTripleDensity
        ((epsilonRef / 8) *
          ((affine.H.card : ENNReal) /
            (affine.F.enncard * affine.G₁.enncard * affine.G₂.enncard)))
        affine.F affine.G₁ affine.G₂ refinedH := by
    refine ⟨hrefinedNonempty, ?_⟩
    rw [hencodeRefined]
    have hconstant :
        (epsilonRef / (2 : ENNReal) ^ (3 : ℕ)) *
            ((wz1EncodeTriples affine.H).card /
              wz1VertexCardProduct
                (wz1TripleVertexClasses affine.F affine.G₁ affine.G₂)
                Finset.univ) =
          (epsilonRef / 8) *
            ((affine.H.card : ENNReal) /
              (affine.F.enncard * affine.G₁.enncard * affine.G₂.enncard)) := by
      rw [hencodedAmbientCard]
      simp [wz1VertexCardProduct, wz1TripleVertexClasses, Finset.prod,
        DiscreteSet.enncard]
      ring
    rw [← hconstant]
    exact hrefinedUniform
  have hdensity :
      Kakeya.realRpowENN delta' (100 * eta) ≤
        (epsilonRef / 8) *
          ((affine.H.card : ENNReal) /
            (affine.F.enncard * affine.G₁.enncard * affine.G₂.enncard)) := by
    have hpowerReal := budget.density_refinement_real heta
    have hpowerENN :
        8 * Kakeya.realRpowENN delta' (100 * eta) * upper ^ 3 ≤
          epsilonRef * Kakeya.realRpowENN delta (38 * eta - 3) := by
      dsimp only [upper, C, epsilonRef]
      simp only [Kakeya.realRpowENN]
      have hleft :
          (8 : ENNReal) * ENNReal.ofReal (Real.rpow delta' (100 * eta)) *
              (ENNReal.ofReal (Real.rpow delta (-eta)) *
                ENNReal.ofReal (1 / delta')) ^ 3 =
            ENNReal.ofReal (8 * Real.rpow delta' (100 * eta) *
              (Real.rpow delta (-eta) * (1 / delta')) ^ 3) := by
        have hinner :
            (ENNReal.ofReal (Real.rpow delta (-eta)) *
                ENNReal.ofReal (1 / delta')) ^ 3 =
              ENNReal.ofReal
                ((Real.rpow delta (-eta) * (1 / delta')) ^ 3) := by
          exact ofReal_product_pow_three
            (Real.rpow_nonneg hdelta.le _) (by positivity)
        rw [hinner]
        calc
          (8 : ENNReal) * ENNReal.ofReal (Real.rpow delta' (100 * eta)) *
              ENNReal.ofReal ((Real.rpow delta (-eta) * (1 / delta')) ^ 3) =
            ENNReal.ofReal (8 * Real.rpow delta' (100 * eta)) *
              ENNReal.ofReal ((Real.rpow delta (-eta) * (1 / delta')) ^ 3) := by
                norm_num
          _ = ENNReal.ofReal
              ((8 * Real.rpow delta' (100 * eta)) *
                ((Real.rpow delta (-eta) * (1 / delta')) ^ 3)) :=
            ofReal_mul_ofReal (mul_nonneg (by norm_num)
              (Real.rpow_nonneg hdelta'.le _))
          _ = ENNReal.ofReal (8 * Real.rpow delta' (100 * eta) *
              (Real.rpow delta (-eta) * (1 / delta')) ^ 3) := by ring
      have hright :
          ENNReal.ofReal (Real.rpow delta (20 * eta)) *
              ENNReal.ofReal (Real.rpow delta (38 * eta - 3)) =
            ENNReal.ofReal (Real.rpow delta (20 * eta) *
              Real.rpow delta (38 * eta - 3)) := by
        exact ofReal_mul_ofReal
          (Real.rpow_nonneg hdelta.le (20 * eta))
      rw [hleft, hright]
      exact ENNReal.ofReal_mono hpowerReal
    have hcardsZero :
        affine.F.enncard * affine.G₁.enncard * affine.G₂.enncard ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero
        (by simpa [DiscreteSet.enncard] using affine.F_nonempty.card_pos.ne')
        (by simpa [DiscreteSet.enncard] using affine.G₁_nonempty.card_pos.ne'))
        (by simpa [DiscreteSet.enncard] using affine.G₂_nonempty.card_pos.ne')
    have hcardsTop :
        affine.F.enncard * affine.G₁.enncard * affine.G₂.enncard ≠ ⊤ := by
      exact ENNReal.mul_ne_top
        (ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.coe_ne_top)
        ENNReal.coe_ne_top
    apply refinement_density_of_power_budget
      (upper := upper)
      ENNReal.coe_ne_top hcardsZero hcardsTop
      (by rwa [hupperEq] at hcardUpperF)
      (by rwa [hupperEq] at hcardUpperG₁)
      (by rwa [hupperEq] at hcardUpperG₂)
      hedge hpowerENN
  exact ⟨{
    delta := delta'
    delta_eq := rfl
    refinedH := refinedH
    refinedH_subset := hrefinedHSubset
    refinedH_card := by
      rw [hrefinedHcard]
      simpa [epsilonRef, delta] using hrefinedCard'
    F_frostman := hFfrost
    G₁_frostman := hG₁frost
    G₂_frostman := hG₂frost
    uniform := huniformRaw.mono hdensity
  }⟩

end

end Kakeya.Assouad
